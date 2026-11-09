const std = @import("std");
const types = @import("./types.zig");
const ExprId = @import("../../expr.zig").ExprId;
const TheoremContext = @import("../../expr.zig").TheoremContext;
const TemplateExpr = @import("../../rules.zig").TemplateExpr;
const templateHasUnboundBinder =
    @import("../../rules.zig").templateHasUnboundBinder;
const Context = types.Context;
const semantic = @import("./semantic.zig");
const isRigidHead = semantic.isRigidHead;
const bag = @import("./bag.zig");

const AcuiMember = struct {
    expr: ExprId,
    consumed: bool = false,
};

// Extract binder values from the members of an ACUI multiset (Proposal B).
//
// The structural walk in `def_match.extractHypPartialBindings` can't cross an
// ACUI head: e.g. the template context `G , ≃[A] x = t` (`join(G, hyp(eqc(A,x,t)))`)
// almost never matches the ref's context shape, so `A`, `x`, `t` stay unbound
// and the next hypothesis (`G ⊩ t : A`) is left searching its full ref pool.
// Here we treat the template's leaves under this combiner as a multiset and try
// to pin the binders of an unbound leaf from a forced ref member.
//
// The key step is *subtracting the bound siblings*. A leaf like the bound `G`
// (a binder already pinned to the goal context) expands to a known multiset of
// ref members; in any valid alignment those members are claimed by `G`. We mark
// them consumed first, so the unbound leaf only competes against what's left.
// Without this, `G ⊩ … , ≃[A] x = t` against a goal whose context already holds
// other equations would see several `hyp(eqc …)` members and give up. After
// removing `G`'s members, the lone remaining equation is forced.
//
// Why this is completeness-safe: in any valid ACUI alignment each bound leaf
// maps to ref members equal to its own (hash-consed ⇒ identity equality), and
// the unbound leaf maps to one of the rest. If, after removing the bound-leaf
// members, exactly one remaining member is shape-compatible with the unbound
// leaf, every valid alignment maps the leaf to it — so the binder values it
// yields are forced (the same the full validator would derive). With zero or
// several candidates we commit nothing. These are only search-guidance bindings
// (the proof is re-derived by `tryCandidate`), so an over-eager commit could
// only cost completeness, which the uniqueness gate prevents.
//
// Treating the args as a multiset assumes commutativity, so callers gate this
// on it (`bag.isCommutative`). A combiner that is neither commutative
// nor idempotent is a sequence and goes through
// `def_match.extractOrderedSpineBindings` instead.
pub fn extractAcuiMemberBindings(
    context: *const Context,
    theorem: *TheoremContext,
    head_id: u32,
    template: TemplateExpr,
    container: ExprId,
    bindings: []?ExprId,
    comptime extract_fn: fn (
        *const Context,
        *TheoremContext,
        TemplateExpr,
        ExprId,
        []?ExprId,
    ) void,
) void {
    var members: [bag.capacity]AcuiMember = undefined;
    var count: usize = 0;
    // Bail (extract nothing) on an unusually large context rather than risk
    // truncating the multiset, which could make a member look spuriously unique.
    if (!collectAcuiMembers(context, theorem, container, head_id, &members, &count)) return;
    const pool = members[0..count];
    const consume = consumesClaimed(context, head_id);

    // Pass 1: consume ref members claimed by the bound sibling leaves.
    if (consume) consumeBoundLeafMembers(context, theorem, head_id, template, bindings, pool);
    // Pass 2: pin each unbound leaf from a unique remaining member.
    extractUnboundLeafMembers(
        context,
        theorem,
        head_id,
        template,
        bindings,
        pool,
        consume,
        extract_fn,
    );
}

/// Whether a member one leaf claims is spent for the others. Under
/// idempotence (`g , g = g`) a leaf may repeat a member a sibling holds, so
/// claiming one rules out nothing, and a leaf whose only unclaimed match is
/// unique may still take a claimed one instead.
fn consumesClaimed(context: *const Context, head_id: u32) bool {
    const law = bag.lawOf(context, head_id) orelse return true;
    return !law.isIdempotent();
}

// The members of `container` under `head_id` (see `bag.flatten`) as an
// unconsumed pool. Returns false on overflow (caller then bails).
fn collectAcuiMembers(
    context: *const Context,
    theorem: *const TheoremContext,
    container: ExprId,
    head_id: u32,
    buf: *[bag.capacity]AcuiMember,
    count: *usize,
) bool {
    const members = bag.flatten(context, theorem, head_id, container) orelse return false;
    for (members.slice(), buf[0..members.len]) |expr, *slot| slot.* = .{ .expr = expr };
    count.* = members.len;
    return true;
}

// Mark consumed the pool members claimed by template leaves that have no
// unbound binder: a bound binder (e.g. `G`) expands to its own multiset; any
// other fully-bound leaf matches a single member directly.
fn consumeBoundLeafMembers(
    context: *const Context,
    theorem: *const TheoremContext,
    head_id: u32,
    template: TemplateExpr,
    bindings: []const ?ExprId,
    pool: []AcuiMember,
) void {
    switch (template) {
        .binder => |idx| {
            if (idx >= bindings.len) return;
            const value = bindings[idx] orelse return;
            const sub = bag.flatten(context, theorem, head_id, value) orelse return;
            for (sub.slice()) |member| consumePoolMemberById(pool, member);
        },
        .app => |app| {
            if (app.term_id == head_id) {
                for (app.args) |arg| {
                    consumeBoundLeafMembers(context, theorem, head_id, arg, bindings, pool);
                }
                return;
            }
            if (templateHasUnboundBinder(template, bindings)) return;
            for (pool) |*slot| {
                if (slot.consumed) continue;
                if (templateMatchesExprReadOnly(theorem, template, slot.expr, bindings)) {
                    slot.consumed = true;
                    return;
                }
            }
        },
    }
}

fn consumePoolMemberById(pool: []AcuiMember, expr: ExprId) void {
    for (pool) |*slot| {
        if (!slot.consumed and slot.expr == expr) {
            slot.consumed = true;
            return;
        }
    }
}

// For each template leaf with an unbound binder, if exactly one unconsumed pool
// member is shape-compatible, pin the leaf's binders from it and consume it.
fn extractUnboundLeafMembers(
    context: *const Context,
    theorem: *TheoremContext,
    head_id: u32,
    template: TemplateExpr,
    bindings: []?ExprId,
    pool: []AcuiMember,
    consume: bool,
    comptime extract_fn: fn (
        *const Context,
        *TheoremContext,
        TemplateExpr,
        ExprId,
        []?ExprId,
    ) void,
) void {
    switch (template) {
        // A bare binder captures "everything else"; can't pin to one member.
        .binder => return,
        .app => |app| {
            if (app.term_id == head_id) {
                for (app.args) |arg| {
                    extractUnboundLeafMembers(
                        context,
                        theorem,
                        head_id,
                        arg,
                        bindings,
                        pool,
                        consume,
                        extract_fn,
                    );
                }
                return;
            }
            if (!templateHasUnboundBinder(template, bindings)) return;
            var found: ?usize = null;
            var matches: usize = 0;
            for (pool, 0..) |slot, i| {
                if (slot.consumed) continue;
                if (templateMatchesExprReadOnly(theorem, template, slot.expr, bindings)) {
                    // Copies of one member pin the leaf alike: one choice.
                    if (found) |f| if (pool[f].expr == slot.expr) continue;
                    matches += 1;
                    found = i;
                }
            }
            if (matches == 1) {
                const idx = found.?;
                extract_fn(context, theorem, template, pool[idx].expr, bindings);
                pool[idx].consumed = consume;
            }
        },
    }
}

// Read-only structural alignment: does `expr` match `template` under the
// current bindings? Bound binders demand exact ExprId equality; unbound
// binders match anything (we make no commitment, since we're only deciding
// whether the candidate could plausibly work).
pub fn templateMatchesExprReadOnly(
    theorem: *const TheoremContext,
    template: TemplateExpr,
    expr_id: ExprId,
    bindings: []const ?ExprId,
) bool {
    return templateMatchesExprImpl(theorem, template, expr_id, bindings, false);
}

// Shared structural walk for the two read-only plausibility matchers above.
// `meta_wildcard` (comptime) selects the bound-binder leaf semantics: exact
// `ExprId` equality (strict) vs. unify-modulo-meta (carry-to-leaf witness).
fn templateMatchesExprImpl(
    theorem: *const TheoremContext,
    template: TemplateExpr,
    expr_id: ExprId,
    bindings: []const ?ExprId,
    comptime meta_wildcard: bool,
) bool {
    switch (template) {
        .binder => |idx| {
            if (idx >= bindings.len) return true;
            if (bindings[idx]) |bound| {
                if (meta_wildcard) return exprUnifiesModuloMeta(theorem, bound, expr_id);
                return bound == expr_id;
            }
            return true;
        },
        .app => |app| {
            const node = theorem.interner.node(expr_id);
            switch (node.*) {
                .app => |concrete| {
                    if (concrete.term_id != app.term_id) return false;
                    if (concrete.args.len != app.args.len) return false;
                    for (app.args, concrete.args) |tmpl_arg, conc_arg| {
                        if (!templateMatchesExprImpl(
                            theorem,
                            tmpl_arg,
                            conc_arg,
                            bindings,
                            meta_wildcard,
                        )) return false;
                    }
                    return true;
                },
                else => return false,
            }
        },
    }
}

/// Structural unifiability of two interned expressions treating any
/// search-meta leaf (on either side) as a wildcard. Used by the ACUI
/// membership prune to keep a carry-to-leaf witness binding (e.g. `P ?t`)
/// plausible against a concrete member (`P c`) without committing the meta —
/// the verdict is deferred to full validation. For meta-free expressions this
/// is exact structural equality, so a differing rigid skeleton (head/arity/var
/// clash) still prunes.
pub fn exprUnifiesModuloMeta(
    theorem: *const TheoremContext,
    a: ExprId,
    b: ExprId,
) bool {
    if (a == b) return true;
    const na = theorem.interner.node(a).*;
    const nb = theorem.interner.node(b).*;
    if (na == .placeholder and theorem.placeholderClass(na.placeholder) == .meta)
        return true;
    if (nb == .placeholder and theorem.placeholderClass(nb.placeholder) == .meta)
        return true;
    switch (na) {
        .app => |aa| switch (nb) {
            .app => |bb| {
                if (aa.term_id != bb.term_id) return false;
                if (aa.args.len != bb.args.len) return false;
                for (aa.args, bb.args) |x, y| {
                    if (!exprUnifiesModuloMeta(theorem, x, y)) return false;
                }
                return true;
            },
            else => return false,
        },
        // Distinct non-meta leaves (variables / non-meta placeholders) already
        // failed the `a == b` identity check above, so they do not unify.
        else => return false,
    }
}

// Canonicalize ACUI units away: under any registered combiner head (e.g. `join`
// / `,`), drop unit operands (`emp`) and flatten nested same-head combiners, so
// `combine(emp, X) ≡ X` structurally. Non-combiner apps are rebuilt with
// normalized children; leaves are returned unchanged. Returns the original id
// when nothing changed.
//
// Why: a generated context target carries a redundant `emp` — an `imp_intro`
// over an `emp ⊢ …` goal binds the rule's context binder to `emp`, so its
// hypothesis instantiates to `emp, p, …`. Search's strict `matchTemplate` then
// cannot equate that with a unit-free pool ref (e.g. `l3 : a=b, a∈a ⊢ …`), even
// though the validator absorbs the unit via the unit law. Normalizing the
// generation target before the recursive solve closes that gap soundly (the
// real `tryCandidate` still has final say).
pub fn normalizeAcuiUnits(
    context: *const Context,
    theorem: *TheoremContext,
    expr_id: ExprId,
) error{ OutOfMemory, TooManyTheoremExprs }!ExprId {
    return rebuildAcuiShared(context, theorem, expr_id, .unit_free);
}

/// Canonical `ExprId` for ACUI equality inside one interner scope. Like
/// `normalizeAcuiUnits` (flatten association, drop units) but additionally
/// *sorts* the members of a commutative combiner by id and *dedups* the
/// members of an idempotent one, so two ACUI-equal expressions map to the same
/// id. The forward pool uses it for fact shapes, which are terms the matchers
/// then explore: by id, a fact keeps its members in about the order it was
/// written, which the matchers explore well (a content order made one euclid
/// line 30x dearer to find). It is not a cross-scope key.
///
/// Conservative: it only collapses differences the *registered subset* actually
/// licenses — reordering only under C, duplicates only under C and I (after the
/// sort, so duplicates are adjacent). It therefore never maps two
/// genuinely-unequal expressions to the same id.
pub fn canonicalizeAcuiInScope(
    context: *const Context,
    theorem: *TheoremContext,
    expr_id: ExprId,
) error{ OutOfMemory, TooManyTheoremExprs }!ExprId {
    return rebuildAcuiShared(context, theorem, expr_id, .in_scope);
}

const AcuiForm = enum {
    /// Association flattened and this combiner's units dropped.
    unit_free,
    /// `unit_free`, with members sorted by id under C and deduped under C
    /// and I.
    in_scope,
};

/// The rebuilt ids of the app nodes a rebuild has done, so a shared subterm
/// is rebuilt once.
const RebuildMemo = TheoremContext.DagMemo(ExprId);

fn rebuildAcuiShared(
    context: *const Context,
    theorem: *TheoremContext,
    expr_id: ExprId,
    comptime form: AcuiForm,
) error{ OutOfMemory, TooManyTheoremExprs }!ExprId {
    var memo: RebuildMemo = .{};
    defer memo.deinit(theorem.allocator);
    return rebuildAcui(context, theorem, &memo, expr_id, form);
}

fn rebuildAcui(
    context: *const Context,
    theorem: *TheoremContext,
    memo: *RebuildMemo,
    expr_id: ExprId,
    comptime form: AcuiForm,
) error{ OutOfMemory, TooManyTheoremExprs }!ExprId {
    if (theorem.interner.node(expr_id).* != .app) return expr_id;
    if (memo.get(expr_id)) |rebuilt| return rebuilt;
    const rebuilt = try rebuildAcuiNode(context, theorem, memo, expr_id, form);
    try memo.put(theorem.allocator, expr_id, rebuilt);
    return rebuilt;
}

fn rebuildAcuiNode(
    context: *const Context,
    theorem: *TheoremContext,
    memo: *RebuildMemo,
    expr_id: ExprId,
    comptime form: AcuiForm,
) error{ OutOfMemory, TooManyTheoremExprs }!ExprId {
    var term_id: u32 = undefined;
    var arg_count: usize = 0;
    switch (theorem.interner.node(expr_id).*) {
        .app => |a| {
            term_id = a.term_id;
            arg_count = a.args.len;
        },
        else => return expr_id,
    }
    if (arg_count == 0) return expr_id;

    if (bag.combinerOf(context, term_id)) |combiner| {
        return rebuildAcuiCombiner(context, theorem, memo, combiner, expr_id, form);
    }

    // Non-combiner application: rebuild children, rebuild only if one changed.
    const args = try theorem.allocator.alloc(ExprId, arg_count);
    defer theorem.allocator.free(args);
    @memcpy(args, theorem.interner.node(expr_id).app.args);
    var changed = false;
    for (args) |*a| {
        const rebuilt = try rebuildAcui(context, theorem, memo, a.*, form);
        if (rebuilt != a.*) changed = true;
        a.* = rebuilt;
    }
    if (!changed) return expr_id;
    return theorem.interner.internApp(term_id, args);
}

fn rebuildAcuiCombiner(
    context: *const Context,
    theorem: *TheoremContext,
    memo: *RebuildMemo,
    combiner: bag.Combiner,
    expr_id: ExprId,
    comptime form: AcuiForm,
) error{ OutOfMemory, TooManyTheoremExprs }!ExprId {
    // Bail unchanged on an oversized bag rather than truncate it.
    const raw = combiner.flatten(theorem, expr_id) orelse return expr_id;

    // Each step is gated on the law the *registered subset* actually declares,
    // so this never equates two genuinely-unequal expressions (worst case: a
    // missed reuse). The minimum subset is AU — the DSL makes the associativity
    // rule and unit term mandatory while `comm`/`idem` are optional — so
    // flattening (A) and unit removal (U) are always licensed; ordering and
    // multiplicity are only collapsed under C and I respectively.

    // U (always): drop this combiner's unit members, including a member that
    // rebuilds to it (a member that is another combiner's unit stays). Nothing
    // is a unit if the unit term is unresolvable, so a malformed unit-less
    // declaration is inert here rather than wrong.
    var kept: [bag.capacity]ExprId = undefined;
    var kept_n: usize = 0;
    for (raw.slice()) |member| {
        const rebuilt = try rebuildAcui(context, theorem, memo, member, form);
        if (combiner.isUnit(theorem, rebuilt)) continue;
        kept[kept_n] = rebuilt;
        kept_n += 1;
    }

    // C (only when commutative): order is immaterial, so sort to collide
    // order-variant regions. Under a non-commutative subset (AU/AUI) order is
    // significant and must be preserved — we leave the members as written.
    if (form == .in_scope and combiner.law.isCommutative()) {
        std.mem.sort(ExprId, kept[0..kept_n], {}, std.sort.asc(ExprId));
        // I (only when also commutative): collapse duplicates, now adjacent after
        // the sort. We deliberately do NOT dedup an idempotent-but-non-commutative
        // (AUI) combiner: collapsing only *adjacent* duplicates there would be a
        // partial, order-dependent canonicalization, so we conservatively skip it
        // (a missed reuse, never an unsound collision).
        if (combiner.law.isIdempotent()) {
            var w: usize = 0;
            var i: usize = 0;
            while (i < kept_n) : (i += 1) {
                if (w == 0 or kept[w - 1] != kept[i]) {
                    kept[w] = kept[i];
                    w += 1;
                }
            }
            kept_n = w;
        }
    }

    // Every member was a unit ⇒ the whole region is the unit element.
    return (try combiner.build(theorem, kept[0..kept_n])) orelse expr_id;
}
