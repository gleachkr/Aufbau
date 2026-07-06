const std = @import("std");
const ExprId = @import("../../expr.zig").ExprId;
const TheoremContext = @import("../../expr.zig").TheoremContext;
const GlobalEnv = @import("../../env.zig").GlobalEnv;
const RuleDecl = @import("../../env.zig").RuleDecl;
const TermDecl = @import("../../env.zig").TermDecl;
const TemplateExpr = @import("../../rules.zig").TemplateExpr;
const ArgInfo = @import("../../parse_recovery.zig").ArgInfo;
const AssertionKind = @import("../../parse_recovery.zig").AssertionKind;
const RewriteRegistry = @import("../../rewrite_registry.zig").RewriteRegistry;
const StructuralCombiner =
    @import("../../rewrite_registry.zig").StructuralCombiner;

/// Search-side placeholder class.  Stage 1 only uses `.wildcard`, but the
/// helper APIs carry the kind so later stages can replace the factory with
/// the branch-local meta store without changing every call site again.  The
/// canonical definition lives with the store (Stage 2).
pub const MetaKind = @import("./meta_store.zig").MetaKind;

pub const PlaceholderFactory = struct {
    context: ?*anyopaque = null,
    kind: MetaKind = .wildcard,
    makeFn: ?*const fn (
        ?*anyopaque,
        *TheoremContext,
        []const u8,
        MetaKind,
    ) anyerror!ExprId = null,

    pub fn make(
        self: PlaceholderFactory,
        theorem: *TheoremContext,
        sort_name: []const u8,
    ) !ExprId {
        return self.makeKind(theorem, sort_name, self.kind);
    }

    /// Like `make`, but mints with an explicit kind, overriding `self.kind`.
    /// Used by the open walk to mint a bound-class binder as a `.bound_choice`
    /// meta (grounded to an `@vars`-pool dummy) while the rest of the template
    /// defers to the factory's default `.existential` kind.
    pub fn makeKind(
        self: PlaceholderFactory,
        theorem: *TheoremContext,
        sort_name: []const u8,
        kind: MetaKind,
    ) !ExprId {
        if (self.makeFn) |make_fn| {
            return try make_fn(self.context, theorem, sort_name, kind);
        }
        return try theorem.addPlaceholderResolved(sort_name);
    }
};

pub const MissingBinderContext = struct {
    placeholder_factory: PlaceholderFactory = .{},
    /// Optional per-rule-binder cache.  When present, repeated occurrences of
    /// one unresolved binder are rendered as the same logical unknown.  Existing
    /// callers leave this null to preserve the historical fresh-placeholder
    /// behavior for holey inline hints.
    logical_unknowns: ?[]?ExprId = null,
};

pub const TargetPlaceholderMode = enum {
    rigid,
    wildcard,
};

pub const TargetMatchOptions = struct {
    target_placeholders: TargetPlaceholderMode = .rigid,
};

pub fn fillOptionalBindingsForProbe(
    theorem: *TheoremContext,
    rule: *const RuleDecl,
    bindings: []const ?ExprId,
) ![]const ExprId {
    const allocator = theorem.allocator;
    const concrete = try allocator.alloc(ExprId, bindings.len);
    errdefer allocator.free(concrete);
    for (bindings, 0..) |binding, idx| {
        concrete[idx] = binding orelse
            try theorem.addPlaceholderResolved(rule.args[idx].sort_name);
    }
    return concrete;
}

pub fn templateHasUnresolvedBinder(
    template: TemplateExpr,
    bindings: []const ?ExprId,
) bool {
    return switch (template) {
        .binder => |idx| idx >= bindings.len or bindings[idx] == null,
        .app => |app| blk: {
            for (app.args) |arg| {
                if (templateHasUnresolvedBinder(arg, bindings)) {
                    break :blk true;
                }
            }
            break :blk false;
        },
    };
}

pub fn instantiateTemplatePartial(
    theorem: *TheoremContext,
    template: TemplateExpr,
    binders: []const ?ExprId,
) !?ExprId {
    return try instantiateTemplateStrict(theorem, template, binders, true);
}

/// Concrete-only instantiation for search generation.  Returns null when a
/// referenced binder is not present or has not been solved.
pub fn instantiateTemplateConcrete(
    theorem: *TheoremContext,
    template: TemplateExpr,
    binders: []const ?ExprId,
) !?ExprId {
    return try instantiateTemplateStrict(theorem, template, binders, false);
}

fn instantiateTemplateStrict(
    theorem: *TheoremContext,
    template: TemplateExpr,
    binders: []const ?ExprId,
    missing_index_is_error: bool,
) !?ExprId {
    return switch (template) {
        .binder => |idx| blk: {
            if (idx >= binders.len) {
                if (missing_index_is_error) {
                    return error.TemplateBinderOutOfRange;
                }
                break :blk null;
            }
            break :blk binders[idx];
        },
        .app => |app| blk: {
            const args = try theorem.allocator.alloc(ExprId, app.args.len);
            errdefer theorem.allocator.free(args);
            for (app.args, 0..) |arg, idx| {
                args[idx] = (try instantiateTemplateStrict(
                    theorem,
                    arg,
                    binders,
                    missing_index_is_error,
                )) orelse {
                    theorem.allocator.free(args);
                    break :blk null;
                };
            }
            break :blk try theorem.interner.internAppOwned(app.term_id, args);
        },
    };
}

/// Like `instantiateTemplatePartial`, but open binders are rendered as
/// sort-typed placeholders.  If an ACUI structural-combiner subtree contains an
/// open binder, the whole subtree is collapsed to one wildcard placeholder; a
/// wildcard summand inside a structural combiner would make later context
/// splitting ambiguous.
pub fn instantiateTemplateHoley(
    theorem: *TheoremContext,
    env: *const GlobalEnv,
    registry: *const RewriteRegistry,
    rule: *const RuleDecl,
    template: TemplateExpr,
    binders: []const ?ExprId,
    missing: MissingBinderContext,
) !?ExprId {
    var state = missing;
    return try instantiateTemplateHoleyState(
        theorem,
        env,
        registry,
        rule,
        template,
        binders,
        &state,
    );
}

fn instantiateTemplateHoleyState(
    theorem: *TheoremContext,
    env: *const GlobalEnv,
    registry: *const RewriteRegistry,
    rule: *const RuleDecl,
    template: TemplateExpr,
    binders: []const ?ExprId,
    missing: *MissingBinderContext,
) !?ExprId {
    return switch (template) {
        .binder => |idx| blk: {
            if (idx >= binders.len) return error.TemplateBinderOutOfRange;
            if (binders[idx]) |expr| break :blk expr;
            break :blk try unresolvedBinderExpr(theorem, rule, idx, missing);
        },
        .app => |app| blk: {
            if (registry.hasStructuralCombiner(app.term_id) and
                app.term_id < env.terms.items.len and
                templateHasUnresolvedBinder(template, binders))
            {
                break :blk try missing.placeholder_factory.make(
                    theorem,
                    env.terms.items[app.term_id].ret_sort_name,
                );
            }
            const args = try theorem.allocator.alloc(ExprId, app.args.len);
            errdefer theorem.allocator.free(args);
            for (app.args, 0..) |arg, idx| {
                args[idx] = (try instantiateTemplateHoleyState(
                    theorem,
                    env,
                    registry,
                    rule,
                    arg,
                    binders,
                    missing,
                )) orelse {
                    theorem.allocator.free(args);
                    break :blk null;
                };
            }
            break :blk try theorem.interner.internAppOwned(app.term_id, args);
        },
    };
}

fn unresolvedBinderExpr(
    theorem: *TheoremContext,
    rule: *const RuleDecl,
    idx: usize,
    missing: *MissingBinderContext,
) !ExprId {
    if (idx >= rule.args.len) return error.TemplateBinderOutOfRange;
    if (missing.logical_unknowns) |unknowns| {
        if (idx >= unknowns.len) return error.TemplateBinderOutOfRange;
        if (unknowns[idx]) |expr| return expr;
        const expr = try missing.placeholder_factory.make(
            theorem,
            rule.args[idx].sort_name,
        );
        unknowns[idx] = expr;
        return expr;
    }
    return try missing.placeholder_factory.make(theorem, rule.args[idx].sort_name);
}

/// Stage 4 open-target instantiation (META.md "structured open backward
/// generation").  Like the holey instantiation, but kind/policy-aware:
///
/// - an unresolved binder becomes one shared existential meta per binder
///   (the `logical_unknowns` cache), minted through `factory`;
/// - an unresolved *bound-class* binder defers to a `.bound_choice` meta
///   (it needs a variable witness, not an arbitrary term): a structurally-
///   constrained leaf the carry-to-leaf match forces, or the phase-3 `@vars`
///   pool invention grounds when the witness is genuinely free. It is opened in
///   place even inside an ACUI-combiner subtree (never collapsed into one meta).
/// - an unresolved binder marked `excluded` (recover-owned: its recover law
///   could not fire) also fails the instantiation, never falls back to a
///   bare meta;
/// - an ACUI structural-combiner subtree containing an unresolved binder
///   collapses to a single whole-context meta only when *every* such binder is a
///   plain context-split binder. If any is excluded/out-of-range the walk fails
///   (`templateHasExcludedUnresolvedBinder`); if any is *openable* — bound-class
///   or a subterm conclusion binder — the subtree is opened in place,
///   per-binder, preserving the combiner structure
///   (`templateHasOpenableUnresolvedBinder`).
pub const OpenInstantiateOptions = struct {
    factory: PlaceholderFactory,
    /// Per-binder shared unknowns; repeated occurrences of one binder reuse
    /// the same meta leaf. Length must cover every binder index used.
    logical_unknowns: []?ExprId,
    /// Recover-owned binder indices (in the same binder space as
    /// `arg_infos`); an unresolved excluded binder fails the walk.
    excluded: ?[]const bool = null,
    /// Bitmask of binder indices that occur in the rule's (advertised)
    /// conclusion. Such a binder is *determined* by matching the conclusion
    /// against the goal, so it must be pinned before instantiation — never
    /// deferred as a fresh meta (per-binder or via the whole-context collapse).
    /// Only binders absent from the conclusion are genuine `@auto backward`
    /// witnesses (e.g. `rex`'s `t`, which appears only in the hypothesis) and
    /// may be deferred. An unresolved conclusion binder fails the walk, exactly
    /// like a bound-class or recover-owned one, so an over-general application
    /// (`rim` on a goal that pins neither its principal nor its rest) is
    /// abandoned rather than fabricating a `?g ⊢ ?d` goal that matches the whole
    /// ref pool. Zero (the default) restricts nothing; indices ≥ 64 are not
    /// represented and fall back to the prior deferral behaviour.
    ///
    /// Kept separate from `excluded` (same fail-the-walk effect) rather than
    /// folded in: `excluded` is a per-binder slice the view machinery owns
    /// (recover-owned binders); this is a mask the caller derives from the
    /// conclusion template. Different provenance, different representation.
    conclusion_binders: u64 = 0,
    /// When set, an openable (bound-class / subterm-conclusion) binder inside an
    /// ACUI structural combiner is opened *in place* — preserving the combiner
    /// structure for the open-path readback — instead of hard-blocking the walk.
    /// Set only on the constrained-MP / non-`@auto`-backward path (eliminators
    /// like `nat_ind_elim`, whose step context `join(join(g,k:Nat),ih:C)` must
    /// open `ih`). Left false on the `@auto`-backward witness path, which
    /// resolves such binders through force-first / enumeration instead.
    open_bound_in_combiner: bool = false,
    arg_infos: []const ArgInfo,
};

inline fn isConclusionBinder(options: *const OpenInstantiateOptions, idx: usize) bool {
    // `idx < 64` is load-bearing, not just a fast path: it guards the `@intCast`
    // shift amount (index ≥ 64 would be an illegal cast). The mask never holds a
    // bit ≥ 64 anyway (`conclusionBinderMaskOrNone` returns 0 on overflow), so
    // short-circuiting is also the correct unrestricted answer for those.
    return idx < 64 and (options.conclusion_binders & (@as(u64, 1) << @intCast(idx))) != 0;
}

pub fn instantiateTemplateOpen(
    theorem: *TheoremContext,
    env: *const GlobalEnv,
    registry: *const RewriteRegistry,
    template: TemplateExpr,
    binders: []const ?ExprId,
    options: *OpenInstantiateOptions,
) anyerror!?ExprId {
    return instantiateTemplateOpenInner(
        theorem,
        env,
        registry,
        template,
        binders,
        options,
        true,
    );
}

// `top_level` is true only for the whole hypothesis template; recursive
// app-argument calls pass false. See the conclusion-binder check below.
fn instantiateTemplateOpenInner(
    theorem: *TheoremContext,
    env: *const GlobalEnv,
    registry: *const RewriteRegistry,
    template: TemplateExpr,
    binders: []const ?ExprId,
    options: *OpenInstantiateOptions,
    top_level: bool,
) anyerror!?ExprId {
    return switch (template) {
        .binder => |idx| blk: {
            if (idx >= binders.len or idx >= options.arg_infos.len) {
                return error.TemplateBinderOutOfRange;
            }
            if (binders[idx]) |expr| break :blk expr;
            if (options.excluded) |mask| {
                if (idx < mask.len and mask[idx]) break :blk null;
            }
            // A bound-class binder is a hidden quantifier witness: it needs a
            // *variable* (theorem-local dummy from an `@vars` pool), not an
            // arbitrary term. It defers to a `.bound_choice` meta — a
            // structurally-constrained leaf like `P ?x` that the leaf match
            // forces (carry-to-leaf) or, when the witness is genuinely free
            // (e.g. `bound_choice_use {x} : P x > B`), the phase-3 invention
            // pass grounds to a pool dummy. It is kept after the `excluded`
            // check (a recover-owned bound binder still fails) and is opened in
            // place inside an ACUI combiner rather than collapsed into a
            // whole-context meta (see `templateHasOpenableUnresolvedBinder` in
            // the `.app` case below).
            const bound = options.arg_infos[idx].bound;
            // A conclusion binder that *is* the whole hypothesis would become a
            // whole-formula meta matching every fact in the pool, so it must be
            // pinned by the goal match, never fabricated. But a conclusion binder
            // in a subterm position (e.g. `x` inside `child_from_mark`'s hyp
            // `M x`, whose conclusion is `N x`) yields a structurally-constrained
            // meta that legitimately shares with the goal's inherited meta and
            // carries to a leaf — so it stays deferrable. Whole-*context* metas
            // under structural combiners collapse only when no openable binder
            // is present; see `templateHasOpenableUnresolvedBinder` in the
            // `.app` case below.
            if (top_level and isConclusionBinder(options, idx)) break :blk null;
            if (idx >= options.logical_unknowns.len) {
                return error.TemplateBinderOutOfRange;
            }
            if (options.logical_unknowns[idx]) |existing| break :blk existing;
            const meta = try options.factory.makeKind(
                theorem,
                options.arg_infos[idx].sort_name,
                if (bound) .bound_choice else options.factory.kind,
            );
            options.logical_unknowns[idx] = meta;
            break :blk meta;
        },
        .app => |app| blk: {
            if (registry.hasStructuralCombiner(app.term_id) and
                app.term_id < env.terms.items.len and
                templateHasUnresolvedBinder(template, binders))
            {
                // An excluded (recover-owned) or out-of-range binder inside the
                // combiner must hard-fail the branch — it can be neither opened
                // nor collapsed into a whole-context meta.
                if (templateHasExcludedUnresolvedBinder(
                    template,
                    binders,
                    options,
                )) break :blk null;
                // An *openable* binder (bound-class, or a conclusion binder in
                // this subterm position) inside the combiner. When
                // `open_bound_in_combiner` is set (the constrained-MP /
                // non-`@auto`-backward path that reaches an eliminator like
                // `nat_ind_elim`), open it in place — minted as a
                // `.bound_choice`/meta leaf by the `.binder` arm below — so the
                // combiner structure (e.g. the step's context
                // `join(join(g, k:Nat), ih:C)`) is preserved for the open-path
                // readback. Otherwise (the `@auto`-backward witness path, e.g.
                // `drinker`/`fan_in`) keep the prior hard-block: those rules
                // resolve their witnesses through the force-first / enumeration
                // machinery, which the block routes to, and opening in place
                // would derail it.
                const openable = templateHasOpenableUnresolvedBinder(
                    template,
                    binders,
                    options,
                );
                if (openable and !options.open_bound_in_combiner) break :blk null;
                // Only when every unresolved binder is a plain context-split
                // binder do we collapse the whole subtree to one context meta (a
                // per-binder split there would make later context splitting
                // ambiguous).
                if (!openable) break :blk try options.factory.make(
                    theorem,
                    env.terms.items[app.term_id].ret_sort_name,
                );
                // else (openable and allowed): fall through to open in place.
            }
            const args = try theorem.allocator.alloc(ExprId, app.args.len);
            errdefer theorem.allocator.free(args);
            for (app.args, 0..) |arg, idx| {
                args[idx] = (try instantiateTemplateOpenInner(
                    theorem,
                    env,
                    registry,
                    arg,
                    binders,
                    options,
                    false,
                )) orelse {
                    theorem.allocator.free(args);
                    break :blk null;
                };
            }
            break :blk try theorem.interner.internAppOwned(app.term_id, args);
        },
    };
}

/// True when the combiner subtree holds an unresolved binder that must
/// hard-fail the open walk: a recover-owned (`excluded`) binder whose recover
/// law could not fire, or an out-of-range binder. Such a binder can be neither
/// opened in place nor collapsed into a whole-context meta.
fn templateHasExcludedUnresolvedBinder(
    template: TemplateExpr,
    binders: []const ?ExprId,
    options: *const OpenInstantiateOptions,
) bool {
    switch (template) {
        .binder => |idx| {
            if (idx >= binders.len) return true;
            if (binders[idx] != null) return false;
            if (idx >= options.arg_infos.len) return true;
            if (options.excluded) |mask| {
                if (idx < mask.len and mask[idx]) return true;
            }
            return false;
        },
        .app => |app| {
            for (app.args) |arg| {
                if (templateHasExcludedUnresolvedBinder(
                    arg,
                    binders,
                    options,
                )) return true;
            }
            return false;
        },
    }
}

/// True when the combiner subtree holds an unresolved binder that should be
/// opened *in place* — preserving the combiner structure — rather than
/// collapsed into one whole-context meta: a bound-class binder (a hidden
/// quantifier witness, opened as a `.bound_choice` meta) or a conclusion binder
/// in this subterm position (a structurally-constrained meta that legitimately
/// carries to a leaf). Assumes the subtree has already passed
/// `templateHasExcludedUnresolvedBinder`.
fn templateHasOpenableUnresolvedBinder(
    template: TemplateExpr,
    binders: []const ?ExprId,
    options: *const OpenInstantiateOptions,
) bool {
    switch (template) {
        .binder => |idx| {
            if (idx >= binders.len) return false;
            if (binders[idx] != null) return false;
            if (idx >= options.arg_infos.len) return false;
            if (options.arg_infos[idx].bound) return true;
            if (isConclusionBinder(options, idx)) return true;
            return false;
        },
        .app => |app| {
            for (app.args) |arg| {
                if (templateHasOpenableUnresolvedBinder(
                    arg,
                    binders,
                    options,
                )) return true;
            }
            return false;
        },
    }
}

/// Conservative structured-target guard for future open-goal search.  A bare
/// unresolved binder is not structured; an application head is.
pub fn templateHasConcreteHead(
    template: TemplateExpr,
    binders: []const ?ExprId,
) bool {
    return switch (template) {
        .app => true,
        .binder => |idx| idx < binders.len and binders[idx] != null,
    };
}

pub fn exprHasConcreteHead(
    theorem: *const TheoremContext,
    expr_id: ExprId,
) bool {
    return switch (theorem.interner.node(expr_id).*) {
        .app => true,
        .variable, .placeholder => false,
    };
}

/// Match a rule template against a target expression.  In wildcard-target mode,
/// placeholders in the target are don't-care leaves and do not bind rule
/// binders.  This is intentionally separate from `TheoremContext.matchTemplate`,
/// whose binder case always writes into `bindings`.
pub fn matchTemplateToTarget(
    theorem: *const TheoremContext,
    template: TemplateExpr,
    target: ExprId,
    bindings: []?ExprId,
    options: TargetMatchOptions,
) bool {
    if (options.target_placeholders == .wildcard) {
        switch (theorem.interner.node(target).*) {
            .placeholder => return true,
            .variable, .app => {},
        }
    }
    return switch (template) {
        .binder => |idx| blk: {
            if (idx >= bindings.len) break :blk false;
            if (bindings[idx]) |existing| {
                break :blk existing == target;
            }
            bindings[idx] = target;
            break :blk true;
        },
        .app => |app| blk: {
            const node = theorem.interner.node(target);
            const target_app = switch (node.*) {
                .app => |concrete| concrete,
                .variable, .placeholder => break :blk false,
            };
            if (target_app.term_id != app.term_id) break :blk false;
            if (target_app.args.len != app.args.len) break :blk false;
            for (app.args, target_app.args) |tmpl_arg, target_arg| {
                if (!matchTemplateToTarget(
                    theorem,
                    tmpl_arg,
                    target_arg,
                    bindings,
                    options,
                )) break :blk false;
            }
            break :blk true;
        },
    };
}

fn argInfo(sort_name: []const u8) ArgInfo {
    return .{ .sort_name = sort_name, .bound = false, .deps = 0 };
}

fn appendTerm(env: *GlobalEnv, name: []const u8, ret_sort: []const u8) !u32 {
    const id: u32 = @intCast(env.terms.items.len);
    try env.terms.append(env.allocator, TermDecl{
        .name = name,
        .args = &.{},
        .arg_names = &.{},
        .dummy_args = &.{},
        .dummy_names = &.{},
        .ret_sort_name = ret_sort,
        .is_def = false,
        .body = null,
    });
    try env.term_names.put(name, id);
    return id;
}

fn tmplApp(term_id: u32, args: []const TemplateExpr) TemplateExpr {
    return .{ .app = .{ .term_id = term_id, .args = args } };
}

fn testRule(args: []const ArgInfo, concl: TemplateExpr) RuleDecl {
    return .{
        .name = "r",
        .args = args,
        .arg_names = &.{},
        .hyps = &.{},
        .concl = concl,
        .kind = AssertionKind.axiom,
        .is_local = false,
    };
}

test "partial instantiation returns null for missing binder" {
    var theorem = TheoremContext.init(std.testing.allocator);
    defer theorem.deinit();
    try theorem.seedBinderCount(1);

    const bindings = [_]?ExprId{ theorem.theorem_vars.items[0], null };
    const result = try instantiateTemplatePartial(
        &theorem,
        .{ .binder = 1 },
        &bindings,
    );
    try std.testing.expect(result == null);
}

test "holey instantiation preserves concrete structure" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();

    var env = GlobalEnv.init(allocator);
    var registry = RewriteRegistry.init(allocator);
    const f = try appendTerm(&env, "f", "wff");
    var theorem = TheoremContext.init(std.testing.allocator);
    defer theorem.deinit();
    try theorem.seedBinderCount(1);

    const args = [_]ArgInfo{ argInfo("obj"), argInfo("obj") };
    const tmpl_args = [_]TemplateExpr{ .{ .binder = 0 }, .{ .binder = 1 } };
    const template = tmplApp(f, &tmpl_args);
    const rule = testRule(&args, template);
    const bindings = [_]?ExprId{ theorem.theorem_vars.items[0], null };

    const result = (try instantiateTemplateHoley(
        &theorem,
        &env,
        &registry,
        &rule,
        template,
        &bindings,
        .{},
    )) orelse return error.ExpectedHoleyInstantiation;
    const node = theorem.interner.node(result).*;
    const result_app = switch (node) {
        .app => |a| a,
        else => return error.ExpectedApp,
    };
    try std.testing.expectEqual(f, result_app.term_id);
    try std.testing.expectEqual(theorem.theorem_vars.items[0], result_app.args[0]);
    try std.testing.expectEqual(@as(usize, 1), theorem.theorem_placeholders.items.len);
}

test "unresolved binder under ACUI combiner collapses to whole wildcard" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();

    var env = GlobalEnv.init(allocator);
    var registry = RewriteRegistry.init(allocator);
    const comma = try appendTerm(&env, "comma", "ctx");
    try registry.acui_by_head.put(comma, StructuralCombiner{
        .unit_term_name = "emp",
        .assoc_name = "comma_assoc",
        .comm_name = "comma_comm",
        .idem_name = "comma_idem",
    });
    var theorem = TheoremContext.init(std.testing.allocator);
    defer theorem.deinit();
    try theorem.seedBinderCount(1);

    const args = [_]ArgInfo{ argInfo("ctx"), argInfo("ctx") };
    const tmpl_args = [_]TemplateExpr{ .{ .binder = 0 }, .{ .binder = 1 } };
    const template = tmplApp(comma, &tmpl_args);
    const rule = testRule(&args, template);
    const bindings = [_]?ExprId{ theorem.theorem_vars.items[0], null };

    const result = (try instantiateTemplateHoley(
        &theorem,
        &env,
        &registry,
        &rule,
        template,
        &bindings,
        .{},
    )) orelse return error.ExpectedHoleyInstantiation;
    try std.testing.expectEqual(@as(usize, 1), theorem.theorem_placeholders.items.len);
    try std.testing.expectEqual(
        @as(u32, 0),
        theorem.interner.node(result).*.placeholder,
    );
}

test "wildcard target matching binds no rule binders" {
    var theorem = TheoremContext.init(std.testing.allocator);
    defer theorem.deinit();
    const target = try theorem.addPlaceholderResolved("obj");
    var bindings = [_]?ExprId{null};

    try std.testing.expect(matchTemplateToTarget(
        &theorem,
        .{ .binder = 0 },
        target,
        &bindings,
        .{ .target_placeholders = .wildcard },
    ));
    try std.testing.expect(bindings[0] == null);
}

test "repeated unresolved binder can share one logical unknown" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();

    var env = GlobalEnv.init(allocator);
    var registry = RewriteRegistry.init(allocator);
    const f = try appendTerm(&env, "pair", "obj");
    var theorem = TheoremContext.init(std.testing.allocator);
    defer theorem.deinit();

    const args = [_]ArgInfo{argInfo("obj")};
    const tmpl_args = [_]TemplateExpr{ .{ .binder = 0 }, .{ .binder = 0 } };
    const template = tmplApp(f, &tmpl_args);
    const rule = testRule(&args, template);
    const bindings = [_]?ExprId{null};
    var unknowns = [_]?ExprId{null};

    const result = (try instantiateTemplateHoley(
        &theorem,
        &env,
        &registry,
        &rule,
        template,
        &bindings,
        .{ .logical_unknowns = &unknowns },
    )) orelse return error.ExpectedHoleyInstantiation;
    const result_app = theorem.interner.node(result).*.app;
    try std.testing.expectEqual(result_app.args[0], result_app.args[1]);
    try std.testing.expectEqual(@as(usize, 1), theorem.theorem_placeholders.items.len);
}
