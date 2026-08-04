//! `conversion?` driver: seed an egraph from the goal line and the
//! reference pool, saturate the `@conversion` rules, and — when the goal is
//! convertible to a pool formula — lower the extracted explanation into
//! ordinary proof lines (rule instance + `@congr` lifting + `refl`/`trans`/
//! `symm` chaining + a final `transport` citing the pool ref). See
//! `docs/design_notes/conversion_egraph.md`.
//!
//! Everything here is per-search-call and allocated on the caller's work
//! arena; nothing outlives the call except the copied-out replacement text.

const std = @import("std");
const egraph = @import("./egraph.zig");
const types = @import("./types.zig");
const Refs = @import("./refs.zig");
const ProofScript = @import("../../proof_script.zig");
const expr_mod = @import("../../expr.zig");
const ExprId = expr_mod.ExprId;
const VarId = expr_mod.VarId;
const TheoremContext = expr_mod.TheoremContext;
const ViewTrace = @import("../../view_trace.zig");
const rewrite_registry = @import("../../rewrite_registry.zig");
const ResolvedRelation = rewrite_registry.ResolvedRelation;
const TemplateExpr = @import("../../rules.zig").TemplateExpr;
const GlobalEnv = @import("../../env.zig").GlobalEnv;
const Context = types.Context;
const NameExprMap = types.NameExprMap;
const Lowerer = @import("./conversion/lowerer.zig").Lowerer;

/// The certificates backing one AC-absorbed operator: the `@conversion
/// comm`/`assoc` theorems the lowering cites for re-treeing chains.
pub const AcCert = struct {
    comm_rule_id: u32,
    assoc_rule_id: u32,
    /// True when the assoc certificate's conclusion reads
    /// `rel(t(t(a,b), c), t(a, t(b,c)))` — left-nested match side.
    assoc_forward: bool,
};

pub const AcCertMap = std.AutoArrayHashMapUnmanaged(u32, AcCert);

/// Assemble per-head AC policies: a head absorbed into bag interning needs
/// both certificates and a `@congr` rule (extraction lifts through bag
/// positions with it). Heads with only one certificate keep saturating.
fn buildAcCerts(
    work: std.mem.Allocator,
    context: *const Context,
) !AcCertMap {
    const Partial = struct {
        comm: ?u32 = null,
        assoc: ?u32 = null,
        assoc_forward: bool = true,
    };
    var partial: std.AutoArrayHashMapUnmanaged(u32, Partial) = .{};
    for (context.registry.conversionRules()) |conv| {
        if (conv.role == .none) continue;
        const head = conv.head_term_id orelse continue;
        const gop = try partial.getOrPut(work, head);
        if (!gop.found_existing) gop.value_ptr.* = .{};
        switch (conv.role) {
            .comm => gop.value_ptr.comm = conv.rule_id,
            .assoc => {
                gop.value_ptr.assoc = conv.rule_id;
                // Left-nested lhs = the certificate's forward direction.
                gop.value_ptr.assoc_forward = conv.lhs == .app and
                    conv.lhs.app.args[0] == .app;
            },
            .none => unreachable,
        }
    }
    var certs: AcCertMap = .{};
    var it = partial.iterator();
    while (it.next()) |entry| {
        const head = entry.key_ptr.*;
        const p = entry.value_ptr.*;
        if (p.comm == null or p.assoc == null) continue;
        if (!context.registry.congr_by_head.contains(head)) continue;
        try certs.put(work, head, .{
            .comm_rule_id = p.comm.?,
            .assoc_rule_id = p.assoc.?,
            .assoc_forward = p.assoc_forward,
        });
    }
    return certs;
}

pub const Options = struct {
    max_iterations: usize = 16,
    max_nodes: usize = 10_000,
};

/// Def rules tag their egraph `Rule.rule_id` with the high bit so the
/// lowering can tell a definition step (one `refl` line the checker closes
/// through transparent unfolding) from a theorem citation. Theorem rule ids
/// index `env.rules` and never reach the bit.
pub const def_rule_tag: u32 = 1 << 31;

/// The enrolled def's term id, when `rule_id` carries the def tag.
pub fn defRuleTermId(rule_id: u32) ?u32 {
    if (rule_id & def_rule_tag == 0) return null;
    return rule_id & ~def_rule_tag;
}

pub const Result = struct {
    /// Full replacement text for the placeholder line's span (the emitted
    /// chain lines plus the transported goal line), or null on a miss.
    replacement: ?[]const u8 = null,
    /// The cited reference's source text (`#N` or a line label) on success.
    via: ?[]const u8 = null,
    /// A pool formula shares the goal's e-class, but no proof chain could
    /// be extracted or lowered from it. Keeps the failure report honest: a
    /// saturated outcome with this flag set is NOT a forced negative.
    convertible_unlowered: bool = false,
    stats: egraph.SaturateStats = .{ .outcome = .saturated },
    pool_size: usize = 0,
    rule_count: usize = 0,
    /// Pool entries of shape `rel(lhs, rhs)` enrolled as ground unions.
    pool_equations: usize = 0,
    /// Operators absorbed into bag interning (both role certificates
    /// plus @congr coverage). Their laws are representational, so they
    /// keep the search alive even with zero enrolled rules.
    ac_heads: usize = 0,
    /// Operators holding at least one role certificate that did NOT
    /// absorb (missing the partner law or @congr); their certificates
    /// enroll as ordinary both-way rewrites.
    partial_ac_heads: usize = 0,
    /// The found chain (or a seam of it) outgrew the lowering's emission
    /// caps; the conversion is proven, the proof text was abandoned.
    lower_capped: bool = false,
    /// `@compute` orientations enrolled for the directed fold. Nonzero
    /// means a saturated miss is NOT a forced negative: the fold reduces
    /// each redex once in declaration order and never explores
    /// alternative reduction orders.
    compute_rule_count: usize = 0,
    /// The goal line itself asserts `rel(lhs, rhs)`: its sides were seeded
    /// as standalone terms, and joining their classes proves the line with
    /// no pool reference (`via` stays null on that path).
    equation_goal: bool = false,
    classes: usize = 0,
    nodes: usize = 0,
};

pub fn run(
    work: std.mem.Allocator,
    context: *const Context,
    theorem: *TheoremContext,
    theorem_vars: *const NameExprMap,
    goal: ExprId,
    proof_src: []const u8,
    block_lines: []const ProofScript.ProofLine,
    target_line: ProofScript.ProofLine,
    opts: Options,
) !Result {
    var result = Result{};

    // Heads certified assoc+comm absorb those laws into bag interning;
    // their certificate theorems are cited by the lowering instead of
    // being enrolled for saturation.
    var ac_certs = try buildAcCerts(work, context);

    // Rules: one egraph orientation per enrolled direction, declaration
    // order (deterministic). Bound-binder slots and dep restrictions are
    // shared by both orientations; the dep gate uses them to admit only
    // matches the verifier's disjointness conditions can accept.
    var rules: std.ArrayListUnmanaged(egraph.Rule) = .{};
    for (context.registry.conversionRules()) |conv| {
        if (conv.role != .none) {
            const head = conv.head_term_id orelse continue;
            if (ac_certs.contains(head)) continue;
        }
        const decl = &context.env.rules.items[conv.rule_id];
        var bound_slots: std.ArrayListUnmanaged(u32) = .{};
        var restrictions: std.ArrayListUnmanaged(egraph.Restriction) = .{};
        var bound_ordinal: u6 = 0;
        for (decl.args, 0..) |arg, slot| {
            if (!arg.bound) continue;
            try bound_slots.append(work, @intCast(slot));
            for (decl.args, 0..) |term_arg, term_slot| {
                if (term_arg.bound) continue;
                if ((term_arg.deps >> bound_ordinal) & 1 == 0) {
                    try restrictions.append(work, .{
                        .bound_slot = @intCast(slot),
                        .term_slot = @intCast(term_slot),
                    });
                }
            }
            bound_ordinal += 1;
        }
        if (conv.ltr) try rules.append(work, .{
            .rule_id = conv.rule_id,
            .reversed = false,
            .match_side = conv.lhs,
            .target_side = conv.rhs,
            .num_binders = conv.num_binders,
            .bound_slots = bound_slots.items,
            .restrictions = restrictions.items,
        });
        if (conv.rtl) try rules.append(work, .{
            .rule_id = conv.rule_id,
            .reversed = true,
            .match_side = conv.rhs,
            .target_side = conv.lhs,
            .num_binders = conv.num_binders,
            .bound_slots = bound_slots.items,
            .restrictions = restrictions.items,
        });
    }
    // Enrolled defs: the def's own equation `rel(definiens, head args)` as
    // an ordinary rule (`fold` matches the definiens, `unfold` the head).
    // The binder space is the def's args followed by its hidden dummies;
    // each dummy slot is a bound slot whose freshness against every term
    // arg rides the same restriction machinery as theorem dep conditions
    // (an arg is declared before the dummies exist, so no dep bit can
    // license an occurrence).
    for (context.registry.defConversionRules()) |def_conv| {
        if (def_conv.term_id & def_rule_tag != 0) continue;
        const decl = &context.env.terms.items[def_conv.term_id];
        var bound_slots: std.ArrayListUnmanaged(u32) = .{};
        var restrictions: std.ArrayListUnmanaged(egraph.Restriction) = .{};
        var bound_ordinal: u6 = 0;
        for (decl.args, 0..) |arg, slot| {
            if (!arg.bound) continue;
            try bound_slots.append(work, @intCast(slot));
            for (decl.args, 0..) |term_arg, term_slot| {
                if (term_arg.bound) continue;
                if ((term_arg.deps >> bound_ordinal) & 1 == 0) {
                    try restrictions.append(work, .{
                        .bound_slot = @intCast(slot),
                        .term_slot = @intCast(term_slot),
                    });
                }
            }
            bound_ordinal += 1;
        }
        for (0..decl.dummy_args.len) |dummy_idx| {
            const slot: u32 = @intCast(decl.args.len + dummy_idx);
            try bound_slots.append(work, slot);
            for (decl.args, 0..) |term_arg, term_slot| {
                if (term_arg.bound) continue;
                try restrictions.append(work, .{
                    .bound_slot = slot,
                    .term_slot = @intCast(term_slot),
                });
            }
        }
        const tag = def_rule_tag | def_conv.term_id;
        if (def_conv.fold) try rules.append(work, .{
            .rule_id = tag,
            .reversed = false,
            .match_side = def_conv.lhs,
            .target_side = def_conv.rhs,
            .num_binders = def_conv.num_binders,
            .bound_slots = bound_slots.items,
            .restrictions = restrictions.items,
        });
        if (def_conv.unfold) try rules.append(work, .{
            .rule_id = tag,
            .reversed = true,
            .match_side = def_conv.rhs,
            .target_side = def_conv.lhs,
            .num_binders = def_conv.num_binders,
            .bound_slots = bound_slots.items,
            .restrictions = restrictions.items,
        });
    }
    // `@compute` rules: one orientation each, flagged for the egraph's
    // directed fold scheduler instead of general saturation. Bound-binder
    // slots and dep restrictions ride the same machinery as general
    // rules; the fold's shared apply path runs the same dep gate, and a
    // dep-deferred designated redex stays unconsumed.
    for (context.registry.computeRules()) |comp| {
        const decl = &context.env.rules.items[comp.rule_id];
        var bound_slots: std.ArrayListUnmanaged(u32) = .{};
        var restrictions: std.ArrayListUnmanaged(egraph.Restriction) = .{};
        var bound_ordinal: u6 = 0;
        for (decl.args, 0..) |arg, slot| {
            if (!arg.bound) continue;
            try bound_slots.append(work, @intCast(slot));
            for (decl.args, 0..) |term_arg, term_slot| {
                if (term_arg.bound) continue;
                if ((term_arg.deps >> bound_ordinal) & 1 == 0) {
                    try restrictions.append(work, .{
                        .bound_slot = @intCast(slot),
                        .term_slot = @intCast(term_slot),
                    });
                }
            }
            bound_ordinal += 1;
        }
        try rules.append(work, .{
            .rule_id = comp.rule_id,
            .reversed = comp.rtl,
            .match_side = if (comp.ltr) comp.lhs else comp.rhs,
            .target_side = if (comp.ltr) comp.rhs else comp.lhs,
            .num_binders = comp.num_binders,
            .bound_slots = bound_slots.items,
            .restrictions = restrictions.items,
            .compute = true,
        });
    }
    result.compute_rule_count = context.registry.computeRules().len;
    result.rule_count = rules.items.len;
    result.ac_heads = ac_certs.count();
    {
        var partial: std.AutoArrayHashMapUnmanaged(u32, void) = .{};
        for (context.registry.conversionRules()) |conv| {
            if (conv.role == .none) continue;
            const head = conv.head_term_id orelse continue;
            if (ac_certs.contains(head)) continue;
            try partial.put(work, head, {});
        }
        result.partial_ac_heads = partial.count();
    }

    var eg = egraph.EGraph.init(work);
    // The congruence gate: only heads with a `@congr` proof step may drive
    // congruence unions. Set semantics, so hash-map iteration order is fine.
    var congr_it = context.registry.congr_by_head.keyIterator();
    while (congr_it.next()) |head| {
        try eg.congr_heads.put(work, head.*, {});
    }
    for (ac_certs.keys()) |head| {
        try eg.ac_heads.put(work, head, {});
    }
    // Bound-position masks for every term with bound args.
    for (context.env.terms.items, 0..) |term, term_id| {
        var mask: u64 = 0;
        for (term.args, 0..) |arg, idx| {
            if (arg.bound and idx < 64) mask |= @as(u64, 1) << @intCast(idx);
        }
        if (mask != 0) {
            try eg.bound_masks.put(work, @intCast(term_id), mask);
        }
    }
    // Declared leaf dependencies: a theorem variable `(m: tm y)` depends
    // on the bound binder y with no structural occurrence the egraph
    // could see, so the dep gate's and extraction's avoidability checks
    // consult these masks. Dep bits index bound binders in declaration
    // order, same convention as the rule restrictions above.
    {
        var bound_leaves: std.ArrayListUnmanaged(egraph.LeafId) = .{};
        for (theorem.arg_infos, 0..) |arg, idx| {
            if (!arg.bound) continue;
            try bound_leaves.append(
                work,
                leafIdFor(.{ .theorem_var = @intCast(idx) }),
            );
        }
        for (theorem.arg_infos, 0..) |arg, idx| {
            if (arg.bound or arg.deps == 0) continue;
            var deps: std.ArrayListUnmanaged(egraph.LeafId) = .{};
            for (bound_leaves.items, 0..) |leaf, ordinal| {
                if ((arg.deps >> @intCast(ordinal)) & 1 != 0) {
                    try deps.append(work, leaf);
                }
            }
            if (deps.items.len == 0) continue;
            try eg.leaf_deps.put(
                work,
                leafIdFor(.{ .theorem_var = @intCast(idx) }),
                deps.items,
            );
        }
    }
    // Registered relation heads: pool entries with one of these at the top
    // are proven `rel(lhs, rhs)` facts whose sides may be unioned. Set
    // semantics, so hash-map iteration order is fine.
    var rel_heads: std.AutoArrayHashMapUnmanaged(u32, void) = .{};
    var sort_it = context.registry.relations.keyIterator();
    while (sort_it.next()) |sort_name| {
        const relation = context.registry.resolveRelation(
            context.env,
            sort_name.*,
        ) orelse continue;
        try rel_heads.put(work, relation.rel_term_id, {});
    }

    const goal_term = (try addExpr(&eg, context.env, theorem, goal)) orelse {
        return result;
    };

    // Equation goals: when the goal line itself asserts `rel(lhs, rhs)`,
    // its sides double as standalone seed terms (they are already subterms
    // of the goal seed, so this adds no nodes). If saturation joins their
    // classes the line is provable with no pool reference at all. The
    // sides are never unioned up front — that would assume the goal.
    const eq_sides = goalEqSides(theorem, goal, &rel_heads, goal_term);
    result.equation_goal = eq_sides != null;

    const pool = try Refs.buildReferencePool(work, context, theorem);
    result.pool_size = pool.len;
    var pool_terms = try work.alloc(?*const egraph.Term, pool.len);
    var pool_exprs = try work.alloc(?ExprId, pool.len);
    for (pool, 0..) |entry, idx| {
        const expr = Refs.sourceRefExpr(context, theorem, entry.ref) catch {
            pool_terms[idx] = null;
            pool_exprs[idx] = null;
            continue;
        };
        pool_exprs[idx] = expr;
        pool_terms[idx] = try addExpr(&eg, context.env, theorem, expr);
    }

    // Local equations: a pool entry shaped `rel(lhs, rhs)` is itself a
    // proof that its sides convert, so union them up front. These ground
    // unions participate in congruence closure from the first rebuild and
    // lower as direct citations of the entry (`simp [h]`, in effect).
    for (pool_terms, 0..) |maybe_term, idx| {
        const term = maybe_term orelse continue;
        const app = switch (eg.nodes.items[term.node].node) {
            .app => |app| app,
            // Relation heads are never AC-policied, so an equation's top
            // node is always a plain application.
            .bag => continue,
            .leaf => continue,
        };
        if (!rel_heads.contains(app.term_id)) continue;
        if (term.children.len != 2) continue;
        const lhs = term.children[0] orelse continue;
        const rhs = term.children[1] orelse continue;
        result.pool_equations += 1;
        _ = try eg.merge(
            termClass(&eg, lhs),
            termClass(&eg, rhs),
            .{ .pool_equation = .{
                .pool_index = @intCast(idx),
                .lhs = lhs,
                .rhs = rhs,
            } },
        );
    }

    // Nothing can ever union: report the enrollment gap without paying for
    // a saturation that provably does no work. Absorbed AC heads still
    // convert by interning alone (pure permutation goals), so they keep
    // the search alive even with zero enrolled rules.
    if (rules.items.len == 0 and
        result.pool_equations == 0 and
        ac_certs.count() == 0 and
        !eqSidesConverged(&eg, eq_sides))
    {
        return result;
    }

    // Saturate one iteration at a time and stop as soon as the goal shares
    // a class with a pool entry. Absorption-style rules union a variable's
    // class with a compound containing that same class, and such cyclic
    // classes make AC rule sets generative up to any node cap — a found
    // chain must not pay for that tail. Misses still saturate to fixpoint
    // (or a cap), which the forced-negative report requires.
    result.stats = .{ .outcome = .iteration_capped };
    while (!poolConverged(&eg, goal_term, pool_terms) and
        !eqSidesConverged(&eg, eq_sides))
    {
        if (result.stats.iterations >= opts.max_iterations) break;
        const slice = try eg.saturate(rules.items, .{
            .max_iterations = 1,
            .max_nodes = opts.max_nodes,
        });
        result.stats.iterations += slice.iterations;
        result.stats.unions_applied += slice.unions_applied;
        result.stats.dep_deferred += slice.dep_deferred;
        result.stats.ac_match_capped += slice.ac_match_capped;
        result.stats.ac_cyclic_dropped += slice.ac_cyclic_dropped;
        result.stats.fold_applied += slice.fold_applied;
        if (slice.outcome != .iteration_capped) {
            result.stats.outcome = slice.outcome;
            break;
        }
    }
    result.classes = eg.classCount();
    result.nodes = eg.eNodeCount();

    // Bags re-sort members as unions land, so the pre-saturation seed
    // terms' children may no longer parallel their nodes. Rebuild them for
    // extraction; no merges happen past this point, so they stay aligned.
    var extract_goal = goal_term;
    var extract_pool = pool_terms;
    var extract_sides = eq_sides;
    if (ac_certs.count() != 0) {
        extract_goal = (try addExpr(&eg, context.env, theorem, goal)) orelse {
            result.convertible_unlowered =
                poolConverged(&eg, goal_term, pool_terms) or
                eqSidesConverged(&eg, eq_sides);
            return result;
        };
        extract_sides = goalEqSides(theorem, goal, &rel_heads, extract_goal);
        const rebuilt = try work.alloc(?*const egraph.Term, pool.len);
        for (pool_exprs, 0..) |maybe_expr, idx| {
            rebuilt[idx] = if (maybe_expr) |expr|
                try addExpr(&eg, context.env, theorem, expr)
            else
                null;
        }
        extract_pool = rebuilt;
    }

    const goal_class = termClass(&eg, extract_goal);
    // Prototype for every lowering attempt (pool references and the
    // equation fallback); nothing in it is attempt-specific, and every
    // mutable field is still at its empty default when the copies are
    // taken.
    const lowerer_proto = Lowerer{
        .work = work,
        .context = context,
        .theorem = theorem,
        .eg = &eg,
        .pool = pool,
        .ac_certs = &ac_certs,
        .goal_expr = goal,
        .names = try ViewTrace.DiagNames.build(
            work,
            theorem,
            context.parser,
            theorem_vars,
        ),
        .proof_src = proof_src,
        .target_line = target_line,
        .indent = proof_src[target_line.span.start..target_line.label_span.start],
    };
    for (pool, extract_pool, pool_exprs, 0..) |entry, maybe_term, maybe_expr, idx| {
        const ref_term = maybe_term orelse {
            // The extraction rebuild failed (a written member's class
            // spliced deeper than the written tree). If the seed-time
            // term had converged, the goal is provably convertible —
            // keep the failure report honest.
            if (pool_terms[idx]) |seed| {
                if (eg.sameClass(
                    termClass(&eg, seed),
                    termClass(&eg, goal_term),
                )) {
                    result.convertible_unlowered = true;
                }
            }
            continue;
        };
        if (!eg.sameClass(termClass(&eg, ref_term), goal_class)) continue;
        const steps = (try eg.explain(
            rules.items,
            ref_term,
            extract_goal,
            .{},
        )) orelse {
            result.convertible_unlowered = true;
            continue;
        };
        var lowerer = lowerer_proto;
        try lowerer.seedLabels(block_lines);
        var best = try lowerer.lower(
            entry.ref,
            ref_term,
            maybe_expr.?,
            steps,
        );
        var any_cap = lowerer.cap_tripped;
        // When the theory carries `@rewrite` rules, also lower the chain
        // reversed: a computation grounded by a reduced-side reference
        // (the `refl` pool line) traverses the fold backwards, where no
        // big-step group can form; the reducing direction collapses each
        // fold step's rewrite cascade. Keep whichever emission is shorter.
        if (context.registry.hasRewriteRules()) {
            var reversed_lowerer = lowerer_proto;
            try reversed_lowerer.seedLabels(block_lines);
            const reversed = try reversed_lowerer.lowerReversed(
                entry.ref,
                extract_goal,
                maybe_expr.?,
                try reverseSteps(work, steps),
            );
            if (reversed != null and
                (best == null or
                    reversed_lowerer.lines_emitted < lowerer.lines_emitted))
            {
                best = reversed;
            }
            any_cap = any_cap or reversed_lowerer.cap_tripped;
        }
        if (best) |replacement| {
            result.replacement = replacement;
            result.via = try lowerer.renderRefText(entry.ref);
            return result;
        }
        result.convertible_unlowered = true;
        if (any_cap) result.lower_capped = true;
    }

    // Equation fallback: no pool reference lowered, but the goal's own
    // sides share a class — the line is provable outright. Ground the
    // chain in `refl` (or one `symm` for the reversed orientation) and
    // keep the shorter emission, mirroring the pool path's dual lowering.
    if (extract_sides) |sides| {
        if (eg.sameClass(
            termClass(&eg, sides.lhs),
            termClass(&eg, sides.rhs),
        )) {
            const steps = (try eg.explain(
                rules.items,
                sides.lhs,
                sides.rhs,
                .{},
            )) orelse {
                result.convertible_unlowered = true;
                return result;
            };
            var lowerer = lowerer_proto;
            try lowerer.seedLabels(block_lines);
            var best = try lowerer.lowerEquation(
                sides.lhs,
                sides.lhs_expr,
                sides.rhs_expr,
                steps,
                false,
            );
            var any_cap = lowerer.cap_tripped;
            if (context.registry.hasRewriteRules()) {
                var reversed_lowerer = lowerer_proto;
                try reversed_lowerer.seedLabels(block_lines);
                const reversed = try reversed_lowerer.lowerEquation(
                    sides.rhs,
                    sides.rhs_expr,
                    sides.lhs_expr,
                    try reverseSteps(work, steps),
                    true,
                );
                if (reversed != null and
                    (best == null or
                        reversed_lowerer.lines_emitted < lowerer.lines_emitted))
                {
                    best = reversed;
                }
                any_cap = any_cap or reversed_lowerer.cap_tripped;
            }
            if (best) |replacement| {
                result.replacement = replacement;
                return result;
            }
            result.convertible_unlowered = true;
            if (any_cap) result.lower_capped = true;
        }
    } else if (eqSidesConverged(&eg, eq_sides)) {
        // The extraction rebuild lost the sides (an AC splice); the goal
        // is still provably convertible — keep the failure report honest.
        result.convertible_unlowered = true;
    }
    return result;
}

/// The goal's own sides, when the goal line is `rel(lhs, rhs)` for a
/// registered relation head.
const EqSides = struct {
    lhs: *const egraph.Term,
    rhs: *const egraph.Term,
    lhs_expr: ExprId,
    rhs_expr: ExprId,
};

/// Equation-goal detection against a seeded goal term. The side terms are
/// the goal term's children (relation heads are never AC-policied, so the
/// top node is a plain application with both slots resolved).
fn goalEqSides(
    theorem: *const TheoremContext,
    goal: ExprId,
    rel_heads: *const std.AutoArrayHashMapUnmanaged(u32, void),
    goal_term: *const egraph.Term,
) ?EqSides {
    const app = switch (theorem.interner.node(goal).*) {
        .app => |app| app,
        else => return null,
    };
    if (!rel_heads.contains(app.term_id)) return null;
    if (goal_term.children.len != 2) return null;
    const lhs = goal_term.children[0] orelse return null;
    const rhs = goal_term.children[1] orelse return null;
    return .{
        .lhs = lhs,
        .rhs = rhs,
        .lhs_expr = app.args[0],
        .rhs_expr = app.args[1],
    };
}

fn eqSidesConverged(
    eg: *const egraph.EGraph,
    maybe_sides: ?EqSides,
) bool {
    const sides = maybe_sides orelse return false;
    return eg.sameClass(
        termClass(eg, sides.lhs),
        termClass(eg, sides.rhs),
    );
}

/// Flip an explanation chain end-for-end: the step list reverses and each
/// step swaps endpoints and orientation. Positions stay valid — a step's
/// path components above its own redex are identical on both sides.
fn reverseSteps(
    work: std.mem.Allocator,
    steps: []const egraph.Step,
) ![]egraph.Step {
    const out = try work.alloc(egraph.Step, steps.len);
    for (steps, 0..) |step, idx| {
        out[steps.len - 1 - idx] = .{
            .source = step.source,
            .needs_symm = !step.needs_symm,
            .position = step.position,
            .before = step.after,
            .after = step.before,
            .bindings = step.bindings,
            .bag = if (step.bag) |bag| .{
                .matched_before = bag.matched_after,
                .matched_after = bag.matched_before,
            } else null,
        };
    }
    return out;
}

fn termClass(eg: *const egraph.EGraph, term: *const egraph.Term) egraph.EClassId {
    return eg.find(eg.nodes.items[term.node].class);
}

fn poolConverged(
    eg: *const egraph.EGraph,
    goal_term: *const egraph.Term,
    pool_terms: []const ?*const egraph.Term,
) bool {
    const goal_class = termClass(eg, goal_term);
    for (pool_terms) |maybe_term| {
        const ref_term = maybe_term orelse continue;
        if (eg.sameClass(termClass(eg, ref_term), goal_class)) return true;
    }
    return false;
}

/// Leaf encoding for variables: theorem vars on even ids, dummies on odd.
fn leafIdFor(var_id: VarId) egraph.LeafId {
    return switch (var_id) {
        .theorem_var => |idx| @as(egraph.LeafId, idx) << 1,
        .dummy_var => |idx| (@as(egraph.LeafId, idx) << 1) | 1,
    };
}

pub fn varIdForLeaf(leaf: egraph.LeafId) VarId {
    const idx: u32 = @intCast(leaf >> 1);
    return if (leaf & 1 == 0)
        .{ .theorem_var = idx }
    else
        .{ .dummy_var = idx };
}

/// Translate a concrete expression into the egraph, returning its resolved
/// seed term. Null when the expression is not concrete (placeholders) or
/// malformed against the term signatures.
fn addExpr(
    eg: *egraph.EGraph,
    env: *const GlobalEnv,
    theorem: *const TheoremContext,
    expr_id: ExprId,
) error{OutOfMemory}!?*const egraph.Term {
    switch (theorem.interner.node(expr_id).*) {
        .placeholder => return null,
        .variable => |var_id| {
            const shape = egraph.ENode{ .leaf = leafIdFor(var_id) };
            _ = try eg.add(shape);
            const node = (try eg.lookupNode(shape)).?;
            const term = try eg.allocator.create(egraph.Term);
            term.* = .{ .node = node, .children = &.{} };
            return term;
        },
        .app => |app| {
            if (app.term_id >= env.terms.items.len) return null;
            const decl = &env.terms.items[app.term_id];
            if (decl.args.len != app.args.len) return null;
            if (app.args.len == 2 and eg.ac_heads.contains(app.term_id)) {
                return try addAcExpr(eg, env, theorem, app.term_id, expr_id);
            }
            const children = try eg.allocator.alloc(
                egraph.Child,
                app.args.len,
            );
            const term_children = try eg.allocator.alloc(
                ?*const egraph.Term,
                app.args.len,
            );
            for (decl.args, app.args, 0..) |arg_info, child_expr, idx| {
                if (arg_info.bound) {
                    const var_id = switch (theorem.interner.node(child_expr).*) {
                        .variable => |v| v,
                        else => return null,
                    };
                    children[idx] = .{ .bound = leafIdFor(var_id) };
                    term_children[idx] = null;
                } else {
                    const child = (try addExpr(
                        eg,
                        env,
                        theorem,
                        child_expr,
                    )) orelse return null;
                    children[idx] = .{ .class = termClass(eg, child) };
                    term_children[idx] = child;
                }
            }
            const shape = egraph.ENode{ .app = .{
                .term_id = app.term_id,
                .children = children,
            } };
            _ = try eg.add(shape);
            const node = (try eg.lookupNode(shape)).?;
            const term = try eg.allocator.create(egraph.Term);
            term.* = .{ .node = node, .children = term_children };
            return term;
        },
    }
}

/// Translate a policied-head application: flatten the written tree over
/// the head, translate each member, intern the bag, and pair the member
/// terms against the node's sorted order. Null when the node spliced
/// deeper than the written tree (a member's class acquired a same-head bag
/// through unions) — extraction has no written subterm for those members,
/// so the ref is skipped cleanly.
fn addAcExpr(
    eg: *egraph.EGraph,
    env: *const GlobalEnv,
    theorem: *const TheoremContext,
    term_id: u32,
    expr_id: ExprId,
) error{OutOfMemory}!?*const egraph.Term {
    var member_exprs: std.ArrayListUnmanaged(ExprId) = .{};
    try flattenAcExpr(eg.allocator, theorem, term_id, expr_id, &member_exprs);
    const member_terms = try eg.allocator.alloc(
        *const egraph.Term,
        member_exprs.items.len,
    );
    for (member_exprs.items, 0..) |member, idx| {
        member_terms[idx] = (try addExpr(eg, env, theorem, member)) orelse {
            return null;
        };
    }
    const members = try eg.allocator.alloc(
        egraph.EClassId,
        member_terms.len,
    );
    for (member_terms, 0..) |term, idx| {
        members[idx] = termClass(eg, term);
    }
    const shape = egraph.ENode{ .bag = .{
        .term_id = term_id,
        .members = members,
    } };
    _ = try eg.add(shape);
    const node = (try eg.lookupNode(shape)).?;
    const bag = switch (eg.nodes.items[node].node) {
        .bag => |bag| bag,
        else => return null,
    };
    if (bag.members.len != member_terms.len) return null;
    const children = try eg.allocator.alloc(
        ?*const egraph.Term,
        bag.members.len,
    );
    @memset(children, null);
    for (member_terms) |member_term| {
        const root = termClass(eg, member_term);
        var placed = false;
        for (bag.members, 0..) |member, idx| {
            if (children[idx] != null) continue;
            if (eg.find(member) != root) continue;
            children[idx] = member_term;
            placed = true;
            break;
        }
        if (!placed) return null;
    }
    const term = try eg.allocator.create(egraph.Term);
    term.* = .{ .node = node, .children = children };
    return term;
}

pub fn flattenAcExpr(
    allocator: std.mem.Allocator,
    theorem: *const TheoremContext,
    term_id: u32,
    expr_id: ExprId,
    out: *std.ArrayListUnmanaged(ExprId),
) error{OutOfMemory}!void {
    switch (theorem.interner.node(expr_id).*) {
        .app => |app| if (app.term_id == term_id and app.args.len == 2) {
            try flattenAcExpr(allocator, theorem, term_id, app.args[0], out);
            try flattenAcExpr(allocator, theorem, term_id, app.args[1], out);
            return;
        },
        else => {},
    }
    try out.append(allocator, expr_id);
}
