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

/// The certificates backing one AC-absorbed operator: the `@conversion
/// comm`/`assoc` theorems the lowering cites for re-treeing chains.
const AcCert = struct {
    comm_rule_id: u32,
    assoc_rule_id: u32,
    /// True when the assoc certificate's conclusion reads
    /// `rel(t(t(a,b), c), t(a, t(b,c)))` — left-nested match side.
    assoc_forward: bool,
};

const AcCertMap = std.AutoArrayHashMapUnmanaged(u32, AcCert);

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
    result.rule_count = rules.items.len;

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
    // a saturation that provably does no work.
    if (rules.items.len == 0 and result.pool_equations == 0) return result;

    // Saturate one iteration at a time and stop as soon as the goal shares
    // a class with a pool entry. Absorption-style rules union a variable's
    // class with a compound containing that same class, and such cyclic
    // classes make AC rule sets generative up to any node cap — a found
    // chain must not pay for that tail. Misses still saturate to fixpoint
    // (or a cap), which the forced-negative report requires.
    result.stats = .{ .outcome = .iteration_capped };
    while (!poolConverged(&eg, goal_term, pool_terms)) {
        if (result.stats.iterations >= opts.max_iterations) break;
        const slice = try eg.saturate(rules.items, .{
            .max_iterations = 1,
            .max_nodes = opts.max_nodes,
        });
        result.stats.iterations += slice.iterations;
        result.stats.unions_applied += slice.unions_applied;
        result.stats.dep_deferred += slice.dep_deferred;
        result.stats.ac_match_capped += slice.ac_match_capped;
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
    if (ac_certs.count() != 0) {
        extract_goal = (try addExpr(&eg, context.env, theorem, goal)) orelse {
            result.convertible_unlowered =
                poolConverged(&eg, goal_term, pool_terms);
            return result;
        };
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
    for (pool, extract_pool, pool_exprs) |entry, maybe_term, maybe_expr| {
        const ref_term = maybe_term orelse continue;
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
        var lowerer = Lowerer{
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
        try lowerer.seedLabels(block_lines);
        if (try lowerer.lower(
            entry.ref,
            ref_term,
            maybe_expr.?,
            steps,
        )) |replacement| {
            result.replacement = replacement;
            result.via = try lowerer.renderRefText(entry.ref);
            return result;
        }
        result.convertible_unlowered = true;
    }
    return result;
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

fn varIdForLeaf(leaf: egraph.LeafId) VarId {
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
                    const var_id = switch (
                        theorem.interner.node(child_expr).*
                    ) {
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

fn flattenAcExpr(
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

/// Lowers one explanation into proof-script source text. Every emitted line
/// asserts its full conclusion, so unification replay solves all rule
/// binders — no explicit bindings are needed on any line.
const Lowerer = struct {
    work: std.mem.Allocator,
    context: *const Context,
    theorem: *TheoremContext,
    eg: *egraph.EGraph,
    pool: []const Refs.RefPoolEntry,
    ac_certs: *const AcCertMap,
    /// The goal formula as written: the endpoint the chain must reach
    /// (the canonical comb rendering is aligned to it at the final seam).
    goal_expr: ExprId,
    names: ViewTrace.DiagNames,
    proof_src: []const u8,
    target_line: ProofScript.ProofLine,
    indent: []const u8,
    used_labels: std.StringHashMapUnmanaged(void) = .{},
    label_counter: usize = 0,
    /// Safety valve: re-treeing seams are O(members²) lines each, so a
    /// runaway chain aborts the ref instead of flooding the buffer.
    lines_emitted: usize = 0,
    align_depth: usize = 0,
    out: std.ArrayListUnmanaged(u8) = .{},

    fn seedLabels(
        self: *Lowerer,
        block_lines: []const ProofScript.ProofLine,
    ) !void {
        for (block_lines) |line| {
            try self.used_labels.put(self.work, line.label, {});
        }
    }

    fn freshLabel(self: *Lowerer) ![]const u8 {
        while (true) {
            self.label_counter += 1;
            const candidate = try std.fmt.allocPrint(
                self.work,
                "{s}_{d}",
                .{ self.target_line.label, self.label_counter },
            );
            const entry = try self.used_labels.getOrPut(self.work, candidate);
            if (!entry.found_existing) return candidate;
        }
    }

    fn ppExpr(self: *Lowerer, expr_id: ExprId) ![]const u8 {
        return try ViewTrace.formatExprNamed(
            self.work,
            self.theorem,
            self.context.env,
            &self.names,
            expr_id,
        );
    }

    fn ruleName(self: *Lowerer, rule_id: u32) []const u8 {
        return self.context.env.rules.items[rule_id].name;
    }

    fn relationForSort(self: *Lowerer, sort_name: []const u8) ?ResolvedRelation {
        return self.context.registry.resolveRelation(
            self.context.env,
            sort_name,
        );
    }

    /// Relation governing a term (by its head's return sort). Null for a
    /// bare-variable term or an unrelated sort — both end the lowering.
    fn relationForTerm(
        self: *Lowerer,
        term: *const egraph.Term,
    ) ?ResolvedRelation {
        const sort_name = self.sortOfTerm(term) orelse return null;
        return self.relationForSort(sort_name);
    }

    fn sortOfTerm(self: *Lowerer, term: *const egraph.Term) ?[]const u8 {
        switch (self.eg.nodes.items[term.node].node) {
            .app => |app| {
                return self.context.env.terms.items[app.term_id].ret_sort_name;
            },
            .bag => |bag| {
                return self.context.env.terms.items[bag.term_id].ret_sort_name;
            },
            .leaf => |leaf| {
                const var_id = varIdForLeaf(leaf);
                return switch (var_id) {
                    .theorem_var => |idx| blk: {
                        if (idx >= self.theorem.arg_infos.len) break :blk null;
                        break :blk self.theorem.arg_infos[idx].sort_name;
                    },
                    .dummy_var => null,
                };
            },
        }
    }

    /// Rebuild a resolved term as an interned expression for rendering.
    fn termToExpr(
        self: *Lowerer,
        term: *const egraph.Term,
    ) error{ OutOfMemory, TooManyTheoremExprs }!?ExprId {
        switch (self.eg.nodes.items[term.node].node) {
            .leaf => |leaf| {
                return try self.theorem.interner.internVar(varIdForLeaf(leaf));
            },
            // A bag term denotes the right-nested comb over its children.
            .bag => |bag| {
                var idx = term.children.len - 1;
                var acc = (try self.termToExpr(
                    term.children[idx].?,
                )) orelse return null;
                while (idx > 0) {
                    idx -= 1;
                    const child = (try self.termToExpr(
                        term.children[idx].?,
                    )) orelse return null;
                    acc = try self.theorem.interner.internApp(
                        bag.term_id,
                        &.{ child, acc },
                    );
                }
                return acc;
            },
            .app => |app| {
                const args = try self.work.alloc(ExprId, app.children.len);
                for (app.children, term.children, 0..) |child, sub, idx| {
                    switch (child) {
                        .bound => |leaf| {
                            args[idx] = try self.theorem.interner.internVar(
                                varIdForLeaf(leaf),
                            );
                        },
                        .class => {
                            args[idx] = (try self.termToExpr(
                                sub.?,
                            )) orelse return null;
                        },
                    }
                }
                return try self.theorem.interner.internApp(app.term_id, args);
            },
        }
    }

    fn relExpr(
        self: *Lowerer,
        relation: ResolvedRelation,
        lhs: *const egraph.Term,
        rhs: *const egraph.Term,
    ) !?ExprId {
        const lhs_expr = (try self.termToExpr(lhs)) orelse return null;
        const rhs_expr = (try self.termToExpr(rhs)) orelse return null;
        return try self.relIds(relation, lhs_expr, rhs_expr);
    }

    fn relIds(
        self: *Lowerer,
        relation: ResolvedRelation,
        lhs: ExprId,
        rhs: ExprId,
    ) !ExprId {
        return try self.theorem.interner.internApp(
            relation.rel_term_id,
            &.{ lhs, rhs },
        );
    }

    fn sortOfExpr(self: *Lowerer, expr: ExprId) ?[]const u8 {
        switch (self.theorem.interner.node(expr).*) {
            .app => |app| {
                if (app.term_id >= self.context.env.terms.items.len) {
                    return null;
                }
                return self.context.env.terms.items[app.term_id].ret_sort_name;
            },
            .variable => |var_id| return switch (var_id) {
                .theorem_var => |idx| blk: {
                    if (idx >= self.theorem.arg_infos.len) break :blk null;
                    break :blk self.theorem.arg_infos[idx].sort_name;
                },
                .dummy_var => null,
            },
            .placeholder => return null,
        }
    }

    /// Emit `label: $ <formula> $ by <rule> [refs...]` and return the label.
    fn emitLine(
        self: *Lowerer,
        formula: ExprId,
        rule_id: u32,
        ref_labels: []const []const u8,
    ) !?[]const u8 {
        self.lines_emitted += 1;
        if (self.lines_emitted > 4096) return null;
        const text = (try self.ppExpr(formula));
        const label = try self.freshLabel();
        const writer = self.out.writer(self.work);
        try writer.print("{s}{s}: $ {s} $ by {s}", .{
            self.indent,
            label,
            text,
            self.ruleName(rule_id),
        });
        if (ref_labels.len != 0) {
            try writer.writeAll(" [");
            for (ref_labels, 0..) |ref_label, idx| {
                if (idx != 0) try writer.writeAll(", ");
                try writer.writeAll(ref_label);
            }
            try writer.writeAll("]");
        }
        try writer.writeAll("\n");
        return label;
    }

    /// Replace the redex at `position` in `term`, verifying it matches
    /// `before` structurally.
    fn replaceAt(
        self: *Lowerer,
        term: *const egraph.Term,
        position: []const u32,
        before: *const egraph.Term,
        after: *const egraph.Term,
    ) error{OutOfMemory}!?*const egraph.Term {
        if (position.len == 0) {
            if (!egraph.termEql(self.eg, term, before)) return null;
            return after;
        }
        const idx = position[0];
        if (idx >= term.children.len) return null;
        const child = term.children[idx] orelse return null;
        const replaced = (try self.replaceAt(
            child,
            position[1..],
            before,
            after,
        )) orelse return null;
        const children = try self.work.dupe(?*const egraph.Term, term.children);
        children[idx] = replaced;
        const rebuilt = try self.work.create(egraph.Term);
        rebuilt.* = .{ .node = term.node, .children = children };
        return rebuilt;
    }

    /// Emit the proof of `rel(current, next)` for one step: the rule
    /// instance, or the pool equation cited directly (through `symm` when
    /// traversed backwards), lifted through one `@congr` application per
    /// enclosing level with `refl` siblings. Returns the label proving the
    /// root-level relation.
    fn emitStep(
        self: *Lowerer,
        step: egraph.Step,
        full_before: *const egraph.Term,
        full_after: *const egraph.Term,
    ) !?[]const u8 {
        if (step.bag != null) {
            return try self.emitBagStep(step, full_before, full_after);
        }
        const redex_relation = self.relationForTerm(step.before) orelse
            self.relationForTerm(step.after) orelse return null;
        var label: []const u8 = undefined;
        switch (step.source) {
            // Redex-level rule instance: a fresh line, since the rule
            // proves any instance.
            .rule => |rule_id| {
                const thm_lhs = if (step.needs_symm) step.after else step.before;
                const thm_rhs = if (step.needs_symm) step.before else step.after;
                const instance = (try self.relExpr(
                    redex_relation,
                    thm_lhs,
                    thm_rhs,
                )) orelse return null;
                label = (try self.emitLine(instance, rule_id, &.{})) orelse {
                    return null;
                };
                if (step.needs_symm) {
                    const flipped = (try self.relExpr(
                        redex_relation,
                        step.before,
                        step.after,
                    )) orelse return null;
                    label = (try self.emitLine(
                        flipped,
                        redex_relation.symm_id,
                        &.{label},
                    )) orelse return null;
                }
            },
            // The pool entry asserts rel(before, after) — or its flip —
            // in its own written form. Cite it (through symm when
            // traversed backwards); when the chain's canonical renderings
            // differ from the written sides (AC bags), align the seams.
            .pool_equation => |pool_idx| {
                label = try self.renderRefText(self.pool[pool_idx].ref);
                const written = Refs.sourceRefExpr(
                    self.context,
                    self.theorem,
                    self.pool[pool_idx].ref,
                ) catch return null;
                const wapp = self.exprApp(written) orelse return null;
                if (wapp.args.len != 2) return null;
                var w_before = wapp.args[0];
                var w_after = wapp.args[1];
                if (step.needs_symm) {
                    w_before = wapp.args[1];
                    w_after = wapp.args[0];
                    label = (try self.emitLine(
                        try self.relIds(redex_relation, w_before, w_after),
                        redex_relation.symm_id,
                        &.{label},
                    )) orelse return null;
                }
                const before_expr = (try self.termToExpr(
                    step.before,
                )) orelse return null;
                const after_expr = (try self.termToExpr(
                    step.after,
                )) orelse return null;
                if (before_expr != w_before) {
                    const pre = (try self.alignEmit(
                        before_expr,
                        w_before,
                    )) orelse return null;
                    label = (try self.emitLine(
                        try self.relIds(redex_relation, before_expr, w_after),
                        redex_relation.trans_id,
                        &.{ pre, label },
                    )) orelse return null;
                }
                if (w_after != after_expr) {
                    const post = (try self.alignEmit(
                        w_after,
                        after_expr,
                    )) orelse return null;
                    label = (try self.emitLine(
                        try self.relIds(
                            redex_relation,
                            before_expr,
                            after_expr,
                        ),
                        redex_relation.trans_id,
                        &.{ label, post },
                    )) orelse return null;
                }
            },
        }

        // Congruence lifting, innermost level first.
        var depth = step.position.len;
        while (depth > 0) {
            depth -= 1;
            const before_parent = termAt(full_before, step.position[0..depth]) orelse
                return null;
            const after_parent = termAt(full_after, step.position[0..depth]) orelse
                return null;
            label = (try self.emitParentCongruence(
                before_parent,
                after_parent,
                step.position[depth],
                label,
            )) orelse return null;
        }
        return label;
    }

    /// One `@congr` application: `rel(f(..a..), f(..b..))` from the child
    /// proof at `changed_idx` and `refl` lines for every other regular arg.
    fn emitCongruence(
        self: *Lowerer,
        before_parent: *const egraph.Term,
        after_parent: *const egraph.Term,
        changed_idx: u32,
        child_label: []const u8,
    ) !?[]const u8 {
        const app = switch (self.eg.nodes.items[before_parent.node].node) {
            .app => |app| app,
            .leaf => return null,
            .bag => return null,
        };
        const congr = self.context.registry.congr_by_head.get(app.term_id) orelse
            return null;
        const decl = &self.context.env.terms.items[app.term_id];

        var ref_labels: std.ArrayListUnmanaged([]const u8) = .{};
        for (decl.args, 0..) |arg_info, idx| {
            if (arg_info.bound) continue;
            if (idx == changed_idx) {
                try ref_labels.append(self.work, child_label);
                continue;
            }
            // Unchanged sibling: refl for the argument's sort.
            const sibling = before_parent.children[idx].?;
            const relation = self.relationForSort(arg_info.sort_name) orelse
                return null;
            const refl_formula = (try self.relExpr(
                relation,
                sibling,
                sibling,
            )) orelse return null;
            const refl_label = (try self.emitLine(
                refl_formula,
                relation.refl_id,
                &.{},
            )) orelse return null;
            try ref_labels.append(self.work, refl_label);
        }

        const parent_relation = self.relationForSort(decl.ret_sort_name) orelse
            return null;
        const formula = (try self.relExpr(
            parent_relation,
            before_parent,
            after_parent,
        )) orelse return null;
        return try self.emitLine(formula, congr.rule_id, ref_labels.items);
    }

    // --- AC re-treeing -------------------------------------------------
    //
    // Bag interning makes AC equality definitional inside the egraph; the
    // proof debt comes due here. Chain formulas render bags as canonical
    // right-nested combs, and every seam between a canonical comb and
    // another tree of the same members (the written goal/reference, a rule
    // instance's own shape, a cited pool equation) is discharged by an
    // explicit chain of comm/assoc certificate steps.

    const Prim = enum { comm, assoc_ltr, assoc_rtl };

    /// A lifted child rewrite: the proving label and the rebuilt root.
    const Rewritten = struct { label: []const u8, root: ExprId };

    /// Error set for the mutually recursive alignment family (emitLine's
    /// inferred set plus the interner's).
    const AlignErr = @typeInfo(
        @typeInfo(@TypeOf(emitLine)).@"fn".return_type.?,
    ).error_union.error_set || error{ OutOfMemory, TooManyTheoremExprs };

    fn exprApp(
        self: *Lowerer,
        expr: ExprId,
    ) ?@TypeOf(self.theorem.interner.node(expr).app) {
        return switch (self.theorem.interner.node(expr).*) {
            .app => |app| app,
            else => null,
        };
    }

    fn exprAt(self: *Lowerer, root: ExprId, path: []const u32) ?ExprId {
        var current = root;
        for (path) |idx| {
            const app = self.exprApp(current) orelse return null;
            if (idx >= app.args.len) return null;
            current = app.args[idx];
        }
        return current;
    }

    fn replaceExprAt(
        self: *Lowerer,
        root: ExprId,
        path: []const u32,
        replacement: ExprId,
    ) error{ OutOfMemory, TooManyTheoremExprs }!?ExprId {
        if (path.len == 0) return replacement;
        const app = self.exprApp(root) orelse return null;
        const idx = path[0];
        if (idx >= app.args.len) return null;
        const sub = (try self.replaceExprAt(
            app.args[idx],
            path[1..],
            replacement,
        )) orelse return null;
        const args = try self.work.dupe(ExprId, app.args);
        args[idx] = sub;
        return try self.theorem.interner.internApp(app.term_id, args);
    }

    /// Canonical form of an expression under the certified AC laws:
    /// members of certified heads flatten, canonicalize recursively, sort
    /// by interned id, and right-nest. Two expressions are alignable iff
    /// their canonical forms intern identically.
    fn canonKey(
        self: *Lowerer,
        expr: ExprId,
    ) error{ OutOfMemory, TooManyTheoremExprs }!ExprId {
        switch (self.theorem.interner.node(expr).*) {
            .variable, .placeholder => return expr,
            .app => |app| {
                if (app.args.len == 2 and
                    self.ac_certs.contains(app.term_id))
                {
                    var members: std.ArrayListUnmanaged(ExprId) = .{};
                    try flattenAcExpr(
                        self.work,
                        self.theorem,
                        app.term_id,
                        expr,
                        &members,
                    );
                    const keys = try self.work.alloc(
                        ExprId,
                        members.items.len,
                    );
                    for (members.items, 0..) |member, idx| {
                        keys[idx] = try self.canonKey(member);
                    }
                    std.mem.sort(ExprId, keys, {}, std.sort.asc(ExprId));
                    var idx = keys.len - 1;
                    var acc = keys[idx];
                    while (idx > 0) {
                        idx -= 1;
                        acc = try self.theorem.interner.internApp(
                            app.term_id,
                            &.{ keys[idx], acc },
                        );
                    }
                    return acc;
                }
                const args = try self.work.alloc(ExprId, app.args.len);
                for (app.args, 0..) |arg, idx| {
                    args[idx] = try self.canonKey(arg);
                }
                return try self.theorem.interner.internApp(
                    app.term_id,
                    args,
                );
            },
        }
    }

    /// Replace the subexpression at `path` and lift the child's proof to
    /// the root through one `@congr` line per level with refl siblings.
    fn liftExprLabel(
        self: *Lowerer,
        root: ExprId,
        path: []const u32,
        replacement: ExprId,
        child_label: []const u8,
    ) AlignErr!?Rewritten {
        if (path.len == 0) {
            return .{ .label = child_label, .root = replacement };
        }
        const app = self.exprApp(root) orelse return null;
        const idx = path[0];
        if (idx >= app.args.len) return null;
        const sub = (try self.liftExprLabel(
            app.args[idx],
            path[1..],
            replacement,
            child_label,
        )) orelse return null;
        const args = try self.work.dupe(ExprId, app.args);
        args[idx] = sub.root;
        const new_root = try self.theorem.interner.internApp(
            app.term_id,
            args,
        );
        const congr = self.context.registry.congr_by_head.get(
            app.term_id,
        ) orelse return null;
        const decl = &self.context.env.terms.items[app.term_id];
        var ref_labels: std.ArrayListUnmanaged([]const u8) = .{};
        for (decl.args, app.args, 0..) |arg_info, old_arg, i| {
            if (arg_info.bound) continue;
            if (i == idx) {
                try ref_labels.append(self.work, sub.label);
                continue;
            }
            const child_rel = self.relationForSort(
                arg_info.sort_name,
            ) orelse return null;
            const refl_label = (try self.emitLine(
                try self.relIds(child_rel, old_arg, old_arg),
                child_rel.refl_id,
                &.{},
            )) orelse return null;
            try ref_labels.append(self.work, refl_label);
        }
        const relation = self.relationForSort(
            decl.ret_sort_name,
        ) orelse return null;
        const label = (try self.emitLine(
            try self.relIds(relation, root, new_root),
            congr.rule_id,
            ref_labels.items,
        )) orelse return null;
        return .{ .label = label, .root = new_root };
    }

    /// Apply one certified law at `path`, emit its certificate line (with
    /// symm when traversed against the theorem's orientation), and lift it
    /// to the root. Returns the proving label and the rewritten root.
    fn emitPrimAt(
        self: *Lowerer,
        head: u32,
        cert: AcCert,
        root: ExprId,
        path: []const u32,
        prim: Prim,
    ) AlignErr!?Rewritten {
        const redex = self.exprAt(root, path) orelse return null;
        const ra = self.exprApp(redex) orelse return null;
        if (ra.term_id != head or ra.args.len != 2) return null;
        var redex_after: ExprId = undefined;
        var rule_id: u32 = undefined;
        var needs_symm = false;
        switch (prim) {
            .comm => {
                redex_after = try self.theorem.interner.internApp(
                    head,
                    &.{ ra.args[1], ra.args[0] },
                );
                rule_id = cert.comm_rule_id;
            },
            .assoc_ltr => {
                const inner = self.exprApp(ra.args[0]) orelse return null;
                if (inner.term_id != head) return null;
                const right = try self.theorem.interner.internApp(
                    head,
                    &.{ inner.args[1], ra.args[1] },
                );
                redex_after = try self.theorem.interner.internApp(
                    head,
                    &.{ inner.args[0], right },
                );
                rule_id = cert.assoc_rule_id;
                needs_symm = !cert.assoc_forward;
            },
            .assoc_rtl => {
                const inner = self.exprApp(ra.args[1]) orelse return null;
                if (inner.term_id != head) return null;
                const left = try self.theorem.interner.internApp(
                    head,
                    &.{ ra.args[0], inner.args[0] },
                );
                redex_after = try self.theorem.interner.internApp(
                    head,
                    &.{ left, inner.args[1] },
                );
                rule_id = cert.assoc_rule_id;
                needs_symm = cert.assoc_forward;
            },
        }
        const relation = self.relationForSort(
            self.sortOfExpr(redex) orelse return null,
        ) orelse return null;
        var label: []const u8 = undefined;
        if (needs_symm) {
            label = (try self.emitLine(
                try self.relIds(relation, redex_after, redex),
                rule_id,
                &.{},
            )) orelse return null;
            label = (try self.emitLine(
                try self.relIds(relation, redex, redex_after),
                relation.symm_id,
                &.{label},
            )) orelse return null;
        } else {
            label = (try self.emitLine(
                try self.relIds(relation, redex, redex_after),
                rule_id,
                &.{},
            )) orelse return null;
        }
        return try self.liftExprLabel(root, path, redex_after, label);
    }

    fn joinChain(
        self: *Lowerer,
        relation: ResolvedRelation,
        base_from: ExprId,
        chain: ?[]const u8,
        step_label: []const u8,
        current: ExprId,
    ) !?[]const u8 {
        const prev = chain orelse return step_label;
        return try self.emitLine(
            try self.relIds(relation, base_from, current),
            relation.trans_id,
            &.{ prev, step_label },
        );
    }

    fn collectAcLeaves(
        self: *Lowerer,
        head: u32,
        expr: ExprId,
        path: []const u32,
        members: *std.ArrayListUnmanaged(ExprId),
        paths: *std.ArrayListUnmanaged([]const u32),
    ) error{OutOfMemory}!void {
        const app = self.exprApp(expr);
        if (app != null and app.?.term_id == head and app.?.args.len == 2) {
            const left = try self.work.alloc(u32, path.len + 1);
            @memcpy(left[0..path.len], path);
            left[path.len] = 0;
            try self.collectAcLeaves(head, app.?.args[0], left, members, paths);
            const right = try self.work.alloc(u32, path.len + 1);
            @memcpy(right[0..path.len], path);
            right[path.len] = 1;
            try self.collectAcLeaves(head, app.?.args[1], right, members, paths);
            return;
        }
        try members.append(self.work, expr);
        try paths.append(self.work, path);
    }

    /// First spine position whose left child shares the head (the next
    /// left-to-right rotation toward the right-nested comb), or null when
    /// the tree is already a right comb.
    fn findLtrRedex(
        self: *Lowerer,
        head: u32,
        expr: ExprId,
    ) !?[]const u32 {
        var path: std.ArrayListUnmanaged(u32) = .{};
        var current = expr;
        while (true) {
            const app = self.exprApp(current) orelse return null;
            if (app.term_id != head or app.args.len != 2) return null;
            const left = self.exprApp(app.args[0]);
            if (left != null and left.?.term_id == head and
                left.?.args.len == 2)
            {
                return path.items;
            }
            try path.append(self.work, 1);
            current = app.args[1];
        }
    }

    fn rotateLtr(
        self: *Lowerer,
        head: u32,
        root: ExprId,
        path: []const u32,
    ) !?ExprId {
        const redex = self.exprAt(root, path) orelse return null;
        const ra = self.exprApp(redex) orelse return null;
        const inner = self.exprApp(ra.args[0]) orelse return null;
        if (ra.term_id != head or inner.term_id != head) return null;
        const right = try self.theorem.interner.internApp(
            head,
            &.{ inner.args[1], ra.args[1] },
        );
        const rotated = try self.theorem.interner.internApp(
            head,
            &.{ inner.args[0], right },
        );
        return try self.replaceExprAt(root, path, rotated);
    }

    /// Swap the spine members at positions `s` and `s+1` of a `count`-wide
    /// right comb (three primitive steps, or one comm for the tail pair).
    fn emitCombSwap(
        self: *Lowerer,
        head: u32,
        cert: AcCert,
        relation: ResolvedRelation,
        base_from: ExprId,
        chain: *?[]const u8,
        current_in: ExprId,
        s: usize,
        count: usize,
    ) !?ExprId {
        var current = current_in;
        var path: std.ArrayListUnmanaged(u32) = .{};
        for (0..s) |_| try path.append(self.work, 1);
        if (s + 2 == count) {
            const stepped = (try self.emitPrimAt(
                head,
                cert,
                current,
                path.items,
                .comm,
            )) orelse return null;
            current = stepped.root;
            chain.* = (try self.joinChain(
                relation,
                base_from,
                chain.*,
                stepped.label,
                current,
            )) orelse return null;
            return current;
        }
        var stepped = (try self.emitPrimAt(
            head,
            cert,
            current,
            path.items,
            .assoc_rtl,
        )) orelse return null;
        current = stepped.root;
        chain.* = (try self.joinChain(
            relation,
            base_from,
            chain.*,
            stepped.label,
            current,
        )) orelse return null;
        try path.append(self.work, 0);
        stepped = (try self.emitPrimAt(
            head,
            cert,
            current,
            path.items,
            .comm,
        )) orelse return null;
        current = stepped.root;
        chain.* = (try self.joinChain(
            relation,
            base_from,
            chain.*,
            stepped.label,
            current,
        )) orelse return null;
        _ = path.pop();
        stepped = (try self.emitPrimAt(
            head,
            cert,
            current,
            path.items,
            .assoc_ltr,
        )) orelse return null;
        current = stepped.root;
        chain.* = (try self.joinChain(
            relation,
            base_from,
            chain.*,
            stepped.label,
            current,
        )) orelse return null;
        return current;
    }

    /// Emit a proof of `rel(from, to)` for two expressions equal modulo
    /// the certified AC laws, recursively under congruence. Emits refl for
    /// identical expressions. Null aborts the ref (clean miss).
    fn alignEmit(
        self: *Lowerer,
        from: ExprId,
        to: ExprId,
    ) AlignErr!?[]const u8 {
        if (self.align_depth >= 64) return null;
        self.align_depth += 1;
        defer self.align_depth -= 1;
        const relation = self.relationForSort(
            self.sortOfExpr(from) orelse return null,
        ) orelse return null;
        if (from == to) {
            return try self.emitLine(
                try self.relIds(relation, from, from),
                relation.refl_id,
                &.{},
            );
        }
        const fa = self.exprApp(from) orelse return null;
        const ta = self.exprApp(to) orelse return null;
        if (fa.term_id != ta.term_id) return null;
        if (fa.args.len == 2 and self.ac_certs.get(fa.term_id) != null) {
            const cert = self.ac_certs.get(fa.term_id).?;
            return try self.alignAc(fa.term_id, cert, relation, from, to);
        }
        // Congruent descent: one @congr line over child alignments.
        const congr = self.context.registry.congr_by_head.get(
            fa.term_id,
        ) orelse return null;
        const decl = &self.context.env.terms.items[fa.term_id];
        if (decl.args.len != fa.args.len or fa.args.len != ta.args.len) {
            return null;
        }
        var ref_labels: std.ArrayListUnmanaged([]const u8) = .{};
        for (decl.args, fa.args, ta.args) |arg_info, fc, tc| {
            if (arg_info.bound) {
                if (fc != tc) return null;
                continue;
            }
            const label = (try self.alignEmit(fc, tc)) orelse return null;
            try ref_labels.append(self.work, label);
        }
        return try self.emitLine(
            try self.relIds(relation, from, to),
            congr.rule_id,
            ref_labels.items,
        );
    }

    /// The AC seam engine: align two trees over one certified head with
    /// equal member multisets. Route: align members in place, right-nest,
    /// bubble into the target's member order, un-nest into the target's
    /// exact shape.
    fn alignAc(
        self: *Lowerer,
        head: u32,
        cert: AcCert,
        relation: ResolvedRelation,
        from: ExprId,
        to: ExprId,
    ) AlignErr!?[]const u8 {
        var from_members: std.ArrayListUnmanaged(ExprId) = .{};
        var from_paths: std.ArrayListUnmanaged([]const u32) = .{};
        try self.collectAcLeaves(head, from, &.{}, &from_members, &from_paths);
        var to_members: std.ArrayListUnmanaged(ExprId) = .{};
        var to_paths: std.ArrayListUnmanaged([]const u32) = .{};
        try self.collectAcLeaves(head, to, &.{}, &to_members, &to_paths);
        const count = from_members.items.len;
        if (to_members.items.len != count) return null;

        // Pair members: exact expressions first, canonical forms second.
        const pair = try self.work.alloc(?u32, count);
        @memset(pair, null);
        const taken = try self.work.alloc(bool, count);
        @memset(taken, false);
        for (0..count) |i| {
            for (0..count) |j| {
                if (taken[j]) continue;
                if (from_members.items[i] == to_members.items[j]) {
                    pair[i] = @intCast(j);
                    taken[j] = true;
                    break;
                }
            }
        }
        for (0..count) |i| {
            if (pair[i] != null) continue;
            const key = try self.canonKey(from_members.items[i]);
            for (0..count) |j| {
                if (taken[j]) continue;
                if (key == try self.canonKey(to_members.items[j])) {
                    pair[i] = @intCast(j);
                    taken[j] = true;
                    break;
                }
            }
            if (pair[i] == null) return null;
        }

        var chain: ?[]const u8 = null;
        var current = from;
        // Phase 1: align member expressions at their original positions
        // (tree shape is preserved, so the recorded paths stay valid).
        for (0..count) |i| {
            const target_member = to_members.items[pair[i].?];
            if (from_members.items[i] == target_member) continue;
            const sub = (try self.alignEmit(
                from_members.items[i],
                target_member,
            )) orelse return null;
            const lifted = (try self.liftExprLabel(
                current,
                from_paths.items[i],
                target_member,
                sub,
            )) orelse return null;
            current = lifted.root;
            chain = (try self.joinChain(
                relation,
                from,
                chain,
                lifted.label,
                current,
            )) orelse return null;
        }
        // Phase 2: right-nest.
        while (try self.findLtrRedex(head, current)) |path| {
            const stepped = (try self.emitPrimAt(
                head,
                cert,
                current,
                path,
                .assoc_ltr,
            )) orelse return null;
            current = stepped.root;
            chain = (try self.joinChain(
                relation,
                from,
                chain,
                stepped.label,
                current,
            )) orelse return null;
        }
        // Phase 3: bubble the comb members into the target's order. After
        // phase 1 the comb holds the target member expressions in the
        // source's member order.
        const arr = try self.work.alloc(ExprId, count);
        for (0..count) |i| arr[i] = to_members.items[pair[i].?];
        const want = to_members.items;
        for (0..count) |i| {
            if (arr[i] == want[i]) continue;
            var j = i + 1;
            while (j < count) : (j += 1) {
                if (arr[j] == want[i]) break;
            }
            if (j == count) return null;
            while (j > i) : (j -= 1) {
                current = (try self.emitCombSwap(
                    head,
                    cert,
                    relation,
                    from,
                    &chain,
                    current,
                    j - 1,
                    count,
                )) orelse return null;
                std.mem.swap(ExprId, &arr[j - 1], &arr[j]);
            }
        }
        // Phase 4: un-nest into `to`'s exact shape by reversing the plan
        // that right-nests `to`.
        var to_plan: std.ArrayListUnmanaged([]const u32) = .{};
        var sim = to;
        while (try self.findLtrRedex(head, sim)) |path| {
            try to_plan.append(self.work, path);
            sim = (try self.rotateLtr(head, sim, path)) orelse return null;
        }
        if (sim != current) return null;
        var k = to_plan.items.len;
        while (k > 0) {
            k -= 1;
            const stepped = (try self.emitPrimAt(
                head,
                cert,
                current,
                to_plan.items[k],
                .assoc_rtl,
            )) orelse return null;
            current = stepped.root;
            chain = (try self.joinChain(
                relation,
                from,
                chain,
                stepped.label,
                current,
            )) orelse return null;
        }
        if (current != to) return null;
        return chain orelse try self.emitLine(
            try self.relIds(relation, from, to),
            relation.refl_id,
            &.{},
        );
    }

    fn conversionRuleById(
        self: *Lowerer,
        rule_id: u32,
    ) ?rewrite_registry.ConversionRule {
        for (self.context.registry.conversionRules()) |conv| {
            if (conv.rule_id == rule_id) return conv;
        }
        return null;
    }

    fn instantiateTemplate(
        self: *Lowerer,
        template: TemplateExpr,
        bindings: []const ?egraph.BindingValue,
    ) error{ OutOfMemory, TooManyTheoremExprs }!?ExprId {
        switch (template) {
            .binder => |idx| {
                const binding = bindings[idx] orelse return null;
                return switch (binding) {
                    .term => |term| try self.termToExpr(term),
                    .bound => |leaf| try self.theorem.interner.internVar(
                        varIdForLeaf(leaf),
                    ),
                };
            },
            .app => |app| {
                const args = try self.work.alloc(ExprId, app.args.len);
                for (app.args, 0..) |arg, idx| {
                    args[idx] = (try self.instantiateTemplate(
                        arg,
                        bindings,
                    )) orelse return null;
                }
                return try self.theorem.interner.internApp(
                    app.term_id,
                    args,
                );
            },
        }
    }

    /// One extracted rewrite whose redex lives in a bag: the rule instance
    /// in the theorem's own tree shape, wrapped with the extension comb,
    /// aligned at both seams to the canonical comb renderings the chain
    /// traverses, and lifted through the enclosing structure.
    fn emitBagStep(
        self: *Lowerer,
        step: egraph.Step,
        full_before: *const egraph.Term,
        full_after: *const egraph.Term,
    ) !?[]const u8 {
        const info = step.bag.?;
        const rule_id = step.source.rule;
        const conv = self.conversionRuleById(rule_id) orelse return null;
        const lhs_inst = (try self.instantiateTemplate(
            conv.lhs,
            step.bindings,
        )) orelse return null;
        const rhs_inst = (try self.instantiateTemplate(
            conv.rhs,
            step.bindings,
        )) orelse return null;
        const redex_relation = self.relationForSort(
            self.sortOfExpr(lhs_inst) orelse return null,
        ) orelse return null;
        var label = (try self.emitLine(
            try self.relIds(redex_relation, lhs_inst, rhs_inst),
            rule_id,
            &.{},
        )) orelse return null;
        var inst_before = lhs_inst;
        var inst_after = rhs_inst;
        if (step.needs_symm) {
            inst_before = rhs_inst;
            inst_after = lhs_inst;
            label = (try self.emitLine(
                try self.relIds(redex_relation, inst_before, inst_after),
                redex_relation.symm_id,
                &.{label},
            )) orelse return null;
        }

        // Extension: complement of the matched member indices on a bag
        // endpoint (both endpoints carry the same representatives).
        var head: u32 = 0;
        var ext_exprs: std.ArrayListUnmanaged(ExprId) = .{};
        const before_node = self.eg.nodes.items[step.before.node].node;
        const after_node = self.eg.nodes.items[step.after.node].node;
        if (before_node == .bag) {
            head = before_node.bag.term_id;
            for (step.before.children, 0..) |child, idx| {
                if (std.mem.indexOfScalar(
                    u32,
                    info.matched_before,
                    @intCast(idx),
                ) != null) continue;
                const expr = (try self.termToExpr(child.?)) orelse {
                    return null;
                };
                try ext_exprs.append(self.work, expr);
            }
        } else if (after_node == .bag) {
            head = after_node.bag.term_id;
            for (step.after.children, 0..) |child, idx| {
                if (std.mem.indexOfScalar(
                    u32,
                    info.matched_after,
                    @intCast(idx),
                ) != null) continue;
                const expr = (try self.termToExpr(child.?)) orelse {
                    return null;
                };
                try ext_exprs.append(self.work, expr);
            }
        } else {
            return null;
        }

        var x_before = inst_before;
        var x_after = inst_after;
        var step_label = label;
        if (ext_exprs.items.len != 0) {
            var idx = ext_exprs.items.len - 1;
            var ext_comb = ext_exprs.items[idx];
            while (idx > 0) {
                idx -= 1;
                ext_comb = try self.theorem.interner.internApp(
                    head,
                    &.{ ext_exprs.items[idx], ext_comb },
                );
            }
            x_before = try self.theorem.interner.internApp(
                head,
                &.{ inst_before, ext_comb },
            );
            x_after = try self.theorem.interner.internApp(
                head,
                &.{ inst_after, ext_comb },
            );
            const congr = self.context.registry.congr_by_head.get(
                head,
            ) orelse return null;
            const ext_rel = self.relationForSort(
                self.sortOfExpr(ext_comb) orelse return null,
            ) orelse return null;
            const refl_label = (try self.emitLine(
                try self.relIds(ext_rel, ext_comb, ext_comb),
                ext_rel.refl_id,
                &.{},
            )) orelse return null;
            const parent_rel = self.relationForSort(
                self.sortOfExpr(x_before) orelse return null,
            ) orelse return null;
            step_label = (try self.emitLine(
                try self.relIds(parent_rel, x_before, x_after),
                congr.rule_id,
                &.{ label, refl_label },
            )) orelse return null;
        }

        // Seam alignments to the canonical comb renderings.
        const before_expr = (try self.termToExpr(step.before)) orelse {
            return null;
        };
        const after_expr = (try self.termToExpr(step.after)) orelse {
            return null;
        };
        const seam_rel = self.relationForSort(
            self.sortOfExpr(before_expr) orelse return null,
        ) orelse return null;
        var chain = step_label;
        if (before_expr != x_before) {
            const pre = (try self.alignEmit(
                before_expr,
                x_before,
            )) orelse return null;
            chain = (try self.emitLine(
                try self.relIds(seam_rel, before_expr, x_after),
                seam_rel.trans_id,
                &.{ pre, chain },
            )) orelse return null;
        }
        if (x_after != after_expr) {
            const post = (try self.alignEmit(
                x_after,
                after_expr,
            )) orelse return null;
            chain = (try self.emitLine(
                try self.relIds(seam_rel, before_expr, after_expr),
                seam_rel.trans_id,
                &.{ chain, post },
            )) orelse return null;
        }

        // Lift through the enclosing structure.
        var depth = step.position.len;
        while (depth > 0) {
            depth -= 1;
            const before_parent = termAt(
                full_before,
                step.position[0..depth],
            ) orelse return null;
            const after_parent = termAt(
                full_after,
                step.position[0..depth],
            ) orelse return null;
            chain = (try self.emitParentCongruence(
                before_parent,
                after_parent,
                step.position[depth],
                chain,
            )) orelse return null;
        }
        return chain;
    }

    fn emitParentCongruence(
        self: *Lowerer,
        before_parent: *const egraph.Term,
        after_parent: *const egraph.Term,
        changed_idx: u32,
        child_label: []const u8,
    ) !?[]const u8 {
        return switch (self.eg.nodes.items[before_parent.node].node) {
            .bag => try self.emitBagCongruence(
                before_parent,
                after_parent,
                changed_idx,
                child_label,
            ),
            else => try self.emitCongruence(
                before_parent,
                after_parent,
                changed_idx,
                child_label,
            ),
        };
    }

    /// Congruence lift of one member proof through a bag's canonical
    /// comb: binary `@congr` lines down the spine to the changed member.
    fn emitBagCongruence(
        self: *Lowerer,
        before_parent: *const egraph.Term,
        after_parent: *const egraph.Term,
        changed_idx: u32,
        child_label: []const u8,
    ) !?[]const u8 {
        const bag = switch (self.eg.nodes.items[before_parent.node].node) {
            .bag => |bag| bag,
            else => return null,
        };
        const head = bag.term_id;
        const congr = self.context.registry.congr_by_head.get(
            head,
        ) orelse return null;
        const count = before_parent.children.len;
        if (after_parent.children.len != count) return null;
        if (changed_idx >= count) return null;

        // Suffix combs of both renderings.
        const before_combs = try self.work.alloc(ExprId, count);
        const after_combs = try self.work.alloc(ExprId, count);
        var idx = count;
        while (idx > 0) {
            idx -= 1;
            const bc = (try self.termToExpr(
                before_parent.children[idx].?,
            )) orelse return null;
            const ac = (try self.termToExpr(
                after_parent.children[idx].?,
            )) orelse return null;
            if (idx == count - 1) {
                before_combs[idx] = bc;
                after_combs[idx] = ac;
            } else {
                before_combs[idx] = try self.theorem.interner.internApp(
                    head,
                    &.{ bc, before_combs[idx + 1] },
                );
                after_combs[idx] = try self.theorem.interner.internApp(
                    head,
                    &.{ ac, after_combs[idx + 1] },
                );
            }
        }

        var label = child_label;
        const m: usize = changed_idx;
        const relation = self.relationForSort(
            self.sortOfExpr(before_combs[0]) orelse return null,
        ) orelse return null;
        if (m != count - 1) {
            const tail_rel = self.relationForSort(
                self.sortOfExpr(before_combs[m + 1]) orelse return null,
            ) orelse return null;
            const refl_tail = (try self.emitLine(
                try self.relIds(
                    tail_rel,
                    before_combs[m + 1],
                    before_combs[m + 1],
                ),
                tail_rel.refl_id,
                &.{},
            )) orelse return null;
            label = (try self.emitLine(
                try self.relIds(relation, before_combs[m], after_combs[m]),
                congr.rule_id,
                &.{ label, refl_tail },
            )) orelse return null;
        }
        var i = m;
        while (i > 0) {
            i -= 1;
            const member_expr = (try self.termToExpr(
                before_parent.children[i].?,
            )) orelse return null;
            const member_rel = self.relationForSort(
                self.sortOfExpr(member_expr) orelse return null,
            ) orelse return null;
            const refl_member = (try self.emitLine(
                try self.relIds(member_rel, member_expr, member_expr),
                member_rel.refl_id,
                &.{},
            )) orelse return null;
            label = (try self.emitLine(
                try self.relIds(relation, before_combs[i], after_combs[i]),
                congr.rule_id,
                &.{ refl_member, label },
            )) orelse return null;
        }
        return label;
    }

    fn renderRefText(self: *Lowerer, ref: ProofScript.Ref) ![]const u8 {
        return switch (ref) {
            .hyp => |hyp| try std.fmt.allocPrint(
                self.work,
                "#{d}",
                .{hyp.index},
            ),
            .line => |line| line.label,
            .application => error.UnexpectedInlineRef,
        };
    }

    /// Produce the replacement text for the whole placeholder line: the
    /// chain lines proving `rel(ref, goal)` followed by the original line
    /// transported from the ref. Null aborts this ref (clean miss). The
    /// chain's endpoints are the written reference and written goal; when
    /// bags are in play the canonical comb renderings the chain traverses
    /// are aligned to them at both seams.
    fn lower(
        self: *Lowerer,
        ref: ProofScript.Ref,
        ref_term: *const egraph.Term,
        ref_expr: ExprId,
        steps: []const egraph.Step,
    ) !?[]const u8 {
        const root_relation = self.relationForTerm(ref_term) orelse return null;
        const transport_id = root_relation.transport_id orelse return null;

        var current = ref_term;
        var current_expr = (try self.termToExpr(ref_term)) orelse return null;
        var chain_label: ?[]const u8 = null;
        if (ref_expr != current_expr) {
            chain_label = (try self.alignEmit(
                ref_expr,
                current_expr,
            )) orelse return null;
        }
        for (steps) |step| {
            const next = (try self.replaceAt(
                current,
                step.position,
                step.before,
                step.after,
            )) orelse return null;
            const step_label = (try self.emitStep(
                step,
                current,
                next,
            )) orelse return null;
            const next_expr = (try self.termToExpr(next)) orelse return null;
            if (chain_label) |prev| {
                chain_label = (try self.emitLine(
                    try self.relIds(root_relation, ref_expr, next_expr),
                    root_relation.trans_id,
                    &.{ prev, step_label },
                )) orelse return null;
            } else {
                chain_label = step_label;
            }
            current = next;
            current_expr = next_expr;
        }
        if (current_expr != self.goal_expr) {
            const seam = (try self.alignEmit(
                current_expr,
                self.goal_expr,
            )) orelse return null;
            if (chain_label) |prev| {
                chain_label = (try self.emitLine(
                    try self.relIds(root_relation, ref_expr, self.goal_expr),
                    root_relation.trans_id,
                    &.{ prev, seam },
                )) orelse return null;
            } else {
                chain_label = seam;
            }
        }
        if (chain_label == null) {
            // Zero steps: the two formulas are already structurally equal;
            // transport still needs a relation proof, so emit refl.
            chain_label = (try self.emitLine(
                try self.relIds(root_relation, ref_expr, ref_expr),
                root_relation.refl_id,
                &.{},
            )) orelse return null;
        }

        // The original line, verbatim label and assertion, transported.
        const line = self.target_line;
        const writer = self.out.writer(self.work);
        try writer.print("{s}{s}: {s} by {s} [{s}, {s}]", .{
            self.indent,
            line.label,
            self.proof_src[line.assertion.span.start..line.assertion.span.end],
            self.ruleName(transport_id),
            chain_label.?,
            try self.renderRefText(ref),
        });
        try writer.writeAll(
            self.proof_src[line.application.span.end..line.span.end],
        );
        return try self.out.toOwnedSlice(self.work);
    }
};

fn termAt(
    term: *const egraph.Term,
    position: []const u32,
) ?*const egraph.Term {
    var current = term;
    for (position) |idx| {
        if (idx >= current.children.len) return null;
        current = current.children[idx] orelse return null;
    }
    return current;
}
