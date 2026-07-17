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
const GlobalEnv = @import("../../env.zig").GlobalEnv;
const Context = types.Context;
const NameExprMap = types.NameExprMap;

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

    // Rules: one egraph orientation per enrolled direction, declaration
    // order (deterministic).
    var rules: std.ArrayListUnmanaged(egraph.Rule) = .{};
    for (context.registry.conversionRules()) |conv| {
        if (conv.ltr) try rules.append(work, .{
            .rule_id = conv.rule_id,
            .reversed = false,
            .match_side = conv.lhs,
            .target_side = conv.rhs,
            .num_binders = conv.num_binders,
        });
        if (conv.rtl) try rules.append(work, .{
            .rule_id = conv.rule_id,
            .reversed = true,
            .match_side = conv.rhs,
            .target_side = conv.lhs,
            .num_binders = conv.num_binders,
        });
    }
    result.rule_count = rules.items.len;
    if (rules.items.len == 0) return result;

    var eg = egraph.EGraph.init(work);
    // The congruence gate: only heads with a `@congr` proof step may drive
    // congruence unions. Set semantics, so hash-map iteration order is fine.
    var congr_it = context.registry.congr_by_head.keyIterator();
    while (congr_it.next()) |head| {
        try eg.congr_heads.put(work, head.*, {});
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

    const goal_term = (try addExpr(&eg, context.env, theorem, goal)) orelse {
        return result;
    };

    const pool = try Refs.buildReferencePool(work, context, theorem);
    result.pool_size = pool.len;
    var pool_terms = try work.alloc(?*const egraph.Term, pool.len);
    for (pool, 0..) |entry, idx| {
        const expr = Refs.sourceRefExpr(context, theorem, entry.ref) catch {
            pool_terms[idx] = null;
            continue;
        };
        pool_terms[idx] = try addExpr(&eg, context.env, theorem, expr);
    }

    result.stats = try eg.saturate(rules.items, .{
        .max_iterations = opts.max_iterations,
        .max_nodes = opts.max_nodes,
    });
    result.classes = eg.classCount();
    result.nodes = eg.eNodeCount();

    const goal_class = termClass(&eg, goal_term);
    for (pool, pool_terms) |entry, maybe_term| {
        const ref_term = maybe_term orelse continue;
        if (!eg.sameClass(termClass(&eg, ref_term), goal_class)) continue;
        const steps = (try eg.explain(
            rules.items,
            ref_term,
            goal_term,
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
        if (try lowerer.lower(entry.ref, ref_term, steps)) |replacement| {
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

/// Lowers one explanation into proof-script source text. Every emitted line
/// asserts its full conclusion, so unification replay solves all rule
/// binders — no explicit bindings are needed on any line.
const Lowerer = struct {
    work: std.mem.Allocator,
    context: *const Context,
    theorem: *TheoremContext,
    eg: *egraph.EGraph,
    names: ViewTrace.DiagNames,
    proof_src: []const u8,
    target_line: ProofScript.ProofLine,
    indent: []const u8,
    used_labels: std.StringHashMapUnmanaged(void) = .{},
    label_counter: usize = 0,
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
        return try self.theorem.interner.internApp(
            relation.rel_term_id,
            &.{ lhs_expr, rhs_expr },
        );
    }

    /// Emit `label: $ <formula> $ by <rule> [refs...]` and return the label.
    fn emitLine(
        self: *Lowerer,
        formula: ExprId,
        rule_id: u32,
        ref_labels: []const []const u8,
    ) !?[]const u8 {
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
    /// instance (through `symm` when traversed backwards), lifted through
    /// one `@congr` application per enclosing level with `refl` siblings.
    /// Returns the label proving the root-level relation.
    fn emitStep(
        self: *Lowerer,
        step: egraph.Step,
        full_before: *const egraph.Term,
        full_after: *const egraph.Term,
    ) !?[]const u8 {
        // Redex-level rule instance.
        const redex_relation = self.relationForTerm(step.before) orelse
            self.relationForTerm(step.after) orelse return null;
        const thm_lhs = if (step.needs_symm) step.after else step.before;
        const thm_rhs = if (step.needs_symm) step.before else step.after;
        const instance = (try self.relExpr(
            redex_relation,
            thm_lhs,
            thm_rhs,
        )) orelse return null;
        var label = (try self.emitLine(instance, step.rule_id, &.{})) orelse {
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

        // Congruence lifting, innermost level first.
        var depth = step.position.len;
        while (depth > 0) {
            depth -= 1;
            const before_parent = termAt(full_before, step.position[0..depth]) orelse
                return null;
            const after_parent = termAt(full_after, step.position[0..depth]) orelse
                return null;
            label = (try self.emitCongruence(
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
    /// transported from the ref. Null aborts this ref (clean miss).
    fn lower(
        self: *Lowerer,
        ref: ProofScript.Ref,
        ref_term: *const egraph.Term,
        steps: []const egraph.Step,
    ) !?[]const u8 {
        const root_relation = self.relationForTerm(ref_term) orelse return null;
        const transport_id = root_relation.transport_id orelse return null;

        var current = ref_term;
        var chain_label: ?[]const u8 = null;
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
            if (chain_label) |prev| {
                const formula = (try self.relExpr(
                    root_relation,
                    ref_term,
                    next,
                )) orelse return null;
                chain_label = (try self.emitLine(
                    formula,
                    root_relation.trans_id,
                    &.{ prev, step_label },
                )) orelse return null;
            } else {
                chain_label = step_label;
            }
            current = next;
        }
        if (chain_label == null) {
            // Zero steps: the two formulas are already structurally equal;
            // transport still needs a relation proof, so emit refl.
            const formula = (try self.relExpr(
                root_relation,
                ref_term,
                ref_term,
            )) orelse return null;
            chain_label = (try self.emitLine(
                formula,
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
