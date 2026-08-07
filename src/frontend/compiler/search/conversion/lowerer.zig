//! Explanation lowering for conversion?: turns an egraph explanation chain
//! into proof-script source text (split out of conversion.zig; the one
//! construction site is conversion.zig's run()).
//!
//! On theories with `@rewrite` rules the lowering emits BIG STEPS: a rule
//! step whose result spawns a rewrite cascade (a beta step's substitution
//! ladder) absorbs the in-redex `@rewrite` steps that follow it into one
//! line stated in rewrite-normalized form, which line-check conclusion
//! normalization re-derives (see "Big-step grouping" below).

const std = @import("std");
const egraph = @import("../egraph.zig");
const types = @import("../types.zig");
const Refs = @import("../refs.zig");
const ProofScript = @import("../../../proof_script.zig");
const expr_mod = @import("../../../expr.zig");
const ExprId = expr_mod.ExprId;
const TheoremContext = expr_mod.TheoremContext;
const ViewTrace = @import("../../../view_trace.zig");
const rewrite_registry = @import("../../../rewrite_registry.zig");
const ResolvedRelation = rewrite_registry.ResolvedRelation;
const TemplateExpr = @import("../../../rules.zig").TemplateExpr;
const templateBinderMask = @import("../../../rules.zig").templateBinderMask;
const Context = types.Context;

const conversion = @import("../conversion.zig");
const AcCert = conversion.AcCert;
const AcCertMap = conversion.AcCertMap;
const varIdForLeaf = conversion.varIdForLeaf;
const flattenAcExpr = conversion.flattenAcExpr;
const Normalizer = @import("../../../normalizer.zig").Normalizer;
const CheckedLine = @import("../../checked_ir.zig").CheckedLine;

/// A reference as it is written in a proof line: `#name`/`#index` for a
/// hypothesis, the label for an earlier line. Depends on nothing but the
/// allocator, so the driver can render one without a lowering attempt.
pub fn renderRefText(
    work: std.mem.Allocator,
    ref: ProofScript.Ref,
) ![]const u8 {
    return switch (ref) {
        .hyp => |hyp| if (hyp.name) |name|
            try std.fmt.allocPrint(work, "#{s}", .{name})
        else
            try std.fmt.allocPrint(work, "#{d}", .{hyp.index}),
        .line => |line| line.label,
        .application => error.UnexpectedInlineRef,
    };
}

/// Lowers one explanation into proof-script source text. Every emitted line
/// asserts its full conclusion, so unification replay solves all rule
/// binders — no explicit bindings are needed on any line.
pub const Lowerer = struct {
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
    /// Set when a null return came from an emission cap rather than a
    /// structural gap — the driver reports the two differently.
    cap_tripped: bool = false,
    /// Lazily built checker-equivalent rewrite normalizer for big-step
    /// grouping (see `tryBigStep`).
    norm_state: ?*NormState = null,
    out: std.ArrayListUnmanaged(u8) = .{},

    const NormState = struct {
        /// Proof lines the normalizer emits as it reduces; discarded —
        /// only the resulting expressions gate the grouping.
        lines: std.ArrayListUnmanaged(CheckedLine) = .{},
        normalizer: Normalizer,
    };

    pub fn seedLabels(
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
        if (self.lines_emitted > 4096) {
            self.cap_tripped = true;
            return null;
        }
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
    /// root-level relation. A big-step group passes the driving step with
    /// `after` replaced by the group's final redex, so the rule line may
    /// state a rewrite-normalized result side.
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
                // A def step: the endpoints denote the same term up to
                // transparent unfolding (the matched dummy witness is part
                // of the stated formula), so one `refl` line states the
                // boundary in traversal order and the checker closes it.
                // No symm — refl is orientation-free here.
                if (conversion.defRuleTermId(rule_id) != null) {
                    const instance = (try self.relExpr(
                        redex_relation,
                        step.before,
                        step.after,
                    )) orelse return null;
                    label = (try self.emitLine(
                        instance,
                        redex_relation.refl_id,
                        &.{},
                    )) orelse return null;
                } else {
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
                }
            },
            // The pool entry asserts rel(before, after) — or its flip —
            // in its own written form. Cite it (through symm when
            // traversed backwards); when the chain's canonical renderings
            // differ from the written sides (AC bags), align the seams.
            .pool_equation => |pool_idx| {
                label = try renderRefText(self.work, self.pool[pool_idx].ref);
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
                        redex_relation.sort_name,
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
                        redex_relation.sort_name,
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
            // A splice re-tree: both endpoints carry the same member
            // multiset, so the whole step is one AC seam alignment.
            .ac_flatten => {
                const before_expr = (try self.termToExpr(
                    step.before,
                )) orelse return null;
                const after_expr = (try self.termToExpr(
                    step.after,
                )) orelse return null;
                label = (try self.alignEmit(
                    before_expr,
                    after_expr,
                    redex_relation.sort_name,
                )) orelse return null;
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
    /// `sort_hint` supplies the sort when the expression itself cannot
    /// (a dummy variable has no interned sort); the congruent descent
    /// passes each child's declared arg sort.
    fn alignEmit(
        self: *Lowerer,
        from: ExprId,
        to: ExprId,
        sort_hint: ?[]const u8,
    ) AlignErr!?[]const u8 {
        if (self.align_depth >= 64) {
            self.cap_tripped = true;
            return null;
        }
        self.align_depth += 1;
        defer self.align_depth -= 1;
        const relation = self.relationForSort(
            self.sortOfExpr(from) orelse sort_hint orelse return null,
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
            const label = (try self.alignEmit(
                fc,
                tc,
                arg_info.sort_name,
            )) orelse return null;
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
                self.context.env.terms.items[head].args[0].sort_name,
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
        // `@compute` enrollments cite through the same rule id space and
        // lower identically (their unions are ordinary rule unions).
        for (self.context.registry.computeRules()) |comp| {
            if (comp.rule_id == rule_id) return comp;
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
        const sides: struct { lhs: TemplateExpr, rhs: TemplateExpr } =
            if (conversion.defRuleTermId(rule_id)) |term_id| blk: {
                const def_conv = self.context.registry.defConversionByTerm(
                    term_id,
                ) orelse return null;
                break :blk .{ .lhs = def_conv.lhs, .rhs = def_conv.rhs };
            } else blk: {
                const conv = self.conversionRuleById(rule_id) orelse {
                    return null;
                };
                break :blk .{ .lhs = conv.lhs, .rhs = conv.rhs };
            };
        const lhs_inst = (try self.instantiateTemplate(
            sides.lhs,
            step.bindings,
        )) orelse return null;
        const rhs_inst = (try self.instantiateTemplate(
            sides.rhs,
            step.bindings,
        )) orelse return null;
        const redex_relation = self.relationForSort(
            self.sortOfExpr(lhs_inst) orelse return null,
        ) orelse return null;
        var inst_before = lhs_inst;
        var inst_after = rhs_inst;
        if (step.needs_symm) {
            inst_before = rhs_inst;
            inst_after = lhs_inst;
        }
        var label: []const u8 = undefined;
        if (conversion.defRuleTermId(rule_id) != null) {
            // A def step lowers as one orientation-free `refl` line (see
            // emitStep); the swap above already put the instances in
            // traversal order.
            label = (try self.emitLine(
                try self.relIds(redex_relation, inst_before, inst_after),
                redex_relation.refl_id,
                &.{},
            )) orelse return null;
        } else {
            label = (try self.emitLine(
                try self.relIds(redex_relation, lhs_inst, rhs_inst),
                rule_id,
                &.{},
            )) orelse return null;
            if (step.needs_symm) {
                label = (try self.emitLine(
                    try self.relIds(redex_relation, inst_before, inst_after),
                    redex_relation.symm_id,
                    &.{label},
                )) orelse return null;
            }
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
                seam_rel.sort_name,
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
                seam_rel.sort_name,
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
        // Sorts come from the head's declaration, not the expressions: a
        // bare member can be a dummy variable, which has no interned sort.
        const head_decl = &self.context.env.terms.items[head];
        const relation = self.relationForSort(
            head_decl.ret_sort_name,
        ) orelse return null;
        if (m != count - 1) {
            const tail_rel = self.relationForSort(
                head_decl.args[1].sort_name,
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
                head_decl.args[0].sort_name,
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

    // --- Big-step grouping ---------------------------------------------
    //
    // One elementary rewrite costs a whole stanza (rule instance, symm
    // orientation, a congruence ladder to the root, a trans splice), so a
    // fold step that spawns a substitution cascade emits steps x depth
    // lines. But a cited rule's conclusion may be *stated in reduced
    // form*: line-check conclusion normalization replays the `@rewrite`
    // registry against it (the manual's `beta_step` idiom). Grouping
    // exploits that — a driving rule step absorbs the in-redex `@rewrite`
    // steps that follow it and emits ONE line whose result side is the
    // rewrite normal form; the checker re-derives the absorbed cascade.

    /// The lazily built checker-equivalent normalizer (the `@rewrite`
    /// registry applied to fixpoint). The proof lines it emits are
    /// discarded — only the resulting expressions gate the grouping.
    fn normState(self: *Lowerer) !*NormState {
        return self.norm_state orelse blk: {
            const state = try self.work.create(NormState);
            state.* = .{ .normalizer = undefined };
            state.normalizer = Normalizer.init(
                self.work,
                self.theorem,
                self.context.registry,
                self.context.env,
                &state.lines,
            );
            self.norm_state = state;
            break :blk state;
        };
    }

    /// Normal form under the checker's own line normalizer. The step
    /// budget resets per call to mirror the checker's per-line budget.
    fn rewriteNormalForm(self: *Lowerer, expr: ExprId) !ExprId {
        const state = try self.normState();
        state.normalizer.step_count = 0;
        const result = try state.normalizer.normalize(expr);
        return result.result_expr;
    }

    /// Whether a rule step can drive a big-step group: a plain (non-def,
    /// non-bag) theorem citation whose result still carries `@rewrite`
    /// residue, and whose intact stated side binds every binder the
    /// reduced side mentions (a binder occurring only in rewritten-away
    /// structure would leave the emitted line uninferable). False keeps
    /// the elementary stanza.
    fn canDriveBigStep(self: *Lowerer, step: egraph.Step) !bool {
        if (step.bag != null) return false;
        const rule_id = switch (step.source) {
            .rule => |rule_id| rule_id,
            else => return false,
        };
        if (conversion.defRuleTermId(rule_id) != null) return false;
        if (!self.context.registry.hasRewriteRules()) return false;
        const conv = self.conversionRuleById(rule_id) orelse return false;
        const intact = if (step.needs_symm) conv.rhs else conv.lhs;
        const reduced = if (step.needs_symm) conv.lhs else conv.rhs;
        const intact_mask = templateBinderMask(intact);
        const reduced_mask = templateBinderMask(reduced);
        // A binder index past the mask's width would under-count the
        // coverage requirement; abstain from grouping rather than guess.
        if (intact_mask.overflow or reduced_mask.overflow) return false;
        if (intact_mask.mask & reduced_mask.mask != reduced_mask.mask) {
            return false;
        }
        const after_expr = (try self.termToExpr(step.after)) orelse {
            return false;
        };
        return (try self.rewriteNormalForm(after_expr)) != after_expr;
    }

    /// True when a step can fold into the enclosing big-step group: an
    /// in-redex application of an `@rewrite`-enrolled rule, in either
    /// direction — line-check normalization replays the forward ones, and
    /// a backward detour is fine as long as the group's final form shares
    /// the normal form (the commit gate checks exactly that). Anything
    /// else (a def boundary, a pool citation, an AC re-tree, a step
    /// outside the driving redex) ends the group.
    fn isAbsorbableDebris(
        self: *Lowerer,
        step: egraph.Step,
        driver_position: []const u32,
    ) bool {
        if (step.bag != null) return false;
        const rule_id = switch (step.source) {
            .rule => |rule_id| rule_id,
            else => return false,
        };
        if (conversion.defRuleTermId(rule_id) != null) return false;
        if (!std.mem.startsWith(u32, step.position, driver_position)) {
            return false;
        }
        // The rewrite's match side sits on the `before` endpoint of a
        // forward step and the `after` endpoint of a backward one.
        return self.rewriteRuleAtHead(rule_id, step.before) or
            self.rewriteRuleAtHead(rule_id, step.after);
    }

    fn rewriteRuleAtHead(
        self: *Lowerer,
        rule_id: u32,
        term: *const egraph.Term,
    ) bool {
        const head = switch (self.eg.nodes.items[term.node].node) {
            .app => |app| app.term_id,
            else => return false,
        };
        for (self.context.registry.getRewriteRules(head)) |rule| {
            if (rule.rule_id == rule_id) return true;
        }
        return false;
    }

    /// A committed big-step group: the root after every absorbed step,
    /// the driving redex's result in rewrite-normalized form, and how
    /// many steps the group consumed.
    const BigStep = struct {
        root: *const egraph.Term,
        redex_after: *const egraph.Term,
        consumed: usize,
    };

    /// Try to extend the driving step at `idx` into a big-step group:
    /// absorb the following in-redex `@rewrite` steps and state one
    /// conclusion whose result side is the rewrite normal form.
    /// Committed only when the checker's own normalized comparison
    /// accepts the stated line (see `checkerAcceptsBigStep`), so an
    /// emitted big-step line always checks; anything short falls back to
    /// the elementary stanzas.
    fn tryBigStep(
        self: *Lowerer,
        steps: []const egraph.Step,
        idx: usize,
        first_next: *const egraph.Term,
    ) !?BigStep {
        const step = steps[idx];
        if (!try self.canDriveBigStep(step)) return null;
        var root = first_next;
        var end = idx + 1;
        while (end < steps.len and
            self.isAbsorbableDebris(steps[end], step.position))
        {
            root = (try self.replaceAt(
                root,
                steps[end].position,
                steps[end].before,
                steps[end].after,
            )) orelse break;
            end += 1;
        }
        if (end == idx + 1) return null;
        const redex_after = termAt(root, step.position) orelse return null;
        if (!try self.checkerAcceptsBigStep(step, redex_after)) {
            return null;
        }
        return .{
            .root = root,
            .redex_after = redex_after,
            .consumed = end - idx,
        };
    }

    /// The commit gate for a big-step group: replay the checker's own
    /// acceptance test on the rule line the group will emit. That line
    /// states the driving rule's conclusion with its result side replaced
    /// by the group's final redex, so line-check falls through to
    /// normalized comparison — which needs a relation registered for the
    /// formula's sort, a transport to rebase the proof onto the stated
    /// form, and rewrite normalization that joins the stated and derived
    /// conclusions (descent through the relation head needs a `@congr`
    /// lifting it into the formula relation). Running the same comparison
    /// here keeps groups from forming when the theory cannot replay them.
    fn checkerAcceptsBigStep(
        self: *Lowerer,
        step: egraph.Step,
        redex_after: *const egraph.Term,
    ) !bool {
        const relation = self.relationForTerm(step.before) orelse
            self.relationForTerm(step.after) orelse return false;
        const before_expr = (try self.termToExpr(step.before)) orelse {
            return false;
        };
        const after_expr = (try self.termToExpr(step.after)) orelse {
            return false;
        };
        const redex_expr = (try self.termToExpr(redex_after)) orelse {
            return false;
        };
        // Oriented the way emitStep states the rule line (the symm flip
        // it appends for backward steps is an exact instance and always
        // checks).
        const stated = if (step.needs_symm)
            try self.relIds(relation, redex_expr, before_expr)
        else
            try self.relIds(relation, before_expr, redex_expr);
        const derived = if (step.needs_symm)
            try self.relIds(relation, after_expr, before_expr)
        else
            try self.relIds(relation, before_expr, after_expr);
        const state = try self.normState();
        const line_relation = state.normalizer.resolveRelationForExpr(
            derived,
        ) orelse return false;
        if (line_relation.transport_id == null) return false;
        // One budget across both sides, as in the checker's
        // buildNormalizedConversion.
        state.normalizer.step_count = 0;
        const norm_derived = try state.normalizer.normalize(derived);
        const norm_stated = try state.normalizer.normalize(stated);
        return norm_derived.result_expr == norm_stated.result_expr;
    }

    /// Produce the replacement text for the whole placeholder line: the
    /// chain lines proving `rel(ref, goal)` followed by the original line
    /// transported from the ref. Null aborts this ref (clean miss). The
    /// chain's endpoints are the written reference and written goal; when
    /// bags are in play the canonical comb renderings the chain traverses
    /// are aligned to them at both seams.
    pub fn lower(
        self: *Lowerer,
        ref: ProofScript.Ref,
        ref_term: *const egraph.Term,
        ref_expr: ExprId,
        steps: []const egraph.Step,
    ) !?[]const u8 {
        return try self.lowerOriented(
            ref,
            ref_term,
            ref_expr,
            self.goal_expr,
            steps,
            false,
        );
    }

    /// Reversed-orientation variant: walk the chain from the goal term to
    /// the reference and flip the finished chain with one `symm` line.
    /// When the reference is the reduced side (a `refl` line grounding a
    /// computation), the given explanation traverses the fold backwards —
    /// every rule through `symm`, each rule's rewrite cascade *preceding*
    /// it — and no big-step group can form. The same steps reversed run in
    /// the reducing direction, where each fold step is followed by its
    /// cascade and big-step grouping collapses it. The driver lowers both
    /// orientations and keeps the shorter emission.
    pub fn lowerReversed(
        self: *Lowerer,
        ref: ProofScript.Ref,
        goal_term: *const egraph.Term,
        ref_expr: ExprId,
        reversed_steps: []const egraph.Step,
    ) !?[]const u8 {
        return try self.lowerOriented(
            ref,
            goal_term,
            self.goal_expr,
            ref_expr,
            reversed_steps,
            true,
        );
    }

    /// Equation goals: the target line itself asserts `rel(lhs, rhs)` for
    /// a registered relation and both sides landed in one e-class, so the
    /// lhs→rhs chain IS the goal — no pool reference, no transport. The
    /// final line restates the target verbatim: `trans [refl(lhs), chain]`
    /// forward, one `symm [chain]` when the chain was lowered reversed, or
    /// a bare `refl` when the sides are structurally identical.
    pub fn lowerEquation(
        self: *Lowerer,
        start_term: *const egraph.Term,
        start_expr: ExprId,
        end_expr: ExprId,
        steps: []const egraph.Step,
        reversed: bool,
    ) !?[]const u8 {
        const root_relation = self.relationForTerm(start_term) orelse {
            return null;
        };
        const chain: ?[]const u8 = switch (try self.emitChain(
            root_relation,
            start_term,
            start_expr,
            end_expr,
            steps,
        )) {
            .label => |label| label,
            .empty => null,
            .failed => return null,
        };
        if (chain) |label| {
            if (reversed) {
                try self.printTargetLine(root_relation.symm_id, &.{label});
            } else {
                const refl_label = (try self.emitLine(
                    try self.relIds(root_relation, start_expr, start_expr),
                    root_relation.refl_id,
                    &.{},
                )) orelse return null;
                try self.printTargetLine(
                    root_relation.trans_id,
                    &.{ refl_label, label },
                );
            }
        } else {
            try self.printTargetLine(root_relation.refl_id, &.{});
        }
        return try self.out.toOwnedSlice(self.work);
    }

    fn lowerOriented(
        self: *Lowerer,
        ref: ProofScript.Ref,
        start_term: *const egraph.Term,
        start_expr: ExprId,
        end_expr: ExprId,
        steps: []const egraph.Step,
        reversed: bool,
    ) !?[]const u8 {
        const root_relation = self.relationForTerm(start_term) orelse {
            return null;
        };
        const transport_id = root_relation.transport_id orelse return null;
        const ref_expr = if (reversed) end_expr else start_expr;

        var chain_label: ?[]const u8 = switch (try self.emitChain(
            root_relation,
            start_term,
            start_expr,
            end_expr,
            steps,
        )) {
            .label => |label| label,
            .empty => null,
            .failed => return null,
        };
        // A reversed chain proves rel(goal, ref); the transport needs
        // rel(ref, goal), so flip it once at the root.
        if (reversed) {
            if (chain_label) |prev| {
                chain_label = (try self.emitLine(
                    try self.relIds(root_relation, end_expr, start_expr),
                    root_relation.symm_id,
                    &.{prev},
                )) orelse return null;
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
        try self.printTargetLine(
            transport_id,
            &.{ chain_label.?, try renderRefText(self.work, ref) },
        );
        return try self.out.toOwnedSlice(self.work);
    }

    const Chain = union(enum) {
        /// Label of the emitted line proving rel(start_expr, end_expr).
        label: []const u8,
        /// No steps and no seams: the endpoints are structurally identical.
        empty,
        /// Emission aborted (a cap tripped or a step could not be lifted).
        failed,
    };

    /// Emit the trans-composed conversion chain from `start_term` to
    /// `end_expr`: re-treeing seams at both ends, one stanza per step (with
    /// big-step absorption), trans joins against the running prefix.
    fn emitChain(
        self: *Lowerer,
        root_relation: ResolvedRelation,
        start_term: *const egraph.Term,
        start_expr: ExprId,
        end_expr: ExprId,
        steps: []const egraph.Step,
    ) !Chain {
        var current = start_term;
        var current_expr = (try self.termToExpr(start_term)) orelse {
            return .failed;
        };
        var chain_label: ?[]const u8 = null;
        if (start_expr != current_expr) {
            chain_label = (try self.alignEmit(
                start_expr,
                current_expr,
                root_relation.sort_name,
            )) orelse return .failed;
        }
        var step_idx: usize = 0;
        while (step_idx < steps.len) {
            const step = steps[step_idx];
            var next = (try self.replaceAt(
                current,
                step.position,
                step.before,
                step.after,
            )) orelse return .failed;
            // A driving rule step may absorb its rewrite cascade: the
            // emitted line then cites the rule with its result stated in
            // normalized form, and line-check conclusion normalization
            // re-derives the absorbed steps.
            var emit_step = step;
            var consumed: usize = 1;
            if (try self.tryBigStep(steps, step_idx, next)) |group| {
                emit_step.after = group.redex_after;
                next = group.root;
                consumed = group.consumed;
            }
            const step_label = (try self.emitStep(
                emit_step,
                current,
                next,
            )) orelse return .failed;
            const next_expr = (try self.termToExpr(next)) orelse {
                return .failed;
            };
            if (chain_label) |prev| {
                chain_label = (try self.emitLine(
                    try self.relIds(root_relation, start_expr, next_expr),
                    root_relation.trans_id,
                    &.{ prev, step_label },
                )) orelse return .failed;
            } else {
                chain_label = step_label;
            }
            current = next;
            current_expr = next_expr;
            step_idx += consumed;
        }
        if (current_expr != end_expr) {
            const seam = (try self.alignEmit(
                current_expr,
                end_expr,
                root_relation.sort_name,
            )) orelse return .failed;
            if (chain_label) |prev| {
                chain_label = (try self.emitLine(
                    try self.relIds(root_relation, start_expr, end_expr),
                    root_relation.trans_id,
                    &.{ prev, seam },
                )) orelse return .failed;
            } else {
                chain_label = seam;
            }
        }
        return if (chain_label) |label|
            .{ .label = label }
        else
            .empty;
    }

    /// Re-emit the target line verbatim — the user's label and assertion
    /// text — with a fresh justification.
    fn printTargetLine(
        self: *Lowerer,
        rule_id: u32,
        ref_labels: []const []const u8,
    ) !void {
        const line = self.target_line;
        const writer = self.out.writer(self.work);
        try writer.print("{s}{s}: {s} by {s}", .{
            self.indent,
            line.label,
            self.proof_src[line.assertion.span.start..line.assertion.span.end],
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
        try writer.writeAll(
            self.proof_src[line.application.span.end..line.span.end],
        );
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
