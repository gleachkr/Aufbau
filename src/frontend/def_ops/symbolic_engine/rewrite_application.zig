const std = @import("std");
const ExprId = @import("../../expr.zig").ExprId;
const TemplateExpr = @import("../../rules.zig").TemplateExpr;
const RewriteRule = @import("../../rewrite_registry.zig").RewriteRule;
const BindingValidation = @import("../../binding_validation.zig");
const Types = @import("../types.zig");
const MatchState = @import("../match_state.zig");
const TransparentMatch = @import("./transparent_match.zig");
const WitnessState = @import("./witness_state.zig");

const SymbolicExpr = Types.SymbolicExpr;
const BoundValue = Types.BoundValue;
const MatchSession = MatchState.MatchSession;

/// Resolve a symbolic `.binder` node through the session bindings to its
/// representative value. Rewrite patterns are structural; a rule binder that
/// earlier matching already solved must be transparent to them (a conclusion
/// like `[x := a] e` where `e` was bound through a hidden-def unfold).
pub fn resolveBoundBinderSymbolic(
    self: anytype,
    symbolic: *const SymbolicExpr,
    state: *MatchSession,
) anyerror!*const SymbolicExpr {
    var current = symbolic;
    // A representative can itself be a binder reference; the hop cap breaks
    // any aliasing cycle (an acyclic chain visits distinct binders).
    var hops: usize = 0;
    while (hops <= state.bindings.len) : (hops += 1) {
        const idx = switch (current.*) {
            .binder => |idx| idx,
            else => return current,
        };
        if (idx >= state.bindings.len) return current;
        const bound = state.bindings[idx] orelse return current;
        const repr = try WitnessState.boundValueRepresentative(self, bound);
        if (repr.* == .binder) {
            // Representative selection re-expresses concrete values as binder
            // back-references (possibly to this very binder); the raw concrete
            // expr is the exact resolution.
            switch (bound) {
                .concrete => |concrete| return try self.allocSymbolic(
                    .{ .fixed = concrete.raw },
                ),
                .symbolic => if (repr.binder == idx) return current,
            }
        }
        current = repr;
    }
    return current;
}

pub fn applyRewriteRuleToExpr(
    self: anytype,
    rule: RewriteRule,
    expr_id: ExprId,
    state: *MatchSession,
) anyerror!?*const SymbolicExpr {
    const node = self.shared.theorem.interner.node(expr_id);
    const app = switch (node.*) {
        .app => |value| value,
        .variable => return null,
        .placeholder => return null,
    };
    if (app.term_id != rule.head_term_id) return null;

    var snapshot = try WitnessState.saveMatchSnapshot(self, state);
    defer WitnessState.deinitMatchSnapshot(self, &snapshot);

    const rewrite_bindings = try self.shared.allocator.alloc(
        ?BoundValue,
        rule.num_binders,
    );
    defer self.shared.allocator.free(rewrite_bindings);
    @memset(rewrite_bindings, null);

    if (!try matchRewriteTemplateToExpr(
        self,
        rule.lhs,
        expr_id,
        rewrite_bindings,
        state,
    )) {
        try WitnessState.restoreMatchSnapshot(self, &snapshot, state);
        return null;
    }
    if (!try validateRewriteRuleBindings(
        self,
        rule,
        rewrite_bindings,
        state,
    )) {
        try WitnessState.restoreMatchSnapshot(self, &snapshot, state);
        return null;
    }
    return try instantiateRewriteRuleRhs(
        self,
        rule,
        rewrite_bindings,
    ) orelse blk: {
        try WitnessState.restoreMatchSnapshot(self, &snapshot, state);
        break :blk null;
    };
}

pub fn applyRewriteRuleToSymbolic(
    self: anytype,
    rule: RewriteRule,
    symbolic: *const SymbolicExpr,
    state: *MatchSession,
) anyerror!?*const SymbolicExpr {
    const resolved = try resolveBoundBinderSymbolic(self, symbolic, state);
    return switch (resolved.*) {
        .fixed => |expr_id| try applyRewriteRuleToExpr(
            self,
            rule,
            expr_id,
            state,
        ),
        .app => |app| blk: {
            if (app.term_id != rule.head_term_id) break :blk null;

            var snapshot = try WitnessState.saveMatchSnapshot(self, state);
            defer WitnessState.deinitMatchSnapshot(self, &snapshot);

            const rewrite_bindings = try self.shared.allocator.alloc(
                ?BoundValue,
                rule.num_binders,
            );
            defer self.shared.allocator.free(rewrite_bindings);
            @memset(rewrite_bindings, null);

            if (!try matchRewriteTemplateToSymbolic(
                self,
                rule.lhs,
                resolved,
                rewrite_bindings,
                state,
            )) {
                try WitnessState.restoreMatchSnapshot(self, &snapshot, state);
                break :blk null;
            }
            if (!try validateRewriteRuleBindings(
                self,
                rule,
                rewrite_bindings,
                state,
            )) {
                try WitnessState.restoreMatchSnapshot(self, &snapshot, state);
                break :blk null;
            }
            break :blk try instantiateRewriteRuleRhs(
                self,
                rule,
                rewrite_bindings,
            ) orelse inner: {
                try WitnessState.restoreMatchSnapshot(self, &snapshot, state);
                break :inner null;
            };
        },
        .binder, .dummy => null,
    };
}

fn matchRewriteTemplateToExpr(
    self: anytype,
    template: TemplateExpr,
    actual: ExprId,
    rewrite_bindings: []?BoundValue,
    state: *MatchSession,
) anyerror!bool {
    return switch (template) {
        .binder => |idx| try assignRewriteBinderFromExpr(
            self,
            rewrite_bindings,
            idx,
            actual,
            state,
        ),
        .app => |tmpl_app| blk: {
            const actual_node = self.shared.theorem.interner.node(actual);
            const actual_app = switch (actual_node.*) {
                .app => |value| value,
                .variable => break :blk false,
                .placeholder => break :blk false,
            };
            if (actual_app.term_id != tmpl_app.term_id or
                actual_app.args.len != tmpl_app.args.len)
            {
                break :blk false;
            }

            const saved = try self.shared.allocator.dupe(
                ?BoundValue,
                rewrite_bindings,
            );
            defer self.shared.allocator.free(saved);
            var snapshot = try WitnessState.saveMatchSnapshot(self, state);
            defer WitnessState.deinitMatchSnapshot(self, &snapshot);

            for (tmpl_app.args, actual_app.args) |tmpl_arg, actual_arg| {
                if (!try matchRewriteTemplateToExpr(
                    self,
                    tmpl_arg,
                    actual_arg,
                    rewrite_bindings,
                    state,
                )) {
                    @memcpy(rewrite_bindings, saved);
                    try WitnessState.restoreMatchSnapshot(
                        self,
                        &snapshot,
                        state,
                    );
                    break :blk false;
                }
            }
            break :blk true;
        },
    };
}

fn matchRewriteTemplateToSymbolic(
    self: anytype,
    template: TemplateExpr,
    actual: *const SymbolicExpr,
    rewrite_bindings: []?BoundValue,
    state: *MatchSession,
) anyerror!bool {
    return switch (template) {
        .binder => |idx| try assignRewriteBinderFromSymbolic(
            self,
            rewrite_bindings,
            idx,
            actual,
            state,
        ),
        .app => |tmpl_app| switch ((try resolveBoundBinderSymbolic(
            self,
            actual,
            state,
        )).*) {
            .fixed => |expr_id| try matchRewriteTemplateToExpr(
                self,
                template,
                expr_id,
                rewrite_bindings,
                state,
            ),
            .app => |actual_app| blk: {
                if (actual_app.term_id != tmpl_app.term_id or
                    actual_app.args.len != tmpl_app.args.len)
                {
                    break :blk false;
                }

                const saved = try self.shared.allocator.dupe(
                    ?BoundValue,
                    rewrite_bindings,
                );
                defer self.shared.allocator.free(saved);
                var snapshot = try WitnessState.saveMatchSnapshot(self, state);
                defer WitnessState.deinitMatchSnapshot(self, &snapshot);

                for (tmpl_app.args, actual_app.args) |tmpl_arg, actual_arg| {
                    if (!try matchRewriteTemplateToSymbolic(
                        self,
                        tmpl_arg,
                        actual_arg,
                        rewrite_bindings,
                        state,
                    )) {
                        @memcpy(rewrite_bindings, saved);
                        try WitnessState.restoreMatchSnapshot(
                            self,
                            &snapshot,
                            state,
                        );
                        break :blk false;
                    }
                }
                break :blk true;
            },
            .binder, .dummy => false,
        },
    };
}

fn assignRewriteBinderFromExpr(
    self: anytype,
    rewrite_bindings: []?BoundValue,
    idx: usize,
    actual: ExprId,
    state: *MatchSession,
) anyerror!bool {
    if (idx >= rewrite_bindings.len) return false;
    const value = try WitnessState.rebuildBoundValueFromState(
        self,
        actual,
        state,
        .transparent,
    );
    if (rewrite_bindings[idx]) |existing| {
        return try rewriteBoundValuesEql(self, existing, value);
    }
    rewrite_bindings[idx] = value;
    return true;
}

fn assignRewriteBinderFromSymbolic(
    self: anytype,
    rewrite_bindings: []?BoundValue,
    idx: usize,
    symbolic: *const SymbolicExpr,
    state: *MatchSession,
) anyerror!bool {
    if (idx >= rewrite_bindings.len) return false;
    const value = try rewriteBoundValueFromSymbolic(self, symbolic, state);
    if (rewrite_bindings[idx]) |existing| {
        return try rewriteBoundValuesEql(self, existing, value);
    }
    rewrite_bindings[idx] = value;
    return true;
}

fn rewriteBoundValueFromSymbolic(
    self: anytype,
    symbolic: *const SymbolicExpr,
    state: *MatchSession,
) anyerror!BoundValue {
    const resolved = try resolveBoundBinderSymbolic(self, symbolic, state);
    return switch (resolved.*) {
        .fixed => |expr_id| try WitnessState.rebuildBoundValueFromState(
            self,
            expr_id,
            state,
            .transparent,
        ),
        else => WitnessState.makeSymbolicBoundValue(
            resolved,
            .transparent,
        ),
    };
}

fn rewriteBoundValuesEql(
    self: anytype,
    lhs: BoundValue,
    rhs: BoundValue,
) anyerror!bool {
    const lhs_repr = try WitnessState.boundValueRepresentative(self, lhs);
    const rhs_repr = try WitnessState.boundValueRepresentative(self, rhs);
    return WitnessState.symbolicExprEql(self, lhs_repr, rhs_repr);
}

fn validateRewriteRuleBindings(
    self: anytype,
    rule: RewriteRule,
    rewrite_bindings: []const ?BoundValue,
    state: *MatchSession,
) anyerror!bool {
    if (rule.rule_id >= self.shared.env.rules.items.len) return false;
    const rule_decl = &self.shared.env.rules.items[rule.rule_id];

    var infos: [56]BindingValidation.ExprInfo = undefined;
    std.debug.assert(rewrite_bindings.len <= infos.len);
    for (rewrite_bindings, 0..) |binding_opt, idx| {
        const binding = binding_opt orelse return false;
        infos[idx] = .{
            .sort_name = try rewriteBoundValueSortName(
                self,
                binding,
                state,
            ) orelse return false,
            .bound = try rewriteBoundValueIsBound(
                self,
                binding,
                state,
            ),
            .deps = try rewriteBoundValueDeps(
                self,
                binding,
                state,
            ),
        };
    }
    if (BindingValidation.firstViolation(
        rule_decl.args,
        infos[0..rewrite_bindings.len],
    ) != null) {
        return false;
    }

    // The concrete dep masks cannot see unmaterialized hidden-def dummies, so
    // a substitution rule could otherwise apply "vacuously" to a body that
    // still mentions the bound dummy. Mirror the dependency half of
    // `firstViolation` on dummy-root occurrence masks when they are all
    // computable; when any mask is not, keep the concrete-only verdict.
    dummy_check: {
        var masks: [56]u64 = undefined;
        var seen_binders: std.AutoHashMapUnmanaged(usize, void) = .empty;
        defer seen_binders.deinit(self.shared.allocator);
        for (rewrite_bindings, 0..) |binding_opt, idx| {
            seen_binders.clearRetainingCapacity();
            const repr = try WitnessState.boundValueRepresentative(
                self,
                binding_opt.?,
            );
            masks[idx] = (try dummyRootMaskInSymbolic(
                self,
                repr,
                state,
                &seen_binders,
            )) orelse break :dummy_check;
        }
        if (BindingValidation.firstDepViolationOverMasks(
            u64,
            rule_decl.args,
            masks[0..rewrite_bindings.len],
        ) != null) {
            return false;
        }
    }
    return true;
}

/// Dummy-root occurrence mask for a rewrite binding. Unmaterialized hidden-def
/// dummies carry no concrete dep bit, so dependency exclusions must be checked
/// on these masks instead. Returns null when the mask is not computable (an
/// unbound rule binder inside the value, or a root slot beyond the mask
/// width); callers then fall back to the concrete-only check.
fn dummyRootMaskInSymbolic(
    self: anytype,
    symbolic: *const SymbolicExpr,
    state: *MatchSession,
    seen_binders: *std.AutoHashMapUnmanaged(usize, void),
) anyerror!?u64 {
    switch (symbolic.*) {
        .binder => |idx| {
            if (idx >= state.bindings.len) return null;
            const gop = try seen_binders.getOrPut(self.shared.allocator, idx);
            if (gop.found_existing) return 0;
            const bound = state.bindings[idx] orelse return null;
            const repr = try WitnessState.boundValueRepresentative(self, bound);
            return try dummyRootMaskInSymbolic(self, repr, state, seen_binders);
        },
        .fixed => return 0,
        .dummy => |slot| {
            const root = try WitnessState.resolveDummySlot(slot, state);
            // A resolved root's witness is concrete; its deps are already in
            // the concrete mask.
            if (state.witnesses.get(root) != null or
                state.materialized_witnesses.get(root) != null)
            {
                return 0;
            }
            if (root >= 64) return null;
            return @as(u64, 1) << @intCast(root);
        },
        .app => |app| {
            var mask: u64 = 0;
            for (app.args) |arg| {
                const child = (try dummyRootMaskInSymbolic(
                    self,
                    arg,
                    state,
                    seen_binders,
                )) orelse return null;
                mask |= child;
            }
            return mask;
        },
    }
}

fn rewriteBoundValueDeps(
    self: anytype,
    bound: BoundValue,
    state: *MatchSession,
) anyerror!u55 {
    var deps: u55 = 0;
    var seen_binders: std.AutoHashMapUnmanaged(usize, void) = .empty;
    defer seen_binders.deinit(self.shared.allocator);
    try WitnessState.collectConcreteDepsInBoundValue(
        self,
        bound,
        state,
        &deps,
        &seen_binders,
    );
    return deps;
}

fn rewriteBoundValueSortName(
    self: anytype,
    bound: BoundValue,
    state: *MatchSession,
) anyerror!?[]const u8 {
    // Representatives may be binder back-references; resolve them so the
    // leaf info is readable.
    const symbolic = try resolveBoundBinderSymbolic(
        self,
        try WitnessState.boundValueRepresentative(self, bound),
        state,
    );
    return WitnessState.symbolicSortName(self, symbolic, state);
}

fn rewriteBoundValueIsBound(
    self: anytype,
    bound: BoundValue,
    state: *MatchSession,
) anyerror!bool {
    const symbolic = try resolveBoundBinderSymbolic(
        self,
        try WitnessState.boundValueRepresentative(self, bound),
        state,
    );
    return try symbolicIsBound(self, symbolic);
}

fn symbolicIsBound(
    self: anytype,
    symbolic: *const SymbolicExpr,
) anyerror!bool {
    return switch (symbolic.*) {
        .binder => false,
        .dummy => true,
        .app => false,
        .fixed => |expr_id| blk: {
            const info =
                (try WitnessState.getConcreteLeafInfo(self, expr_id)) orelse
                break :blk false;
            break :blk info.bound;
        },
    };
}

fn instantiateRewriteRuleRhs(
    self: anytype,
    rule: RewriteRule,
    rewrite_bindings: []const ?BoundValue,
) anyerror!?*const SymbolicExpr {
    const subst = try self.shared.allocator.alloc(
        *const SymbolicExpr,
        rewrite_bindings.len,
    );
    for (rewrite_bindings, 0..) |binding_opt, idx| {
        const binding = binding_opt orelse return null;
        subst[idx] = try WitnessState.boundValueRepresentative(self, binding);
    }
    return try TransparentMatch.symbolicFromStableTemplateSubst(self, rule.rhs, subst);
}
