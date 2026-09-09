const std = @import("std");
const ExprId = @import("../expr.zig").ExprId;
const TemplateExpr = @import("../rules.zig").TemplateExpr;
const DefOps = @import("../def_ops.zig");
const BranchStateOps = @import("./branch_state.zig");
const SemanticCompare = @import("./semantic_compare.zig");
const StructuralFragmentMatcher =
    @import("./fragment_matcher.zig");
const StructuralIntervals = @import("./intervals.zig");
const StructuralTransparentMatcher =
    @import("./transparent_matcher.zig");
const SessionSync = @import("./session_sync.zig");
const types = @import("./types.zig");
const BinderSpace = types.BinderSpace;
const BranchState = types.BranchState;

pub fn matchExpr(
    self: anytype,
    template: TemplateExpr,
    actual: ExprId,
    space: BinderSpace,
    state: BranchState,
) anyerror![]BranchState {
    if (try StructuralFragmentMatcher.matchStructural(
        @This(),
        self,
        template,
        actual,
        space,
        state,
    )) |states| {
        return states;
    }

    return switch (template) {
        .binder => |idx| blk: {
            if (BranchStateOps.matchState(&state, space) != null) {
                if (try matchBinderSymbolically(
                    self,
                    idx,
                    actual,
                    space,
                    state,
                )) |new_state| {
                    const out = try self.allocator.alloc(BranchState, 1);
                    out[0] = new_state;
                    break :blk out;
                }
            }

            var new_state = try BranchStateOps.cloneState(self, state);
            const bindings = BranchStateOps.getBindings(&new_state, space);
            if (idx >= bindings.len) break :blk &.{};
            if (bindings[idx]) |existing| {
                if (!try SemanticCompare.bindingCompatible(
                    self,
                    existing,
                    actual,
                )) {
                    break :blk &.{};
                }
            } else {
                if (!try StructuralIntervals.bindingSatisfiesStructural(
                    self,
                    &new_state,
                    space,
                    idx,
                    actual,
                )) {
                    break :blk &.{};
                }
                bindings[idx] = actual;
            }
            const out = try self.allocator.alloc(BranchState, 1);
            out[0] = new_state;
            break :blk out;
        },
        .app => |app| blk: {
            const node = self.theorem.interner.node(actual);
            const actual_app = switch (node.*) {
                .app => |value| value,
                .variable => {
                    break :blk try StructuralTransparentMatcher
                        .matchExprTransparent(
                        self,
                        template,
                        actual,
                        space,
                        state,
                    );
                },
                .placeholder => {
                    break :blk try StructuralTransparentMatcher
                        .matchExprTransparent(
                        self,
                        template,
                        actual,
                        space,
                        state,
                    );
                },
            };
            if (actual_app.term_id != app.term_id or
                actual_app.args.len != app.args.len)
            {
                break :blk try StructuralTransparentMatcher
                    .matchExprTransparent(
                    self,
                    template,
                    actual,
                    space,
                    state,
                );
            }
            var states = std.ArrayListUnmanaged(BranchState){};
            try states.append(
                self.allocator,
                try BranchStateOps.cloneState(self, state),
            );
            for (app.args, actual_app.args) |tmpl_arg, actual_arg| {
                var next = std.ArrayListUnmanaged(BranchState){};
                for (states.items) |current| {
                    const matches = try matchExpr(
                        self,
                        tmpl_arg,
                        actual_arg,
                        space,
                        current,
                    );
                    try next.appendSlice(self.allocator, matches);
                }
                if (next.items.len == 0) {
                    // Same head, clashing arguments. When the head is a
                    // def, unfolding may still reconcile them: a def can
                    // erase an argument, so two applications that differ
                    // only there denote the same thing.
                    if (!isOpenableDef(self, app.term_id)) break :blk &.{};
                    break :blk try StructuralTransparentMatcher
                        .matchExprTransparent(
                        self,
                        template,
                        actual,
                        space,
                        state,
                    );
                }
                states = next;
            }
            break :blk try states.toOwnedSlice(self.allocator);
        },
    };
}

fn isOpenableDef(self: anytype, term_id: u32) bool {
    if (term_id >= self.env.terms.items.len) return false;
    const term = &self.env.terms.items[term_id];
    return term.is_def and term.body != null;
}

fn matchBinderSymbolically(
    self: anytype,
    idx: usize,
    actual: ExprId,
    space: BinderSpace,
    state: BranchState,
) anyerror!?BranchState {
    const seed_state = BranchStateOps.matchState(&state, space) orelse return null;
    const args = self.argInfosForSpace(space);
    if (idx >= args.len) return null;

    const def_ops = self.defOpsContext();

    var session = try def_ops.beginRuleMatchFromSeedState(args, seed_state);
    defer session.deinit();

    if (!try session.matchTransparentOrSemantic(.{ .binder = idx }, actual)) {
        return null;
    }

    var new_state = try BranchStateOps.cloneState(self, state);
    try SessionSync.syncFromSession(
        self.allocator,
        &new_state,
        space,
        &session,
    );
    return new_state;
}
