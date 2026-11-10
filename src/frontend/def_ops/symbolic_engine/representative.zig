const std = @import("std");
const ExprId = @import("../../expr.zig").ExprId;
const Types = @import("../types.zig");
const MatchState = @import("../match_state.zig");
const Root = @import("witness_state.zig");

const SymbolicExpr = Types.SymbolicExpr;
const BindingMode = Types.BindingMode;
const RepresentativeCache = Types.RepresentativeCache;
const MatchSession = MatchState.MatchSession;

const symbolicToConcreteIfPlain = Root.symbolicToConcreteIfPlain;
const slotForWitness = Root.slotForWitness;
const materializeRepresentativeSymbolic = Root.materializeRepresentativeSymbolic;

pub fn chooseRepresentative(
    self: anytype,
    expr_id: ExprId,
    mode: BindingMode,
) anyerror!ExprId {
    if (mode == .exact) return expr_id;

    var state = try MatchSession.init(self.shared.allocator, 0);
    defer state.deinit(self.shared.allocator);

    const symbolic = try chooseRepresentativeSymbolic(
        self,
        expr_id,
        &state,
        mode,
    );
    return (try materializeRepresentativeSymbolic(
        self,
        symbolic,
        &state,
    )) orelse error.MissingRepresentative;
}

pub fn representativeCacheForMode(
    state: *MatchSession,
    mode: BindingMode,
) *RepresentativeCache {
    return switch (mode) {
        .exact => unreachable,
        .transparent => &state.transparent_representatives,
        .normalized => &state.normalized_representatives,
    };
}

pub fn chooseRepresentativeSymbolic(
    self: anytype,
    expr_id: ExprId,
    state: *MatchSession,
    mode: BindingMode,
) anyerror!*const SymbolicExpr {
    if (mode == .exact) {
        return try self.allocSymbolic(.{ .fixed = expr_id });
    }

    const cache = representativeCacheForMode(state, mode);
    if (cache.get(expr_id)) |cached| return cached;
    // Session-independent fast path: a placeholder-free input with a plain
    // representative computes to the same `.fixed` node in every session
    // (see `SharedContext.pureReprKey`), and `allocSymbolic`
    // re-interns to the identical pointer the original computation returned.
    if (self.shared.pureRepresentativeGet(mode, expr_id)) |plain| {
        return try self.allocSymbolic(.{ .fixed = plain });
    }

    const current = try rebuildCanonicalRepresentative(self, expr_id, state, mode);
    try cache.put(self.shared.allocator, expr_id, current);
    if (current.* == .fixed) {
        if (self.shared.exprIsPlaceholderFree(expr_id)) {
            try self.shared.pureRepresentativePut(
                mode,
                expr_id,
                current.fixed,
            );
        }
    }
    return current;
}

// Rebuild from the arguments' representatives, then canonicalize a plain
// result. A representative never folds a subterm into a def: a def the value
// does not mention is invisible to the line, and folding into one hid
// structure from rewrites and readers (#586, #619, #626).
fn rebuildCanonicalRepresentative(
    self: anytype,
    expr_id: ExprId,
    state: *MatchSession,
    mode: BindingMode,
) anyerror!*const SymbolicExpr {
    var current = try rebuildExprRepresentativeSymbolic(self, expr_id, state, mode);
    if (self.shared.registry != null) {
        if (try symbolicToConcreteIfPlain(self, current, state)) |plain| {
            const canonical = try self.shared.canonicalize(plain);
            current = try self.allocSymbolic(.{ .fixed = canonical });
        }
    }
    return current;
}

pub fn rebuildExprRepresentativeSymbolic(
    self: anytype,
    expr_id: ExprId,
    state: *MatchSession,
    mode: BindingMode,
) anyerror!*const SymbolicExpr {
    const node = self.shared.theorem.interner.node(expr_id);
    return switch (node.*) {
        .variable => try self.allocSymbolic(.{ .fixed = expr_id }),
        .placeholder => |idx| blk: {
            var witness_slots: std.AutoHashMapUnmanaged(ExprId, usize) = .empty;
            defer witness_slots.deinit(self.shared.allocator);
            var witness_it = state.witnesses.iterator();
            while (witness_it.next()) |entry| {
                try witness_slots.put(
                    self.shared.allocator,
                    entry.value_ptr.*,
                    entry.key_ptr.*,
                );
            }
            var materialized_it = state.materialized_witnesses.iterator();
            while (materialized_it.next()) |entry| {
                try witness_slots.put(
                    self.shared.allocator,
                    entry.value_ptr.*,
                    entry.key_ptr.*,
                );
            }
            break :blk try resymbolizePlaceholderExpr(
                self,
                expr_id,
                idx,
                state,
                &witness_slots,
            );
        },
        .app => |app| blk: {
            const args = try self.shared.allocator.alloc(
                *const SymbolicExpr,
                app.args.len,
            );
            var args_owned = true;
            errdefer if (args_owned) self.shared.allocator.free(args);
            const plain_args = try self.shared.allocator.alloc(ExprId, app.args.len);
            var plain_args_owned = true;
            errdefer if (plain_args_owned) self.shared.allocator.free(plain_args);

            var all_plain = true;
            var changed = false;
            for (app.args, 0..) |arg, idx| {
                args[idx] = try chooseRepresentativeSymbolic(
                    self,
                    arg,
                    state,
                    mode,
                );
                if (try symbolicToConcreteIfPlain(self, args[idx], state)) |plain| {
                    plain_args[idx] = plain;
                    changed = changed or plain != arg;
                } else {
                    all_plain = false;
                    changed = true;
                }
            }
            if (all_plain) {
                self.shared.allocator.free(args);
                args_owned = false;
                if (!changed) {
                    self.shared.allocator.free(plain_args);
                    plain_args_owned = false;
                    break :blk try self.allocSymbolic(
                        .{ .fixed = expr_id },
                    );
                }
                const rebuilt = try self.shared.theorem.interner.internAppOwned(
                    app.term_id,
                    plain_args,
                );
                plain_args_owned = false;
                break :blk try self.allocSymbolic(
                    .{ .fixed = rebuilt },
                );
            }
            self.shared.allocator.free(plain_args);
            plain_args_owned = false;
            break :blk try self.allocSymbolic(.{ .app = .{
                .term_id = app.term_id,
                .args = args,
            } });
        },
    };
}

pub fn resymbolizePlaceholderExpr(
    self: anytype,
    expr_id: ExprId,
    idx: usize,
    state: *MatchSession,
    witness_slots: *std.AutoHashMapUnmanaged(ExprId, usize),
) anyerror!*const SymbolicExpr {
    const placeholder = try self.shared.theorem.requirePlaceholderInfo(idx);
    const slot = try slotForWitness(
        self,
        expr_id,
        .{
            .sort_name = placeholder.sort_name,
            .bound = true,
        },
        state,
        witness_slots,
    );
    return try self.allocSymbolic(.{ .dummy = slot });
}
