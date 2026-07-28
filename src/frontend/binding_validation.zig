const std = @import("std");
const ExprId = @import("./expr.zig").ExprId;
const TheoremContext = @import("./expr.zig").TheoremContext;
const GlobalEnv = @import("./env.zig").GlobalEnv;
const ArgInfo = @import("parse_recovery.zig").ArgInfo;

pub const ExprInfo = struct {
    sort_name: []const u8,
    bound: bool,
    deps: u55,
};

pub const DepViolation = struct {
    first_idx: usize,
    second_idx: usize,
};

pub const Violation = union(enum) {
    len_mismatch,
    sort_mismatch: usize,
    boundness_mismatch: usize,
    dep_violation: DepViolation,
};

pub fn exprInfo(
    env: *const GlobalEnv,
    theorem: *const TheoremContext,
    theorem_args: []const ArgInfo,
    expr_id: ExprId,
) !ExprInfo {
    if (try theorem.leafInfoWithArgs(theorem_args, expr_id)) |leaf| {
        return .{
            .sort_name = leaf.sort_name,
            .bound = leaf.bound,
            .deps = leaf.deps,
        };
    }

    const app = switch (theorem.interner.node(expr_id).*) {
        .app => |value| value,
        .variable, .placeholder => unreachable,
    };
    if (app.term_id >= env.terms.items.len) return error.UnknownTerm;

    var deps: u55 = 0;
    for (app.args) |arg_id| {
        deps |= (try exprInfo(env, theorem, theorem_args, arg_id)).deps;
    }
    return .{
        .sort_name = env.terms.items[app.term_id].ret_sort_name,
        .bound = false,
        .deps = deps,
    };
}

pub fn currentExprInfo(
    env: *const GlobalEnv,
    theorem: *const TheoremContext,
    expr_id: ExprId,
) !ExprInfo {
    return try exprInfo(env, theorem, theorem.arg_infos, expr_id);
}

/// Memoized twin of `currentExprInfo` for the hot per-candidate validation
/// path. `exprInfo` re-walks hash-consed shared subtrees once per occurrence
/// (ACUI rule bindings share whole contexts). Only the deps mask needs the
/// recursion; it is memoized per app node in
/// `TheoremContext.expr_deps_cache`, which is only valid for the CURRENT
/// `arg_infos` — hence no caller-supplied-args variant. Leaf info is
/// mint-immutable, so entries never go stale. Errors (unknown term/leaf) are
/// raised before any caching, identically to the plain walk.
pub fn currentExprInfoCached(
    env: *const GlobalEnv,
    theorem: *TheoremContext,
    expr_id: ExprId,
) !ExprInfo {
    if (try theorem.leafInfoWithArgs(theorem.arg_infos, expr_id)) |leaf| {
        return .{
            .sort_name = leaf.sort_name,
            .bound = leaf.bound,
            .deps = leaf.deps,
        };
    }

    const app = switch (theorem.interner.node(expr_id).*) {
        .app => |value| value,
        .variable, .placeholder => unreachable,
    };
    if (app.term_id >= env.terms.items.len) return error.UnknownTerm;

    return .{
        .sort_name = env.terms.items[app.term_id].ret_sort_name,
        .bound = false,
        .deps = try currentExprDepsCached(env, theorem, expr_id),
    };
}

fn currentExprDepsCached(
    env: *const GlobalEnv,
    theorem: *TheoremContext,
    expr_id: ExprId,
) !u55 {
    if (try theorem.leafInfoWithArgs(theorem.arg_infos, expr_id)) |leaf| {
        return leaf.deps;
    }

    const app = switch (theorem.interner.node(expr_id).*) {
        .app => |value| value,
        .variable, .placeholder => unreachable,
    };
    if (app.term_id >= env.terms.items.len) return error.UnknownTerm;

    if (theorem.expr_deps_cache.get(expr_id)) |cached| return cached;

    var deps: u55 = 0;
    for (app.args) |arg_id| {
        deps |= try currentExprDepsCached(env, theorem, arg_id);
    }
    // Memo-or-forget on OOM.
    theorem.expr_deps_cache.put(theorem.allocator, expr_id, deps) catch {};
    return deps;
}

pub fn defExprInfo(
    env: *const GlobalEnv,
    theorem: *const TheoremContext,
    theorem_args: []const ArgInfo,
    expr_id: ExprId,
) !ExprInfo {
    if (try theorem.leafInfoWithArgs(theorem_args, expr_id)) |leaf| {
        return .{
            .sort_name = leaf.sort_name,
            .bound = leaf.bound,
            .deps = leaf.deps,
        };
    }

    const app = switch (theorem.interner.node(expr_id).*) {
        .app => |value| value,
        .variable, .placeholder => unreachable,
    };
    if (app.term_id >= env.terms.items.len) return error.UnknownTerm;

    const term = env.terms.items[app.term_id];
    var deps: u55 = 0;
    var bound_deps: [56]u55 = undefined;
    var bound_len: usize = 0;

    for (term.args, app.args) |arg, arg_id| {
        const arg_info = try defExprInfo(env, theorem, theorem_args, arg_id);
        if (arg.bound) {
            bound_deps[bound_len] = arg_info.deps;
            bound_len += 1;
            continue;
        }

        var arg_deps = arg_info.deps;
        for (0..bound_len) |j| {
            if ((@as(u64, arg.deps) >> @intCast(j)) & 1 == 0) continue;
            arg_deps &= ~bound_deps[j];
        }
        deps |= arg_deps;
    }

    // A dependency declared on the term's result type makes the variable
    // substituted for that bound arg free in the whole application,
    // whether or not it occurs in the regular args (verifier.zig opTerm,
    // defn context, is the reference).
    for (0..bound_len) |j| {
        if ((@as(u64, term.ret_deps) >> @intCast(j)) & 1 == 0) continue;
        deps |= bound_deps[j];
    }

    return .{
        .sort_name = term.ret_sort_name,
        .bound = false,
        .deps = deps,
    };
}

pub fn currentDefExprInfo(
    env: *const GlobalEnv,
    theorem: *const TheoremContext,
    expr_id: ExprId,
) !ExprInfo {
    return try defExprInfo(env, theorem, theorem.arg_infos, expr_id);
}

pub fn firstViolation(
    expected_args: []const ArgInfo,
    infos: []const ExprInfo,
) ?Violation {
    if (expected_args.len != infos.len) return .len_mismatch;
    std.debug.assert(expected_args.len <= 56);

    var bound_deps: [56]u55 = undefined;
    var bound_arg_indices: [56]usize = undefined;
    var bound_len: usize = 0;
    var prev_deps: [56]u55 = undefined;
    var prev_arg_indices: [56]usize = undefined;
    var prev_len: usize = 0;

    for (expected_args, infos, 0..) |expected, info, idx| {
        if (!std.mem.eql(u8, info.sort_name, expected.sort_name)) {
            return .{ .sort_mismatch = idx };
        }
        if (expected.bound and !info.bound) {
            return .{ .boundness_mismatch = idx };
        }
        if (expected.bound) {
            for (prev_deps[0..prev_len], prev_arg_indices[0..prev_len]) |
                prev_dep,
                prev_idx,
            | {
                if (prev_dep & info.deps != 0) {
                    return .{ .dep_violation = .{
                        .first_idx = prev_idx,
                        .second_idx = idx,
                    } };
                }
            }
            bound_deps[bound_len] = info.deps;
            bound_arg_indices[bound_len] = idx;
            bound_len += 1;
        } else {
            for (bound_deps[0..bound_len], bound_arg_indices[0..bound_len], 0..) |
                bound_dep,
                bound_idx,
                k,
            | {
                if ((@as(u64, expected.deps) >> @intCast(k)) & 1 != 0) {
                    continue;
                }
                if (bound_dep & info.deps != 0) {
                    return .{ .dep_violation = .{
                        .first_idx = bound_idx,
                        .second_idx = idx,
                    } };
                }
            }
        }
        prev_deps[prev_len] = info.deps;
        prev_arg_indices[prev_len] = idx;
        prev_len += 1;
    }
    return null;
}

pub fn firstDepViolation(
    expected_args: []const ArgInfo,
    infos: []const ExprInfo,
) ?DepViolation {
    if (expected_args.len != infos.len) return null;
    std.debug.assert(expected_args.len <= 56);

    var bound_deps: [56]u55 = undefined;
    var bound_arg_indices: [56]usize = undefined;
    var bound_len: usize = 0;
    var prev_deps: [56]u55 = undefined;
    var prev_arg_indices: [56]usize = undefined;
    var prev_len: usize = 0;

    for (expected_args, infos, 0..) |expected, info, idx| {
        if (expected.bound) {
            for (prev_deps[0..prev_len], prev_arg_indices[0..prev_len]) |
                prev_dep,
                prev_idx,
            | {
                if (prev_dep & info.deps != 0) {
                    return .{
                        .first_idx = prev_idx,
                        .second_idx = idx,
                    };
                }
            }
            bound_deps[bound_len] = info.deps;
            bound_arg_indices[bound_len] = idx;
            bound_len += 1;
        } else {
            for (bound_deps[0..bound_len], bound_arg_indices[0..bound_len], 0..) |
                bound_dep,
                bound_idx,
                k,
            | {
                if ((@as(u64, expected.deps) >> @intCast(k)) & 1 != 0) {
                    continue;
                }
                if (bound_dep & info.deps != 0) {
                    return .{
                        .first_idx = bound_idx,
                        .second_idx = idx,
                    };
                }
            }
        }
        prev_deps[prev_len] = info.deps;
        prev_arg_indices[prev_len] = idx;
        prev_len += 1;
    }
    return null;
}
