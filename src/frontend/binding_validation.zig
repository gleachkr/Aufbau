const std = @import("std");
const ExprId = @import("./expr.zig").ExprId;
const TheoremContext = @import("./expr.zig").TheoremContext;
const GlobalEnv = @import("./env.zig").GlobalEnv;
const ArgInfo = @import("parse_recovery.zig").ArgInfo;
const max_bound_vars = @import("parse_recovery.zig").max_bound_vars;

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

/// Scratch for one `ExprInfo` per rule arg: on the stack for ordinary
/// arities, on the heap past that (a rule may have any number of args).
pub fn infoScratch(
    fallback: std.mem.Allocator,
) std.heap.StackFallbackAllocator(16 * @sizeOf(ExprInfo)) {
    return std.heap.stackFallback(16 * @sizeOf(ExprInfo), fallback);
}

/// First violation of `bindings` against `expected_args`, each binding read
/// in the theorem's own context.
pub fn firstCurrentViolation(
    env: *const GlobalEnv,
    theorem: *TheoremContext,
    expected_args: []const ArgInfo,
    bindings: []const ExprId,
) !?Violation {
    var scratch = infoScratch(theorem.allocator);
    const allocator = scratch.get();
    const infos = try allocator.alloc(ExprInfo, bindings.len);
    defer allocator.free(infos);
    for (bindings, infos) |binding, *info| {
        info.* = try exprInfo(env, theorem, binding);
    }
    return firstViolation(expected_args, infos);
}

/// Sort, boundness and dependency mask of `expr_id` in the theorem's own
/// context. The mask is the OR of the leaves' masks; it is memoized per app
/// node in `TheoremContext.expr_deps_cache`, so a hash-consed DAG is walked
/// once, not once per path (a chain of lines that each double the previous
/// expression has linear DAG size and exponential tree size). Errors
/// (unknown term/leaf) are raised before any caching.
pub fn exprInfo(
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
        .deps = try exprDeps(env, theorem, expr_id),
    };
}

fn exprDeps(
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
        deps |= try exprDeps(env, theorem, arg_id);
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
    // Indexed by bound arg; the parser caps those per declaration.
    var bound_deps: [max_bound_vars]u55 = undefined;
    // The j-th bound arg's own binder-space dep bit, for matching against
    // `arg.deps` masks (which are binder-indexed and shift past any dummy
    // the term declares ahead of a bound arg — bit j would be wrong).
    var bound_bits: [max_bound_vars]u55 = undefined;
    var bound_len: usize = 0;

    for (term.args, app.args) |arg, arg_id| {
        const arg_info = try defExprInfo(env, theorem, theorem_args, arg_id);
        if (arg.bound) {
            bound_deps[bound_len] = arg_info.deps;
            bound_bits[bound_len] = arg.deps;
            bound_len += 1;
            continue;
        }

        var arg_deps = arg_info.deps;
        for (0..bound_len) |j| {
            if (arg.deps & bound_bits[j] == 0) continue;
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

/// The bound/regular dependency-exclusion algorithm alone, generic over the
/// dependency-mask type. `firstDepViolation` runs it over concrete u55 dep
/// masks; the def-ops rewrite validation runs it over dummy-root occurrence
/// masks (u64), where an unmaterialized hidden-def dummy has no concrete dep
/// bit.
pub fn firstDepViolationOverMasks(
    comptime Mask: type,
    expected_args: []const ArgInfo,
    deps: []const Mask,
) ?DepViolation {
    const identity = struct {
        fn get(mask: Mask) Mask {
            return mask;
        }
    }.get;
    return firstDepViolationBy(Mask, Mask, identity, expected_args, deps);
}

/// MMB's dependency rule over one value per expected arg: a bound arg's value
/// shares no variable with any earlier arg's value, and a regular arg's value
/// shares none with an earlier bound arg's value unless the regular arg
/// declares a dependency on that bound arg. Reports the first violation in
/// argument order, paired with the earliest arg it clashes with.
///
/// Two running unions settle the clean case in one pass; only a possible
/// clash rescans the earlier args. Nothing is stored per arg, so any arity
/// works (only bound args are capped, at 55; a rule may have more args).
fn firstDepViolationBy(
    comptime Mask: type,
    comptime T: type,
    comptime maskOf: fn (T) Mask,
    expected_args: []const ArgInfo,
    items: []const T,
) ?DepViolation {
    std.debug.assert(expected_args.len == items.len);

    var prev_union: Mask = 0;
    var bound_union: Mask = 0;
    for (expected_args, items, 0..) |expected, item, idx| {
        const mask = maskOf(item);
        if (expected.bound) {
            if (prev_union & mask != 0) {
                for (items[0..idx], 0..) |prev, prev_idx| {
                    if (maskOf(prev) & mask != 0) {
                        return .{ .first_idx = prev_idx, .second_idx = idx };
                    }
                }
                unreachable;
            }
            bound_union |= mask;
        } else if (bound_union & mask != 0) {
            for (expected_args[0..idx], items[0..idx], 0..) |
                prev_expected,
                prev,
                prev_idx,
            | {
                if (!prev_expected.bound) continue;
                if (expected.deps & prev_expected.deps != 0) continue;
                if (maskOf(prev) & mask != 0) {
                    return .{ .first_idx = prev_idx, .second_idx = idx };
                }
            }
        }
        prev_union |= mask;
    }
    return null;
}

fn infoDeps(info: ExprInfo) u55 {
    return info.deps;
}

pub fn firstViolation(
    expected_args: []const ArgInfo,
    infos: []const ExprInfo,
) ?Violation {
    if (expected_args.len != infos.len) return .len_mismatch;

    // The first sort or boundness mismatch, if any. A dependency violation
    // wins only when it comes earlier in argument order.
    var shape_violation: ?Violation = null;
    var shape_ok_len = infos.len;
    for (expected_args, infos, 0..) |expected, info, idx| {
        if (!std.mem.eql(u8, info.sort_name, expected.sort_name)) {
            shape_violation = .{ .sort_mismatch = idx };
        } else if (expected.bound and !info.bound) {
            shape_violation = .{ .boundness_mismatch = idx };
        } else continue;
        shape_ok_len = idx;
        break;
    }
    if (firstDepViolation(
        expected_args[0..shape_ok_len],
        infos[0..shape_ok_len],
    )) |violation| {
        return .{ .dep_violation = violation };
    }
    return shape_violation;
}

pub fn firstDepViolation(
    expected_args: []const ArgInfo,
    infos: []const ExprInfo,
) ?DepViolation {
    if (expected_args.len != infos.len) return null;
    return firstDepViolationBy(u55, ExprInfo, infoDeps, expected_args, infos);
}

test "firstViolation keeps argument order past 56 args" {
    // 60 regular args, a bound arg, then a regular arg declared to depend on
    // it. Only bound args are capped, so the scans reach past index 56.
    const obj: ArgInfo = .{ .sort_name = "obj", .bound = false, .deps = 0 };
    var expected = [_]ArgInfo{obj} ** 62;
    expected[60] = .{ .sort_name = "obj", .bound = true, .deps = 1 };
    expected[61] = .{ .sort_name = "obj", .bound = false, .deps = 1 };
    const x: ExprInfo = .{ .sort_name = "obj", .bound = true, .deps = 1 << 3 };
    var infos = [_]ExprInfo{.{ .sort_name = "obj", .bound = false, .deps = 0 }} ** 62;
    infos[60] = x;
    infos[61] = .{ .sort_name = "obj", .bound = false, .deps = x.deps };
    try std.testing.expectEqual(@as(?Violation, null), firstViolation(&expected, &infos));

    // The bound arg's variable also occurs in an earlier arg.
    infos[57].deps = x.deps;
    const clash: Violation = .{ .dep_violation = .{ .first_idx = 57, .second_idx = 60 } };
    try std.testing.expectEqual(clash, firstViolation(&expected, &infos).?);
    // A later sort mismatch does not hide it; an earlier one comes first.
    infos[61].sort_name = "wff";
    try std.testing.expectEqual(clash, firstViolation(&expected, &infos).?);
    infos[10].sort_name = "wff";
    try std.testing.expectEqual(
        Violation{ .sort_mismatch = 10 },
        firstViolation(&expected, &infos).?,
    );

    // A regular arg that does not declare the dependency.
    infos[10].sort_name = "obj";
    infos[57].deps = 0;
    infos[61].sort_name = "obj";
    expected[61].deps = 0;
    try std.testing.expectEqual(
        Violation{ .dep_violation = .{ .first_idx = 60, .second_idx = 61 } },
        firstViolation(&expected, &infos).?,
    );
}
