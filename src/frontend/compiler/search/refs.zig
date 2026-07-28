const std = @import("std");
const types = @import("./types.zig");
const ExprId = @import("../../expr.zig").ExprId;
const TheoremContext = @import("../../expr.zig").TheoremContext;
const ProofScript = @import("../../proof_script.zig");
const Context = types.Context;

pub const RefPoolEntry = struct {
    ref: ProofScript.Ref,
    order: usize,
};

pub fn sourceRefExpr(
    context: *const Context,
    theorem: *const TheoremContext,
    ref: ProofScript.Ref,
) !ExprId {
    return switch (ref) {
        .hyp => |hyp| blk: {
            const hyp_idx = switch (ProofScript.resolveHypRef(
                theorem.theorem_hyp_names,
                theorem.theorem_hyps.items.len,
                hyp,
            )) {
                .index => |value| value,
                .unknown, .ambiguous => return error.UnknownHypothesisRef,
            };
            break :blk theorem.theorem_hyps.items[hyp_idx];
        },
        .line => |line| blk: {
            const line_idx = context.labels.get(line.label) orelse {
                return error.UnknownLabel;
            };
            if (line_idx >= context.checked.items.len) {
                return error.UnknownLabel;
            }
            break :blk context.checked.items[line_idx].expr;
        },
        .application => error.UnexpectedInlineRef,
    };
}

pub fn buildReferencePool(
    allocator: std.mem.Allocator,
    context: *const Context,
    theorem: *const TheoremContext,
) ![]RefPoolEntry {
    var pool = std.ArrayListUnmanaged(RefPoolEntry){};
    errdefer pool.deinit(allocator);

    for (theorem.theorem_hyps.items, 0..) |_, idx| {
        try pool.append(allocator, .{
            .ref = .{ .hyp = .{
                .index = idx + 1,
                .span = .{ .start = 0, .end = 0 },
            } },
            .order = idx,
        });
    }

    var line_refs = std.ArrayListUnmanaged(RefPoolEntry){};
    defer line_refs.deinit(allocator);
    var labels = context.labels.iterator();
    while (labels.next()) |entry| {
        const line_idx = entry.value_ptr.*;
        if (line_idx >= context.checked.items.len) continue;
        try line_refs.append(allocator, .{
            .ref = .{ .line = .{
                .label = entry.key_ptr.*,
                .span = .{ .start = 0, .end = 0 },
            } },
            .order = line_idx,
        });
    }
    std.mem.sort(RefPoolEntry, line_refs.items, {}, refPoolEntryLessThan);
    try pool.appendSlice(allocator, line_refs.items);
    return try pool.toOwnedSlice(allocator);
}

fn refPoolEntryLessThan(_: void, lhs: RefPoolEntry, rhs: RefPoolEntry) bool {
    if (lhs.order != rhs.order) return lhs.order < rhs.order;
    return refNameLessThan(lhs.ref, rhs.ref);
}

fn refNameLessThan(lhs: ProofScript.Ref, rhs: ProofScript.Ref) bool {
    return switch (lhs) {
        .hyp => |lhs_hyp| switch (rhs) {
            .hyp => |rhs_hyp| lhs_hyp.index < rhs_hyp.index,
            .line, .application => true,
        },
        .line => |lhs_line| switch (rhs) {
            .hyp => false,
            .line => |rhs_line| std.mem.lessThan(
                u8,
                lhs_line.label,
                rhs_line.label,
            ),
            .application => true,
        },
        .application => false,
    };
}

pub fn refsFromIndices(
    allocator: std.mem.Allocator,
    pool: []const RefPoolEntry,
    indices: []const usize,
) ![]const ProofScript.Ref {
    const refs = try allocator.alloc(ProofScript.Ref, indices.len);
    for (indices, 0..) |pool_idx, idx| {
        refs[idx] = pool[pool_idx].ref;
    }
    return refs;
}

pub fn advanceReferenceIndices(indices: []usize, base: usize) bool {
    if (indices.len == 0) return false;
    var idx = indices.len;
    while (idx > 0) {
        idx -= 1;
        indices[idx] += 1;
        if (indices[idx] < base) return true;
        indices[idx] = 0;
    }
    return false;
}

pub fn rankReferenceIndices(base: usize, indices: []const usize) usize {
    if (base == 0) return 0;
    var rank: usize = 0;
    for (indices) |idx| {
        rank = std.math.mul(usize, rank, base) catch
            std.math.maxInt(usize);
        rank = std.math.add(usize, rank, idx) catch
            std.math.maxInt(usize);
    }
    return rank;
}
