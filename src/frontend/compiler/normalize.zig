const std = @import("std");
const ExprId = @import("../expr.zig").ExprId;
const TheoremContext = @import("../expr.zig").TheoremContext;
const GlobalEnv = @import("../env.zig").GlobalEnv;
const RewriteRegistry = @import("../rewrite_registry.zig").RewriteRegistry;
const ResolvedRelation = @import("../rewrite_registry.zig").ResolvedRelation;
const Normalizer = @import("../normalizer.zig").Normalizer;
const Canonicalizer = @import("../normalizer.zig").Canonicalizer;
const CommonTargetResult = @import("../normalizer.zig").CommonTargetResult;
const CheckedIr = @import("../checked_ir.zig");
const CheckedLine = CheckedIr.CheckedLine;
const CompilerDiag = @import("../diag.zig");
const DebugConfig = @import("../debug.zig").DebugConfig;
const DebugTrace = @import("../debug.zig");
const ViewTrace = @import("../view_trace.zig");
const DefOps = @import("../def_ops.zig");

pub const NormalizedConversion = struct {
    relation: ResolvedRelation,
    conv_line_idx: ?usize,
    normalizer: Normalizer,
};

pub const ExpectedNormalization = struct {
    relation: ResolvedRelation,
    normalized_expr: ExprId,
    conv_line_idx: ?usize,
    normalizer: Normalizer,
};

pub const ComparisonSnapshot = struct {
    normalized_expected: ?ExprId = null,
    normalized_actual: ?ExprId = null,
};

pub fn maybeBuildComparisonSnapshotWithDebug(
    allocator: std.mem.Allocator,
    theorem: *TheoremContext,
    registry: *RewriteRegistry,
    env: *const GlobalEnv,
    scratch: *CompilerDiag.Scratch,
    expected: ExprId,
    actual: ExprId,
    debug: DebugConfig,
) ComparisonSnapshot {
    // A diagnostic shows normal forms, not their proofs: the proof-free
    // engine reaches the same forms without a proof's pass over a bag for
    // each member, which on a long context costs more than the check it
    // explains.
    var canonicalizer = Canonicalizer.initWithScratch(
        allocator,
        theorem,
        registry,
        env,
        {},
        scratch,
    );
    defer canonicalizer.deinit();
    const mark = scratch.mark();
    defer scratch.discard(mark);
    const normalized_expected =
        canonicalizer.canonicalizeWithFreshBudget(expected) catch return .{};
    const normalized_actual =
        canonicalizer.canonicalizeWithFreshBudget(actual) catch return .{};

    if (normalized_expected == expected and normalized_actual == actual) {
        DebugTrace.traceNormalization(
            debug,
            "comparison snapshot found no normalized change",
            .{},
        );
        return .{};
    }
    tryTraceComparison(
        debug,
        allocator,
        theorem,
        env,
        "comparison snapshot",
        expected,
        actual,
    );
    return .{
        .normalized_expected = normalized_expected,
        .normalized_actual = normalized_actual,
    };
}

pub fn normalizeExprForSnapshot(
    allocator: std.mem.Allocator,
    theorem: *TheoremContext,
    registry: *RewriteRegistry,
    env: *const GlobalEnv,
    checked: *std.ArrayListUnmanaged(CheckedLine),
    scratch: *CompilerDiag.Scratch,
    expr: ExprId,
) !ExprId {
    var normalizer = Normalizer.initWithScratch(
        allocator,
        theorem,
        registry,
        env,
        checked,
        scratch,
    );
    defer normalizer.deinit();
    const mark = scratch.mark();
    const normalized = normalizer.normalize(expr) catch |err| {
        scratch.discard(mark);
        return err;
    };
    scratch.discard(mark);
    return normalized.result_expr;
}

pub fn buildNormalizedConversionWithProviderAndDebug(
    allocator: std.mem.Allocator,
    theorem: *TheoremContext,
    registry: *RewriteRegistry,
    env: *const GlobalEnv,
    checked: *std.ArrayListUnmanaged(CheckedLine),
    scratch: *CompilerDiag.Scratch,
    actual: ExprId,
    expected: ExprId,
    hidden_witness_provider: ?DefOps.HiddenWitnessProvider,
    debug: DebugConfig,
) !?NormalizedConversion {
    tryTraceComparison(
        debug,
        allocator,
        theorem,
        env,
        "trying normalized comparison",
        expected,
        actual,
    );
    var normalizer = Normalizer.initWithDebugAndScratch(
        allocator,
        theorem,
        registry,
        env,
        checked,
        scratch,
        debug,
    );
    normalizer.hidden_witness_provider = hidden_witness_provider;
    // Handed to the caller with the result; freed here otherwise.
    var returned = false;
    defer if (!returned) normalizer.deinit();
    const relation = normalizer.resolveRelationForExpr(actual) orelse {
        DebugTrace.traceNormalization(
            debug,
            "normalized comparison has no relation for the actual expr",
            .{},
        );
        return null;
    };
    // Two sides that differ only in the order of their ACUI members are
    // proved equal by moving the members out of place, which costs far
    // less than sorting both sides.
    const lines_mark = checked.items.len;
    const rearrange_mark = scratch.mark();
    if (normalizer.buildRearrangement(actual, expected)) |rearranged| {
        if (rearranged) |conv_line_idx| {
            DebugTrace.traceNormalization(
                debug,
                "rearranged comparison succeeded",
                .{},
            );
            returned = true;
            return .{
                .relation = relation,
                .conv_line_idx = conv_line_idx,
                .normalizer = normalizer,
            };
        }
    } else |err| {
        if (err == error.OutOfMemory) return err;
    }
    scratch.discard(rearrange_mark);
    CheckedIr.rollbackToMark(allocator, checked, lines_mark);
    // The attempt may have normalized members, caching proofs among the
    // lines just dropped and spending steps the normal forms below need.
    normalizer.cache.clearRetainingCapacity();
    normalizer.step_count = 0;

    const actual_mark = scratch.mark();
    const norm_actual = normalizer.normalize(actual) catch |err| {
        return err;
    };
    scratch.discard(actual_mark);
    const expected_mark = scratch.mark();
    const norm_expected = normalizer.normalize(expected) catch |err| {
        return err;
    };
    scratch.discard(expected_mark);

    const common_target: CommonTargetResult = if (norm_actual.result_expr ==
        norm_expected.result_expr)
        .{
            .target_expr = norm_actual.result_expr,
            .lhs_conv_line_idx = null,
            .rhs_conv_line_idx = null,
        }
    else
        (try normalizer.buildCommonTarget(
            norm_actual.result_expr,
            norm_expected.result_expr,
        ) orelse {
            DebugTrace.traceNormalization(
                debug,
                "normalized comparison could not build a common target",
                .{},
            );
            return null;
        });

    const actual_to_common = try normalizer.composeTransitivity(
        relation,
        actual,
        norm_actual.result_expr,
        common_target.target_expr,
        norm_actual.conv_line_idx,
        common_target.lhs_conv_line_idx,
    );
    const expected_to_common = try normalizer.composeTransitivity(
        relation,
        expected,
        norm_expected.result_expr,
        common_target.target_expr,
        norm_expected.conv_line_idx,
        common_target.rhs_conv_line_idx,
    );

    const conv_line_idx = if (actual_to_common) |actual_idx|
        if (expected_to_common) |expected_idx|
            try normalizer.composeTransitivity(
                relation,
                actual,
                common_target.target_expr,
                expected,
                actual_idx,
                try normalizer.emitSymm(
                    relation,
                    expected,
                    common_target.target_expr,
                    expected_idx,
                ),
            )
        else
            actual_idx
    else if (expected_to_common) |expected_idx|
        try normalizer.emitSymm(
            relation,
            expected,
            common_target.target_expr,
            expected_idx,
        )
    else
        null;

    DebugTrace.traceNormalization(
        debug,
        "normalized comparison succeeded",
        .{},
    );
    returned = true;
    return .{
        .relation = relation,
        .conv_line_idx = conv_line_idx,
        .normalizer = normalizer,
    };
}

pub fn buildExpectedNormalizationWithDebug(
    allocator: std.mem.Allocator,
    theorem: *TheoremContext,
    registry: *RewriteRegistry,
    env: *const GlobalEnv,
    checked: *std.ArrayListUnmanaged(CheckedLine),
    scratch: *CompilerDiag.Scratch,
    expected: ExprId,
    debug: DebugConfig,
) !?ExpectedNormalization {
    var normalizer = Normalizer.initWithDebugAndScratch(
        allocator,
        theorem,
        registry,
        env,
        checked,
        scratch,
        debug,
    );
    // Handed to the caller with the result; freed here otherwise.
    var returned = false;
    defer if (!returned) normalizer.deinit();
    const relation = normalizer.resolveRelationForExpr(expected) orelse {
        return null;
    };
    const mark = scratch.mark();
    const normalized = normalizer.normalize(expected) catch |err| {
        return err;
    };
    scratch.discard(mark);
    if (normalized.result_expr == expected and normalized.conv_line_idx == null) {
        return null;
    }
    returned = true;
    return .{
        .relation = relation,
        .normalized_expr = normalized.result_expr,
        .conv_line_idx = normalized.conv_line_idx,
        .normalizer = normalizer,
    };
}

fn tryTraceComparison(
    debug: DebugConfig,
    allocator: std.mem.Allocator,
    theorem: *TheoremContext,
    env: *const GlobalEnv,
    label: []const u8,
    expected: ExprId,
    actual: ExprId,
) void {
    if (!debug.normalization) return;

    const expected_text = ViewTrace.formatExpr(
        allocator,
        theorem,
        env,
        expected,
    ) catch return;
    defer allocator.free(expected_text);
    const actual_text = ViewTrace.formatExpr(
        allocator,
        theorem,
        env,
        actual,
    ) catch return;
    defer allocator.free(actual_text);

    DebugTrace.traceNormalization(
        debug,
        "{s}: expected={s}",
        .{ label, expected_text },
    );
    DebugTrace.traceNormalization(
        debug,
        "{s}: actual={s}",
        .{ label, actual_text },
    );
}
