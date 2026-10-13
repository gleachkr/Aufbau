const std = @import("std");

const DefOps = @import("./def_ops.zig");
const ExprId = @import("./expr.zig").ExprId;
const GlobalEnv = @import("./env.zig").GlobalEnv;
const RewriteRegistry = @import("./rewrite_registry.zig").RewriteRegistry;
const TemplateExpr = @import("./rules.zig").TemplateExpr;
const Normalizer = @import("./normalizer.zig").Normalizer;
const Canonicalizer = @import("./normalizer.zig").Canonicalizer;
const CheckedLine = @import("./checked_ir.zig").CheckedLine;
const CompilerDiag = @import("./diag.zig");

/// Finish a normalized comparison by canonicalizing both mirrored
/// expressions and applying the resulting equality to the match session,
/// then checking that a proof can carry one to the other. This produces
/// inference evidence only; final validation is still responsible for
/// emitting any transport proof lines.
pub fn finish(
    allocator: std.mem.Allocator,
    env: *const GlobalEnv,
    registry: *RewriteRegistry,
    scratch: *CompilerDiag.Scratch,
    comparison: *DefOps.NormalizedComparison,
) !bool {
    var canonicalizer = Canonicalizer.init(
        allocator,
        comparison.mirrorTheorem(),
        registry,
        env,
        {},
    );
    // The canonicalization memo is per-call scratch; the results interned into
    // the mirror theorem outlive it.
    defer canonicalizer.deinit();
    const canonical_expected = try canonicalizer.canonicalize(
        comparison.expected_expr,
    );
    const canonical_actual = try canonicalizer.canonicalize(
        comparison.actual_expr,
    );
    if (!try comparison.finish(canonical_expected, canonical_actual)) {
        return false;
    }

    // Normalizing with proofs reaches the same normal forms, so it decides
    // nothing the comparison has not; it fails where no proof can be built
    // (a missing `@congr`), and a match no proof can carry is no match. Its
    // proofs cost a pass over a bag for each member, so it runs only once the
    // comparison has succeeded.
    var checked = std.ArrayListUnmanaged(CheckedLine).empty;
    defer checked.deinit(allocator);
    var normalizer = Normalizer.initWithScratch(
        allocator,
        comparison.mirrorTheorem(),
        registry,
        env,
        &checked,
        scratch,
    );
    defer normalizer.deinit();
    for ([_]ExprId{ comparison.expected_expr, comparison.actual_expr }) |expr| {
        const mark = scratch.mark();
        _ = try normalizer.normalize(expr);
        scratch.discard(mark);
    }
    return true;
}

pub fn matchTemplate(
    allocator: std.mem.Allocator,
    env: *const GlobalEnv,
    registry: *RewriteRegistry,
    scratch: *CompilerDiag.Scratch,
    session: *DefOps.RuleMatchSession,
    template: TemplateExpr,
    actual: ExprId,
) !bool {
    var comparison = try session.beginNormalizedComparison(template, actual);
    defer comparison.deinit();
    return try finish(
        allocator,
        env,
        registry,
        scratch,
        &comparison,
    );
}
