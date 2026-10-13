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
    const sides = [_]ExprId{ comparison.expected_expr, comparison.actual_expr };
    var canonicalizer = Canonicalizer.initWithScratch(
        allocator,
        comparison.mirrorTheorem(),
        registry,
        env,
        {},
        scratch,
    );
    // The canonicalization memo is per-call scratch; the results interned into
    // the mirror theorem outlive it.
    defer canonicalizer.deinit();
    var canonical: [2]ExprId = undefined;
    // Each side gets the step budget of an engine of its own.
    for (sides, &canonical) |expr, *out| {
        const mark = scratch.mark();
        out.* = try canonicalizer.canonicalizeWithFreshBudget(expr);
        scratch.discard(mark);
    }
    if (!try comparison.finish(canonical[0], canonical[1])) {
        return false;
    }

    // Normalizing with proofs reaches the same normal forms, so it decides
    // nothing the comparison has not; it fails, with the error that stops it,
    // where no proof can be built (a missing `@congr`). Its proofs cost a pass
    // over a bag for each member, so it runs only once the comparison has
    // succeeded.
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
    for (sides) |expr| {
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
