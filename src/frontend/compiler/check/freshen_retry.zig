const std = @import("std");
const ExprId = @import("../../expr.zig").ExprId;
const TheoremContext = @import("../../expr.zig").TheoremContext;
const GlobalEnv = @import("../../env.zig").GlobalEnv;
const RuleDecl = @import("../../env.zig").RuleDecl;
const RewriteRegistry = @import("../../rewrite_registry.zig").RewriteRegistry;
const CompilerDiag = @import("../../diag.zig");
const AlphaRewrite = @import("../alpha_rewrite.zig");
const CheckedIr = @import("../../checked_ir.zig");
const CheckedLine = CheckedIr.CheckedLine;
const CheckedRef = CheckedIr.CheckedRef;
const Matching = @import("./matching.zig");

// Applies a rule whose bindings went through one or more @freshen repairs.
// `steps` is the repair sequence in the order it was performed: step i's
// bindings differ from step i-1's (or from `original_bindings` for i = 0) in
// exactly one target argument, and each step carries the conversion line that
// proves its target change. Hypothesis references are transported forward
// through the steps in order; the freshened conclusion is transported
// backward through them in reverse, landing on the form the line states.
pub fn applyFreshenedRuleLine(
    allocator: std.mem.Allocator,
    theorem: *TheoremContext,
    registry: *RewriteRegistry,
    env: *const GlobalEnv,
    checked: *std.ArrayListUnmanaged(CheckedLine),
    diag_scratch: *CompilerDiag.Scratch,
    line_expr: ExprId,
    rule: *const RuleDecl,
    rule_id: u32,
    original_bindings: []const ExprId,
    steps: []const AlphaRewrite.FreshenResult,
    refs: []const CheckedRef,
    base_ref_exprs: []const ExprId,
) !usize {
    std.debug.assert(steps.len != 0);
    const final_bindings = steps[steps.len - 1].bindings;
    const fresh_refs = try allocator.dupe(CheckedRef, refs);
    errdefer allocator.free(fresh_refs);

    for (base_ref_exprs, 0..) |actual, idx| {
        const expected_old = try theorem.instantiateTemplate(
            rule.hyps[idx],
            original_bindings,
        );
        var current_ref = (try Matching.tryMatchHypothesis(
            allocator,
            theorem,
            registry,
            env,
            checked,
            diag_scratch,
            .none,
            idx,
            refs[idx],
            actual,
            expected_old,
        )) orelse return error.HypothesisMismatch;
        var current_expected = expected_old;

        for (steps) |step| {
            const next_expected = try theorem.instantiateTemplate(
                rule.hyps[idx],
                step.bindings,
            );
            if (next_expected == current_expected) continue;

            const conv_idx = (try AlphaRewrite.buildRelationProofFromTargetChange(
                allocator,
                theorem,
                registry,
                env,
                checked,
                diag_scratch,
                current_expected,
                next_expected,
                step.old_target_expr,
                step.new_target_expr,
                step.target_conv_line_idx,
            )) orelse return error.FreshenTransportFailed;
            current_ref = try AlphaRewrite.transportRefAlongProof(
                allocator,
                theorem,
                registry,
                env,
                checked,
                diag_scratch,
                next_expected,
                current_expected,
                conv_idx,
                current_ref,
            );
            current_expected = next_expected;
        }
        fresh_refs[idx] = current_ref;
    }

    const expected_new_line = try theorem.instantiateTemplate(
        rule.concl,
        final_bindings,
    );
    const raw_idx = try CheckedIr.appendRuleLine(
        checked,
        allocator,
        expected_new_line,
        rule_id,
        final_bindings,
        fresh_refs,
    );

    var result_ref: CheckedRef = .{ .line = raw_idx };
    var result_expr = expected_new_line;
    var step_idx = steps.len;
    while (step_idx > 0) {
        step_idx -= 1;
        const step = steps[step_idx];
        const before_bindings = if (step_idx == 0)
            original_bindings
        else
            steps[step_idx - 1].bindings;
        const expected_before = try theorem.instantiateTemplate(
            rule.concl,
            before_bindings,
        );
        if (expected_before == result_expr) continue;

        const conv_idx = (try AlphaRewrite.buildRelationProofFromTargetChange(
            allocator,
            theorem,
            registry,
            env,
            checked,
            diag_scratch,
            expected_before,
            result_expr,
            step.old_target_expr,
            step.new_target_expr,
            step.target_conv_line_idx,
        )) orelse return error.FreshenTransportFailed;
        result_ref = try AlphaRewrite.transportRefBackwardAlongProof(
            allocator,
            theorem,
            registry,
            env,
            checked,
            diag_scratch,
            expected_before,
            result_expr,
            conv_idx,
            result_ref,
        );
        result_expr = expected_before;
    }

    if (result_expr != line_expr) {
        result_ref = (try Matching.tryMatchHypothesis(
            allocator,
            theorem,
            registry,
            env,
            checked,
            diag_scratch,
            .none,
            0,
            result_ref,
            result_expr,
            line_expr,
        )) orelse return error.ConclusionMismatch;
    }

    return switch (result_ref) {
        .line => |line_idx| line_idx,
        .hyp => error.ConclusionMismatch,
    };
}
