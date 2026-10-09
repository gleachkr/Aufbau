//! The goal of a search placeholder nested inside an application: what the
//! enclosing rule expects at that argument, read from the rule's hypothesis
//! template and the line's other bindings.

const std = @import("std");
const types = @import("../types.zig");
const refs_mod = @import("../refs.zig");
const def_match = @import("../backward/def_match.zig");
const ExprId = @import("../../../expr.zig").ExprId;
const TheoremContext = @import("../../../expr.zig").TheoremContext;
const ParseRecovery = @import("../../../parse_recovery.zig");
const ProofScript = @import("../../../proof_script.zig");
const RuleApplication = ProofScript.RuleApplication;
const TemplateExpr = @import("../../../rules.zig").TemplateExpr;
const RewriteRegistry = @import("../../../rewrite_registry.zig").RewriteRegistry;
const CompilerContext = @import("../../context.zig").CompilerContext;
const OpenTerms = @import("../../inference/open_terms.zig");
const Check = @import("../../check.zig");
const Goal = types.Goal;
const Context = types.Context;
const NameExprMap = types.NameExprMap;
const extractHypPartialBindings = def_match.extractHypPartialBindings;
const placeholders_mod = @import("./placeholders.zig");
const applicationAtPath = placeholders_mod.applicationAtPath;

pub const InlineExpectedRef = struct {
    allocator: std.mem.Allocator,
    rule_id: u32,
    child_index: usize,
    bindings: []const ?ExprId,
    expected: ?ExprId,
    query: ExprId,
    has_placeholder: bool,

    pub fn deinit(self: *InlineExpectedRef) void {
        self.allocator.free(self.bindings);
        self.* = undefined;
    }
};

pub fn expectedGoalForInlineTarget(
    compiler: *CompilerContext,
    context: *const Context,
    line: ProofScript.ProofLine,
    line_goal: Goal,
    path: []const usize,
    theorem: *TheoremContext,
    theorem_vars: *NameExprMap,
) !?InlineExpectedRef {
    if (path.len == 0) return null;
    var current_goal = line_goal;
    var prefix_len: usize = 0;
    while (prefix_len < path.len) : (prefix_len += 1) {
        const parent_path = path[0..prefix_len];
        const parent_app = applicationAtPath(line.application, parent_path) orelse
            return null;
        const child_index = path[prefix_len];
        var expected = try expectedRefForApplication(
            compiler,
            context,
            line,
            parent_app,
            current_goal,
            child_index,
            theorem,
            theorem_vars,
        ) orelse return null;
        if (prefix_len + 1 == path.len) return expected;
        const expected_expr = expected.expected orelse {
            expected.deinit();
            return null;
        };
        expected.deinit();
        current_goal = .{ .implicit_whole_conclusion = expected_expr };
    }
    return null;
}

/// True when binder `target_idx` occurs inside `template` as (a descendant of)
/// an operand of an `@acui` structural combiner — e.g. `G` or `H` within a
/// sequent context `G , H`. Such a binder is an ACUI split position, not a
/// value the goal alone determines, so the inline-slot goal must leave it open
/// rather than commit the probe's canonical split.
fn binderUnderAcuiCombiner(
    registry: *const RewriteRegistry,
    template: TemplateExpr,
    target_idx: usize,
    under_combiner: bool,
) bool {
    return switch (template) {
        .binder => |idx| under_combiner and idx == target_idx,
        .app => |app| blk: {
            const now_under = under_combiner or
                registry.hasStructuralCombiner(app.term_id);
            for (app.args) |arg| {
                if (binderUnderAcuiCombiner(registry, arg, target_idx, now_under))
                    break :blk true;
            }
            break :blk false;
        },
    };
}

fn expectedRefForApplication(
    compiler: *CompilerContext,
    context: *const Context,
    line: ProofScript.ProofLine,
    application: RuleApplication,
    goal: Goal,
    child_index: usize,
    theorem: *TheoremContext,
    theorem_vars: *NameExprMap,
) !?InlineExpectedRef {
    const rule_context = context.ruleApplyContext(context.allocator, context.checked);
    const app_line = Check.ApplicationLine{
        .label = line.label,
        .application = application,
        .assertion_span = application.span,
    };
    var probe = Check.probeExpectedRefsForApplication(
        compiler,
        &rule_context,
        application,
        try goal.lineAssertion(theorem, context.env),
        goal.expectedHint(),
        .{
            .theorem_name = context.assertion.name,
            .line_label = line.label,
            .span = application.span,
        },
        app_line,
        theorem,
        theorem_vars,
    ) catch |err| switch (err) {
        error.OutOfMemory => return err,
        else => return null,
    };
    defer probe.deinit();
    if (child_index >= probe.expected_refs.len) return null;

    const rule = &context.env.rules.items[probe.rule_id];
    if (child_index >= rule.hyps.len) return null;
    const bindings = try context.allocator.dupe(?ExprId, probe.bindings);
    errdefer context.allocator.free(bindings);
    if (goal.concreteOrHint()) |line_expr| {
        if (!theorem.matchTemplate(rule.concl, line_expr, bindings)) {
            extractHypPartialBindings(
                context,
                theorem,
                rule.concl,
                line_expr,
                bindings,
            );
        }
    }
    for (application.refs, 0..) |sibling, idx| {
        if (idx == child_index or idx >= rule.hyps.len) continue;
        const expr = refs_mod.sourceRefExpr(
            context,
            theorem,
            sibling,
        ) catch continue;
        if (!theorem.matchTemplate(rule.hyps[idx], expr, bindings)) {
            extractHypPartialBindings(
                context,
                theorem,
                rule.hyps[idx],
                expr,
                bindings,
            );
        }
    }
    for (bindings, 0..) |*binding, idx| {
        if (binding.* == null and idx < probe.contextual_bindings.len) {
            // Skip binders that sit as an operand of an `@acui` combiner in the
            // rule conclusion (e.g. a sequent context `G , H`). The probe's
            // inference commits one canonical ACUI split — the whole context to
            // the last operand, the unit `emp` to the earlier ones — so an
            // earlier-operand context binder would inherit `emp`, and a slot goal
            // resolved through it (`emp ⊢ q`) would match nothing in the pool.
            // Leaving it open lets the slot's own search pick the split that a
            // real reference supplies.
            if (binderUnderAcuiCombiner(
                context.registry,
                rule.concl,
                idx,
                false,
            )) continue;
            binding.* = probe.contextual_bindings[idx];
        }
    }
    const instantiated = try OpenTerms.instantiateTemplatePartial(
        theorem,
        rule.hyps[child_index],
        bindings,
    );
    var has_placeholder = false;
    const query = try instantiateTemplateQuery(
        context.allocator,
        theorem,
        rule.hyps[child_index],
        rule.args,
        bindings,
        &has_placeholder,
    );
    return .{
        .allocator = context.allocator,
        .rule_id = probe.rule_id,
        .child_index = child_index,
        .bindings = bindings,
        .expected = instantiated orelse probe.expected_refs[child_index],
        .query = query,
        .has_placeholder = has_placeholder,
    };
}

fn instantiateTemplateQuery(
    allocator: std.mem.Allocator,
    theorem: *TheoremContext,
    template: TemplateExpr,
    args: []const ParseRecovery.ArgInfo,
    bindings: []const ?ExprId,
    has_placeholder: *bool,
) !ExprId {
    const query_bindings = try allocator.dupe(?ExprId, bindings);
    defer allocator.free(query_bindings);
    return try instantiateTemplateQueryInner(
        theorem,
        template,
        args,
        query_bindings,
        has_placeholder,
    );
}

fn instantiateTemplateQueryInner(
    theorem: *TheoremContext,
    template: TemplateExpr,
    args: []const ParseRecovery.ArgInfo,
    bindings: []?ExprId,
    has_placeholder: *bool,
) !ExprId {
    return switch (template) {
        .binder => |idx| blk: {
            if (idx >= bindings.len or idx >= args.len) {
                return error.TemplateBinderOutOfRange;
            }
            if (bindings[idx]) |expr| break :blk expr;
            // The query is a goal to match, so an unknown is a hole.
            const placeholder = try theorem.addMetaPlaceholderResolved(args[idx].sort_name);
            bindings[idx] = placeholder;
            has_placeholder.* = true;
            break :blk placeholder;
        },
        .app => |app| blk: {
            const app_args = try theorem.allocator.alloc(
                ExprId,
                app.args.len,
            );
            errdefer theorem.allocator.free(app_args);
            for (app.args, 0..) |arg, idx| {
                app_args[idx] = try instantiateTemplateQueryInner(
                    theorem,
                    arg,
                    args,
                    bindings,
                    has_placeholder,
                );
            }
            break :blk try theorem.interner.internAppOwned(
                app.term_id,
                app_args,
            );
        },
    };
}
