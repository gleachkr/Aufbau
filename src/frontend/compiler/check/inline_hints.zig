//! Inline-application hint flow: expected-ref inference for
//! inline minors, holey hint filling, sibling/semantic refinement, and
//! speculative ACUI-spine demotion.

const std = @import("std");
const ExprId = @import("../../expr.zig").ExprId;
const TheoremContext = @import("../../expr.zig").TheoremContext;
const GlobalEnv = @import("../../env.zig").GlobalEnv;
const RuleDecl = @import("../../env.zig").RuleDecl;
const AssertionStmt = @import("../../parse_recovery.zig").AssertionStmt;
const MM0Parser = @import("../../parse_recovery.zig").MM0Parser;
const ExprModule = @import("../../../trusted/expressions.zig");
const Expr = ExprModule.Expr;
const SourceSpan = ExprModule.SourceSpan;
const ProofScript = @import("../../proof_script.zig");
const ProofLine = ProofScript.ProofLine;
const Ref = ProofScript.Ref;
const RuleApplication = ProofScript.RuleApplication;
const Span = ProofScript.Span;
const TemplateExpr = @import("../../rules.zig").TemplateExpr;
const TheoremBlock = @import("../../proof_script.zig").TheoremBlock;
const RewriteRegistry = @import("../../rewrite_registry.zig").RewriteRegistry;
const CompilerViews = @import("../../views.zig");
const FreshSelect = @import("../fresh_select.zig");
const AlphaRewrite = @import("../alpha_rewrite.zig");
const RuleCatalog = @import("../rule_catalog.zig");
const ViewDecl = CompilerViews.ViewDecl;
const FreshDecl = FreshSelect.FreshDecl;
const FreshenDecl = FreshSelect.FreshenDecl;
const CompilerDiag = @import("../../diag.zig");
const CompilerContext = @import("../context.zig").CompilerContext;
const HoleInferenceSink = @import("../context.zig").HoleInferenceSink;
const InlineConclusionSink = @import("../context.zig").InlineConclusionSink;
const DiagnosticSink = @import("../diagnostic_sink.zig").DiagnosticSink;
const Normalize = @import("../normalize.zig");
const ViewTrace = @import("../../view_trace.zig");
const Diagnostic = CompilerDiag.Diagnostic;
const CheckedIr = @import("../../checked_ir.zig");
const CheckedLine = CheckedIr.CheckedLine;
const CheckedRef = CheckedIr.CheckedRef;
const Inference = @import("../inference.zig");
const Matching = @import("./matching.zig");
const DiagNotes = @import("./diag_notes.zig");
const FreshenRetry = @import("./freshen_retry.zig");
const TheoremBoundary = @import("../theorem_boundary.zig");
const CompilerVars = @import("../vars.zig");
const SortVarRegistry = CompilerVars.SortVarRegistry;
const Holes = @import("../holes.zig");
const Idents = @import("../../idents.zig");
const OpenTerms = @import("../inference/open_terms.zig");
const addFallbackFailureNote = DiagNotes.addFallbackFailureNote;
const concreteMatchFailureSpan = DiagNotes.concreteMatchFailureSpan;
const setHoleyInferenceDiagnostic = DiagNotes.setHoleyInferenceDiagnostic;
const addHoleConcreteMatchNotes = DiagNotes.addHoleConcreteMatchNotes;
const addComparisonSnapshotNotes = DiagNotes.addComparisonSnapshotNotes;
const addFreshenAttemptNotes = DiagNotes.addFreshenAttemptNotes;
const addBoundaryAttemptNotes = DiagNotes.addBoundaryAttemptNotes;
const applyFreshenedRuleLine = FreshenRetry.applyFreshenedRuleLine;
const findRuleArgIndex = Idents.findRuleArgIndex;

const NameExprMap = @import("./types.zig").NameExprMap;
const LineAssertion = @import("./types.zig").LineAssertion;
const ApplicationLine = @import("./types.zig").ApplicationLine;
const RuleApplyContext = @import("./types.zig").RuleApplyContext;
const getDiagnostic = @import("./types.zig").getDiagnostic;
const restoreDiagnostic = @import("./types.zig").restoreDiagnostic;

pub fn inferExpectedRefsForInlineApplications(
    allocator: std.mem.Allocator,
    theorem: *TheoremContext,
    rule: *const RuleDecl,
    line_assertion: LineAssertion,
    expected_conclusion_hint: ?ExprId,
    partial_bindings: []const ?ExprId,
) ![]?ExprId {
    const contextual = try allocator.dupe(?ExprId, partial_bindings);
    defer allocator.free(contextual);
    return inferExpectedRefsForInlineApplicationsWithContext(
        allocator,
        theorem,
        rule,
        line_assertion,
        expected_conclusion_hint,
        contextual,
    );
}

/// All-or-nothing structural fold: match `expr` against `template`, committing
/// the newly bound binders into `bindings` only if the whole match succeeds;
/// on any mismatch `bindings` is rolled back from `snap`. `snap` is caller-owned
/// scratch at least `bindings.len` long. This is the load-bearing "commit only
/// on a full match" step the inline-hint machinery relies on.
pub fn foldTemplateOrRestore(
    theorem: *TheoremContext,
    template: TemplateExpr,
    expr: ExprId,
    bindings: []?ExprId,
    snap: []?ExprId,
) void {
    @memcpy(snap, bindings);
    if (!theorem.matchTemplate(template, expr, bindings)) {
        @memcpy(bindings, snap);
    }
}

fn inferExpectedRefsForInlineApplicationsWithContext(
    allocator: std.mem.Allocator,
    theorem: *TheoremContext,
    rule: *const RuleDecl,
    line_assertion: LineAssertion,
    expected_conclusion_hint: ?ExprId,
    contextual: []?ExprId,
) ![]?ExprId {
    const expected_refs = try allocator.alloc(?ExprId, rule.hyps.len);
    @memset(expected_refs, null);

    const line_expr = expected_conclusion_hint orelse switch (line_assertion) {
        .concrete => |expr| expr,
        .holey, .implicit_whole_conclusion => return expected_refs,
    };

    const snapshot = try allocator.dupe(?ExprId, contextual);
    defer allocator.free(snapshot);
    foldTemplateOrRestore(theorem, rule.concl, line_expr, contextual, snapshot);

    try instantiateExpectedRefs(theorem, rule, contextual, expected_refs);
    return expected_refs;
}

const ExpectedRefsProbe = struct {
    contextual_bindings: []const ?ExprId,
    expected_refs: []?ExprId,
};

/// Controls how a residual *open* binder is rendered when instantiating an
/// inline minor's expected-conclusion hint.
///
/// - `.strict` bails the whole hint to `null` if any binder is unresolved (the
///   historical behavior; used on the search-side probe).
/// - `.holey` substitutes a sort-typed placeholder for each open binder so the
///   surrounding *concrete* structure can still serve as a hint. This recovers
///   the `nd_or_comm` pattern where an ACUI-underdetermined context binder
///   (`H ∈ {emp, p∨q}`) would otherwise null out a hint whose wff part is
///   concrete and sufficient. See `docs/design_notes/nd_or_comm_validation_gap`.
const InlineHintMode = enum { strict, holey };

pub fn inferExpectedRefsForInlineApplicationProbe(
    self: *CompilerContext,
    context: *const RuleApplyContext,
    application: RuleApplication,
    line_assertion: LineAssertion,
    expected_conclusion_hint: ?ExprId,
    line: ApplicationLine,
    rule_id: u32,
    rule: *const RuleDecl,
    theorem: *TheoremContext,
    theorem_vars: *NameExprMap,
    partial_bindings: []const ?ExprId,
    mode: InlineHintMode,
) !ExpectedRefsProbe {
    const allocator = context.allocator;
    const contextual = try semanticExpectationBindings(
        self,
        context,
        rule_id,
        rule,
        line,
        line_assertion,
        expected_conclusion_hint,
        theorem,
        theorem_vars,
        partial_bindings,
        &.{},
    );
    errdefer allocator.free(contextual);

    const expected_refs = try allocator.alloc(?ExprId, rule.hyps.len);
    errdefer allocator.free(expected_refs);
    @memset(expected_refs, null);
    try instantiateExpectedRefs(theorem, rule, contextual, expected_refs);

    const line_expr = expected_conclusion_hint orelse switch (line_assertion) {
        .concrete => |expr| expr,
        .holey, .implicit_whole_conclusion => return .{
            .contextual_bindings = contextual,
            .expected_refs = expected_refs,
        },
    };

    for (rule.hyps, 0..) |_, child_idx| {
        const child_bindings = try semanticBindingsForChildExpectation(
            self,
            context,
            application,
            line,
            rule_id,
            rule,
            line_expr,
            theorem,
            theorem_vars,
            contextual,
            child_idx,
        ) orelse continue;
        defer allocator.free(child_bindings);
        expected_refs[child_idx] = switch (mode) {
            .strict => try OpenTerms.instantiateTemplatePartial(
                theorem,
                rule.hyps[child_idx],
                child_bindings,
            ),
            .holey => try OpenTerms.instantiateTemplateHoley(
                theorem,
                context.env,
                context.registry,
                rule,
                rule.hyps[child_idx],
                child_bindings,
                .{},
            ),
        };
    }

    return .{
        .contextual_bindings = contextual,
        .expected_refs = expected_refs,
    };
}

fn templateMentionsBinder(template: TemplateExpr, idx: usize) bool {
    return switch (template) {
        .binder => |i| i == idx,
        .app => |app| blk: {
            for (app.args) |arg| {
                if (templateMentionsBinder(arg, idx)) break :blk true;
            }
            break :blk false;
        },
    };
}

/// True when the rule has a binder that appears in its conclusion but in none of
/// its hypotheses (e.g. `or_intro_r`'s free left disjunct `a` in `g ⊢ a ∨ b`
/// where the only hyp is `g ⊢ b`). Such a binder cannot be recovered from the
/// minor's own refs, so it is exactly the binder a parent's expected-conclusion
/// hint is needed to pin.
fn applicationBindsArg(app: RuleApplication, name: ?[]const u8) bool {
    const arg_name = name orelse return false;
    for (app.arg_bindings) |binding| {
        if (std.mem.eql(u8, binding.name, arg_name)) return true;
    }
    return false;
}

/// True when the minor `app` (using `rule`) has a binder that (a) appears in the
/// conclusion but in no hypothesis and (b) is not explicitly annotated on the
/// application. Such a binder cannot be recovered from the minor's own refs and
/// has no user-supplied value, so it is exactly what a parent's expected-
/// conclusion hint is needed to pin (e.g. the generated `or_intro_r [l2]` whose
/// free left disjunct `a` is conclusion-only and unannotated).
///
/// Rules with no conclusion-only binder (`not_elim`, `and_intro`, …) are fully
/// determined by their refs, and minors that *do* have one but annotate it
/// (prawitz `or_comm`'s `or_intro_r (a := b) [l2]`) are already pinned. Both must
/// be left untouched: handing them a hint only perturbs an already-deterministic
/// choice (and would surface spurious ACUI-context ambiguity diagnostics).
fn minorHasUnboundConclusionOnlyBinder(
    rule: *const RuleDecl,
    app: RuleApplication,
) bool {
    var idx: usize = 0;
    while (idx < rule.args.len) : (idx += 1) {
        if (!templateMentionsBinder(rule.concl, idx)) continue;
        var in_hyp = false;
        for (rule.hyps) |hyp| {
            if (templateMentionsBinder(hyp, idx)) {
                in_hyp = true;
                break;
            }
        }
        if (in_hyp) continue;
        const arg_name = if (idx < rule.arg_names.len)
            rule.arg_names[idx]
        else
            null;
        if (!applicationBindsArg(app, arg_name)) return true;
    }
    return false;
}

/// True when `ref` is an inline application that a context-holey hint can help.
/// Three shapes qualify, each leaving a binder the strict structural pre-pass
/// cannot pin and that the application does not annotate:
///   1. a conclusion-only binder (`minorHasUnboundConclusionOnlyBinder`, e.g.
///      `or_intro_r`'s free left disjunct, or any 0-hyp `ax`);
///   2. an additive ACUI "rest" binder (`minorHasAcuiRestBinder`, e.g. `lan`'s
///      `g`, `rim`'s `d`) — needed so nested additive inline chains can infer.
///   3. an inline-application *descendant* that qualifies (recursively): a relay
///      minor like `feq_sym [red_test []]` has no underdetermined binder of its
///      own — every binder is shared between hypothesis and conclusion — but its
///      child can only be pinned through a hint the relay must receive and pass
///      down. Without the hint the whole subtree deadlocks at the leaf.
fn inlineMinorWantsHoleyHint(
    env: *const GlobalEnv,
    registry: *const RewriteRegistry,
    ref: Ref,
) bool {
    return switch (ref) {
        .application => |app| blk: {
            const rule_id = env.getRuleId(app.rule_name) orelse break :blk false;
            if (rule_id >= env.rules.items.len) break :blk false;
            const rule = &env.rules.items[rule_id];
            if (minorHasUnboundConclusionOnlyBinder(rule, app)) break :blk true;
            // Additive ACUI rules: a bare "rest" binder sharing an ACUI-combiner
            // region with a structured principal (e.g. `lan`'s `g` in `g , (a∧b)`,
            // `rim`'s `d` in `(a→b) , d`) is left null by the strict structural
            // conclusion match — `matchTemplate` bails at the combiner head — even
            // though that binder also occurs in a hypothesis. The minor then has no
            // expected conclusion to pass to *its* own inline children, so a nested
            // additive chain (`rim [lan [ran [ax [], ax []]]]`) fails to infer.
            // Offer the same holey, ACUI-aware hint that already recovers a 0-hyp
            // `ax` minor, extended to these intermediate additive minors.
            if (minorHasAcuiRestBinder(registry, rule, app)) break :blk true;
            for (app.refs) |child| {
                if (child != .application) continue;
                if (inlineMinorWantsHoleyHint(env, registry, child)) {
                    break :blk true;
                }
            }
            break :blk false;
        },
        else => false,
    };
}

/// True when `rule`'s conclusion has an ACUI-combiner region holding both a
/// structured (principal) summand and a bare, unannotated "rest" binder — the
/// additive shape whose rest the strict structural conclusion match cannot pin.
/// Requiring a structured sibling keeps this off pure multiplicative split rules
/// (`or_elim`'s `G , H , K`, all bare binders), which the search side splits and
/// the existing conclusion-only-binder gate already covers where needed.
fn minorHasAcuiRestBinder(
    registry: *const RewriteRegistry,
    rule: *const RuleDecl,
    app: RuleApplication,
) bool {
    return acuiRestBinderWalk(registry, rule.concl, rule, app);
}

fn acuiRestBinderWalk(
    registry: *const RewriteRegistry,
    template: TemplateExpr,
    rule: *const RuleDecl,
    app: RuleApplication,
) bool {
    switch (template) {
        .binder => return false,
        .app => |a| {
            if (registry.hasStructuralCombiner(a.term_id)) {
                var has_structured = false;
                var unbound_bare = false;
                scanAcuiSpine(
                    a.term_id,
                    template,
                    rule,
                    app,
                    &has_structured,
                    &unbound_bare,
                );
                if (has_structured and unbound_bare) return true;
            }
            for (a.args) |arg| {
                if (acuiRestBinderWalk(registry, arg, rule, app)) return true;
            }
            return false;
        },
    }
}

fn scanAcuiSpine(
    head_id: u32,
    template: TemplateExpr,
    rule: *const RuleDecl,
    app: RuleApplication,
    has_structured: *bool,
    unbound_bare: *bool,
) void {
    switch (template) {
        .binder => |idx| {
            const arg_name = if (idx < rule.arg_names.len)
                rule.arg_names[idx]
            else
                null;
            if (!applicationBindsArg(app, arg_name)) unbound_bare.* = true;
        },
        .app => |a| {
            if (a.term_id == head_id) {
                for (a.args) |arg| {
                    scanAcuiSpine(head_id, arg, rule, app, has_structured, unbound_bare);
                }
            } else {
                has_structured.* = true;
            }
        },
    }
}

/// Backfill expected-conclusion hints for inline-application minors that the
/// strict conclusion-match pre-pass left as `null`.
///
/// The strict `inferExpectedRefsForInlineApplications` matches only the rule
/// conclusion with a single `matchTemplate`. For an ACUI-context rule like
/// `or_elim` (`G,H,K ⊢ r`) that concat-spine cannot strict-match a single-member
/// goal context, so every minor's hint comes back `null` — and a conclusion-only
/// disjunct in a generated minor (`or_intro_r`'s left arm) then has nothing to
/// pin it. This reuses the sibling- and ACUI-aware probe (which folds in the
/// known sibling refs to recover `p,q,r`) and renders the residual open context
/// binder as a whole-context placeholder, yielding a self-validating hint like
/// `‹hole› ⊢ q∨p`.
///
/// The single load-bearing gate is `inlineMinorWantsHoleyHint`: a minor is
/// helped only if its own rule has a conclusion-only binder that the application
/// leaves unannotated — exactly the binder no ref can reach. That keeps the probe
/// off already-determined chained inference (it never fires for `not_elim`,
/// `and_intro`, annotated minors, or non-ACUI proofs like church beta) and off
/// any hint the strict pre-pass already produced. No speculative ACUI context
/// splitting happens here: the open context becomes a wildcard placeholder, not
/// an enumeration of candidate members (that lives only in search-side
/// `backward/split.zig`).
pub fn fillHoleyInlineHints(
    self: *CompilerContext,
    context: *const RuleApplyContext,
    application: RuleApplication,
    line_assertion: LineAssertion,
    expected_conclusion_hint: ?ExprId,
    line: ApplicationLine,
    rule_id: u32,
    rule: *const RuleDecl,
    theorem: *TheoremContext,
    theorem_vars: *NameExprMap,
    partial_bindings: []const ?ExprId,
    expected_refs: []?ExprId,
) !void {
    if (application.refs.len != rule.hyps.len) return;
    if (expected_refs.len != application.refs.len) return;

    var needs_fallback = false;
    for (application.refs, expected_refs) |ref, hint| {
        if (hint == null and
            inlineMinorWantsHoleyHint(context.env, context.registry, ref))
        {
            needs_fallback = true;
            break;
        }
    }
    if (!needs_fallback) return;

    const allocator = context.allocator;
    const probe = try inferExpectedRefsForInlineApplicationProbe(
        self,
        context,
        application,
        line_assertion,
        expected_conclusion_hint,
        line,
        rule_id,
        rule,
        theorem,
        theorem_vars,
        partial_bindings,
        .holey,
    );
    defer allocator.free(probe.contextual_bindings);
    defer allocator.free(probe.expected_refs);

    for (application.refs, expected_refs, probe.expected_refs) |ref, *hint, holey| {
        if (hint.* == null and
            inlineMinorWantsHoleyHint(context.env, context.registry, ref))
        {
            hint.* = holey;
        }
    }
}

fn instantiateExpectedRefs(
    theorem: *TheoremContext,
    rule: *const RuleDecl,
    bindings: []const ?ExprId,
    expected_refs: []?ExprId,
) !void {
    for (rule.hyps, 0..) |hyp, idx| {
        expected_refs[idx] = try OpenTerms.instantiateTemplatePartial(
            theorem,
            hyp,
            bindings,
        );
    }
}

fn semanticBindingsForChildExpectation(
    self: *CompilerContext,
    context: *const RuleApplyContext,
    application: RuleApplication,
    line: ApplicationLine,
    rule_id: u32,
    rule: *const RuleDecl,
    line_expr: ExprId,
    theorem: *TheoremContext,
    theorem_vars: *NameExprMap,
    base_bindings: []const ?ExprId,
    child_idx: usize,
) !?[]const ?ExprId {
    const allocator = context.allocator;
    if (application.refs.len != rule.hyps.len) return null;

    var sibling_hyps = std.ArrayListUnmanaged(TemplateExpr){};
    defer sibling_hyps.deinit(allocator);
    var sibling_exprs = std.ArrayListUnmanaged(ExprId){};
    defer sibling_exprs.deinit(allocator);

    for (application.refs, 0..) |ref, idx| {
        if (idx == child_idx) continue;
        const expr = knownInlineSiblingRefExpr(
            context,
            theorem,
            ref,
        ) orelse continue;
        try sibling_hyps.append(allocator, rule.hyps[idx]);
        try sibling_exprs.append(allocator, expr);
    }
    if (sibling_exprs.items.len == 0) return null;

    var sibling_rule = rule.*;
    sibling_rule.hyps = sibling_hyps.items;
    return try semanticExpectationBindingsForLineExpr(
        self,
        context,
        rule_id,
        &sibling_rule,
        line,
        line_expr,
        theorem,
        theorem_vars,
        base_bindings,
        sibling_exprs.items,
        null,
    );
}

fn knownInlineSiblingRefExpr(
    context: *const RuleApplyContext,
    theorem: *const TheoremContext,
    ref: Ref,
) ?ExprId {
    return switch (ref) {
        .hyp => |hyp| blk: {
            const hyp_idx = switch (ProofScript.resolveHypRef(
                theorem.theorem_hyp_names,
                theorem.theorem_hyps.items.len,
                hyp,
            )) {
                .index => |value| value,
                .unknown, .ambiguous => break :blk null,
            };
            break :blk theorem.theorem_hyps.items[hyp_idx];
        },
        .line => |label| blk: {
            const line_idx = context.labels.get(label.label) orelse {
                break :blk null;
            };
            if (line_idx >= context.checked.items.len) break :blk null;
            break :blk context.checked.items[line_idx].expr;
        },
        .application => null,
    };
}

fn semanticExpectationBindings(
    self: *CompilerContext,
    context: *const RuleApplyContext,
    rule_id: u32,
    rule: *const RuleDecl,
    line: ApplicationLine,
    line_assertion: LineAssertion,
    expected_conclusion_hint: ?ExprId,
    theorem: *TheoremContext,
    theorem_vars: *NameExprMap,
    partial_bindings: []const ?ExprId,
    ref_exprs: []const ExprId,
) ![]const ?ExprId {
    const line_expr = expected_conclusion_hint orelse switch (line_assertion) {
        .concrete => |expr| expr,
        .holey, .implicit_whole_conclusion => {
            return try context.allocator.dupe(?ExprId, partial_bindings);
        },
    };
    var conclusion_rule = rule.*;
    var maybe_view = context.views.get(rule_id);
    if (ref_exprs.len == 0) {
        conclusion_rule.hyps = &.{};
        if (maybe_view) |*view| view.hyps = &.{};
    }
    return semanticExpectationBindingsForLineExpr(
        self,
        context,
        rule_id,
        &conclusion_rule,
        line,
        line_expr,
        theorem,
        theorem_vars,
        partial_bindings,
        ref_exprs,
        maybe_view,
    );
}

fn semanticExpectationBindingsForLineExpr(
    self: *CompilerContext,
    context: *const RuleApplyContext,
    rule_id: u32,
    rule: *const RuleDecl,
    line: ApplicationLine,
    line_expr: ExprId,
    theorem: *TheoremContext,
    theorem_vars: *NameExprMap,
    partial_bindings: []const ?ExprId,
    ref_exprs: []const ExprId,
    maybe_view: ?ViewDecl,
) ![]const ?ExprId {
    const allocator = context.allocator;
    if (rule.hyps.len != ref_exprs.len) {
        return try allocator.dupe(?ExprId, partial_bindings);
    }
    const saved_diag = getDiagnostic(self);
    const had_omitted = Inference.hasOmittedBindings(partial_bindings);
    const has_omitted_structural = had_omitted and
        try Inference.hasOmittedStructuralBindings(
            context.env,
            context.registry,
            rule,
            partial_bindings,
        );
    const prefer_structural_solver = had_omitted and
        try Inference.shouldPreferStructuralSolver(
            context.env,
            context.registry,
            rule,
            partial_bindings,
        );
    const use_advanced_inference = had_omitted and
        (maybe_view != null or has_omitted_structural);
    const fresh_context: Inference.HiddenWitnessFreshContext = .{
        .parser = context.parser,
        .theorem_vars = theorem_vars,
        .sort_vars = context.sort_vars,
    };
    const inference_context: Inference.RuleInferenceContext = .{
        .allocator = allocator,
        .env = context.env,
        .registry = context.registry,
        .scratch = context.diag_scratch,
        .theorem = theorem,
        .assertion = context.assertion,
        .rule_id = rule_id,
        .rule = rule,
        .rule_unify_cache = null,
    };
    const inferred = Inference.inferOptionalBindingsAllowUnresolved(
        self,
        &inference_context,
        line,
        partial_bindings,
        ref_exprs,
        line_expr,
        fresh_context,
        maybe_view,
        use_advanced_inference,
        prefer_structural_solver,
    ) catch |err| switch (err) {
        error.OutOfMemory => return err,
        else => blk: {
            restoreDiagnostic(self, saved_diag);
            break :blk try allocator.dupe(?ExprId, partial_bindings);
        },
    };
    restoreDiagnostic(self, saved_diag);
    demoteSpeculativeAcuiSpineBindings(
        context.registry,
        rule,
        partial_bindings,
        @constCast(inferred),
    );
    return inferred;
}

/// Strip ACUI-spine positional commitments from an *incomplete* probe result.
///
/// When `inferOptionalBindingsAllowUnresolved` falls back to a failed strict
/// replay's snapshot, any binder that sits directly in a structural-combiner
/// region (`g`/`h` in `g , h ⊢ …`) holds just one of possibly many
/// ACUI-equivalent assignments — a 2-member context positionally matched as
/// `g:=m1, h:=m2` even when a sibling hypothesis forces `h` to the whole bag.
/// Downstream probe stages treat these bindings as established (they suppress
/// the structural solver and poison sibling folds), so an unforced spine pick
/// must be left unresolved instead. Complete results are untouched: those come
/// from a solver run that validated every obligation.
fn demoteSpeculativeAcuiSpineBindings(
    registry: *const RewriteRegistry,
    rule: *const RuleDecl,
    partial_bindings: []const ?ExprId,
    inferred: []?ExprId,
) void {
    var complete = true;
    for (inferred) |binding| {
        if (binding == null) {
            complete = false;
            break;
        }
    }
    if (complete) return;
    demoteAcuiSpineBindingsForRule(registry, rule, partial_bindings, inferred);
}

/// Demote every bare ACUI structural-combiner spine binder (that is not
/// explicitly bound in `partial_bindings`) across the rule's hypotheses and
/// conclusion back to unresolved. Demotion only ever clears a binding and is
/// idempotent, so the hyps/concl visit order does not affect the result.
pub fn demoteAcuiSpineBindingsForRule(
    registry: *const RewriteRegistry,
    rule: *const RuleDecl,
    partial_bindings: []const ?ExprId,
    inferred: []?ExprId,
) void {
    for (rule.hyps) |hyp| {
        demoteAcuiSpineBindingsInTemplate(registry, hyp, false, partial_bindings, inferred);
    }
    demoteAcuiSpineBindingsInTemplate(registry, rule.concl, false, partial_bindings, inferred);
}

fn demoteAcuiSpineBindingsInTemplate(
    registry: *const RewriteRegistry,
    template: TemplateExpr,
    in_spine: bool,
    partial_bindings: []const ?ExprId,
    inferred: []?ExprId,
) void {
    switch (template) {
        .binder => |idx| {
            if (!in_spine or idx >= inferred.len) return;
            const explicitly_bound =
                idx < partial_bindings.len and partial_bindings[idx] != null;
            if (!explicitly_bound) inferred[idx] = null;
        },
        .app => |app| {
            const spine = registry.hasStructuralCombiner(app.term_id);
            for (app.args) |arg| {
                demoteAcuiSpineBindingsInTemplate(
                    registry,
                    arg,
                    spine,
                    partial_bindings,
                    inferred,
                );
            }
        },
    }
}
