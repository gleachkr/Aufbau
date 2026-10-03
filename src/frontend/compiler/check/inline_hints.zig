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
const templateMentionsBinder = @import("../../rules.zig").templateMentionsBinder;
const TheoremBlock = @import("../../proof_script.zig").TheoremBlock;
const RewriteRegistry = @import("../../rewrite_registry.zig").RewriteRegistry;
const AcuiBag = @import("../../acui_bag.zig");
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
const LineGoal = @import("./types.zig").LineGoal;
const ApplicationLine = @import("./types.zig").ApplicationLine;
const RuleApplyContext = @import("./types.zig").RuleApplyContext;
const getDiagnostic = @import("./types.zig").getDiagnostic;
const restoreDiagnostic = @import("./types.zig").restoreDiagnostic;

pub fn inferExpectedRefsForInlineApplications(
    allocator: std.mem.Allocator,
    theorem: *TheoremContext,
    registry: *const RewriteRegistry,
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
        registry,
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
    registry: *const RewriteRegistry,
    rule: *const RuleDecl,
    line_assertion: LineAssertion,
    expected_conclusion_hint: ?ExprId,
    contextual: []?ExprId,
) ![]?ExprId {
    const expected_refs = try allocator.alloc(?ExprId, rule.hyps.len);
    errdefer allocator.free(expected_refs);
    @memset(expected_refs, null);

    const snapshot = try allocator.dupe(?ExprId, contextual);
    defer allocator.free(snapshot);
    const goal = LineGoal.of(expected_conclusion_hint, line_assertion) orelse
        return expected_refs;
    const line_expr = switch (goal) {
        .expr => |expr| expr,
        // A holey line still fixes the binders its visible structure
        // determines (`λ x : a. x` fixes `A` and `t` in `t_lam`'s
        // conclusion); fold them all-or-nothing, so a child's hint is as
        // concrete as the parent's visible part allows. A binder facing a
        // subterm with a hole in it fixes nothing, and an ACUI spine
        // binder's position is only a guess, as in
        // `seedBindingsFromHoleyHint`.
        .holey => |holey| {
            const scratch = try allocator.alloc(?ExprId, contextual.len);
            defer allocator.free(scratch);
            if (try Holes.foldTemplateToSurface(theorem, rule.concl, holey, contextual, scratch)) {
                demoteAcuiSpineBindingsInTemplate(registry, rule.concl, false, snapshot, contextual);
            }
            try instantiateExpectedRefs(theorem, rule, contextual, expected_refs);
            return expected_refs;
        },
    };

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

    const line_expr = LineGoal.interned(expected_conclusion_hint, line_assertion) orelse
        return .{
            .contextual_bindings = contextual,
            .expected_refs = expected_refs,
        };

    // Under a holey line, open binders become line holes, as in
    // `fillViewInlineHints`, so the minor's hint is itself a holey goal hint.
    const missing: OpenTerms.MissingBinderContext = if (mode == .holey and
        isHoleyGoalHint(theorem, line_expr))
        .{ .placeholder_factory = .{ .makeFn = mintHintHole } }
    else
        .{};
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
                missing,
            ),
        };
    }

    return .{
        .contextual_bindings = contextual,
        .expected_refs = expected_refs,
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
///   2. an additive ACUI "rest" binder (`hasAcuiRestBinder`, e.g. `lan`'s
///      `g`, `rim`'s `d`) — needed so nested additive inline chains can infer —
///      in the conclusion or in a premise (`imp_intro`'s `g , a`, whose split
///      of the cited context only the conclusion's context decides);
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
            if (hasAcuiRestBinder(registry, rule, app)) break :blk true;
            // The same shape in a premise (`imp_intro`'s `g , a ⊢ b`) splits
            // the cited context ambiguously; only the conclusion's context,
            // which the hint carries, decides which member is `a`.
            for (rule.hyps) |hyp| {
                if (acuiRestBinderWalk(registry, hyp, rule, app)) break :blk true;
            }
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
fn hasAcuiRestBinder(
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
/// Two gates decide which null hints the probe may fill:
///   - `inlineMinorWantsHoleyHint`: the minor's own rule has a binder no ref can
///     reach (conclusion-only, an additive rest, or a qualifying descendant);
///   - `hasAcuiRestBinder` on the *parent* rule: an additive parent
///     (`not_left`'s `g , ¬ a ⊢ ⊥`) strict-matches its conclusion only when the
///     goal context is literally a join, so against a one-member context
///     (`¬ D ⊢ ⊥`) every inline child's hint comes back null.
/// That keeps the probe off already-determined chained inference (it never
/// fires for `not_elim` or `and_intro` parents with determined minors, annotated
/// minors, or non-ACUI proofs like church beta) and off any hint the strict
/// pre-pass already produced. No speculative ACUI context
/// splitting happens here: the open context becomes a wildcard placeholder, not
/// an enumeration of candidate members (that lives only in search-side
/// `backward/split.zig`).
///
/// After the probe and the `@view` pass, a hint still missing on a concrete
/// goal comes from the goal alone, each binder it leaves open a line hole:
/// `mp [sep_intro_imp [#1], ex_intro [l1]]` over `y ∈ image f X B` gives
/// `sep_intro_imp` the hint `‹hole› → y ∈ image f X B`, though neither child
/// can be checked before the other fixes `mp`'s `a`.
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
    const allocator = context.allocator;
    // Which minors still missing a hint may take a holey one: `minor_wants`
    // by their own rule, `wants` also for every inline minor of an additive
    // parent. Every pass below fills only missing hints.
    const minor_wants = try allocator.alloc(bool, application.refs.len);
    defer allocator.free(minor_wants);
    const wants = try allocator.alloc(bool, application.refs.len);
    defer allocator.free(wants);
    @memset(minor_wants, false);
    @memset(wants, false);
    if (!anyMissingApplication(application.refs, expected_refs)) return;
    const parent_acui_rest = hasAcuiRestBinder(context.registry, rule, application);
    for (application.refs, expected_refs, minor_wants, wants) |ref, hint, *minor, *want| {
        if (hint != null or ref != .application) continue;
        minor.* = inlineMinorWantsHoleyHint(context.env, context.registry, ref);
        want.* = minor.* or parent_acui_rest;
    }
    try fillRuleHoleyInlineHints(
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
        expected_refs,
        wants,
    );
    try fillViewInlineHints(
        context,
        line_assertion,
        expected_conclusion_hint,
        rule_id,
        rule,
        theorem,
        partial_bindings,
        expected_refs,
        minor_wants,
    );
    // Last: the view pass fills only null hints, and a view rule's literal
    // premise (`g ⊢ [x/‹hole›] p`) would hide the view premise it reads.
    try fillHintsFromGoal(
        context,
        line_assertion,
        expected_conclusion_hint,
        rule,
        theorem,
        partial_bindings,
        expected_refs,
        wants,
        .concrete,
    );
}

fn fillRuleHoleyInlineHints(
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
    wants: []const bool,
) !void {
    if (!anyMissing(expected_refs, wants)) return;

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

    var still_missing = false;
    for (expected_refs, probe.expected_refs, wants) |*hint, holey, want| {
        if (hint.* == null and want) {
            hint.* = holey;
            if (holey == null) still_missing = true;
        }
    }
    if (!still_missing) return;

    // The goal itself is holey (a holey line, or a hint with holes from the
    // parent), so neither pass above could match the conclusion. Match
    // it with holes as wildcards instead: a binder facing a holey subterm
    // takes that subterm, placeholders and all, so the minor still sees the
    // visible part (`Q` in `Q ∨ P ‹hole›`).
    try fillHintsFromGoal(
        context,
        line_assertion,
        expected_conclusion_hint,
        rule,
        theorem,
        partial_bindings,
        expected_refs,
        wants,
        .holey,
    );
}

const GoalKind = enum { holey, concrete };

/// Fill each still-missing hint a minor wants from `rule`'s bindings against
/// the goal, an open binder becoming a line hole. `.holey` reads a holey goal
/// with its holes as wildcards; `.concrete` reads a concrete goal, so a minor
/// whose own refs cannot pin it still sees the parts the goal fixes
/// (`‹hole› → y ∈ image f X B` for `mp`'s first premise).
fn fillHintsFromGoal(
    context: *const RuleApplyContext,
    line_assertion: LineAssertion,
    expected_conclusion_hint: ?ExprId,
    rule: *const RuleDecl,
    theorem: *TheoremContext,
    partial_bindings: []const ?ExprId,
    expected_refs: []?ExprId,
    wants: []const bool,
    kind: GoalKind,
) !void {
    if (!anyMissing(expected_refs, wants)) return;
    const bindings = try goalBindings(
        context,
        rule,
        theorem,
        line_assertion,
        expected_conclusion_hint,
        partial_bindings,
        kind,
    ) orelse return;
    defer context.allocator.free(bindings);
    for (expected_refs, rule.hyps, wants) |*hint, hyp, want| {
        if (hint.* != null or !want) continue;
        const holey = try OpenTerms.instantiateTemplateHoley(
            theorem,
            context.env,
            context.registry,
            rule,
            hyp,
            bindings,
            .{ .placeholder_factory = .{ .makeFn = mintHintHole } },
        ) orelse continue;
        if (!theorem.isPlaceholder(holey)) hint.* = holey;
    }
}

/// True when `hint` came from a holey goal: it holds a line hole (a line's
/// hole, or a binder the goal left open). Other holey hints hold plain meta
/// holes, and search's hints carry its own metas.
pub fn isHoleyGoalHint(theorem: *const TheoremContext, hint: ExprId) bool {
    return theorem.containsLineHole(hint);
}

/// An open binder in a holey goal's hint is a line hole, like the line's own
/// holes: a wildcard that spends no dependency slot.
fn mintHintHole(
    _: ?*anyopaque,
    theorem: *TheoremContext,
    sort_name: []const u8,
    _: OpenTerms.MetaKind,
) anyerror!ExprId {
    return theorem.addLineHolePlaceholder(sort_name);
}

/// `rule`'s bindings from a goal of `kind`, or null when the goal is of the
/// other kind or its visible structure does not match the conclusion. Caller
/// owns the result.
fn goalBindings(
    context: *const RuleApplyContext,
    rule: *const RuleDecl,
    theorem: *TheoremContext,
    line_assertion: LineAssertion,
    expected_conclusion_hint: ?ExprId,
    partial_bindings: []const ?ExprId,
    kind: GoalKind,
) !?[]?ExprId {
    const goal = switch (LineGoal.of(expected_conclusion_hint, line_assertion) orelse
        return null) {
        .expr => |expr| if (isHoleyGoalHint(theorem, expr) == (kind == .holey))
            expr
        else
            return null,
        .holey => |holey| if (kind == .holey)
            (try Holes.internWithLineHoles(theorem, context.env, holey)) orelse return null
        else
            return null,
    };
    const bindings = try context.allocator.dupe(?ExprId, partial_bindings);
    errdefer context.allocator.free(bindings);
    if (!try matchTemplateHoley(theorem, context.registry, rule.concl, goal, bindings, .bind)) {
        context.allocator.free(bindings);
        return null;
    }
    demoteAcuiSpineBindingsInTemplate(context.registry, rule.concl, false, partial_bindings, bindings);
    return bindings;
}

/// True when some inline application among `refs` has no hint yet.
fn anyMissingApplication(refs: []const Ref, expected_refs: []const ?ExprId) bool {
    for (refs, expected_refs) |ref, hint| {
        if (hint == null and ref == .application) return true;
    }
    return false;
}

/// True when some hint a minor wants is still missing.
fn anyMissing(expected_refs: []const ?ExprId, wants: []const bool) bool {
    for (expected_refs, wants) |hint, want| {
        if (hint == null and want) return true;
    }
    return false;
}

/// Derive the still-missing hints of a `@view` rule's inline minors from the
/// view's own premises.
///
/// A view rule's premise is often stated through a binder only `@recover`
/// fills: `ex_intro`'s `g ⊢ [x/t] p` cannot be instantiated while the witness
/// `t` is open, so every hint above comes back null and the minor elaborates
/// unguided. The view premise (`g ⊢ q`) is what the minor must conclude, and
/// its binders are pinned by matching the view conclusion against the line,
/// so a holey instance (`¬D ⊢ ‹hole›`) still fixes the context. Without it,
/// `ex_intro [imp_intro [#1]]` over `¬D , P C ⊢ ∀ y P y` splits `imp_intro`'s
/// `g , a` the wrong way round and the witness cannot be recovered.
///
/// ACUI spine binders of the view conclusion are positional guesses under the
/// structural match, so they are left open (the holey instance collapses their
/// region to one placeholder) unless the application binds them explicitly.
fn fillViewInlineHints(
    context: *const RuleApplyContext,
    line_assertion: LineAssertion,
    expected_conclusion_hint: ?ExprId,
    rule_id: u32,
    rule: *const RuleDecl,
    theorem: *TheoremContext,
    partial_bindings: []const ?ExprId,
    expected_refs: []?ExprId,
    minor_wants: []const bool,
) !void {
    const view = context.views.get(rule_id) orelse return;
    if (view.hyps.len != expected_refs.len) return;
    if (!anyMissing(expected_refs, minor_wants)) return;
    const line_expr = LineGoal.interned(expected_conclusion_hint, line_assertion) orelse
        return;
    // Under a holey line, open binders become line holes too, so the minor's
    // hint is itself a holey goal hint.
    const holey_parent = isHoleyGoalHint(theorem, line_expr);

    const allocator = context.allocator;
    const explicit = try allocator.alloc(?ExprId, view.num_binders);
    defer allocator.free(explicit);
    @memset(explicit, null);
    for (view.binder_map, 0..) |maybe_rule_idx, vi| {
        const rule_idx = maybe_rule_idx orelse continue;
        if (rule_idx < partial_bindings.len) explicit[vi] = partial_bindings[rule_idx];
    }
    const bindings = try allocator.dupe(?ExprId, explicit);
    defer allocator.free(bindings);
    if (!theorem.matchTemplate(view.concl, line_expr, bindings)) return;
    demoteAcuiSpineBindingsInTemplate(context.registry, view.concl, false, explicit, bindings);

    var view_rule = rule.*;
    view_rule.args = view.arg_infos;
    view_rule.arg_names = view.arg_names;
    view_rule.hyps = view.hyps;
    view_rule.concl = view.concl;
    for (expected_refs, view.hyps, minor_wants) |*hint, hyp, want| {
        if (hint.* != null or !want) continue;
        hint.* = try OpenTerms.instantiateTemplateHoley(
            theorem,
            context.env,
            context.registry,
            &view_rule,
            hyp,
            bindings,
            if (holey_parent)
                .{ .placeholder_factory = .{ .makeFn = mintHintHole } }
            else
                .{},
        );
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
    const line_expr = LineGoal.interned(expected_conclusion_hint, line_assertion) orelse
        return try context.allocator.dupe(?ExprId, partial_bindings);
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

/// The binders a holey expected-conclusion hint fixes for `rule`, or null
/// when it fixes none beyond `partial_bindings`.
///
/// Matches the conclusion against the hint with placeholders as wildcards: a
/// binder whose hint subterm holds a placeholder stays open, as does an ACUI
/// spine binder (its position is only a guess). `¬D ⊢ ‹hole›` against
/// `imp_intro`'s `g ⊢ a → b` yields `g := ¬D` although the hint as a whole
/// cannot match. Caller owns the result.
pub fn seedBindingsFromHoleyHint(
    allocator: std.mem.Allocator,
    theorem: *TheoremContext,
    registry: *const RewriteRegistry,
    rule: *const RuleDecl,
    hint: ExprId,
    partial_bindings: []const ?ExprId,
) !?[]?ExprId {
    if (!theorem.containsPlaceholder(hint)) return null;
    const seeded = try allocator.dupe(?ExprId, partial_bindings);
    errdefer allocator.free(seeded);
    if (try matchTemplateHoley(theorem, registry, rule.concl, hint, seeded, .skip)) {
        demoteAcuiSpineBindingsInTemplate(registry, rule.concl, false, partial_bindings, seeded);
        if (!std.mem.eql(?ExprId, seeded, partial_bindings)) return seeded;
    }
    allocator.free(seeded);
    return null;
}

/// How `matchTemplateHoley` treats a binder facing a subterm with a
/// placeholder in it. Either way the face never contradicts the binding.
const HoleyFace = enum {
    /// Leave the binder alone: only hole-free faces bind.
    skip,
    /// Bind the holey face, merged with the binder's other faces.
    bind,
};

/// Match `template` against `expr`, which may hold placeholders, extending
/// `bindings`. A placeholder matches anything.
fn matchTemplateHoley(
    theorem: *TheoremContext,
    registry: *const RewriteRegistry,
    template: TemplateExpr,
    expr: ExprId,
    bindings: []?ExprId,
    holey_face: HoleyFace,
) !bool {
    if (theorem.isPlaceholder(expr)) return true;
    switch (template) {
        .binder => |idx| {
            if (idx >= bindings.len) return false;
            const holey = theorem.containsPlaceholder(expr);
            const existing = bindings[idx] orelse {
                if (!holey or holey_face == .bind) bindings[idx] = expr;
                return true;
            };
            if (existing == expr) return true;
            const existing_holey = theorem.containsPlaceholder(existing);
            if (!holey and !existing_holey) return false;
            if (holey_face == .skip) return holey;
            // Two faces of one binder: each shows part of it. On a clash
            // (or through an ACUI combiner, where faces line up only modulo
            // order) the first face stays unless the new one is hole-free.
            bindings[idx] = try mergeHoleyFaces(theorem, registry, existing, expr) orelse
                if (holey) existing else expr;
            return true;
        },
        .app => |app| {
            const node = theorem.interner.node(expr);
            if (node.* != .app or node.app.term_id != app.term_id or
                node.app.args.len != app.args.len) return false;
            for (app.args, node.app.args) |targ, earg| {
                if (!try matchTemplateHoley(theorem, registry, targ, earg, bindings, holey_face)) return false;
            }
            return true;
        },
    }
}

/// The most specific expression both faces show, or null when their visible
/// parts clash. A placeholder gives way to the other face; heads must agree
/// and not be an ACUI combiner, whose arguments are not positional.
fn mergeHoleyFaces(
    theorem: *TheoremContext,
    registry: *const RewriteRegistry,
    a: ExprId,
    b: ExprId,
) !?ExprId {
    if (a == b or theorem.isPlaceholder(b)) return a;
    if (theorem.isPlaceholder(a)) return b;
    const a_node = theorem.interner.node(a);
    const b_node = theorem.interner.node(b);
    if (a_node.* != .app or b_node.* != .app) return null;
    const a_app = a_node.app;
    const b_app = b_node.app;
    if (a_app.term_id != b_app.term_id or a_app.args.len != b_app.args.len or
        registry.hasStructuralCombiner(a_app.term_id)) return null;
    const args = try theorem.allocator.alloc(ExprId, a_app.args.len);
    defer theorem.allocator.free(args);
    for (a_app.args, b_app.args, args) |a_arg, b_arg, *arg| {
        arg.* = try mergeHoleyFaces(theorem, registry, a_arg, b_arg) orelse return null;
    }
    return try theorem.interner.internApp(a_app.term_id, args);
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

/// Candidate pins for an ambiguous ACUI principal in `rule`'s conclusion.
///
/// A rule like `not_left` (`g , ¬ a ⊢ ⊥`) against `¬D , P x , ¬P y ⊢ ⊥` has
/// two members its principal `¬ a` can claim. Strict replay of the conclusion
/// commits to the one its positional spine match reaches (the last), so the
/// application checks or fails by member ORDER. When the principal is also
/// what an inline minor's hint needs (`not_left [ex_intro [l5]]`: `a` fixes
/// `ex_intro`'s conclusion, which is not known until its hint is), nothing
/// downstream can correct that guess. Each returned slice pins the principal's
/// binders to one competing member, exactly as if the user had written those
/// bindings, for the caller to retry with.
///
/// Returns an empty list unless the first combiner spine in the conclusion has
/// exactly one structured member (the principal), at least one bare binder
/// member not bound explicitly (the rest), and at least two expected members
/// that match the principal consistently with `explicit`. Members carrying a
/// placeholder (from a holey hint) are skipped. Free the result with
/// `freePrincipalPins`.
pub fn ambiguousPrincipalPins(
    allocator: std.mem.Allocator,
    theorem: *const TheoremContext,
    env: *const GlobalEnv,
    registry: *const RewriteRegistry,
    rule: *const RuleDecl,
    expected: ExprId,
    explicit: []const ?ExprId,
) ![][]?ExprId {
    var pins = std.ArrayListUnmanaged([]?ExprId){};
    errdefer {
        for (pins.items) |pin| allocator.free(pin);
        pins.deinit(allocator);
    }
    const site = findPrincipalSite(theorem, registry, rule.concl, expected) orelse
        return &.{};
    const combiner = AcuiBag.Combiner.of(registry, env, site.head_id) orelse return &.{};

    const template_members = combiner.flattenTemplate(site.template) orelse return &.{};
    var principal: ?TemplateExpr = null;
    var has_open_rest = false;
    for (template_members.slice()) |member| switch (member) {
        .binder => |idx| {
            if (idx >= explicit.len or explicit[idx] == null) has_open_rest = true;
        },
        .app => {
            if (principal != null) return &.{};
            principal = member;
        },
    };
    const principal_template = principal orelse return &.{};
    if (!has_open_rest) return &.{};

    const expr_members = combiner.flatten(theorem, site.expr) orelse return &.{};

    const scratch = try allocator.alloc(?ExprId, explicit.len);
    defer allocator.free(scratch);
    for (expr_members.slice()) |member| {
        // A holey hint's placeholder member is no candidate: pinning a binder
        // to a placeholder would fix a guess, not a member.
        if (theorem.containsPlaceholder(member)) continue;
        @memcpy(scratch, explicit);
        if (!theorem.matchTemplate(principal_template, member, scratch)) continue;
        const duplicate = for (pins.items) |pin| {
            if (std.mem.eql(?ExprId, pin, scratch)) break true;
        } else false;
        if (duplicate) continue;
        try pins.append(allocator, try allocator.dupe(?ExprId, scratch));
    }
    if (pins.items.len < 2) {
        for (pins.items) |pin| allocator.free(pin);
        pins.deinit(allocator);
        return &.{};
    }
    return try pins.toOwnedSlice(allocator);
}

pub fn freePrincipalPins(allocator: std.mem.Allocator, pins: []const []?ExprId) void {
    for (pins) |pin| allocator.free(pin);
    allocator.free(pins);
}

const PrincipalSite = struct {
    head_id: u32,
    template: TemplateExpr,
    expr: ExprId,
};

/// Walk the conclusion template and the expected expression in lockstep
/// through plain applications to the first combiner spine.
fn findPrincipalSite(
    theorem: *const TheoremContext,
    registry: *const RewriteRegistry,
    template: TemplateExpr,
    expr: ExprId,
) ?PrincipalSite {
    const app = switch (template) {
        .binder => return null,
        .app => |a| a,
    };
    if (registry.hasStructuralCombiner(app.term_id)) {
        return .{ .head_id = app.term_id, .template = template, .expr = expr };
    }
    const node = theorem.interner.node(expr);
    if (node.* != .app or node.app.term_id != app.term_id or
        node.app.args.len != app.args.len) return null;
    for (app.args, node.app.args) |targ, earg| {
        if (findPrincipalSite(theorem, registry, targ, earg)) |site| return site;
    }
    return null;
}

const HoleyFaceFixture = struct {
    arena: std.heap.ArenaAllocator,
    registry: RewriteRegistry,
    theorem: TheoremContext,
    a: ExprId,
    b: ExprId,

    // Term ids: `f` is a free constructor, `comma` an ACUI combiner.
    const f: u32 = 0;
    const comma: u32 = 1;

    fn init(self: *HoleyFaceFixture) !void {
        self.arena = std.heap.ArenaAllocator.init(std.testing.allocator);
        self.registry = RewriteRegistry.init(self.arena.allocator());
        try self.registry.acui_by_head.put(comma, .{
            .unit_term_name = "emp",
            .assoc_name = "comma_assoc",
            .comm_name = "comma_comm",
            .idem_name = "comma_idem",
        });
        self.theorem = TheoremContext.init(std.testing.allocator);
        try self.theorem.seedBinderCount(2);
        self.a = self.theorem.theorem_vars.items[0];
        self.b = self.theorem.theorem_vars.items[1];
    }

    fn deinit(self: *HoleyFaceFixture) void {
        self.theorem.deinit();
        self.arena.deinit();
    }

    fn app(self: *HoleyFaceFixture, head: u32, x: ExprId, y: ExprId) !ExprId {
        return self.theorem.interner.internApp(head, &.{ x, y });
    }

    fn hole(self: *HoleyFaceFixture) !ExprId {
        return self.theorem.addLineHolePlaceholder("obj");
    }

    fn merge(self: *HoleyFaceFixture, x: ExprId, y: ExprId) !?ExprId {
        return mergeHoleyFaces(&self.theorem, &self.registry, x, y);
    }
};

test "two holey faces of one binder merge into what both show" {
    var fx: HoleyFaceFixture = undefined;
    try fx.init();
    defer fx.deinit();
    const f = HoleyFaceFixture.f;

    // A hole gives way to the other face, on either side.
    const h = try fx.hole();
    try std.testing.expectEqual(@as(?ExprId, fx.a), try fx.merge(h, fx.a));
    try std.testing.expectEqual(@as(?ExprId, fx.a), try fx.merge(fx.a, h));

    // f(A, _) and f(_, B) give f(A, B).
    const left = try fx.app(f, fx.a, try fx.hole());
    const right = try fx.app(f, try fx.hole(), fx.b);
    try std.testing.expectEqual(@as(?ExprId, try fx.app(f, fx.a, fx.b)), try fx.merge(left, right));

    // f(A, _) and f(B, _) clash.
    const clash = try fx.app(f, fx.b, try fx.hole());
    try std.testing.expectEqual(@as(?ExprId, null), try fx.merge(left, clash));
}

test "holey faces under an ACUI combiner are not merged by position" {
    var fx: HoleyFaceFixture = undefined;
    try fx.init();
    defer fx.deinit();
    const comma = HoleyFaceFixture.comma;

    // `A , _` and `_ , A` line up only modulo order: merging by position
    // would guess `A , A`.
    const left = try fx.app(comma, fx.a, try fx.hole());
    const right = try fx.app(comma, try fx.hole(), fx.a);
    try std.testing.expectEqual(@as(?ExprId, null), try fx.merge(left, right));
    try std.testing.expectEqual(@as(?ExprId, left), try fx.merge(left, left));
}

test "a binder's holey faces merge; on a clash the first stands unless the new face is hole-free" {
    var fx: HoleyFaceFixture = undefined;
    try fx.init();
    defer fx.deinit();
    const f = HoleyFaceFixture.f;
    const g: u32 = 2;

    // Template f(x, x) against f(g(A, _), <second face>).
    const tmpl_args = [_]TemplateExpr{ .{ .binder = 0 }, .{ .binder = 0 } };
    const template: TemplateExpr = .{ .app = .{ .term_id = f, .args = &tmpl_args } };
    const first = try fx.app(g, fx.a, try fx.hole());
    const cases = [_]struct { second: ExprId, want: ExprId }{
        // Holes on both sides: the faces merge.
        .{ .second = try fx.app(g, try fx.hole(), fx.b), .want = try fx.app(g, fx.a, fx.b) },
        // A holey face that clashes leaves the first.
        .{ .second = try fx.app(g, fx.b, try fx.hole()), .want = first },
        // A hole-free face replaces the first, as before.
        .{ .second = try fx.app(g, fx.b, fx.b), .want = try fx.app(g, fx.b, fx.b) },
    };
    for (cases) |case| {
        var bindings = [_]?ExprId{null};
        const goal = try fx.app(f, first, case.second);
        try std.testing.expect(try matchTemplateHoley(&fx.theorem, &fx.registry, template, goal, &bindings, .bind));
        try std.testing.expectEqual(@as(?ExprId, case.want), bindings[0]);
    }
}
