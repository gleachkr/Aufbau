//! Binding inference and candidate elaboration: parse explicit
//! bindings, infer the rest, and validate assertions against candidates.

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
const CompilerViews = @import("../views.zig");
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
const Idents = @import("../idents.zig");
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
const CandidateElaboration = @import("./types.zig").CandidateElaboration;
const ApplicationLine = @import("./types.zig").ApplicationLine;
const getDiagnostic = @import("./types.zig").getDiagnostic;
const restoreDiagnostic = @import("./types.zig").restoreDiagnostic;

pub fn resolveLineAssertionForBindings(
    self: *CompilerContext,
    allocator: std.mem.Allocator,
    parser: *MM0Parser,
    theorem: *TheoremContext,
    env: *const GlobalEnv,
    registry: *RewriteRegistry,
    diag_scratch: *CompilerDiag.Scratch,
    assertion: AssertionStmt,
    line: ApplicationLine,
    rule: *const RuleDecl,
    line_assertion: LineAssertion,
    bindings: []const ExprId,
) !ExprId {
    return switch (line_assertion) {
        .concrete => |line_expr| line_expr,
        .implicit_whole_conclusion => try theorem.instantiateTemplate(
            rule.concl,
            bindings,
        ),
        .holey => |holey| blk: {
            const expected_line = try theorem.instantiateTemplate(
                rule.concl,
                bindings,
            );
            break :blk try validateHoleyAssertionAgainstCandidate(
                self,
                allocator,
                parser,
                theorem,
                env,
                registry,
                diag_scratch,
                assertion,
                line,
                holey,
                expected_line,
            );
        },
    };
}

fn requireConcreteBindingsWithDiagnostic(
    self: *CompilerContext,
    allocator: std.mem.Allocator,
    env: *const GlobalEnv,
    theorem: *const TheoremContext,
    assertion: AssertionStmt,
    rule: *const RuleDecl,
    line: ApplicationLine,
    partial_bindings: []const ?ExprId,
) ![]const ExprId {
    for (partial_bindings, 0..) |binding, idx| {
        if (binding != null) continue;
        self.setProof(
            try Inference.buildMissingBinderDiagnostic(
                allocator,
                env,
                theorem,
                assertion,
                rule,
                line,
                .strict_replay,
                partial_bindings,
                partial_bindings,
                idx,
                null,
            ),
        );
        return error.MissingBinderAssignment;
    }
    return try Inference.requireConcreteBindings(allocator, partial_bindings);
}

fn concreteBindingsToOptional(
    allocator: std.mem.Allocator,
    bindings: []const ExprId,
) ![]const ?ExprId {
    const optional = try allocator.alloc(?ExprId, bindings.len);
    for (bindings, 0..) |binding, idx| {
        optional[idx] = binding;
    }
    return optional;
}

pub fn inferCandidateOptionalBindings(
    self: *CompilerContext,
    context: *const Inference.RuleInferenceContext,
    line: ApplicationLine,
    line_assertion: LineAssertion,
    partial_bindings: []const ?ExprId,
    base_ref_exprs: []const ExprId,
    expected_conclusion_hint: ?ExprId,
    fresh_context: Inference.HiddenWitnessFreshContext,
    maybe_view: ?ViewDecl,
    had_omitted: bool,
    rule_has_advanced_inference: bool,
    use_advanced_inference: bool,
    has_omitted_structural: bool,
    prefer_structural_solver: bool,
) ![]const ?ExprId {
    const allocator = context.allocator;
    switch (line_assertion) {
        .concrete => |line_expr| {
            if (had_omitted) {
                return try Inference.inferOptionalBindingsAllowUnresolved(
                    self,
                    context,
                    line,
                    partial_bindings,
                    base_ref_exprs,
                    line_expr,
                    fresh_context,
                    maybe_view,
                    use_advanced_inference,
                    prefer_structural_solver,
                );
            }
        },
        .holey => |holey| {
            if (had_omitted) {
                return try inferHoleyOptionalBindingsForProbe(
                    context,
                    partial_bindings,
                    base_ref_exprs,
                    maybe_view,
                    holey,
                );
            }
        },
        .implicit_whole_conclusion => {},
    }

    const concrete = try inferCandidateBindings(
        self,
        context,
        line,
        line_assertion,
        partial_bindings,
        base_ref_exprs,
        expected_conclusion_hint,
        fresh_context,
        maybe_view,
        had_omitted,
        rule_has_advanced_inference,
        use_advanced_inference,
        has_omitted_structural,
        prefer_structural_solver,
    );
    defer allocator.free(concrete);
    return try concreteBindingsToOptional(allocator, concrete);
}

fn inferHoleyOptionalBindingsForProbe(
    context: *const Inference.RuleInferenceContext,
    partial_bindings: []const ?ExprId,
    base_ref_exprs: []const ExprId,
    maybe_view: ?ViewDecl,
    holey: *const Expr,
) ![]const ?ExprId {
    const allocator = context.allocator;
    const theorem = context.theorem;
    const rule = context.rule;
    const optional = try allocator.dupe(?ExprId, partial_bindings);
    errdefer allocator.free(optional);

    for (rule.hyps, base_ref_exprs) |hyp, ref_expr| {
        if (!theorem.matchTemplate(hyp, ref_expr, optional)) {
            return error.UnifyMismatch;
        }
    }

    if (maybe_view) |view| {
        CompilerViews.applyViewBindingsSurfaceConclusion(
            allocator,
            theorem,
            context.env,
            context.registry,
            &view,
            holey,
            base_ref_exprs,
            optional,
            null,
            null,
            false,
        ) catch |err| {
            if (err == error.OutOfMemory) return err;
            try matchRawTemplateToHoleyConclusion(theorem, rule, optional, holey);
        };
    } else {
        try matchRawTemplateToHoleyConclusion(theorem, rule, optional, holey);
    }

    return optional;
}

fn matchRawTemplateToHoleyConclusion(
    theorem: *TheoremContext,
    rule: *const RuleDecl,
    bindings: []?ExprId,
    holey: *const Expr,
) !void {
    var report = Holes.InferenceReport{};
    if (!try Holes.matchTemplateToSurfaceDetailed(
        theorem,
        rule.concl,
        holey,
        bindings,
        &report,
    )) {
        return error.HoleyInferenceMismatch;
    }
}

pub fn validateOptionalBindingsForProbe(
    self: *CompilerContext,
    env: *const GlobalEnv,
    theorem: *const TheoremContext,
    parser: ?*const MM0Parser,
    theorem_vars: ?*const NameExprMap,
    assertion: AssertionStmt,
    line: ApplicationLine,
    rule: *const RuleDecl,
    bindings: []const ?ExprId,
) !void {
    var all_resolved = true;
    for (bindings, 0..) |binding, idx| {
        const expr = binding orelse {
            all_resolved = false;
            continue;
        };
        Inference.validateBindingExpr(
            env,
            theorem,
            assertion.args,
            rule.args[idx],
            expr,
        ) catch |err| {
            var diag = CompilerDiag.withPhase(.{
                .kind = .generic,
                .err = err,
                .theorem_name = assertion.name,
                .line_label = line.label,
                .rule_name = line.application.rule_name,
                .name = rule.arg_names[idx],
                .span = CompilerDiag.proofBindingDiagnosticSpan(
                    line,
                    rule.arg_names[idx],
                ),
            }, .inference);
            var note_bufs: Inference.BindingValidationNoteBufs = .{};
            Inference.attachBindingValidationNotes(
                &diag,
                &note_bufs,
                env,
                theorem,
                parser,
                theorem_vars,
                assertion.args,
                rule.args[idx],
                expr,
                err,
            );
            self.setProof(diag);
            return err;
        };
    }
    if (!all_resolved) {
        if (try Inference.firstPartialDepViolation(
            env,
            theorem,
            assertion.args,
            rule.args,
            rule.arg_names,
            bindings,
        )) |found_detail| {
            var detail = found_detail;
            var text_bufs: Inference.DepViolationTextBufs = .{};
            Inference.attachDepViolationBindingTexts(
                &text_bufs,
                env,
                theorem,
                parser,
                theorem_vars,
                &detail,
                bindings[detail.first_arg_idx],
                bindings[detail.second_arg_idx],
            );
            self.setProof(CompilerDiag.withPhase(.{
                .kind = .generic,
                .err = error.DepViolation,
                .theorem_name = assertion.name,
                .line_label = line.label,
                .rule_name = line.application.rule_name,
                .span = line.ruleApplicationSpan(),
                .detail = .{ .dep_violation = detail },
            }, .theorem_application));
            return error.DepViolation;
        }
        return;
    }

    const concrete = try Inference.requireConcreteBindings(
        theorem.allocator,
        bindings,
    );
    defer theorem.allocator.free(concrete);
    try Inference.validateResolvedBindingsWithDebug(
        self,
        self.debug,
        env,
        theorem,
        parser,
        theorem_vars,
        assertion,
        line,
        rule,
        concrete,
    );
}

pub fn inferCandidateBindings(
    self: *CompilerContext,
    context: *const Inference.RuleInferenceContext,
    line: ApplicationLine,
    line_assertion: LineAssertion,
    partial_bindings: []const ?ExprId,
    base_ref_exprs: []const ExprId,
    expected_conclusion_hint: ?ExprId,
    fresh_context: Inference.HiddenWitnessFreshContext,
    maybe_view: ?ViewDecl,
    had_omitted: bool,
    rule_has_advanced_inference: bool,
    use_advanced_inference: bool,
    has_omitted_structural: bool,
    prefer_structural_solver: bool,
) ![]const ExprId {
    const allocator = context.allocator;
    const env = context.env;
    const registry = context.registry;
    const theorem = context.theorem;
    const assertion = context.assertion;
    const rule = context.rule;

    return switch (line_assertion) {
        .holey => |holey| blk: {
            const has_structural_hole = try Holes.containsStructuralHole(
                env,
                registry,
                holey,
            );
            // Exact refs can identify a candidate before the visible holey
            // assertion is checked.  Keep this shortcut conservative: it must
            // solve every binder, and it must not bypass structural-hole
            // inference such as `_ctx` ACUI minimal-residual solving.
            if (had_omitted and
                !has_structural_hole and
                !prefer_structural_solver)
            {
                if (try Inference.inferBindingsFromRefsOnly(
                    allocator,
                    theorem,
                    rule,
                    partial_bindings,
                    base_ref_exprs,
                )) |refs_only_bindings| {
                    break :blk refs_only_bindings;
                }
            }

            const use_holey_advanced = had_omitted and
                (rule_has_advanced_inference or has_structural_hole);
            if (use_holey_advanced) {
                break :blk Inference.inferBindingsFromHoleyAdvanced(
                    self,
                    context,
                    line,
                    partial_bindings,
                    base_ref_exprs,
                    holey,
                    maybe_view,
                    fresh_context,
                ) catch |err| {
                    if (getDiagnostic(self) == null) {
                        try setHoleyInferenceDiagnostic(
                            self,
                            allocator,
                            env,
                            theorem,
                            assertion,
                            line,
                            rule,
                            holey,
                            err,
                            .{},
                            fresh_context,
                        );
                    }
                    return err;
                };
            }
            if (!had_omitted) {
                break :blk try Inference.requireConcreteBindings(
                    allocator,
                    partial_bindings,
                );
            }
            var hole_report = Holes.InferenceReport{};
            break :blk Holes.inferBindingsFromAssertionDetailed(
                allocator,
                theorem,
                rule,
                partial_bindings,
                base_ref_exprs,
                holey,
                &hole_report,
            ) catch |err| {
                // The lightweight hole matcher is deliberately exact.  If
                // the visible assertion is too holey, exact ref replay can
                // fail before it gets to the candidate conclusion, even when
                // transparent rule matching would identify a unique concrete
                // candidate from the refs.  Try that def-aware path before
                // reporting the exact matcher's failure.
                if (err == error.UnifyMismatch or
                    err == error.HoleyInferenceMismatch)
                {
                    if (Inference.inferBindingsFromHoleyAdvanced(
                        self,
                        context,
                        line,
                        partial_bindings,
                        base_ref_exprs,
                        holey,
                        maybe_view,
                        fresh_context,
                    )) |bindings| {
                        restoreDiagnostic(self, null);
                        break :blk bindings;
                    } else |_| {
                        restoreDiagnostic(self, null);
                    }
                }
                try setHoleyInferenceDiagnostic(
                    self,
                    allocator,
                    env,
                    theorem,
                    assertion,
                    line,
                    rule,
                    holey,
                    err,
                    hole_report,
                    fresh_context,
                );
                return err;
            };
        },
        .implicit_whole_conclusion => blk: {
            if (had_omitted) {
                if (expected_conclusion_hint) |hint| {
                    if (Inference.inferBindings(
                        self,
                        context,
                        line,
                        partial_bindings,
                        base_ref_exprs,
                        hint,
                        fresh_context,
                        maybe_view,
                        use_advanced_inference,
                        prefer_structural_solver,
                    )) |hint_bindings| {
                        restoreDiagnostic(self, null);
                        break :blk hint_bindings;
                    } else |err| {
                        if (err == error.OutOfMemory) return err;
                        restoreDiagnostic(self, null);
                    }
                }
                if (maybe_view) |view| {
                    const seeded = try allocator.dupe(
                        ?ExprId,
                        partial_bindings,
                    );
                    defer allocator.free(seeded);
                    const view_applied = if (CompilerViews.applyViewBindingsRefsOnly(
                        allocator,
                        theorem,
                        env,
                        registry,
                        &view,
                        base_ref_exprs,
                        seeded,
                        null,
                        null,
                        self.debug.views,
                    ))
                        true
                    else |err| blk_view: {
                        if (err == error.OutOfMemory) return err;
                        break :blk_view false;
                    };
                    if (view_applied) {
                        if (!Inference.hasOmittedBindings(seeded)) {
                            break :blk try Inference.requireConcreteBindings(
                                allocator,
                                seeded,
                            );
                        }
                        if (try Inference.inferBindingsFromRefsOnly(
                            allocator,
                            theorem,
                            rule,
                            seeded,
                            base_ref_exprs,
                        )) |refs_only_bindings| {
                            break :blk refs_only_bindings;
                        }
                    }
                }
                // For implicit chained applications, an exact refs-only
                // result can commit to a non-minimal structural residual
                // before the enclosing application can validate it. Let the
                // structural path see the whole constraint set instead.
                if (!has_omitted_structural or !use_advanced_inference) {
                    if (try Inference.inferBindingsFromRefsOnly(
                        allocator,
                        theorem,
                        rule,
                        partial_bindings,
                        base_ref_exprs,
                    )) |refs_only_bindings| {
                        break :blk refs_only_bindings;
                    }
                }
                // Keep the cheap exact path above for ordinary inline
                // applications. If normalized or view-backed rules remain
                // underdetermined, treat the implicit conclusion like a
                // whole-line hole so structural hypothesis constraints can
                // recover hidden binders, e.g. an ACUI context for `nd`.
                if (use_advanced_inference) {
                    const whole_hole = Expr{ .hole = .{
                        .sort = try templateSort(env, rule, rule.concl),
                        .token = "<implicit>",
                    } };
                    break :blk try Inference.inferBindingsFromHoleyAdvanced(
                        self,
                        context,
                        line,
                        partial_bindings,
                        base_ref_exprs,
                        &whole_hole,
                        maybe_view,
                        fresh_context,
                    );
                }
            }
            break :blk try requireConcreteBindingsWithDiagnostic(
                self,
                allocator,
                env,
                theorem,
                assertion,
                rule,
                line,
                partial_bindings,
            );
        },
        .concrete => |line_expr| blk: {
            if (had_omitted) {
                break :blk try Inference.inferBindings(
                    self,
                    context,
                    line,
                    partial_bindings,
                    base_ref_exprs,
                    line_expr,
                    fresh_context,
                    maybe_view,
                    use_advanced_inference,
                    prefer_structural_solver,
                );
            }
            break :blk try Inference.requireConcreteBindings(
                allocator,
                partial_bindings,
            );
        },
    };
}

fn templateSort(
    env: *const GlobalEnv,
    rule: *const RuleDecl,
    template: TemplateExpr,
) !u7 {
    const sort_name = switch (template) {
        .binder => |idx| rule.args[idx].sort_name,
        .app => |app| blk: {
            if (app.term_id >= env.terms.items.len) return error.UnknownTerm;
            break :blk env.terms.items[app.term_id].ret_sort_name;
        },
    };
    const sort_id = env.sort_names.get(sort_name) orelse {
        return error.UnknownSort;
    };
    return @intCast(sort_id);
}

pub fn elaborateCandidateLine(
    self: *CompilerContext,
    allocator: std.mem.Allocator,
    parser: *MM0Parser,
    theorem: *TheoremContext,
    env: *const GlobalEnv,
    registry: *RewriteRegistry,
    diag_scratch: *CompilerDiag.Scratch,
    assertion: AssertionStmt,
    line: ApplicationLine,
    rule: *const RuleDecl,
    line_assertion: LineAssertion,
    resolved_bindings: []const ExprId,
) !CandidateElaboration {
    const raw_conclusion = try theorem.instantiateTemplate(
        rule.concl,
        resolved_bindings,
    );
    const displayed_conclusion = switch (line_assertion) {
        .concrete => |line_expr| line_expr,
        .implicit_whole_conclusion => raw_conclusion,
        .holey => |holey| try validateHoleyAssertionAgainstCandidate(
            self,
            allocator,
            parser,
            theorem,
            env,
            registry,
            diag_scratch,
            assertion,
            line,
            holey,
            raw_conclusion,
        ),
    };
    return .{
        .resolved_bindings = resolved_bindings,
        .raw_conclusion = raw_conclusion,
        .displayed_conclusion = displayed_conclusion,
    };
}

fn validateHoleyAssertionAgainstCandidate(
    self: *CompilerContext,
    allocator: std.mem.Allocator,
    parser: *MM0Parser,
    theorem: *TheoremContext,
    env: *const GlobalEnv,
    registry: *RewriteRegistry,
    diag_scratch: *CompilerDiag.Scratch,
    assertion: AssertionStmt,
    line: ApplicationLine,
    holey: *const Expr,
    expected_line: ExprId,
) !ExprId {
    // Prefer the raw instantiated conclusion when the holey surface permits
    // it. A whole-line hole such as `_wff` can match anything; returning the
    // normalized form there hides the rule's raw constructor from later
    // omitted-binder inference that uses this line as a ref. If the raw shape
    // does not match the visible surface, normalized and materialized checks
    // below still handle normalized conclusions.
    var hole_report = Holes.ConcreteMatchReport{};
    if (try holeyAssertionMatchesCandidate(
        allocator,
        parser,
        theorem,
        env,
        holey,
        expected_line,
        &hole_report,
    )) {
        return expected_line;
    }

    var scratch_checked = std.ArrayListUnmanaged(CheckedLine){};
    defer scratch_checked.deinit(allocator);
    const normalized_line = try Normalize.normalizeExprForSnapshot(
        allocator,
        theorem,
        registry,
        env,
        &scratch_checked,
        diag_scratch,
        expected_line,
    );
    if (normalized_line != expected_line) {
        var normalized_report = Holes.ConcreteMatchReport{};
        if (try holeyAssertionMatchesCandidate(
            allocator,
            parser,
            theorem,
            env,
            holey,
            normalized_line,
            &normalized_report,
        )) {
            return normalized_line;
        }
        hole_report = normalized_report;
    }

    const can_materialize = normalized_line != expected_line or
        try Holes.containsStructuralHole(env, registry, holey);
    if (can_materialize) {
        var materialized_report = Holes.ConcreteMatchReport{};
        if (try Holes.materializeSurfaceWithCandidate(
            parser,
            theorem,
            env,
            holey,
            expected_line,
            &materialized_report,
        )) |materialized_line| {
            return materialized_line;
        } else if (materialized_report.failure != null) {
            hole_report = materialized_report;
        }
    }

    var diag = CompilerDiag.withPhase(.{
        .kind = .conclusion_mismatch,
        .err = error.HoleConclusionMismatch,
        .theorem_name = assertion.name,
        .line_label = line.label,
        .rule_name = line.application.rule_name,
        .span = concreteMatchFailureSpan(line, hole_report) orelse
            line.assertion_span,
    }, .theorem_application);
    addHoleConcreteMatchNotes(&diag, line, hole_report);
    self.setProof(diag);
    return error.HoleConclusionMismatch;
}

fn holeyAssertionMatchesCandidate(
    allocator: std.mem.Allocator,
    parser: *MM0Parser,
    theorem: *TheoremContext,
    env: *const GlobalEnv,
    holey: *const Expr,
    candidate: ExprId,
    report: *Holes.ConcreteMatchReport,
) !bool {
    var exact_report = Holes.ConcreteMatchReport{};
    if (try Holes.matchesConcreteDetailed(
        parser,
        theorem,
        env,
        holey,
        candidate,
        &exact_report,
    )) {
        return true;
    }

    var semantic_report = Holes.ConcreteMatchReport{};
    if (try Holes.matchesConcreteSemanticallyDetailed(
        allocator,
        parser,
        theorem,
        env,
        holey,
        candidate,
        &semantic_report,
    )) {
        return true;
    }

    report.* = semantic_report;
    return false;
}

pub fn parseBindings(
    self: *CompilerContext,
    allocator: std.mem.Allocator,
    parser: *MM0Parser,
    theorem: *TheoremContext,
    theorem_vars: *NameExprMap,
    sort_vars: *const SortVarRegistry,
    theorem_name: []const u8,
    rule: *const RuleDecl,
    application: RuleApplication,
    line: ApplicationLine,
) ![]?ExprId {
    for (rule.arg_names) |arg_name| {
        if (arg_name == null) {
            self.setProof(CompilerDiag.withPhase(.{
                .kind = .generic,
                .err = error.UnnamedRuleBinder,
                .theorem_name = theorem_name,
                .line_label = line.label,
                .rule_name = application.rule_name,
                .span = application.ruleApplicationSpan(),
            }, .theorem_application));
            return error.UnnamedRuleBinder;
        }
    }

    const bindings = try allocator.alloc(?ExprId, rule.args.len);
    @memset(bindings, null);

    for (application.arg_bindings) |binding| {
        const arg_index = findRuleArgIndex(rule, binding.name) orelse {
            self.setProof(CompilerDiag.withPhase(.{
                .kind = .unknown_binder_name,
                .err = error.UnknownBinderName,
                .theorem_name = theorem_name,
                .line_label = line.label,
                .rule_name = application.rule_name,
                .name = binding.name,
                .span = binding.span,
            }, .theorem_application));
            return error.UnknownBinderName;
        };
        if (bindings[arg_index] != null) {
            self.setProof(CompilerDiag.withPhase(.{
                .kind = .duplicate_binder_assignment,
                .err = error.DuplicateBinderAssignment,
                .theorem_name = theorem_name,
                .line_label = line.label,
                .rule_name = application.rule_name,
                .name = binding.name,
                .span = binding.span,
            }, .theorem_application));
            return error.DuplicateBinderAssignment;
        }

        const expr = blk: {
            try CompilerVars.ensureMathTextVars(
                parser,
                theorem,
                theorem_vars,
                sort_vars,
                binding.formula.text,
            );
            break :blk parser.parseArgText(
                binding.formula.text,
                theorem_vars,
                rule.args[arg_index],
            );
        } catch |err| {
            var diag = CompilerDiag.proofMathParseDiagnostic(
                parser,
                .parse_binding,
                err,
                theorem_name,
                line.label,
                application.rule_name,
                binding.name,
                binding.formula.span,
            );
            DiagNotes.attachSortRetryNote(
                &diag,
                parser,
                theorem_vars,
                rule.args[arg_index],
                binding.formula.text,
            );
            self.setProof(diag);
            return err;
        };
        bindings[arg_index] = try theorem.internParsedExpr(expr);
    }

    return bindings;
}

pub fn lineAssertionKnownDeps(
    env: *const GlobalEnv,
    theorem: *const TheoremContext,
    rule: *const RuleDecl,
    line_assertion: LineAssertion,
    partial_bindings: []const ?ExprId,
) !u55 {
    return switch (line_assertion) {
        .concrete => |expr_id| (try Inference.exprInfo(
            env,
            theorem,
            theorem.arg_infos,
            expr_id,
        )).deps,
        .holey => |expr| expr.deps(),
        .implicit_whole_conclusion => try templateKnownDeps(
            env,
            theorem,
            rule.concl,
            partial_bindings,
        ),
    };
}

fn templateKnownDeps(
    env: *const GlobalEnv,
    theorem: *const TheoremContext,
    template: TemplateExpr,
    partial_bindings: []const ?ExprId,
) !u55 {
    return switch (template) {
        .binder => |idx| blk: {
            const expr_id = partial_bindings[idx] orelse break :blk 0;
            break :blk (try Inference.exprInfo(
                env,
                theorem,
                theorem.arg_infos,
                expr_id,
            )).deps;
        },
        .app => |app| blk: {
            var deps: u55 = 0;
            for (app.args) |arg| {
                deps |= try templateKnownDeps(
                    env,
                    theorem,
                    arg,
                    partial_bindings,
                );
            }
            break :blk deps;
        },
    };
}

pub fn validateFreshBindingsAgainstLine(
    self: *CompilerContext,
    allocator: std.mem.Allocator,
    env: *const GlobalEnv,
    theorem: *TheoremContext,
    theorem_name: []const u8,
    rule: *const RuleDecl,
    line: ApplicationLine,
    line_expr: ExprId,
    ref_exprs: []const ExprId,
    partial_bindings: []const ?ExprId,
    resolved_bindings: []const ExprId,
    fresh_list: []const FreshDecl,
) !void {
    const optional_bindings = try allocator.dupe(?ExprId, partial_bindings);
    defer allocator.free(optional_bindings);
    for (fresh_list) |fresh| {
        optional_bindings[fresh.target_arg_idx] = null;
    }

    const used_deps = try FreshSelect.collectUsedDeps(
        env,
        theorem,
        line_expr,
        ref_exprs,
        optional_bindings,
        0,
    );
    for (fresh_list) |fresh| {
        if (partial_bindings[fresh.target_arg_idx] != null) continue;
        const selected = resolved_bindings[fresh.target_arg_idx];
        const selected_deps = (try Inference.exprInfo(
            env,
            theorem,
            theorem.arg_infos,
            selected,
        )).deps;
        if ((used_deps & selected_deps) == 0) continue;
        self.setProof(CompilerDiag.withPhase(.{
            .kind = .parse_fresh,
            .err = error.FreshNoAvailableVar,
            .theorem_name = theorem_name,
            .line_label = line.label,
            .rule_name = line.application.rule_name,
            .name = rule.arg_names[fresh.target_arg_idx].?,
            .span = line.ruleApplicationSpan(),
        }, .theorem_application));
        return error.FreshNoAvailableVar;
    }
}

pub fn applyFreshBindings(
    self: *CompilerContext,
    parser: *MM0Parser,
    env: *const GlobalEnv,
    theorem: *TheoremContext,
    theorem_vars: *NameExprMap,
    sort_vars: *const SortVarRegistry,
    theorem_name: []const u8,
    rule: *const RuleDecl,
    line: ApplicationLine,
    line_deps: u55,
    ref_exprs: []const ExprId,
    bindings: []?ExprId,
    fresh_list: []const FreshDecl,
) !void {
    const used_deps = try FreshSelect.collectUsedDepsFromLineDeps(
        env,
        theorem,
        line_deps,
        ref_exprs,
        bindings,
        0,
    );
    var reserved_deps: u55 = 0;

    for (fresh_list) |fresh| {
        if (bindings[fresh.target_arg_idx] != null) continue;

        const selection = FreshSelect.chooseFreshBinding(
            parser,
            theorem,
            theorem_vars,
            sort_vars,
            rule.args[fresh.target_arg_idx].sort_name,
            used_deps,
            reserved_deps,
        ) catch |err| {
            self.setProof(CompilerDiag.withPhase(.{
                .kind = .parse_fresh,
                .err = err,
                .theorem_name = theorem_name,
                .line_label = line.label,
                .rule_name = line.application.rule_name,
                .name = rule.arg_names[fresh.target_arg_idx].?,
                .span = line.ruleApplicationSpan(),
            }, .theorem_application));
            return err;
        };
        bindings[fresh.target_arg_idx] = selection.expr_id;
        reserved_deps |= selection.deps;
    }
}
