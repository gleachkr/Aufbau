//! Shared types for theorem-block checking — the rule-application
//! context, per-line assertion forms, probe result carriers — plus the small
//! theorem-var-map and saved-diagnostic helpers everything shares.

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

pub const NameExprMap = std.StringHashMap(*const Expr);

pub const LabelIndexMap = std.StringHashMap(usize);

pub const SuccessfulLineAttempt = struct {
    line_idx: usize,
    theorem: TheoremContext,
    theorem_vars: NameExprMap,
};

pub const UnresolvedHypothesis = struct {
    index: usize,
    expected: ?ExprId,
};

pub const ConclusionProbe = struct {
    allocator: std.mem.Allocator,
    rule_id: u32,
    rule_name: []const u8,
    bindings: []const ?ExprId,
    raw_conclusion: ExprId,
    displayed_conclusion: ExprId,
    unresolved_hyps: []const UnresolvedHypothesis,

    pub fn deinit(self: *ConclusionProbe) void {
        self.allocator.free(self.bindings);
        self.allocator.free(self.unresolved_hyps);
        self.* = undefined;
    }
};

pub const RefExpectationProbe = struct {
    allocator: std.mem.Allocator,
    rule_id: u32,
    bindings: []const ?ExprId,
    contextual_bindings: []const ?ExprId,
    expected_refs: []const ?ExprId,

    pub fn deinit(self: *RefExpectationProbe) void {
        self.allocator.free(self.bindings);
        self.allocator.free(self.contextual_bindings);
        self.allocator.free(self.expected_refs);
        self.* = undefined;
    }
};

pub const LineAssertion = union(enum) {
    concrete: ExprId,
    holey: *const Expr,
    implicit_whole_conclusion,

    pub fn fromParsed(parsed: Holes.ParsedAssertion) LineAssertion {
        return switch (parsed) {
            .concrete => |expr_id| .{ .concrete = expr_id },
            .holey => |expr| .{ .holey = expr },
        };
    }
};

pub const CandidateElaboration = struct {
    resolved_bindings: []const ExprId,
    raw_conclusion: ExprId,
    displayed_conclusion: ExprId,
};

pub const ApplicationDiagnosticContext = struct {
    theorem_name: []const u8,
    line_label: ?[]const u8,
    span: ?Span,

    pub fn fromLine(assertion: AssertionStmt, line: ProofLine) @This() {
        return .{
            .theorem_name = assertion.name,
            .line_label = line.label,
            .span = line.span,
        };
    }
};

pub const ApplicationLine = struct {
    label: []const u8,
    application: RuleApplication,
    assertion_span: Span,

    pub fn fromLine(line: ProofLine) @This() {
        return .{
            .label = line.label,
            .application = line.application,
            .assertion_span = line.assertion.span,
        };
    }

    pub fn forInline(parent: ApplicationLine, application: RuleApplication) @This() {
        return .{
            .label = parent.label,
            .application = application,
            .assertion_span = application.span,
        };
    }

    pub fn ruleApplicationSpan(self: @This()) Span {
        return self.application.ruleApplicationSpan();
    }

    pub fn refsOrRuleSpan(self: @This()) Span {
        return self.application.refsOrRuleSpan();
    }

    pub fn bindingSpan(self: @This(), binder_name: ?[]const u8) ?Span {
        return self.application.bindingSpan(binder_name);
    }
};

pub const RuleApplyContext = struct {
    allocator: std.mem.Allocator,
    parser: *MM0Parser,
    env: *const GlobalEnv,
    registry: *RewriteRegistry,
    rule_catalog: *const RuleCatalog.Catalog,
    fresh_bindings: *const std.AutoHashMap(u32, []const FreshDecl),
    freshen_bindings: *const std.AutoHashMap(u32, []const FreshenDecl),
    views: *const std.AutoHashMap(u32, ViewDecl),
    sort_vars: *const SortVarRegistry,
    assertion: AssertionStmt,
    labels: *const LabelIndexMap,
    /// Every line in the block, in order — including lines not yet
    /// checked. Lets the unknown-label diagnostic distinguish a typo from a
    /// reference to a line that appears later in the proof. Empty for the
    /// search's own contexts, which check one line at a time.
    block_lines: []const ProofScript.ProofLine = &.{},
    checked: *std.ArrayListUnmanaged(CheckedLine),
    diag_scratch: *CompilerDiag.Scratch,
    rule_unify_cache: *Inference.RuleUnifyCache,
};

pub fn buildTheoremVarMap(
    allocator: std.mem.Allocator,
    assertion: AssertionStmt,
) !NameExprMap {
    var vars = NameExprMap.init(allocator);
    for (assertion.arg_names, assertion.arg_exprs) |name, expr| {
        if (name) |actual_name| {
            try vars.put(actual_name, expr);
        }
    }
    return vars;
}

pub fn cloneNameExprMap(
    allocator: std.mem.Allocator,
    src: *const NameExprMap,
) !NameExprMap {
    var dst = NameExprMap.init(allocator);
    errdefer dst.deinit();

    try dst.ensureTotalCapacity(src.count());
    var it = src.iterator();
    while (it.next()) |entry| {
        try dst.put(entry.key_ptr.*, entry.value_ptr.*);
    }
    return dst;
}

pub fn getDiagnostic(self: *CompilerContext) ?Diagnostic {
    return self.getDiagnostic();
}

pub fn restoreDiagnostic(self: *CompilerContext, diag: ?Diagnostic) void {
    self.restoreDiagnostic(diag);
}
