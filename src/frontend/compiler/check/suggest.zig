//! Name-suggestion and label-lookup helpers for diagnostics
//! (edit-distance suggestions, rule/label resolution).

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

const LabelIndexMap = @import("./types.zig").LabelIndexMap;
const ApplicationDiagnosticContext = @import("./types.zig").ApplicationDiagnosticContext;

pub fn findSearchPlaceholder(application: RuleApplication) ?RuleApplication {
    if (ProofScript.isSearchPlaceholderRuleName(application.rule_name)) {
        return application;
    }
    for (application.refs) |ref| switch (ref) {
        .application => |child| {
            if (findSearchPlaceholder(child)) |found| return found;
        },
        .hyp, .line => {},
    };
    return null;
}

/// Bounded Levenshtein distance: returns null when the distance exceeds
/// `max`. Used only on failed name lookups, so the quadratic cost is paid
/// once per diagnostic.
fn editDistanceAtMost(a: []const u8, b: []const u8, max: usize) ?usize {
    const larger = @max(a.len, b.len);
    const smaller = @min(a.len, b.len);
    if (larger - smaller > max) return null;
    if (larger > 64) return null;
    var prev: [65]usize = undefined;
    var curr: [65]usize = undefined;
    for (0..b.len + 1) |j| prev[j] = j;
    for (a[0..a.len], 0..) |ca, i| {
        curr[0] = i + 1;
        var row_min = curr[0];
        for (b[0..b.len], 0..) |cb, j| {
            const cost: usize = if (ca == cb) 0 else 1;
            curr[j + 1] = @min(
                @min(curr[j] + 1, prev[j + 1] + 1),
                prev[j] + cost,
            );
            row_min = @min(row_min, curr[j + 1]);
        }
        if (row_min > max) return null;
        @memcpy(prev[0 .. b.len + 1], curr[0 .. b.len + 1]);
    }
    if (prev[b.len] > max) return null;
    return prev[b.len];
}

fn suggestionThreshold(name_len: usize) usize {
    return if (name_len >= 5) 2 else 1;
}

/// Deterministically pick the known name closest to `name`: smallest edit
/// distance wins, lexicographic order breaks ties (hash-map iteration
/// order must not leak into diagnostics).
fn considerSuggestion(
    name: []const u8,
    candidate: []const u8,
    best: *?[]const u8,
    best_dist: *usize,
) void {
    const max = suggestionThreshold(name.len);
    const dist = editDistanceAtMost(name, candidate, max) orelse return;
    if (dist == 0) return;
    if (dist < best_dist.* or
        (dist == best_dist.* and best.* != null and
            std.mem.order(u8, candidate, best.*.?) == .lt))
    {
        best.* = candidate;
        best_dist.* = dist;
    }
}

/// The closest name in `map`'s keys to `name`, or null when nothing is
/// close enough. `map` is any string-keyed map — the rule table or a
/// block's label index.
pub fn closestKeyName(map: anytype, name: []const u8) ?[]const u8 {
    var best: ?[]const u8 = null;
    var best_dist: usize = std.math.maxInt(usize);
    var it = map.keyIterator();
    while (it.next()) |key| {
        considerSuggestion(name, key.*, &best, &best_dist);
    }
    return best;
}

pub fn labelAppearsInBlock(
    block_lines: []const ProofScript.ProofLine,
    name: []const u8,
) bool {
    for (block_lines) |line| {
        if (std.mem.eql(u8, line.label, name)) return true;
    }
    return false;
}

pub fn lookupRuleApplicationId(
    self: *CompilerContext,
    env: *const GlobalEnv,
    rule_catalog: *const RuleCatalog.Catalog,
    labels: *const LabelIndexMap,
    diag_context: ApplicationDiagnosticContext,
    application: RuleApplication,
) !u32 {
    if (env.getRuleId(application.rule_name)) |rule_id| return rule_id;

    if (rule_catalog.get(application.rule_name)) |entry| {
        if (entry.ordinal >= env.rules.items.len) {
            var diag: Diagnostic = .{
                .kind = .rule_not_yet_available,
                .err = error.RuleNotYetAvailable,
                .theorem_name = diag_context.theorem_name,
                .line_label = diag_context.line_label,
                .rule_name = application.rule_name,
                .span = application.rule_span,
            };
            CompilerDiag.setPhase(&diag, .theorem_application);
            CompilerDiag.addNote(&diag, .rule_declared_later, .mm0, null);
            CompilerDiag.addRelated(
                &diag,
                .rule_declaration_here,
                .mm0,
                entry.name_span,
            );
            self.setProof(diag);
            return error.RuleNotYetAvailable;
        }
    }

    var diag = CompilerDiag.withPhase(.{
        .kind = .unknown_rule,
        .err = error.UnknownRule,
        .theorem_name = diag_context.theorem_name,
        .line_label = diag_context.line_label,
        .rule_name = application.rule_name,
        .span = application.rule_span,
    }, .theorem_application);
    if (env.term_names.get(application.rule_name) != null) {
        CompilerDiag.addNote(&diag, .name_is_term_not_rule, .proof, null);
    } else if (labels.contains(application.rule_name)) {
        CompilerDiag.addNote(&diag, .name_is_label_not_rule, .proof, null);
    } else if (closestKeyName(
        &env.rule_names,
        application.rule_name,
    )) |suggestion| {
        diag.detail = .{ .name_suggestion = .{ .suggestion = suggestion } };
    }
    self.setProof(diag);
    return error.UnknownRule;
}
