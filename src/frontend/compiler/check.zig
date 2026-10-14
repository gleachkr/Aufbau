//! Theorem-block checking facade. The driver (`checkTheoremBlock`) lives
//! here; the application core, binding inference, hint flow, and their
//! supporting types live in the `check/` submodules and are re-exported
//! where they form the public checking API.

const std = @import("std");
const ExprId = @import("../expr.zig").ExprId;
const TheoremContext = @import("../expr.zig").TheoremContext;
const GlobalEnv = @import("../env.zig").GlobalEnv;
const AssertionStmt = @import("../parse_recovery.zig").AssertionStmt;
const MM0Parser = @import("../parse_recovery.zig").MM0Parser;
const ExprModule = @import("../../trusted/expressions.zig");
const Expr = ExprModule.Expr;
const ProofScript = @import("../proof_script.zig");
const ProofLine = ProofScript.ProofLine;
const Span = ProofScript.Span;
const TheoremBlock = @import("../proof_script.zig").TheoremBlock;
const CompilerDiag = @import("../diag.zig");
const CompilerContext = @import("./context.zig").CompilerContext;
const KeepChecking = @import("./context.zig").KeepChecking;
const HoleInferenceSink = @import("./context.zig").HoleInferenceSink;
const ViewTrace = @import("../view_trace.zig");
const DebugTrace = @import("../debug.zig");
const CheckedIr = @import("../checked_ir.zig");
const CheckedLine = CheckedIr.CheckedLine;
const Inference = @import("./inference.zig");
const Matching = @import("./check/matching.zig");
const DiagNotes = @import("./check/diag_notes.zig");
const TheoryState = @import("./theory_state.zig").TheoryState;
const CompilerVars = @import("./vars.zig");
const SortVarRegistry = CompilerVars.SortVarRegistry;
const Holes = @import("./holes.zig");
const addBoundaryAttemptNotes = DiagNotes.addBoundaryAttemptNotes;

pub const NameExprMap = @import("./check/types.zig").NameExprMap;
pub const LabelIndexMap = @import("./check/types.zig").LabelIndexMap;
pub const UnresolvedHypothesis = @import("./check/types.zig").UnresolvedHypothesis;
pub const ConclusionProbe = @import("./check/types.zig").ConclusionProbe;
pub const RefExpectationProbe = @import("./check/types.zig").RefExpectationProbe;
pub const LineAssertion = @import("./check/types.zig").LineAssertion;
pub const HoleyLine = Holes.HoleyLine;
pub const ApplicationDiagnosticContext = @import("./check/types.zig").ApplicationDiagnosticContext;
pub const ApplicationLine = @import("./check/types.zig").ApplicationLine;
pub const RuleApplyContext = @import("./check/types.zig").RuleApplyContext;
pub const applyRuleApplication = @import("./check/apply.zig").applyRuleApplication;
pub const probeRuleConclusion = @import("./check/apply.zig").probeRuleConclusion;
pub const probeExpectedRefsForApplication = @import("./check/apply.zig").probeExpectedRefsForApplication;
pub const buildTheoremVarMap = @import("./check/types.zig").buildTheoremVarMap;
pub const cloneNameExprMap = @import("./check/types.zig").cloneNameExprMap;

const ensureConcreteCheckedIrRange = @import("./check/checked_range.zig").ensureConcreteCheckedIrRange;
const findSearchPlaceholder = @import("./check/suggest.zig").findSearchPlaceholder;

/// `checkTheoremBlock` behind the context's check memo, when one is
/// attached (`CompilerContext.check_memo`): a hit replays the recorded
/// outcome and output instead of checking again. A hit yields no checked
/// lines, so paths that emit (the compile path) must call
/// `checkTheoremBlock` directly.
pub fn checkTheoremBlockMemoized(
    self: *CompilerContext,
    allocator: std.mem.Allocator,
    theory: *TheoryState,
    assertion: AssertionStmt,
    block: TheoremBlock,
    theorem: *TheoremContext,
    theorem_concl: ExprId,
) ![]const CheckedLine {
    const memo = self.check_memo orelse return checkTheoremBlock(
        self,
        allocator,
        theory,
        assertion,
        block,
        theorem,
        theorem_concl,
    );
    if (!memo.active) {
        return checkTheoremBlock(
            self,
            allocator,
            theory,
            assertion,
            block,
            theorem,
            theorem_concl,
        );
    }
    const mm0_pos = theory.parser.core.pos;
    const key = memo.keyForBlock(self.source, mm0_pos, self.proof_source.?, block);
    if (memo.find(key, &theory.rule_catalog)) |entry| {
        try entry.replay(self, block.span.start);
        if (entry.outcome) |err| return err;
        return &.{};
    }
    const recording = memo.beginRecording(self);
    const checked = checkTheoremBlock(
        self,
        allocator,
        theory,
        assertion,
        block,
        theorem,
        theorem_concl,
    ) catch |err| {
        memo.finishRecording(self, recording, key, err, block.span);
        return err;
    };
    memo.finishRecording(self, recording, key, null, block.span);
    return checked;
}

pub fn checkTheoremBlock(
    self: *CompilerContext,
    allocator: std.mem.Allocator,
    theory: *TheoryState,
    assertion: AssertionStmt,
    block: TheoremBlock,
    theorem: *TheoremContext,
    theorem_concl: ExprId,
) ![]const CheckedLine {
    var walk = try LineWalk.init(self, allocator, theory, assertion, block.lines, theorem);
    defer walk.deinit();

    const stopped = for (block.lines) |line| {
        if (try walk.step(line) == .stop) break true;
    } else false;
    // The block ends on an unfinished line: there is no final statement to
    // reconcile with the conclusion yet.
    if (!stopped and !walk.ends_unfinished) {
        walk.reconcileFinalLine(block, theorem_concl) catch |err| {
            if (err != error.OutOfMemory) walk.reportHeldFailure();
            return err;
        };
    }
    try walk.raiseHeldFailure();
    return try walk.checked.toOwnedSlice(allocator);
}

/// The line half of `checkTheoremBlock`: `step` admits or checks one line
/// and adds it to the label environment. The search replays the lines
/// before its target through the same walk, so it plans against the context
/// the checker builds. The walk owns its state; `checked` may be moved out
/// with `toOwnedSlice` before `deinit`.
pub const LineWalk = struct {
    compiler: *CompilerContext,
    allocator: std.mem.Allocator,
    theory: *TheoryState,
    assertion: AssertionStmt,
    /// Every line of the block, for the unknown-label diagnostic.
    block_lines: []const ProofLine,
    theorem: *TheoremContext,
    theorem_vars: NameExprMap,
    labels: LabelIndexMap,
    checked: std.ArrayListUnmanaged(CheckedLine) = .empty,
    rule_unify_cache: Inference.RuleUnifyCache,
    diag_scratch: CompilerDiag.Scratch,
    /// Analysis only: lines with no statement to admit. A placeholder line
    /// whose assertion has holes is unfinished, and so is a holey line that
    /// cites one.
    unfinished: std.ArrayListUnmanaged([]const u8) = .empty,
    /// The last line with a statement, which the final reconciliation
    /// relates to the conclusion.
    last: ?LastLine = null,
    /// The last line walked was unfinished.
    ends_unfinished: bool = false,
    /// With `CompilerContext.keep_checking`: the latest failed line's
    /// diagnostic. It is held back so the theorem's own failure carries it;
    /// an earlier one is reported when a later line fails.
    failure: ?CompilerDiag.Diagnostic = null,

    pub const LastLine = struct {
        expr: ExprId,
        idx: usize,
        label: []const u8,
        span: Span,
    };

    pub const Next = enum {
        next,
        /// An incomplete line the analysis tolerates: the walk ends here and
        /// the lines checked so far stand, as if the block ended.
        stop,
    };

    pub fn init(
        compiler: *CompilerContext,
        allocator: std.mem.Allocator,
        theory: *TheoryState,
        assertion: AssertionStmt,
        block_lines: []const ProofLine,
        theorem: *TheoremContext,
    ) !LineWalk {
        return .{
            .compiler = compiler,
            .allocator = allocator,
            .theory = theory,
            .assertion = assertion,
            .block_lines = block_lines,
            .theorem = theorem,
            .theorem_vars = try buildTheoremVarMap(allocator, assertion),
            .labels = LabelIndexMap.init(allocator),
            .rule_unify_cache = Inference.RuleUnifyCache.init(allocator),
            .diag_scratch = CompilerDiag.Scratch.init(allocator),
        };
    }

    pub fn deinit(self: *LineWalk) void {
        CheckedIr.deinitLines(self.allocator, self.checked.items);
        self.checked.deinit(self.allocator);
        self.unfinished.deinit(self.allocator);
        self.diag_scratch.deinit();
        self.rule_unify_cache.deinit();
        self.labels.deinit();
        self.theorem_vars.deinit();
        self.* = undefined;
    }

    /// Check `line`. With `CompilerContext.keep_checking`, a line that fails
    /// is reported and its statement taken as written, so the walk goes on.
    pub fn step(self: *LineWalk, line: ProofLine) !Next {
        const checked_mark = self.checked.items.len;
        return self.checkLine(line) catch |err| {
            if (err == error.OutOfMemory) return err;
            // A failure the checks left undiagnosed still belongs to this
            // line, not to the theorem as a whole.
            if (self.compiler.getDiagnostic() == null) {
                self.compiler.setProof(.{
                    .kind = .generic,
                    .err = CompilerDiag.narrowDiagnosticError(err),
                    .theorem_name = self.assertion.name,
                    .line_label = line.label,
                    .rule_name = line.application.rule_name,
                    .span = line.ruleApplicationSpan(),
                });
            }
            const keep = self.compiler.keep_checking orelse return err;
            try self.admitFailedLine(keep, line, checked_mark);
            return .next;
        };
    }

    fn checkLine(self: *LineWalk, line: ProofLine) !Next {
        const compiler = self.compiler;
        const allocator = self.allocator;
        const assertion = self.assertion;
        // A line the lenient parse could not finish. Only the analyze path
        // parses leniently: report the recorded parse failure and keep the
        // lines checked so far, exactly as if the block ended here, so a
        // half-typed line leaves the theorem usable. The line contributes
        // nothing to the label environment and can never reach emission —
        // the compile path parses strictly and errors out instead.
        if (line.incomplete) {
            compiler.addPrimaryDiagnostic(CompilerDiag.incompleteProofLineDiagnostic(
                assertion.name,
                line,
            ));
            return .stop;
        }

        const has_placeholder =
            ProofScript.applicationHasSearchPlaceholder(line.application);
        if (has_placeholder and !compiler.allow_search_placeholders) {
            const placeholder =
                findSearchPlaceholder(line.application) orelse line.application;
            var diag = CompilerDiag.withPhase(.{
                .kind = .unresolved_search_placeholder,
                .err = error.UnknownRule,
                .theorem_name = assertion.name,
                .line_label = line.label,
                .rule_name = placeholder.rule_name,
                .span = placeholder.rule_span,
            }, .theorem_application);
            CompilerDiag.addNote(&diag, .search_placeholder_meaning, .proof, null);
            CompilerDiag.addNote(
                &diag,
                .search_placeholder_unfinished,
                .proof,
                null,
            );
            compiler.setProof(diag);
            return error.UnknownRule;
        }

        if (self.labels.contains(line.label) or
            ProofScript.containsLabel(self.unfinished.items, line.label))
        {
            compiler.setProof(CompilerDiag.withPhase(.{
                .kind = .duplicate_label,
                .err = error.DuplicateLabel,
                .theorem_name = assertion.name,
                .line_label = line.label,
                .name = line.label,
                .span = line.label_span,
            }, .theorem_application));
            return error.DuplicateLabel;
        }

        const parsed_assertion = try parseProofLineAssertion(
            compiler,
            &self.theory.parser,
            self.theorem,
            &self.theorem_vars,
            &self.theory.sort_vars,
            assertion,
            line,
        );
        const line_assertion = try LineAssertion.fromParsed(
            self.theorem,
            &self.theory.env,
            parsed_assertion,
        );

        // Analysis checks past a search placeholder: the line is admitted
        // like `sorry!` when its assertion is concrete, so later lines can
        // cite it. A line citing an unfinished line (a placeholder, or a
        // failed line that states nothing) is admitted the same way and
        // warned about. The compile path rejected placeholders above.
        if (compiler.allow_search_placeholders or compiler.keep_checking != null) {
            const cited = ProofScript.findLineRef(
                line.application,
                self.unfinished.items,
            );
            if (cited) |ref| {
                compiler.addWarning(.{
                    .kind = .cites_unfinished_line,
                    .err = error.CitesUnfinishedLine,
                    .source = .proof,
                    .theorem_name = assertion.name,
                    .line_label = line.label,
                    .name = ref.label,
                    .span = ref.span,
                });
            }
            if (has_placeholder or cited != null) {
                switch (parsed_assertion) {
                    .concrete => |expr| {
                        try self.admit(line, try CheckedIr.appendSorryLine(
                            &self.checked,
                            allocator,
                            expr,
                        ));
                    },
                    .holey => {
                        try self.unfinished.append(allocator, line.label);
                        self.ends_unfinished = true;
                    },
                }
                return .next;
            }
        }

        if (ProofScript.isSorryRuleName(line.application.rule_name)) {
            try self.admit(line, try admitSorryLine(
                compiler,
                allocator,
                &self.checked,
                assertion,
                line,
                parsed_assertion,
            ));
            return .next;
        }

        const apply_context: RuleApplyContext = .{
            .allocator = allocator,
            .parser = &self.theory.parser,
            .env = &self.theory.env,
            .registry = &self.theory.registry,
            .rule_catalog = &self.theory.rule_catalog,
            .fresh_bindings = &self.theory.fresh_bindings,
            .freshen_bindings = &self.theory.freshen_bindings,
            .views = &self.theory.views,
            .sort_vars = &self.theory.sort_vars,
            .assertion = assertion,
            .labels = &self.labels,
            .block_lines = self.block_lines,
            .checked = &self.checked,
            .diag_scratch = &self.diag_scratch,
            .rule_unify_cache = &self.rule_unify_cache,
        };
        const checked_mark = self.checked.items.len;
        const line_idx = try applyRuleApplication(
            compiler,
            &apply_context,
            line.application,
            line_assertion,
            null,
            ApplicationDiagnosticContext.fromLine(assertion, line),
            ApplicationLine.fromLine(line),
            self.theorem,
            &self.theorem_vars,
        );

        if (parsed_assertion == .holey) {
            try collectHoleInferences(
                compiler,
                &apply_context,
                checked_mark,
                self.theorem,
                &self.theorem_vars,
                line,
                parsed_assertion.holey,
                self.checked.items[line_idx].expr,
            );
        }

        try self.admit(line, line_idx);
        return .next;
    }

    /// `line`'s statement is `checked[line_idx]`: later lines may cite it.
    fn admit(self: *LineWalk, line: ProofLine, line_idx: usize) !void {
        try self.labels.put(line.label, line_idx);
        self.last = .{
            .expr = self.checked.items[line_idx].expr,
            .idx = line_idx,
            .label = line.label,
            .span = line.span,
        };
        self.ends_unfinished = false;
    }

    /// `line` failed: hold its diagnostic, and let later lines cite the
    /// statement it states. A statement that does not parse or has holes
    /// leaves the line unfinished, like a placeholder line in analysis.
    fn admitFailedLine(
        self: *LineWalk,
        keep: KeepChecking,
        line: ProofLine,
        checked_mark: usize,
    ) !void {
        const compiler = self.compiler;
        // Lines an inline application added before the line failed.
        CheckedIr.deinitLines(self.allocator, self.checked.items[checked_mark..]);
        self.checked.shrinkRetainingCapacity(checked_mark);

        const diag = compiler.getDiagnostic().?;
        compiler.restoreDiagnostic(null);
        if (self.failure) |previous| {
            if (keep.reports(previous)) compiler.addPrimaryDiagnostic(previous);
        }
        self.failure = diag;

        // Unfinished unless its statement is admitted below. A repeated
        // label keeps its first line.
        self.ends_unfinished = true;
        if (self.labels.contains(line.label) or
            ProofScript.containsLabel(self.unfinished.items, line.label))
        {
            return;
        }
        const parsed = Holes.parseAssertion(
            &self.theory.parser,
            self.theorem,
            &self.theorem_vars,
            &self.theory.sort_vars,
            line.assertion.text,
        ) catch |parse_err| switch (parse_err) {
            error.OutOfMemory => return parse_err,
            else => null,
        };
        if (parsed) |assertion| switch (assertion) {
            .concrete => |expr| {
                const line_idx = try CheckedIr.appendSorryLine(
                    &self.checked,
                    self.allocator,
                    expr,
                );
                return self.admit(line, line_idx);
            },
            .holey => {},
        };
        try self.unfinished.append(self.allocator, line.label);
    }

    /// Report the held line failure, if any, as one of the theorem's errors.
    pub fn reportHeldFailure(self: *LineWalk) void {
        const failure = self.failure orelse return;
        self.failure = null;
        const keep = self.compiler.keep_checking.?;
        if (keep.reports(failure)) self.compiler.addPrimaryDiagnostic(failure);
    }

    /// Fail with the held line failure, if any: the theorem's diagnostic.
    pub fn raiseHeldFailure(self: *LineWalk) !void {
        const failure = self.failure orelse return;
        self.failure = null;
        self.compiler.restoreDiagnostic(failure);
        return failure.err;
    }

    /// Relate the last line's statement to the theorem's conclusion.
    pub fn reconcileFinalLine(
        self: *LineWalk,
        block: TheoremBlock,
        theorem_concl: ExprId,
    ) !void {
        const compiler = self.compiler;
        const allocator = self.allocator;
        const assertion = self.assertion;
        const theorem = self.theorem;
        const parser = &self.theory.parser;
        const env: *const GlobalEnv = &self.theory.env;
        const registry = &self.theory.registry;
        const sort_vars: *const SortVarRegistry = &self.theory.sort_vars;
        const theorem_vars = &self.theorem_vars;
        const checked = &self.checked;
        const diag_scratch = &self.diag_scratch;
        const final = self.last orelse {
            compiler.setProof(CompilerDiag.withPhase(.{
                .kind = .empty_proof_block,
                .err = error.EmptyProofBlock,
                .theorem_name = assertion.name,
                .block_name = block.name,
                .span = block.name_span,
            }, .final_reconciliation));
            return error.EmptyProofBlock;
        };
        if (final.expr != theorem_concl) {
            const final_mark = diag_scratch.mark();
            const checked_mark = checked.items.len;
            DebugTrace.traceBoundary(
                compiler.debug,
                "reconciling the final line with the theorem conclusion",
                .{},
            );
            if ((Matching.convertTo(.{
                .allocator = allocator,
                .theorem = theorem,
                .registry = registry,
                .env = env,
                .checked = checked,
                .scratch = diag_scratch,
                .debug = compiler.debug,
                .fresh = .{
                    .parser = parser,
                    .theorem_vars = theorem_vars,
                    .sort_vars = sort_vars,
                },
            }, .{ .ref = .{ .line = final.idx } }, final.expr, theorem_concl) catch |err| {
                if (CompilerDiag.takeScratchDetail(
                    diag_scratch,
                    final_mark,
                    env,
                    err,
                )) |detail| {
                    self.setFinalLineFailure(
                        final,
                        theorem_concl,
                        .generic,
                        CompilerDiag.narrowDiagnosticError(err),
                        detail,
                    );
                    return err;
                }
                diag_scratch.discard(final_mark);
                return err;
            }) != null) {
                diag_scratch.discard(final_mark);
                try ensureConcreteCheckedIrRange(
                    compiler,
                    env,
                    theorem,
                    parser,
                    theorem_vars,
                    assertion.name,
                    checked.items[checked_mark..],
                    final.label,
                    final.span,
                    .final_reconciliation,
                );
                return;
            }
            diag_scratch.discard(final_mark);
            DebugTrace.traceBoundary(
                compiler.debug,
                "no conversion relates the final line to the conclusion",
                .{},
            );
            self.setFinalLineFailure(
                final,
                theorem_concl,
                .final_line_mismatch,
                error.FinalLineMismatch,
                .none,
            );
            return error.FinalLineMismatch;
        }
    }

    /// Report the final line's failure to reach the conclusion, with notes
    /// on how the two were compared.
    fn setFinalLineFailure(
        self: *LineWalk,
        final: LastLine,
        theorem_concl: ExprId,
        kind: CompilerDiag.DiagnosticKind,
        err: CompilerDiag.DiagnosticError,
        detail: CompilerDiag.DiagnosticDetail,
    ) void {
        var diag = CompilerDiag.withPhase(.{
            .kind = kind,
            .err = err,
            .theorem_name = self.assertion.name,
            .line_label = final.label,
            .span = final.span,
            .detail = detail,
        }, .final_reconciliation);
        addBoundaryAttemptNotes(
            self.allocator,
            &diag,
            self.theorem,
            &self.theory.env,
            &self.theory.parser,
            &self.theorem_vars,
            theorem_concl,
            final.expr,
        );
        self.compiler.setProof(diag);
    }
};

fn collectHoleInferences(
    self: *CompilerContext,
    apply_context: *const RuleApplyContext,
    checked_mark: usize,
    theorem: *TheoremContext,
    theorem_vars: *const NameExprMap,
    line: ProofLine,
    surface: *const Expr,
    checked_line: ExprId,
) !void {
    const sink = self.hole_inference_sink orelse return;
    const allocator = apply_context.allocator;
    const parser = apply_context.parser;
    const env = apply_context.env;
    // Report the line as written with its holes filled. The checked line can
    // differ in shape: it unfolds a definition the line keeps folded
    // (`_wff -> c e. img f B` checks as `... sep x B (R f x)`). Keep the
    // checked line when the filled one is not the same up to unfolding.
    const fill = Holes.fillThroughDefs(
        parser,
        theorem,
        env,
        surface,
        checked_line,
    ) catch |err| switch (err) {
        error.OutOfMemory => return err,
        // Editor-only display: a failed fill must not fail the check.
        else => null,
    };
    const concrete = fill orelse checked_line;
    var names = try ViewTrace.DiagNames.build(
        allocator,
        theorem,
        parser,
        theorem_vars,
    );
    defer names.deinit(allocator);
    try collectHoleInferencesRecursive(
        sink,
        theorem,
        env,
        &names,
        line.assertion.span.start + 1,
        surface,
        concrete,
    );
    const filled = try ViewTrace.formatExprSource(
        sink.allocator,
        theorem,
        env,
        &names,
        concrete,
    ) orelse return;
    // Offer the filled line only if it checks as written: a holey line can
    // check where its filled form does not (a rewrite the concrete path
    // needs a congruence for, or a print that does not parse back).
    const checks = filledLineChecks(
        self,
        apply_context,
        checked_mark,
        theorem,
        theorem_vars,
        line,
        filled,
    ) catch |err| {
        sink.allocator.free(filled);
        return err;
    };
    if (!checks) {
        sink.allocator.free(filled);
        return;
    }
    try sink.addAssertionOwned(line.span, line.assertion.span, filled);
}

/// Whether `line` checks with the assertion `text` against the lines checked
/// before it (`apply_context.checked` up to `checked_mark`). Runs on clones
/// and leaves the diagnostics and sinks as they were.
fn filledLineChecks(
    self: *CompilerContext,
    apply_context: *const RuleApplyContext,
    checked_mark: usize,
    theorem: *const TheoremContext,
    theorem_vars: *const NameExprMap,
    line: ProofLine,
    text: []const u8,
) !bool {
    const allocator = apply_context.allocator;
    var probe_theorem = try theorem.clone();
    defer probe_theorem.deinit();
    var probe_vars = try cloneNameExprMap(allocator, theorem_vars);
    defer probe_vars.deinit();

    const saved_diag = self.getDiagnostic();
    defer self.restoreDiagnostic(saved_diag);
    const diag_mark = apply_context.diag_scratch.mark();
    defer apply_context.diag_scratch.discard(diag_mark);
    const inline_mark = if (self.inline_conclusion_sink) |sink| sink.mark() else 0;
    defer if (self.inline_conclusion_sink) |sink| sink.rollback(inline_mark);

    const parsed = Holes.parseAssertion(
        apply_context.parser,
        &probe_theorem,
        &probe_vars,
        apply_context.sort_vars,
        text,
    ) catch |err| switch (err) {
        error.OutOfMemory => return err,
        else => return false,
    };
    if (parsed == .holey) return false;

    var scratch: std.ArrayListUnmanaged(CheckedLine) = .empty;
    defer {
        CheckedIr.rollbackToMark(allocator, &scratch, checked_mark);
        scratch.deinit(allocator);
    }
    try scratch.appendSlice(allocator, apply_context.checked.items[0..checked_mark]);
    var probe_context = apply_context.*;
    probe_context.checked = &scratch;
    _ = applyRuleApplication(
        self,
        &probe_context,
        line.application,
        .{ .concrete = parsed.concrete },
        null,
        ApplicationDiagnosticContext.fromLine(apply_context.assertion, line),
        ApplicationLine.fromLine(line),
        &probe_theorem,
        &probe_vars,
    ) catch |err| switch (err) {
        error.OutOfMemory => return err,
        else => return false,
    };
    CheckedIr.validateLinesCached(&probe_theorem, scratch.items[checked_mark..]) catch
        return false;
    return true;
}

fn collectHoleInferencesRecursive(
    sink: *HoleInferenceSink,
    theorem: *const TheoremContext,
    env: *const GlobalEnv,
    names: *const ViewTrace.DiagNames,
    math_start: usize,
    surface: *const Expr,
    concrete: ExprId,
) !void {
    switch (surface.*) {
        .hole => |hole| {
            const token_span = hole.token_span orelse return;
            const expression = try ViewTrace.formatExprNamed(
                sink.allocator,
                theorem,
                env,
                names,
                concrete,
            );
            try sink.addOwned(
                .{
                    .start = math_start + token_span.start,
                    .end = math_start + token_span.end,
                },
                expression,
            );
        },
        .variable => {},
        .term => |surface_app| {
            const concrete_app = switch (theorem.interner.node(concrete).*) {
                .app => |app| app,
                else => return,
            };
            if (surface_app.id != concrete_app.term_id or
                surface_app.args.len != concrete_app.args.len)
            {
                return;
            }
            for (surface_app.args, concrete_app.args) |
                surface_arg,
                concrete_arg,
            | {
                if (!Holes.contains(surface_arg)) continue;
                try collectHoleInferencesRecursive(
                    sink,
                    theorem,
                    env,
                    names,
                    math_start,
                    surface_arg,
                    concrete_arg,
                );
            }
        },
    }
}

/// `by sorry!`: admit the stated goal with no rule. The line joins the
/// checked IR as a `.sorry` line, so later references and the final
/// conclusion check see it like any other, and a warning marks the theorem
/// as not verified. The goal must be concrete and the application bare: a
/// sorry has nothing to infer a hole from and no hypotheses to discharge.
fn admitSorryLine(
    self: *CompilerContext,
    allocator: std.mem.Allocator,
    checked: *std.ArrayListUnmanaged(CheckedLine),
    assertion: AssertionStmt,
    line: ProofLine,
    parsed_assertion: Holes.ParsedAssertion,
) !usize {
    const app = line.application;
    const goal: ?ExprId = switch (parsed_assertion) {
        .concrete => |expr_id| expr_id,
        .holey => null,
    };
    if (goal == null or app.arg_bindings.len != 0 or
        app.search_params.len != 0 or app.refs.len != 0)
    {
        self.setProof(CompilerDiag.withPhase(.{
            .kind = .sorry_line_arguments,
            .err = error.SorryLineArguments,
            .theorem_name = assertion.name,
            .line_label = line.label,
            .rule_name = app.rule_name,
            .span = if (goal == null) line.assertion.span else app.span,
        }, .theorem_application));
        return error.SorryLineArguments;
    }
    const line_idx = try CheckedIr.appendSorryLine(checked, allocator, goal.?);
    self.addWarning(.{
        .kind = .sorry_line,
        .err = error.SorryLine,
        .source = .proof,
        .theorem_name = assertion.name,
        .line_label = line.label,
        .rule_name = app.rule_name,
        .span = app.rule_span,
    });
    return line_idx;
}

fn parseProofLineAssertion(
    self: *CompilerContext,
    parser: *MM0Parser,
    theorem: *TheoremContext,
    theorem_vars: *NameExprMap,
    sort_vars: *const SortVarRegistry,
    assertion: AssertionStmt,
    line: ProofLine,
) !Holes.ParsedAssertion {
    return Holes.parseAssertion(
        parser,
        theorem,
        theorem_vars,
        sort_vars,
        line.assertion.text,
    ) catch |err| {
        var diag = CompilerDiag.proofMathParseDiagnostic(
            parser,
            .parse_assertion,
            err,
            assertion.name,
            line.label,
            line.application.rule_name,
            null,
            line.assertion.span,
        );
        DiagNotes.attachSortRetryNote(
            &diag,
            parser,
            theorem_vars,
            null,
            line.assertion.text,
        );
        self.setProof(diag);
        return err;
    };
}
