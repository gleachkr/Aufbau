//! Theorem-block checking facade. The driver (`checkTheoremBlock`) lives
//! here; the application core, binding inference, hint flow, and their
//! supporting types live in the `check/` submodules and are re-exported
//! where they form the public checking API.

const std = @import("std");
const ExprId = @import("../expr.zig").ExprId;
const PlaceholderId = @import("../expr.zig").PlaceholderId;
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
const OpenGoals = @import("./check/open_goals.zig");
const NamedUnknowns = @import("./check/unknowns.zig");
const UnknownsSolve = @import("./check/unknowns_solve.zig");
const Apply = @import("./check/apply.zig");
const Idents = @import("../idents.zig");
const RuleDecl = @import("../env.zig").RuleDecl;

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
    try walk.solveUnknowns(theorem_concl);
    errdefer walk.reportHeldGoals(false) catch {};

    const stopped = for (block.lines) |line| {
        if (try walk.step(line) == .stop) break true;
    } else false;
    try walk.hoverUnknowns();
    try walk.reportHeldGoals(true);
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
    /// Analysis only: what the current line's check learned about its open
    /// goals, reported once the line is done (`reportOpenGoals`).
    open_goals: OpenGoals.Records = .empty,
    /// The open-goal reports of the lines walked so far, held to the end
    /// of the block when it may name unknowns: a later line can still fix
    /// a name a goal shows (`reportHeldGoals`).
    held_goals: std.ArrayListUnmanaged(HeldGoals) = .empty,
    hold_goals: bool = false,
    /// Named unknowns the lines checked so far have bound.
    unknowns: NamedUnknowns.Unknowns = .{},
    /// The hole sink's length when the block began (`hoverUnknowns`).
    hover_from: usize = 0,
    /// The last line with a statement, which the final reconciliation
    /// relates to the conclusion.
    last: ?LastLine = null,
    /// The last line walked was unfinished.
    ends_unfinished: bool = false,
    /// With `CompilerContext.keep_checking`: the latest failed line's
    /// diagnostic. It is held back so the theorem's own failure carries it;
    /// an earlier one is reported when a later line fails.
    failure: ?CompilerDiag.Diagnostic = null,

    const HeldGoals = struct {
        line: ProofLine,
        records: []const OpenGoals.Record,
    };

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
        self.open_goals.deinit(self.allocator);
        for (self.held_goals.items) |held| self.allocator.free(held.records);
        self.held_goals.deinit(self.allocator);
        self.unknowns.deinit(self.allocator);
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
        self.open_goals.clearRetainingCapacity();
        const next = self.checkLine(line) catch |err| {
            if (err == error.OutOfMemory) return err;
            // A step still to be proved (an open goal whose goal is not yet
            // known) stops the line's check without failing it: the line
            // stands as written.
            if (err == error.UnfinishedLine) {
                try self.admitUnfinishedLine(line, checked_mark);
                return .next;
            }
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
            try self.reportOpenGoals(line);
            const keep = self.compiler.keep_checking orelse return err;
            try self.admitFailedLine(keep, line, checked_mark);
            return .next;
        };
        try self.reportOpenGoals(line);
        return next;
    }

    /// Report each open goal in `line` once, with what its check learned of
    /// it. A compile refuses the first open goal instead (`checkLine`).
    fn reportOpenGoals(self: *LineWalk, line: ProofLine) !void {
        if (line.incomplete or !OpenGoals.admitted(self.compiler)) return;
        if (self.hold_goals) {
            const records = try self.allocator.dupe(OpenGoals.Record, self.open_goals.items);
            errdefer self.allocator.free(records);
            try self.held_goals.append(self.allocator, .{ .line = line, .records = records });
            return;
        }
        OpenGoals.reportLine(
            self.compiler,
            self.assertion.name,
            line.label,
            line.application,
            self.open_goals.items,
        );
    }

    /// Report the held open goals, in source order. With `rewrite`, a line
    /// `?` whose statement names unknowns shows what the block fixed of
    /// them: values, partial shapes, and the names still open.
    pub fn reportHeldGoals(self: *LineWalk, rewrite: bool) !void {
        defer {
            for (self.held_goals.items) |held| self.allocator.free(held.records);
            self.held_goals.clearRetainingCapacity();
        }
        for (self.held_goals.items) |held| {
            var records = held.records;
            var extended: ?[]OpenGoals.Record = null;
            defer if (extended) |owned| self.allocator.free(owned);
            if (rewrite) if (try self.knownGoal(held.line)) |goal| {
                const owned = try self.allocator.alloc(OpenGoals.Record, records.len + 1);
                @memcpy(owned[0..records.len], records);
                owned[records.len] = .{ .at = held.line.application.rule_span.start, .goal = goal };
                extended = owned;
                records = owned;
            };
            OpenGoals.reportLine(
                self.compiler,
                self.assertion.name,
                held.line.label,
                held.line.application,
                records,
            );
        }
    }

    /// The goal of the line `?` on `line` with what is known of its named
    /// unknowns written in, or null when its statement as written stands.
    fn knownGoal(self: *LineWalk, line: ProofLine) !?[]const u8 {
        const app = line.application;
        if (!ProofScript.isOpenGoalRuleName(app.rule_name) or OpenGoals.hasBindings(app)) return null;
        const parsed = Holes.parseAssertion(
            &self.theory.parser,
            self.theorem,
            &self.theorem_vars,
            &self.theory.sort_vars,
            line.assertion.text,
        ) catch |err| switch (err) {
            error.OutOfMemory => return err,
            else => return null,
        };
        const surface = switch (parsed) {
            .concrete => return null,
            .holey => |surface| surface,
        };
        if (!NamedUnknowns.hasNamed(surface)) return null;
        var names: std.AutoHashMapUnmanaged(PlaceholderId, []const u8) = .empty;
        defer names.deinit(self.allocator);
        const goal = (try self.unknowns.writeKnown(
            self.allocator,
            self.theorem,
            &self.theory.env,
            surface,
            &names,
        )) orelse return null;
        return try OpenGoals.formatGoalNamed(
            self.allocator,
            self.theorem,
            &self.theory.env,
            &self.theory.parser,
            &self.theorem_vars,
            goal,
            &names,
        );
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
        // A compile has nothing to emit for an open goal. Analysis admits
        // it below and reports each one.
        if (!OpenGoals.admitted(compiler)) {
            if (ProofScript.isOpenGoalRuleName(line.application.rule_name) and
                OpenGoals.hasBindings(line.application))
            {
                return self.reportOpenGoalBindings(line);
            }
            if (ProofScript.findOpenGoal(line.application)) |marker| {
                compiler.setProof(OpenGoals.diagnostic(
                    assertion.name,
                    line.label,
                    marker,
                    null,
                ));
                return error.OpenGoal;
            }
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

        const parsed_assertion = try self.writeBoundUnknowns(try parseProofLineAssertion(
            compiler,
            &self.theory.parser,
            self.theorem,
            &self.theorem_vars,
            &self.theory.sort_vars,
            assertion,
            line,
        ));
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
            .open_goals = &self.open_goals,
            .unknowns = &self.unknowns,
        };
        if (ProofScript.isOpenGoalRuleName(line.application.rule_name)) {
            return try self.admitOpenGoalLine(&apply_context, line, parsed_assertion);
        }
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
            try self.recordUnknowns(
                line,
                parsed_assertion.holey,
                self.checked.items[line_idx].expr,
            );
        }
        try self.checkHoleyBindings(line, line.application, line_idx);

        try self.admit(line, line_idx);
        return .next;
    }

    /// Solve the block's named unknowns from all its lines before the walk
    /// (`unknowns_solve.zig`); `conclusion` is the theorem's, when the last
    /// line is to prove it.
    pub fn solveUnknowns(self: *LineWalk, conclusion: ?ExprId) !void {
        if (self.compiler.hole_inference_sink) |sink| self.hover_from = sink.items.items.len;
        self.hold_goals = UnknownsSolve.mayNameUnknowns(&self.theory.parser, self.block_lines);
        try UnknownsSolve.solve(.{
            .allocator = self.allocator,
            .theory = self.theory,
            .theorem = self.theorem,
            .theorem_vars = &self.theorem_vars,
            .lines = self.block_lines,
            .conclusion = conclusion,
        }, &self.unknowns);
    }

    /// `parsed` with the named unknowns earlier lines bound written as
    /// their values; concrete once no hole is left.
    pub fn writeBoundUnknowns(
        self: *LineWalk,
        parsed: Holes.ParsedAssertion,
    ) !Holes.ParsedAssertion {
        const surface = switch (parsed) {
            .concrete => return parsed,
            .holey => |surface| surface,
        };
        const written = try self.unknowns.substitute(
            self.allocator,
            self.theorem,
            &self.theory.parser,
            surface,
        );
        if (written == surface) return parsed;
        if (Holes.contains(written)) return .{ .holey = written };
        return .{ .concrete = try self.theorem.internParsedExpr(written) };
    }

    /// Once the lines are walked, a hover on each occurrence of a named
    /// unknown that has none yet: its value, or the shape the pre-pass
    /// forced on it ("partly inferred"). A line that filled a name itself
    /// already has the anonymous-hole hover there.
    pub fn hoverUnknowns(self: *LineWalk) !void {
        const sink = self.compiler.hole_inference_sink orelse return;
        if (self.unknowns.bound.count() == 0 and self.unknowns.partial.count() == 0) return;
        var names = try ViewTrace.DiagNames.build(
            self.allocator,
            self.theorem,
            &self.theory.parser,
            &self.theorem_vars,
        );
        defer names.deinit(self.allocator);
        for (self.block_lines) |line| {
            const parsed = Holes.parseAssertion(
                &self.theory.parser,
                self.theorem,
                &self.theorem_vars,
                &self.theory.sort_vars,
                line.assertion.text,
            ) catch |err| switch (err) {
                error.OutOfMemory => return err,
                else => continue,
            };
            switch (parsed) {
                .concrete => {},
                .holey => |surface| try self.hoverNames(sink, &names, line.assertion.span.start + 1, surface),
            }
            try self.hoverBindings(sink, &names, line.application);
        }
    }

    /// The hovers of the names in `app`'s explicit bindings and in its
    /// inline sub-proofs'.
    fn hoverBindings(
        self: *LineWalk,
        sink: *HoleInferenceSink,
        names: *const ViewTrace.DiagNames,
        app: ProofScript.RuleApplication,
    ) !void {
        for (app.refs) |ref| switch (ref) {
            .application => |child| try self.hoverBindings(sink, names, child),
            else => {},
        };
        if (app.arg_bindings.len == 0) return;
        const rule_id = self.theory.env.rule_names.get(app.rule_name) orelse return;
        const rule = &self.theory.env.rules.items[rule_id];
        for (app.arg_bindings) |binding| {
            const surface = (try self.bindingSurface(rule, binding)) orelse continue;
            try self.hoverNames(sink, names, binding.formula.span.start + 1, surface.expr);
        }
    }

    /// `binding`'s value as written, holes allowed, with the index of its
    /// binder in `rule`; null when either is malformed (the check reports
    /// that).
    fn bindingSurface(
        self: *LineWalk,
        rule: *const RuleDecl,
        binding: ProofScript.ArgBinding,
    ) !?struct { arg_index: usize, expr: *const Expr } {
        const arg_index = Idents.findRuleArgIndex(rule, binding.name) orelse return null;
        const expr = self.theory.parser.parseHoleyArgText(
            binding.formula.text,
            &self.theorem_vars,
            rule.args[arg_index],
        ) catch |err| switch (err) {
            error.OutOfMemory => return err,
            else => return null,
        };
        return .{ .arg_index = arg_index, .expr = expr };
    }

    fn hoverNames(
        self: *LineWalk,
        sink: *HoleInferenceSink,
        names: *const ViewTrace.DiagNames,
        math_start: usize,
        surface: *const Expr,
    ) !void {
        switch (surface.*) {
            .variable => {},
            .hole => |hole| {
                const name = hole.name orelse return;
                const token_span = hole.token_span orelse return;
                const span: Span = .{
                    .start = math_start + token_span.start,
                    .end = math_start + token_span.end,
                };
                if (sink.covers(self.hover_from, span)) return;
                const known = (try self.unknowns.known(self.theorem, name)) orelse return;
                const text = if (known.complete)
                    try ViewTrace.formatExprNamed(
                        sink.allocator,
                        self.theorem,
                        &self.theory.env,
                        names,
                        known.value,
                    )
                else
                    (try OpenGoals.formatGoalNamed(
                        sink.allocator,
                        self.theorem,
                        &self.theory.env,
                        &self.theory.parser,
                        &self.theorem_vars,
                        known.value,
                        &self.unknowns.open,
                    )) orelse return;
                try sink.addItemOwned(.{
                    .span = span,
                    .expression = text,
                    .partial = !known.complete,
                });
            },
            .term => |term| for (term.args) |arg| {
                try self.hoverNames(sink, names, math_start, arg);
            },
        }
    }

    /// Bind the named unknowns `line` fills, now that it checked as
    /// `checked`; a fill that disagrees with an earlier one fails the line.
    fn recordUnknowns(
        self: *LineWalk,
        line: ProofLine,
        surface: *const Expr,
        checked: ExprId,
    ) !void {
        const name = (self.unknowns.record(
            self.allocator,
            &self.theory.parser,
            self.theorem,
            &self.theory.env,
            &self.theory.registry,
            surface,
            checked,
        ) catch |err| switch (err) {
            error.NamedUnknownPairingLimit => return self.failUnknowns(line, error.NamedUnknownPairingLimit, null),
            else => return err,
        }) orelse return;
        return self.failUnknowns(line, error.NamedUnknownConflict, name);
    }

    fn failUnknowns(
        self: *LineWalk,
        line: ProofLine,
        err: CompilerDiag.DiagnosticError,
        name: ?[]const u8,
    ) CompilerDiag.DiagnosticError {
        self.compiler.setProof(CompilerDiag.withPhase(.{
            .kind = .generic,
            .err = err,
            .theorem_name = self.assertion.name,
            .line_label = line.label,
            .rule_name = line.application.rule_name,
            .name = name,
            .span = line.assertion.span,
        }, .theorem_application));
        return err;
    }

    /// Check each explicit binding of `app` and its inline sub-proofs that
    /// is written with holes (`(a := $ ?x → q $)`) against the value its
    /// binder took, now that the line checked: `app` checked as the line at
    /// `line_idx`. The names such a binding fills are bound.
    fn checkHoleyBindings(
        self: *LineWalk,
        line: ProofLine,
        app: ProofScript.RuleApplication,
        line_idx: usize,
    ) !void {
        var idx = line_idx;
        const rule_line = while (true) switch (self.checked.items[idx].data) {
            .rule => |rule_line| break rule_line,
            .transport => |transport| switch (transport.source) {
                .line => |source| idx = source,
                .hyp => return,
            },
            .sorry => return,
        };
        const rule = &self.theory.env.rules.items[rule_line.rule_id];
        for (app.arg_bindings) |binding| {
            const surface = (try self.bindingSurface(rule, binding)) orelse continue;
            if (!Holes.contains(surface.expr)) continue;
            const fit = self.unknowns.recordBinding(
                self.allocator,
                &self.theory.parser,
                self.theorem,
                &self.theory.env,
                &self.theory.registry,
                surface.expr,
                rule_line.bindings[surface.arg_index],
            ) catch |err| switch (err) {
                error.NamedUnknownPairingLimit => {
                    self.reportBinding(line, app, binding, error.NamedUnknownPairingLimit, binding.name);
                    return error.NamedUnknownPairingLimit;
                },
                else => return err,
            };
            switch (fit) {
                .fits => continue,
                .mismatch => {
                    self.reportBinding(line, app, binding, error.HoleyBindingMismatch, binding.name);
                    return error.HoleyBindingMismatch;
                },
                .conflict => |unknown| {
                    self.reportBinding(line, app, binding, error.NamedUnknownConflict, unknown);
                    return error.NamedUnknownConflict;
                },
            }
        }
        for (app.refs, 0..) |ref, ref_idx| {
            if (ref_idx >= rule_line.refs.len) break;
            const child = switch (ref) {
                .application => |child| child,
                else => continue,
            };
            switch (rule_line.refs[ref_idx]) {
                .line => |child_idx| try self.checkHoleyBindings(line, child, child_idx),
                .hyp => {},
            }
        }
    }

    fn reportBinding(
        self: *LineWalk,
        line: ProofLine,
        app: ProofScript.RuleApplication,
        binding: ProofScript.ArgBinding,
        err: CompilerDiag.DiagnosticError,
        name: []const u8,
    ) void {
        self.compiler.setProof(CompilerDiag.withPhase(.{
            .kind = .generic,
            .err = err,
            .theorem_name = self.assertion.name,
            .line_label = line.label,
            .rule_name = app.rule_name,
            .name = name,
            .span = binding.formula.span,
        }, .theorem_application));
    }

    /// A line justified by `?`: its goal is the statement it writes, holes
    /// and all. A concrete statement is admitted like `sorry!`, so later
    /// lines can cite it; a holey one leaves the line unfinished.
    ///
    /// References, `? [l1, ?]`, say which facts the step uses, by some rule
    /// not chosen yet: each is checked as far as it can be without one.
    fn admitOpenGoalLine(
        self: *LineWalk,
        apply_context: *const RuleApplyContext,
        line: ProofLine,
        parsed_assertion: Holes.ParsedAssertion,
    ) !Next {
        const app = line.application;
        if (OpenGoals.hasBindings(app)) return self.reportOpenGoalBindings(line);
        try self.open_goals.append(self.allocator, .{
            .at = app.rule_span.start,
            .goal = std.mem.trim(u8, line.assertion.text, " \t\r\n"),
        });
        try checkOpenGoalRefs(
            self.compiler,
            apply_context,
            ApplicationLine.fromLine(line),
            app.refs,
            self.unfinished.items,
            self.theorem,
            &self.theorem_vars,
        );
        switch (parsed_assertion) {
            .concrete => |expr| try self.admit(
                line,
                try CheckedIr.appendSorryLine(&self.checked, self.allocator, expr),
            ),
            .holey => {
                try self.unfinished.append(self.allocator, line.label);
                self.ends_unfinished = true;
            },
        }
        return .next;
    }

    fn reportOpenGoalBindings(self: *LineWalk, line: ProofLine) anyerror {
        self.compiler.setProof(CompilerDiag.withPhase(.{
            .kind = .open_goal_bindings,
            .err = error.OpenGoalBindings,
            .theorem_name = self.assertion.name,
            .line_label = line.label,
            .rule_name = line.application.rule_name,
            .span = line.application.span,
        }, .theorem_application));
        return error.OpenGoalBindings;
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
        try self.admitAsWritten(line);
    }

    /// A line whose check stopped at an open goal its position fixes only
    /// part of: it fails nothing, and stands as written. The diagnostic the
    /// check left is that open goal, with the part that is known.
    fn admitUnfinishedLine(
        self: *LineWalk,
        line: ProofLine,
        checked_mark: usize,
    ) !void {
        CheckedIr.deinitLines(self.allocator, self.checked.items[checked_mark..]);
        self.checked.shrinkRetainingCapacity(checked_mark);
        if (self.compiler.getDiagnostic()) |diag| switch (diag.detail) {
            .open_goal => |info| try self.open_goals.append(self.allocator, .{
                .at = diag.span.?.start,
                .goal = info.goal,
            }),
            else => {},
        };
        self.compiler.restoreDiagnostic(null);
        try self.reportOpenGoals(line);
        try self.admitAsWritten(line);
    }

    /// Admit a line its check did not finish by the statement it writes, so
    /// later lines can cite it; a holey or unparseable one is unfinished.
    fn admitAsWritten(self: *LineWalk, line: ProofLine) !void {
        // Unfinished unless its statement is admitted below. A repeated
        // label keeps its first line.
        self.ends_unfinished = true;
        if (self.labels.contains(line.label) or
            ProofScript.containsLabel(self.unfinished.items, line.label))
        {
            return;
        }
        const parsed = if (Holes.parseAssertion(
            &self.theory.parser,
            self.theorem,
            &self.theorem_vars,
            &self.theory.sort_vars,
            line.assertion.text,
        )) |written| try self.writeBoundUnknowns(written) else |parse_err| switch (parse_err) {
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
                var text_bufs: Inference.DepViolationTextBufs = .{};
                if (Inference.takeScratchDetail(
                    &text_bufs,
                    diag_scratch,
                    final_mark,
                    env,
                    theorem,
                    parser,
                    theorem_vars,
                    err,
                )) |taken| {
                    self.setFinalLineFailure(
                        final,
                        theorem_concl,
                        .generic,
                        CompilerDiag.narrowDiagnosticError(err),
                        taken,
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
                .{ .detail = .none },
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
        taken: CompilerDiag.ScratchDetail,
    ) void {
        var diag = CompilerDiag.withPhase(.{
            .kind = kind,
            .err = err,
            .theorem_name = self.assertion.name,
            .line_label = final.label,
            .rule_name = taken.rule_name,
            .span = final.span,
            .detail = taken.detail,
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

/// The references of an open goal line, `? [l1, #2, rule [..], ?]`: each
/// must name something, and an inline application is checked on its own,
/// with no goal from a rule. An open goal among them has no goal yet.
fn checkOpenGoalRefs(
    compiler: *CompilerContext,
    context: *const RuleApplyContext,
    line: ApplicationLine,
    refs: []const ProofScript.Ref,
    unfinished: []const []const u8,
    theorem: *TheoremContext,
    theorem_vars: *NameExprMap,
) !void {
    for (refs) |ref| switch (ref) {
        .hyp => |hyp| {
            const resolved = ProofScript.resolveHypRef(
                theorem.theorem_hyp_names,
                theorem.theorem_hyps.items.len,
                hyp,
            );
            if (resolved == .index) continue;
            return Apply.reportHypRef(
                compiler,
                context.assertion.name,
                line.label,
                hyp,
                resolved == .ambiguous,
            );
        },
        .line => |label| {
            if (context.labels.contains(label.label)) continue;
            if (ProofScript.containsLabel(unfinished, label.label)) continue;
            return Apply.reportUnknownLabel(compiler, context, line.label, label);
        },
        .application => |inline_app| {
            // Reported with the line; it has no goal to check against.
            if (ProofScript.isOpenGoalRuleName(inline_app.rule_name)) continue;
            _ = try applyRuleApplication(
                compiler,
                context,
                inline_app,
                .implicit_whole_conclusion,
                null,
                .{
                    .theorem_name = context.assertion.name,
                    .line_label = line.label,
                    .span = inline_app.span,
                },
                line.forInline(inline_app),
                theorem,
                theorem_vars,
            );
        },
    };
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
