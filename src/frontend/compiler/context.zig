const std = @import("std");

const DebugConfig = @import("../debug.zig").DebugConfig;
const DiagnosticSink = @import("./diagnostic_sink.zig").DiagnosticSink;
const CompilerDiag = @import("../diag.zig");
const Diagnostic = CompilerDiag.Diagnostic;
const DiagnosticPhase = CompilerDiag.DiagnosticPhase;
const GlobalEnv = @import("../env.zig").GlobalEnv;
const RuleDecl = @import("../env.zig").RuleDecl;
const findRuleArgIndex = @import("../idents.zig").findRuleArgIndex;
const TemplateExpr = @import("../rules.zig").TemplateExpr;
const templateMentionsBinder = @import("../rules.zig").templateMentionsBinder;
const ProofScript = @import("../proof_script.zig");
const Span = ProofScript.Span;
const ArgBinding = ProofScript.ArgBinding;
const RuleApplication = ProofScript.RuleApplication;
const StatementSink = @import("../statement_sink.zig").StatementSink;
const CheckMemo = @import("./check_memo.zig").CheckMemo;
const ExprModule = @import("../expr.zig");
const TheoremContext = ExprModule.TheoremContext;
const MM0Parser = @import("../parse_recovery.zig").MM0Parser;
const Inference = @import("./inference.zig");

pub const HoleInference = struct {
    span: Span,
    expression: []const u8,
};

/// A holey line's assertion with every hole filled in, printed so it
/// parses back to the line's checked conclusion.
pub const FilledAssertion = struct {
    /// The whole proof line.
    line: Span,
    /// The assertion's math string, `$` delimiters included.
    assertion: Span,
    /// The filled math text, without delimiters.
    text: []const u8,
};

pub const HoleInferenceSink = struct {
    allocator: std.mem.Allocator,
    items: std.ArrayListUnmanaged(HoleInference) = .empty,
    /// Only for lines whose conclusion prints with source names.
    assertions: std.ArrayListUnmanaged(FilledAssertion) = .empty,

    pub fn deinit(self: *HoleInferenceSink) void {
        for (self.items.items) |item| {
            self.allocator.free(item.expression);
        }
        self.items.deinit(self.allocator);
        for (self.assertions.items) |item| {
            self.allocator.free(item.text);
        }
        self.assertions.deinit(self.allocator);
        self.* = undefined;
    }

    pub fn addAssertionOwned(
        self: *HoleInferenceSink,
        line: Span,
        assertion: Span,
        text: []const u8,
    ) !void {
        errdefer self.allocator.free(text);
        try self.assertions.append(self.allocator, .{
            .line = line,
            .assertion = assertion,
            .text = text,
        });
    }

    pub fn addOwned(
        self: *HoleInferenceSink,
        span: Span,
        expression: []const u8,
    ) !void {
        errdefer self.allocator.free(expression);
        try self.items.append(self.allocator, .{
            .span = span,
            .expression = expression,
        });
    }
};

pub const InlineConclusion = struct {
    /// Span of the inline rule application in the proof source.
    span: Span,
    /// Rendered conclusion of the hidden line the application elaborated to.
    conclusion: []const u8,
};

/// Collects the rendered conclusion of every inline rule application the
/// checker elaborates. An entry survives only if every attempt enclosing its
/// application succeeds: a failed fallback or retry candidate, and any search
/// probe, rolls the sink back to its entry mark (see `mark`/`rollback`).
pub const InlineConclusionSink = struct {
    allocator: std.mem.Allocator,
    items: std.ArrayListUnmanaged(InlineConclusion) = .empty,

    pub fn deinit(self: *InlineConclusionSink) void {
        for (self.items.items) |item| {
            self.allocator.free(item.conclusion);
        }
        self.items.deinit(self.allocator);
        self.* = undefined;
    }

    pub fn addOwned(
        self: *InlineConclusionSink,
        span: Span,
        conclusion: []const u8,
    ) !void {
        errdefer self.allocator.free(conclusion);
        try self.items.append(self.allocator, .{
            .span = span,
            .conclusion = conclusion,
        });
    }

    pub fn mark(self: *const InlineConclusionSink) usize {
        return self.items.items.len;
    }

    /// Drop (and free) every entry recorded since `at`.
    pub fn rollback(self: *InlineConclusionSink, at: usize) void {
        for (self.items.items[at..]) |item| {
            self.allocator.free(item.conclusion);
        }
        self.items.shrinkRetainingCapacity(at);
    }
};

/// A search suggestion's bindings, held back from the checker so it can
/// learn which ones it needs (#374). The checker sees the suggestion with
/// the withheld bindings dropped (`register`); an application whose binders
/// inference cannot reproduce looks its full list up here (`Withheld`),
/// supplies the values it needs, and marks them used. Speculative attempts
/// roll their marks back like `InlineConclusionSink` entries.
pub const BindingOracle = struct {
    allocator: std.mem.Allocator,
    /// Each withheld application's full binding list, keyed by the address
    /// of the bindings its source still states (`register`).
    full: std.AutoHashMapUnmanaged(usize, []const ArgBinding) = .{},
    /// In the order taken, so `rollback` can truncate.
    used: std.AutoArrayHashMapUnmanaged(*const ArgBinding, void) = .{},
    /// Bindings a check found it needed before inference ran: an inline
    /// sub-proof checked against the weak hint its withheld parent gave it,
    /// and proved something other than the parent's premise, or failed even
    /// with the parent's premise binders supplied. The next check supplies
    /// them up front. Forcing over-approximates what the checker needs, so
    /// trimming tries each forced binding away again once the suggestion
    /// checks. Only ever grows (a rolled-back attempt's included, which
    /// costs at most that one try), so a check that forced nothing new
    /// shows as an unchanged count.
    forced: std.AutoHashMapUnmanaged(*const ArgBinding, void) = .{},

    pub fn deinit(self: *BindingOracle) void {
        self.full.deinit(self.allocator);
        self.used.deinit(self.allocator);
        self.forced.deinit(self.allocator);
        self.* = undefined;
    }

    /// Withhold `full` from an application whose source now states only
    /// `stated`, a slice of its own (or `full[0..0]`, for none).
    pub fn register(
        self: *BindingOracle,
        stated: []const ArgBinding,
        full: []const ArgBinding,
    ) !void {
        try self.full.put(self.allocator, @intFromPtr(stated.ptr), full);
    }

    /// The full binding list behind a withheld application, if it had any.
    pub fn lookup(self: *const BindingOracle, app: RuleApplication) ?[]const ArgBinding {
        return self.full.get(@intFromPtr(app.arg_bindings.ptr));
    }

    /// Force every binding of the withheld inline sub-proofs among `refs`,
    /// a level at a time: the nearest level that has one not forced before.
    /// For a sub-proof that strayed below the level its parent can see.
    pub fn forceNearestSubProofs(self: *BindingOracle, refs: []const ProofScript.Ref) !void {
        var level = std.ArrayListUnmanaged(RuleApplication).empty;
        defer level.deinit(self.allocator);
        var next = std.ArrayListUnmanaged(RuleApplication).empty;
        defer next.deinit(self.allocator);
        try appendSubProofs(self.allocator, &level, refs);
        while (level.items.len != 0) {
            const before = self.forced.count();
            for (level.items) |app| {
                const full = self.lookup(app) orelse continue;
                for (full) |*binding| try self.forced.put(self.allocator, binding, {});
            }
            if (self.forced.count() != before) return;
            next.clearRetainingCapacity();
            for (level.items) |app| try appendSubProofs(self.allocator, &next, app.refs);
            std.mem.swap(std.ArrayListUnmanaged(RuleApplication), &level, &next);
        }
    }

    fn appendSubProofs(
        allocator: std.mem.Allocator,
        out: *std.ArrayListUnmanaged(RuleApplication),
        refs: []const ProofScript.Ref,
    ) !void {
        for (refs) |ref| switch (ref) {
            .application => |app| try out.append(allocator, app),
            .hyp, .line => {},
        };
    }

    pub fn mark(self: *const BindingOracle) usize {
        return self.used.count();
    }

    pub fn rollback(self: *BindingOracle, at: usize) void {
        self.used.shrinkRetainingCapacity(at);
    }

    /// One withheld application as the checker sees it: its rule, its full
    /// binding list, and the values parsed from that list.
    pub const Withheld = struct {
        oracle: *BindingOracle,
        rule: *const RuleDecl,
        full: []const ArgBinding,
        values: []const ?ExprModule.ExprId,

        /// Copy into `dest` each value that `mask` selects (null: each
        /// forced one) and `dest` lacks, and mark its binding used (and
        /// forced, if `force`).
        pub fn supply(
            w: Withheld,
            mask: ?[]const bool,
            force: bool,
            dest: []?ExprModule.ExprId,
        ) !void {
            const oracle = w.oracle;
            for (w.full) |*binding| {
                const idx = findRuleArgIndex(w.rule, binding.name) orelse continue;
                const want = if (mask) |m| m[idx] else oracle.forced.contains(binding);
                if (!want or dest[idx] != null) continue;
                dest[idx] = w.values[idx];
                try oracle.used.put(oracle.allocator, binding, {});
                if (force) try oracle.forced.put(oracle.allocator, binding, {});
            }
        }

        /// Force each binding that `premise` mentions: an inline sub-proof
        /// proved something other than it. One the application already had
        /// is forced too, so trimming tries it away again.
        pub fn forcePremise(w: Withheld, premise: TemplateExpr) !void {
            for (w.full) |*binding| {
                const idx = findRuleArgIndex(w.rule, binding.name) orelse continue;
                if (!templateMentionsBinder(premise, idx)) continue;
                try w.oracle.forced.put(w.oracle.allocator, binding, {});
            }
        }

        /// Force what the premises of the inline sub-proofs among `refs`
        /// mention, or, when that is nothing new, the sub-proofs' own
        /// bindings (`forceNearestSubProofs`).
        pub fn forceStrayed(w: Withheld, refs: []const ProofScript.Ref) !void {
            const before = w.oracle.forced.count();
            for (refs, w.rule.hyps) |ref, premise| {
                if (ref == .application) try w.forcePremise(premise);
            }
            if (w.oracle.forced.count() == before) try w.oracle.forceNearestSubProofs(refs);
        }
    };
};

/// Observability counters from binder inference, collected across every
/// solver the run constructs. Threaded like `HoleInferenceSink`: paths that
/// do not attach one pay nothing.
pub const InferenceStatsSink = struct {
    /// Largest branch population any single constraint left behind in any
    /// structural solve of the run.
    peak_solver_branches: usize = 0,

    pub fn recordSolver(self: *InferenceStatsSink, peak_branches: usize) void {
        self.peak_solver_branches = @max(self.peak_solver_branches, peak_branches);
    }
};

/// Analysis only: check a theorem past a line that fails, taking the line's
/// statement as written, and report every failure.
pub const KeepChecking = struct {
    /// The rules the analysis dropped because their own check failed.
    invalid_rules: *const std.StringHashMap(void),

    /// False for a failure that only cites a dropped rule: that rule's own
    /// failure is already reported.
    pub fn reports(self: KeepChecking, diag: Diagnostic) bool {
        switch (diag.err) {
            error.UnknownRule, error.RuleNotYetAvailable => {},
            else => return true,
        }
        const rule_name = diag.rule_name orelse return true;
        return !self.invalid_rules.contains(rule_name);
    }
};

pub const CompilerContext = struct {
    source: []const u8,
    proof_source: ?[]const u8,
    debug: DebugConfig,
    diagnostics: *DiagnosticSink,
    /// Analysis, not compilation: a proof line holding a search placeholder
    /// is admitted like `sorry!` when its statement is concrete, and a
    /// placeholder nested in an application is admitted as the goal its
    /// position expects when that goal is concrete (a search checking its
    /// result in a line that holds another). False on the compile path,
    /// which rejects every placeholder.
    allow_search_placeholders: bool = false,
    /// Set while the analysis walks the proofs; null on the compile path,
    /// which stops at the first failure.
    keep_checking: ?KeepChecking = null,
    hole_inference_sink: ?*HoleInferenceSink = null,
    inline_conclusion_sink: ?*InlineConclusionSink = null,
    /// Set while a search trims a suggestion's bindings; null otherwise.
    binding_oracle: ?*BindingOracle = null,
    statement_sink: ?*StatementSink = null,
    inference_stats_sink: ?*InferenceStatsSink = null,
    /// Work ceiling installed by a budgeted search for the duration of one
    /// generation call; every inference solver constructed under it polls
    /// it (`expr.zig` `WorkBudget`). Null on the compile path.
    work_budget: ?ExprModule.WorkBudget = null,
    /// Memo of block check outcomes for editor re-analysis; null on the
    /// compile path. See `check_memo.zig`.
    check_memo: ?*CheckMemo = null,
    /// `@frameAddress` of the outermost frame that elaborates rule
    /// applications: the first `applyRuleApplication` on the stack, or a
    /// search's entry frame, since its candidate checks run deep in its
    /// descent. The checker's call-stack guard measures from here
    /// (`check/apply.zig`).
    stack_base: ?usize = null,

    /// Tell the check memo how a theorem or lemma block came out: the one
    /// thing later checks can observe of its proof.
    pub fn noteBlockOutcome(self: *CompilerContext, name: []const u8, ok: bool) void {
        const memo = self.check_memo orelse return;
        memo.feedOutcome(name, ok);
    }

    pub fn recordSolverBranches(self: *CompilerContext, peak_branches: usize) void {
        const sink = self.inference_stats_sink orelse return;
        sink.recordSolver(peak_branches);
    }

    pub fn init(
        source: []const u8,
        proof_source: ?[]const u8,
        debug: DebugConfig,
        diagnostics: *DiagnosticSink,
    ) CompilerContext {
        return .{
            .source = source,
            .proof_source = proof_source,
            .debug = debug,
            .diagnostics = diagnostics,
        };
    }

    pub fn setDiagnostic(self: *CompilerContext, diag: Diagnostic) void {
        self.diagnostics.setDiagnostic(diag);
    }

    pub fn setIfMissing(self: *CompilerContext, diag: Diagnostic) void {
        self.diagnostics.setIfMissing(diag);
    }

    pub fn setProof(self: *CompilerContext, diag: Diagnostic) void {
        self.diagnostics.setProof(diag);
    }

    pub fn maybeSetProof(self: *CompilerContext, diag: Diagnostic) void {
        self.diagnostics.maybeSetProof(diag);
    }

    /// Reports the detail `err` left in `scratch` since `mark`, if any. A
    /// congruence step's dependency violation names its `@congr` rule
    /// rather than `rule_name`, and shows what the step assigned.
    pub fn setProofScratchDiagnosticIfPresent(
        self: *CompilerContext,
        scratch: *CompilerDiag.Scratch,
        mark: CompilerDiag.Scratch.Mark,
        env: *const GlobalEnv,
        theorem: *const TheoremContext,
        parser: ?*const MM0Parser,
        theorem_vars: ?*const Inference.NameExprMap,
        phase: ?DiagnosticPhase,
        kind: CompilerDiag.DiagnosticKind,
        err: anyerror,
        theorem_name: []const u8,
        line_label: ?[]const u8,
        rule_name: ?[]const u8,
        span: ?Span,
    ) bool {
        var text_bufs: Inference.DepViolationTextBufs = .{};
        const taken = Inference.takeScratchDetail(
            &text_bufs,
            scratch,
            mark,
            env,
            theorem,
            parser,
            theorem_vars,
            err,
        ) orelse return false;
        var diag: Diagnostic = .{
            .kind = kind,
            .err = CompilerDiag.narrowDiagnosticError(err),
            .theorem_name = theorem_name,
            .line_label = line_label,
            .rule_name = taken.rule_name orelse rule_name,
            .span = span,
            .detail = taken.detail,
        };
        if (phase) |actual_phase| {
            CompilerDiag.setPhase(&diag, actual_phase);
        }
        self.diagnostics.maybeSetProof(diag);
        return true;
    }

    pub fn addPrimaryDiagnostic(
        self: *CompilerContext,
        diag: Diagnostic,
    ) void {
        self.diagnostics.addPrimaryDiagnostic(diag);
    }

    pub fn addWarning(self: *CompilerContext, diag: Diagnostic) void {
        self.diagnostics.addWarning(diag);
    }

    pub fn getDiagnostic(self: *const CompilerContext) ?Diagnostic {
        return self.diagnostics.getDiagnostic();
    }

    pub fn restoreDiagnostic(
        self: *CompilerContext,
        diag: ?Diagnostic,
    ) void {
        self.diagnostics.restoreDiagnostic(diag);
    }
};
