const std = @import("std");

const DebugConfig = @import("../debug.zig").DebugConfig;
const DiagnosticSink = @import("./diagnostic_sink.zig").DiagnosticSink;
const CompilerDiag = @import("../diag.zig");
const Diagnostic = CompilerDiag.Diagnostic;
const DiagnosticPhase = CompilerDiag.DiagnosticPhase;
const GlobalEnv = @import("../env.zig").GlobalEnv;
const Span = @import("../proof_script.zig").Span;
const StatementSink = @import("../statement_sink.zig").StatementSink;
const CheckMemo = @import("./check_memo.zig").CheckMemo;
const ExprModule = @import("../expr.zig");

pub const HoleInference = struct {
    span: Span,
    expression: []const u8,
};

pub const HoleInferenceSink = struct {
    allocator: std.mem.Allocator,
    items: std.ArrayListUnmanaged(HoleInference) = .{},

    pub fn deinit(self: *HoleInferenceSink) void {
        for (self.items.items) |item| {
            self.allocator.free(item.expression);
        }
        self.items.deinit(self.allocator);
        self.* = undefined;
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
    items: std.ArrayListUnmanaged(InlineConclusion) = .{},

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

pub const CompilerContext = struct {
    source: []const u8,
    proof_source: ?[]const u8,
    debug: DebugConfig,
    diagnostics: *DiagnosticSink,
    allow_search_placeholders: bool = false,
    hole_inference_sink: ?*HoleInferenceSink = null,
    inline_conclusion_sink: ?*InlineConclusionSink = null,
    statement_sink: ?*StatementSink = null,
    inference_stats_sink: ?*InferenceStatsSink = null,
    /// Work ceiling installed by a budgeted search for the duration of one
    /// generation call; every inference solver constructed under it polls
    /// it (`expr.zig` `WorkBudget`). Null on the compile path.
    work_budget: ?ExprModule.WorkBudget = null,
    /// Memo of block check outcomes for editor re-analysis; null on the
    /// compile path. See `check_memo.zig`.
    check_memo: ?*CheckMemo = null,

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

    pub fn setProofScratchDiagnosticIfPresent(
        self: *CompilerContext,
        scratch: *CompilerDiag.Scratch,
        mark: CompilerDiag.Scratch.Mark,
        env: *const GlobalEnv,
        phase: ?DiagnosticPhase,
        kind: CompilerDiag.DiagnosticKind,
        err: anyerror,
        theorem_name: []const u8,
        line_label: ?[]const u8,
        rule_name: ?[]const u8,
        span: ?Span,
    ) bool {
        return self.diagnostics.setProofScratchDiagnosticIfPresent(
            scratch,
            mark,
            env,
            phase,
            kind,
            err,
            theorem_name,
            line_label,
            rule_name,
            span,
        );
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
