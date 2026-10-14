const std = @import("std");
const ArenaAllocator = @import("./arena_allocator.zig").ArenaAllocator;
const MmbWriter = @import("./compiler/mmb_writer.zig");
const CompilerDiag = @import("./diag.zig");
const Pipeline = @import("./compiler/pipeline.zig");
const DiagnosticSink = @import("./compiler/diagnostic_sink.zig")
    .DiagnosticSink;
const Context = @import("./compiler/context.zig");
const CompilerContext = Context.CompilerContext;
const DebugConfig = @import("./debug.zig").DebugConfig;
const ExprModule = @import("./expr.zig");

const Diagnostic = CompilerDiag.Diagnostic;
const DiagnosticSource = CompilerDiag.DiagnosticSource;

pub const HoleInference = Context.HoleInference;
pub const HoleInferenceSink = Context.HoleInferenceSink;
pub const InlineConclusion = Context.InlineConclusion;
pub const InlineConclusionSink = Context.InlineConclusionSink;
pub const StatementSink = @import("./statement_sink.zig").StatementSink;
pub const CheckMemo = @import("./compiler/check_memo.zig").CheckMemo;

pub const Compiler = struct {
    pub const InferenceStatsSink = Context.InferenceStatsSink;
    pub const max_warnings = DiagnosticSink.max_warnings;
    pub const max_primary_diagnostics =
        DiagnosticSink.max_primary_diagnostics;

    allocator: std.mem.Allocator,
    source: []const u8,
    proof_source: ?[]const u8,
    diagnostics: DiagnosticSink,
    debug: DebugConfig,
    allow_search_placeholders: bool,
    hole_inference_sink: ?*HoleInferenceSink,
    inline_conclusion_sink: ?*InlineConclusionSink,
    statement_sink: ?*StatementSink,
    inference_stats_sink: ?*InferenceStatsSink,
    /// Search work ceiling for every inference solver this compiler
    /// constructs (`CompilerContext.work_budget`); null on the compile path.
    work_budget: ?ExprModule.WorkBudget = null,
    /// Memo of proof-block check outcomes across analyses (editor hosts).
    check_memo: ?*CheckMemo = null,

    const PipelineOutput = Pipeline.Output;

    pub inline fn init(
        allocator: std.mem.Allocator,
        source: []const u8,
    ) Compiler {
        return initInternal(allocator, source, null);
    }

    pub inline fn initWithProof(
        allocator: std.mem.Allocator,
        source: []const u8,
        proof_source: []const u8,
    ) Compiler {
        return initInternal(allocator, source, proof_source);
    }

    /// `inline`, as are `init` and `initWithProof`: a `Compiler` holds about
    /// 300 KB of diagnostic storage, and returned through a call it is built
    /// once and then copied, undefined storage and all, into the caller's
    /// variable, which a short compile notices.
    inline fn initInternal(
        allocator: std.mem.Allocator,
        source: []const u8,
        proof_source: ?[]const u8,
    ) Compiler {
        return .{
            .allocator = allocator,
            .source = source,
            .proof_source = proof_source,
            .diagnostics = DiagnosticSink.init(source, proof_source),
            .debug = DebugConfig.none,
            .allow_search_placeholders = false,
            .hole_inference_sink = null,
            .inline_conclusion_sink = null,
            .statement_sink = null,
            .inference_stats_sink = null,
        };
    }

    pub fn check(self: *Compiler) !void {
        self.clearDiagnostics();

        var arena = ArenaAllocator.init(self.allocator);
        defer arena.deinit();

        var compiler_context = self.context();
        try Pipeline.run(&compiler_context, arena.allocator(), null);
        try self.diagnostics.promoteWarningsToErrors();
    }

    pub fn analyze(self: *Compiler) !void {
        self.clearDiagnostics();

        var arena = ArenaAllocator.init(self.allocator);
        defer arena.deinit();

        var compiler_context = self.context();
        if (self.proof_source != null) {
            try Pipeline.analyze(&compiler_context, arena.allocator());
            return;
        }
        try Pipeline.analyzeMm0(&compiler_context, arena.allocator());
    }

    pub fn analyzeMm0(self: *Compiler) !void {
        self.clearDiagnostics();

        var arena = ArenaAllocator.init(self.allocator);
        defer arena.deinit();

        var compiler_context = self.context();
        try Pipeline.analyzeMm0(&compiler_context, arena.allocator());
    }

    pub fn compileMmb(
        self: *Compiler,
        out_allocator: std.mem.Allocator,
    ) ![]u8 {
        self.clearDiagnostics();

        _ = self.proof_source orelse return error.MissingProofFile;

        var arena = ArenaAllocator.init(self.allocator);
        defer arena.deinit();

        var emit = PipelineOutput{};
        var compiler_context = self.context();
        try Pipeline.run(&compiler_context, arena.allocator(), &emit);
        try self.diagnostics.promoteWarningsToErrors();

        return try MmbWriter.buildFile(
            out_allocator,
            emit.sort_names.items,
            emit.sorts.items,
            emit.terms.items,
            emit.theorems.items,
            emit.statements.items,
        );
    }

    /// A compiler for the analysis that explains a failed `compileMmb`:
    /// the same unit, file mappings and statement sink.
    pub inline fn failureAnalysis(self: *const Compiler) Compiler {
        var result = initInternal(self.allocator, self.source, self.proof_source);
        result.diagnostics.setMapping(.mm0, self.diagnostics.mm0_mapping);
        result.diagnostics.setMapping(.proof, self.diagnostics.proof_mapping);
        result.statement_sink = self.statement_sink;
        return result;
    }

    /// After `compile.compileMmb` failed: analyze the unit, which checks on
    /// past failed lines and theorems, so the primary diagnostics name every
    /// failure, not only the first. The compile's own diagnostic is added
    /// when the analysis did not find it: a failure only emission sees, or a
    /// warning promoted to an error. False when the compile failed with no
    /// diagnostic at all (out of memory, say), for the host to report.
    ///
    /// Search placeholders are the host's call: an editor admits them and
    /// lists them itself, while the command line leaves each one an error.
    pub fn analyzeCompileFailure(self: *Compiler, compile: *const Compiler) bool {
        self.analyze() catch {};
        const diag = compile.getDiagnostic() orelse return false;
        for (self.primaryDiagnostics()) |found| {
            if (found.err == diag.err and found.source == diag.source and
                std.meta.eql(found.span, diag.span)) return true;
        }
        self.addPrimaryDiagnostic(diag);
        return true;
    }

    pub fn primaryDiagnostics(self: *const Compiler) []const Diagnostic {
        return self.diagnostics.primaryDiagnostics();
    }

    pub fn warningDiagnostics(self: *const Compiler) []const Diagnostic {
        return self.diagnostics.warningDiagnostics();
    }

    pub fn omittedPrimaryDiagnostic(
        self: *const Compiler,
        source: DiagnosticSource,
    ) ?Diagnostic {
        return self.diagnostics.omittedPrimaryDiagnostic(source);
    }

    pub fn addPrimaryDiagnostic(self: *Compiler, diag: Diagnostic) void {
        self.diagnostics.addPrimaryDiagnostic(diag);
    }

    pub fn addWarning(self: *Compiler, diag: Diagnostic) void {
        self.diagnostics.addWarning(diag);
    }

    pub fn reportWarnings(self: *const Compiler) void {
        self.diagnostics.reportWarnings();
    }

    pub fn reportPrimaryDiagnostics(self: *const Compiler) void {
        self.diagnostics.reportPrimaryDiagnostics();
    }

    pub fn reportError(self: *const Compiler, err: anyerror) void {
        self.diagnostics.reportError(err);
    }

    pub fn setDiagnostic(self: *Compiler, diag: Diagnostic) void {
        self.diagnostics.setDiagnostic(diag);
    }

    pub fn getDiagnostic(self: *const Compiler) ?Diagnostic {
        return self.diagnostics.getDiagnostic();
    }

    pub fn restoreDiagnostic(self: *Compiler, diag: ?Diagnostic) void {
        self.diagnostics.restoreDiagnostic(diag);
    }

    fn clearDiagnostics(self: *Compiler) void {
        self.diagnostics.clear();
    }

    fn context(self: *Compiler) CompilerContext {
        var result = CompilerContext.init(
            self.source,
            self.proof_source,
            self.debug,
            &self.diagnostics,
        );
        result.allow_search_placeholders = self.allow_search_placeholders;
        result.hole_inference_sink = self.hole_inference_sink;
        result.inline_conclusion_sink = self.inline_conclusion_sink;
        result.statement_sink = self.statement_sink;
        result.inference_stats_sink = self.inference_stats_sink;
        result.work_budget = self.work_budget;
        result.check_memo = self.check_memo;
        return result;
    }
};

pub const diagnosticSummary = CompilerDiag.diagnosticSummary;
