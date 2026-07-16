const std = @import("std");

const DebugConfig = @import("../debug.zig").DebugConfig;
const DiagnosticSink = @import("./diagnostic_sink.zig").DiagnosticSink;
const CompilerDiag = @import("./diag.zig");
const Diagnostic = CompilerDiag.Diagnostic;
const DiagnosticPhase = CompilerDiag.DiagnosticPhase;
const GlobalEnv = @import("../env.zig").GlobalEnv;
const Span = @import("../proof_script.zig").Span;
const StatementSink = @import("../statement_sink.zig").StatementSink;

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
/// checker elaborates. Fallback and retry candidates re-elaborate the same
/// source application, so one span may be recorded more than once; the LAST
/// entry for a span is the one from the attempt that ultimately succeeded.
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
