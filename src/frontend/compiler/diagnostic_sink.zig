const std = @import("std");
const CompilerDiag = @import("../diag.zig");
const Diagnostic = CompilerDiag.Diagnostic;
const DiagnosticDetail = CompilerDiag.DiagnosticDetail;
const DiagnosticPhase = CompilerDiag.DiagnosticPhase;
const DiagnosticSource = CompilerDiag.DiagnosticSource;
const GlobalEnv = @import("../env.zig").GlobalEnv;
const Span = @import("../proof_script.zig").Span;
const Imports = @import("../imports.zig");

pub const DiagnosticSink = struct {
    pub const max_warnings = 32;
    pub const max_primary_diagnostics = 256;
    const diagnostic_storage_size = 32768;
    const truncated_diagnostic_string = "<diagnostic string truncated>";

    source: []const u8,
    proof_source: ?[]const u8,
    /// When a source is a join of several files, how joined offsets map
    /// back to (file, offset) so reports name the right file.
    mm0_mapping: ?Imports.Mapping = null,
    proof_mapping: ?Imports.Mapping = null,
    last_diagnostic: ?Diagnostic,
    primary_diagnostic_storage: [max_primary_diagnostics]Diagnostic =
        undefined,
    primary_diagnostic_count: usize = 0,
    dropped_primary_diagnostic_count: usize = 0,
    dropped_mm0_primary_diagnostic_count: usize = 0,
    dropped_proof_primary_diagnostic_count: usize = 0,
    warning_storage: [max_warnings]Diagnostic = undefined,
    warning_count: usize = 0,
    dropped_warning_count: usize = 0,
    warnings_as_errors: bool = false,
    diagnostic_storage: [diagnostic_storage_size]u8 = undefined,
    diagnostic_storage_len: usize = 0,

    pub fn init(
        source: []const u8,
        proof_source: ?[]const u8,
    ) DiagnosticSink {
        return .{
            .source = source,
            .proof_source = proof_source,
            .last_diagnostic = null,
        };
    }

    pub fn clear(self: *DiagnosticSink) void {
        self.diagnostic_storage_len = 0;
        self.last_diagnostic = null;
        self.primary_diagnostic_count = 0;
        self.dropped_primary_diagnostic_count = 0;
        self.dropped_mm0_primary_diagnostic_count = 0;
        self.dropped_proof_primary_diagnostic_count = 0;
        self.warning_count = 0;
        self.dropped_warning_count = 0;
    }

    pub fn primaryDiagnostics(
        self: *const DiagnosticSink,
    ) []const Diagnostic {
        return self.primary_diagnostic_storage[0..self.primary_diagnostic_count];
    }

    pub fn warningDiagnostics(
        self: *const DiagnosticSink,
    ) []const Diagnostic {
        return self.warning_storage[0..self.warning_count];
    }

    pub fn omittedPrimaryDiagnostic(
        self: *const DiagnosticSink,
        source: DiagnosticSource,
    ) ?Diagnostic {
        const count = self.droppedPrimaryDiagnosticCount(source);
        if (count == 0) return null;
        return .{
            .kind = .omitted_diagnostics,
            .err = error.DiagnosticsOmitted,
            .source = source,
            .detail = .{ .omitted_diagnostics = .{ .count = count } },
        };
    }

    pub fn addPrimaryDiagnostic(
        self: *DiagnosticSink,
        diag: Diagnostic,
    ) void {
        const primary = self.stableDiagnostic(diag);
        if (self.primary_diagnostic_count >=
            self.primary_diagnostic_storage.len)
        {
            self.dropped_primary_diagnostic_count += 1;
            switch (primary.source) {
                .mm0 => self.dropped_mm0_primary_diagnostic_count += 1,
                .proof => self.dropped_proof_primary_diagnostic_count += 1,
            }
            return;
        }
        self.primary_diagnostic_storage[self.primary_diagnostic_count] =
            primary;
        self.primary_diagnostic_count += 1;
    }

    pub fn addWarning(self: *DiagnosticSink, diag: Diagnostic) void {
        var warning = self.stableDiagnostic(diag);
        warning.severity = .warning;
        if (self.warning_count >= self.warning_storage.len) {
            self.dropped_warning_count += 1;
            return;
        }
        self.warning_storage[self.warning_count] = warning;
        self.warning_count += 1;
    }

    /// Each warning takes the stderr lock on its own, so one failed write
    /// (which stays sticky until unlock) does not drop the ones after it.
    pub fn reportWarnings(self: *const DiagnosticSink) void {
        for (self.warningDiagnostics()) |diag| self.reportDiagnostic(diag);
        if (self.dropped_warning_count != 0) {
            var buffer: [256]u8 = undefined;
            const stderr = &std.debug.lockStderr(&buffer).file_writer.interface;
            defer std.debug.unlockStderr();
            stderr.print(
                "{s}: ",
                .{CompilerDiag.severityLabel(.warning)},
            ) catch return;
            CompilerDiag.writeOmittedWarningsSummary(
                stderr,
                self.dropped_warning_count,
            ) catch return;
            stderr.writeByte('\n') catch return;
        }
    }

    /// Every primary diagnostic, then a count of those that did not fit.
    pub fn reportPrimaryDiagnostics(self: *const DiagnosticSink) void {
        for (self.primaryDiagnostics()) |diag| self.reportDiagnostic(diag);
        for ([_]DiagnosticSource{ .mm0, .proof }) |source| {
            if (self.omittedPrimaryDiagnostic(source)) |omitted| {
                self.reportDiagnostic(omitted);
            }
        }
    }

    pub fn reportError(self: *const DiagnosticSink, err: anyerror) void {
        if (self.last_diagnostic) |diag| {
            if (diag.err == err) {
                self.reportDiagnostic(diag);
                return;
            }
        }
        std.debug.print("{s}: {s}\n", .{
            CompilerDiag.severityLabel(.@"error"),
            CompilerDiag.errorSummary(err),
        });
    }

    pub fn promoteWarningsToErrors(self: *DiagnosticSink) !void {
        if (!self.warnings_as_errors) return;
        const warnings = self.warningDiagnostics();
        if (warnings.len == 0) return;

        var diag = warnings[0];
        diag.severity = .@"error";
        self.setDiagnostic(diag);
        return diag.err;
    }

    pub fn reportDiagnostic(
        self: *const DiagnosticSink,
        diag: Diagnostic,
    ) void {
        var buffer: [256]u8 = undefined;
        const stderr = &std.debug.lockStderr(&buffer).file_writer.interface;
        defer std.debug.unlockStderr();
        self.writeDiagnostic(stderr, diag) catch return;
    }

    fn writeDiagnostic(
        self: *const DiagnosticSink,
        stderr: *std.Io.Writer,
        diag: Diagnostic,
    ) std.Io.Writer.Error!void {
        try stderr.print(
            "{s}: ",
            .{CompilerDiag.severityLabel(diag.severity)},
        );
        try CompilerDiag.renderDiagnostic(stderr, diag, "\n  ");
        try stderr.writeByte('\n');
        try self.writeDiagnosticNotes(stderr, diag);
        try self.writeDiagnosticRelated(stderr, diag);
        try self.writeDiagnosticLocation(stderr, diag);
    }

    pub fn setMapping(
        self: *DiagnosticSink,
        source: DiagnosticSource,
        new_mapping: ?Imports.Mapping,
    ) void {
        switch (source) {
            .mm0 => self.mm0_mapping = new_mapping,
            .proof => self.proof_mapping = new_mapping,
        }
    }

    /// The file a diagnostic's span lies in, when the source is a join
    /// with a mapping; null otherwise.
    pub fn diagnosticFileLabel(
        self: *const DiagnosticSink,
        diag: Diagnostic,
    ) ?[]const u8 {
        const span = diag.span orelse return null;
        const m = self.mapping(diag.source) orelse return null;
        const hit = m.locateSpan(.{ .start = span.start, .end = span.end }) orelse
            return null;
        return hit.label;
    }

    /// The file and file-local span a joined-source span lies in, when the
    /// source is a join with a mapping; null otherwise (the span then
    /// indexes the whole source text as given).
    pub fn locateInFile(
        self: *const DiagnosticSink,
        source: DiagnosticSource,
        span: Span,
    ) ?Imports.Mapping.Located {
        const m = self.mapping(source) orelse return null;
        return m.locateSpan(.{ .start = span.start, .end = span.end });
    }

    fn mapping(
        self: *const DiagnosticSink,
        source: DiagnosticSource,
    ) ?Imports.Mapping {
        return switch (source) {
            .mm0 => self.mm0_mapping,
            .proof => self.proof_mapping,
        };
    }

    fn writeDiagnosticLocation(
        self: *const DiagnosticSink,
        stderr: *std.Io.Writer,
        diag: Diagnostic,
    ) std.Io.Writer.Error!void {
        const span = diag.span orelse return;
        const located = self.locateSpan(diag.source, span) orelse return;
        try writeSpanLocation(stderr, "", located.info, located.span);
    }

    fn writeDiagnosticNotes(
        self: *const DiagnosticSink,
        stderr: *std.Io.Writer,
        diag: Diagnostic,
    ) std.Io.Writer.Error!void {
        for (diag.noteSlice()) |note| {
            try stderr.print("  {s}: ", .{CompilerDiag.noteHeading()});
            try CompilerDiag.renderNoteMessage(stderr, note.message);
            try stderr.writeByte('\n');
            const span = note.span orelse continue;
            const located = self.locateSpan(note.source, span) orelse continue;
            try writeSpanLocation(
                stderr,
                CompilerDiag.noteHeading(),
                located.info,
                located.span,
            );
        }
    }

    fn writeDiagnosticRelated(
        self: *const DiagnosticSink,
        stderr: *std.Io.Writer,
        diag: Diagnostic,
    ) std.Io.Writer.Error!void {
        for (diag.relatedSlice()) |related| {
            try stderr.print(
                "  {s}: ",
                .{CompilerDiag.relatedHeading()},
            );
            try CompilerDiag.renderRelatedLabel(stderr, related.label);
            try stderr.writeByte('\n');
            const located = self.locateSpan(related.source, related.span) orelse
                continue;
            try writeSpanLocation(
                stderr,
                CompilerDiag.relatedHeading(),
                located.info,
                located.span,
            );
        }
    }

    fn sourceInfo(
        self: *const DiagnosticSink,
        source: DiagnosticSource,
    ) ?SourceInfo {
        return switch (source) {
            .mm0 => .{
                .label = "source",
                .text = self.source,
            },
            .proof => .{
                .label = "proof",
                .text = self.proof_source orelse return null,
            },
        };
    }

    const LocatedSpan = struct {
        info: SourceInfo,
        span: Span,
    };

    /// The text and label a span should be reported against: the joined
    /// file it came from when a mapping is set, else the whole source.
    fn locateSpan(
        self: *const DiagnosticSink,
        source: DiagnosticSource,
        span: Span,
    ) ?LocatedSpan {
        if (self.mapping(source)) |m| {
            if (m.locateSpan(.{ .start = span.start, .end = span.end })) |hit| {
                return .{
                    .info = .{ .label = hit.label, .text = hit.text },
                    .span = .{ .start = hit.span.start, .end = hit.span.end },
                };
            }
        }
        const info = self.sourceInfo(source) orelse return null;
        return .{ .info = info, .span = span };
    }

    pub fn setDiagnostic(self: *DiagnosticSink, diag: Diagnostic) void {
        self.last_diagnostic = self.stableDiagnostic(diag);
    }

    pub fn setIfMissing(self: *DiagnosticSink, diag: Diagnostic) void {
        if (self.getDiagnostic() != null) return;
        self.setDiagnostic(diag);
    }

    pub fn setProof(self: *DiagnosticSink, diag: Diagnostic) void {
        var proof_diag = diag;
        proof_diag.source = .proof;
        self.setDiagnostic(proof_diag);
    }

    pub fn maybeSetProof(self: *DiagnosticSink, diag: Diagnostic) void {
        self.setProof(diag);
    }

    pub fn getDiagnostic(self: *const DiagnosticSink) ?Diagnostic {
        return self.last_diagnostic;
    }

    pub fn restoreDiagnostic(
        self: *DiagnosticSink,
        diag: ?Diagnostic,
    ) void {
        self.last_diagnostic = diag;
    }

    fn stableDiagnostic(self: *DiagnosticSink, diag: Diagnostic) Diagnostic {
        var stable = diag;
        stable.theorem_name = self.stableString(diag.theorem_name);
        stable.block_name = self.stableString(diag.block_name);
        stable.line_label = self.stableString(diag.line_label);
        stable.rule_name = self.stableString(diag.rule_name);
        stable.name = self.stableString(diag.name);
        stable.expected_name = self.stableString(diag.expected_name);
        stable.detail = self.stableDiagnosticDetail(diag.detail);
        for (diag.noteSlice(), 0..) |note, idx| {
            stable.notes[idx] = .{
                .message = self.stableNoteMessage(note.message),
                .source = note.source,
                .span = note.span,
            };
        }
        for (diag.relatedSlice(), 0..) |related, idx| {
            stable.related[idx] = related;
        }
        return stable;
    }

    /// Stable-copies every string payload field of a note message, so new
    /// `NoteMessage` variants get the copy for free.
    fn stableNoteMessage(
        self: *DiagnosticSink,
        message: CompilerDiag.NoteMessage,
    ) CompilerDiag.NoteMessage {
        switch (message) {
            inline else => |payload, tag| {
                const Payload = @TypeOf(payload);
                if (Payload == void) return message;
                var stable_payload = payload;
                const info = @typeInfo(Payload).@"struct";
                inline for (info.field_names, info.field_types) |name, field_type| {
                    if (field_type == []const u8) {
                        @field(stable_payload, name) =
                            self.stableRequiredString(
                                @field(payload, name),
                            );
                    }
                }
                return @unionInit(
                    CompilerDiag.NoteMessage,
                    @tagName(tag),
                    stable_payload,
                );
            },
        }
    }

    fn stableDiagnosticDetail(
        self: *DiagnosticSink,
        detail: DiagnosticDetail,
    ) DiagnosticDetail {
        return switch (detail) {
            .none => .none,
            .omitted_diagnostics => |info| .{ .omitted_diagnostics = info },
            .proof_heap => |info| .{ .proof_heap = info },
            .unknown_math_token => |info| .{ .unknown_math_token = .{
                .token = self.stableRequiredString(info.token),
            } },
            .name_suggestion => |info| .{ .name_suggestion = .{
                .suggestion = self.stableRequiredString(info.suggestion),
            } },
            .missing_binder_assignment => |info| .{
                .missing_binder_assignment = .{
                    .binder_name = self.stableRequiredString(info.binder_name),
                    .path = info.path,
                },
            },
            .inference_failure => |info| .{ .inference_failure = .{
                .path = info.path,
                .first_unsolved_binder_name = self.stableString(
                    info.first_unsolved_binder_name,
                ),
            } },
            .dep_violation => |info| .{ .dep_violation = .{
                .first_arg_idx = info.first_arg_idx,
                .second_arg_idx = info.second_arg_idx,
                .first_arg_name = self.stableString(info.first_arg_name),
                .second_arg_name = self.stableString(info.second_arg_name),
                .first_deps = info.first_deps,
                .second_deps = info.second_deps,
                .first_bound = info.first_bound,
                .second_bound = info.second_bound,
                .first_rule_bound = info.first_rule_bound,
                .second_rule_bound = info.second_rule_bound,
                .first_binding_text = self.stableString(
                    info.first_binding_text,
                ),
                .second_binding_text = self.stableString(
                    info.second_binding_text,
                ),
            } },
            .definition_body => |info| .{ .definition_body = .{
                .declared_sort_name = self.stableRequiredString(
                    info.declared_sort_name,
                ),
                .actual_sort_name = self.stableRequiredString(
                    info.actual_sort_name,
                ),
                .body_deps = info.body_deps,
                .hidden_binder_count = info.hidden_binder_count,
            } },
            .missing_congruence_rule => |info| .{ .missing_congruence_rule = .{
                .reason = info.reason,
                .term_name = self.stableString(info.term_name),
                .sort_name = self.stableString(info.sort_name),
                .arg_index = info.arg_index,
            } },
            .hypothesis_ref => |info| .{ .hypothesis_ref = .{
                .index = info.index,
                .name = self.stableString(info.name),
            } },
            .premise_mismatch => |info| .{ .premise_mismatch = .{
                .premise = info.premise,
                .hypothesis_index = info.hypothesis_index,
                .hypothesis_name = self.stableString(info.hypothesis_name),
            } },
            .unused_parameter => |info| .{ .unused_parameter = .{
                .parameter_name = self.stableRequiredString(
                    info.parameter_name,
                ),
            } },
            .rewrite_cycle => |info| .{ .rewrite_cycle = .{
                .rule_name = self.stableRequiredString(info.rule_name),
            } },
            .rewrite_step_limit => |info| .{ .rewrite_step_limit = .{
                .rule_name = self.stableRequiredString(info.rule_name),
            } },
            .local_term_reference => |info| .{ .local_term_reference = .{
                .term_name = self.stableRequiredString(info.term_name),
            } },
            .expected_char => |info| .{ .expected_char = info },
        };
    }

    fn stableString(
        self: *DiagnosticSink,
        value: ?[]const u8,
    ) ?[]const u8 {
        const actual = value orelse return null;
        return self.stableRequiredString(actual);
    }

    fn stableRequiredString(
        self: *DiagnosticSink,
        value: []const u8,
    ) []const u8 {
        if (self.isStableSourceSlice(value)) return value;
        const remaining = diagnostic_storage_size - self.diagnostic_storage_len;
        if (value.len > remaining) return truncated_diagnostic_string;

        const start = self.diagnostic_storage_len;
        const end = start + value.len;
        @memcpy(self.diagnostic_storage[start..end], value);
        self.diagnostic_storage_len = end;
        return self.diagnostic_storage[start..end];
    }

    fn isStableSourceSlice(
        self: *const DiagnosticSink,
        value: []const u8,
    ) bool {
        if (isSubslice(self.source, value)) return true;
        if (self.proof_source) |proof_source| {
            if (isSubslice(proof_source, value)) return true;
        }
        return false;
    }

    fn droppedPrimaryDiagnosticCount(
        self: *const DiagnosticSink,
        source: DiagnosticSource,
    ) usize {
        return switch (source) {
            .mm0 => self.dropped_mm0_primary_diagnostic_count,
            .proof => self.dropped_proof_primary_diagnostic_count,
        };
    }
};

fn writeSpanLocation(
    stderr: *std.Io.Writer,
    prefix: []const u8,
    source_info: SourceInfo,
    span: Span,
) std.Io.Writer.Error!void {
    const info = lineCol(source_info.text, span.start);
    const line = source_info.text[info.line_start..info.line_end];

    if (prefix.len == 0) {
        try stderr.print(
            "  --> {s}:{d}:{d}\n",
            .{ source_info.label, info.line, info.column },
        );
    } else {
        try stderr.print(
            "  {s} --> {s}:{d}:{d}\n",
            .{ prefix, source_info.label, info.line, info.column },
        );
    }
    try stderr.print("  | {s}\n", .{line});
    try stderr.writeAll("  | ");

    const caret_start = span.start - info.line_start;
    const caret_end = if (span.end > span.start)
        @min(span.end, info.line_end)
    else
        @min(span.start + 1, info.line_end);
    const caret_len = @max(caret_end - span.start, 1);

    try stderr.splatByteAll(' ', caret_start);
    try stderr.splatByteAll('^', caret_len);
    try stderr.writeByte('\n');
}

const SourceInfo = struct {
    label: []const u8,
    text: []const u8,
};

const LineCol = struct {
    line: usize,
    column: usize,
    line_start: usize,
    line_end: usize,
};

fn isSubslice(owner: []const u8, value: []const u8) bool {
    const owner_start = @intFromPtr(owner.ptr);
    const owner_end = owner_start + owner.len;
    const value_start = @intFromPtr(value.ptr);
    const value_end = value_start + value.len;
    return value_start >= owner_start and value_end <= owner_end;
}

fn lineCol(src: []const u8, pos_raw: usize) LineCol {
    const pos = @min(pos_raw, src.len);
    var line: usize = 1;
    var column: usize = 1;
    var line_start: usize = 0;
    var i: usize = 0;

    while (i < pos) : (i += 1) {
        if (src[i] == '\n') {
            line += 1;
            column = 1;
            line_start = i + 1;
        } else {
            column += 1;
        }
    }

    var line_end = line_start;
    while (line_end < src.len and src[line_end] != '\n') : (line_end += 1) {}

    return .{
        .line = line,
        .column = column,
        .line_start = line_start,
        .line_end = line_end,
    };
}
