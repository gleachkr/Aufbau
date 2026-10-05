//! JSON rendering of structured diagnostic fields shared by the wasm
//! frontend. Lives outside `wasm.zig` (which only builds for wasm32) so the
//! exhaustive `DiagnosticDetail` switch is analyzed by the native unit-test
//! build: adding a detail variant without a JSON rendering fails
//! `zig build test-unit` instead of surfacing later in the web-demo build.
const std = @import("std");
const mm0 = @import("mm0");

/// Write each field of `fields` into the object `jw` has open.
pub fn writeFields(jw: *std.json.Stringify, fields: anytype) !void {
    inline for (@typeInfo(@TypeOf(fields)).@"struct".fields) |field| {
        try jw.objectField(field.name);
        try jw.write(@field(fields, field.name));
    }
}

/// `diag.detail`: null, or an object whose `kind` is the detail's tag.
pub fn writeDetail(
    jw: *std.json.Stringify,
    gpa: std.mem.Allocator,
    diag: mm0.CompilerDiagnostic,
) !void {
    if (diag.detail == .none) return jw.write(null);
    var summary: std.Io.Writer.Allocating = .init(gpa);
    defer summary.deinit();

    try jw.beginObject();
    try writeFields(jw, .{ .kind = @tagName(diag.detail) });
    switch (diag.detail) {
        .none => unreachable,
        .omitted_diagnostics => |info| {
            try mm0.writeCompilerOmittedDiagnosticsSummary(&summary.writer, info.count);
            try writeFields(jw, .{
                .summary = summary.written(),
                .count = info.count,
            });
        },
        .unknown_math_token => |info| try writeFields(jw, .{ .token = info.token }),
        .name_suggestion => |info| try writeFields(jw, .{ .suggestion = info.suggestion }),
        .expected_char => |info| try writeFields(jw, .{ .expected = &[1]u8{info.ch} }),
        .missing_binder_assignment => |info| try writeFields(jw, .{
            .binder = info.binder_name,
            .path = info.path,
        }),
        .inference_failure => |info| try writeFields(jw, .{
            .path = info.path,
            .firstUnsolvedBinder = info.first_unsolved_binder_name,
        }),
        .dep_violation => |info| {
            try mm0.writeCompilerDepViolationSummary(&summary.writer, info);
            try writeFields(jw, .{
                .summary = summary.written(),
                .firstArgName = info.first_arg_name,
                .secondArgName = info.second_arg_name,
                .firstArgIndex = info.first_arg_idx,
                .secondArgIndex = info.second_arg_idx,
                .firstDeps = info.first_deps,
                .secondDeps = info.second_deps,
                .firstBound = info.first_bound,
                .secondBound = info.second_bound,
                .firstAssigned = info.first_binding_text,
                .secondAssigned = info.second_binding_text,
            });
        },
        .definition_body => |info| try writeFields(jw, .{
            .summary = mm0.compilerDiagnosticSummary(diag),
            .declaredSort = info.declared_sort_name,
            .actualSort = info.actual_sort_name,
            .bodyDeps = info.body_deps,
            .hiddenBinderCount = info.hidden_binder_count,
        }),
        .missing_congruence_rule => |info| {
            try mm0.writeCompilerMissingCongruenceRuleSummary(&summary.writer, info);
            try writeFields(jw, .{
                .reason = info.reason,
                .summary = summary.written(),
                .term = info.term_name,
                .sort = info.sort_name,
                .argIndex = info.arg_index,
            });
        },
        .hypothesis_ref => |info| try writeFields(jw, .{
            .index = info.index,
            .name = info.name,
        }),
        .unused_parameter => |info| try writeFields(jw, .{ .parameter = info.parameter_name }),
        .local_term_reference => |info| try writeFields(jw, .{ .term = info.term_name }),
    }
    try jw.endObject();
}

/// `diag`'s detail, parsed back from the JSON `writeDetail` makes.
fn parseDetail(diag: mm0.CompilerDiagnostic) !std.json.Parsed(std.json.Value) {
    var out: std.Io.Writer.Allocating = .init(std.testing.allocator);
    defer out.deinit();
    var jw: std.json.Stringify = .{ .writer = &out.writer };
    try writeDetail(&jw, std.testing.allocator, diag);
    return std.json.parseFromSlice(
        std.json.Value,
        std.testing.allocator,
        out.written(),
        .{},
    );
}

// The value of this test is that it *instantiates* `writeDetail`, which
// analyzes every switch arm natively: a `DiagnosticDetail` variant without a
// rendering fails here rather than in the wasm-only web-demo build.
test "detail renders as parseable JSON with its source token escaped" {
    var parsed = try parseDetail(.{
        .kind = .generic,
        .err = error.AbstractConflict,
        .detail = .{ .unknown_math_token = .{ .token = "t\\p\"\x01" } },
    });
    defer parsed.deinit();

    const detail = parsed.value.object;
    try std.testing.expectEqualStrings("unknown_math_token", detail.get("kind").?.string);
    try std.testing.expectEqualStrings("t\\p\"\x01", detail.get("token").?.string);
}

test "none detail renders as null" {
    var parsed = try parseDetail(.{
        .kind = .generic,
        .err = error.AbstractConflict,
    });
    defer parsed.deinit();

    try std.testing.expect(parsed.value == .null);
}
