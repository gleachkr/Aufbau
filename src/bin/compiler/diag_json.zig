//! JSON rendering of structured diagnostic fields shared by the wasm
//! frontend. Lives outside `wasm.zig` (which only builds for wasm32) so the
//! exhaustive `DiagnosticDetail` switch is analyzed by the native unit-test
//! build: adding a detail variant without a JSON rendering fails
//! `zig build test-unit` instead of surfacing later in the web-demo build.
const std = @import("std");
const mm0 = @import("mm0");
const json_out = @import("json_out.zig");

pub fn writeOptionalUsizeField(
    writer: anytype,
    name: []const u8,
    value: anytype,
) !void {
    try writer.print("\"{s}\":", .{name});
    switch (@typeInfo(@TypeOf(value))) {
        .optional => {
            if (value) |actual| {
                try writer.print("{d}", .{actual});
            } else {
                try writer.writeAll("null");
            }
        },
        else => {
            try writer.print("{d}", .{value});
        },
    }
}

pub fn phaseName(phase: mm0.CompilerDiagnosticPhase) []const u8 {
    return switch (phase) {
        .parse => "parse",
        .inference => "inference",
        .theorem_application => "theorem_application",
        .freshen => "freshen",
        .normalization => "normalization",
        .final_reconciliation => "final_reconciliation",
    };
}

pub fn writeDetailField(
    writer: anytype,
    diag: mm0.CompilerDiagnostic,
) !void {
    const writeJsonStringField = json_out.writeStringField;
    const writeOptionalStringField = json_out.writeOptionalStringField;
    try writer.writeAll("\"detail\":");
    switch (diag.detail) {
        .none => try writer.writeAll("null"),
        .omitted_diagnostics => |info| {
            try writer.writeAll("{");
            try writeJsonStringField(
                writer,
                "kind",
                "omitted_diagnostics",
            );
            try writer.writeByte(',');
            try writer.writeAll("\"summary\":\"");
            try mm0.writeCompilerOmittedDiagnosticsSummary(
                writer,
                info.count,
            );
            try writer.writeByte('"');
            try writer.writeByte(',');
            try writer.print("\"count\":{d}", .{info.count});
            try writer.writeAll("}");
        },
        .unknown_math_token => |info| {
            try writer.writeAll("{");
            try writeJsonStringField(writer, "kind", "unknown_math_token");
            try writer.writeByte(',');
            try writeJsonStringField(writer, "token", info.token);
            try writer.writeAll("}");
        },
        .name_suggestion => |info| {
            try writer.writeAll("{");
            try writeJsonStringField(writer, "kind", "name_suggestion");
            try writer.writeByte(',');
            try writeJsonStringField(writer, "suggestion", info.suggestion);
            try writer.writeAll("}");
        },
        .expected_char => |info| {
            try writer.writeAll("{");
            try writeJsonStringField(writer, "kind", "expected_char");
            try writer.writeByte(',');
            try writeJsonStringField(writer, "expected", &[1]u8{info.ch});
            try writer.writeAll("}");
        },
        .missing_binder_assignment => |info| {
            try writer.writeAll("{");
            try writeJsonStringField(
                writer,
                "kind",
                "missing_binder_assignment",
            );
            try writer.writeByte(',');
            try writeJsonStringField(writer, "binder", info.binder_name);
            try writer.writeByte(',');
            try writeJsonStringField(
                writer,
                "path",
                @tagName(info.path),
            );
            try writer.writeAll("}");
        },
        .inference_failure => |info| {
            try writer.writeAll("{");
            try writeJsonStringField(writer, "kind", "inference_failure");
            try writer.writeByte(',');
            try writeJsonStringField(writer, "path", @tagName(info.path));
            try writer.writeByte(',');
            try writeOptionalStringField(
                writer,
                "firstUnsolvedBinder",
                info.first_unsolved_binder_name,
            );
            try writer.writeAll("}");
        },
        .dep_violation => |info| {
            try writer.writeAll("{");
            try writeJsonStringField(writer, "kind", "dep_violation");
            try writer.writeByte(',');
            try writer.writeAll("\"summary\":\"");
            try mm0.writeCompilerDepViolationSummary(writer, info);
            try writer.writeByte('"');
            try writer.writeByte(',');
            try writeOptionalStringField(
                writer,
                "firstArgName",
                info.first_arg_name,
            );
            try writer.writeByte(',');
            try writeOptionalStringField(
                writer,
                "secondArgName",
                info.second_arg_name,
            );
            try writer.writeByte(',');
            try writeOptionalUsizeField(
                writer,
                "firstArgIndex",
                info.first_arg_idx,
            );
            try writer.writeByte(',');
            try writeOptionalUsizeField(
                writer,
                "secondArgIndex",
                info.second_arg_idx,
            );
            try writer.writeByte(',');
            try writeOptionalUsizeField(
                writer,
                "firstDeps",
                info.first_deps,
            );
            try writer.writeByte(',');
            try writeOptionalUsizeField(
                writer,
                "secondDeps",
                info.second_deps,
            );
            try writer.writeByte(',');
            try writer.print("\"firstBound\":{}", .{info.first_bound});
            try writer.writeByte(',');
            try writer.print("\"secondBound\":{}", .{info.second_bound});
            try writer.writeByte(',');
            try writeOptionalStringField(
                writer,
                "firstAssigned",
                info.first_binding_text,
            );
            try writer.writeByte(',');
            try writeOptionalStringField(
                writer,
                "secondAssigned",
                info.second_binding_text,
            );
            try writer.writeAll("}");
        },
        .definition_body => |info| {
            try writer.writeAll("{");
            try writeJsonStringField(writer, "kind", "definition_body");
            try writer.writeByte(',');
            try writeJsonStringField(
                writer,
                "summary",
                mm0.compilerDiagnosticSummary(diag),
            );
            try writer.writeByte(',');
            try writeJsonStringField(
                writer,
                "declaredSort",
                info.declared_sort_name,
            );
            try writer.writeByte(',');
            try writeJsonStringField(
                writer,
                "actualSort",
                info.actual_sort_name,
            );
            try writer.writeByte(',');
            try writeOptionalUsizeField(writer, "bodyDeps", info.body_deps);
            try writer.writeByte(',');
            try writer.print(
                "\"hiddenBinderCount\":{d}",
                .{info.hidden_binder_count},
            );
            try writer.writeAll("}");
        },
        .missing_congruence_rule => |info| {
            try writer.writeAll("{");
            try writeJsonStringField(
                writer,
                "kind",
                "missing_congruence_rule",
            );
            try writer.writeByte(',');
            try writeJsonStringField(
                writer,
                "reason",
                @tagName(info.reason),
            );
            try writer.writeByte(',');
            try writer.writeAll("\"summary\":\"");
            try mm0.writeCompilerMissingCongruenceRuleSummary(writer, info);
            try writer.writeByte('"');
            try writer.writeByte(',');
            try writeOptionalStringField(writer, "term", info.term_name);
            try writer.writeByte(',');
            try writeOptionalStringField(writer, "sort", info.sort_name);
            try writer.writeByte(',');
            try writeOptionalUsizeField(writer, "argIndex", info.arg_index);
            try writer.writeAll("}");
        },
        .hypothesis_ref => |info| {
            try writer.writeAll("{");
            try writeJsonStringField(writer, "kind", "hypothesis_ref");
            try writer.writeByte(',');
            try writer.writeAll("\"index\":");
            try writer.print("{d}", .{info.index});
            try writer.writeByte(',');
            try writeOptionalStringField(writer, "name", info.name);
            try writer.writeAll("}");
        },
        .unused_parameter => |info| {
            try writer.writeAll("{");
            try writeJsonStringField(writer, "kind", "unused_parameter");
            try writer.writeByte(',');
            try writeJsonStringField(
                writer,
                "parameter",
                info.parameter_name,
            );
            try writer.writeAll("}");
        },
    }
}

// The value of this test is that it *instantiates* `writeDetailField`, which
// analyzes every switch arm natively: a `DiagnosticDetail` variant without a
// rendering fails here rather than in the wasm-only web-demo build.
test "detail field renders as parseable JSON for every carrier" {
    const allocator = std.testing.allocator;

    var out: std.io.Writer.Allocating = .init(allocator);
    defer out.deinit();

    const diag = mm0.CompilerDiagnostic{
        .kind = .generic,
        .err = error.AbstractConflict,
        .detail = .{ .unknown_math_token = .{ .token = "t\\p" } },
    };

    try out.writer.writeByte('{');
    try writeDetailField(&out.writer, diag);
    try out.writer.writeByte('}');

    var parsed = try std.json.parseFromSlice(
        std.json.Value,
        allocator,
        out.written(),
        .{},
    );
    defer parsed.deinit();

    const detail = parsed.value.object.get("detail").?;
    try std.testing.expectEqualStrings(
        "unknown_math_token",
        detail.object.get("kind").?.string,
    );
    try std.testing.expectEqualStrings(
        "t\\p",
        detail.object.get("token").?.string,
    );
}

test "none detail renders as null" {
    const allocator = std.testing.allocator;

    var out: std.io.Writer.Allocating = .init(allocator);
    defer out.deinit();

    const diag = mm0.CompilerDiagnostic{
        .kind = .generic,
        .err = error.AbstractConflict,
    };

    try out.writer.writeByte('{');
    try writeDetailField(&out.writer, diag);
    try out.writer.writeByte('}');

    var parsed = try std.json.parseFromSlice(
        std.json.Value,
        allocator,
        out.written(),
        .{},
    );
    defer parsed.deinit();

    try std.testing.expect(parsed.value.object.get("detail").? == .null);
}
