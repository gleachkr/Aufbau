//! What a check found for the holes of a proof text: hovers and fills.

const std = @import("std");
const Analyze = @import("../compiler/pipeline/analyze.zig");
const ArenaAllocator = @import("../arena_allocator.zig").ArenaAllocator;
const Context = @import("../compiler/context.zig");
const DiagnosticSink = @import("../compiler/diagnostic_sink.zig").DiagnosticSink;
const ProofBlock = @import("../proof_script.zig").ProofBlock;
const Span = @import("../proof_script.zig").Span;
const markdown = @import("markdown.zig");
const HoverResult = @import("types.zig").HoverResult;

const CompilerContext = Context.CompilerContext;
const HoleInferenceSink = Context.HoleInferenceSink;

/// What is to be written over a holey line's assertion.
pub const HoleFill = struct {
    /// The assertion's math string, `$` delimiters included.
    assertion: Span,
    /// The math string to put in its place, delimiters included.
    replacement: []const u8,
};

/// The holes of `block`, a block of `proof_src`, as an analysis finds them.
/// Only its own proof is checked: no check depends on another proof.
pub fn ofBlock(
    allocator: std.mem.Allocator,
    mm0_src: []const u8,
    proof_src: []const u8,
    block: ProofBlock,
) std.mem.Allocator.Error!HoleInferenceSink {
    var work_arena = ArenaAllocator.init(allocator);
    defer work_arena.deinit();
    const work = work_arena.allocator();
    var found: HoleInferenceSink = .{ .allocator = allocator };
    errdefer found.deinit();

    var walk_diagnostics = DiagnosticSink.init(mm0_src, proof_src);
    var walk = CompilerContext.init(mm0_src, proof_src, .none, &walk_diagnostics);
    var point = Analyze.analyzeToBlock(&walk, work, block) catch |err| switch (err) {
        error.OutOfMemory => return error.OutOfMemory,
        else => return found,
    };

    var diagnostics = DiagnosticSink.init(mm0_src, proof_src);
    var context = CompilerContext.init(mm0_src, proof_src, .none, &diagnostics);
    context.hole_inference_sink = &found;
    // Past a line that fails, as an analysis. Which failures it would report
    // does not matter here.
    const no_rules = std.StringHashMap(void).init(work);
    context.keep_checking = .{ .invalid_rules = &no_rules };
    point.check(&context, work, block) catch |err| switch (err) {
        error.OutOfMemory => return error.OutOfMemory,
        else => {},
    };
    return found;
}

/// The value of the hole at `offset`, if `found` has one.
pub fn hoverAt(
    allocator: std.mem.Allocator,
    found: *const HoleInferenceSink,
    offset: usize,
) !?HoverResult {
    for (found.items.items) |item| {
        if (offset < item.span.start or offset >= item.span.end) continue;
        return .{
            .range = .{
                .document = .proof,
                .start = item.span.start,
                .end = item.span.end,
            },
            .markdown = try markdown.inferredHoleMarkdown(
                allocator,
                item.expression,
                item.partial,
            ),
        };
    }
    return null;
}

/// The fill for the holey line of `proof_text` that takes `offset`, if its
/// filled assertion can be written in the proof.
pub fn fillAt(
    allocator: std.mem.Allocator,
    found: *const HoleInferenceSink,
    proof_text: []const u8,
    offset: usize,
) !?HoleFill {
    for (found.assertions.items) |filled| {
        if (!lineTakes(filled.line, offset, proof_text)) continue;
        return .{
            .assertion = filled.assertion,
            .replacement = try std.fmt.allocPrint(allocator, "$ {s} $", .{filled.text}),
        };
    }
    return null;
}

/// Whether `offset` is on `line`. A line's span ends past its newline, so
/// only a line ending the text also takes the offset just past its end.
pub fn lineTakes(line: Span, offset: usize, proof_text: []const u8) bool {
    if (offset < line.start) return false;
    return offset < line.end or (offset == line.end and offset == proof_text.len);
}
