//! Fuzz target: proof search on markers put in place of real proofs.
//!
//! A proof case that compiles and verifies cleanly has the justifications
//! of up to three of its proof steps (whole lines or inline sub-proofs)
//! replaced by `auto?`, `exact?`, `apply?` or `conversion?`, and the
//! search driver behind `abc search` runs on it with a small work budget.
//! The search must not panic, leak, hang or run away with memory, and
//! must not fail; it must trim every suggestion it returns; and putting
//! each found proof in its marker's place (and the original proofs back
//! on a line where a marker found none) must give a file that compiles
//! and verifies.
//! Steps on lines with holes are left alone: a search there may fill the
//! holes differently, which breaks the lines that rely on them.
const std = @import("std");
const mm0 = @import("mm0");
const harness = @import("harness.zig");

const ProofScript = mm0.ProofScript;
const SearchDriver = mm0.CompilerSupport.SearchDriver;

const max_markers = 3;
const markers = [_][]const u8{ "auto?", "exact?", "apply?", "conversion?" };

/// A proof step to replace, in the original proof text.
const Step = struct {
    span: ProofScript.Span,
    /// Where its proof line starts.
    line: usize,
};

fn search(seeds: []const harness.Seed, input: harness.Input) !void {
    const gpa = input.gpa;
    const smith = input.smith;
    const index = smith.index(seeds.len);
    if (try harness.compiledSeed(seeds, index) == null) return;
    const seed = seeds[index];

    var arena: std.heap.ArenaAllocator = .init(gpa);
    defer arena.deinit();
    const steps = try proofSteps(arena.allocator(), seed.mm0, seed.auf);
    if (steps.len == 0) return;

    // Up to `max_markers` steps that do not overlap, in source order.
    var chosen: std.ArrayList(Step) = .empty;
    const wanted = smith.valueRangeAtMost(u8, 1, max_markers);
    for (0..wanted) |_| {
        const step = steps[smith.index(steps.len)];
        for (chosen.items) |other| {
            if (step.span.start < other.span.end and other.span.start < step.span.end) break;
        } else try chosen.append(arena.allocator(), step);
    }
    std.mem.sort(Step, chosen.items, {}, struct {
        fn before(_: void, a: Step, b: Step) bool {
            return a.span.start < b.span.start;
        }
    }.before);

    // The proof text with the markers, and where each marker went.
    var text: std.ArrayList(u8) = .empty;
    const placed = try arena.allocator().alloc(Placed, chosen.items.len);
    var copied: usize = 0;
    for (chosen.items, placed) |step, *place| {
        try text.appendSlice(arena.allocator(), seed.auf[copied..step.span.start]);
        const marker = markers[smith.index(markers.len)];
        place.* = .{
            .at = text.items.len,
            .original = seed.auf[step.span.start..step.span.end],
            .line = step.line,
        };
        try text.appendSlice(arena.allocator(), marker);
        copied = step.span.end;
    }
    try text.appendSlice(arena.allocator(), seed.auf[copied..]);
    input.dump("case.mm0", seed.mm0);
    input.dump("case.auf", text.items);

    const zero: ProofScript.Span = .{ .start = 0, .end = 0 };
    const params = [_]ProofScript.SearchParam{
        .{ .name = "depth", .name_span = zero, .value = smith.valueRangeAtMost(u8, 1, 4), .value_span = zero, .span = zero },
        .{ .name = "budget", .name_span = zero, .value = 1, .value_span = zero, .span = zero },
    };
    var result = try SearchDriver.run(gpa, seed.mm0, text.items, .{ .params = &params });
    defer result.deinit();

    for (result.markers) |marker| {
        if (marker.outcome == .failed)
            fail(seed, "{s}:{s}: the search failed: {?t}", .{ marker.theorem, marker.label, marker.failure });
        if (marker.cost.untrimmed != 0)
            fail(seed, "{s}:{s}: {d} suggestions came back untrimmed", .{ marker.theorem, marker.label, marker.cost.untrimmed });
    }

    // Each found proof in its marker's place, the original elsewhere. The
    // driver puts a found proof in place before it searches the next
    // marker, so a sibling marker on the line was searched against the
    // rule variables the found proof fixed, and the original may not fit
    // them: a line with any marker not found gets all its originals back.
    const marker_places = try arena.allocator().alloc(*const Placed, result.markers.len);
    for (result.markers, marker_places) |marker, *marker_place| {
        marker_place.* = for (placed) |*place| {
            if (place.at == marker.span.start) break place;
        } else return; // Not a marker this target placed; nothing to check.
        if (marker.outcome == .found and marker.edit == null) return;
    }
    var filled: std.ArrayList(u8) = .empty;
    try filled.appendSlice(arena.allocator(), text.items);
    var i = result.markers.len;
    while (i > 0) {
        i -= 1;
        const marker = result.markers[i];
        const place = marker_places[i];
        const line_found = for (result.markers, marker_places) |other, other_place| {
            if (other_place.line == place.line and other.outcome != .found) break false;
        } else true;
        const edit: SearchDriver.Edit = if (line_found)
            marker.edit.?
        else
            .{ .span = marker.span, .text = place.original };
        try filled.replaceRange(arena.allocator(), edit.span.start, edit.span.end - edit.span.start, edit.text);
    }
    input.dump("filled.auf", filled.items);

    var compiler = mm0.Compiler.initWithProof(gpa, seed.mm0, filled.items);
    const mmb = compiler.compileMmb(gpa) catch |err| {
        if (err == error.OutOfMemory) return err;
        fail(seed, "the found proofs do not compile: {t}", .{err});
    };
    defer gpa.free(mmb);
    mm0.verifyPair(gpa, seed.mm0, mmb) catch |err| {
        if (err == error.OutOfMemory) return err;
        fail(seed, "the found proofs do not verify: {t}", .{err});
    };
}

const Placed = struct {
    /// Where the marker starts in the proof text with markers.
    at: usize,
    /// The proof step it replaced.
    original: []const u8,
    /// Where the step's proof line starts in the original proof text.
    line: usize,
};

/// The span of every proof step in `auf` on a line without holes: the
/// line's rule application and each inline sub-proof, nested ones
/// included.
fn proofSteps(arena: std.mem.Allocator, mm0_src: []const u8, auf: []const u8) ![]const Step {
    const holes = try holeTokens(arena, mm0_src);
    var steps: std.ArrayList(Step) = .empty;
    var parser = ProofScript.Parser.init(arena, auf);
    while (parser.nextItem() catch return steps.items) |item| switch (item) {
        .block => |block| for (block.lines) |line| {
            if (!mentionsAny(line.assertion.text, holes)) try collect(arena, &steps, line.span.start, line.application);
        },
        .def, .notation => {},
    };
    return steps.items;
}

/// The tokens `@hole` declares in `mm0_src`.
fn holeTokens(arena: std.mem.Allocator, mm0_src: []const u8) ![]const []const u8 {
    var tokens: std.ArrayList([]const u8) = .empty;
    var rest = mm0_src;
    while (std.mem.indexOf(u8, rest, "@hole")) |at| {
        rest = std.mem.trimStart(u8, rest[at + "@hole".len ..], " \t");
        const end = std.mem.indexOfAny(u8, rest, " \t\r\n") orelse rest.len;
        if (end != 0) try tokens.append(arena, rest[0..end]);
        rest = rest[end..];
    }
    return tokens.items;
}

fn mentionsAny(text: []const u8, tokens: []const []const u8) bool {
    for (tokens) |token| {
        if (std.mem.indexOf(u8, text, token) != null) return true;
    }
    return false;
}

fn collect(arena: std.mem.Allocator, steps: *std.ArrayList(Step), line: usize, application: ProofScript.RuleApplication) !void {
    try steps.append(arena, .{ .span = application.span, .line = line });
    for (application.refs) |ref| switch (ref) {
        .application => |child| try collect(arena, steps, line, child),
        .hyp, .line => {},
    };
}

fn fail(seed: harness.Seed, comptime format: []const u8, args: anytype) noreturn {
    std.debug.print("seed {s}: " ++ format ++ "\n", .{seed.stem} ++ args);
    @panic("search oracle failed");
}

test "fuzz proof search" {
    try harness.run("search", .{ .time_limit_s = 30 }, try harness.seeds(), search);
}
