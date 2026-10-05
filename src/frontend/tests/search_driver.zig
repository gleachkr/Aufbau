const std = @import("std");
const mm0 = @import("mm0");

const SearchDriver = mm0.CompilerSupport.SearchDriver;

const test_mm0 =
    \\delimiter $ ( ) $;
    \\provable sort wff;
    \\--| @hole _A
    \\sort ty;
    \\term o: ty;
    \\term isty (A: ty): wff;
    \\term P: wff;
    \\term Q: wff;
    \\term R: wff;
    \\axiom p: $ P $;
    \\axiom use: $ P $ > $ Q $;
    \\axiom both: $ P $ > $ Q $ > $ R $;
    \\axiom o_ty: $ isty o $;
    \\theorem t1: $ R $;
    \\theorem t2: $ R $;
    \\theorem t3: $ isty o $;
;

fn run(proof_src: []const u8) !SearchDriver.Result {
    return runWith(proof_src, .{});
}

fn runWith(proof_src: []const u8, options: SearchDriver.Options) !SearchDriver.Result {
    return SearchDriver.run(std.testing.allocator, test_mm0, proof_src, options);
}

/// `proof_src` with every marker's edits made, as `--fill` makes them.
fn applyEdits(
    proof_src: []const u8,
    markers: []const SearchDriver.Marker,
) ![]u8 {
    var edits = std.ArrayListUnmanaged(SearchDriver.Edit){};
    defer edits.deinit(std.testing.allocator);
    for (markers) |marker| {
        if (marker.filled_assertion) |edit| {
            try edits.append(std.testing.allocator, edit);
        }
        if (marker.edit) |edit| try edits.append(std.testing.allocator, edit);
    }
    var text = std.ArrayListUnmanaged(u8){};
    errdefer text.deinit(std.testing.allocator);
    var at: usize = 0;
    for (edits.items) |edit| {
        try std.testing.expect(edit.span.start >= at);
        try text.appendSlice(std.testing.allocator, proof_src[at..edit.span.start]);
        try text.appendSlice(std.testing.allocator, edit.text);
        at = edit.span.end;
    }
    try text.appendSlice(std.testing.allocator, proof_src[at..]);
    return text.toOwnedSlice(std.testing.allocator);
}

test "search driver puts each find in place for the markers after it" {
    const proof_src =
        \\t1
        \\---
        \\l1: $ P $ by exact?
        \\l2: $ Q $ by use [exact?]
        \\l3: $ R $ by auto?
        \\
        \\t2
        \\---
        \\l1: $ R $ by both [p [], use [p []]]
        \\
        \\t3
        \\---
        \\l1: $ isty o $ by o_ty
    ;
    var result = try run(proof_src);
    defer result.deinit();

    try std.testing.expectEqual(@as(usize, 3), result.markers.len);
    for (result.markers) |marker| {
        try std.testing.expectEqual(.found, marker.outcome);
    }
    try std.testing.expectEqualStrings("p", result.markers[0].suggestions[0]);
    try std.testing.expectEqualStrings("l1", result.markers[1].suggestions[0]);
    try std.testing.expectEqualStrings("both [l1, l2]", result.markers[2].suggestions[0]);
    try std.testing.expectEqualStrings("t1", result.markers[2].theorem);
    try std.testing.expectEqualStrings("l3", result.markers[2].label);
    try std.testing.expect(std.mem.startsWith(
        u8,
        result.text,
        \\t1
        \\---
        \\l1: $ P $ by p
        \\l2: $ Q $ by use [l1]
        \\l3: $ R $ by both [l1, l2]
        ,
    ));
    // Spans index the text the run was given, not the working text.
    for (result.markers) |marker| {
        try std.testing.expect(std.mem.startsWith(
            u8,
            proof_src[marker.span.start..],
            marker.kind.keyword(),
        ));
    }
    const filled = try applyEdits(proof_src, result.markers);
    defer std.testing.allocator.free(filled);
    try std.testing.expectEqualStrings(result.text, filled);
}

test "search driver leaves a missed marker as written and continues" {
    const proof_src =
        \\t1
        \\---
        \\l1: $ Q $ by exact?
        \\l2: $ R $ by both [p [], l1]
        \\
        \\t2
        \\---
        \\l1: $ R $ by both [exact?, use [p []]]
        \\
        \\t3
        \\---
        \\l1: $ isty o $ by o_ty
    ;
    var result = try run(proof_src);
    defer result.deinit();

    try std.testing.expectEqual(@as(usize, 2), result.markers.len);
    try std.testing.expectEqual(.missed, result.markers[0].outcome);
    try std.testing.expectEqual(@as(usize, 0), result.markers[0].suggestions.len);
    try std.testing.expectEqual(.found, result.markers[1].outcome);
    try std.testing.expectEqualStrings("t2", result.markers[1].theorem);
    try std.testing.expect(std.mem.indexOf(
        u8,
        result.text,
        "l1: $ Q $ by exact?",
    ) != null);
}

test "search driver does not search after a line that does not check" {
    const proof_src =
        \\t1
        \\---
        \\l1: $ Q $ by p []
        \\l2: $ R $ by exact?
        \\
        \\t2
        \\---
        \\l1: $ R $ by both [p [], use [exact?]]
        \\
        \\t3
        \\---
        \\l1: $ isty o $ by o_ty
    ;
    var result = try run(proof_src);
    defer result.deinit();

    try std.testing.expectEqual(@as(usize, 2), result.markers.len);
    try std.testing.expectEqual(.not_searched, result.markers[0].outcome);
    try std.testing.expectEqualStrings("l1", result.markers[0].blocked_by.?);
    try std.testing.expectEqual(.found, result.markers[1].outcome);
}

test "search driver lists apply? candidates without putting one in place" {
    const proof_src =
        \\t1
        \\---
        \\l1: $ P $ by p
        \\l2: $ Q $ by use [l1]
        \\l3: $ R $ by apply?
        \\
        \\t2
        \\---
        \\l1: $ R $ by both [p [], use [p []]]
        \\
        \\t3
        \\---
        \\l1: $ isty o $ by o_ty
    ;
    var result = try run(proof_src);
    defer result.deinit();

    try std.testing.expectEqual(@as(usize, 1), result.markers.len);
    try std.testing.expectEqual(.candidates, result.markers[0].outcome);
    try std.testing.expect(result.markers[0].suggestions.len != 0);
    try std.testing.expectEqualStrings(proof_src, result.text);
}

test "search driver reports the hole values a find gives its line" {
    const proof_src =
        \\t1
        \\---
        \\l1: $ R $ by both [p [], use [p []]]
        \\
        \\t2
        \\---
        \\l1: $ R $ by both [p [], use [p []]]
        \\
        \\t3
        \\---
        \\l1: $ isty _A $ by auto?
        \\l2: $ isty o $ by o_ty
    ;
    var result = try run(proof_src);
    defer result.deinit();

    try std.testing.expectEqual(@as(usize, 1), result.markers.len);
    const marker = result.markers[0];
    try std.testing.expectEqual(.found, marker.outcome);
    try std.testing.expectEqualStrings("o_ty", marker.suggestions[0]);
    try std.testing.expectEqual(@as(usize, 1), marker.holes.len);
    try std.testing.expectEqualStrings("_A", marker.holes[0].name);
    try std.testing.expectEqualStrings("o", marker.holes[0].value);

    const filled = try applyEdits(proof_src, result.markers);
    defer std.testing.allocator.free(filled);
    try std.testing.expect(std.mem.endsWith(
        u8,
        filled,
        \\l1: $ isty o $ by o_ty
        \\l2: $ isty o $ by o_ty
        ,
    ));
}

test "search driver retries a miss with the larger limits its report advises" {
    const proof_src =
        \\t1
        \\---
        \\l1: $ R $ by auto? (depth: 1)
        \\
        \\t2
        \\---
        \\l1: $ R $ by both [exact?, use [p []]]
        \\
        \\t3
        \\---
        \\l1: $ isty o $ by o_ty
    ;
    var once = try run(proof_src);
    defer once.deinit();
    try std.testing.expectEqual(.missed, once.markers[0].outcome);
    try std.testing.expectEqual(@as(usize, 0), once.markers[0].rounds.len);
    const retry = once.markers[0].retry.?;

    var result = try runWith(proof_src, .{ .retries = 1 });
    defer result.deinit();

    try std.testing.expectEqual(@as(usize, 2), result.markers.len);
    const marker = result.markers[0];
    try std.testing.expectEqual(.found, marker.outcome);
    try std.testing.expectEqual(@as(usize, 1), marker.rounds.len);
    try std.testing.expectEqual(.missed, marker.rounds[0].outcome);
    try std.testing.expectEqualStrings(retry, marker.rounds[0].retry);
    try std.testing.expectEqual(.found, result.markers[1].outcome);
    // The edits replace the markers as written, not as retried.
    const filled = try applyEdits(proof_src, result.markers);
    defer std.testing.allocator.free(filled);
    try std.testing.expectEqualStrings(result.text, filled);
    try std.testing.expect(std.mem.indexOf(u8, result.text, "auto?") == null);
}

test "search driver searches only the markers named, with default limits" {
    const nowhere: mm0.CompilerSupport.Search.Span = .{ .start = 0, .end = 0 };
    const depth_one: SearchDriver.Options = .{
        .only = .{ .theorem = "t1" },
        .params = &.{.{
            .name = "depth",
            .name_span = nowhere,
            .value = 1,
            .value_span = nowhere,
            .span = nowhere,
        }},
    };
    const blocks =
        \\
        \\t2
        \\---
        \\l1: $ R $ by auto?
        \\
        \\t3
        \\---
        \\l1: $ isty o $ by o_ty
    ;

    // `t2`'s marker is not searched, and `R` needs depth 2.
    var limited = try runWith("t1\n---\nl1: $ R $ by auto?\n" ++ blocks, depth_one);
    defer limited.deinit();
    try std.testing.expectEqual(@as(usize, 1), limited.markers.len);
    try std.testing.expectEqualStrings("t1", limited.markers[0].theorem);
    try std.testing.expectEqual(.missed, limited.markers[0].outcome);

    // A marker's own depth wins over the run's.
    var own = try runWith("t1\n---\nl1: $ R $ by auto? (depth: 2)\n" ++ blocks, depth_one);
    defer own.deinit();
    try std.testing.expectEqual(@as(usize, 1), own.markers.len);
    try std.testing.expectEqual(.found, own.markers[0].outcome);
    try std.testing.expect(std.mem.endsWith(u8, own.text, blocks));

    var line = try runWith(
        "t1\n---\nl1: $ P $ by exact?\nl2: $ R $ by auto?\n" ++ blocks,
        .{ .only = .{ .theorem = "t1", .label = "l2" } },
    );
    defer line.deinit();
    try std.testing.expectEqual(@as(usize, 1), line.markers.len);
    try std.testing.expectEqualStrings("l2", line.markers[0].label);
}
