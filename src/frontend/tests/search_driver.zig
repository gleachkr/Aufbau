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
    return SearchDriver.run(std.testing.allocator, test_mm0, proof_src);
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
}
