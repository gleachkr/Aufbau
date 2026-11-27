const std = @import("std");
const Index = @import("index.zig");
const Snapshot = Index.Snapshot;

/// The snapshot of a theory and, when given, its proof text.
pub fn buildSnapshot(mm0_text: []const u8, proof_text: ?[]const u8) !Snapshot {
    return Snapshot.build(std.testing.allocator, .{
        .mm0_uri = "file:///test.mm0",
        .mm0_text = mm0_text,
        .proof_uri = if (proof_text != null) "file:///test.auf" else null,
        .proof_text = proof_text,
    });
}

pub fn completionNamed(
    items: []const Index.CompletionItem,
    label: []const u8,
) ?Index.CompletionItem {
    for (items) |item| {
        if (std.mem.eql(u8, item.label, label)) return item;
    }
    return null;
}
