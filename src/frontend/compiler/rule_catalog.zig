const std = @import("std");
const AssertionStmt = @import("../parse_recovery.zig").AssertionStmt;
const MM0Parser = @import("../parse_recovery.zig").MM0Parser;
const CompilerDiag = @import("../diag.zig");
const Span = @import("../proof_script.zig").Span;

pub const Entry = struct {
    /// The parser position just past the assertion's statement. A check
    /// whose parser has not passed it cites a rule declared later.
    end: usize,
    name_span: Span,

    pub fn declaredBefore(self: Entry, parser_pos: usize) bool {
        return self.end < parser_pos;
    }
};

const EntryMap = std.StringHashMap(Entry);

/// Every assertion of the `.mm0`, by name, with where its statement ends.
/// Only a rule name the env does not know yet reads it, to tell a rule
/// declared later from an unknown one, so the whole-file parse it takes
/// runs on the first lookup rather than up front.
pub const Catalog = struct {
    allocator: std.mem.Allocator,
    src: []const u8,
    entries: ?EntryMap = null,

    pub fn init(allocator: std.mem.Allocator, src: []const u8) Catalog {
        return .{ .allocator = allocator, .src = src };
    }

    pub fn get(self: *Catalog, name: []const u8) ?Entry {
        if (self.entries == null) {
            self.entries = EntryMap.init(self.allocator);
            build(self.allocator, self.src, &self.entries.?) catch {};
        }
        return self.entries.?.get(name);
    }
};

/// A convenience index: a malformed statement (or running out of memory)
/// ends the walk, keeping the assertions before it.
fn build(
    allocator: std.mem.Allocator,
    src: []const u8,
    catalog: *EntryMap,
) !void {
    var parser = MM0Parser.init(src, allocator);
    while (try parser.next()) |stmt| {
        switch (stmt) {
            .assertion => |assertion| try recordAssertion(
                catalog,
                assertion,
                parser.core.pos,
            ),
            else => {},
        }
    }
}

fn recordAssertion(
    catalog: *EntryMap,
    assertion: AssertionStmt,
    end: usize,
) !void {
    const gop = try catalog.getOrPut(assertion.name);
    if (gop.found_existing) return;
    gop.value_ptr.* = .{
        .end = end,
        .name_span = CompilerDiag.mathSpanToSpan(assertion.name_span),
    };
}
