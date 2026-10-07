const std = @import("std");
const AssertionStmt = @import("../parse_recovery.zig").AssertionStmt;
const MM0Parser = @import("../parse_recovery.zig").MM0Parser;
const CompilerDiag = @import("../diag.zig");
const Span = @import("../proof_script.zig").Span;

pub const Entry = struct {
    ordinal: u32,
    name_span: Span,
};

const EntryMap = std.StringHashMap(Entry);

/// Every assertion of the `.mm0`, by name, with its declaration ordinal.
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
            // A convenience index: a malformed statement ends the walk
            // rather than failing the lookup.
            self.entries = build(self.allocator, self.src) catch
                EntryMap.init(self.allocator);
        }
        return self.entries.?.get(name);
    }
};

fn build(
    allocator: std.mem.Allocator,
    src: []const u8,
) !EntryMap {
    var parser = MM0Parser.init(src, allocator);
    var catalog = EntryMap.init(allocator);
    var ordinal: u32 = 0;

    while (try parser.next()) |stmt| {
        switch (stmt) {
            .assertion => |assertion| {
                try recordAssertion(
                    &catalog,
                    assertion,
                    ordinal,
                );
                ordinal += 1;
            },
            else => {},
        }
    }

    return catalog;
}

fn recordAssertion(
    catalog: *EntryMap,
    assertion: AssertionStmt,
    ordinal: u32,
) !void {
    const gop = try catalog.getOrPut(assertion.name);
    if (gop.found_existing) return;
    gop.value_ptr.* = .{
        .ordinal = ordinal,
        .name_span = CompilerDiag.mathSpanToSpan(assertion.name_span),
    };
}
