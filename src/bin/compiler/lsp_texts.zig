//! The texts of the files the language server's units are built from, one
//! copy of each file however many units read it. A unit holds each of its
//! files' texts until it is dropped; a text is freed once no unit holds it.
//! An open document's text is keyed by its version, a file read from disk by
//! its mtime: a unit built while either is unchanged shares the text earlier
//! units read.
//!
//! Every unit releases what it holds: a navigation cache entry when it is
//! dropped, an analysis that joined its own unit when it ends. Those are the
//! only units: the handler answers one message at a time and an analysis
//! runs between messages, so no other unit outlives the call that built it.
//! Code that keeps a unit anywhere else has to hold its texts too.
const std = @import("std");

const Allocator = std.mem.Allocator;

pub const FileText = struct {
    /// The file's path (owned).
    path: []const u8,
    /// Owned.
    text: []const u8,
    /// The open document's version, or null for a file read from disk.
    version: ?i32,
    /// The mtime of a file read from disk, or null for an open document.
    mtime: ?i128,
    /// How many units hold this text.
    holders: usize,
};

pub const FileTexts = struct {
    allocator: Allocator,
    /// The text last read from each path. A text a newer one replaced here
    /// lives on while units still hold it.
    latest: std.StringHashMapUnmanaged(*FileText) = .empty,

    pub fn init(allocator: Allocator) FileTexts {
        return .{ .allocator = allocator };
    }

    /// Once every unit has let go of its texts, so none is left.
    pub fn deinit(self: *FileTexts) void {
        std.debug.assert(self.latest.count() == 0);
        self.latest.deinit(self.allocator);
        self.* = undefined;
    }

    /// The text of the open document at `path`, held for the caller.
    pub fn document(
        self: *FileTexts,
        path: []const u8,
        text: []const u8,
        version: i32,
    ) Allocator.Error!*FileText {
        if (self.latest.get(path)) |known| {
            if (known.version == version) return hold(known);
        }
        const owned = try self.allocator.dupe(u8, text);
        errdefer self.allocator.free(owned);
        return self.add(path, owned, version, null);
    }

    /// The text of the file at `path` on disk, held for the caller. It is
    /// read only when its mtime differs from that of the text last read.
    pub fn disk(self: *FileTexts, io: std.Io, path: []const u8) !*FileText {
        const file = try std.Io.Dir.cwd().openFile(io, path, .{});
        defer file.close(io);
        const stat = try file.stat(io);
        const mtime = stat.mtime.nanoseconds;
        if (self.latest.get(path)) |known| {
            if (known.mtime == mtime) return hold(known);
        }
        var buffer: [4096]u8 = undefined;
        var reader = file.reader(io, &buffer);
        // The extra byte is for the read that finds the end.
        var text = try std.ArrayList(u8).initCapacity(self.allocator, @intCast(stat.size + 1));
        errdefer text.deinit(self.allocator);
        reader.interface.appendRemaining(self.allocator, &text, .unlimited) catch |err| switch (err) {
            error.ReadFailed => return reader.err.?,
            else => |e| return e,
        };
        const owned = try text.toOwnedSlice(self.allocator);
        errdefer self.allocator.free(owned);
        return self.add(path, owned, null, mtime);
    }

    /// Let go of a text `document` or `disk` gave.
    pub fn release(self: *FileTexts, text: *FileText) void {
        text.holders -= 1;
        if (text.holders != 0) return;
        if (self.latest.get(text.path)) |known| {
            if (known == text) _ = self.latest.remove(text.path);
        }
        self.destroy(text);
    }

    fn hold(text: *FileText) *FileText {
        text.holders += 1;
        return text;
    }

    /// Takes `owned` on success.
    fn add(
        self: *FileTexts,
        path: []const u8,
        owned: []const u8,
        version: ?i32,
        mtime: ?i128,
    ) Allocator.Error!*FileText {
        const owned_path = try self.allocator.dupe(u8, path);
        errdefer self.allocator.free(owned_path);
        const text = try self.allocator.create(FileText);
        errdefer self.allocator.destroy(text);
        text.* = .{
            .path = owned_path,
            .text = owned,
            .version = version,
            .mtime = mtime,
            .holders = 1,
        };
        const slot = try self.latest.getOrPut(self.allocator, path);
        // A replaced text keeps its own path; the key is the newest one's.
        slot.key_ptr.* = owned_path;
        slot.value_ptr.* = text;
        return text;
    }

    fn destroy(self: *FileTexts, text: *FileText) void {
        self.allocator.free(text.text);
        self.allocator.free(text.path);
        self.allocator.destroy(text);
    }
};
