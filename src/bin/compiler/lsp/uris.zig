//! The names the language server gives files: a document's URI, the path
//! its unit keys it by, and the root pair a path belongs to.

const std = @import("std");
const mm0 = @import("mm0");

const Imports = mm0.Imports;

pub const UnsupportedUriScheme = error{UnsupportedUriScheme};

pub const UnsupportedUriHost = error{UnsupportedUriHost};

pub const UnsupportedDocument = error{UnsupportedDocument};

pub const DocumentKind = enum {
    mm0,
    proof,
    other,
};

/// A root `.mm0` and the proof file beside it, whether or not they exist.
pub const UnitRoots = struct {
    mm0_uri: []const u8,
    mm0_path: []const u8,
    proof_uri: []const u8,
    proof_path: []const u8,

    /// The root `.mm0` and the proof file beside it that a request on `uri`
    /// navigates: the document itself and its sibling. Null for any other
    /// document.
    pub fn of(arena: std.mem.Allocator, uri: []const u8) !?UnitRoots {
        const path = uriToPath(arena, uri) catch return null;
        switch (documentKind(path)) {
            .mm0 => {
                const proof_path = siblingPathForMm0(arena, path) catch return null;
                return .{
                    .mm0_uri = uri,
                    .mm0_path = path,
                    .proof_uri = try pathToUri(arena, proof_path),
                    .proof_path = proof_path,
                };
            },
            .proof => {
                const mm0_path = siblingPathForProof(arena, path) catch return null;
                return .{
                    .mm0_uri = try pathToUri(arena, mm0_path),
                    .mm0_path = mm0_path,
                    .proof_uri = uri,
                    .proof_path = path,
                };
            },
            .other => return null,
        }
    }
};

pub fn uriToPath(
    allocator: std.mem.Allocator,
    uri_text: []const u8,
) ![]const u8 {
    const uri = try std.Uri.parse(uri_text);
    if (!std.mem.eql(u8, uri.scheme, "file")) {
        return UnsupportedUriScheme.UnsupportedUriScheme;
    }
    if (uri.host) |host| {
        const host_text = try host.toRawMaybeAlloc(allocator);
        if (host_text.len != 0 and
            !std.mem.eql(u8, host_text, "localhost"))
        {
            return UnsupportedUriHost.UnsupportedUriHost;
        }
    }
    // No file path holds a NUL byte, and the OS calls assert on one.
    const encoded = switch (uri.path) {
        .raw, .percent_encoded => |text| text,
    };
    if (std.mem.indexOfScalar(u8, encoded, 0) != null or
        (uri.path == .percent_encoded and std.mem.indexOf(u8, encoded, "%00") != null))
    {
        return error.InvalidFormat;
    }
    // Decoded only when the path holds an escape; otherwise a slice of the
    // URI.
    const raw = try uri.path.toRawMaybeAlloc(allocator);
    defer if (raw.ptr != encoded.ptr) allocator.free(raw);
    // Keyed the way `Imports.resolveSpecPath` keys what the file imports,
    // so an import leading back to it is recognised.
    return try Imports.normalizePath(allocator, raw);
}

pub fn pathToUri(
    allocator: std.mem.Allocator,
    path: []const u8,
) ![]const u8 {
    return try std.fmt.allocPrint(
        allocator,
        "file://{f}",
        .{std.fmt.alt(std.Uri.Component{ .raw = path }, .formatPath)},
    );
}

pub fn siblingPathForProof(
    allocator: std.mem.Allocator,
    proof_path: []const u8,
) ![]const u8 {
    return try Imports.theorySiblingKey(allocator, proof_path) orelse
        UnsupportedDocument.UnsupportedDocument;
}

pub fn siblingPathForMm0(
    allocator: std.mem.Allocator,
    mm0_path: []const u8,
) ![]const u8 {
    return try Imports.proofSiblingKey(allocator, mm0_path) orelse
        UnsupportedDocument.UnsupportedDocument;
}

pub fn documentKind(path: []const u8) DocumentKind {
    if (std.mem.endsWith(u8, path, ".mm0")) return .mm0;
    if (std.mem.endsWith(u8, path, ".auf")) return .proof;
    return .other;
}
