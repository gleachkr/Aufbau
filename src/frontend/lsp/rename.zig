//! Rename and document highlights over the index. A rename edits every
//! symbol whose target is the renamed declaration, binder, hypothesis or
//! proof line, except notation tokens, which use a term without naming it.
const std = @import("std");

const Snapshot = @import("index.zig").Snapshot;
const references = @import("references.zig");
const source = @import("source.zig");
const Types = @import("types.zig");

const ProofBody = @import("model.zig").ProofBody;
const DocumentId = Types.DocumentId;
const SourceRange = Types.SourceRange;
const Declaration = Types.Declaration;
const BinderDecl = Types.BinderDecl;

/// The name under the cursor and what it names.
pub const RenameTarget = struct {
    /// The name itself, without the `#` of a hypothesis reference.
    range: SourceRange,
    name: []const u8,
    /// Where the named thing is declared; every occurrence targets it.
    declaration: SourceRange,
    scope: Scope,
};

/// Where a new name could clash.
pub const Scope = union(enum) {
    /// A sort, term, definition, rule, lemma or `@vars` token.
    global,
    /// A binder or hypothesis of this declaration.
    declaration: usize,
    /// A line of this proof block.
    block: usize,
};

pub const RenameError = error{
    /// Not an identifier, `_`, or a keyword.
    InvalidName,
    /// The name is already in use where it would clash.
    NameInUse,
    /// Part of the unit did not parse, so its occurrences are unknown.
    SyntaxError,
    /// The old name is declared twice where it lives, so which uses mean
    /// the renamed declaration is unknown.
    DuplicateName,
};

pub const Highlight = struct {
    range: SourceRange,
    /// The declaration itself rather than a use.
    declaration: bool,
};

/// What a rename at `offset` would rename, or null when the cursor is not
/// on a renameable name.
pub fn renameTargetAt(
    snapshot: *Snapshot,
    document: DocumentId,
    offset: usize,
) std.mem.Allocator.Error!?RenameTarget {
    const symbol = try snapshot.lookupAt(document, offset) orelse return null;
    if (symbol.via_notation) return null;
    const declaration = symbol.target_range orelse return null;
    const name = textAt(snapshot, declaration) orelse return null;
    return .{
        .range = nameRange(snapshot, symbol.source_range, name) orelse return null,
        .name = name,
        .declaration = declaration,
        .scope = try scopeOf(snapshot, declaration) orelse return null,
    };
}

/// The ranges to replace with `new_name`. Empty when the name is unchanged.
pub fn renameEdits(
    snapshot: *Snapshot,
    allocator: std.mem.Allocator,
    target: RenameTarget,
    new_name: []const u8,
) (RenameError || std.mem.Allocator.Error)![]const SourceRange {
    if (!snapshot.complete) return error.SyntaxError;
    if (!isValidName(new_name)) return error.InvalidName;
    if (std.mem.eql(u8, new_name, target.name)) return &.{};
    if (try declarationCount(snapshot, target.scope, target.name) > 1) return error.DuplicateName;
    if (try nameInUse(snapshot, allocator, target.scope, new_name)) return error.NameInUse;

    const found = try references.occurrences(snapshot, allocator, target.declaration, null);
    defer allocator.free(found);
    var edits = std.ArrayListUnmanaged(SourceRange).empty;
    errdefer edits.deinit(allocator);
    try edits.append(allocator, target.declaration);
    for (found) |occurrence| {
        if (occurrence.via_notation) continue;
        const range = nameRange(snapshot, occurrence.range, target.name) orelse continue;
        try edits.append(allocator, range);
    }
    references.sortedUnique(&edits);
    return try edits.toOwnedSlice(allocator);
}

/// The occurrences, in `within`, of what the symbol at `offset` refers to,
/// notation tokens included, marking the declaration.
pub fn highlightsAt(
    snapshot: *Snapshot,
    allocator: std.mem.Allocator,
    document: DocumentId,
    offset: usize,
    within: []const SourceRange,
) std.mem.Allocator.Error![]const Highlight {
    const symbol = try snapshot.lookupAt(document, offset) orelse return &.{};
    const declaration = symbol.target_range orelse return &.{};
    const ranges = try snapshot.referencesTo(allocator, declaration, within);
    defer allocator.free(ranges);
    const highlights = try allocator.alloc(Highlight, ranges.len);
    for (ranges, highlights) |range, *highlight| {
        highlight.* = .{ .range = range, .declaration = range.eql(declaration) };
    }
    return highlights;
}

fn textAt(snapshot: *const Snapshot, range: SourceRange) ?[]const u8 {
    const text = snapshot.textForDocument(range.document) orelse return null;
    if (range.end > text.len or range.start > range.end) return null;
    return text[range.start..range.end];
}

/// The part of an occurrence that spells `name`: all of it, or all but the
/// `#` of a named hypothesis reference. Null for anything else, such as a
/// positional `#2`.
fn nameRange(snapshot: *const Snapshot, range: SourceRange, name: []const u8) ?SourceRange {
    const text = textAt(snapshot, range) orelse return null;
    if (std.mem.eql(u8, text, name)) return range;
    if (text.len == name.len + 1 and text[0] == '#' and std.mem.eql(u8, text[1..], name)) {
        return .{ .document = range.document, .start = range.start + 1, .end = range.end };
    }
    return null;
}

fn scopeOf(
    snapshot: *Snapshot,
    declaration: SourceRange,
) std.mem.Allocator.Error!?Scope {
    if (snapshot.blockWithBodyAt(declaration.document, declaration.start)) |block_index| {
        const body = try snapshot.bodyOf(block_index);
        for (body.lines) |line| {
            if (line.name_range.eql(declaration)) return .{ .block = block_index };
        }
        return null;
    }
    for (snapshot.declarations, 0..) |decl, index| {
        if (decl.name_range.eql(declaration)) return .global;
        if (decl.declaresBinder(declaration) or decl.declaresHypothesis(declaration)) {
            return .{ .declaration = index };
        }
    }
    return null;
}

/// Whether `name` is taken where the renamed thing lives. Deliberately
/// broad: a global name may not repeat any name in the unit, so that it can
/// never be captured by a binder or shadow a line; a binder, hypothesis or
/// line may not repeat a global name or one from its own declaration or
/// block.
fn nameInUse(
    snapshot: *Snapshot,
    allocator: std.mem.Allocator,
    scope: Scope,
    name: []const u8,
) std.mem.Allocator.Error!bool {
    for (snapshot.notations) |notation| {
        if (std.mem.eql(u8, notation.token, name)) return true;
    }
    for (snapshot.hole_tokens) |token| {
        if (std.mem.eql(u8, token, name)) return true;
    }
    for (snapshot.declarations) |decl| {
        if (std.mem.eql(u8, decl.name, name)) return true;
        if (scope == .global and countDeclared(decl, name) > 0) return true;
    }
    switch (scope) {
        .global => {
            var bodies = references.BodyWalk.init(snapshot, allocator, &.{name}, null);
            defer bodies.deinit();
            while (try bodies.next()) |body| {
                if (countLines(body, name) > 0) return true;
            }
            return false;
        },
        .declaration => |index| return countDeclared(snapshot.declarations[index], name) > 0,
        .block => |block_index| {
            if (countLines(try snapshot.bodyOf(block_index), name) > 0) return true;
            const decl_index = snapshot.proof_blocks[block_index].decl_index orelse return false;
            return countDeclared(snapshot.declarations[decl_index], name) > 0;
        },
    }
}

/// How many things `name` names where the renamed thing lives.
fn declarationCount(
    snapshot: *Snapshot,
    scope: Scope,
    name: []const u8,
) std.mem.Allocator.Error!usize {
    return switch (scope) {
        .global => blk: {
            var count: usize = 0;
            for (snapshot.declarations) |decl| {
                if (std.mem.eql(u8, decl.name, name)) count += 1;
            }
            break :blk count;
        },
        .declaration => |index| countDeclared(snapshot.declarations[index], name),
        .block => |block_index| countLines(try snapshot.bodyOf(block_index), name),
    };
}

/// How many of the declaration's binders and hypotheses are called `name`.
fn countDeclared(decl: Declaration, name: []const u8) usize {
    var count: usize = 0;
    for ([_][]const BinderDecl{ decl.binders, decl.local_binders }) |binders| {
        for (binders) |binder| {
            if (std.mem.eql(u8, binder.name, name)) count += 1;
        }
    }
    for (decl.hypotheses) |hyp| {
        const hyp_name = hyp.name orelse continue;
        if (std.mem.eql(u8, hyp_name, name)) count += 1;
    }
    return count;
}

/// How many lines of the body are called `name`.
fn countLines(body: ProofBody, name: []const u8) usize {
    var count: usize = 0;
    for (body.lines) |line| {
        if (std.mem.eql(u8, line.name, name)) count += 1;
    }
    return count;
}

/// The words of `.mm0` and `.auf` syntax a name may not be.
const keywords = [_][]const u8{
    "axiom",  "coercion", "def",    "delimiter", "free", "import",
    "infixl", "infixr",   "input",  "local",     "max",  "notation",
    "output", "prec",     "prefix", "provable",  "pub",  "pure",
    "sort",   "strict",   "term",   "theorem",   "by",   "include",
    "lemma",
};

fn isValidName(name: []const u8) bool {
    if (name.len == 0 or !source.isIdentStart(name[0])) return false;
    for (name) |ch| {
        if (!source.isIdentChar(ch)) return false;
    }
    if (std.mem.eql(u8, name, "_")) return false;
    for (keywords) |keyword| {
        if (std.mem.eql(u8, name, keyword)) return false;
    }
    return true;
}
