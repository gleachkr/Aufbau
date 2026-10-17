//! Rename and document highlights over the index. A rename edits every
//! symbol whose target is the renamed declaration, binder, hypothesis or
//! proof line, except notation tokens, which use a term without naming it.
const std = @import("std");

const source = @import("source.zig");
const Types = @import("types.zig");
const model = @import("model.zig");

const DocumentId = Types.DocumentId;
const SourceRange = Types.SourceRange;
const Declaration = Types.Declaration;
const BinderDecl = Types.BinderDecl;
const NavigationSymbol = model.NavigationSymbol;

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
    snapshot: anytype,
    document: DocumentId,
    offset: usize,
) ?RenameTarget {
    const symbol = symbolAt(snapshot, document, offset) orelse return null;
    if (symbol.via_notation) return null;
    const declaration = symbol.target_range orelse return null;
    const name = textAt(snapshot, declaration) orelse return null;
    return .{
        .range = nameRange(snapshot, symbol.source_range, name) orelse return null,
        .name = name,
        .declaration = declaration,
        .scope = scopeOf(snapshot, declaration) orelse return null,
    };
}

/// The ranges to replace with `new_name`. Empty when the name is unchanged.
pub fn renameEdits(
    snapshot: anytype,
    allocator: std.mem.Allocator,
    target: RenameTarget,
    new_name: []const u8,
) (RenameError || std.mem.Allocator.Error)![]const SourceRange {
    if (!snapshot.complete) return error.SyntaxError;
    if (!isValidName(new_name)) return error.InvalidName;
    if (std.mem.eql(u8, new_name, target.name)) return &.{};
    if (declarationCount(snapshot, target.scope, target.name) > 1) return error.DuplicateName;
    if (nameInUse(snapshot, target.scope, new_name)) return error.NameInUse;

    var edits = std.ArrayListUnmanaged(SourceRange).empty;
    try edits.append(allocator, target.declaration);
    for (snapshot.symbols) |symbol| {
        if (symbol.via_notation) continue;
        const declaration = symbol.target_range orelse continue;
        if (!rangeEql(declaration, target.declaration)) continue;
        const range = nameRange(snapshot, symbol.source_range, target.name) orelse continue;
        if (containsRange(edits.items, range)) continue;
        try edits.append(allocator, range);
    }
    return try edits.toOwnedSlice(allocator);
}

/// Every occurrence of what the symbol at `offset` refers to, notation
/// tokens included.
pub fn highlightsAt(
    snapshot: anytype,
    allocator: std.mem.Allocator,
    document: DocumentId,
    offset: usize,
) ![]const Highlight {
    const symbol = symbolAt(snapshot, document, offset) orelse return &.{};
    const declaration = symbol.target_range orelse return &.{};
    var highlights = std.ArrayListUnmanaged(Highlight).empty;
    for (snapshot.symbols) |other| {
        const other_declaration = other.target_range orelse continue;
        if (!rangeEql(other_declaration, declaration)) continue;
        if (containsRange(highlights.items, other.source_range)) continue;
        try highlights.append(allocator, .{
            .range = other.source_range,
            .declaration = rangeEql(other.source_range, declaration),
        });
    }
    return try highlights.toOwnedSlice(allocator);
}

/// The first symbol containing `offset`, as the other lookups pick it.
fn symbolAt(snapshot: anytype, document: DocumentId, offset: usize) ?NavigationSymbol {
    for (snapshot.symbols) |symbol| {
        const range = symbol.source_range;
        if (range.document == document and offset >= range.start and offset < range.end) {
            return symbol;
        }
    }
    return null;
}

fn textAt(snapshot: anytype, range: SourceRange) ?[]const u8 {
    const text = snapshot.textForDocument(range.document) orelse return null;
    if (range.end > text.len or range.start > range.end) return null;
    return text[range.start..range.end];
}

/// The part of an occurrence that spells `name`: all of it, or all but the
/// `#` of a named hypothesis reference. Null for anything else, such as a
/// positional `#2`.
fn nameRange(snapshot: anytype, range: SourceRange, name: []const u8) ?SourceRange {
    const text = textAt(snapshot, range) orelse return null;
    if (std.mem.eql(u8, text, name)) return range;
    if (text.len == name.len + 1 and text[0] == '#' and std.mem.eql(u8, text[1..], name)) {
        return .{ .document = range.document, .start = range.start + 1, .end = range.end };
    }
    return null;
}

fn scopeOf(snapshot: anytype, declaration: SourceRange) ?Scope {
    for (snapshot.declarations, 0..) |decl, index| {
        if (rangeEql(decl.name_range, declaration)) {
            if (decl.kind != .proof_line) return .global;
            for (snapshot.proof_lines) |line| {
                if (line.decl_index == index) return .{ .block = line.block_index };
            }
            return null;
        }
        if (declaresBinder(decl.binders, declaration) or
            declaresBinder(decl.local_binders, declaration))
        {
            return .{ .declaration = index };
        }
        for (decl.hypotheses) |hyp| {
            const range = hyp.name_range orelse continue;
            if (rangeEql(range, declaration)) return .{ .declaration = index };
        }
    }
    return null;
}

fn declaresBinder(binders: []const BinderDecl, declaration: SourceRange) bool {
    for (binders) |binder| {
        const range = binder.range orelse continue;
        if (rangeEql(range, declaration)) return true;
    }
    return false;
}

/// Whether `name` is taken where the renamed thing lives. Deliberately
/// broad: a global name may not repeat any name in the unit, so that it can
/// never be captured by a binder or shadow a line; a binder, hypothesis or
/// line may not repeat a global name or one from its own declaration or
/// block.
fn nameInUse(snapshot: anytype, scope: Scope, name: []const u8) bool {
    for (snapshot.notations) |notation| {
        if (std.mem.eql(u8, notation.token, name)) return true;
    }
    const global = scope == .global;
    for (snapshot.declarations) |decl| {
        // A line's name matters to a global name; to another line, only
        // in its own block.
        if ((global or decl.kind != .proof_line) and std.mem.eql(u8, decl.name, name)) return true;
        if (global and declaresName(decl, name)) return true;
    }
    switch (scope) {
        .global => return false,
        .declaration => |index| return declaresName(snapshot.declarations[index], name),
        .block => |block_index| {
            for (snapshot.proof_lines) |line| {
                if (line.block_index == block_index and std.mem.eql(u8, line.name, name)) return true;
            }
            const decl_index = snapshot.proof_blocks[block_index].decl_index orelse return false;
            return declaresName(snapshot.declarations[decl_index], name);
        },
    }
}

/// How many things `name` names where the renamed thing lives.
fn declarationCount(snapshot: anytype, scope: Scope, name: []const u8) usize {
    var count: usize = 0;
    switch (scope) {
        .global => for (snapshot.declarations) |decl| {
            if (decl.kind != .proof_line and std.mem.eql(u8, decl.name, name)) count += 1;
        },
        .declaration => |index| {
            const decl = snapshot.declarations[index];
            for ([_][]const BinderDecl{ decl.binders, decl.local_binders }) |binders| {
                for (binders) |binder| {
                    if (std.mem.eql(u8, binder.name, name)) count += 1;
                }
            }
            for (decl.hypotheses) |hyp| {
                const hyp_name = hyp.name orelse continue;
                if (std.mem.eql(u8, hyp_name, name)) count += 1;
            }
        },
        .block => |block_index| for (snapshot.proof_lines) |line| {
            if (line.block_index == block_index and std.mem.eql(u8, line.name, name)) count += 1;
        },
    }
    return count;
}

/// Whether one of the declaration's binders or hypotheses is called `name`.
fn declaresName(decl: Declaration, name: []const u8) bool {
    for (decl.binders) |binder| {
        if (std.mem.eql(u8, binder.name, name)) return true;
    }
    for (decl.local_binders) |binder| {
        if (std.mem.eql(u8, binder.name, name)) return true;
    }
    for (decl.hypotheses) |hyp| {
        const hyp_name = hyp.name orelse continue;
        if (std.mem.eql(u8, hyp_name, name)) return true;
    }
    return false;
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

fn rangeEql(a: SourceRange, b: SourceRange) bool {
    return a.document == b.document and a.start == b.start and a.end == b.end;
}

/// Whether `items`, ranges or highlights, already hold `needle`.
fn containsRange(items: anytype, needle: SourceRange) bool {
    for (items) |item| {
        const range = if (@TypeOf(item) == SourceRange) item else item.range;
        if (rangeEql(range, needle)) return true;
    }
    return false;
}
