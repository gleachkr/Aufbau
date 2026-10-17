//! Names outside math strings: the sorts and dependencies of a declaration
//! signature, and what an annotation's arguments name. Every name here is a
//! slice of the indexed document text.
const std = @import("std");

const source = @import("source.zig");
const markdown = @import("markdown.zig");
const Types = @import("types.zig");
const support = @import("builder_support.zig");

const DocumentId = Types.DocumentId;
const BinderDecl = Types.BinderDecl;
const SignatureToken = source.SignatureToken;

const nextAnnotationToken = source.nextAnnotationToken;
const nextMathStringIn = source.nextMathStringIn;
const binderMarkdown = markdown.binderMarkdown;
const findBinderIn = support.findBinderIn;

/// Index the sorts and dependencies of `signature`, a slice of the
/// `document` text that starts after a declaration's name. Dependencies
/// resolve against `binders`, the scope of declaration `decl_index`.
/// Returns the scanned tokens, for a caller that declares the binders.
pub fn indexSignature(
    self: anytype,
    document: DocumentId,
    signature: []const u8,
    decl_index: ?usize,
    binders: []const BinderDecl,
) ![]const SignatureToken {
    const tokens = try source.scanSignature(self.allocator, signature);
    for (tokens) |token| switch (token.role) {
        .binder => {},
        .sort => try self.addSortUse(document, token.text),
        .dep => try addBinderUse(self, document, token.text, decl_index, binders),
    };
    return tokens;
}

/// Index a declaration's annotations: the rules, terms and sorts they name,
/// and the declaration's own binders. A `@view` declares binders of its
/// own; one named like a rule binder stands for it. The `@recover` and
/// `@abstract` lines after a `@view` name its binders.
pub fn indexAnnotations(
    self: anytype,
    document: DocumentId,
    decl_index: usize,
    annotations: []const []const u8,
) !void {
    const binders = self.declarations.items[decl_index].binders;
    var view: []const BinderDecl = &.{};
    for (annotations) |annotation| {
        var pos: usize = 0;
        const directive = (nextAnnotationToken(annotation, &pos) orelse continue).text;
        const args = annotation[pos..];
        if (std.mem.eql(u8, directive, "@relation")) {
            try indexGlobalArgs(self, document, args, &.{ .sort, .term, .rule, .rule, .rule, .rule });
        } else if (std.mem.eql(u8, directive, "@acui")) {
            try indexGlobalArgs(self, document, args, &.{ .rule, .rule, .term, .rule });
        } else if (std.mem.eql(u8, directive, "@fallback")) {
            try indexGlobalArgs(self, document, args, &.{.rule});
        } else if (std.mem.eql(u8, directive, "@fresh") or
            std.mem.eql(u8, directive, "@freshen") or
            std.mem.eql(u8, directive, "@alpha"))
        {
            try indexViewArgs(self, document, args, decl_index, binders);
        } else if (std.mem.eql(u8, directive, "@auto")) {
            try indexTrigger(self, document, args, decl_index, binders);
        } else if (std.mem.eql(u8, directive, "@view")) {
            view = try indexView(self, document, args, decl_index);
        } else if (std.mem.eql(u8, directive, "@recover") or
            std.mem.eql(u8, directive, "@abstract"))
        {
            try indexViewArgs(self, document, args, decl_index, view);
        }
    }
}

const GlobalRole = enum { sort, term, rule };

/// Positional arguments naming global declarations; `_` and unknown
/// names are skipped.
fn indexGlobalArgs(
    self: anytype,
    document: DocumentId,
    args: []const u8,
    roles: []const GlobalRole,
) !void {
    var pos: usize = 0;
    for (roles) |role| {
        const token = nextAnnotationToken(args, &pos) orelse return;
        const index = switch (role) {
            .sort => self.sortDeclIndex(token.text),
            .term => termDeclIndex(self, token.text),
            .rule => ruleDeclIndex(self, token.text),
        } orelse continue;
        try addGlobalUse(self, document, token.text, index);
    }
}

/// `@auto trigger (TERM child …)`: the name after each `(` is a term, any
/// other name a binder of the rule.
fn indexTrigger(
    self: anytype,
    document: DocumentId,
    args: []const u8,
    decl_index: usize,
    binders: []const BinderDecl,
) !void {
    var pos: usize = 0;
    const mode = nextAnnotationToken(args, &pos) orelse return;
    if (!std.mem.eql(u8, mode.text, "trigger")) return;
    var after_open = false;
    while (pos < args.len) {
        const ch = args[pos];
        if (!source.isIdentStart(ch)) {
            if (ch == '(') after_open = true;
            if (ch == ')') after_open = false;
            pos += 1;
            continue;
        }
        const start = pos;
        while (pos < args.len and source.isIdentChar(args[pos])) pos += 1;
        const name = args[start..pos];
        if (after_open) {
            if (termDeclIndex(self, name)) |index| {
                try addGlobalUse(self, document, name, index);
            }
        } else {
            try addBinderUse(self, document, name, decl_index, binders);
        }
        after_open = false;
    }
}

/// A `@view` signature: declares the view's binders (a rule binder's name
/// stands for that binder), indexes its sorts and dependencies, and its
/// math in the view's scope. Returns the view's binders in order.
fn indexView(
    self: anytype,
    document: DocumentId,
    signature: []const u8,
    decl_index: usize,
) ![]const BinderDecl {
    const decl = self.declarations.items[decl_index];
    const tokens = try source.scanSignature(self.allocator, signature);
    var scope = std.ArrayListUnmanaged(BinderDecl).empty;
    var local = std.ArrayListUnmanaged(BinderDecl).empty;
    for (tokens) |token| {
        if (token.role != .binder) continue;
        if (findBinderIn(decl.binders, token.text)) |rule_binder| {
            try addBinderUse(self, document, token.text, decl_index, decl.binders);
            try scope.append(self.allocator, rule_binder);
            continue;
        }
        const range = self.rangeOf(document, token.text);
        const binder: BinderDecl = .{
            .name = token.text,
            .sort_name = token.sort,
            .bound = token.bound,
            .range = range,
        };
        try scope.append(self.allocator, binder);
        try local.append(self.allocator, binder);
        if (range) |declared| try self.addSymbol(.{
            .source_range = declared,
            .target_range = declared,
            .markdown = try binderMarkdown(self.allocator, decl, binder),
        });
    }
    for (tokens) |token| switch (token.role) {
        .binder => {},
        .sort => try self.addSortUse(document, token.text),
        .dep => try addBinderUse(self, document, token.text, decl_index, scope.items),
    };
    var pos: usize = 0;
    while (nextMathStringIn(signature, signature.len, &pos)) |math| {
        try indexAnnotationMath(self, document, math.text, decl_index, scope.items);
    }
    try self.addLocalBinders(decl_index, local.items);
    return try scope.toOwnedSlice(self.allocator);
}

/// Binder names, and `$ … $` patterns over the same binders.
fn indexViewArgs(
    self: anytype,
    document: DocumentId,
    args: []const u8,
    decl_index: usize,
    binders: []const BinderDecl,
) !void {
    var pos: usize = 0;
    while (pos < args.len) {
        const ch = args[pos];
        if (ch == '$') {
            const start = pos + 1;
            const end = std.mem.indexOfScalarPos(u8, args, start, '$') orelse args.len;
            try indexAnnotationMath(self, document, args[start..end], decl_index, binders);
            pos = end + 1;
            continue;
        }
        if (!source.isIdentStart(ch)) {
            pos += 1;
            continue;
        }
        const start = pos;
        while (pos < args.len and source.isIdentChar(args[pos])) pos += 1;
        try addBinderUse(self, document, args[start..pos], decl_index, binders);
    }
}

fn indexAnnotationMath(
    self: anytype,
    document: DocumentId,
    math: []const u8,
    decl_index: usize,
    binders: []const BinderDecl,
) !void {
    const range = self.rangeOf(document, math) orelse return;
    try self.indexMathStringIn(document, math, range.start, decl_index, binders, false, null);
}

fn addBinderUse(
    self: anytype,
    document: DocumentId,
    name: []const u8,
    decl_index: ?usize,
    binders: []const BinderDecl,
) !void {
    const index = decl_index orelse return;
    const binder = findBinderIn(binders, name) orelse return;
    const range = self.rangeOf(document, name) orelse return;
    const decl = self.declarations.items[index];
    try self.addSymbol(.{
        .source_range = range,
        .target_range = binder.range orelse decl.name_range,
        .markdown = try binderMarkdown(self.allocator, decl, binder),
    });
}

/// An annotation may name a rule declared after it (`@relation` sits on
/// the reflexivity axiom), so the use is not gated on availability.
fn addGlobalUse(
    self: anytype,
    document: DocumentId,
    name: []const u8,
    decl_index: usize,
) !void {
    const range = self.rangeOf(document, name) orelse return;
    const decl = self.declarations.items[decl_index];
    try self.addSymbol(.{
        .source_range = range,
        .target_range = decl.name_range,
        .markdown = decl.markdown,
    });
}

fn termDeclIndex(self: anytype, name: []const u8) ?usize {
    const index = self.decl_by_name.get(name) orelse return null;
    return switch (self.declarations.items[index].kind) {
        .term, .def => index,
        else => null,
    };
}

/// An axiom or theorem, or else the latest lemma of that name.
fn ruleDeclIndex(self: anytype, name: []const u8) ?usize {
    if (self.decl_by_name.get(name)) |index| {
        switch (self.declarations.items[index].kind) {
            .axiom, .theorem => return index,
            else => {},
        }
    }
    var found: ?usize = null;
    for (self.proof_rules.items) |rule| {
        if (std.mem.eql(u8, rule.name, name)) found = rule.decl_index;
    }
    return found;
}
