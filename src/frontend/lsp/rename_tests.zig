const std = @import("std");
const Index = @import("index.zig");
const source = @import("source.zig");
const CompilerModule = @import("../compiler.zig");
const Imports = @import("../imports.zig");

const Snapshot = Index.Snapshot;
const DocumentId = Index.DocumentId;
const SourceRange = Index.SourceRange;

const Texts = struct {
    mm0: []const u8,
    proof: []const u8 = "",

    fn of(self: Texts, document: DocumentId) []const u8 {
        return switch (document) {
            .mm0 => self.mm0,
            .proof => self.proof,
        };
    }
};

fn build(arena: std.mem.Allocator, texts: Texts) !Snapshot {
    return Snapshot.build(arena, .{
        .mm0_uri = "file:///test.mm0",
        .mm0_text = texts.mm0,
        .proof_uri = "file:///test.auf",
        .proof_text = texts.proof,
    });
}

/// The offset of the `nth` (from 0) whole-word occurrence of `word`.
fn wordOffset(text: []const u8, word: []const u8, nth: usize) !usize {
    var at = source.findIdentIn(text, word, 0) orelse return error.WordNotFound;
    for (0..nth) |_| {
        at = source.findIdentIn(text, word, at + word.len) orelse return error.WordNotFound;
    }
    return at;
}

/// The snapshot of `texts` and what the `nth` `word` of `document` names.
fn targetAt(
    arena: std.mem.Allocator,
    texts: Texts,
    document: DocumentId,
    word: []const u8,
    nth: usize,
) !struct { snapshot: Snapshot, target: Index.RenameTarget } {
    const snapshot = try build(arena, texts);
    const offset = try wordOffset(texts.of(document), word, nth);
    const target = snapshot.renameTargetAt(document, offset) orelse
        return error.NothingToRename;
    return .{ .snapshot = snapshot, .target = target };
}

/// The texts after renaming what the `nth` `word` of `document` names.
fn renamed(
    arena: std.mem.Allocator,
    texts: Texts,
    document: DocumentId,
    word: []const u8,
    nth: usize,
    new_name: []const u8,
) !Texts {
    const found = try targetAt(arena, texts, document, word, nth);
    var edits: [2]std.ArrayListUnmanaged(Edit) = .{ .empty, .empty };
    for (try found.snapshot.renameEdits(arena, found.target, new_name)) |range| {
        try edits[@backingInt(range.document)].append(arena, .{ .range = range, .text = new_name });
    }
    return .{
        .mm0 = try applyEdits(arena, texts.mm0, edits[@backingInt(DocumentId.mm0)].items),
        .proof = try applyEdits(arena, texts.proof, edits[@backingInt(DocumentId.proof)].items),
    };
}

fn expectRenamed(
    texts: Texts,
    document: DocumentId,
    word: []const u8,
    nth: usize,
    new_name: []const u8,
    expected: Texts,
) !void {
    var arena_state = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena_state.deinit();
    const result = try renamed(arena_state.allocator(), texts, document, word, nth, new_name);
    try std.testing.expectEqualStrings(expected.mm0, result.mm0);
    try std.testing.expectEqualStrings(expected.proof, result.proof);
}

fn expectRefused(
    texts: Texts,
    document: DocumentId,
    word: []const u8,
    nth: usize,
    new_name: []const u8,
    expected: Index.RenameError,
) !void {
    var arena_state = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    const found = try targetAt(arena, texts, document, word, nth);
    try std.testing.expectError(expected, found.snapshot.renameEdits(arena, found.target, new_name));
}

test "renaming a term renames its name but not its notation" {
    try expectRenamed(.{
        .mm0 =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term im (a b: wff): wff; infixr im: $->$ prec 25;
        \\--| @auto trigger (im a _)
        \\axiom ax (a: wff): $ im a (a -> a) $;
        ,
    }, .mm0, "im", 0, "imp", .{
        .mm0 =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term imp (a b: wff): wff; infixr imp: $->$ prec 25;
        \\--| @auto trigger (imp a _)
        \\axiom ax (a: wff): $ imp a (a -> a) $;
        ,
    });
}

test "renaming a rule follows its annotations and its proofs" {
    const texts: Texts = .{
        .mm0 =
        \\provable sort wff;
        \\term bi (a b: wff): wff;
        \\--| @relation wff bi biid bitr bisym _
        \\axiom biid (a: wff): $ bi a a $;
        \\axiom bitr (a b c: wff): $ bi a b $ > $ bi b c $ > $ bi a c $;
        \\axiom bisym (a b: wff): $ bi a b $ > $ bi b a $;
        \\--| @fallback bitr
        \\axiom bitr2 (a b c: wff): $ bi a b $ > $ bi b c $ > $ bi a c $;
        \\theorem t (a: wff): $ bi a a $;
        ,
        .proof =
        \\t
        \\---
        \\l1: $ bi a a $ by bitr [biid, biid]
        ,
    };
    try expectRenamed(texts, .proof, "bitr", 0, "trans", .{
        .mm0 =
        \\provable sort wff;
        \\term bi (a b: wff): wff;
        \\--| @relation wff bi biid trans bisym _
        \\axiom biid (a: wff): $ bi a a $;
        \\axiom trans (a b c: wff): $ bi a b $ > $ bi b c $ > $ bi a c $;
        \\axiom bisym (a b: wff): $ bi a b $ > $ bi b a $;
        \\--| @fallback trans
        \\axiom bitr2 (a b c: wff): $ bi a b $ > $ bi b c $ > $ bi a c $;
        \\theorem t (a: wff): $ bi a a $;
        ,
        .proof =
        \\t
        \\---
        \\l1: $ bi a a $ by trans [biid, biid]
        ,
    });
    // A theorem from its proof block's header.
    try expectRenamed(texts, .proof, "t", 0, "refl", .{
        .mm0 =
        \\provable sort wff;
        \\term bi (a b: wff): wff;
        \\--| @relation wff bi biid bitr bisym _
        \\axiom biid (a: wff): $ bi a a $;
        \\axiom bitr (a b c: wff): $ bi a b $ > $ bi b c $ > $ bi a c $;
        \\axiom bisym (a b: wff): $ bi a b $ > $ bi b a $;
        \\--| @fallback bitr
        \\axiom bitr2 (a b c: wff): $ bi a b $ > $ bi b c $ > $ bi a c $;
        \\theorem refl (a: wff): $ bi a a $;
        ,
        .proof =
        \\refl
        \\---
        \\l1: $ bi a a $ by bitr [biid, biid]
        ,
    });
}

const view_texts: Texts = .{
    .mm0 =
    \\provable sort wff;
    \\sort obj;
    \\term all {x: obj} (p: wff x): wff;
    \\--| @view {x: obj} (p: wff x) (q: wff): $ p $ > $ all x q $
    \\--| @recover q p x x
    \\--| @fresh x
    \\axiom gen {x: obj} (p: wff x): $ p $ > $ all x p $;
    \\theorem t {y: obj} (p: wff y): $ p $ > $ all y p $;
    ,
    .proof =
    \\t
    \\---
    \\l1: $ all y p $ by gen (x := $ y $) [#1]
    ,
};

test "renaming a rule's binder follows dependencies, bindings and its view" {
    // The `x` of `gen`: the view's `x` is the same binder, `all`'s is not.
    try expectRenamed(view_texts, .mm0, "x", 8, "z", .{
        .mm0 =
        \\provable sort wff;
        \\sort obj;
        \\term all {x: obj} (p: wff x): wff;
        \\--| @view {z: obj} (p: wff z) (q: wff): $ p $ > $ all z q $
        \\--| @recover q p z z
        \\--| @fresh z
        \\axiom gen {z: obj} (p: wff z): $ p $ > $ all z p $;
        \\theorem t {y: obj} (p: wff y): $ p $ > $ all y p $;
        ,
        .proof =
        \\t
        \\---
        \\l1: $ all y p $ by gen (z := $ y $) [#1]
        ,
    });
}

test "renaming a view's own binder stays in the view" {
    try expectRenamed(view_texts, .mm0, "q", 0, "r", .{
        .mm0 =
        \\provable sort wff;
        \\sort obj;
        \\term all {x: obj} (p: wff x): wff;
        \\--| @view {x: obj} (p: wff x) (r: wff): $ p $ > $ all x r $
        \\--| @recover r p x x
        \\--| @fresh x
        \\axiom gen {x: obj} (p: wff x): $ p $ > $ all x p $;
        \\theorem t {y: obj} (p: wff y): $ p $ > $ all y p $;
        ,
        .proof = view_texts.proof,
    });
}

test "renaming a named hypothesis keeps the hash and positional references" {
    try expectRenamed(.{
        .mm0 =
        \\provable sort wff;
        \\term imp (a b: wff): wff; infixr imp: $->$ prec 25;
        \\axiom mp (a b: wff): $ a $ > $ a -> b $ > $ b $;
        \\theorem named (a b: wff) (ha: $ a $) (hab: $ a -> b $): $ b $;
        ,
        .proof =
        \\named
        \\---
        \\l1: $ b $ by mp [#ha, #2]
        ,
    }, .proof, "ha", 0, "h1", .{
        .mm0 =
        \\provable sort wff;
        \\term imp (a b: wff): wff; infixr imp: $->$ prec 25;
        \\axiom mp (a b: wff): $ a $ > $ a -> b $ > $ b $;
        \\theorem named (a b: wff) (h1: $ a $) (hab: $ a -> b $): $ b $;
        ,
        .proof =
        \\named
        \\---
        \\l1: $ b $ by mp [#h1, #2]
        ,
    });
}

const lines_texts: Texts = .{
    .mm0 =
    \\provable sort wff;
    \\term top: wff;
    \\axiom ti: $ top $;
    \\axiom keep: $ top $ > $ top $;
    \\theorem t1: $ top $;
    \\theorem t2: $ top $;
    ,
    .proof =
    \\t1
    \\---
    \\l1: $ top $ by ti []
    \\l2: $ top $ by keep [l1]
    \\
    \\t2
    \\---
    \\l1: $ top $ by ti []
    \\l3: $ top $ by keep [l1]
    ,
};

test "renaming a proof line stays in its block" {
    // `l3` is taken in the other block only.
    try expectRenamed(lines_texts, .proof, "l1", 1, "l3", .{
        .mm0 = lines_texts.mm0,
        .proof =
        \\t1
        \\---
        \\l3: $ top $ by ti []
        \\l2: $ top $ by keep [l3]
        \\
        \\t2
        \\---
        \\l1: $ top $ by ti []
        \\l3: $ top $ by keep [l1]
        ,
    });
    try expectRefused(lines_texts, .proof, "l1", 1, "l2", error.NameInUse);
    try expectRefused(lines_texts, .proof, "l1", 1, "keep", error.NameInUse);
}

test "renaming a sort follows every signature" {
    try expectRenamed(.{
        .mm0 =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\sort obj;
        \\term f (a: obj): obj;
        \\term g: obj > obj;
        \\term c (a: obj): wff;
        \\coercion c: obj > wff;
        \\def h (a: obj) {.d: obj}: obj = $ f a $;
        \\term k (a: obj): obj;
        \\notation k (a: obj): obj = ($k$:20) a;
        \\axiom ax (a: obj): $ c a $;
        ,
        .proof =
        \\def l (a: obj): obj = $ f a $
        \\
        \\lemma lem (a: obj): $ c (l a) $
        \\---
        \\l1: $ c (l a) $ by ax
        ,
    }, .mm0, "obj", 0, "thing", .{
        .mm0 =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\sort thing;
        \\term f (a: thing): thing;
        \\term g: thing > thing;
        \\term c (a: thing): wff;
        \\coercion c: thing > wff;
        \\def h (a: thing) {.d: thing}: thing = $ f a $;
        \\term k (a: thing): thing;
        \\notation k (a: thing): thing = ($k$:20) a;
        \\axiom ax (a: thing): $ c a $;
        ,
        .proof =
        \\def l (a: thing): thing = $ f a $
        \\
        \\lemma lem (a: thing): $ c (l a) $
        \\---
        \\l1: $ c (l a) $ by ax
        ,
    });
}

test "renaming a definition filler's dummy stays in the filler" {
    try expectRenamed(.{
        .mm0 =
        \\sort obj;
        \\term f (a b: obj): obj;
        \\def pick (a: obj): obj;
        ,
        .proof =
        \\def pick (.e: obj) = $ f a e $
        ,
    }, .proof, "e", 0, "w", .{
        .mm0 =
        \\sort obj;
        \\term f (a b: obj): obj;
        \\def pick (a: obj): obj;
        ,
        .proof =
        \\def pick (.w: obj) = $ f a w $
        ,
    });
}

test "rename refuses notation tokens, invalid names and names in use" {
    var arena_state = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena_state.deinit();
    const texts: Texts = .{
        .mm0 =
        \\--| @hole _wff
        \\provable sort wff;
        \\term im (a b: wff): wff; infixr im: $->$ prec 25;
        \\term top: wff;
        \\axiom ax (a b: wff): $ a -> b -> a $;
        ,
    };
    var snapshot = try build(arena_state.allocator(), texts);
    const arrow = std.mem.lastIndexOf(u8, texts.mm0, "->").?;
    try std.testing.expect(snapshot.renameTargetAt(.mm0, arrow) == null);

    try expectRefused(texts, .mm0, "top", 0, "2top", error.InvalidName);
    try expectRefused(texts, .mm0, "top", 0, "_", error.InvalidName);
    try expectRefused(texts, .mm0, "top", 0, "axiom", error.InvalidName);
    try expectRefused(texts, .mm0, "top", 0, "im", error.NameInUse);
    try expectRefused(texts, .mm0, "top", 0, "_wff", error.NameInUse);
    // A global name may not repeat a binder: it would be captured.
    try expectRefused(texts, .mm0, "top", 0, "b", error.NameInUse);
    // A binder may not repeat a sibling, a global name or a token.
    try expectRefused(texts, .mm0, "a", 1, "b", error.NameInUse);
    try expectRefused(texts, .mm0, "a", 1, "top", error.NameInUse);
    try expectRefused(texts, .mm0, "a", 1, "->", error.InvalidName);
}

test "rename refuses while part of the source does not parse" {
    // `top` in the broken statement is not indexed, so a rename would miss it.
    try expectRefused(.{
        .mm0 =
        \\provable sort wff;
        \\term top: wff;
        \\axiom ti: $ top $;
        \\axiom broken $ top $;
        ,
    }, .mm0, "top", 0, "truth", error.SyntaxError);
    // So would a half-typed proof line.
    try expectRefused(.{
        .mm0 = lines_texts.mm0,
        .proof =
        \\t1
        \\---
        \\l1: $ top $ by ti []
        \\l2: $ top $ by
        ,
    }, .proof, "ti", 0, "truth", error.SyntaxError);
}

test "rename refuses a name declared twice" {
    try expectRefused(.{
        .mm0 =
        \\provable sort wff;
        \\term top: wff;
        \\axiom ti: $ top $;
        \\axiom ti: $ top $;
        ,
    }, .mm0, "ti", 0, "truth", error.DuplicateName);
    try expectRefused(.{
        .mm0 = lines_texts.mm0,
        .proof =
        \\t1
        \\---
        \\l1: $ top $ by ti []
        \\l1: $ top $ by keep [l1]
        ,
    }, .proof, "l1", 0, "start", error.DuplicateName);
}

test "highlights mark the declaration and every use, notation included" {
    var arena_state = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    const text =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term im (a b: wff): wff; infixr im: $->$ prec 25;
        \\axiom ax (a: wff): $ im a (a -> a) $;
    ;
    var snapshot = try build(arena, .{ .mm0 = text });
    const highlights = try snapshot.highlightsAt(arena, .mm0, try wordOffset(text, "im", 2));
    var spellings = std.ArrayListUnmanaged(u8).empty;
    for (highlights) |highlight| {
        try spellings.print(arena, "{s}{s} ", .{
            text[highlight.range.start..highlight.range.end],
            if (highlight.declaration) "*" else "",
        });
    }
    // The declaration, the notation statement's name and token, then the
    // axiom's uses.
    try std.testing.expectEqualStrings("im* im -> im -> ", spellings.items);
}

/// Rename every name in a proof case, all at once, and compile the result.
fn expectProofCaseSurvivesRenamingEverything(stem: []const u8) !void {
    var arena_state = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();

    var failure: ?Imports.LoadFailure = null;
    const pair = try Imports.loadPair(
        std.testing.io,
        arena,
        try std.fmt.allocPrint(arena, "tests/proof_cases/{s}.mm0", .{stem}),
        try std.fmt.allocPrint(arena, "tests/proof_cases/{s}.auf", .{stem}),
        &failure,
    );
    const texts: Texts = .{ .mm0 = pair.mm0.text, .proof = pair.proof.?.text };
    var snapshot = try build(arena, texts);

    var declarations = std.ArrayListUnmanaged(SourceRange).empty;
    var edits: [2]std.ArrayListUnmanaged(Edit) = .{ .empty, .empty };
    for (snapshot.symbols) |symbol| {
        const range = symbol.source_range;
        const target = snapshot.renameTargetAt(range.document, range.start) orelse continue;
        const seen = for (declarations.items) |declaration| {
            if (declaration.eql(target.declaration)) break true;
        } else false;
        if (seen) continue;
        try declarations.append(arena, target.declaration);
        const new_name = try std.fmt.allocPrint(arena, "{s}_rn", .{target.name});
        for (try snapshot.renameEdits(arena, target, new_name)) |edit_range| {
            try edits[@backingInt(edit_range.document)].append(arena, .{ .range = edit_range, .text = new_name });
        }
    }
    try std.testing.expect(declarations.items.len > 0);

    var compiler = CompilerModule.Compiler.initWithProof(
        arena,
        try applyEdits(arena, texts.mm0, edits[@backingInt(DocumentId.mm0)].items),
        try applyEdits(arena, texts.proof, edits[@backingInt(DocumentId.proof)].items),
    );
    try compiler.check();
}

const Edit = struct { range: SourceRange, text: []const u8 };

fn applyEdits(arena: std.mem.Allocator, text: []const u8, edits: []Edit) ![]const u8 {
    std.mem.sort(Edit, edits, {}, struct {
        fn lessThan(_: void, a: Edit, b: Edit) bool {
            return a.range.start < b.range.start;
        }
    }.lessThan);
    var out = std.ArrayListUnmanaged(u8).empty;
    var pos: usize = 0;
    for (edits) |edit| {
        try std.testing.expect(edit.range.start >= pos);
        try out.appendSlice(arena, text[pos..edit.range.start]);
        try out.appendSlice(arena, edit.text);
        pos = edit.range.end;
    }
    try out.appendSlice(arena, text[pos..]);
    return out.items;
}

test "proof cases still compile with every name renamed" {
    // Between them: `@relation`, `@acui` on a proof-local definition,
    // `@view`/`@abstract`/`@recover`, `@fresh`/`@freshen`/`@alpha`/`@vars`,
    // `@fallback`, coercions, lemmas, named hypotheses and an import.
    for ([_][]const u8{
        "pass_chained_normalize",
        "pass_local_def_acui",
        "pass_abstract_basic",
        "pass_view_recover_free_hole_auto",
        "pass_chained_alpha",
        "pass_fresh_reuse",
        "pass_chained_fallback",
        "pass_named_hyp_refs",
    }) |stem| {
        expectProofCaseSurvivesRenamingEverything(stem) catch |err| {
            std.debug.print("proof case {s}: {}\n", .{ stem, err });
            return err;
        };
    }
}
