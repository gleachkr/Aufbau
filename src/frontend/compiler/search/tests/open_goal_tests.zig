//! The code actions on an open goal `?`.

const helpers = @import("./helpers.zig");
const std = helpers.std;
const types = helpers.types;
const suggestionsAtNeedle = helpers.suggestionsAtNeedle;
const Compiler = @import("../../../compiler.zig").Compiler;

const rules =
    \\provable sort wff;
    \\term imp (a b: wff): wff; infixr imp: $->$ prec 25;
    \\term and (a b: wff): wff; infixr and: $/\$ prec 30;
    \\axiom mp (a b: wff): $ a -> b $ > $ a $ > $ b $;
    \\axiom andi (a b: wff): $ a $ > $ b $ > $ a /\ b $;
    \\
;

/// The rules, with `_wff` holes, and the theorem `t`.
fn theory(comptime theorem: []const u8) []const u8 {
    return "--| @hole _wff\n" ++ rules ++ theorem;
}

const both = theory("theorem t (p q: wff): $ p $ > $ q $ > $ p /\\ q $;");
const left = theory("theorem t (p q: wff): $ p $ > $ p /\\ q $;");
const detach = theory("theorem t (p q: wff): $ p -> q $ > $ p $ > $ q $;");
const nested = theory("theorem t (p q: wff): $ q -> p $ > $ q $ > $ p /\\ q $;");

/// The actions at the first `needle` in `proof_src`.
fn actionsAt(
    arena: *std.heap.ArenaAllocator,
    mm0: []const u8,
    proof_src: []const u8,
    needle: []const u8,
) !types.SourceSuggestions {
    const suggestions = try suggestionsAtNeedle(arena, mm0, proof_src, needle, .{});
    try std.testing.expectEqual(.open_goal, suggestions.target_kind);
    return suggestions;
}

/// `proof_src` with `action` applied.
fn applied(
    allocator: std.mem.Allocator,
    proof_src: []const u8,
    action: types.SourceSuggestion,
) ![]const u8 {
    return try std.mem.concat(allocator, u8, &.{
        proof_src[0..action.replace_span.start],
        action.replacement,
        proof_src[action.replace_span.end..],
    });
}

fn expectTitles(items: []const types.SourceSuggestion, titles: []const []const u8) !void {
    errdefer for (items) |item| std.debug.print("  offered: {s}\n", .{item.title});
    try std.testing.expectEqual(titles.len, items.len);
    for (items, titles) |item, title| try std.testing.expectEqualStrings(title, item.title);
}

/// The editor's analysis of `proof_src` reports no error.
fn expectAnalyzes(mm0: []const u8, proof_src: []const u8) !void {
    var compiler = Compiler.initWithProof(std.testing.allocator, mm0, proof_src);
    compiler.allow_search_placeholders = true;
    try compiler.analyze();
    errdefer for (compiler.primaryDiagnostics()) |diag| std.debug.print("  error: {s}\n", .{@errorName(diag.err)});
    try std.testing.expectEqual(@as(usize, 0), compiler.primaryDiagnostics().len);
}

test "an open goal line offers the rules its goal matches, those the facts close first" {
    const proof_src =
        \\t
        \\---
        \\l1: $ p /\ q $ by ?
        \\
    ;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const suggestions = try actionsAt(&arena, both, proof_src, "by ?");
    try expectTitles(suggestions.items, &.{
        "Apply andi [#1, #2]",
        "Apply mp [l1_1, l1_2]",
        "Admit with sorry!",
    });
    try std.testing.expectEqualStrings(
        "l1: $ p /\\ q $ by andi [#1, #2]\n",
        suggestions.items[0].replacement,
    );
    // Nothing fixes `mp`'s antecedent: both premises stay open, with a hole.
    try std.testing.expectEqualStrings(
        \\l1_1: $ _wff -> p /\ q $ by ?
        \\l1_2: $ _wff $ by ?
        \\l1: $ p /\ q $ by mp [l1_1, l1_2]
        \\
    , suggestions.items[1].replacement);
    // The editor goes on to the first `?` an action adds; one that cites
    // every premise adds none.
    try std.testing.expectEqual(@as(?usize, null), suggestions.items[0].cursor);
    try std.testing.expectEqual(
        @as(?usize, "l1_1: $ _wff -> p /\\ q $ by ".len),
        suggestions.items[1].cursor,
    );
    for (suggestions.items) |action| {
        try expectAnalyzes(both, try applied(arena.allocator(), proof_src, action));
    }
}

test "a premise no fact states becomes an open goal line above" {
    const proof_src =
        \\t
        \\---
        \\l1: $ p /\ q $ by ?
    ;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const suggestions = try actionsAt(&arena, left, proof_src, "by ?");
    try std.testing.expectEqualStrings("Apply andi [#1, l1_1]", suggestions.items[0].title);
    try std.testing.expectEqualStrings(
        \\l1_1: $ q $ by ?
        \\l1: $ p /\ q $ by andi [#1, l1_1]
    , suggestions.items[0].replacement);
    try expectAnalyzes(left, try applied(arena.allocator(), proof_src, suggestions.items[0]));
}

test "a partly unknown premise is not closed by a fact that happens to match" {
    // `#1` is the only fact matching `_ -> q`, but nothing says the proof
    // goes through it.
    const proof_src =
        \\t
        \\---
        \\l1: $ q $ by ?
    ;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const suggestions = try actionsAt(&arena, detach, proof_src, "by ?");
    try expectTitles(suggestions.items, &.{ "Apply mp [l1_1, l1_2]", "Admit with sorry!" });
}

test "references written on an open goal are the rule's premises" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    {
        // `#1` fixes `mp`'s antecedent, and then `#2` states the second
        // premise.
        const proof_src =
            \\t
            \\---
            \\l1: $ q $ by ? [#1, ?]
        ;
        const suggestions = try actionsAt(&arena, detach, proof_src, "by ?");
        try expectTitles(suggestions.items, &.{ "Apply mp [#1, #2]", "Admit with sorry!" });
        try std.testing.expectEqualStrings(
            "l1: $ q $ by mp [#1, #2]",
            suggestions.items[0].replacement,
        );
        try expectAnalyzes(detach, try applied(arena.allocator(), proof_src, suggestions.items[0]));
    }
    {
        // `p` is no implication: `mp` does not take it first.
        const proof_src =
            \\t
            \\---
            \\l1: $ q $ by ? [#2, ?]
        ;
        const suggestions = try actionsAt(&arena, detach, proof_src, "by ?");
        try expectTitles(suggestions.items, &.{"Admit with sorry!"});
        const sorry = suggestions.items[0];
        try std.testing.expectEqualStrings("sorry!", sorry.replacement);
        try std.testing.expectEqualStrings(
            "? [#2, ?]",
            proof_src[sorry.replace_span.start..sorry.replace_span.end],
        );
    }
}

test "an inline open goal is replaced in place" {
    const proof_src =
        \\t
        \\---
        \\l1: $ p /\ q $ by andi [? [#1, ?], #2]
    ;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const suggestions = try actionsAt(&arena, nested, proof_src, "? [#1");
    // No `sorry!` inline: it justifies a line.
    try expectTitles(suggestions.items, &.{"Apply mp [#1, #2]"});
    const edited = try applied(arena.allocator(), proof_src, suggestions.items[0]);
    try std.testing.expectEqualStrings(
        \\t
        \\---
        \\l1: $ p /\ q $ by andi [mp [#1, #2], #2]
    , edited);
    try expectAnalyzes(nested, edited);

    // Without references nothing fixes `mp`'s antecedent: both premises
    // stay open.
    const bare =
        \\t
        \\---
        \\l1: $ p /\ q $ by andi [?, #2]
    ;
    const open_premises = try actionsAt(&arena, nested, bare, "?,");
    try expectTitles(open_premises.items, &.{"Apply mp [?, ?]"});
    try std.testing.expectEqual(@as(?usize, "mp [".len), open_premises.items[0].cursor);
}

test "a premise needing a hole in a sort without one is not offered" {
    const proof_src =
        \\t
        \\---
        \\l1: $ p /\ q $ by ?
    ;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const no_holes = rules ++ "theorem t (p q: wff): $ p $ > $ q $ > $ p /\\ q $;";
    const suggestions = try actionsAt(&arena, no_holes, proof_src, "by ?");
    try expectTitles(suggestions.items, &.{ "Apply andi [#1, #2]", "Admit with sorry!" });
}

test "a holey open goal line offers no sorry!" {
    const proof_src =
        \\t
        \\---
        \\l1: $ p /\ _wff $ by ?
    ;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const suggestions = try actionsAt(&arena, left, proof_src, "by ?");
    for (suggestions.items) |item| {
        try std.testing.expect(!std.mem.eql(u8, item.replacement, "sorry!"));
    }
    // `mp` too: its conclusion variable is the whole goal, hole and all.
    try expectTitles(suggestions.items, &.{ "Apply mp [l1_1, l1_2]", "Apply andi [#1, l1_1]" });
    try std.testing.expectEqualStrings(
        \\l1_1: $ _wff -> p /\ _wff $ by ?
        \\l1_2: $ _wff $ by ?
        \\l1: $ p /\ _wff $ by mp [l1_1, l1_2]
    , suggestions.items[0].replacement);
    try std.testing.expectEqualStrings(
        \\l1_1: $ _wff $ by ?
        \\l1: $ p /\ _wff $ by andi [#1, l1_1]
    , suggestions.items[1].replacement);
}

/// Sequents over contexts that are sets (`,` is ACUI with unit `_`), with
/// no holes: `or_elim` splits its conclusion's context three ways.
const sequents = "delimiter $ ( ) , $;\n" ++ sequent_rules ++
    \\axiom or_elim (G H K: ctx) (p q r: wff):
    \\  $ G |- p \/ q $ > $ H , p |- r $ > $ K , q |- r $ > $ G , H , K |- r $;
    \\theorem t (p q r: wff):
    \\  $ p \/ q |- p \/ q $ > $ p |- r $ > $ q |- r $ > $ _ , p \/ q |- r $;
    \\
;

/// The sequent calculus's sorts, terms and laws, without its rules.
const sequent_rules =
    \\strict provable sort wff;
    \\sort ctx;
    \\term or (p q: wff): wff; infixr or: $\/$ prec 28;
    \\term bi (p q: wff): wff; infixr bi: $<->$ prec 20;
    \\term ctx_eq (G H: ctx): wff;
    \\term emp: ctx; notation emp: ctx = ($_$:max);
    \\--| @acui ctx_assoc ctx_comm emp ctx_idem
    \\term join (G H: ctx): ctx; infixl join: $,$ prec 5;
    \\term hyp (p: wff): ctx; coercion hyp: wff > ctx;
    \\term nd (G: ctx) (p: wff): wff; infixl nd: $|-$ prec 0;
    \\--| @relation wff bi biid bitr bisym mpbi
    \\axiom biid (p: wff): $ p <-> p $;
    \\axiom bitr (p q r: wff): $ p <-> q $ > $ q <-> r $ > $ p <-> r $;
    \\axiom bisym (p q: wff): $ p <-> q $ > $ q <-> p $;
    \\axiom mpbi (p q: wff): $ p <-> q $ > $ p $ > $ q $;
    \\--| @relation ctx ctx_eq ctx_refl ctx_trans ctx_sym _
    \\axiom ctx_refl (G: ctx): $ ctx_eq G G $;
    \\axiom ctx_trans (G H K: ctx): $ ctx_eq G H $ > $ ctx_eq H K $ > $ ctx_eq G K $;
    \\axiom ctx_sym (G H: ctx): $ ctx_eq G H $ > $ ctx_eq H G $;
    \\axiom ctx_assoc (G H K: ctx): $ ctx_eq ((G , H) , K) (G , (H , K)) $;
    \\axiom ctx_comm (G H: ctx): $ ctx_eq (G , H) (H , G) $;
    \\axiom ctx_idem (G: ctx): $ ctx_eq (G , G) G $;
    \\axiom ctx_unit (G: ctx): $ ctx_eq (emp , G) G $;
    \\--| @congr
    \\axiom join_congr (G1 G2 H1 H2: ctx):
    \\  $ ctx_eq G1 G2 $ > $ ctx_eq H1 H2 $ > $ ctx_eq (G1 , H1) (G2 , H2) $;
    \\--| @congr
    \\axiom hyp_congr (p q: wff): $ p <-> q $ > $ ctx_eq (hyp p) (hyp q) $;
    \\--| @congr
    \\axiom nd_congr (G H: ctx) (p q: wff):
    \\  $ ctx_eq G H $ > $ p <-> q $ > $ (G |- p) <-> (H |- q) $;
    \\
;

test "the facts written on an open goal fix a rule's context split" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    {
        // Only the cited facts say how `p \/ q` splits into `G , H , K`.
        const proof_src =
            \\t
            \\---
            \\l1: $ _ , p \/ q |- r $ by ? [#1, #2, #3]
        ;
        const suggestions = try actionsAt(&arena, sequents, proof_src, "by ?");
        try expectTitles(suggestions.items, &.{ "Apply or_elim [#1, #2, #3]", "Admit with sorry!" });
        try expectAnalyzes(sequents, try applied(arena.allocator(), proof_src, suggestions.items[0]));
    }
    {
        // Without them the split is a choice the goal does not make.
        const proof_src =
            \\t
            \\---
            \\l1: $ _ , p \/ q |- r $ by ?
        ;
        const suggestions = try actionsAt(&arena, sequents, proof_src, "by ?");
        try expectTitles(suggestions.items, &.{"Admit with sorry!"});
    }
}

test "a premise with a fresh variable is written with its name" {
    // `x` is not in the goal: `@fresh` picks it from the `@vars` pool. The
    // line citing `all x p` names it, or the checker would pick another.
    const fresh =
        \\provable sort wff;
        \\--| @vars x
        \\sort obj;
        \\term all {x: obj} (p: wff x): wff;
        \\--| @fresh x
        \\axiom ui {x: obj} (p: wff): $ all x p $ > $ p $;
        \\theorem t (p: wff): $ p $;
        \\
    ;
    const proof_src =
        \\t
        \\---
        \\l1: $ p $ by ?
    ;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const suggestions = try actionsAt(&arena, fresh, proof_src, "by ?");
    try expectTitles(suggestions.items, &.{ "Apply ui (x := $ x $) [l1_1]", "Admit with sorry!" });
    try std.testing.expectEqualStrings(
        \\l1_1: $ all x p $ by ?
        \\l1: $ p $ by ui (x := $ x $) [l1_1]
    , suggestions.items[0].replacement);
    try expectAnalyzes(fresh, try applied(arena.allocator(), proof_src, suggestions.items[0]));
}

/// `theory`, with named unknowns: `?a` is an unknown in `wff`.
fn named(comptime theorem: []const u8) []const u8 {
    return "--| @unknown ?\n--| @hole _wff\n" ++ rules ++ theorem;
}

test "a rule variable the goal leaves open is a named unknown in the premises" {
    const mm0 = named("theorem t (p q: wff): $ p -> q $ > $ p $ > $ q $;");
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    {
        const proof_src =
            \\t
            \\---
            \\l1: $ q $ by ?
        ;
        const suggestions = try actionsAt(&arena, mm0, proof_src, "by ?");
        try expectTitles(suggestions.items, &.{ "Apply mp [l1_1, l1_2]", "Admit with sorry!" });
        // Both premises name `mp`'s antecedent `?a`, so filling one fills
        // the other.
        try std.testing.expectEqualStrings(
            \\l1_1: $ ?a -> q $ by ?
            \\l1_2: $ ?a $ by ?
            \\l1: $ q $ by mp [l1_1, l1_2]
        , suggestions.items[0].replacement);
        try expectAnalyzes(mm0, try applied(arena.allocator(), proof_src, suggestions.items[0]));
    }
    {
        // A name the block uses already is not reused.
        const proof_src =
            \\t
            \\---
            \\l0: $ ?a $ by ?
            \\l1: $ q $ by ?
        ;
        const suggestions = try actionsAt(&arena, mm0, proof_src, "q $ by ?");
        try std.testing.expectEqualStrings(
            \\l1_1: $ ?a1 -> q $ by ?
            \\l1_2: $ ?a1 $ by ?
            \\l1: $ q $ by mp [l1_1, l1_2]
        , suggestions.items[0].replacement);
    }
    {
        // A variable where the goal has an anonymous hole gets a name too.
        const proof_src =
            \\t
            \\---
            \\l1: $ _wff $ by ?
            \\l2: $ q $ by ?
        ;
        const suggestions = try actionsAt(&arena, mm0, proof_src, "by ?");
        try std.testing.expectEqualStrings(
            \\l1_1: $ ?a -> ?b $ by ?
            \\l1_2: $ ?a $ by ?
            \\l1: $ _wff $ by mp [l1_1, l1_2]
            \\
        , suggestions.items[0].replacement);
    }
}

test "the premises keep the names the goal gives a rule variable" {
    const mm0 = named("theorem t (p q: wff): $ p $ > $ p /\\ q $;");
    // Not the last line, which the theorem's conclusion would fix.
    const proof_src =
        \\t
        \\---
        \\l1: $ ?c /\ q $ by ?
        \\l2: $ p /\ q $ by ?
    ;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const suggestions = try actionsAt(&arena, mm0, proof_src, "by ?");
    const action = for (suggestions.items) |item| {
        if (std.mem.startsWith(u8, item.title, "Apply andi")) break item;
    } else return error.MissingAndi;
    try std.testing.expectEqualStrings(
        \\l1_1: $ ?c $ by ?
        \\l1_2: $ q $ by ?
        \\l1: $ ?c /\ q $ by andi [l1_1, l1_2]
        \\
    , action.replacement);
    try expectAnalyzes(mm0, try applied(arena.allocator(), proof_src, action));
}

test "a named unknown in a context premise keeps the context's other members" {
    // `or_elim` with one context: the goal fixes `G`, and `p`, `q` become
    // named unknowns, the context members its case premises add.
    const mm0 = "delimiter $ ( ) , $;\n--| @unknown ?\n" ++ sequent_rules ++
        \\axiom or_elim (G: ctx) (p q r: wff):
        \\  $ G |- p \/ q $ > $ G , p |- r $ > $ G , q |- r $ > $ G |- r $;
        \\theorem t (p q: wff): $ p \/ q |- q \/ p $;
        \\
    ;
    const proof_src =
        \\t
        \\---
        \\l1: $ p \/ q |- q \/ p $ by ?
    ;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const suggestions = try actionsAt(&arena, mm0, proof_src, "by ?");
    const action = for (suggestions.items) |item| {
        if (std.mem.startsWith(u8, item.title, "Apply or_elim")) break item;
    } else return error.MissingOrElim;
    try std.testing.expectEqualStrings(
        \\l1_1: $ p \/ q |- ?p \/ ?q $ by ?
        \\l1_2: $ p \/ q , ?p |- q \/ p $ by ?
        \\l1_3: $ p \/ q , ?q |- q \/ p $ by ?
        \\l1: $ p \/ q |- q \/ p $ by or_elim [l1_1, l1_2, l1_3]
    , action.replacement);
    try expectAnalyzes(mm0, try applied(arena.allocator(), proof_src, action));
}

test "a goal with a hole inside a part offers the rules whose variables stand for that part" {
    // `and_elim_l`'s `a` is the whole `p /\ ?q`. The line checker leaves a
    // variable over a part with a hole open; the probe binds it.
    const mm0 = comptime "delimiter $ ( ) $;\n" ++ named("axiom and_elim_l (a b: wff): $ a /\\ b $ > $ a $;\n" ++
        "theorem t (p q: wff): $ p $ > $ p /\\ q $;");
    const proof_src =
        \\t
        \\---
        \\l1: $ p /\ ?q $ by ?
        \\l2: $ p /\ q $ by ?
    ;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const suggestions = try actionsAt(&arena, mm0, proof_src, "by ?");
    const action = for (suggestions.items) |item| {
        if (std.mem.startsWith(u8, item.title, "Apply and_elim_l")) break item;
    } else return error.MissingAndElim;
    try std.testing.expectEqualStrings(
        \\l1_1: $ (p /\ ?q) /\ ?b $ by ?
        \\l1: $ p /\ ?q $ by and_elim_l [l1_1]
        \\
    , action.replacement);
    try expectAnalyzes(mm0, try applied(arena.allocator(), proof_src, action));
}

test "a rule whose conclusion fills the goal's unknowns is offered" {
    // `id` proves `?x -> p` only with `?x` as `p`, which the line, once it
    // cites `id`, is checked for.
    const mm0 = comptime named("axiom id (a: wff): $ a -> a $;\n" ++
        "theorem t (p: wff): $ p -> p $;");
    const proof_src =
        \\t
        \\---
        \\l1: $ ?x -> p $ by ?
        \\l2: $ p -> p $ by ?
    ;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const suggestions = try actionsAt(&arena, mm0, proof_src, "by ?");
    const action = for (suggestions.items) |item| {
        if (std.mem.eql(u8, item.title, "Apply id")) break item;
    } else return error.MissingId;
    try std.testing.expectEqualStrings(
        \\l1: $ ?x -> p $ by id
        \\
    , action.replacement);
    try expectAnalyzes(mm0, try applied(arena.allocator(), proof_src, action));
}

test "a new name skips the names the proof writes, and only those" {
    // `(` splits only after it and `)` only before it, so `(?a` and `?b)`
    // hold the names `?a` and `?b`; a name in a comment is no name.
    const mm0 = comptime "delimiter $ ( $ $ ) $;\n" ++
        named("theorem t (p q: wff): $ p -> q $ > $ p $ > $ q $;");
    const proof_src =
        \\t
        \\---
        \\-- ?c is not used
        \\l0: $ (?a -> ?b) $ by ?
        \\l1: $ q $ by ?
    ;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const suggestions = try actionsAt(&arena, mm0, proof_src, "q $ by ?");
    try std.testing.expectEqualStrings(
        \\l1_1: $ ?a1 -> q $ by ?
        \\l1_2: $ ?a1 $ by ?
        \\l1: $ q $ by mp [l1_1, l1_2]
    , suggestions.items[0].replacement);
}

test "a variable named where the goal has an anonymous hole has its name in every premise" {
    // `b` stands for the goal's `_wff`; the first premise is settled by the
    // goal alone, the second also has the open `c`.
    const mm0 = comptime named("axiom k (a b c: wff): $ b $ > $ c -> b $ > $ a /\\ b $;\n" ++
        "theorem t (p q: wff): $ p $ > $ p /\\ q $;");
    const proof_src =
        \\t
        \\---
        \\l1: $ p /\ _wff $ by ?
        \\l2: $ p /\ q $ by ?
    ;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const suggestions = try actionsAt(&arena, mm0, proof_src, "by ?");
    const action = for (suggestions.items) |item| {
        if (std.mem.startsWith(u8, item.title, "Apply k")) break item;
    } else return error.MissingK;
    try std.testing.expectEqualStrings(
        \\l1_1: $ ?b $ by ?
        \\l1_2: $ ?c -> ?b $ by ?
        \\l1: $ p /\ _wff $ by k [l1_1, l1_2]
        \\
    , action.replacement);
}
