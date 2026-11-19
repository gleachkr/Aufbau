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
    try std.testing.expectEqualStrings("Apply andi [#1, l1_1]", suggestions.items[0].title);
    try std.testing.expectEqualStrings(
        \\l1_1: $ _wff $ by ?
        \\l1: $ p /\ _wff $ by andi [#1, l1_1]
    , suggestions.items[0].replacement);
}

/// Sequents over contexts that are sets (`,` is ACUI with unit `_`), with
/// no holes: `or_elim` splits its conclusion's context three ways.
const sequents =
    \\delimiter $ ( ) , $;
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
    \\axiom or_elim (G H K: ctx) (p q r: wff):
    \\  $ G |- p \/ q $ > $ H , p |- r $ > $ K , q |- r $ > $ G , H , K |- r $;
    \\theorem t (p q r: wff):
    \\  $ p \/ q |- p \/ q $ > $ p |- r $ > $ q |- r $ > $ _ , p \/ q |- r $;
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
