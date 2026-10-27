//! The search core (`core/`, behind `GenerateOptions.core`): it proves
//! propositional sequents over an ACUI context, every proof it returns has
//! passed the checker, and on a miss the generation ladder still runs.

const helpers = @import("./helpers.zig");
const std = helpers.std;
const types = helpers.types;
const suggestionsAtNeedle = helpers.suggestionsAtNeedle;
const expectOffered = helpers.expectOffered;
const generate = @import("../generate.zig");

// Classical propositional natural deduction in the shape of `nd_fol`:
// eager introductions, an unsafe left rule for `→`, `raa`, and the two
// closers.
const nd_rules =
    \\delimiter $ ( ) $;
    \\provable sort wff;
    \\sort ctx;
    \\term im (a b: wff): wff;
    \\infixr im: $→$ prec 25;
    \\term an (a b: wff): wff;
    \\infixr an: $∧$ prec 35;
    \\term not (a: wff): wff;
    \\prefix not: $¬$ prec 40;
    \\term bi (a b: wff): wff;
    \\infixl bi: $↔$ prec 20;
    \\term bot: wff;
    \\notation bot: wff = ($⊥$:max);
    \\term ctx_eq (g h: ctx): wff;
    \\term emp: ctx;
    \\notation emp: ctx = ($∅$:max);
    \\--| @acui ctx_assoc ctx_comm emp ctx_idem
    \\term join (g h: ctx): ctx;
    \\infixl join: $,$ prec 5;
    \\term hyp (a: wff): ctx;
    \\coercion hyp: wff > ctx;
    \\term nd (g: ctx) (a: wff): wff;
    \\infixl nd: $⊢$ prec 1;
    \\--| @relation wff bi biid bitr bisym mpbi
    \\axiom biid (a: wff): $ a ↔ a $;
    \\axiom bitr (a b c: wff): $ a ↔ b $ > $ b ↔ c $ > $ a ↔ c $;
    \\axiom bisym (a b: wff): $ a ↔ b $ > $ b ↔ a $;
    \\axiom mpbi (a b: wff): $ a ↔ b $ > $ a $ > $ b $;
    \\--| @relation ctx ctx_eq ctx_refl ctx_trans ctx_sym _
    \\axiom ctx_refl (g: ctx): $ ctx_eq g g $;
    \\axiom ctx_trans (g h i: ctx):
    \\  $ ctx_eq g h $ > $ ctx_eq h i $ > $ ctx_eq g i $;
    \\axiom ctx_sym (g h: ctx): $ ctx_eq g h $ > $ ctx_eq h g $;
    \\axiom ctx_assoc (g h i: ctx): $ ctx_eq ((g , h) , i) (g , (h , i)) $;
    \\axiom ctx_comm (g h: ctx): $ ctx_eq (g , h) (h , g) $;
    \\axiom ctx_idem (g: ctx): $ ctx_eq (g , g) g $;
    \\axiom ctx_unit (g: ctx): $ ctx_eq (emp , g) g $;
    \\--| @congr
    \\axiom join_congr (g1 g2 h1 h2: ctx):
    \\  $ ctx_eq g1 g2 $ > $ ctx_eq h1 h2 $ > $ ctx_eq (g1 , h1) (g2 , h2) $;
    \\--| @congr
    \\axiom hyp_congr (a b: wff): $ a ↔ b $ > $ ctx_eq (hyp a) (hyp b) $;
    \\--| @congr
    \\axiom nd_congr (e f: ctx) (a b: wff):
    \\  $ ctx_eq e f $ > $ a ↔ b $ > $ (e ⊢ a) ↔ (f ⊢ b) $;
    \\axiom ax (g: ctx) (a: wff): $ g , a ⊢ a $;
    \\axiom contra_left (g: ctx) (a c: wff): $ g , ¬ a , a ⊢ c $;
    \\--| @auto eager
    \\axiom imp_intro (g: ctx) (a b: wff): $ g , a ⊢ b $ > $ g ⊢ a → b $;
    \\--| @auto eager
    \\axiom not_intro (g: ctx) (a: wff): $ g , a ⊢ ⊥ $ > $ g ⊢ ¬ a $;
    \\--| @auto eager 2
    \\axiom and_intro (g: ctx) (a b: wff): $ g ⊢ a $ > $ g ⊢ b $ > $ g ⊢ a ∧ b $;
    \\--| @auto backward
    \\axiom imp_left (g: ctx) (a b c: wff):
    \\  $ g , (a → b) ⊢ a $ > $ g , b ⊢ c $ > $ g , (a → b) ⊢ c $;
    \\--| @auto backward
    \\axiom raa (g: ctx) (a: wff): $ g , ¬ a ⊢ ⊥ $ > $ g ⊢ a $;
    \\
;

fn search(
    arena: *std.heap.ArenaAllocator,
    comptime theorem: []const u8,
    comptime proof: []const u8,
    counters: *types.SearchCounters,
    core: bool,
) !types.SourceSuggestions {
    return suggestionsAtNeedle(arena, nd_rules ++ theorem, proof, "auto?", .{
        .counters = counters,
        .generate = .{ .enabled = true, .core = core },
    });
}

const contrapose =
    \\theorem contrapose (a b: wff): $ ∅ ⊢ (a → b) → ¬ b → ¬ a $;
;
const contrapose_proof =
    \\contrapose
    \\----------
    \\l1: $ ∅ ⊢ (a → b) → ¬ b → ¬ a $ by auto?
;

test "the search core proves a propositional sequent the checker accepts" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    var suggestions = try search(&arena, contrapose, contrapose_proof, &counters, true);
    defer suggestions.deinit();

    try expectOffered(suggestions.items, &.{
        "imp_intro [imp_intro [not_intro [imp_left [ax [], contra_left []]]]]",
    });
    try std.testing.expectEqualStrings("the search core", generate.phaseName(counters.gen_last_phase));
    try std.testing.expectEqual(@as(usize, 1), counters.gen_last_depth);
    try std.testing.expect(counters.core_nodes > 0);
    try std.testing.expectEqual(@as(usize, 0), counters.core_rejects);
}

test "the search core closes a goal with a hypothesis that states it" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    var suggestions = try search(&arena,
        \\theorem pair (g: ctx) (a: wff): $ g ⊢ a $ > $ g ⊢ a ∧ a $;
    ,
        \\pair
        \\----
        \\l1: $ g ⊢ a ∧ a $ by auto?
    , &counters, true);
    defer suggestions.deinit();

    try expectOffered(suggestions.items, &.{"and_intro [#1, #1]"});
    try std.testing.expectEqualStrings("the search core", generate.phaseName(counters.gen_last_phase));
}

test "a goal the search core cannot prove still runs the ladder" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    var suggestions = try search(&arena,
        \\theorem unprovable (a b: wff): $ ∅ ⊢ a → b $;
    ,
        \\unprovable
        \\----------
        \\l1: $ ∅ ⊢ a → b $ by auto?
    , &counters, true);
    defer suggestions.deinit();

    try std.testing.expectEqual(@as(usize, 0), suggestions.items.len);
    try std.testing.expect(counters.core_nodes > 0);
    try std.testing.expect(!std.mem.eql(u8, "the search core", generate.phaseName(counters.gen_last_phase)));
}

test "the search core is off by default" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    var suggestions = try search(&arena, contrapose, contrapose_proof, &counters, false);
    defer suggestions.deinit();

    try std.testing.expect(suggestions.items.len > 0);
    try std.testing.expectEqual(@as(usize, 0), counters.core_nodes);
    try std.testing.expect(!std.mem.eql(u8, "the search core", generate.phaseName(counters.gen_last_phase)));
}
