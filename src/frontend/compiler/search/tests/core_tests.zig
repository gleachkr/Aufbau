//! The search core (`core/`, `GenerateOptions.core`, on by default): it proves
//! sequents over an ACUI context, closing quantifier witnesses by
//! unification under the eigenvariable condition; every proof it returns
//! has passed the checker, and on a miss the generation ladder still runs.

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

test "the search core is on by default" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    var suggestions = try suggestionsAtNeedle(&arena, nd_rules ++ contrapose, contrapose_proof, "auto?", .{
        .counters = &counters,
        .generate = .{ .enabled = true },
    });
    defer suggestions.deinit();

    try std.testing.expect(suggestions.items.len > 0);
    try std.testing.expectEqualStrings("the search core", generate.phaseName(counters.gen_last_phase));
}

test "with the search core off, the ladder alone finds the proof" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    var suggestions = try search(&arena, contrapose, contrapose_proof, &counters, false);
    defer suggestions.deinit();

    try std.testing.expect(suggestions.items.len > 0);
    try std.testing.expectEqual(@as(usize, 0), counters.core_nodes);
    try std.testing.expect(!std.mem.eql(u8, "the search core", generate.phaseName(counters.gen_last_phase)));
}

/// `name: statement` searched with the core on the nd_fol bench fixture,
/// with `extra` declarations appended to it.
fn ndFolSearch(
    arena: *std.heap.ArenaAllocator,
    extra: []const u8,
    comptime name: []const u8,
    comptime statement: []const u8,
    counters: *types.SearchCounters,
    max_depth: usize,
) !types.SourceSuggestions {
    const allocator = arena.allocator();
    const fixture = try std.Io.Dir.cwd().readFileAlloc(std.testing.io, "tests/search_bench_cases/nd_fol.mm0", allocator, .unlimited);
    const mm0_src = try std.mem.concat(allocator, u8, &.{ fixture, extra });
    const underline: [name.len]u8 = @splat('-');
    const proof_src = name ++ "\n" ++ underline ++ "\nl1: $ " ++ statement ++ " $ by auto?\n";
    return suggestionsAtNeedle(arena, mm0_src, proof_src, "auto?", .{
        .counters = counters,
        .generate = .{ .enabled = true, .core = true, .max_depth = max_depth },
    });
}

test "the search core closes a quantifier witness by unification" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    var suggestions = try ndFolSearch(&arena, "", "all_inst", "∅ ⊢ (∀ x P x) → P C", &counters, 6);
    defer suggestions.deinit();

    try expectOffered(suggestions.items, &.{"imp_intro [all_left [ax (g := $ ∀ x P x $) []]]"});
    try std.testing.expectEqualStrings("the search core", generate.phaseName(counters.gen_last_phase));
    try std.testing.expectEqual(@as(usize, 0), counters.core_rejects);
}

test "the search core introduces eigenvariables and closes later witnesses with them" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    var suggestions = try ndFolSearch(&arena, "", "ex_swap", "∅ ⊢ (∃ x ∃ y R x y) → (∃ z ∃ w R w z)", &counters, 6);
    defer suggestions.deinit();

    try expectOffered(suggestions.items, &.{
        "imp_intro [ex_left [ex_left (x := $ y $, p := $ R u y $) [ex_intro [ex_intro (x := $ w $, p := $ R w v $) [ax (g := $ ∅ $, a := $ R u v $) []]]]]]",
    });
    try std.testing.expectEqualStrings("the search core", generate.phaseName(counters.gen_last_phase));
    try std.testing.expectEqual(@as(usize, 0), counters.core_rejects);
}

test "the search core names a witness the proof leaves open" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    var suggestions = try ndFolSearch(&arena, "", "all_ex_inst", "∅ ⊢ (∀ x P x) → (∃ y P y)", &counters, 6);
    defer suggestions.deinit();

    // Any object closes `P ?t ⊢ P ?t`; the first `@vars` name stands in.
    try expectOffered(suggestions.items, &.{"imp_intro [ex_intro [all_left [ax (g := $ ∀ x P x $, a := $ P u $) []]]]"});
    try std.testing.expectEqualStrings("the search core", generate.phaseName(counters.gen_last_phase));
}

test "a witness never takes an eigenvariable introduced after it" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    // Unprovable: closing `R ?s v ⊢ R u ?t` would put `v`, introduced after
    // `?t`, into `?t`. The core must not reach a proof the checker rejects.
    var suggestions = try ndFolSearch(
        &arena,
        "theorem swap_bad {x y: obj}: $ ∅ ⊢ (∀ x ∃ y R x y) → ∃ y ∀ x R x y $;\n",
        "swap_bad",
        "∅ ⊢ (∀ x ∃ y R x y) → ∃ y ∀ x R x y",
        &counters,
        2,
    );
    defer suggestions.deinit();

    try std.testing.expectEqual(@as(usize, 0), suggestions.items.len);
    try std.testing.expect(counters.core_nodes > 0);
    try std.testing.expectEqual(@as(usize, 0), counters.core_rejects);
}

test "an eigenvariable becomes the variable a hypothesis names" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    // `∀` introduction needs a variable the goal does not mention; `#1`
    // states the instances for `z`, which a name picked when the
    // eigenvariable is introduced (the pool's first free one, `y`) misses.
    var suggestions = try ndFolSearch(
        &arena,
        "theorem gen {x z: obj}: $ ∅ ⊢ P z $ > $ ∅ ⊢ ∀ x (P x ∧ P x) $;\n",
        "gen",
        "∅ ⊢ ∀ x (P x ∧ P x)",
        &counters,
        6,
    );
    defer suggestions.deinit();

    try expectOffered(suggestions.items, &.{"all_intro [and_intro [#1, #1]]"});
    try std.testing.expectEqualStrings("the search core", generate.phaseName(counters.gen_last_phase));
    try std.testing.expectEqual(@as(usize, 0), counters.core_rejects);
}

test "a witness in a context member is closed by a hypothesis's context" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    // After `ex_intro` and `imp_intro` the context holds `P t` with `t`
    // open; `#1` closes the goal once the two contexts unify member by
    // member, binding `t` to `C`.
    var suggestions = try ndFolSearch(
        &arena,
        "theorem wit {x: obj}: $ Q C , P C ⊢ R C C $ > $ Q C ⊢ ∃ x (P x → R C C) $;\n",
        "wit",
        "Q C ⊢ ∃ x (P x → R C C)",
        &counters,
        6,
    );
    defer suggestions.deinit();

    try expectOffered(suggestions.items, &.{"ex_intro [imp_intro [#1]]"});
    try std.testing.expectEqualStrings("the search core", generate.phaseName(counters.gen_last_phase));
    try std.testing.expectEqual(@as(usize, 1), counters.gen_last_depth);
}

// `dn a` is `¬ ¬ a` by definition.
const dn_def =
    \\def dn (a: wff): wff = $ ¬ ¬ a $;
    \\
;

test "the search core matches a definition as an ordinary term" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    var suggestions = try search(&arena, dn_def ++
        \\theorem dn_self (a b: wff): $ ∅ ⊢ dn a → b → dn a $;
    ,
        \\dn_self
        \\-------
        \\l1: $ ∅ ⊢ dn a → b → dn a $ by auto?
    , &counters, true);
    defer suggestions.deinit();

    try expectOffered(suggestions.items, &.{"imp_intro [imp_intro [ax []]]"});
    try std.testing.expectEqualStrings("the search core", generate.phaseName(counters.gen_last_phase));
}

test "the search core unfolds a definition to match a rule" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    // `ax` closes `dn a ⊢ ¬ ¬ a` once `dn a` unfolds; the checker accepts
    // the step by unfolding `dn`.
    var suggestions = try search(&arena, dn_def ++
        \\theorem dn_unfold (a: wff): $ ∅ ⊢ dn a → ¬ ¬ a $;
    ,
        \\dn_unfold
        \\---------
        \\l1: $ ∅ ⊢ dn a → ¬ ¬ a $ by auto?
    , &counters, true);
    defer suggestions.deinit();

    try expectOffered(suggestions.items, &.{"imp_intro [ax []]"});
    try std.testing.expectEqualStrings("the search core", generate.phaseName(counters.gen_last_phase));
    try std.testing.expectEqual(@as(usize, 0), counters.core_rejects);
}

test "a definition's dummy is a variable the proof names" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    // `some_p` unfolds to `∃ y P y` with `y` a dummy; `ex_intro` takes the
    // witness `C` from the context, and the dummy, which the printed proof
    // leaves to the checker, is named at close-out.
    var suggestions = try ndFolSearch(
        &arena,
        "def some_p {.y: obj}: wff = $ ∃ y P y $;\n" ++
            "theorem some_p_cc: $ P cc ⊢ some_p $;\n",
        "some_p_cc",
        "P cc ⊢ some_p",
        &counters,
        6,
    );
    defer suggestions.deinit();

    try expectOffered(suggestions.items, &.{"ex_intro [ax (g := $ ∅ $, a := $ P C $) []]"});
    try std.testing.expectEqualStrings("the search core", generate.phaseName(counters.gen_last_phase));
    try std.testing.expectEqual(@as(usize, 0), counters.core_rejects);
}

test "a hypothesis stated with a definition closes the unfolded goal" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    // `#1`'s dummy unifies with the goal's bound `x`.
    var suggestions = try ndFolSearch(
        &arena,
        "def all_q {.y: obj}: wff = $ ∀ y Q y $;\n" ++
            "theorem all_q_use {x: obj}: $ ∅ ⊢ all_q $ > $ ∅ ⊢ (∀ x Q x) ∧ (∀ x Q x) $;\n",
        "all_q_use",
        "∅ ⊢ (∀ x Q x) ∧ (∀ x Q x)",
        &counters,
        6,
    );
    defer suggestions.deinit();

    try expectOffered(suggestions.items, &.{"and_intro [#1, #1]"});
    try std.testing.expectEqualStrings("the search core", generate.phaseName(counters.gen_last_phase));
}

test "a definition's dummy never becomes a variable its arguments hold" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    // `other x` unfolds to `∀ y (P y → P x)`; reading `#1` as that unfolding
    // would make the dummy `x` and capture the argument.
    var suggestions = try ndFolSearch(
        &arena,
        "def other {.y: obj} (a: obj): wff = $ ∀ y (P y → P a) $;\n" ++
            "theorem capture {x: obj}: $ ∅ ⊢ ∀ x (P x → P x) $ > $ ∅ ⊢ other x ∧ other x $;\n",
        "capture",
        "∅ ⊢ other x ∧ other x",
        &counters,
        2,
    );
    defer suggestions.deinit();

    try std.testing.expect(counters.core_nodes > 0);
    try std.testing.expectEqual(@as(usize, 0), counters.core_rejects);
    try std.testing.expect(!std.mem.eql(u8, "the search core", generate.phaseName(counters.gen_last_phase)));
}

test "a definition's dummy never becomes an ordinary variable" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    // `all_p` unfolds to `∀ y P y`; `gen`, tried first, keeps the dummy as
    // its bound variable, and `ax` would then make it `a`, which is not a
    // bound variable at all. Unprovable, and the core must not hand the checker
    // that proof.
    var suggestions = try ndFolSearch(
        &arena,
        "def all_p {.y: obj}: wff = $ ∀ y P y $;\n" ++
            "--| @auto eager 1\naxiom gen {x: obj} (g: ctx) (p: wff x): $ g ⊢ p $ > $ g ⊢ ∀ x p $;\n" ++
            "theorem all_p_bad (a: obj): $ P a ⊢ all_p $;\n",
        "all_p_bad",
        "P a ⊢ all_p",
        &counters,
        2,
    );
    defer suggestions.deinit();

    try std.testing.expect(counters.core_nodes > 0);
    try std.testing.expectEqual(@as(usize, 0), counters.core_rejects);
    try std.testing.expect(!std.mem.eql(u8, "the search core", generate.phaseName(counters.gen_last_phase)));
}

test "the search core proves a premise in its rewrite normal form" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    // `twice_intro`'s premise holds the redex `dbl a`, which rewrites to
    // `a ∧ a`; the checker accepts the step by normalizing the premise.
    var suggestions = try search(&arena,
        \\term dbl (a: wff): wff;
        \\--| @rewrite
        \\axiom dbl_an (a: wff): $ dbl a ↔ a ∧ a $;
        \\term twice (a: wff): wff;
        \\axiom twice_intro (g: ctx) (a: wff): $ g ⊢ dbl a $ > $ g ⊢ twice a $;
        \\theorem twice_a (a: wff): $ a ⊢ twice a $;
    ,
        \\twice_a
        \\-------
        \\l1: $ a ⊢ twice a $ by auto?
    , &counters, true);
    defer suggestions.deinit();

    try expectOffered(suggestions.items, &.{"twice_intro [and_intro [ax [], ax []]]"});
    try std.testing.expectEqualStrings("the search core", generate.phaseName(counters.gen_last_phase));
    try std.testing.expectEqual(@as(usize, 0), counters.core_rejects);
}

// `dn T` stated by an axiom: proving `¬ ¬ T` from it unfolds the rule's
// conclusion, which the core does not do.
const dn_axiom =
    \\term T: wff;
    \\axiom t_dn: $ ∅ ⊢ dn T $;
    \\theorem dn_t: $ ∅ ⊢ ¬ ¬ T ∧ ¬ ¬ T $;
;
const dn_axiom_proof =
    \\dn_t
    \\----
    \\l1: $ ∅ ⊢ ¬ ¬ T ∧ ¬ ¬ T $ by auto?
;

test "a goal that needs a rule's definition unfolded goes on to the ladder" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    var suggestions = try search(&arena, dn_def ++ dn_axiom, dn_axiom_proof, &counters, true);
    defer suggestions.deinit();

    try std.testing.expect(suggestions.items.len > 0);
    try std.testing.expect(counters.core_nodes > 0);
    try std.testing.expect(!std.mem.eql(u8, "the search core", generate.phaseName(counters.gen_last_phase)));
}

test "with the ladder off, a goal the search core cannot prove has no proof" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    // The ladder proves this goal (test above).
    var suggestions = try suggestionsAtNeedle(&arena, nd_rules ++ dn_def ++ dn_axiom, dn_axiom_proof, "auto?", .{
        .counters = &counters,
        .generate = .{ .enabled = true, .ladder = false },
    });
    defer suggestions.deinit();

    try std.testing.expectEqual(@as(usize, 0), suggestions.items.len);
    try std.testing.expect(counters.core_nodes > 0);
}
