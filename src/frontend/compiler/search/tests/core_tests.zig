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
    options: struct { max_depth: usize = 6, ladder: bool = true, fixture: []const u8 = "nd_fol" },
) !types.SourceSuggestions {
    const allocator = arena.allocator();
    const path = try std.fmt.allocPrint(allocator, "tests/search_bench_cases/{s}.mm0", .{options.fixture});
    const fixture = try std.Io.Dir.cwd().readFileAlloc(std.testing.io, path, allocator, .unlimited);
    const mm0_src = try std.mem.concat(allocator, u8, &.{ fixture, extra });
    const underline: [name.len]u8 = @splat('-');
    const proof_src = name ++ "\n" ++ underline ++ "\nl1: $ " ++ statement ++ " $ by auto?\n";
    return suggestionsAtNeedle(arena, mm0_src, proof_src, "auto?", .{
        .counters = counters,
        .generate = .{ .enabled = true, .core = true, .max_depth = options.max_depth, .ladder = options.ladder },
    });
}

test "the search core closes a quantifier witness by unification" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    var suggestions = try ndFolSearch(&arena, "", "all_inst", "∅ ⊢ (∀ x P x) → P C", &counters, .{ .max_depth = 6 });
    defer suggestions.deinit();

    try expectOffered(suggestions.items, &.{"imp_intro [all_elim [ax []]]"});
    try std.testing.expectEqualStrings("the search core", generate.phaseName(counters.gen_last_phase));
    try std.testing.expectEqual(@as(usize, 0), counters.core_rejects);
}

test "the search core introduces eigenvariables and closes later witnesses with them" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    var suggestions = try ndFolSearch(&arena, "", "ex_swap", "∅ ⊢ (∃ x ∃ y R x y) → (∃ z ∃ w R w z)", &counters, .{ .max_depth = 6 });
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
    var suggestions = try ndFolSearch(&arena, "", "all_ex_inst", "∅ ⊢ (∀ x P x) → (∃ y P y)", &counters, .{ .max_depth = 6 });
    defer suggestions.deinit();

    // Any object closes `[x/?t] P x` from `∀ x P x`; the first `@vars`
    // name stands in.
    try expectOffered(suggestions.items, &.{"imp_intro [ex_intro [all_elim (t := $ u $) [ax []]]]"});
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
        .{ .max_depth = 2 },
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
        .{ .max_depth = 6 },
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
        .{ .max_depth = 6 },
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
        .{ .max_depth = 6 },
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
        .{ .max_depth = 6 },
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
        .{ .max_depth = 2 },
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
        .{ .max_depth = 2 },
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

test "the search core unfolds a rule's definition to match a goal" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    // `t_dn` states `dn T`; the goal holds its unfolding `¬ ¬ T`.
    var suggestions = try search(&arena, dn_def ++
        \\term T: wff;
        \\axiom t_dn: $ ∅ ⊢ dn T $;
        \\theorem dn_t: $ ∅ ⊢ ¬ ¬ T ∧ ¬ ¬ T $;
    ,
        \\dn_t
        \\----
        \\l1: $ ∅ ⊢ ¬ ¬ T ∧ ¬ ¬ T $ by auto?
    , &counters, true);
    defer suggestions.deinit();

    try expectOffered(suggestions.items, &.{"and_intro [t_dn [], t_dn []]"});
    try std.testing.expectEqualStrings("the search core", generate.phaseName(counters.gen_last_phase));
    try std.testing.expectEqual(@as(usize, 0), counters.core_rejects);
}

// `all_p` stated by an axiom: proving `∀ x P x` from it unfolds the
// axiom's conclusion, whose dummy the core has no binder for
// (`Terms.unfoldTemplate`).
const all_p_axiom =
    "def all_p {.y: obj}: wff = $ ∀ y P y $;\n" ++
    "axiom all_p_ax (g: ctx): $ g ⊢ all_p $;\n" ++
    "theorem all_p_x {x: obj}: $ ∅ ⊢ ∀ x P x ∧ ∀ x P x $;\n";

test "a goal that needs a rule's definition with a dummy unfolded goes on to the ladder" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    var suggestions = try ndFolSearch(&arena, all_p_axiom, "all_p_x", "∅ ⊢ ∀ x P x ∧ ∀ x P x", &counters, .{});
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
    var suggestions = try ndFolSearch(&arena, all_p_axiom, "all_p_x", "∅ ⊢ ∀ x P x ∧ ∀ x P x", &counters, .{ .ladder = false });
    defer suggestions.deinit();

    try std.testing.expectEqual(@as(usize, 0), suggestions.items.len);
    try std.testing.expect(counters.core_nodes > 0);
}

// `imp_elim`'s `a` is a cut: the conclusion does not fix it.
const imp_elim_rule =
    \\axiom imp_elim (g: ctx) (a b: wff): $ g ⊢ a → b $ > $ g ⊢ a $ > $ g ⊢ b $;
    \\
;

test "the search core closes a cut by unification with a hypothesis" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    var suggestions = try search(&arena, imp_elim_rule ++
        \\theorem mp_hyps (g: ctx) (a b: wff): $ g ⊢ a → b $ > $ g ⊢ a $ > $ g ⊢ b $;
    ,
        \\mp_hyps
        \\-------
        \\l1: $ g ⊢ b $ by auto?
    , &counters, true);
    defer suggestions.deinit();

    try expectOffered(suggestions.items, &.{"imp_elim [#1, #2]"});
    try std.testing.expectEqualStrings("the search core", generate.phaseName(counters.gen_last_phase));
    try std.testing.expectEqual(@as(usize, 0), counters.core_rejects);
}

// `valid_intro`'s `w` is an eigenvariable its premise states directly.
const valid_rules =
    \\--| @vars w v
    \\sort world;
    \\term sat (w: world) (a: wff): wff;
    \\term valid (a: wff): wff;
    \\axiom valid_intro {w: world} (a: wff): $ ∅ ⊢ sat w (a → a) $ > $ valid (a → a) $;
    \\axiom sat_refl (g: ctx) (w: world) (a: wff): $ g ⊢ sat w (a → a) $;
    \\
;

test "the search core introduces an eigenvariable a premise states without a view" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    var suggestions = try search(&arena, valid_rules ++
        \\theorem valid_refl (a: wff): $ valid (a → a) $;
    ,
        \\valid_refl
        \\----------
        \\l1: $ valid (a → a) $ by auto?
    , &counters, true);
    defer suggestions.deinit();

    try expectOffered(suggestions.items, &.{"valid_intro [sat_refl (w := $ v $) []]"});
    try std.testing.expectEqualStrings("the search core", generate.phaseName(counters.gen_last_phase));
    try std.testing.expectEqual(@as(usize, 0), counters.core_rejects);
}

// Hilbert-style modus ponens: the conclusion `b` is a bare binder, `a` a cut.
const hilbert_rules =
    \\axiom mp (a b: wff): $ a → b $ > $ a $ > $ b $;
    \\axiom and_elim_l_imp (a b: wff): $ a ∧ b → a $;
    \\
;

test "the search core fixes a cut from a hypothesis before the premise only a closer proves" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    // No pool fact fits `?a → a`, so the bare premise `?a` goes first and
    // the hypothesis fixes it; the closer cannot give `?a` its structure.
    var suggestions = try search(&arena, hilbert_rules ++
        \\theorem and_elim_l (a b: wff): $ a ∧ b $ > $ a $;
    ,
        \\and_elim_l
        \\----------
        \\l1: $ a $ by auto?
    , &counters, true);
    defer suggestions.deinit();

    try expectOffered(suggestions.items, &.{"mp [and_elim_l_imp [], #1]"});
    try std.testing.expectEqualStrings("the search core", generate.phaseName(counters.gen_last_phase));
    try std.testing.expectEqual(@as(usize, 0), counters.core_rejects);
}

test "two bare premises wait for the sibling that fixes them" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    // No fact fits `?a → ?b → p ∧ q`, but the closer `and_i` does and fixes
    // both; closing `?a` and `?b` from the six hypotheses first tries the
    // pairs against it (37 goals instead of 4).
    var suggestions = try search(&arena,
        \\axiom mp2 (a b c: wff): $ a $ > $ b $ > $ a → b → c $ > $ c $;
        \\axiom and_i (a b: wff): $ a → b → a ∧ b $;
        \\term r (n: wff): wff;
        \\theorem pair (p q s: wff): $ r s $ > $ r p $ > $ r q $ > $ r (r s) $ > $ p $ > $ q $ > $ p ∧ q $;
    ,
        \\pair
        \\----
        \\l1: $ p ∧ q $ by auto?
    , &counters, true);
    defer suggestions.deinit();

    try expectOffered(suggestions.items, &.{"mp2 [#5, #6, and_i []]"});
    try std.testing.expectEqualStrings("the search core", generate.phaseName(counters.gen_last_phase));
    try std.testing.expect(counters.core_nodes <= 8);
}

// A forward rule joining two contexts that the core leaves out: as a
// bridge it only links facts in hand.
const join_rules =
    \\--| @auto forward
    \\--| @auto bridge
    \\axiom imp_elim_m (g h: ctx) (a b: wff): $ g ⊢ a → b $ > $ h ⊢ a $ > $ g , h ⊢ b $;
    \\
;

test "the search core closes a goal with a fact forward saturation derived" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    var suggestions = try search(&arena, join_rules ++
        \\theorem join_mp (g h: ctx) (a b: wff): $ g ⊢ a → b $ > $ h ⊢ a $ > $ g , h ⊢ b $;
    ,
        \\join_mp
        \\-------
        \\l1: $ g , h ⊢ b $ by auto?
    , &counters, true);
    defer suggestions.deinit();

    try expectOffered(suggestions.items, &.{"imp_elim_m [#1, #2]"});
    try std.testing.expectEqualStrings("the search core", generate.phaseName(counters.gen_last_phase));
    try std.testing.expectEqual(@as(usize, 0), counters.core_rejects);
}

test "the search core closes premises with a fact forward saturation derived" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    var suggestions = try search(&arena, join_rules ++
        \\theorem join_mp_pair (g h: ctx) (a b: wff):
        \\  $ g ⊢ a → b $ > $ h ⊢ a $ > $ g , h ⊢ b ∧ b $;
    ,
        \\join_mp_pair
        \\------------
        \\l1: $ g , h ⊢ b ∧ b $ by auto?
    , &counters, true);
    defer suggestions.deinit();

    try expectOffered(suggestions.items, &.{"and_intro [imp_elim_m [#1, #2], imp_elim_m [#1, #2]]"});
    try std.testing.expectEqualStrings("the search core", generate.phaseName(counters.gen_last_phase));
    try std.testing.expectEqual(@as(usize, 0), counters.core_rejects);
}

// The conclusions' bags have two rest binders, which split the goal's
// context between the premises.
const split_rules =
    \\axiom imp_elim_s (g h: ctx) (a b: wff): $ g ⊢ a → b $ > $ h ⊢ a $ > $ g , h ⊢ b $;
    \\axiom weaken_s (g h: ctx) (a: wff): $ g ⊢ a $ > $ g , h ⊢ a $;
    \\
;

const cut_rule =
    \\axiom cut_s (g h: ctx) (a b: wff): $ g ⊢ a $ > $ h , a ⊢ b $ > $ g , h ⊢ b $;
    \\
;

test "the search core splits a context between the hypotheses that close a rule's premises" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    var suggestions = try search(&arena, split_rules ++
        \\theorem split_mp (g h: ctx) (a b: wff): $ g ⊢ a → b $ > $ h ⊢ a $ > $ g , h ⊢ b $;
    ,
        \\split_mp
        \\--------
        \\l1: $ g , h ⊢ b $ by auto?
    , &counters, true);
    defer suggestions.deinit();

    try expectOffered(suggestions.items, &.{"imp_elim_s [#1, #2]"});
    try std.testing.expectEqualStrings("the search core", generate.phaseName(counters.gen_last_phase));
    try std.testing.expectEqual(@as(usize, 0), counters.core_rejects);
}

test "a hypothesis fixes a share that sits beside other members" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    // `#2` states `h , k , a ⊢ b`: the share beside `a` takes `h , k`.
    var suggestions = try search(&arena, cut_rule ++
        \\theorem cut_hyps (g h k: ctx) (a b: wff):
        \\  $ g ⊢ a $ > $ h , k , a ⊢ b $ > $ g , h , k ⊢ b ∧ b $;
    ,
        \\cut_hyps
        \\--------
        \\l1: $ g , h , k ⊢ b ∧ b $ by auto?
    , &counters, true);
    defer suggestions.deinit();

    try expectOffered(suggestions.items, &.{"and_intro [cut_s [#1, #2], cut_s [#1, #2]]"});
    try std.testing.expectEqualStrings("the search core", generate.phaseName(counters.gen_last_phase));
    try std.testing.expectEqual(@as(usize, 0), counters.core_rejects);
}

test "a share a hypothesis leaves open takes the rest of the context" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    // `#1` fixes the first share to `g`; the second takes `h`, which `#2`
    // needs exactly.
    var suggestions = try search(&arena, split_rules ++
        \\theorem rest_mp (g h: ctx) (a b: wff): $ g ⊢ a ∧ a → b $ > $ h ⊢ a $ > $ g , h ⊢ b $;
    ,
        \\rest_mp
        \\-------
        \\l1: $ g , h ⊢ b $ by auto?
    , &counters, true);
    defer suggestions.deinit();

    try expectOffered(suggestions.items, &.{"imp_elim_s [#1, and_intro [#2, #2]]"});
    try std.testing.expectEqualStrings("the search core", generate.phaseName(counters.gen_last_phase));
    try std.testing.expectEqual(@as(usize, 0), counters.core_rejects);
}

test "a share takes the whole context when the rest is not enough" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    // `#1` takes the whole context, so `ax` needs all of it again.
    var suggestions = try search(&arena, split_rules ++
        \\theorem whole_mp (g: ctx) (a b: wff): $ g , a ⊢ a → b $ > $ g , a ⊢ b $;
    ,
        \\whole_mp
        \\--------
        \\l1: $ g , a ⊢ b $ by auto?
    , &counters, true);
    defer suggestions.deinit();

    try expectOffered(suggestions.items, &.{"imp_elim_s [#1, ax (g := $ g $, a := $ a $) []]"});
    try std.testing.expectEqualStrings("the search core", generate.phaseName(counters.gen_last_phase));
    try std.testing.expectEqual(@as(usize, 0), counters.core_rejects);
}

test "a share no premise holds takes the rest of the context" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    var suggestions = try search(&arena, split_rules ++
        \\theorem weak (g h: ctx) (a: wff): $ g ⊢ a $ > $ g , h ⊢ a ∧ a $;
    ,
        \\weak
        \\----
        \\l1: $ g , h ⊢ a ∧ a $ by auto?
    , &counters, true);
    defer suggestions.deinit();

    try expectOffered(suggestions.items, &.{"and_intro [weaken_s [#1], weaken_s [#1]]"});
    try std.testing.expectEqualStrings("the search core", generate.phaseName(counters.gen_last_phase));
    try std.testing.expectEqual(@as(usize, 0), counters.core_rejects);
}

test "shares never hold what the goal's context does not" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    // `#1` would put `h` into a share of `g`'s context.
    var suggestions = try suggestionsAtNeedle(&arena, nd_rules ++ split_rules ++
        \\theorem stray_mp (g h: ctx) (a b: wff): $ h ⊢ a → b $ > $ g ⊢ a $ > $ g ⊢ b $;
    ,
        \\stray_mp
        \\--------
        \\l1: $ g ⊢ b $ by auto?
    , "auto?", .{
        .counters = &counters,
        .generate = .{ .enabled = true, .ladder = false },
    });
    defer suggestions.deinit();

    try std.testing.expectEqual(@as(usize, 0), suggestions.items.len);
    try std.testing.expect(counters.core_nodes > 0);
    try std.testing.expectEqual(@as(usize, 0), counters.core_rejects);
}

// `name_elim`'s eigenvariable `z` sits in the minor premise's context,
// which `imp_elim_s` splits; the hypotheses closing the split's premises
// name it `y`, and only placing their `P y` among the context's members
// makes `z` that variable.
test "a share's member names the eigenvariable a context member holds" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    var suggestions = try search(&arena, split_rules ++
        \\sort obj;
        \\term P (a: obj): wff;
        \\term Q: wff;
        \\term R: wff;
        \\term S: wff;
        \\axiom name_elim {z: obj} (g h: ctx) (c: wff): $ g ⊢ R $ > $ h , P z ⊢ c $ > $ g , h ⊢ c $;
        \\theorem name_mp (g h: ctx) {y: obj}:
        \\  $ g ⊢ R $ > $ h , P y ⊢ S → Q $ > $ P y ⊢ S $ > $ g , h ⊢ Q $;
    ,
        \\name_mp
        \\-------
        \\l1: $ g , h ⊢ Q $ by auto?
    , &counters, true);
    defer suggestions.deinit();

    try expectOffered(suggestions.items, &.{"name_elim [#1, imp_elim_s [#2, #3]]"});
    try std.testing.expectEqualStrings("the search core", generate.phaseName(counters.gen_last_phase));
    try std.testing.expectEqual(@as(usize, 0), counters.core_rejects);
}

// `ex_elim2`'s `z` is bound and only its premises hold it, though the
// contexts may depend on it; its view reads back nothing. The core takes
// `z` for an eigenvariable, which the first hypothesis names `x`.
test "a bound binder the contexts may depend on is an eigenvariable" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    var suggestions = try search(&arena,
        \\--| @vars x y
        \\sort obj;
        \\term ex {x: obj} (p: wff x): wff;
        \\term P (a: obj): wff;
        \\term Q: wff;
        \\--| @view {z: obj} (g h: ctx z) (p: wff z) (c: wff): $ g ⊢ ex z p $ > $ h , p ⊢ c $ > $ g , h ⊢ c $
        \\--| @freshen c z
        \\axiom ex_elim2 {z: obj} (g h: ctx z) (p: wff z) (c: wff):
        \\  $ g ⊢ ex z p $ > $ h , p ⊢ c $ > $ g , h ⊢ c $;
        \\theorem ex_q (g h: ctx) {x: obj}: $ g ⊢ ex x (P x) $ > $ h , P x ⊢ Q $ > $ g , h ⊢ Q ∧ Q $;
    ,
        \\ex_q
        \\----
        \\l1: $ g , h ⊢ Q ∧ Q $ by auto?
    , &counters, true);
    defer suggestions.deinit();

    try expectOffered(suggestions.items, &.{"and_intro [ex_elim2 [#1, #2], ex_elim2 [#1, #2]]"});
    try std.testing.expectEqualStrings("the search core", generate.phaseName(counters.gen_last_phase));
    try std.testing.expectEqual(@as(usize, 0), counters.core_rejects);
}

// `le_trans`'s `y` is shared by both premises. The first premise's fact
// `suc a ≤ b` gives `y = b`, and `b ≤ c` has no proof; the second
// premise's fact `suc b ≤ c` gives `y = suc b`, and the first premise
// then follows by `le_suc_suc`.
test "a step whose first premise fixes a cut wrongly retries with another first" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    var suggestions = try search(&arena,
        \\sort obj;
        \\term suc (a: obj): obj;
        \\term le (a b: obj): wff;
        \\infixl le: $≤$ prec 30;
        \\axiom le_trans (g h: ctx) (x y z: obj):
        \\  $ g ⊢ x ≤ y $ > $ h ⊢ y ≤ z $ > $ g , h ⊢ x ≤ z $;
        \\axiom le_suc_suc (g: ctx) (a b: obj): $ g ⊢ a ≤ b $ > $ g ⊢ suc a ≤ suc b $;
        \\theorem le_chain (g h: ctx) (a b c: obj):
        \\  $ g ⊢ suc a ≤ b $ > $ h ⊢ suc b ≤ c $ > $ g ⊢ a ≤ b $ > $ g , h ⊢ suc a ≤ c $;
    ,
        \\le_chain
        \\--------
        \\l1: $ g , h ⊢ suc a ≤ c $ by auto?
    , &counters, true);
    defer suggestions.deinit();

    try expectOffered(suggestions.items, &.{"le_trans [le_suc_suc [#3], #2]"});
    try std.testing.expectEqualStrings("the search core", generate.phaseName(counters.gen_last_phase));
    try std.testing.expectEqual(@as(usize, 0), counters.core_rejects);
}

// The goal's context mentions `x`, under `ex`; `g` may depend on
// `ex_elim3`'s `z`, so `z` still becomes `x`, which only `h` and `c` must
// not mention.
test "an eigenvariable becomes a variable only dependent arguments mention" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    var suggestions = try search(&arena,
        \\--| @vars x y
        \\sort obj;
        \\term ex {x: obj} (p: wff x): wff;
        \\term P (a: obj): wff;
        \\term Q: wff;
        \\--| @freshen h z
        \\--| @freshen c z
        \\axiom ex_elim3 {z: obj} (g: ctx z) (h: ctx) (p: wff z) (c: wff):
        \\  $ g ⊢ ex z p $ > $ h , p ⊢ c $ > $ g , h ⊢ c $;
        \\theorem ex_q3 (h: ctx) {x: obj}:
        \\  $ ex x (P x) ⊢ ex x (P x) $ > $ h , P x ⊢ Q $ > $ ex x (P x) , h ⊢ Q ∧ Q $;
    ,
        \\ex_q3
        \\-----
        \\l1: $ ex x (P x) , h ⊢ Q ∧ Q $ by auto?
    , &counters, true);
    defer suggestions.deinit();

    try expectOffered(suggestions.items, &.{"and_intro [ex_elim3 [#1, #2], ex_elim3 [#1, #2]]"});
    try std.testing.expectEqualStrings("the search core", generate.phaseName(counters.gen_last_phase));
    try std.testing.expectEqual(@as(usize, 0), counters.core_rejects);
}

// `has_P a` unfolds to `holds y a (P y)` with its dummy `y` an
// eigenvariable; `holds_intro`'s premise `sb y a (P y)` then has the
// normal form `P a`, with `y` read as a fresh bound variable.
test "a goal holding a definition's dummy is tried in its normal form" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    var suggestions = try search(&arena,
        \\--| @vars x y
        \\sort obj;
        \\term sb {x: obj} (t: obj) (p: wff x): wff;
        \\term P (a: obj): wff;
        \\--| @rewrite
        \\axiom sb_P {x: obj} (t: obj): $ sb x t (P x) ↔ P t $;
        \\term holds {x: obj} (t: obj) (p: wff x): wff;
        \\axiom holds_intro {x: obj} (g: ctx) (t: obj) (p: wff x):
        \\  $ g ⊢ sb x t p $ > $ g ⊢ holds x t p $;
        \\def has_P (t: obj) (.y: obj): wff = $ holds y t (P y) $;
        \\theorem has_p_both (g: ctx) (a: obj): $ g ⊢ P a $ > $ g ⊢ has_P a ∧ has_P a $;
    ,
        \\has_p_both
        \\----------
        \\l1: $ g ⊢ has_P a ∧ has_P a $ by auto?
    , &counters, true);
    defer suggestions.deinit();

    try expectOffered(suggestions.items, &.{"and_intro [holds_intro [#1], holds_intro [#1]]"});
    try std.testing.expectEqualStrings("the search core", generate.phaseName(counters.gen_last_phase));
    try std.testing.expectEqual(@as(usize, 0), counters.core_rejects);
}

// `or_elim`'s minor premises each fit `#2`, which would make `q` the `a`
// of `p`; the major premise holds both `p` and `q` and a hypothesis
// stated with `either` fixes them, so it goes first. The second minor
// premise then needs `b_c`, a rule no hypothesis closes.
test "the premise holding the most shared cuts goes first" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    var suggestions = try search(&arena,
        \\term or (a b: wff): wff;
        \\infixr or: $∨$ prec 30;
        \\axiom or_elim (g h k: ctx) (p q r: wff):
        \\  $ g ⊢ p ∨ q $ > $ h , p ⊢ r $ > $ k , q ⊢ r $ > $ g , h , k ⊢ r $;
        \\term A: wff;
        \\term B: wff;
        \\term C: wff;
        \\def either: wff = $ A ∨ B $;
        \\axiom b_c (g: ctx): $ g ⊢ B $ > $ g ⊢ C $;
        \\theorem cases (g h: ctx): $ g ⊢ either $ > $ h , A ⊢ C $ > $ g , h ⊢ C $;
    ,
        \\cases
        \\-----
        \\l1: $ g , h ⊢ C $ by auto?
    , &counters, true);
    defer suggestions.deinit();

    try std.testing.expect(suggestions.items.len > 0);
    try std.testing.expectEqualStrings("the search core", generate.phaseName(counters.gen_last_phase));
    try std.testing.expectEqual(@as(usize, 0), counters.core_rejects);
}

// `has_c` unfolds to `holds y c (P y)`, which does not mention `a`; the
// proof keeps the dummy, and naming it `a`, first in the `@vars` pool but
// an ordinary variable, would fail the checker.
test "an eigenvariable is named by a bound variable" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    var suggestions = try search(&arena,
        \\--| @vars a x y
        \\sort obj;
        \\term sb {x: obj} (t: obj) (p: wff x): wff;
        \\term P (a: obj): wff;
        \\term c: obj;
        \\--| @rewrite
        \\axiom sb_P {x: obj} (t: obj): $ sb x t (P x) ↔ P t $;
        \\term holds {x: obj} (t: obj) (p: wff x): wff;
        \\axiom holds_intro {x: obj} (g: ctx) (t: obj) (p: wff x):
        \\  $ g ⊢ sb x t p $ > $ g ⊢ holds x t p $;
        \\def has_c (.y: obj): wff = $ holds y c (P y) $;
        \\theorem has_c_both (g: ctx) (a: obj): $ g , P a ⊢ P c $ > $ g , P a ⊢ has_c ∧ has_c $;
    ,
        \\has_c_both
        \\----------
        \\l1: $ g , P a ⊢ has_c ∧ has_c $ by auto?
    , &counters, true);
    defer suggestions.deinit();

    try expectOffered(suggestions.items, &.{"and_intro [holds_intro [#1], holds_intro [#1]]"});
    try std.testing.expectEqualStrings("the search core", generate.phaseName(counters.gen_last_phase));
    try std.testing.expectEqual(@as(usize, 0), counters.core_rejects);
}

// Contexts as sequences (`martin_lof`'s `join`): `@acui` with neither
// commutativity nor idempotence. `ax` takes the last entry only.
const seq_rules =
    \\delimiter $ ( ) $;
    \\provable sort wff;
    \\sort ctx;
    \\term im (a b: wff): wff;
    \\infixr im: $→$ prec 25;
    \\term an (a b: wff): wff;
    \\infixr an: $∧$ prec 35;
    \\term bi (a b: wff): wff;
    \\infixl bi: $↔$ prec 20;
    \\term ctx_eq (g h: ctx): wff;
    \\term emp: ctx;
    \\notation emp: ctx = ($∅$:max);
    \\--| @acui ctx_assoc _ emp _
    \\term join (g h: ctx): ctx;
    \\infixl join: $,$ prec 5;
    \\term hyp (a: wff): ctx;
    \\coercion hyp: wff > ctx;
    \\term nd (g: ctx) (a: wff): wff;
    \\infixl nd: $⊢$ prec 1;
    \\term ok (g: ctx): wff;
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
    \\--| @auto eager
    \\axiom imp_intro (g: ctx) (a b: wff): $ g , a ⊢ b $ > $ g ⊢ a → b $;
    \\--| @auto eager 2
    \\axiom and_intro (g: ctx) (a b: wff): $ g ⊢ a $ > $ g ⊢ b $ > $ g ⊢ a ∧ b $;
    \\
;

const seq_weaken =
    \\axiom wk (g: ctx) (a b: wff): $ g ⊢ a $ > $ g , b ⊢ a $;
    \\
;

fn seqSearch(
    arena: *std.heap.ArenaAllocator,
    comptime theorem: []const u8,
    comptime proof: []const u8,
    counters: *types.SearchCounters,
) !types.SourceSuggestions {
    return suggestionsAtNeedle(arena, seq_rules ++ theorem, proof, "auto?", .{
        .counters = counters,
        .generate = .{ .enabled = true, .ladder = false },
    });
}

test "the search core takes a context entry only at its place in a sequence" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    // `a` is not the last entry once `b` is assumed, so `ax` needs `wk`.
    var suggestions = try seqSearch(&arena, seq_weaken ++
        \\theorem k_seq (g: ctx) (a b: wff): $ g ⊢ a → b → a $;
    ,
        \\k_seq
        \\-----
        \\l1: $ g ⊢ a → b → a $ by auto?
    , &counters);
    defer suggestions.deinit();

    try expectOffered(suggestions.items, &.{"imp_intro [imp_intro [wk [ax []]]]"});
    try std.testing.expectEqualStrings("the search core", generate.phaseName(counters.gen_last_phase));
    try std.testing.expectEqual(@as(usize, 0), counters.core_rejects);
}

test "a sequence's earlier entry does not close the goal" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    // `#1` makes `a` an older term than `b`, so a context read in term
    // order would put `b` last and let `ax` close the goal.
    var suggestions = try seqSearch(&arena,
        \\theorem not_last (g: ctx) (a b: wff): $ ∅ , a ⊢ a $ > $ g , b , a ⊢ b $;
    ,
        \\not_last
        \\--------
        \\l1: $ g , b , a ⊢ b $ by auto?
    , &counters);
    defer suggestions.deinit();

    try std.testing.expectEqual(@as(usize, 0), suggestions.items.len);
    try std.testing.expect(counters.core_nodes > 0);
    try std.testing.expectEqual(@as(usize, 0), counters.core_rejects);
}

test "an open context in a sequence takes the run of entries around which the rest pair up" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    // `strengthen`'s `h` is a cut that only `#1` can fix: to `b , c`.
    var suggestions = try seqSearch(&arena,
        \\axiom strengthen (g h: ctx) (a: wff): $ g , h ⊢ a $ > $ g ⊢ a $;
        \\theorem drop_two (g: ctx) (a b c: wff): $ g , b , c ⊢ a $ > $ g ⊢ a $;
    ,
        \\drop_two
        \\--------
        \\l1: $ g ⊢ a $ by auto?
    , &counters);
    defer suggestions.deinit();

    try expectOffered(suggestions.items, &.{"strengthen [#1]"});
    try std.testing.expectEqualStrings("the search core", generate.phaseName(counters.gen_last_phase));
    try std.testing.expectEqual(@as(usize, 0), counters.core_rejects);
}

// A substitution `sb x t p` the theory's `@rewrite` rules push inwards.
const sb_rules =
    \\--| @vars x y
    \\sort obj;
    \\term P (a: obj): wff;
    \\term sb {x: obj} (t: obj) (p: wff x): wff;
    \\--| @rewrite
    \\axiom sb_P {x: obj} (t: obj): $ sb x t (P x) ↔ P t $;
    \\--| @rewrite
    \\axiom sb_free {x: obj} (t: obj) (a: wff): $ sb x t a ↔ a $;
    \\term pick {x: obj} (p: wff x) (t: obj): wff;
    \\term both (a b: wff): wff;
    \\--| @congr
    \\axiom both_congr (a b c d: wff): $ a ↔ b $ > $ c ↔ d $ > $ both a c ↔ both b d $;
    \\
;

fn sbSearch(
    arena: *std.heap.ArenaAllocator,
    comptime theorem: []const u8,
    comptime proof: []const u8,
    counters: *types.SearchCounters,
) !types.SourceSuggestions {
    return suggestionsAtNeedle(arena, nd_rules ++ sb_rules ++ theorem, proof, "auto?", .{
        .counters = counters,
        .generate = .{ .enabled = true, .ladder = false },
    });
}

test "a rule's conclusion holds a substitution the rest of it fixes" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    // `pick x p t` fixes the substitution, whose normal form `P c` meets
    // the goal's.
    var suggestions = try sbSearch(&arena,
        \\axiom pick_both (g: ctx) {x: obj} (p: wff x) (t: obj):
        \\  $ g ⊢ pick x p t $ > $ g ⊢ both (pick x p t) (sb x t p) $;
        \\theorem both_c (g: ctx) (c: obj) {x: obj}: $ g ⊢ pick x (P x) c $ >
        \\  $ g ⊢ both (pick x (P x) c) (P c) ∧ both (pick x (P x) c) (P c) $;
    ,
        \\both_c
        \\------
        \\l1: $ g ⊢ both (pick x (P x) c) (P c) ∧ both (pick x (P x) c) (P c) $ by auto?
    , &counters);
    defer suggestions.deinit();

    try expectOffered(suggestions.items, &.{"and_intro [pick_both [#1], pick_both [#1]]"});
    try std.testing.expectEqualStrings("the search core", generate.phaseName(counters.gen_last_phase));
    try std.testing.expectEqual(@as(usize, 0), counters.core_rejects);
}

test "a binder a rule's conclusion holds only in a substitution is fixed by a premise" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    // Nothing in `P c` fixes `pick_out`'s binders; `#1` fixes all three.
    var suggestions = try sbSearch(&arena,
        \\axiom pick_out (g: ctx) {x: obj} (p: wff x) (t: obj):
        \\  $ g ⊢ pick x p t $ > $ g ⊢ sb x t p $;
        \\theorem out_c (g: ctx) (c: obj) {x: obj}: $ g ⊢ pick x (P x) c $ > $ g ⊢ P c ∧ P c $;
    ,
        \\out_c
        \\-----
        \\l1: $ g ⊢ P c ∧ P c $ by auto?
    , &counters);
    defer suggestions.deinit();

    try expectOffered(suggestions.items, &.{"and_intro [pick_out [#1], pick_out [#1]]"});
    try std.testing.expectEqualStrings("the search core", generate.phaseName(counters.gen_last_phase));
    try std.testing.expectEqual(@as(usize, 0), counters.core_rejects);
}

// Leibniz replacement, whose view reads the context `p` off the two sides.
const replace_rules =
    \\term eq (a b: obj): wff;
    \\--| @congr
    \\axiom im_congr (a b c d: wff): $ a ↔ b $ > $ c ↔ d $ > $ (a → c) ↔ (b → d) $;
    \\--| @view (g h: ctx) {z: obj} (a b: obj) (p: wff z) (q r: wff): $ g ⊢ eq a b $ > $ h ⊢ q $ > $ g , h ⊢ r $
    \\--| @abstract p q r z a b
    \\--| @fresh z
    \\axiom eq_replace (g h: ctx) {z: obj} (a b: obj) (p: wff z):
    \\  $ g ⊢ eq a b $ > $ h ⊢ sb z a p $ > $ g , h ⊢ sb z b p $;
    \\--| @view {z: obj} (a b: obj) (p: wff z) (q r: wff): $ eq a b → (q → r) $
    \\--| @abstract p q r z a b
    \\--| @fresh z
    \\axiom eq_replace_imp {z: obj} (a b: obj) (p: wff z): $ eq a b → (sb z a p → sb z b p) $;
    \\
;

test "the search core replaces equals by an abstraction its premises fix" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    // The hypotheses close `g ⊢ eq ?a ?b` and `g ⊢ ?q`; the walk over `P c`
    // and `P d` then reads `p` off as `P z`, `z` a fresh variable.
    var suggestions = try sbSearch(&arena, replace_rules ++
        \\theorem repl (g: ctx) (c d: obj): $ g ⊢ eq c d $ > $ g ⊢ P c $ > $ g ⊢ P d ∧ P d $;
    ,
        \\repl
        \\----
        \\l1: $ g ⊢ P d ∧ P d $ by auto?
    , &counters);
    defer suggestions.deinit();

    try expectOffered(suggestions.items, &.{"and_intro [eq_replace [#1, #2], eq_replace [#1, #2]]"});
    try std.testing.expectEqualStrings("the search core", generate.phaseName(counters.gen_last_phase));
    try std.testing.expectEqual(@as(usize, 0), counters.core_rejects);
}

test "an abstraction with no premises reads its target off the goal" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    var suggestions = try sbSearch(&arena, replace_rules ++
        \\theorem repl_imp (c d: obj): $ eq c d → (P c → P d) $;
    ,
        \\repl_imp
        \\--------
        \\l1: $ eq c d → (P c → P d) $ by auto?
    , &counters);
    defer suggestions.deinit();

    try expectOffered(suggestions.items, &.{"eq_replace_imp"});
    try std.testing.expectEqualStrings("the search core", generate.phaseName(counters.gen_last_phase));
    try std.testing.expectEqual(@as(usize, 0), counters.core_rejects);
}

fn bridgeSearch(
    arena: *std.heap.ArenaAllocator,
    comptime theorem: []const u8,
    comptime proof: []const u8,
    counters: *types.SearchCounters,
) !types.SourceSuggestions {
    return suggestionsAtNeedle(arena, nd_rules ++ theorem, proof, "auto?", .{
        .counters = counters,
        .generate = .{ .enabled = true, .ladder = false },
    });
}

test "a bridge carries a fact into a larger context" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    var suggestions = try bridgeSearch(&arena,
        \\--| @auto bridge
        \\axiom weak (g h: ctx) (a: wff): $ g ⊢ a $ > $ g , h ⊢ a $;
        \\theorem lift (g: ctx) (a b c: wff): $ g ⊢ a $ > $ g ⊢ b $ > $ g , c ⊢ a ∧ b $;
    ,
        \\lift
        \\----
        \\l1: $ g , c ⊢ a ∧ b $ by auto?
    , &counters);
    defer suggestions.deinit();

    try expectOffered(suggestions.items, &.{"and_intro [weak [#1], weak [#2]]"});
    try std.testing.expectEqualStrings("the search core", generate.phaseName(counters.gen_last_phase));
    try std.testing.expectEqual(@as(usize, 0), counters.core_rejects);
}

test "a bridge's premise is never proved by a rule" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    // `wk1 [top_intro]` proves it, but only a fact may close a bridge's
    // premise.
    var suggestions = try bridgeSearch(&arena,
        \\--| @auto bridge
        \\axiom wk1 (g: ctx) (a b: wff): $ g ⊢ a $ > $ g , b ⊢ a $;
        \\term top: wff;
        \\axiom top_intro: $ ∅ ⊢ top $;
        \\theorem top_any (c: wff): $ ∅ , c ⊢ top $;
    ,
        \\top_any
        \\-------
        \\l1: $ ∅ , c ⊢ top $ by auto?
    , &counters);
    defer suggestions.deinit();

    try std.testing.expectEqual(@as(usize, 0), suggestions.items.len);
    try std.testing.expect(counters.core_nodes > 0);
}

test "two eigenvariables unify as one fresh variable" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    // `pick_side`'s `x` is a fresh variable; so is the dummy of `#1`'s
    // `always`, which the premise `pick x p c` meets unfolded.
    var suggestions = try sbSearch(&arena,
        \\term Q: wff;
        \\def always (a: wff) (t: obj) {.y: obj}: wff = $ pick y a t $;
        \\axiom pick_side (g: ctx) {x: obj} (p: wff x) (t: obj):
        \\  $ g ⊢ pick x p t $ > $ g ⊢ both (P t) (sb x t p) $;
        \\theorem side_q (g: ctx) (c: obj): $ g ⊢ always Q c $ > $ g ⊢ both (P c) Q ∧ both (P c) Q $;
    ,
        \\side_q
        \\------
        \\l1: $ g ⊢ both (P c) Q ∧ both (P c) Q $ by auto?
    , &counters);
    defer suggestions.deinit();

    try std.testing.expect(suggestions.items.len > 0);
    try std.testing.expectEqualStrings("the search core", generate.phaseName(counters.gen_last_phase));
    try std.testing.expectEqual(@as(usize, 0), counters.core_rejects);
}

test "an eigenvariable a rule's bound binder stands for is named clear of its other arguments" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    // `pick_beta`'s context `P x` may not hold its `x`, so the dummy of
    // `pick_P` that `x` takes is named `y`, not the pool's first variable.
    var suggestions = try sbSearch(&arena,
        \\def pick_P (t: obj) {.y: obj}: wff = $ pick y (P y) t $;
        \\axiom pick_beta (g: ctx) {x: obj} (p: wff x) (t: obj):
        \\  $ g ⊢ sb x t p $ > $ g ⊢ pick x p t $;
        \\theorem beta_c (c: obj) {x: obj}: $ P x ⊢ P c $ > $ P x ⊢ pick_P c ∧ pick_P c $;
    ,
        \\beta_c
        \\------
        \\l1: $ P x ⊢ pick_P c ∧ pick_P c $ by auto?
    , &counters);
    defer suggestions.deinit();

    try std.testing.expect(suggestions.items.len > 0);
    try std.testing.expectEqualStrings("the search core", generate.phaseName(counters.gen_last_phase));
    try std.testing.expectEqual(@as(usize, 0), counters.core_rejects);
}

test "a rule's bound binder never takes a variable its other arguments hold" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    // Only `pick_intro` concludes `pick x (P x) c`, and its context `P x`
    // holds the `x` it would bind; the checker would reject the step `#1`
    // closes.
    var suggestions = try sbSearch(&arena,
        \\axiom pick_intro (g: ctx) {x: obj} (p: wff x) (t: obj): $ g ⊢ p $ > $ g ⊢ pick x p t $;
        \\theorem intro_x (c: obj) {x: obj}:
        \\  $ P x ⊢ P x $ > $ P x ⊢ pick x (P x) c ∧ pick x (P x) c $;
    ,
        \\intro_x
        \\-------
        \\l1: $ P x ⊢ pick x (P x) c ∧ pick x (P x) c $ by auto?
    , &counters);
    defer suggestions.deinit();

    try std.testing.expectEqual(@as(usize, 0), suggestions.items.len);
    try std.testing.expect(counters.core_nodes > 0);
    try std.testing.expectEqual(@as(usize, 0), counters.core_rejects);
}

test "an open witness takes the structure a rule's conclusion fixes around it" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    // `ex_intro` leaves `R C ?t`; `R_f`'s `a` is `C`, so its `f a` gives
    // `?t` the value `f C`.
    var suggestions = try ndFolSearch(
        &arena,
        "term f (a: obj): obj;\naxiom R_f (g: ctx) (a: obj): $ g ⊢ R a (f a) $;\n" ++
            "theorem ex_f {y: obj}: $ ∅ ⊢ ∃ y R C y $;\n",
        "ex_f",
        "∅ ⊢ ∃ y R C y",
        &counters,
        .{ .ladder = false },
    );
    defer suggestions.deinit();

    try expectOffered(suggestions.items, &.{"ex_intro [R_f (a := $ C $) []]"});
    try std.testing.expectEqualStrings("the search core", generate.phaseName(counters.gen_last_phase));
    try std.testing.expectEqual(@as(usize, 0), counters.core_rejects);
}

test "an open witness never takes structure with a binder nothing fixes" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    // `R_f`'s `a` would be whatever `?t`'s argument is: nothing in the goal
    // says, so the core does not guess one.
    var suggestions = try ndFolSearch(
        &arena,
        "term f (a: obj): obj;\naxiom R_f (g: ctx) (a: obj): $ g ⊢ R C (f a) $;\n" ++
            "theorem ex_f {y: obj}: $ ∅ ⊢ ∃ y R C y $;\n",
        "ex_f",
        "∅ ⊢ ∃ y R C y",
        &counters,
        .{ .ladder = false },
    );
    defer suggestions.deinit();

    try std.testing.expectEqual(@as(usize, 0), suggestions.items.len);
    try std.testing.expect(counters.core_nodes > 0);
    try std.testing.expectEqual(@as(usize, 0), counters.core_rejects);
}

test "a rule's bound binder never takes a variable a theorem variable in its other arguments depends on" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    // `pick_intro`'s context is `q`, which depends on the `x` it would bind:
    // the checker would reject the step as it would for `P x` itself.
    var suggestions = try sbSearch(&arena,
        \\axiom pick_intro (g: ctx) {x: obj} (p: wff x) (t: obj): $ g ⊢ p $ > $ g ⊢ pick x p t $;
        \\theorem intro_q (c: obj) {x: obj} (q: wff x):
        \\  $ q ⊢ P x $ > $ q ⊢ pick x (P x) c ∧ pick x (P x) c $;
    ,
        \\intro_q
        \\-------
        \\l1: $ q ⊢ pick x (P x) c ∧ pick x (P x) c $ by auto?
    , &counters);
    defer suggestions.deinit();

    try std.testing.expectEqual(@as(usize, 0), suggestions.items.len);
    try std.testing.expect(counters.core_nodes > 0);
    try std.testing.expectEqual(@as(usize, 0), counters.core_rejects);
}

test "an eigenvariable a rule's bound binder holds never merges with one in the rule's other arguments" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    // `F` unfolds to `all p (P p)` with a fresh `p`. Under `inst`, which
    // introduces `x` with `eqv x top` in the context, `gen` binds `p` with
    // that context, and closing `P p` from `eqv x top` would make `p` the
    // same variable as `x`. The core bars `p` from `gen`'s context, so it
    // never builds the proof the checker would reject. (`gen` first, `inst`
    // fails on its own: `dom p` is in the context `x` must stay out of.)
    var suggestions = try suggestionsAtNeedle(&arena, nd_rules ++
        \\--| @vars u v w
        \\sort obj;
        \\term P (a: obj): wff;
        \\term ok (a: obj): wff;
        \\term dom (a: obj): wff;
        \\term all {x: obj} (a: wff x): wff;
        \\term eqv (a b: obj): wff;
        \\term top: obj;
        \\def F {.p: obj}: wff = $ all p (P p) $;
        \\axiom ok_top (g: ctx): $ g ⊢ ok top $;
        \\axiom P_top (g: ctx): $ g ⊢ P top $;
        \\axiom gen (g: ctx) {x: obj} (a: wff x): $ g , dom x ⊢ a $ > $ g ⊢ all x a $;
        \\axiom inst (g: ctx) {x: obj} (t: obj x) (a: wff x):
        \\  $ g ⊢ ok t $ > $ g , eqv x t ⊢ a $ > $ g ⊢ a $;
        \\axiom eqv_P (g: ctx) (a b: obj): $ g ⊢ eqv a b $ > $ g ⊢ P b $ > $ g ⊢ P a $;
        \\theorem not_F: $ ∅ ⊢ F $;
    ,
        \\not_F
        \\-----
        \\l1: $ ∅ ⊢ F $ by auto?
    , "auto?", .{
        .counters = &counters,
        .generate = .{ .enabled = true, .ladder = false },
    });
    defer suggestions.deinit();

    try std.testing.expectEqual(@as(usize, 0), suggestions.items.len);
    try std.testing.expect(counters.core_nodes > 0);
    try std.testing.expectEqual(@as(usize, 0), counters.core_rejects);
}

// `s_r` has no cuts of its own, so on `trans`'s premise `R x ?b` it passes
// the cut on to `S x ?b`, which the hypothesis closes with `?b = y`. No
// fact is an `R` for the cut to come from directly.
test "a rule passes a goal's open cut to a premise a fact closes" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    var suggestions = try search(&arena,
        \\sort obj;
        \\term S (a b: obj): wff;
        \\term R (a b: obj): wff;
        \\axiom trans (a b c: obj): $ R a b $ > $ R b c $ > $ R a c $;
        \\axiom s_r (a b: obj): $ S a b $ > $ R a b $;
        \\theorem s_chain (x y z: obj): $ S x y $ > $ S y z $ > $ R x z $;
    ,
        \\s_chain
        \\-------
        \\l1: $ R x z $ by auto?
    , &counters, true);
    defer suggestions.deinit();

    try expectOffered(suggestions.items, &.{"trans [s_r [#1], s_r [#2]]"});
    try std.testing.expectEqualStrings("the search core", generate.phaseName(counters.gen_last_phase));
    try std.testing.expectEqual(@as(usize, 0), counters.core_rejects);
}

// On `and_l`'s premise `p ∧ ?b`, `and_i` would pass the cut on to its
// premise `?b`, which every hypothesis closes; the core does not take it
// (17 goals if it did).
test "a rule never passes an open cut to a premise that is the bare cut" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    var suggestions = try search(&arena,
        \\axiom and_i (a b: wff): $ a $ > $ b $ > $ a ∧ b $;
        \\axiom and_l (a b: wff): $ a ∧ b $ > $ a $;
        \\theorem no_p (p q r s t u v: wff): $ q $ > $ r $ > $ s $ > $ t $ > $ u $ > $ v $ > $ p $;
    ,
        \\no_p
        \\----
        \\l1: $ p $ by auto?
    , &counters, true);
    defer suggestions.deinit();

    try std.testing.expect(counters.core_nodes <= 12);
}

// `syl`'s premise `?m → (a → c)` meets `a2i`'s conclusion
// `(x → y) → (x → z)`: `?m` takes `a → ?y`, with `?y` a cut of its own
// that `a2i`'s premise `a → ?y → c` fixes from the hypothesis.
test "a narrowing gives a binder nothing fixes a cut a premise's fact fixes" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    var suggestions = try search(&arena,
        \\axiom syl (a b c: wff): $ b → c $ > $ a → b $ > $ a → c $;
        \\axiom a2i (x y z: wff): $ x → y → z $ > $ (x → y) → (x → z) $;
        \\axiom ax_1 (a b: wff): $ a → b → a $;
        \\theorem com12 (a b c: wff): $ a → b → c $ > $ b → a → c $;
    ,
        \\com12
        \\-----
        \\l1: $ b → a → c $ by auto?
    , &counters, true);
    defer suggestions.deinit();

    try expectOffered(suggestions.items, &.{"syl [a2i [#1], ax_1 []]"});
    try std.testing.expectEqualStrings("the search core", generate.phaseName(counters.gen_last_phase));
    try std.testing.expectEqual(@as(usize, 0), counters.core_rejects);
}

// `tdef` narrows `eqmpr`'s cut to `all2 x (Q x p)` with its bound `x`
// fixed by nothing: any fresh variable will do, so it is a bound name, and
// `gen` then binds it.
test "a narrowing gives a bound binder nothing fixes a fresh name" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    var suggestions = try search(&arena,
        \\--| @vars x y
        \\sort obj;
        \\term all2 {x: obj} (p: wff x): wff;
        \\term Q (x: obj) (p: wff): wff;
        \\term D (p: wff): wff;
        \\axiom eqmpr (p q: wff): $ q ↔ p $ > $ p $ > $ q $;
        \\axiom tdef (p: wff) {x: obj}: $ D p ↔ all2 x (Q x p) $;
        \\axiom gen {x: obj} (p: wff x): $ p $ > $ all2 x p $;
        \\axiom qax (x: obj) (p: wff): $ Q x p $;
        \\theorem d_p (p: wff): $ D p $;
    ,
        \\d_p
        \\---
        \\l1: $ D p $ by auto?
    , &counters, true);
    defer suggestions.deinit();

    try expectOffered(suggestions.items, &.{"eqmpr [tdef (x := $ x $) [], gen [qax []]]"});
    try std.testing.expectEqualStrings("the search core", generate.phaseName(counters.gen_last_phase));
    try std.testing.expectEqual(@as(usize, 0), counters.core_rejects);
}

// `both`'s premises each unfold `#1`'s `E`, whose dummy the first binds to
// `a`; the second needs it to be `b`, so `E` unfolds again with a fresh
// dummy.
test "each use of a definition picks its own dummies" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    var suggestions = try search(&arena,
        \\--| @vars x y
        \\sort obj;
        \\term all2 {x: obj} (p: wff x): wff;
        \\term R (x y: obj): wff;
        \\term K (x y: obj): wff;
        \\def E (.x: obj): wff = $ all2 x (R x x) $;
        \\axiom both {x y: obj} (p: wff x) (q: wff y): $ all2 x p $ > $ all2 y q $ > $ K x y $;
        \\theorem k_ab {a b: obj}: $ E $ > $ K a b $;
    ,
        \\k_ab
        \\----
        \\l1: $ K a b $ by auto?
    , &counters, true);
    defer suggestions.deinit();

    try expectOffered(suggestions.items, &.{"both [#1, #1]"});
    try std.testing.expectEqualStrings("the search core", generate.phaseName(counters.gen_last_phase));
    try std.testing.expectEqual(@as(usize, 0), counters.core_rejects);
}

// `eqmp`'s bare premise `p` goes first and guesses `eq a b` from the fact,
// which `iff (eq a b) (eq b a)` then refutes; the sibling no fact closes
// goes first in its stead, and `cong` fixes `p` as `eq a a`.
test "a premise no fact closes goes first when the fact guess for its sibling fails" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    var suggestions = try search(&arena,
        \\sort obj;
        \\term eq (a b: obj): wff;
        \\term iff (p q: wff): wff;
        \\axiom eqmp (p q: wff): $ iff p q $ > $ p $ > $ q $;
        \\axiom cong (a b c: obj): $ eq a b $ > $ iff (eq a c) (eq b c) $;
        \\axiom refl (a: obj): $ eq a a $;
        \\theorem sym (a b: obj): $ eq a b $ > $ eq b a $;
    ,
        \\sym
        \\---
        \\l1: $ eq b a $ by auto?
    , &counters, true);
    defer suggestions.deinit();

    try expectOffered(suggestions.items, &.{"eqmp [cong [#1], refl []]"});
    try std.testing.expectEqualStrings("the search core", generate.phaseName(counters.gen_last_phase));
    try std.testing.expectEqual(@as(usize, 0), counters.core_rejects);
}

// `rall`'s context `∀ x P x` holds the `x` it binds, but only bound, and
// `rall` declares `@freshen g x`: the checker renames it.
test "a bound binder's variable an argument holds bound is renamed by its @freshen" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    var suggestions = try ndFolSearch(
        &arena,
        "theorem all_dup {x: obj}: $ ∀ x P x ⊢ ∀ x (P x ∧ P x) $;\n",
        "all_dup",
        "∀ x P x ⊢ ∀ x (P x ∧ P x)",
        &counters,
        .{ .ladder = false, .fixture = "additive_fol" },
    );
    defer suggestions.deinit();

    try std.testing.expect(suggestions.items.len != 0);
    try std.testing.expectEqualStrings("the search core", generate.phaseName(counters.gen_last_phase));
    try std.testing.expectEqual(@as(usize, 0), counters.core_rejects);
}
