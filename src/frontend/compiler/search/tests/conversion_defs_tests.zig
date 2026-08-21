const helpers = @import("./helpers.zig");
const std = helpers.std;
const types = helpers.types;
const conversionSuggestions = helpers.conversionSuggestions;
const expectConversionCompiles = helpers.expectConversionCompiles;
const conversion_ac_prelude = helpers.conversion_ac_prelude;
const bool_conversion_prelude = helpers.bool_conversion_prelude;

const ring_conversion_prelude =
    \\delimiter $ ( ) $;
    \\sort R;
    \\provable sort wff;
    \\term iff (p q: wff): wff;
    \\term eq (x y: R): wff;
    \\term zero: R;
    \\term one: R;
    \\term add (x y: R): R;
    \\term mul (x y: R): R;
    \\term neg (x: R): R;
    \\term sub (x y: R): R;
    \\--| @relation wff iff iff_refl iff_trans iff_symm mpbi
    \\axiom iff_refl (a: wff): $ iff a a $;
    \\axiom iff_trans (a b c: wff) (h1: $ iff a b $) (h2: $ iff b c $): $ iff a c $;
    \\axiom iff_symm (a b: wff) (h: $ iff a b $): $ iff b a $;
    \\axiom mpbi (a b: wff) (h1: $ iff a b $) (h2: $ a $): $ b $;
    \\--| @relation R eq eq_refl eq_trans eq_symm _
    \\axiom eq_refl (x: R): $ eq x x $;
    \\axiom eq_trans (x y z: R) (h1: $ eq x y $) (h2: $ eq y z $): $ eq x z $;
    \\axiom eq_symm (x y: R) (h: $ eq x y $): $ eq y x $;
    \\--| @congr
    \\axiom eq_congr (a b c d: R) (h1: $ eq a b $) (h2: $ eq c d $): $ iff (eq a c) (eq b d) $;
    \\--| @congr
    \\axiom add_congr (a b c d: R) (h1: $ eq a b $) (h2: $ eq c d $): $ eq (add a c) (add b d) $;
    \\--| @congr
    \\axiom mul_congr (a b c d: R) (h1: $ eq a b $) (h2: $ eq c d $): $ eq (mul a c) (mul b d) $;
    \\--| @congr
    \\axiom neg_congr (a b: R) (h: $ eq a b $): $ eq (neg a) (neg b) $;
    \\--| @congr
    \\axiom sub_congr (a b c d: R) (h1: $ eq a b $) (h2: $ eq c d $): $ eq (sub a c) (sub b d) $;
    \\--| @conversion ltr
    \\axiom add_zero (x: R): $ eq (add x zero) x $;
    \\--| @conversion ltr
    \\axiom zero_add (x: R): $ eq (add zero x) x $;
    \\--| @conversion comm
    \\axiom add_comm (x y: R): $ eq (add x y) (add y x) $;
    \\--| @conversion assoc
    \\axiom add_assoc (x y z: R): $ eq (add (add x y) z) (add x (add y z)) $;
    \\--| @conversion ltr
    \\axiom add_neg (x: R): $ eq (add x (neg x)) zero $;
    \\--| @conversion ltr
    \\axiom neg_neg (x: R): $ eq (neg (neg x)) x $;
    \\--| @conversion ltr
    \\axiom mul_one (x: R): $ eq (mul x one) x $;
    \\--| @conversion ltr
    \\axiom one_mul (x: R): $ eq (mul one x) x $;
    \\--| @conversion ltr
    \\axiom mul_zero (x: R): $ eq (mul x zero) zero $;
    \\--| @conversion ltr
    \\axiom zero_mul (x: R): $ eq (mul zero x) zero $;
    \\--| @conversion comm
    \\axiom mul_comm (x y: R): $ eq (mul x y) (mul y x) $;
    \\--| @conversion assoc
    \\axiom mul_assoc (x y z: R): $ eq (mul (mul x y) z) (mul x (mul y z)) $;
    \\--| @conversion both
    \\axiom factor_l (x y z: R): $ eq (add (mul x y) (mul x z)) (mul x (add y z)) $;
    \\--| @conversion both
    \\axiom factor_r (x y z: R): $ eq (add (mul x z) (mul y z)) (mul (add x y) z) $;
    \\--| @conversion ltr
    \\axiom neg_mul_l (x y: R): $ eq (mul (neg x) y) (neg (mul x y)) $;
    \\--| @conversion ltr
    \\axiom neg_mul_r (x y: R): $ eq (mul x (neg y)) (neg (mul x y)) $;
    \\--| @conversion ltr
    \\axiom sub_def (x y: R): $ eq (sub x y) (add x (neg y)) $;
    \\
;

test "conversion? forced negative on the boolean lattice" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    // x∧y and x∨y are never lattice-convertible; the full boolean rule set
    // must still saturate (AC permutations of the seeds are finite) and
    // report a forced negative.
    const mm0_src = bool_conversion_prelude ++
        \\theorem conv_bool_none (x y w: bool) (h: $ eq (and x y) w $):
        \\  $ eq (or x y) w $;
    ;
    const proof_src =
        \\conv_bool_none
        \\----
        \\goal: $ eq (or x y) w $ by conversion?
        \\
    ;

    var miss = try conversionSuggestions(&arena, mm0_src, proof_src, .{
        .status_detail = true,
    });
    defer miss.deinit();
    try std.testing.expectEqual(types.SearchStatus.miss, miss.status);
    const detail = miss.status_detail orelse return error.MissingStatusDetail;
    try std.testing.expect(
        std.mem.indexOf(u8, detail, "the egraph saturated") != null,
    );
    try std.testing.expect(
        std.mem.indexOf(u8, detail, "no chain of the enrolled") != null,
    );
}

test "conversion? proves ring sub_self through the definitional unfold" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const mm0_src = ring_conversion_prelude ++
        \\theorem conv_sub_self (x w: R) (h: $ eq zero w $):
        \\  $ eq (sub x x) w $;
    ;
    const proof_src =
        \\conv_sub_self
        \\----
        \\goal: $ eq (sub x x) w $ by conversion?
        \\
    ;

    var found = try conversionSuggestions(&arena, mm0_src, proof_src, .{});
    defer found.deinit();
    try std.testing.expectEqual(types.SearchStatus.found, found.status);
    const replacement = found.items[0].replacement;
    try std.testing.expect(std.mem.indexOf(u8, replacement, "sub_def") != null);
    try std.testing.expect(std.mem.indexOf(u8, replacement, "add_neg") != null);

    try expectConversionCompiles(&arena, mm0_src, proof_src, found.items[0]);
}

test "conversion? pushes negation through a product under neg_congr" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    // (−x)·(−y) → ¬(x·(−y)) → ¬(¬(x·y)) → x·y: the middle step rewrites
    // underneath neg, exercising the unary congruence lift.
    const mm0_src = ring_conversion_prelude ++
        \\theorem conv_neg_mul_neg (x y w: R) (h: $ eq (mul x y) w $):
        \\  $ eq (mul (neg x) (neg y)) w $;
    ;
    const proof_src =
        \\conv_neg_mul_neg
        \\----
        \\goal: $ eq (mul (neg x) (neg y)) w $ by conversion?
        \\
    ;

    var found = try conversionSuggestions(&arena, mm0_src, proof_src, .{});
    defer found.deinit();
    try std.testing.expectEqual(types.SearchStatus.found, found.status);
    const replacement = found.items[0].replacement;
    // Either neg_mul orientation may anchor the route; both share the
    // prefix, and the double negation must collapse under the unary lift.
    try std.testing.expect(std.mem.indexOf(u8, replacement, "neg_mul") != null);
    try std.testing.expect(std.mem.indexOf(u8, replacement, "neg_neg") != null);
    try std.testing.expect(std.mem.indexOf(u8, replacement, "neg_congr") != null);

    try expectConversionCompiles(&arena, mm0_src, proof_src, found.items[0]);
}

test "conversion? proves difference of squares across distributivity and AC" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    // The deep stress: (a+b)(a−b) expands through both-direction
    // distributivity, commutes ba into ab, cancels via add_neg after AC
    // regrouping, and refolds into sub — many rounds, dense egraph.
    const mm0_src = ring_conversion_prelude ++
        \\theorem conv_diff_squares (a b w: R)
        \\  (h: $ eq (mul (add a b) (sub a b)) w $):
        \\  $ eq (sub (mul a a) (mul b b)) w $;
    ;
    const proof_src =
        \\conv_diff_squares
        \\----
        \\goal: $ eq (sub (mul a a) (mul b b)) w $ by conversion?
        \\
    ;

    var found = try conversionSuggestions(&arena, mm0_src, proof_src, .{});
    defer found.deinit();
    try std.testing.expectEqual(types.SearchStatus.found, found.status);
    const replacement = found.items[0].replacement;
    try std.testing.expect(std.mem.indexOf(u8, replacement, "mpbi") != null);
    try std.testing.expect(std.mem.indexOf(u8, replacement, "#1") != null);

    try expectConversionCompiles(&arena, mm0_src, proof_src, found.items[0]);
}

// --- conversion? def-wrangling (@conversion unfold/fold/both) -------------
//
// Enrolled defs saturate as ordinary rules built from the def's own
// equation rel(definiens, head args). Each def step lowers as a single
// refl line the checker closes through transparent unfolding. A hidden
// dummy is a pattern binder BOUND to an existing variable at match time;
// its freshness against every arg instantiation rides the dep-gate
// restrictions, which is load-bearing for suggestion validity (the
// verifier rejects a captured witness with DepViolation).

const conversion_def_prelude =
    \\delimiter $ ( ) $;
    \\sort var;
    \\provable sort form;
    \\term an (p q: form): form;
    \\term or (p q: form): form;
    \\term iff (p q: form): form;
    \\term eqv (a b: var): form;
    \\term ex {x: var} (p: form x): form;
    \\--| @relation form iff iff_refl iff_trans iff_symm mpbi
    \\axiom iff_refl (a: form): $ iff a a $;
    \\axiom iff_trans (a b c: form) (h1: $ iff a b $) (h2: $ iff b c $): $ iff a c $;
    \\axiom iff_symm (a b: form) (h: $ iff a b $): $ iff b a $;
    \\axiom mpbi (a b: form) (h1: $ iff a b $) (h2: $ a $): $ b $;
    \\--| @congr
    \\axiom an_congr (a b c d: form) (h1: $ iff a b $) (h2: $ iff c d $): $ iff (an a c) (an b d) $;
    \\--| @congr
    \\axiom or_congr (a b c d: form) (h1: $ iff a b $) (h2: $ iff c d $): $ iff (or a c) (or b d) $;
    \\
;

test "conversion? folds a dummy-free def" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const mm0_src = conversion_def_prelude ++
        \\--| @conversion fold
        \\def dup (a: form): form = $ an a a $;
        \\theorem conv_fold (p q: form) (h: $ or (an p p) q $): $ or (dup p) q $;
    ;
    const proof_src =
        \\conv_fold
        \\----
        \\goal: $ or (dup p) q $ by conversion?
        \\
    ;

    var found = try conversionSuggestions(&arena, mm0_src, proof_src, .{});
    defer found.deinit();
    try std.testing.expectEqual(types.SearchStatus.found, found.status);
    const replacement = found.items[0].replacement;
    // The def boundary lowers as a refl line, lifted through @congr and
    // transported onto the hypothesis.
    try std.testing.expect(std.mem.indexOf(u8, replacement, "iff_refl") != null);
    try std.testing.expect(std.mem.indexOf(u8, replacement, "or_congr") != null);
    try std.testing.expect(std.mem.indexOf(u8, replacement, "mpbi") != null);

    try expectConversionCompiles(&arena, mm0_src, proof_src, found.items[0]);
}

test "conversion? unfolds a dummy-free def" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const mm0_src = conversion_def_prelude ++
        \\--| @conversion unfold
        \\def dup (a: form): form = $ an a a $;
        \\theorem conv_unfold (p q: form) (h: $ or (dup p) q $): $ or (an p p) q $;
    ;
    const proof_src =
        \\conv_unfold
        \\----
        \\goal: $ or (an p p) q $ by conversion?
        \\
    ;

    var found = try conversionSuggestions(&arena, mm0_src, proof_src, .{});
    defer found.deinit();
    try std.testing.expectEqual(types.SearchStatus.found, found.status);
    try expectConversionCompiles(&arena, mm0_src, proof_src, found.items[0]);
}

test "conversion? both-enrolled def rewrites in both directions at once" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    // One chain needs an unfold (dup p) and a fold (an q q) of the same def.
    const mm0_src = conversion_def_prelude ++
        \\--| @conversion both
        \\def dup (a: form): form = $ an a a $;
        \\theorem conv_both (p q: form) (h: $ or (dup p) (an q q) $): $ or (an p p) (dup q) $;
    ;
    const proof_src =
        \\conv_both
        \\----
        \\goal: $ or (an p p) (dup q) $ by conversion?
        \\
    ;

    var found = try conversionSuggestions(&arena, mm0_src, proof_src, .{});
    defer found.deinit();
    try std.testing.expectEqual(types.SearchStatus.found, found.status);
    try expectConversionCompiles(&arena, mm0_src, proof_src, found.items[0]);
}

test "conversion? folds a hidden-dummy def binding the written witness" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    // someeq's dummy w is a pattern binder matched against the theorem's
    // own bound variable u; the freshness condition u ∉ deps(a) holds.
    const mm0_src = conversion_def_prelude ++
        \\--| @conversion fold
        \\def someeq {.w: var} (v: var): form = $ ex w (eqv w v) $;
        \\theorem conv_hidden {u: var} (a: var) (q: form) (h: $ an (ex u (eqv u a)) q $): $ an (someeq a) q $;
    ;
    const proof_src =
        \\conv_hidden
        \\----
        \\goal: $ an (someeq a) q $ by conversion?
        \\
    ;

    var found = try conversionSuggestions(&arena, mm0_src, proof_src, .{});
    defer found.deinit();
    try std.testing.expectEqual(types.SearchStatus.found, found.status);
    const replacement = found.items[0].replacement;
    try std.testing.expect(std.mem.indexOf(u8, replacement, "iff_refl") != null);

    try expectConversionCompiles(&arena, mm0_src, proof_src, found.items[0]);
}

test "conversion? refuses a captured dummy witness as a deferred miss" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    // ex u (eqv u u) is NOT an unfolding of someeq u: the witness u is the
    // arg itself (capture), which the verifier rejects as a DepViolation.
    // The dep gate must defer the fold match forever — an honest miss, no
    // unsound suggestion.
    const mm0_src = conversion_def_prelude ++
        \\--| @conversion fold
        \\def someeq {.w: var} (v: var): form = $ ex w (eqv w v) $;
        \\theorem conv_capture {u: var} (q: form) (h: $ an (ex u (eqv u u)) q $): $ an (someeq u) q $;
    ;
    const proof_src =
        \\conv_capture
        \\----
        \\goal: $ an (someeq u) q $ by conversion?
        \\
    ;

    var miss = try conversionSuggestions(&arena, mm0_src, proof_src, .{
        .status_detail = true,
    });
    defer miss.deinit();
    try std.testing.expectEqual(types.SearchStatus.miss, miss.status);
    const detail = miss.status_detail orelse return error.MissingStatusDetail;
    try std.testing.expect(
        std.mem.indexOf(u8, detail, "the egraph saturated") != null,
    );
    try std.testing.expect(
        std.mem.indexOf(u8, detail, "variable-dependency") != null,
    );
}

test "conversion? unannotated defs stay dormant" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const mm0_src = conversion_def_prelude ++
        \\def dup (a: form): form = $ an a a $;
        \\theorem conv_dormant (p q: form) (h: $ or (an p p) q $): $ or (dup p) q $;
    ;
    const proof_src =
        \\conv_dormant
        \\----
        \\goal: $ or (dup p) q $ by conversion?
        \\
    ;

    var miss = try conversionSuggestions(&arena, mm0_src, proof_src, .{});
    defer miss.deinit();
    try std.testing.expectEqual(types.SearchStatus.miss, miss.status);
}

test "conversion? folds a bag-shaped definiens on the AC path" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    // dup's definiens flattens to the sub-multiset {p, p} of the 3-member
    // bag {q, p, p}; the leftover q rejoins the folded target as the
    // extension, exercising the bag-step lowering of a def rule.
    const mm0_src = conversion_ac_prelude ++
        \\--| @conversion fold
        \\def dup (a: wff): wff = $ an a a $;
        \\theorem conv_bag_fold (p q: wff) (h: $ an q (an p p) $): $ an (dup p) q $;
    ;
    const proof_src =
        \\conv_bag_fold
        \\----
        \\goal: $ an (dup p) q $ by conversion?
        \\
    ;

    var found = try conversionSuggestions(&arena, mm0_src, proof_src, .{});
    defer found.deinit();
    try std.testing.expectEqual(types.SearchStatus.found, found.status);
    const replacement = found.items[0].replacement;
    try std.testing.expect(std.mem.indexOf(u8, replacement, "iff_refl") != null);

    try expectConversionCompiles(&arena, mm0_src, proof_src, found.items[0]);
}

// --- conversion? alpha ----------------------------------------------------
