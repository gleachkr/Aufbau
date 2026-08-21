const helpers = @import("./helpers.zig");
const std = helpers.std;
const types = helpers.types;
const conversionSuggestions = helpers.conversionSuggestions;
const expectConversionCompiles = helpers.expectConversionCompiles;

const alpha_prelude =
    \\delimiter $ ( ) $;
    \\provable sort wff;
    \\sort nat;
    \\term iff (p q: wff): wff;
    \\term all {x: nat} (p: wff x): wff;
    \\term sb {x: nat} (a: nat) (p: wff x): wff;
    \\term F (a: nat): wff;
    \\term R (a b: nat): wff;
    \\--| @relation wff iff iff_refl iff_trans iff_symm mpbi
    \\axiom iff_refl (a: wff): $ iff a a $;
    \\axiom iff_trans (a b c: wff) (h1: $ iff a b $) (h2: $ iff b c $): $ iff a c $;
    \\axiom iff_symm (a b: wff) (h: $ iff a b $): $ iff b a $;
    \\axiom mpbi (a b: wff) (h1: $ iff a b $) (h2: $ a $): $ b $;
    \\--| @congr
    \\axiom all_congr {x: nat} (p q: wff x) (h: $ iff p q $): $ iff (all x p) (all x q) $;
    \\--| @conversion ltr
    \\axiom sb_f_var {x: nat} (a: nat): $ iff (sb x a (F x)) (F a) $;
    \\--| @conversion alpha
    \\axiom all_alpha {x y: nat} (p: wff x): $ iff (all x p) (all y (sb x y p)) $;
    \\
;

test "conversion? alpha proves a bound-variable renaming equation goal" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const mm0_src = alpha_prelude ++
        \\theorem alpha_eq {x y: nat}: $ iff (all x (F x)) (all y (F y)) $;
    ;
    const proof_src =
        \\alpha_eq
        \\----
        \\goal: $ iff (all x (F x)) (all y (F y)) $ by conversion?
        \\
    ;

    var found = try conversionSuggestions(&arena, mm0_src, proof_src, .{});
    defer found.deinit();
    try std.testing.expectEqual(types.SearchStatus.found, found.status);
    // The chain cites the alpha lemma and reduces its substitution image
    // through the enrolled sb rule.
    const replacement = found.items[0].replacement;
    try std.testing.expect(std.mem.indexOf(u8, replacement, "all_alpha") != null);
    try std.testing.expect(std.mem.indexOf(u8, replacement, "sb_f_var") != null);

    try expectConversionCompiles(&arena, mm0_src, proof_src, found.items[0]);
}

test "conversion? alpha transports a goal from a renamed hypothesis" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const mm0_src = alpha_prelude ++
        \\theorem alpha_use {x y: nat} (h: $ all x (F x) $): $ all y (F y) $;
    ;
    const proof_src =
        \\alpha_use
        \\----
        \\goal: $ all y (F y) $ by conversion?
        \\
    ;

    var found = try conversionSuggestions(&arena, mm0_src, proof_src, .{});
    defer found.deinit();
    try std.testing.expectEqual(types.SearchStatus.found, found.status);
    const replacement = found.items[0].replacement;
    try std.testing.expect(std.mem.indexOf(u8, replacement, "all_alpha") != null);
    try std.testing.expect(std.mem.indexOf(u8, replacement, "mpbi") != null);

    try expectConversionCompiles(&arena, mm0_src, proof_src, found.items[0]);
}

test "conversion? alpha renames a binder the body never mentions" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    // Binder-free body: both instances hold the SAME body class q, so the
    // comparator takes the equal-class branch (correspond iff the class
    // avoids the renamed atom) rather than walking any structure. The
    // fired image `sb x y q` then discharges through sb_const alone.
    const mm0_src = alpha_prelude ++
        \\--| @conversion ltr
        \\axiom sb_const {x: nat} (a: nat) (q: wff): $ iff (sb x a q) q $;
        \\theorem alpha_vac {x y: nat} (q: wff) (h: $ all x q $): $ all y q $;
    ;
    const proof_src =
        \\alpha_vac
        \\----
        \\goal: $ all y q $ by conversion?
        \\
    ;

    var found = try conversionSuggestions(&arena, mm0_src, proof_src, .{});
    defer found.deinit();
    try std.testing.expectEqual(types.SearchStatus.found, found.status);
    const replacement = found.items[0].replacement;
    try std.testing.expect(std.mem.indexOf(u8, replacement, "all_alpha") != null);
    try std.testing.expect(std.mem.indexOf(u8, replacement, "sb_const") != null);

    try expectConversionCompiles(&arena, mm0_src, proof_src, found.items[0]);
}

test "conversion? alpha refuses a capturing rename" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    // Renaming x -> c in (R x c) captures the free c, and the reverse
    // rename c -> x yields a different body (R x x). The goal must MISS,
    // and because the alpha filter resolved every comparison exactly
    // (no cyclic classes, bags, or budget trips), the saturated outcome
    // IS a forced negative: merely enrolling alpha rules must not
    // degrade the honest miss to budget_exhausted.
    const capture_mm0 = alpha_prelude ++
        \\theorem alpha_cap {x c: nat}: $ iff (all x (R x c)) (all c (R c c)) $;
    ;
    const proof_src =
        \\alpha_cap
        \\----
        \\goal: $ iff (all x (R x c)) (all c (R c c)) $ by conversion?
        \\
    ;

    var miss = try conversionSuggestions(&arena, capture_mm0, proof_src, .{});
    defer miss.deinit();
    try std.testing.expect(miss.status != types.SearchStatus.found);
    try std.testing.expectEqual(types.SearchStatus.miss, miss.status);
}

test "conversion? alpha approximate filter degrades a saturated miss to budget_exhausted" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    // The pool equations make p and q CYCLIC classes (p ~ an p p). The
    // alpha pair (all x (an (F x) p), all y (an (F y) q)) then walks
    // renamedEq(p, q) into itself, and the cycle-conservative in-progress
    // memo read resolves the comparison approximately. The goal still
    // misses (p and q never correspond), but this saturated miss is NOT a
    // forced negative — the other half of the precise-honesty gate: with
    // alpha_filter_skips != 0 the status must be budget_exhausted, never
    // a bare miss.
    const mm0_src = alpha_prelude ++
        \\term an (p q: wff): wff;
        \\theorem alpha_cyc {x y: nat} (p q: wff)
        \\  (h1: $ iff p (an p p) $) (h2: $ iff q (an q q) $):
        \\  $ iff (all x (an (F x) p)) (all y (an (F y) q)) $;
    ;
    const proof_src =
        \\alpha_cyc
        \\----
        \\goal: $ iff (all x (an (F x) p)) (all y (an (F y) q)) $ by conversion?
        \\
    ;

    var miss = try conversionSuggestions(&arena, mm0_src, proof_src, .{});
    defer miss.deinit();
    try std.testing.expect(miss.status != types.SearchStatus.found);
    try std.testing.expectEqual(
        types.SearchStatus.budget_exhausted,
        miss.status,
    );
}

test "conversion? alpha pairs a partner minted mid-saturation" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    // Neither seeded side contains the alpha pair: `all x (F x)` only
    // comes to exist when the passage law fires on the seeded lhs, and
    // the scheduler must then pair it with the rhs's `all y (F y)` on a
    // later iteration.
    const mm0_src = alpha_prelude ++
        \\term or (p q: wff): wff;
        \\--| @congr
        \\axiom or_congr (a b c d: wff) (h1: $ iff a b $) (h2: $ iff c d $):
        \\  $ iff (or a c) (or b d) $;
        \\--| @conversion ltr
        \\axiom pass_al_or {x: nat} (p: wff x) (q: wff):
        \\  $ iff (all x (or p q)) (or (all x p) q) $;
        \\theorem alpha_mid {x y: nat} (q: wff):
        \\  $ iff (all x (or (F x) q)) (or (all y (F y)) q) $;
    ;
    const proof_src =
        \\alpha_mid
        \\----
        \\goal: $ iff (all x (or (F x) q)) (or (all y (F y)) q) $ by conversion?
        \\
    ;

    var found = try conversionSuggestions(&arena, mm0_src, proof_src, .{});
    defer found.deinit();
    try std.testing.expectEqual(types.SearchStatus.found, found.status);
    const replacement = found.items[0].replacement;
    try std.testing.expect(std.mem.indexOf(u8, replacement, "pass_al_or") != null);
    try std.testing.expect(std.mem.indexOf(u8, replacement, "all_alpha") != null);

    try expectConversionCompiles(&arena, mm0_src, proof_src, found.items[0]);
}

// A theory where the winning chain must rewrite INSIDE a substitution
// image: pass_ex_an gives the quantified class an `an`-shaped second
// member, and the extracted route reaches the goal by swapping the sb
// argument's representative — a step that only lowers through a @congr
// rule for sb (which in turn needs a relation on the variable sort).
const alpha_sb_interior_prelude = alpha_prelude ++
    \\term ex {x: nat} (p: wff x): wff;
    \\term an (p q: wff): wff;
    \\term G (a: nat): wff;
    \\--| @congr
    \\axiom ex_congr {x: nat} (p q: wff x) (h: $ iff p q $): $ iff (ex x p) (ex x q) $;
    \\--| @congr
    \\axiom an_congr (a b c d: wff) (h1: $ iff a b $) (h2: $ iff c d $): $ iff (an a c) (an b d) $;
    \\--| @conversion ltr
    \\axiom sb_g_var {x: nat} (a: nat): $ iff (sb x a (G x)) (G a) $;
    \\--| @conversion ltr
    \\axiom sb_an {x: nat} (a: nat) (p q: wff x): $ iff (sb x a (an p q)) (an (sb x a p) (sb x a q)) $;
    \\--| @conversion ltr
    \\axiom sb_const {x: nat} (a: nat) (q: wff): $ iff (sb x a q) q $;
    \\--| @conversion ltr
    \\axiom sb_ex {x y: nat} (a: nat) (p: wff x y):
    \\  $ iff (sb x a (ex y p)) (ex y (sb x a p)) $;
    \\--| @conversion both
    \\axiom pass_ex_an {x: nat} (a: wff) (b: wff x):
    \\  $ iff (ex x (an a b)) (an a (ex x b)) $;
    \\
;

const alpha_sb_congr_rules =
    \\term nat_eq (a b: nat): wff;
    \\--| @relation nat nat_eq neq_refl neq_trans neq_sym _
    \\axiom neq_refl (a: nat): $ nat_eq a a $;
    \\axiom neq_trans (a b c: nat) (h1: $ nat_eq a b $) (h2: $ nat_eq b c $): $ nat_eq a c $;
    \\axiom neq_sym (a b: nat) (h: $ nat_eq a b $): $ nat_eq b a $;
    \\--| @congr
    \\axiom sb_congr {x: nat} (y z: nat) (a b: wff x)
    \\  (hy: $ nat_eq y z $) (h: $ iff a b $): $ iff (sb x y a) (sb x z b) $;
    \\
;

const alpha_sb_interior_theorem =
    \\theorem sb_int {x y u: nat} (h: $ all x (ex y (an (F x) (G y))) $):
    \\  $ all u (ex y (an (F u) (G y))) $;
;

const alpha_sb_interior_proof =
    \\sb_int
    \\----
    \\goal: $ all u (ex y (an (F u) (G y))) $ by conversion?
    \\
;

test "conversion? alpha rewrites inside a substitution image via sb's @congr" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const mm0_src = alpha_sb_interior_prelude ++ alpha_sb_congr_rules ++
        alpha_sb_interior_theorem;

    var found = try conversionSuggestions(
        &arena,
        mm0_src,
        alpha_sb_interior_proof,
        .{},
    );
    defer found.deinit();
    try std.testing.expectEqual(types.SearchStatus.found, found.status);
    const replacement = found.items[0].replacement;
    try std.testing.expect(std.mem.indexOf(u8, replacement, "all_alpha") != null);

    try expectConversionCompiles(
        &arena,
        mm0_src,
        alpha_sb_interior_proof,
        found.items[0],
    );
}

test "conversion? names the congruence-less head blocking extraction" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    // Identical theory, no sb_congr: the classes still merge, but no
    // chain the extractor picks can be lifted through sb — the failure
    // report must name the missing @congr head instead of the generic
    // could-not-extract text.
    const mm0_src = alpha_sb_interior_prelude ++ alpha_sb_interior_theorem;

    var miss = try conversionSuggestions(
        &arena,
        mm0_src,
        alpha_sb_interior_proof,
        .{ .status_detail = true },
    );
    defer miss.deinit();
    try std.testing.expect(miss.status != types.SearchStatus.found);
    const detail = miss.status_detail orelse return error.MissingStatusDetail;
    try std.testing.expect(
        std.mem.indexOf(u8, detail, "'sb'") != null,
    );
    try std.testing.expect(
        std.mem.indexOf(u8, detail, "@congr") != null,
    );
}

// sb rules over R for the nested-rename tests: reduce a substitution
// image at either argument position.
const alpha_sb_r_rules =
    \\--| @conversion ltr
    \\axiom sb_r1 {x: nat} (a b: nat): $ iff (sb x a (R x b)) (R a b) $;
    \\--| @conversion ltr
    \\axiom sb_r2 {x: nat} (a b: nat): $ iff (sb x a (R b x)) (R b a) $;
    \\
;

// Binder commutation: pushes a substitution image through an inner
// `all`. The theory prerequisite for nested renames — without it the
// image stalls at the inner binder and the pair soundly fails to merge.
const alpha_sb_all_rule =
    \\--| @conversion ltr
    \\axiom sb_all {x y: nat} (a: nat) (p: wff x y):
    \\  $ iff (sb x a (all y p)) (all y (sb x a p)) $;
    \\
;

test "conversion? alpha renames nested binders through substitution commutation" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    // Both binders differ and the body references both, so no single
    // rename closes the goal. The nested comparator accepts the pair;
    // only the OUTER lemma instance fires, sb_all pushes the image
    // through the inner binder, and a later pass closes the
    // materialized inner pair — outside-in, one literal lemma instance
    // per level.
    const mm0_src = alpha_prelude ++ alpha_sb_r_rules ++ alpha_sb_all_rule ++
        \\theorem alpha_nest {x y z w: nat}:
        \\  $ iff (all x (all y (R x y))) (all z (all w (R z w))) $;
    ;
    const proof_src =
        \\alpha_nest
        \\----
        \\goal: $ iff (all x (all y (R x y))) (all z (all w (R z w))) $ by conversion?
        \\
    ;

    var found = try conversionSuggestions(&arena, mm0_src, proof_src, .{});
    defer found.deinit();
    try std.testing.expectEqual(types.SearchStatus.found, found.status);
    const replacement = found.items[0].replacement;
    try std.testing.expect(std.mem.indexOf(u8, replacement, "all_alpha") != null);
    try std.testing.expect(std.mem.indexOf(u8, replacement, "sb_all") != null);

    try expectConversionCompiles(&arena, mm0_src, proof_src, found.items[0]);
}

test "conversion? alpha nested rename misses honestly without commutation" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    // Identical goal, but sb_all is not enrolled: the outer image
    // cannot cross the inner binder, so saturation stalls the fired
    // instance and the goal misses. The comparator itself resolved
    // every comparison exactly, so this is a plain miss — the
    // documented sound-but-incomplete failure mode of a missing
    // commutation rule, not a budget artifact.
    const mm0_src = alpha_prelude ++ alpha_sb_r_rules ++
        \\theorem alpha_nest {x y z w: nat}:
        \\  $ iff (all x (all y (R x y))) (all z (all w (R z w))) $;
    ;
    const proof_src =
        \\alpha_nest
        \\----
        \\goal: $ iff (all x (all y (R x y))) (all z (all w (R z w))) $ by conversion?
        \\
    ;

    var miss = try conversionSuggestions(&arena, mm0_src, proof_src, .{});
    defer miss.deinit();
    try std.testing.expect(miss.status != types.SearchStatus.found);
    try std.testing.expectEqual(types.SearchStatus.miss, miss.status);
}
