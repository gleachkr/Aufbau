const helpers = @import("./helpers.zig");
const std = helpers.std;
const types = helpers.types;
const seed = helpers.seed;
const exact = helpers.exact;
const tunable_chain_mm0 = helpers.tunable_chain_mm0;
const conversionSuggestions = helpers.conversionSuggestions;
const expectConversionCompiles = helpers.expectConversionCompiles;
const conversion_ac_prelude = helpers.conversion_ac_prelude;
const bool_conversion_prelude = helpers.bool_conversion_prelude;

const conversion_prelude =
    \\delimiter $ ( ) $;
    \\provable sort wff;
    \\term iff (p q: wff): wff;
    \\term an (p q: wff): wff;
    \\term or (p q: wff): wff;
    \\--| @relation wff iff iff_refl iff_trans iff_symm mpbi
    \\axiom iff_refl (a: wff): $ iff a a $;
    \\axiom iff_trans (a b c: wff) (h1: $ iff a b $) (h2: $ iff b c $): $ iff a c $;
    \\axiom iff_symm (a b: wff) (h: $ iff a b $): $ iff b a $;
    \\axiom mpbi (a b: wff) (h1: $ iff a b $) (h2: $ a $): $ b $;
    \\--| @congr
    \\axiom an_congr (a b c d: wff) (h1: $ iff a b $) (h2: $ iff c d $): $ iff (an a c) (an b d) $;
    \\--| @congr
    \\axiom or_congr (a b c d: wff) (h1: $ iff a b $) (h2: $ iff c d $): $ iff (or a c) (or b d) $;
    \\--| @conversion both
    \\axiom an_comm (a b: wff): $ iff (an a b) (an b a) $;
    \\--| @conversion both
    \\axiom or_comm (a b: wff): $ iff (or a b) (or b a) $;
    \\--| @conversion ltr
    \\axiom an_contract (a: wff): $ iff (an a a) a $;
    \\
;

test "conversion? proves a nested commutativity goal from a hypothesis" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const mm0_src = conversion_prelude ++
        \\theorem conv_deep (p q r: wff) (h: $ or (an p q) r $): $ or r (an q p) $;
    ;
    const proof_src =
        \\conv_deep
        \\----
        \\goal: $ or r (an q p) $ by conversion?
        \\
    ;

    var found = try conversionSuggestions(&arena, mm0_src, proof_src, .{});
    defer found.deinit();
    try std.testing.expectEqual(types.SearchStatus.found, found.status);
    try std.testing.expectEqual(@as(usize, 1), found.items.len);

    // The chain lowers through the enrolled rewrites, a congruence lift, a
    // trans join, and the relation transport citing the hypothesis.
    const replacement = found.items[0].replacement;
    try std.testing.expect(std.mem.indexOf(u8, replacement, "an_comm") != null);
    try std.testing.expect(std.mem.indexOf(u8, replacement, "or_congr") != null);
    try std.testing.expect(std.mem.indexOf(u8, replacement, "iff_trans") != null);
    try std.testing.expect(std.mem.indexOf(u8, replacement, "mpbi") != null);
    try std.testing.expect(std.mem.indexOf(u8, replacement, "#1") != null);

    try expectConversionCompiles(&arena, mm0_src, proof_src, found.items[0]);
}

test "conversion? lowers a reversed ltr rule through symm" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    // `an_contract` is enrolled ltr only; proving the expanded form from
    // the contracted hypothesis traverses its union edge backwards.
    const mm0_src = conversion_prelude ++
        \\theorem conv_expand (p: wff) (h: $ p $): $ an p p $;
    ;
    const proof_src =
        \\conv_expand
        \\----
        \\goal: $ an p p $ by conversion?
        \\
    ;

    var found = try conversionSuggestions(&arena, mm0_src, proof_src, .{});
    defer found.deinit();
    try std.testing.expectEqual(types.SearchStatus.found, found.status);
    const replacement = found.items[0].replacement;
    try std.testing.expect(
        std.mem.indexOf(u8, replacement, "an_contract") != null,
    );
    try std.testing.expect(std.mem.indexOf(u8, replacement, "iff_symm") != null);

    try expectConversionCompiles(&arena, mm0_src, proof_src, found.items[0]);
}

test "conversion? saturated miss is reported as a forced negative" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const mm0_src = conversion_prelude ++
        \\theorem conv_none (p q: wff) (h: $ an p q $): $ or p q $;
    ;
    const proof_src =
        \\conv_none
        \\----
        \\goal: $ or p q $ by conversion?
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

    // Opt-in: the same miss without the flag carries no detail.
    var plain = try conversionSuggestions(&arena, mm0_src, proof_src, .{});
    defer plain.deinit();
    try std.testing.expectEqual(types.SearchStatus.miss, plain.status);
    try std.testing.expectEqual(@as(?[]const u8, null), plain.status_detail);
}

test "conversion? proves an equation goal with no references" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    // The goal line itself asserts the relation; both sides join under
    // the enrolled rewrites, so the chain is grounded by refl and no
    // hypothesis or prior line is cited at all.
    const mm0_src = conversion_prelude ++
        \\theorem conv_eq_goal (p q r: wff): $ iff (or p (an q r)) (or (an r q) p) $;
    ;
    const proof_src =
        \\conv_eq_goal
        \\----
        \\goal: $ iff (or p (an q r)) (or (an r q) p) $ by conversion?
        \\
    ;

    var found = try conversionSuggestions(&arena, mm0_src, proof_src, .{});
    defer found.deinit();
    try std.testing.expectEqual(types.SearchStatus.found, found.status);
    try std.testing.expectEqual(@as(usize, 1), found.items.len);
    try std.testing.expectEqualStrings(
        "conversion joining the goal's sides",
        found.items[0].title,
    );

    // The chain rewrites lhs into rhs and the target line restates the
    // goal verbatim as `trans [refl, chain]` — no transport, no citation.
    const replacement = found.items[0].replacement;
    try std.testing.expect(std.mem.indexOf(u8, replacement, "or_comm") != null);
    try std.testing.expect(std.mem.indexOf(u8, replacement, "an_comm") != null);
    try std.testing.expect(std.mem.indexOf(u8, replacement, "iff_refl") != null);
    try std.testing.expect(std.mem.indexOf(
        u8,
        replacement,
        "goal: $ iff (or p (an q r)) (or (an r q) p) $ by iff_trans",
    ) != null);
    try std.testing.expect(std.mem.indexOf(u8, replacement, "mpbi") == null);

    try expectConversionCompiles(&arena, mm0_src, proof_src, found.items[0]);
}

test "conversion? closes a structurally reflexive equation goal" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    // Zero steps: both sides are the same expression, so the target line
    // is restated with a bare refl.
    const mm0_src = conversion_prelude ++
        \\theorem conv_eq_triv (p q: wff): $ iff (an p q) (an p q) $;
    ;
    const proof_src =
        \\conv_eq_triv
        \\----
        \\goal: $ iff (an p q) (an p q) $ by conversion?
        \\
    ;

    var found = try conversionSuggestions(&arena, mm0_src, proof_src, .{});
    defer found.deinit();
    try std.testing.expectEqual(types.SearchStatus.found, found.status);
    const replacement = found.items[0].replacement;
    try std.testing.expect(std.mem.indexOf(
        u8,
        replacement,
        "goal: $ iff (an p q) (an p q) $ by iff_refl",
    ) != null);

    try expectConversionCompiles(&arena, mm0_src, proof_src, found.items[0]);
}

test "conversion? equation goal still prefers a converged pool reference" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    // A hypothesis carrying the goal formula outranks the self-contained
    // equation chain: existing pool-anchored outputs must not change.
    const mm0_src = conversion_prelude ++
        \\theorem conv_eq_pool (p q: wff) (h: $ iff (or p q) (or q p) $): $ iff (or p q) (or q p) $;
    ;
    const proof_src =
        \\conv_eq_pool
        \\----
        \\goal: $ iff (or p q) (or q p) $ by conversion?
        \\
    ;

    var found = try conversionSuggestions(&arena, mm0_src, proof_src, .{});
    defer found.deinit();
    try std.testing.expectEqual(types.SearchStatus.found, found.status);
    try std.testing.expect(std.mem.startsWith(
        u8,
        found.items[0].title,
        "conversion from ",
    ));
    try std.testing.expect(
        std.mem.indexOf(u8, found.items[0].replacement, "#1") != null,
    );

    try expectConversionCompiles(&arena, mm0_src, proof_src, found.items[0]);
}

test "conversion? relation heads can never absorb AC roles" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    // The equation-goal path (and the pool-equation loop) pair a
    // relation node's two children against the written argument order,
    // which an AC bag's sorted member order would break. That is safe
    // because enrollment rejects a role certificate on a registered
    // relation head — and no declaration order evades it: an
    // AC-absorbable head is sort-homogeneous, so its certificate's
    // conclusion relation is the head itself, forcing registration
    // before the certificate can enroll.
    const mm0_src = conversion_prelude ++
        \\--| @congr
        \\axiom iff_congr (a b c d: wff) (h1: $ iff a b $) (h2: $ iff c d $): $ iff (iff a c) (iff b d) $;
        \\--| @conversion comm
        \\axiom iff_comm (a b: wff): $ iff (iff a b) (iff b a) $;
        \\theorem conv_ac_rel (p q: wff): $ iff (an p q) (an q p) $;
    ;
    const proof_src =
        \\conv_ac_rel
        \\----
        \\goal: $ iff (an p q) (an q p) $ by conversion?
        \\
    ;

    try std.testing.expectError(
        error.ConversionRoleRelationHead,
        conversionSuggestions(&arena, mm0_src, proof_src, .{}),
    );
}

test "conversion? equation goal folds a computation without a wff relation" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    // A term-sort equation goal needs only the term relation bundle: no
    // wff @relation, no transport (the bundle's slot is `_`), and no
    // grounding refl line in the proof. The pool path could never close
    // this; the equation path proves the line outright.
    const mm0_src =
        \\delimiter $ ( ) S $;
        \\provable sort wff;
        \\sort tm;
        \\term eq (a b: tm): wff;
        \\infixl eq: $=$ prec 20;
        \\term zero: tm; notation zero: tm = ($0$:max);
        \\term suc (n: tm): tm; prefix suc: $S$ prec 70;
        \\term add (m n: tm): tm; infixl add: $+$ prec 30;
        \\--| @relation tm eq eq_refl eq_trans eq_symm _
        \\axiom eq_refl (a: tm): $ a = a $;
        \\axiom eq_trans (a b c: tm) (h1: $ a = b $) (h2: $ b = c $): $ a = c $;
        \\axiom eq_symm (a b: tm) (h: $ a = b $): $ b = a $;
        \\--| @congr
        \\axiom suc_congr (a b: tm) (h: $ a = b $): $ S a = S b $;
        \\--| @congr
        \\axiom add_congr (a b c d: tm) (h1: $ a = b $) (h2: $ c = d $): $ a + c = b + d $;
        \\--| @compute ltr
        \\axiom add_z (n: tm): $ 0 + n = n $;
        \\--| @compute ltr
        \\axiom add_s (m n: tm): $ S m + n = S (m + n) $;
        \\theorem two_plus_two: $ S S 0 + S S 0 = S S S S 0 $;
    ;
    const proof_src =
        \\two_plus_two
        \\----
        \\goal: $ S S 0 + S S 0 = S S S S 0 $ by conversion?
        \\
    ;

    var found = try conversionSuggestions(&arena, mm0_src, proof_src, .{});
    defer found.deinit();
    try std.testing.expectEqual(types.SearchStatus.found, found.status);
    const replacement = found.items[0].replacement;
    try std.testing.expect(std.mem.indexOf(u8, replacement, "add_s") != null);

    try expectConversionCompiles(&arena, mm0_src, proof_src, found.items[0]);
}

// The nat theory of the previous test with the fold rules also enrolled
// as `@rewrite`, in two variants (task #190). Big-step grouping states a
// rule line with its result side rewrite-normalized, which the checker
// accepts only through formula-level normalized comparison — that needs a
// relation for the formula's sort, a transport, and a `@congr` lifting
// the equation head into it.
test "conversion? equation goal keeps elementary steps when big-steps cannot check" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    // No wff relation here, so no big-step line can ever check; the
    // grouping gate used to fire on hasRewriteRules() alone and the
    // suggestion failed to compile. Now the commit gate replays the
    // checker's test and the lowering keeps the elementary stanzas
    // (the add_z line below is one of them — absorbed if a group forms).
    const mm0_src =
        \\delimiter $ ( ) S $;
        \\provable sort wff;
        \\sort tm;
        \\term eq (a b: tm): wff;
        \\infixl eq: $=$ prec 20;
        \\term zero: tm; notation zero: tm = ($0$:max);
        \\term suc (n: tm): tm; prefix suc: $S$ prec 70;
        \\term add (m n: tm): tm; infixl add: $+$ prec 30;
        \\--| @relation tm eq eq_refl eq_trans eq_symm _
        \\axiom eq_refl (a: tm): $ a = a $;
        \\axiom eq_trans (a b c: tm) (h1: $ a = b $) (h2: $ b = c $): $ a = c $;
        \\axiom eq_symm (a b: tm) (h: $ a = b $): $ b = a $;
        \\--| @congr
        \\axiom suc_congr (a b: tm) (h: $ a = b $): $ S a = S b $;
        \\--| @congr
        \\axiom add_congr (a b c d: tm) (h1: $ a = b $) (h2: $ c = d $): $ a + c = b + d $;
        \\--| @rewrite
        \\--| @compute ltr
        \\axiom add_z (n: tm): $ 0 + n = n $;
        \\--| @rewrite
        \\--| @compute ltr
        \\axiom add_s (m n: tm): $ S m + n = S (m + n) $;
        \\theorem two_plus_two: $ S S 0 + S S 0 = S S S S 0 $;
    ;
    const proof_src =
        \\two_plus_two
        \\----
        \\goal: $ S S 0 + S S 0 = S S S S 0 $ by conversion?
        \\
    ;

    var found = try conversionSuggestions(&arena, mm0_src, proof_src, .{});
    defer found.deinit();
    try std.testing.expectEqual(types.SearchStatus.found, found.status);
    const replacement = found.items[0].replacement;
    try std.testing.expect(std.mem.indexOf(u8, replacement, "add_z") != null);

    try expectConversionCompiles(&arena, mm0_src, proof_src, found.items[0]);
}

test "conversion? equation goal big-steps an @rewrite-enrolled driver" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    // With the full replay machinery present, a driver that is itself
    // `@rewrite`-enrolled is fine: the stated line's left side reduces
    // too, but the checker normalizes both conclusions to the same form.
    // The whole fold collapses into the one add_s line (no add_z line —
    // it is absorbed), grounded by the equation goal's refl/trans coda.
    const mm0_src =
        \\delimiter $ ( ) S $;
        \\provable sort wff;
        \\sort tm;
        \\term iff (p q: wff): wff;
        \\term eq (a b: tm): wff;
        \\infixl eq: $=$ prec 20;
        \\term zero: tm; notation zero: tm = ($0$:max);
        \\term suc (n: tm): tm; prefix suc: $S$ prec 70;
        \\term add (m n: tm): tm; infixl add: $+$ prec 30;
        \\--| @relation wff iff iff_refl iff_trans iff_symm mpbi
        \\axiom iff_refl (a: wff): $ iff a a $;
        \\axiom iff_trans (a b c: wff) (h1: $ iff a b $) (h2: $ iff b c $): $ iff a c $;
        \\axiom iff_symm (a b: wff) (h: $ iff a b $): $ iff b a $;
        \\axiom mpbi (a b: wff) (h1: $ iff a b $) (h2: $ a $): $ b $;
        \\--| @relation tm eq eq_refl eq_trans eq_symm _
        \\axiom eq_refl (a: tm): $ a = a $;
        \\axiom eq_trans (a b c: tm) (h1: $ a = b $) (h2: $ b = c $): $ a = c $;
        \\axiom eq_symm (a b: tm) (h: $ a = b $): $ b = a $;
        \\--| @congr
        \\axiom eq_congr (a b c d: tm) (h1: $ a = b $) (h2: $ c = d $): $ iff (a = c) (b = d) $;
        \\--| @congr
        \\axiom suc_congr (a b: tm) (h: $ a = b $): $ S a = S b $;
        \\--| @congr
        \\axiom add_congr (a b c d: tm) (h1: $ a = b $) (h2: $ c = d $): $ a + c = b + d $;
        \\--| @rewrite
        \\--| @compute ltr
        \\axiom add_z (n: tm): $ 0 + n = n $;
        \\--| @rewrite
        \\--| @compute ltr
        \\axiom add_s (m n: tm): $ S m + n = S (m + n) $;
        \\theorem two_plus_two: $ S S 0 + S S 0 = S S S S 0 $;
    ;
    const proof_src =
        \\two_plus_two
        \\----
        \\goal: $ S S 0 + S S 0 = S S S S 0 $ by conversion?
        \\
    ;

    var found = try conversionSuggestions(&arena, mm0_src, proof_src, .{});
    defer found.deinit();
    try std.testing.expectEqual(types.SearchStatus.found, found.status);
    const replacement = found.items[0].replacement;
    try std.testing.expect(std.mem.indexOf(u8, replacement, "add_s") != null);
    try std.testing.expect(std.mem.indexOf(u8, replacement, "add_z") == null);

    try expectConversionCompiles(&arena, mm0_src, proof_src, found.items[0]);
}

test "conversion? survives a gate normalizer error (missing @congr)" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    // The chain's one step lands on `h (0 + 0)`. The big-step residue
    // probe normalizes that expression, add_z fires inside `h`, and
    // lifting the child rewrite needs a @congr for h that the theory
    // does not declare — error.MissingCongruenceRule. The gate must
    // decline the group and keep the elementary stanza (which states
    // the kr instance exactly, so the checker never normalizes it);
    // this used to propagate and kill the entire search.
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\sort tm;
        \\term eq (a b: tm): wff;
        \\infixl eq: $=$ prec 20;
        \\term zero: tm; notation zero: tm = ($0$:max);
        \\term add (m n: tm): tm; infixl add: $+$ prec 30;
        \\term h (a: tm): tm;
        \\term k: tm;
        \\--| @relation tm eq eq_refl eq_trans eq_symm _
        \\axiom eq_refl (a: tm): $ a = a $;
        \\axiom eq_trans (a b c: tm) (h1: $ a = b $) (h2: $ b = c $): $ a = c $;
        \\axiom eq_symm (a b: tm) (h: $ a = b $): $ b = a $;
        \\--| @congr
        \\axiom add_congr (a b c d: tm) (h1: $ a = b $) (h2: $ c = d $): $ a + c = b + d $;
        \\--| @rewrite
        \\axiom add_z (n: tm): $ 0 + n = n $;
        \\--| @conversion ltr
        \\axiom kr: $ k = h (0 + 0) $;
        \\theorem t: $ k = h (0 + 0) $;
    ;
    const proof_src =
        \\t
        \\----
        \\goal: $ k = h (0 + 0) $ by conversion?
        \\
    ;

    var found = try conversionSuggestions(&arena, mm0_src, proof_src, .{});
    defer found.deinit();
    try std.testing.expectEqual(types.SearchStatus.found, found.status);
    const replacement = found.items[0].replacement;
    try std.testing.expect(std.mem.indexOf(u8, replacement, "by kr") != null);

    try expectConversionCompiles(&arena, mm0_src, proof_src, found.items[0]);
}

test "conversion? equation goal subsumes the grounding refl-line idiom" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    // The church-addition fixture proof grounds its computation with a
    // hand-written `l1: $ S S 0 = S S 0 $ by eq_refl` pool line. With the
    // goal's own sides seeded, the same theorem closes without it.
    const mm0_src = @embedFile("../fixtures/lambda_one_plus_one.mm0");
    const proof_src =
        \\one_plus_one
        \\------------
        \\goal: $ (λ m. λ n. λ f. λ x. m · f · (n · f · x)) · (λ g. λ y. g · y) · (λ g. λ y. g · y) · (λ w. S w) · 0 = S S 0 $ by conversion?
        \\
    ;

    var found = try conversionSuggestions(&arena, mm0_src, proof_src, .{});
    defer found.deinit();
    try std.testing.expectEqual(types.SearchStatus.found, found.status);
    try std.testing.expectEqualStrings(
        "conversion joining the goal's sides",
        found.items[0].title,
    );
    try expectConversionCompiles(&arena, mm0_src, proof_src, found.items[0]);
}

test "conversion? AC: pure reassociation+permutation lowers via certificates" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const mm0_src = conversion_ac_prelude ++
        \\theorem conv_ac (p q r: wff) (h: $ an (an p q) r $): $ an r (an q p) $;
    ;
    const proof_src =
        \\conv_ac
        \\----
        \\goal: $ an r (an q p) $ by conversion?
        \\
    ;

    var found = try conversionSuggestions(&arena, mm0_src, proof_src, .{});
    defer found.deinit();
    try std.testing.expectEqual(types.SearchStatus.found, found.status);
    const replacement = found.items[0].replacement;
    // Zero saturation steps: the whole chain is seam re-treeing citing
    // the certificates.
    try std.testing.expect(std.mem.indexOf(u8, replacement, "an_comm") != null);
    try std.testing.expect(std.mem.indexOf(u8, replacement, "mpbi") != null);
    try expectConversionCompiles(&arena, mm0_src, proof_src, found.items[0]);
}

test "conversion? AC: rule fires on a sub-multiset with extension" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    // an_contract's redex {p, p} is a sub-multiset of the 3-member bag
    // {p, p, q}; the leftover member rejoins the contracted target.
    const mm0_src = conversion_ac_prelude ++
        \\theorem conv_ext (p q: wff) (h: $ an p (an q p) $): $ an q p $;
    ;
    const proof_src =
        \\conv_ext
        \\----
        \\goal: $ an q p $ by conversion?
        \\
    ;

    var found = try conversionSuggestions(&arena, mm0_src, proof_src, .{});
    defer found.deinit();
    try std.testing.expectEqual(types.SearchStatus.found, found.status);
    const replacement = found.items[0].replacement;
    try std.testing.expect(
        std.mem.indexOf(u8, replacement, "an_contract") != null,
    );
    try expectConversionCompiles(&arena, mm0_src, proof_src, found.items[0]);
}

test "conversion? AC: rewrite inside a bag member lifts through the comb" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const mm0_src = conversion_ac_prelude ++
        \\theorem conv_in (p q r: wff) (h: $ or (an p (an q q)) r $): $ or r (an q p) $;
    ;
    const proof_src =
        \\conv_in
        \\----
        \\goal: $ or r (an q p) $ by conversion?
        \\
    ;

    var found = try conversionSuggestions(&arena, mm0_src, proof_src, .{});
    defer found.deinit();
    try std.testing.expectEqual(types.SearchStatus.found, found.status);
    const replacement = found.items[0].replacement;
    try std.testing.expect(
        std.mem.indexOf(u8, replacement, "an_contract") != null,
    );
    try expectConversionCompiles(&arena, mm0_src, proof_src, found.items[0]);
}

test "conversion? AC: local equation over bags cites the written formula" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const mm0_src = conversion_ac_prelude ++
        \\theorem conv_eq (p q s: wff) (h1: $ iff (an p q) s $) (h2: $ an q p $): $ s $;
    ;
    const proof_src =
        \\conv_eq
        \\----
        \\goal: $ s $ by conversion?
        \\
    ;

    var found = try conversionSuggestions(&arena, mm0_src, proof_src, .{});
    defer found.deinit();
    try std.testing.expectEqual(types.SearchStatus.found, found.status);
    try expectConversionCompiles(&arena, mm0_src, proof_src, found.items[0]);
}

test "conversion? AC: seven-atom forced negative saturates at defaults" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    // The tree-representation baseline dies at n = 7: the miss degrades
    // to budget_exhausted before the AC closure completes (see
    // docs/design_notes/ac_representation.md). With bags the closure is
    // definitional and the forced negative survives.
    const mm0_src = conversion_ac_prelude ++
        \\theorem conv_neg (p1 p2 p3 p4 p5 p6 p7: wff)
        \\  (h: $ an p1 (an p2 (an p3 (an p4 (an p5 (an p6 p7))))) $):
        \\  $ or p1 (or p2 (or p3 (or p4 (or p5 (or p6 p7))))) $;
    ;
    const proof_src =
        \\conv_neg
        \\----
        \\goal: $ or p1 (or p2 (or p3 (or p4 (or p5 (or p6 p7))))) $ by conversion?
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
    // The forced negative must be unhedged: a budget-capped or
    // cyclic-dropped run would append a "NOT a forced negative" caveat,
    // which is exactly the regression this fixture guards against.
    try std.testing.expect(
        std.mem.indexOf(u8, detail, "NOT a forced negative") == null,
    );

    // And the positive twin — a reversed seven-atom conjunction — is
    // found and compiles.
    const found_src = conversion_ac_prelude ++
        \\theorem conv_pos (p1 p2 p3 p4 p5 p6 p7: wff)
        \\  (h: $ an p1 (an p2 (an p3 (an p4 (an p5 (an p6 p7))))) $):
        \\  $ an p7 (an p6 (an p5 (an p4 (an p3 (an p2 p1))))) $;
    ;
    const found_proof =
        \\conv_pos
        \\----
        \\goal: $ an p7 (an p6 (an p5 (an p4 (an p3 (an p2 p1))))) $ by conversion?
        \\
    ;
    var found = try conversionSuggestions(&arena, found_src, found_proof, .{});
    defer found.deinit();
    try std.testing.expectEqual(types.SearchStatus.found, found.status);
    try expectConversionCompiles(&arena, found_src, found_proof, found.items[0]);
}

test "conversion? AC: absorbed certificates alone keep the search alive" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    // The ONLY @conversion annotations are the absorbed certificates, so
    // zero rules enroll for saturation and the pool has no rel-shaped
    // equations — yet a pure permutation goal converts by bag interning
    // alone. Regression: the "nothing can ever union" early-out must not
    // fire while absorbed heads exist.
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term iff (p q: wff): wff;
        \\term an (p q: wff): wff;
        \\--| @relation wff iff iff_refl iff_trans iff_symm mpbi
        \\axiom iff_refl (a: wff): $ iff a a $;
        \\axiom iff_trans (a b c: wff) (h1: $ iff a b $) (h2: $ iff b c $): $ iff a c $;
        \\axiom iff_symm (a b: wff) (h: $ iff a b $): $ iff b a $;
        \\axiom mpbi (a b: wff) (h1: $ iff a b $) (h2: $ a $): $ b $;
        \\--| @congr
        \\axiom an_congr (a b c d: wff) (h1: $ iff a b $) (h2: $ iff c d $): $ iff (an a c) (an b d) $;
        \\--| @conversion comm
        \\axiom an_comm (a b: wff): $ iff (an a b) (an b a) $;
        \\--| @conversion assoc
        \\axiom an_assoc (a b c: wff): $ iff (an (an a b) c) (an a (an b c)) $;
        \\theorem conv_pure (p q r: wff) (h: $ an (an p q) r $): $ an r (an q p) $;
    ;
    const proof_src =
        \\conv_pure
        \\----
        \\goal: $ an r (an q p) $ by conversion?
        \\
    ;

    var found = try conversionSuggestions(&arena, mm0_src, proof_src, .{});
    defer found.deinit();
    try std.testing.expectEqual(types.SearchStatus.found, found.status);
    try expectConversionCompiles(&arena, mm0_src, proof_src, found.items[0]);
}

test "conversion? tree path still lowers assoc laws (direction tokens)" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    // Direction-token comm/assoc rules (role == none) stay on the tree
    // representation — the supported configuration for theories that
    // never migrate to role certificates. Pin the assoc lowering there.
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term iff (p q: wff): wff;
        \\term an (p q: wff): wff;
        \\--| @relation wff iff iff_refl iff_trans iff_symm mpbi
        \\axiom iff_refl (a: wff): $ iff a a $;
        \\axiom iff_trans (a b c: wff) (h1: $ iff a b $) (h2: $ iff b c $): $ iff a c $;
        \\axiom iff_symm (a b: wff) (h: $ iff a b $): $ iff b a $;
        \\axiom mpbi (a b: wff) (h1: $ iff a b $) (h2: $ a $): $ b $;
        \\--| @congr
        \\axiom an_congr (a b c d: wff) (h1: $ iff a b $) (h2: $ iff c d $): $ iff (an a c) (an b d) $;
        \\--| @conversion both
        \\axiom an_comm (a b: wff): $ iff (an a b) (an b a) $;
        \\--| @conversion both
        \\axiom an_assoc (a b c: wff): $ iff (an (an a b) c) (an a (an b c)) $;
        \\theorem conv_tree (p q r: wff) (h: $ an (an p q) r $): $ an q (an p r) $;
    ;
    const proof_src =
        \\conv_tree
        \\----
        \\goal: $ an q (an p r) $ by conversion?
        \\
    ;

    var found = try conversionSuggestions(&arena, mm0_src, proof_src, .{});
    defer found.deinit();
    try std.testing.expectEqual(types.SearchStatus.found, found.status);
    const replacement = found.items[0].replacement;
    try std.testing.expect(
        std.mem.indexOf(u8, replacement, "an_assoc") != null or
            std.mem.indexOf(u8, replacement, "an_comm") != null,
    );
    try expectConversionCompiles(&arena, mm0_src, proof_src, found.items[0]);
}

test "conversion? reports missing enrollment and node-cap truncation" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    // A theory with no @conversion rules at all.
    var unenrolled = try conversionSuggestions(&arena, tunable_chain_mm0,
        \\t
        \\----
        \\l1: $ R $ by conversion?
    , .{ .status_detail = true });
    defer unenrolled.deinit();
    try std.testing.expectEqual(types.SearchStatus.miss, unenrolled.status);
    const no_rules = unenrolled.status_detail orelse
        return error.MissingStatusDetail;
    try std.testing.expect(
        std.mem.indexOf(u8, no_rules, "no @conversion rules are enrolled") != null,
    );

    // A starved e-node cap surfaces as truncation with a concrete hint.
    const mm0_src = conversion_prelude ++
        \\theorem conv_deep (p q r: wff) (h: $ or (an p q) r $): $ or r (an q p) $;
    ;
    var capped = try conversionSuggestions(&arena, mm0_src,
        \\conv_deep
        \\----
        \\goal: $ or r (an q p) $ by conversion? (nodes: 1)
        \\
    , .{ .status_detail = true });
    defer capped.deinit();
    try std.testing.expectEqual(
        types.SearchStatus.budget_exhausted,
        capped.status,
    );
    const detail = capped.status_detail orelse return error.MissingStatusDetail;
    try std.testing.expect(
        std.mem.indexOf(u8, detail, "e-node cap (1)") != null,
    );
    try std.testing.expect(
        std.mem.indexOf(u8, detail, "conversion? (nodes: 2)") != null,
    );
}

// A theory with a relation bundle and congruence but ZERO @conversion
// rules: local equations are the only way anything ever unions.
const equation_only_prelude =
    \\delimiter $ ( ) $;
    \\provable sort wff;
    \\term iff (p q: wff): wff;
    \\term an (p q: wff): wff;
    \\--| @relation wff iff iff_refl iff_trans iff_symm mpbi
    \\axiom iff_refl (a: wff): $ iff a a $;
    \\axiom iff_trans (a b c: wff) (h1: $ iff a b $) (h2: $ iff b c $): $ iff a c $;
    \\axiom iff_symm (a b: wff) (h: $ iff a b $): $ iff b a $;
    \\axiom mpbi (a b: wff) (h1: $ iff a b $) (h2: $ a $): $ b $;
    \\--| @congr
    \\axiom an_congr (a b c d: wff) (h1: $ iff a b $) (h2: $ iff c d $): $ iff (an a c) (an b d) $;
    \\
;

test "conversion? converges through a local equation with no rules enrolled" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    // h1 is an ordinary iff hypothesis, not an enrolled rewrite: its sides
    // union at seed time and congruence closure alone connects the goal.
    const mm0_src = equation_only_prelude ++
        \\theorem conv_ground (p q r: wff) (h1: $ iff q p $) (h2: $ an q r $): $ an p r $;
    ;
    const proof_src =
        \\conv_ground
        \\----
        \\goal: $ an p r $ by conversion?
        \\
    ;

    var found = try conversionSuggestions(&arena, mm0_src, proof_src, .{});
    defer found.deinit();
    try std.testing.expectEqual(types.SearchStatus.found, found.status);

    // The forward equation step is the hypothesis cited as-is — no rule
    // line, just the congruence lift and the transport.
    const replacement = found.items[0].replacement;
    try std.testing.expect(std.mem.indexOf(u8, replacement, "#1") != null);
    try std.testing.expect(std.mem.indexOf(u8, replacement, "an_congr") != null);
    try std.testing.expect(std.mem.indexOf(u8, replacement, "mpbi") != null);
    try std.testing.expect(std.mem.indexOf(u8, replacement, "iff_symm") == null);

    try expectConversionCompiles(&arena, mm0_src, proof_src, found.items[0]);
}

test "conversion? joins a local equation with enrolled rewrites" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    // Needs BOTH: the equation q ~ p (no enrolled rule swaps atoms) and
    // an_comm for the argument flip.
    const mm0_src = conversion_prelude ++
        \\theorem conv_mixed (p q r: wff) (h1: $ iff q p $) (h2: $ an q r $): $ an r p $;
    ;
    const proof_src =
        \\conv_mixed
        \\----
        \\goal: $ an r p $ by conversion?
        \\
    ;

    var found = try conversionSuggestions(&arena, mm0_src, proof_src, .{});
    defer found.deinit();
    try std.testing.expectEqual(types.SearchStatus.found, found.status);
    const replacement = found.items[0].replacement;
    try std.testing.expect(std.mem.indexOf(u8, replacement, "#1") != null);
    try std.testing.expect(std.mem.indexOf(u8, replacement, "an_comm") != null);
    try std.testing.expect(std.mem.indexOf(u8, replacement, "iff_trans") != null);

    try expectConversionCompiles(&arena, mm0_src, proof_src, found.items[0]);
}

test "conversion? cites a local equation backwards through symm" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    // h1 proves iff(p, q); the chain rewrites q -> p, traversing the
    // equation's union edge against its stated direction.
    const mm0_src = equation_only_prelude ++
        \\theorem conv_eq_rev (p q r: wff) (h1: $ iff p q $) (h2: $ an q r $): $ an p r $;
    ;
    const proof_src =
        \\conv_eq_rev
        \\----
        \\goal: $ an p r $ by conversion?
        \\
    ;

    var found = try conversionSuggestions(&arena, mm0_src, proof_src, .{});
    defer found.deinit();
    try std.testing.expectEqual(types.SearchStatus.found, found.status);
    const replacement = found.items[0].replacement;
    try std.testing.expect(std.mem.indexOf(u8, replacement, "iff_symm") != null);
    try std.testing.expect(std.mem.indexOf(u8, replacement, "#1") != null);

    try expectConversionCompiles(&arena, mm0_src, proof_src, found.items[0]);
}

test "conversion? tolerates a self-referential local equation" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    // h1 unions p with a compound containing p's own class — a cyclic
    // e-class from the first rebuild. The found case must not pay for it
    // and the miss case must still saturate to a forced negative.
    const found_mm0 = conversion_prelude ++
        \\theorem conv_cyc (p q: wff) (h1: $ iff p (an p p) $) (h2: $ an p q $): $ an q p $;
    ;
    const found_proof =
        \\conv_cyc
        \\----
        \\goal: $ an q p $ by conversion?
        \\
    ;
    var found = try conversionSuggestions(&arena, found_mm0, found_proof, .{});
    defer found.deinit();
    try std.testing.expectEqual(types.SearchStatus.found, found.status);
    try expectConversionCompiles(&arena, found_mm0, found_proof, found.items[0]);

    const miss_mm0 = conversion_prelude ++
        \\theorem conv_cyc_miss (p q: wff) (h1: $ iff p (an p p) $) (h2: $ an p q $): $ or p q $;
    ;
    var miss = try conversionSuggestions(&arena, miss_mm0,
        \\conv_cyc_miss
        \\----
        \\goal: $ or p q $ by conversion?
        \\
    , .{ .status_detail = true });
    defer miss.deinit();
    try std.testing.expectEqual(types.SearchStatus.miss, miss.status);
    const detail = miss.status_detail orelse return error.MissingStatusDetail;
    try std.testing.expect(
        std.mem.indexOf(u8, detail, "the egraph saturated") != null,
    );
    try std.testing.expect(
        std.mem.indexOf(u8, detail, "1 local equations") != null,
    );
}

// --- conversion? dep safety: prenex/CNF rules of passage ------------------
//
// A first-order theory whose interesting rewrites carry variable-dependency
// side conditions (the classical rules of passage: quantifier scope moves
// legal only when the moved formula does not mention the bound variable).
// The egraph's dep gate must admit exactly the matches whose side condition
// some class representative can witness, and extraction must cite that
// representative. Without the gate, `al_vac` alone would "prove"
// `Pr x ⊢ al x (Pr x)`.

const fol_passage_prelude =
    \\delimiter $ ( ) $;
    \\sort var;
    \\provable sort form;
    \\term iff (p q: form): form;
    \\term an (p q: form): form;
    \\term or (p q: form): form;
    \\term imp (p q: form): form;
    \\term not (p: form): form;
    \\term al {x: var} (p: form x): form;
    \\term ex {x: var} (p: form x): form;
    \\term Pr (v: var): form;
    \\--| @relation form iff iff_refl iff_trans iff_symm mpbi
    \\axiom iff_refl (a: form): $ iff a a $;
    \\axiom iff_trans (a b c: form) (h1: $ iff a b $) (h2: $ iff b c $): $ iff a c $;
    \\axiom iff_symm (a b: form) (h: $ iff a b $): $ iff b a $;
    \\axiom mpbi (a b: form) (h1: $ iff a b $) (h2: $ a $): $ b $;
    \\--| @congr
    \\axiom an_congr (a b c d: form) (h1: $ iff a b $) (h2: $ iff c d $): $ iff (an a c) (an b d) $;
    \\--| @congr
    \\axiom or_congr (a b c d: form) (h1: $ iff a b $) (h2: $ iff c d $): $ iff (or a c) (or b d) $;
    \\--| @congr
    \\axiom imp_congr (a b c d: form) (h1: $ iff a b $) (h2: $ iff c d $): $ iff (imp a c) (imp b d) $;
    \\--| @congr
    \\axiom not_congr (a b: form) (h: $ iff a b $): $ iff (not a) (not b) $;
    \\--| @congr
    \\axiom al_congr {x: var} (p q: form x) (h: $ iff p q $): $ iff (al x p) (al x q) $;
    \\--| @congr
    \\axiom ex_congr {x: var} (p q: form x) (h: $ iff p q $): $ iff (ex x p) (ex x q) $;
    \\--| @conversion both
    \\axiom pass_al_or {x: var} (a: form) (b: form x): $ iff (al x (or a b)) (or a (al x b)) $;
    \\--| @conversion ltr
    \\axiom al_vac {x: var} (a: form): $ iff (al x a) a $;
    \\--| @conversion both
    \\axiom not_al {x: var} (b: form x): $ iff (not (al x b)) (ex x (not b)) $;
    \\--| @conversion both
    \\axiom imp_def (a b: form): $ iff (imp a b) (or (not a) b) $;
    \\
;

test "conversion? applies a rule of passage when the side condition holds" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    // x does not occur in p, so pulling p out of the quantifier is legal.
    const mm0_src = fol_passage_prelude ++
        \\theorem pass_out {x: var} (p: form) (h: $ or p (al x (Pr x)) $): $ al x (or p (Pr x)) $;
    ;
    const proof_src =
        \\pass_out
        \\----
        \\goal: $ al x (or p (Pr x)) $ by conversion?
        \\
    ;

    var found = try conversionSuggestions(&arena, mm0_src, proof_src, .{});
    defer found.deinit();
    try std.testing.expectEqual(types.SearchStatus.found, found.status);
    const replacement = found.items[0].replacement;
    try std.testing.expect(
        std.mem.indexOf(u8, replacement, "pass_al_or") != null,
    );
    try std.testing.expect(std.mem.indexOf(u8, replacement, "mpbi") != null);
    try std.testing.expect(std.mem.indexOf(u8, replacement, "#1") != null);

    try expectConversionCompiles(&arena, mm0_src, proof_src, found.items[0]);
}

test "conversion? refuses an unsound generalization as a dep-deferred miss" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    // al_vac matches `al x (Pr x)` textually, but its `a` binder must
    // avoid x and the class holds only `Pr x` — the gate defers forever
    // and the saturated miss names the dependency constraint. Without the
    // gate this "proves" Pr x ⊢ al x (Pr x) and emits a broken splice.
    const mm0_src = fol_passage_prelude ++
        \\theorem vac_blocked {x: var} (h: $ Pr x $): $ al x (Pr x) $;
    ;
    const proof_src =
        \\vac_blocked
        \\----
        \\goal: $ al x (Pr x) $ by conversion?
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

test "conversion? discharges a side condition through a local equation" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    // The pulled-out slot's class is {Pr x, an p q}: the unmasked
    // extraction minimum is the x-containing `Pr x`, so the splice only
    // checks if the restricted binder extracts under its avoid-mask and
    // cites `an p q`. This is the test that fails if the gate admits
    // without constraint-aware extraction.
    const mm0_src = fol_passage_prelude ++
        \\theorem pass_via_eq {x: var} (p q: form) (h1: $ iff (Pr x) (an p q) $) (h2: $ or (Pr x) (al x (Pr x)) $): $ al x (or (Pr x) (Pr x)) $;
    ;
    const proof_src =
        \\pass_via_eq
        \\----
        \\goal: $ al x (or (Pr x) (Pr x)) $ by conversion?
        \\
    ;

    var found = try conversionSuggestions(&arena, mm0_src, proof_src, .{});
    defer found.deinit();
    try std.testing.expectEqual(types.SearchStatus.found, found.status);
    const replacement = found.items[0].replacement;
    try std.testing.expect(
        std.mem.indexOf(u8, replacement, "pass_al_or") != null,
    );

    try expectConversionCompiles(&arena, mm0_src, proof_src, found.items[0]);
}

test "conversion? applies fully-dependent binder rules without deferral" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    // not_al's binder depends on x — no restriction, no gate involvement.
    const mm0_src = fol_passage_prelude ++
        \\theorem prenex_neg {x: var} (h: $ ex x (not (Pr x)) $): $ not (al x (Pr x)) $;
    ;
    const proof_src =
        \\prenex_neg
        \\----
        \\goal: $ not (al x (Pr x)) $ by conversion?
        \\
    ;

    var found = try conversionSuggestions(&arena, mm0_src, proof_src, .{});
    defer found.deinit();
    try std.testing.expectEqual(types.SearchStatus.found, found.status);
    try std.testing.expect(
        std.mem.indexOf(u8, found.items[0].replacement, "not_al") != null,
    );

    try expectConversionCompiles(&arena, mm0_src, proof_src, found.items[0]);
}

test "conversion? rewrites implications into CNF shape" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const mm0_src = fol_passage_prelude ++
        \\theorem cnf_imp (p q: form) (h: $ or (not p) q $): $ imp p q $;
    ;
    const proof_src =
        \\cnf_imp
        \\----
        \\goal: $ imp p q $ by conversion?
        \\
    ;

    var found = try conversionSuggestions(&arena, mm0_src, proof_src, .{});
    defer found.deinit();
    try std.testing.expectEqual(types.SearchStatus.found, found.status);
    try std.testing.expect(
        std.mem.indexOf(u8, found.items[0].replacement, "imp_def") != null,
    );

    try expectConversionCompiles(&arena, mm0_src, proof_src, found.items[0]);
}

// --- conversion? stress: two-sorted equational theories -------------------
//
// Boolean-algebra and commutative-ring axiom sets adapted from
// gleachkr/eggbau (tests/fixtures/domain_boolean_algebra.mm0 and
// domain_ring.mm0). Unlike the wff-only prelude above, every rewrite step
// here happens at a non-provable object sort (`bool`/`R`) under `eq`, so a
// chain must lift through the relation term's own congruence (`eq_congr`)
// into provable `iff` land before the mpbi transport fires. The object
// sort's `@relation` bundle is transport-free (`_`).

test "conversion? lifts a two-sorted chained De Morgan through eq_congr" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const mm0_src = bool_conversion_prelude ++
        \\theorem conv_chained_demorgan (x y z w: bool)
        \\  (h: $ eq (not (or x (and y z))) w $):
        \\  $ eq (and (not x) (or (not y) (not z))) w $;
    ;
    const proof_src =
        \\conv_chained_demorgan
        \\----
        \\goal: $ eq (and (not x) (or (not y) (not z))) w $ by conversion?
        \\
    ;

    var found = try conversionSuggestions(&arena, mm0_src, proof_src, .{});
    defer found.deinit();
    try std.testing.expectEqual(types.SearchStatus.found, found.status);
    const replacement = found.items[0].replacement;
    // Both De Morgan steps happen at sort bool; the inner one additionally
    // lifts through and_congr. The steps compose with eq_trans at the
    // bool level and the composed chain crosses into iff land once, via
    // the relation term's own congruence before the transport.
    try std.testing.expect(std.mem.indexOf(u8, replacement, "demorgan_or") != null);
    try std.testing.expect(std.mem.indexOf(u8, replacement, "demorgan_and") != null);
    try std.testing.expect(std.mem.indexOf(u8, replacement, "and_congr") != null);
    try std.testing.expect(std.mem.indexOf(u8, replacement, "eq_trans") != null);
    try std.testing.expect(std.mem.indexOf(u8, replacement, "eq_congr") != null);
    try std.testing.expect(std.mem.indexOf(u8, replacement, "mpbi") != null);
    try std.testing.expect(std.mem.indexOf(u8, replacement, "#1") != null);

    try expectConversionCompiles(&arena, mm0_src, proof_src, found.items[0]);
}

test "conversion? proves boolean consensus through factor, complement, and unit" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    // or(x∧y, x∧¬y) → x∧(y∨¬y) → x∧⊤ → ⊤∧x → x: the complement and unit
    // collapse only exist as nodes minted by earlier rule instantiations,
    // so the chain needs several saturation rounds.
    const mm0_src = bool_conversion_prelude ++
        \\theorem conv_consensus (x y w: bool) (h: $ eq x w $):
        \\  $ eq (or (and x y) (and x (not y))) w $;
    ;
    const proof_src =
        \\conv_consensus
        \\----
        \\goal: $ eq (or (and x y) (and x (not y))) w $ by conversion?
        \\
    ;

    var found = try conversionSuggestions(&arena, mm0_src, proof_src, .{});
    defer found.deinit();
    try std.testing.expectEqual(types.SearchStatus.found, found.status);
    const replacement = found.items[0].replacement;
    try std.testing.expect(std.mem.indexOf(u8, replacement, "or_factor") != null);
    try std.testing.expect(std.mem.indexOf(u8, replacement, "or_compl") != null);
    try std.testing.expect(std.mem.indexOf(u8, replacement, "and_top") != null);
    try std.testing.expect(std.mem.indexOf(u8, replacement, "mpbi") != null);

    try expectConversionCompiles(&arena, mm0_src, proof_src, found.items[0]);
}

test "conversion? reverses an ltr rule at the object sort through eq_symm" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    // The goal's lhs IS the or_absorb redex, so the ref-to-goal chain
    // traverses that union edge backwards: the symm fires at sort bool
    // (eq_symm), not at the wff level.
    const mm0_src = bool_conversion_prelude ++
        \\theorem conv_absorb_expand (x y w: bool) (h: $ eq x w $):
        \\  $ eq (or x (and x y)) w $;
    ;
    const proof_src =
        \\conv_absorb_expand
        \\----
        \\goal: $ eq (or x (and x y)) w $ by conversion?
        \\
    ;

    var found = try conversionSuggestions(&arena, mm0_src, proof_src, .{});
    defer found.deinit();
    try std.testing.expectEqual(types.SearchStatus.found, found.status);
    const replacement = found.items[0].replacement;
    try std.testing.expect(std.mem.indexOf(u8, replacement, "or_absorb") != null);
    try std.testing.expect(std.mem.indexOf(u8, replacement, "eq_symm") != null);

    try expectConversionCompiles(&arena, mm0_src, proof_src, found.items[0]);
}

test "conversion? extracts through cyclic nested ground-sum classes" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    // Digit-addition rules make derived ground-sum classes self-containing
    // (hZ+hZ=hZ chains 0-padded numerals into classes containing same-head
    // compounds of themselves). Extraction must thread the exact forest
    // vertices to stay well-founded; class-anchored re-rendering used to
    // re-pose parent alignments unboundedly (a misleading miss).
    const mm0_src = @embedFile("../fixtures/cyclic_ground_sums.mm0");
    const proof_src = @embedFile("../fixtures/cyclic_ground_sums.auf");

    var found = try conversionSuggestions(&arena, mm0_src, proof_src, .{});
    defer found.deinit();
    try std.testing.expectEqual(types.SearchStatus.found, found.status);

    try expectConversionCompiles(&arena, mm0_src, proof_src, found.items[0]);
}

test "conversion? extracts chained ground sums under AC certificates" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    // Same cyclic-class family as above, but the assoc/comm laws are
    // enrolled as AC role certificates (bag nodes), and the second ground
    // sum is computed from the first across a comm rearrangement.
    const mm0_src = @embedFile("../fixtures/ac_certificate_ground_sums.mm0");
    const proof_src = @embedFile("../fixtures/ac_certificate_ground_sums.auf");

    var found = try conversionSuggestions(&arena, mm0_src, proof_src, .{});
    defer found.deinit();
    try std.testing.expectEqual(types.SearchStatus.found, found.status);

    try expectConversionCompiles(&arena, mm0_src, proof_src, found.items[0]);
}

test "conversion? survives a goal-irrelevant reconvergent match flood" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    // The goal needs only assoc + one digit rule, but the pool carries an
    // unrelated reconvergent add chain (a symbolic a+b, two +1 links, and
    // a join of two chain levels) whose assoc/comm closure floods one
    // iteration's match collection past the retained-match budget. The
    // driver saturates one iteration per call (goal-converged early
    // exit), so match dedup must persist on the egraph across calls —
    // rebuilt per call, every iteration re-collected the same
    // already-applied no-op effects, tripped the budget, and starved the
    // goal's matches forever: a node-count fixpoint that never saturated
    // and could not be rescued by any `iters:` value.
    const mm0_src = @embedFile("../fixtures/reconvergent_interference_chain.mm0");
    const proof_src = @embedFile("../fixtures/reconvergent_interference_chain.auf");

    var found = try conversionSuggestions(&arena, mm0_src, proof_src, .{});
    defer found.deinit();
    try std.testing.expectEqual(types.SearchStatus.found, found.status);
    try expectConversionCompiles(&arena, mm0_src, proof_src, found.items[0]);
}

test "conversion? bounds a carry-rule splice flood to an honest capped miss" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    // Carry rules mint nested sums whose classes chain 16 deep under
    // bag absorption; splice flattening used to expand every member
    // reference independently (the cycle guard is per-path, blind to
    // sharing), so one rebuild allocated flat forms exponentially
    // longer than the node graph and the process died of OOM at ~650
    // e-nodes. The splice member cap, the per-iteration enumeration
    // step pool, and budget-fixpoint detection must bound the whole
    // widened search (iters: 80, nodes: 100000) to seconds, and the
    // report must say that raising `iters:` cannot help.
    const mm0_src = @embedFile("../fixtures/carry_cascade_interference.mm0");
    const proof_src = @embedFile("../fixtures/carry_cascade_interference.auf");

    var miss = try conversionSuggestions(&arena, mm0_src, proof_src, .{
        .status_detail = true,
    });
    defer miss.deinit();
    try std.testing.expectEqual(
        types.SearchStatus.budget_exhausted,
        miss.status,
    );
    const detail = miss.status_detail orelse return error.MissingStatusDetail;
    try std.testing.expect(
        std.mem.indexOf(u8, detail, "budget-limited fixpoint") != null,
    );
    try std.testing.expect(
        std.mem.indexOf(u8, detail, "NOT a forced negative") != null,
    );
}
