const helpers = @import("./helpers.zig");
const std = helpers.std;
const types = helpers.types;
const acui = helpers.acui;
const conversionSuggestions = helpers.conversionSuggestions;
const expectConversionCompiles = helpers.expectConversionCompiles;

const compute_probe_prelude =
    \\delimiter $ ( ) $;
    \\provable sort wff;
    \\sort bv;
    \\term iff (a b: wff): wff;
    \\infixl iff: $<->$ prec 20;
    \\term eq (a b: bv): wff;
    \\infixl eq: $=$ prec 50;
    \\term hZ: bv;
    \\term hx (a d: bv): bv;
    \\infixl hx: $:x$ prec 100;
    \\term add (a b: bv): bv;
    \\infixl add: $+$ prec 64;
    \\term h0: bv;
    \\term h1: bv;
    \\term h2: bv;
    \\term h3: bv;
    \\term h4: bv;
    \\term h7: bv;
    \\--| @relation wff iff iff_refl iff_trans iff_symm mpbi
    \\axiom iff_refl (a: wff): $ a <-> a $;
    \\axiom iff_trans (a b c: wff) (h1: $ a <-> b $) (h2: $ b <-> c $):
    \\  $ a <-> c $;
    \\axiom iff_symm (a b: wff) (h: $ a <-> b $): $ b <-> a $;
    \\axiom mpbi (a b: wff) (h1: $ a <-> b $) (h2: $ a $): $ b $;
    \\--| @relation bv eq eq_refl eq_trans eq_symm _
    \\axiom eq_refl (a: bv): $ a = a $;
    \\axiom eq_trans (a b c: bv) (h1: $ a = b $) (h2: $ b = c $):
    \\  $ a = c $;
    \\axiom eq_symm (a b: bv) (h: $ a = b $): $ b = a $;
    \\--| @congr
    \\axiom eq_congr (a b c d: bv) (h1: $ a = b $) (h2: $ c = d $):
    \\  $ (a = c) <-> (b = d) $;
    \\--| @congr
    \\axiom add_congr (a b c d: bv) (h1: $ a = b $) (h2: $ c = d $):
    \\  $ (a + c) = (b + d) $;
    \\--| @congr
    \\axiom hx_congr (a b c d: bv) (h1: $ a = b $) (h2: $ c = d $):
    \\  $ (a :x c) = (b :x d) $;
    \\--| @conversion assoc
    \\axiom add_assoc (a b c: bv): $ ((a + b) + c) = (a + (b + c)) $;
    \\--| @conversion comm
    \\axiom add_comm (a b: bv): $ (a + b) = (b + a) $;
    \\
;

fn computeProbeRules(
    comptime ann: []const u8,
    comptime with_addd_0_1: bool,
) []const u8 {
    return "--| " ++ ann ++ "\n" ++
        "axiom add_z (a: bv): $ hZ + a = a $;\n" ++
        "--| " ++ ann ++ "\n" ++
        "axiom addd_3_4 (a b: bv):\n" ++
        "  $ (a :x h3) + (b :x h4) = (a + b) :x h7 $;\n" ++
        "--| " ++ ann ++ "\n" ++
        "axiom addc_7_1 (a b: bv):\n" ++
        "  $ (a :x h7) + (b :x h1) = ((a + b) + (hZ :x h1)) :x h0 $;\n" ++
        (if (with_addd_0_1)
            "--| " ++ ann ++ "\n" ++
                "axiom addd_0_1 (a b: bv):\n" ++
                "  $ (a :x h0) + (b :x h1) = (a + b) :x h1 $;\n"
        else
            "") ++
        "--| " ++ ann ++ "\n" ++
        "axiom addd_1_1 (a b: bv):\n" ++
        "  $ (a :x h1) + (b :x h1) = (a + b) :x h2 $;\n" ++
        "--| " ++ ann ++ "\n" ++
        "axiom addc_7_2 (a b: bv):\n" ++
        "  $ (a :x h7) + (b :x h2) = ((a + b) + (hZ :x h1)) :x h1 $;\n";
}

test "@compute folds a chained double carry to a found chain" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const mm0_src = compute_probe_prelude ++
        comptime computeProbeRules("@compute ltr", true) ++
            \\theorem probe_e (v x: bv)
            \\  (h: $ v = x + (hZ :x h7 :x h7) + (hZ :x h1 :x h1) $)
            \\  : $ v = x + (hZ :x h1 :x h1 :x h0) $;
        ;
    const proof_src =
        \\probe_e
        \\----
        \\goal: $ v = x + (hZ :x h1 :x h1 :x h0) $ by conversion?
        \\
    ;
    var found = try conversionSuggestions(&arena, mm0_src, proof_src, .{});
    defer found.deinit();
    try std.testing.expectEqual(types.SearchStatus.found, found.status);
    try expectConversionCompiles(&arena, mm0_src, proof_src, found.items[0]);
}

test "conversion? lowers a unit+digit fold through general saturation" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const mm0_src = compute_probe_prelude ++
        comptime computeProbeRules("@conversion ltr", true) ++
            \\theorem probe_c (v x: bv)
            \\  (h: $ v = x + (hZ :x h3) + (hZ :x h4) $)
            \\  : $ v = x + (hZ :x h7) $;
        ;
    const proof_src =
        \\probe_c
        \\----
        \\goal: $ v = x + (hZ :x h7) $ by conversion?
        \\
    ;
    var found = try conversionSuggestions(&arena, mm0_src, proof_src, .{});
    defer found.deinit();
    try std.testing.expectEqual(types.SearchStatus.found, found.status);
    try expectConversionCompiles(&arena, mm0_src, proof_src, found.items[0]);
}

test "@compute rtl folds and lowers a reversed theorem orientation" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const mm0_src = compute_probe_prelude ++
        \\--| @compute rtl
        \\axiom add_z_rtl (a: bv): $ a = hZ + a $;
        \\theorem probe_rtl (v x: bv) (h: $ v = hZ + x $): $ v = x $;
    ;
    const proof_src =
        \\probe_rtl
        \\---------
        \\goal: $ v = x $ by conversion?
        \\
    ;

    var found = try conversionSuggestions(&arena, mm0_src, proof_src, .{});
    defer found.deinit();
    try std.testing.expectEqual(types.SearchStatus.found, found.status);
    const replacement = found.items[0].replacement;
    try std.testing.expect(
        std.mem.indexOf(u8, replacement, "add_z_rtl") != null,
    );
    try std.testing.expect(
        std.mem.indexOf(u8, replacement, "eq_symm") != null,
    );
    try expectConversionCompiles(&arena, mm0_src, proof_src, found.items[0]);
}

test "@compute folds a single digit addition to a found chain" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const mm0_src = compute_probe_prelude ++
        comptime computeProbeRules("@compute ltr", true) ++
            \\theorem probe_a (v x: bv)
            \\  (h: $ v = x + (hZ :x h3) + (hZ :x h4) $)
            \\  : $ v = x + (hZ :x h7) $;
        ;
    const proof_src =
        \\probe_a
        \\----
        \\goal: $ v = x + (hZ :x h7) $ by conversion?
        \\
    ;
    var found = try conversionSuggestions(&arena, mm0_src, proof_src, .{});
    defer found.deinit();
    try std.testing.expectEqual(types.SearchStatus.found, found.status);
    try expectConversionCompiles(&arena, mm0_src, proof_src, found.items[0]);
}

test "conversion? lowers a carry chain through general saturation" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const mm0_src = compute_probe_prelude ++
        comptime computeProbeRules("@conversion ltr", true) ++
            \\theorem probe_d (v x: bv)
            \\  (h: $ v = x + (hZ :x h7) + (hZ :x h1) $)
            \\  : $ v = x + (hZ :x h1 :x h0) $;
        ;
    const proof_src =
        \\probe_d
        \\----
        \\goal: $ v = x + (hZ :x h1 :x h0) $ by conversion?
        \\
    ;
    var found = try conversionSuggestions(&arena, mm0_src, proof_src, .{});
    defer found.deinit();
    try std.testing.expectEqual(types.SearchStatus.found, found.status);
    try expectConversionCompiles(&arena, mm0_src, proof_src, found.items[0]);
}

test "@compute folds a single carry to a found chain" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const mm0_src = compute_probe_prelude ++
        comptime computeProbeRules("@compute ltr", true) ++
            \\theorem probe_b (v x: bv)
            \\  (h: $ v = x + (hZ :x h7) + (hZ :x h1) $)
            \\  : $ v = x + (hZ :x h1 :x h0) $;
        ;
    const proof_src =
        \\probe_b
        \\----
        \\goal: $ v = x + (hZ :x h1 :x h0) $ by conversion?
        \\
    ;
    var found = try conversionSuggestions(&arena, mm0_src, proof_src, .{});
    defer found.deinit();
    try std.testing.expectEqual(types.SearchStatus.found, found.status);
    try expectConversionCompiles(&arena, mm0_src, proof_src, found.items[0]);
}

test "@compute dead-end fold never claims a forced negative" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    // Same double-carry instance, but the table is missing addd_0_1: the
    // fold's designated redex (addc_7_1 on the top digits, by declaration
    // order) dead-ends, and the consumed-node ledger correctly refuses to
    // re-pair. A chain still exists along the other pairing order, so the
    // resulting fixpoint must NOT be reported as a forced negative — the
    // directed fold is a strategy, not a closure.
    const mm0_src = compute_probe_prelude ++
        comptime computeProbeRules("@compute ltr", false) ++
            \\theorem probe_f (v x: bv)
            \\  (h: $ v = x + (hZ :x h7 :x h7) + (hZ :x h1 :x h1) $)
            \\  : $ v = x + (hZ :x h1 :x h1 :x h0) $;
        ;
    const proof_src =
        \\probe_f
        \\----
        \\goal: $ v = x + (hZ :x h1 :x h1 :x h0) $ by conversion?
        \\
    ;
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
        std.mem.indexOf(u8, detail, "@compute") != null,
    );
    try std.testing.expect(
        std.mem.indexOf(u8, detail, "NOT a forced negative") != null,
    );
}

test "@compute folds the carry cascade to a found chain at defaults" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    // The same digit table that grinds general saturation to a
    // budget-limited fixpoint (see the capped-miss test above), enrolled
    // as `@compute ltr` plus the zero laws: the directed fold
    // scheduler fires one designated redex per class per round, so the
    // all-F + all-1 carry cascade folds in linearly many rounds and the
    // correct 17-digit sum must be FOUND at plain defaults — no widened
    // iters/nodes — with the interference chain still in the pool. The
    // emitted chain must lower and check like any hand-written proof.
    const mm0_src = @embedFile("../fixtures/carry_cascade_compute.mm0");
    const proof_src = @embedFile("../fixtures/carry_cascade_compute.auf");

    var found = try conversionSuggestions(&arena, mm0_src, proof_src, .{});
    defer found.deinit();
    try std.testing.expectEqual(types.SearchStatus.found, found.status);
    // The fixture declares `+` `@acui`, so every rearrangement is the
    // checker's to re-derive: re-treeing seams, assoc/comm splices, and
    // hZ unit clears emit nothing (#205). Elementary lowering emitted
    // ~1670 lines here, chain-quality (#202) ~1074, transport frames
    // (#204) ~604, and ACUI elision lands at ~118 — the digit folds,
    // their lifts, and the joins that span them.
    const replacement = found.items[0].replacement;
    try std.testing.expect(
        std.mem.indexOf(u8, replacement, "by add_comm") == null,
    );
    try std.testing.expect(
        std.mem.indexOf(u8, replacement, "by add_assoc") == null,
    );
    try std.testing.expect(countLines(replacement) <= 160);
    try expectConversionCompiles(&arena, mm0_src, proof_src, found.items[0]);
}

test "@compute carry cascade extracts with the zero laws declared first" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    // Declaration order is the fold's redex priority, and the fixture
    // declares the zero laws last so digit pairs consume before hZ
    // debris clears. The reversed ordering clears debris first, which
    // nests the per-position {hZ, t} ladders the recorded chain must
    // explain through — historically an honest convertible-but-unlowered
    // miss in extraction's binder-residual decomposition (#149), gone
    // since the fold moved to any-match scheduling. Splice the zero-law
    // block ahead of the digit table and hold the reversed ordering to
    // the same acceptance bar: FOUND at plain defaults, chain compiles.
    const mm0_fixture = @embedFile("../fixtures/carry_cascade_compute.mm0");
    const proof_src = @embedFile("../fixtures/carry_cascade_compute.auf");

    const z_marker = "--| @compute ltr\naxiom add_zz";
    const z_start = std.mem.indexOf(u8, mm0_fixture, z_marker).?;
    const z_end_needle = "axiom add_z (a: bv): $ hZ + a = a $;\n";
    const z_end = std.mem.indexOf(u8, mm0_fixture, z_end_needle).? +
        z_end_needle.len;
    const table_marker = "--| @compute ltr\naxiom addd_0_0";
    const table_start = std.mem.indexOf(u8, mm0_fixture, table_marker).?;
    const mm0_src = try std.mem.concat(allocator, u8, &.{
        mm0_fixture[0..table_start],
        mm0_fixture[z_start..z_end],
        mm0_fixture[table_start..z_start],
        mm0_fixture[z_end..],
    });
    // The splice must have MOVED the block, not duplicated it.
    try std.testing.expectEqual(
        std.mem.indexOf(u8, mm0_src, "axiom add_zz"),
        std.mem.lastIndexOf(u8, mm0_src, "axiom add_zz"),
    );
    try std.testing.expect(
        std.mem.indexOf(u8, mm0_src, "axiom add_zz").? <
            std.mem.indexOf(u8, mm0_src, "axiom addd_0_0").?,
    );

    var found = try conversionSuggestions(&arena, mm0_src, proof_src, .{});
    defer found.deinit();
    try std.testing.expectEqual(types.SearchStatus.found, found.status);
    try expectConversionCompiles(&arena, mm0_src, proof_src, found.items[0]);
}

test "conversion? big-steps beta chains through @rewrite absorption" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    // The lambda theory enrolls the substitution rules both `@compute`
    // (they drive the fold) and `@rewrite` (line checking replays them),
    // so the lowering can group each beta with the sb cascade it spawns
    // and state one conclusion in reduced form (the `beta_step` idiom).
    const mm0_src = @embedFile("../fixtures/lambda_two_apply.mm0");
    const proof_src = @embedFile("../fixtures/lambda_two_apply.auf");

    var found = try conversionSuggestions(&arena, mm0_src, proof_src, .{});
    defer found.deinit();
    try std.testing.expectEqual(types.SearchStatus.found, found.status);
    const replacement = found.items[0].replacement;
    // The final beta big-steps clean through its whole cascade: cited
    // with the fully reduced conclusion, no substitution left behind.
    try std.testing.expect(std.mem.indexOf(
        u8,
        replacement,
        "$ (λ w . S w) · S 0 = S S 0 $ by beta",
    ) != null);
    // Elementary lowering emits ~185 lines for this chain; grouping plus
    // route/consolidation/dedup (#202) landed at ~34, the fold's
    // size-decreasing anchor re-fire (#203) at ~20, and transport-frame
    // compression (#204) at ~16 — a pure forward evaluation, no backward
    // step anywhere.
    try std.testing.expect(countLines(replacement) <= 20);
    try expectConversionCompiles(&arena, mm0_src, proof_src, found.items[0]);
}

fn countLines(text: []const u8) usize {
    var count: usize = 0;
    var it = std.mem.splitScalar(u8, text, '\n');
    while (it.next()) |line| {
        if (line.len != 0) count += 1;
    }
    return count;
}

test "conversion? big-steps church addition (one plus one)" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    // The manual's Church-addition evaluation — the worst chain of the
    // demo battery (~2160 lines elementary).
    const mm0_src = @embedFile("../fixtures/lambda_one_plus_one.mm0");
    const proof_src = @embedFile("../fixtures/lambda_one_plus_one.auf");

    var found = try conversionSuggestions(&arena, mm0_src, proof_src, .{});
    defer found.deinit();
    try std.testing.expectEqual(types.SearchStatus.found, found.status);
    const replacement = found.items[0].replacement;
    // Elementary lowering emits ~2160 lines here; grouping landed at
    // ~620, #202 (group consolidation + repeated-line dedup) at ~290,
    // the fold's size-decreasing anchor re-fire (#203) at ~190, and
    // transport-frame compression (#204) at ~103 — steps compose with
    // eq_trans at their deepest shared position and each run lifts
    // through the enclosing congruences once.
    try std.testing.expect(countLines(replacement) <= 140);
    try expectConversionCompiles(&arena, mm0_src, proof_src, found.items[0]);
}

test "conversion? church addition lifts only through dep-valid sb_congr" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    // The manual's sb_congr keeps the substituted term apart from the
    // variable (`a1 a2: tm`). The first beta leaves
    // `[g := [m := λ g. …] f] λ y. g · y`, whose `a` mentions g, so no
    // step may lift through that node. The chain must clean up `f`
    // before the beta, not after.
    const mm0_src = try std.mem.replaceOwned(
        u8,
        arena.allocator(),
        @embedFile("../fixtures/lambda_one_plus_one.mm0"),
        "(a1 a2: tm x)",
        "(a1 a2: tm)",
    );
    // Guard the substitution: the fixture's permissive form never trips.
    try std.testing.expect(std.mem.indexOf(u8, mm0_src, "(a1 a2: tm)") != null);
    // As an equation goal: with the pool reference the chain never
    // meets the frozen node.
    const proof_src =
        \\one_plus_one
        \\------------
        \\l1: $ (λ m. λ n. λ f. λ x. m · f · (n · f · x)) · (λ g. λ y. g · y) · (λ g. λ y. g · y) · (λ w. S w) · 0 = S S 0 $ by conversion?
        \\
    ;

    var found = try conversionSuggestions(&arena, mm0_src, proof_src, .{});
    defer found.deinit();
    try std.testing.expectEqual(types.SearchStatus.found, found.status);
    try std.testing.expect(std.mem.indexOf(
        u8,
        found.items[0].replacement,
        "[ g := [ m :=",
    ) == null);
    try expectConversionCompiles(&arena, mm0_src, proof_src, found.items[0]);
}

test "conversion? cites a stuck substitution the goal itself states" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    // The goal's right side is `beta`'s result with the argument left as
    // `[m := …] f`, a node no step may enter under the restrictive
    // sb_congr. Citing `f` (the liftable preference) can never come back
    // to it, so extraction must retry with the plain rendering.
    const restricted = try std.mem.replaceOwned(
        u8,
        arena.allocator(),
        @embedFile("../fixtures/lambda_one_plus_one.mm0"),
        "(a1 a2: tm x)",
        "(a1 a2: tm)",
    );
    try std.testing.expect(std.mem.indexOf(u8, restricted, "(a1 a2: tm)") != null);
    // The theory alone: this proof file covers only `frozen`.
    const theory_end = std.mem.indexOf(u8, restricted, "theorem one_plus_one").?;
    const mm0_src = try std.mem.concat(arena.allocator(), u8, &.{
        restricted[0..theory_end],
        \\theorem frozen {m f g y: tm}:
        \\  $ (λ g. λ y. g · y) · ([m := λ g. λ y. g · y] f) =
        \\    [g := [m := λ g. λ y. g · y] f] (λ y. g · y) $;
        \\
    });
    const proof_src =
        \\frozen
        \\------
        \\l1: $ (λ g. λ y. g · y) · ([m := λ g. λ y. g · y] f) = [g := [m := λ g. λ y. g · y] f] (λ y. g · y) $ by conversion?
        \\
    ;

    var found = try conversionSuggestions(&arena, mm0_src, proof_src, .{});
    defer found.deinit();
    try std.testing.expectEqual(types.SearchStatus.found, found.status);
    try expectConversionCompiles(&arena, mm0_src, proof_src, found.items[0]);
}

test "conversion? never reorders a sum inside a stuck substitution" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    // `+` made AC, so the egraph identifies `x + a` with `a + x`. Under
    // the restrictive sb_congr, `[x := x + a] e` admits no congruence
    // (its `a1` mentions x), so `[x := x + a] e = [x := a + x] e` has no
    // proof: the AC seam would cite sb_congr on a sum that mentions x.
    // Beside the stuck node the reorder is ordinary.
    const restricted = try std.mem.replaceOwned(
        u8,
        arena.allocator(),
        @embedFile("../fixtures/lambda_one_plus_one.mm0"),
        "(a1 a2: tm x)",
        "(a1 a2: tm)",
    );
    try std.testing.expect(std.mem.indexOf(u8, restricted, "(a1 a2: tm)") != null);
    const theory_end = std.mem.indexOf(u8, restricted, "theorem one_plus_one").?;
    const theory = try std.mem.concat(arena.allocator(), u8, &.{
        restricted[0..theory_end],
        \\--| @conversion assoc
        \\axiom add_assoc (a b c: tm): $ (a + b) + c = a + (b + c) $;
        \\--| @conversion comm
        \\axiom add_comm (a b: tm): $ a + b = b + a $;
        \\
    });

    const inside_mm0 = try std.mem.concat(arena.allocator(), u8, &.{
        theory,
        \\theorem inside {x: tm} (e a: tm x): $ [x := x + a] e = [x := a + x] e $;
        \\
    });
    const inside_proof =
        \\inside
        \\------
        \\l1: $ [x := x + a] e = [x := a + x] e $ by conversion?
        \\
    ;
    var inside = try conversionSuggestions(
        &arena,
        inside_mm0,
        inside_proof,
        .{ .status_detail = true },
    );
    defer inside.deinit();
    try std.testing.expect(inside.status != .found);
    // The miss names the restriction that refused the lift.
    const detail = inside.status_detail orelse return error.MissingStatusDetail;
    try std.testing.expect(std.mem.indexOf(
        u8,
        detail,
        "'sb_congr' cannot lift it: 'a1' may not depend on 'x'",
    ) != null);

    const beside_mm0 = try std.mem.concat(arena.allocator(), u8, &.{
        theory,
        \\theorem beside {x: tm} (e a b: tm x):
        \\  $ [x := x + a] e + (0 + b) = [x := x + a] e + b $;
        \\
    });
    const beside_proof =
        \\beside
        \\------
        \\l1: $ [x := x + a] e + (0 + b) = [x := x + a] e + b $ by conversion?
        \\
    ;
    var beside = try conversionSuggestions(&arena, beside_mm0, beside_proof, .{});
    defer beside.deinit();
    try std.testing.expectEqual(types.SearchStatus.found, beside.status);
    try expectConversionCompiles(&arena, beside_mm0, beside_proof, beside.items[0]);
}

test "conversion? big-steps the Y-combinator fixpoint equation" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    // `Y · g` has no normal form; the chain needs two beta steps, not a
    // limit of reductions, and the fold must stop as soon as the pool
    // converges.
    const mm0_src = @embedFile("../fixtures/lambda_y_fixpoint.mm0");
    const proof_src = @embedFile("../fixtures/lambda_y_fixpoint.auf");

    var found = try conversionSuggestions(&arena, mm0_src, proof_src, .{});
    defer found.deinit();
    try std.testing.expectEqual(types.SearchStatus.found, found.status);
    const replacement = found.items[0].replacement;
    // The first beta big-steps clean through its substitution cascade —
    // the same line the manual's hand-written y_reduce proof opens with.
    try std.testing.expect(std.mem.indexOf(
        u8,
        replacement,
        "$ (λ f . (λ x . f · (x · x)) · (λ x . f · (x · x))) · g = " ++
            "(λ x . g · (x · x)) · (λ x . g · (x · x)) $ by beta",
    ) != null);
    // Two beta stanzas, one symm-and-congr splice, and the equation
    // transport frame — the manual's hand-written y_reduce, mechanized.
    try std.testing.expect(countLines(replacement) <= 16);
    try expectConversionCompiles(&arena, mm0_src, proof_src, found.items[0]);
}

// Binder-bearing `@compute` rules: the fold direction may consume a
// quantifier (never mint one — enrollment's coverage check), and its
// dependency side condition rides the same dep gate as general rules.
// The legal fold below also binds the rule's `a` to a theorem variable:
// `conversion?` matches without ever narrowing, so a theorem variable is
// an inert constant to the fold and `al x p` reduces exactly like a
// constant instance would.
const compute_binder_prelude =
    \\delimiter $ ( ) $;
    \\sort var;
    \\provable sort form;
    \\term iff (p q: form): form;
    \\term al {x: var} (p: form x): form;
    \\term Pr (v: var): form;
    \\--| @relation form iff iff_refl iff_trans iff_symm mpbi
    \\axiom iff_refl (a: form): $ iff a a $;
    \\axiom iff_trans (a b c: form) (h1: $ iff a b $) (h2: $ iff b c $): $ iff a c $;
    \\axiom iff_symm (a b: form) (h: $ iff a b $): $ iff b a $;
    \\axiom mpbi (a b: form) (h1: $ iff a b $) (h2: $ a $): $ b $;
    \\--| @congr
    \\axiom al_congr {x: var} (p q: form x) (h: $ iff p q $): $ iff (al x p) (al x q) $;
    \\--| @compute ltr
    \\axiom al_vac {x: var} (a: form): $ iff (al x a) a $;
    \\
;

test "@compute folds a vacuous quantifier over a theorem variable" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    // x does not occur in p (its dep mask says so), so the dep gate
    // admits the fold and the goal reduces to the hypothesis.
    const mm0_src = compute_binder_prelude ++
        \\theorem comp_vac {x: var} (p: form) (h: $ p $): $ al x p $;
    ;
    const proof_src =
        \\comp_vac
        \\----
        \\goal: $ al x p $ by conversion?
        \\
    ;

    var found = try conversionSuggestions(&arena, mm0_src, proof_src, .{});
    defer found.deinit();
    try std.testing.expectEqual(types.SearchStatus.found, found.status);
    try std.testing.expect(
        std.mem.indexOf(u8, found.items[0].replacement, "al_vac") != null,
    );
    try expectConversionCompiles(&arena, mm0_src, proof_src, found.items[0]);
}

test "@compute dep gate defers an unsound vacuous-quantifier fold" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    // al_vac matches `al x (Pr x)` textually, but `a` must avoid x and
    // the class holds only `Pr x`: the designated redex defers forever
    // (it must NOT consume the node), the fold never fires, and the
    // saturated miss stays honest — with `@compute` enrolled it is
    // never a forced negative.
    const mm0_src = compute_binder_prelude ++
        \\theorem comp_vac_blocked {x: var} (h: $ Pr x $): $ al x (Pr x) $;
    ;
    const proof_src =
        \\comp_vac_blocked
        \\----
        \\goal: $ al x (Pr x) $ by conversion?
        \\
    ;

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
        std.mem.indexOf(u8, detail, "NOT a forced negative") != null,
    );
}

// --- @compute: equational lambda calculus over Nat ------------------------
//
// The acceptance experiment for binder-bearing compute rules: explicit
// substitution as an object-level `sb` operator whose equations enroll as
// `@compute`, plus beta and a Nat fragment (zero/suc/add). MM0 has no
// meta-level lambda or alpha — capture avoidance IS `sb_lam`'s dependency
// side condition (`a` must avoid the inner binder), enforced by the same
// dep gate as `@conversion` rules; a capture-threatened redex defers
// forever rather than firing. `sb_vac` (x not free in e) short-circuits
// vacuous substitutions and doubles as the variable-mismatch case; the
// structural rules only see redexes whose body genuinely mentions x.
const lambda_nat_prelude =
    \\delimiter $ ( ) $;
    \\provable sort wff;
    \\sort var;
    \\sort tm;
    \\term iff (a b: wff): wff;
    \\term eq (a b: tm): wff;
    \\term V (x: var): tm;
    \\term lam {x: var} (e: tm x): tm;
    \\term app (f a: tm): tm;
    \\term sb {x: var} (e: tm x) (a: tm): tm;
    \\term zero: tm;
    \\term suc (n: tm): tm;
    \\term add (m n: tm): tm;
    \\--| @relation wff iff iff_refl iff_trans iff_symm mpbi
    \\axiom iff_refl (a: wff): $ iff a a $;
    \\axiom iff_trans (a b c: wff) (h1: $ iff a b $) (h2: $ iff b c $): $ iff a c $;
    \\axiom iff_symm (a b: wff) (h: $ iff a b $): $ iff b a $;
    \\axiom mpbi (a b: wff) (h1: $ iff a b $) (h2: $ a $): $ b $;
    \\--| @relation tm eq eq_refl eq_trans eq_symm _
    \\axiom eq_refl (a: tm): $ eq a a $;
    \\axiom eq_trans (a b c: tm) (h1: $ eq a b $) (h2: $ eq b c $): $ eq a c $;
    \\axiom eq_symm (a b: tm) (h: $ eq a b $): $ eq b a $;
    \\--| @congr
    \\axiom eq_congr (a b c d: tm) (h1: $ eq a b $) (h2: $ eq c d $): $ iff (eq a c) (eq b d) $;
    \\--| @congr
    \\axiom app_congr (a b c d: tm) (h1: $ eq a b $) (h2: $ eq c d $): $ eq (app a c) (app b d) $;
    \\--| @congr
    \\axiom suc_congr (a b: tm) (h: $ eq a b $): $ eq (suc a) (suc b) $;
    \\--| @congr
    \\axiom add_congr (a b c d: tm) (h1: $ eq a b $) (h2: $ eq c d $): $ eq (add a c) (add b d) $;
    \\--| @congr
    \\axiom lam_congr {x: var} (a b: tm x) (h: $ eq a b $): $ eq (lam x a) (lam x b) $;
    \\--| @congr
    \\axiom sb_congr {x: var} (e1 e2: tm x) (a1 a2: tm) (h1: $ eq e1 e2 $) (h2: $ eq a1 a2 $): $ eq (sb x e1 a1) (sb x e2 a2) $;
    \\--| @compute ltr
    \\axiom beta {x: var} (e: tm x) (a: tm): $ eq (app (lam x e) a) (sb x e a) $;
    \\--| @compute ltr
    \\axiom sb_var {x: var} (a: tm): $ eq (sb x (V x) a) a $;
    \\--| @compute ltr
    \\axiom sb_vac {x: var} (e a: tm): $ eq (sb x e a) e $;
    \\--| @compute ltr
    \\axiom sb_app {x: var} (f g: tm x) (a: tm): $ eq (sb x (app f g) a) (app (sb x f a) (sb x g a)) $;
    \\--| @compute ltr
    \\axiom sb_suc {x: var} (e: tm x) (a: tm): $ eq (sb x (suc e) a) (suc (sb x e a)) $;
    \\--| @compute ltr
    \\axiom sb_add {x: var} (f g: tm x) (a: tm): $ eq (sb x (add f g) a) (add (sb x f a) (sb x g a)) $;
    \\--| @compute ltr
    \\axiom sb_lam {x y: var} (e: tm x y) (a: tm): $ eq (sb x (lam y e) a) (lam y (sb x e a)) $;
    \\--| @compute ltr
    \\axiom add_z (n: tm): $ eq (add zero n) n $;
    \\--| @compute ltr
    \\axiom add_s (m n: tm): $ eq (add (suc m) n) (suc (add m n)) $;
    \\
;

test "@compute evaluates a beta redex through explicit substitution" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    // (lam x. suc x) zero -> sb x (suc (V x)) zero -> suc (sb x (V x)
    // zero) -> suc zero. Exercises beta, a structural sb step, and the
    // variable hit, with congruence lifting the inner steps under suc.
    const mm0_src = lambda_nat_prelude ++
        \\theorem eval_suc {x: var} (c: tm) (h: $ eq c (app (lam x (suc (V x))) zero) $): $ eq c (suc zero) $;
    ;
    const proof_src =
        \\eval_suc
        \\----
        \\goal: $ eq c (suc zero) $ by conversion?
        \\
    ;

    var found = try conversionSuggestions(&arena, mm0_src, proof_src, .{});
    defer found.deinit();
    try std.testing.expectEqual(types.SearchStatus.found, found.status);
    try expectConversionCompiles(&arena, mm0_src, proof_src, found.items[0]);
}

test "@compute evaluates the K combinator over theorem variables" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    // K m n = m: two nested betas. The inner beta substitutes under a
    // lam (sb_lam's capture condition holds — m avoids y), the second
    // beta's redex only EXISTS after the first fold's result merges into
    // the outer function position, and the final step is a vacuous
    // substitution into an opaque theorem variable (sb_vac).
    const mm0_src = lambda_nat_prelude ++
        \\theorem k_comb {x y: var} (m n c: tm) (h: $ eq c (app (app (lam x (lam y (V x))) m) n) $): $ eq c m $;
    ;
    const proof_src =
        \\k_comb
        \\----
        \\goal: $ eq c m $ by conversion?
        \\
    ;

    var found = try conversionSuggestions(&arena, mm0_src, proof_src, .{});
    defer found.deinit();
    try std.testing.expectEqual(types.SearchStatus.found, found.status);
    try expectConversionCompiles(&arena, mm0_src, proof_src, found.items[0]);
}

test "@compute evaluates a two-argument lambda addition" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    // (lam x. lam y. x + y) 1 2 = 3: two betas, substitution threading
    // through `add` on both sides, then the recursive add table.
    const mm0_src = lambda_nat_prelude ++
        \\theorem add_two {x y: var} (c: tm) (h: $ eq c (app (app (lam x (lam y (add (V x) (V y)))) (suc zero)) (suc (suc zero))) $): $ eq c (suc (suc (suc zero))) $;
    ;
    const proof_src =
        \\add_two
        \\----
        \\goal: $ eq c (suc (suc (suc zero))) $ by conversion?
        \\
    ;

    var found = try conversionSuggestions(&arena, mm0_src, proof_src, .{});
    defer found.deinit();
    try std.testing.expectEqual(types.SearchStatus.found, found.status);
    try expectConversionCompiles(&arena, mm0_src, proof_src, found.items[0]);
}

test "@compute never proves a capture-unsound beta reduction" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    // m depends on y (declared, not structural): naive substitution of m
    // under `lam y` would capture, so `eq c (lam y (app m (V y)))` is NOT
    // derivable. sb_lam's side condition must defer forever (m's class
    // has no y-avoiding representative) and sb_vac must defer too (the
    // body mentions x). The engine must never claim found — and with
    // @compute enrolled the saturated miss reports as budget_exhausted,
    // never a forced negative.
    const mm0_src = lambda_nat_prelude ++
        \\theorem capture_blocked {x y: var} (m: tm y) (c: tm) (h: $ eq c (app (lam x (lam y (app (V x) (V y)))) m) $): $ eq c (lam y (app m (V y))) $;
    ;
    const proof_src =
        \\capture_blocked
        \\----
        \\goal: $ eq c (lam y (app m (V y))) $ by conversion?
        \\
    ;

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
        std.mem.indexOf(u8, detail, "NOT a forced negative") != null,
    );
}
