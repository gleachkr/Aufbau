//! Commutative-ring normalization by `conversion?` (task #242): `@acui`
//! on `+` and `*`, `@compute ltr` for the ring identities, and `@congr`
//! plumbing. The theory is `fixtures/commutative_ring.mm0`; each test
//! appends one theorem and drives a single `conversion?` search over it.
//! The cases pin the two egraph fixes the Cardano spike needed: a fold
//! whose target re-interns to the folded node must not consume the redex,
//! and a binder already bound by a structured pattern member must not
//! enumerate every sub-multiset of a long bag.

const helpers = @import("./helpers.zig");
const std = helpers.std;
const types = helpers.types;
const conversionSuggestions = helpers.conversionSuggestions;
const expectConversionCompiles = helpers.expectConversionCompiles;

const theory = @embedFile("../fixtures/commutative_ring.mm0");

/// The ring theory extended with inverses and division (`def div`
/// unfolds, `mul_inv` fires under `a ≠ 0`), for Cardano's formula in
/// radical form. `neg_add` is left out so a test can enroll it its own
/// way: as `@conversion ltr` it costs nothing (6 ms, 150 lines for the
/// theorem below), as a `@compute` fold it distributes every negated
/// sum and builds mutually negated classes the extraction then has to
/// route through (0.55 s, 275 lines).
const radical_theory = @embedFile("../fixtures/radical_ring.mm0");

fn expectFoundAndCompiles(
    comptime statement: []const u8,
    comptime goal: []const u8,
) !void {
    try expectFoundAndCompilesIn(theory, statement, goal);
}

fn expectFoundAndCompilesIn(
    comptime base: []const u8,
    comptime statement: []const u8,
    comptime goal: []const u8,
) !void {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const mm0_src = base ++ statement;
    const proof_src = "thm\n---\ngoal: $ " ++ goal ++ " $ by conversion?\n";
    var found = try conversionSuggestions(&arena, mm0_src, proof_src, .{
        .status_detail = true,
    });
    defer found.deinit();
    if (found.status != .found) {
        std.debug.print("status: {s}\n{s}\n", .{
            @tagName(found.status),
            found.status_detail orelse "",
        });
        return error.ConversionMiss;
    }
    try expectConversionCompiles(&arena, mm0_src, proof_src, found.items[0]);
}

// Binomial cube. After `distrib` fires once on `(u + v) * ((u + v) * (u
// + v))`, the product class also holds the expanded sum, and the next
// `distrib` match with `a` bound to a single factor and the rest as
// extension flattens back to the very node it fired on. Before the
// self-loop outcome that no-op counted as the node's one reduction and
// the fold stalled after two rounds.
test "ring conversion?: binomial cube (fold self-loop is not a reduction)" {
    try expectFoundAndCompiles(
        \\theorem thm (u v: R): $ (u + v) * (u + v) * (u + v)
        \\  = u * u * u + u * u * v + u * u * v + u * u * v
        \\  + u * v * v + u * v * v + u * v * v + v * v * v $;
    ,
        \\(u + v) * (u + v) * (u + v)
        \\  = u * u * u + u * u * v + u * u * v + u * u * v
        \\  + u * v * v + u * v * v + u * v * v + v * v * v
    );
}

// `add_neg` (`a + -a = 0`) on a fourteen-member sum: `-a` binds `a` to
// the negated sub-sum's class first, so the bare `a` member must find a
// sub-multiset denoting that class. Before `assignPreboundBinder` the
// matcher materialized every sub-multiset of the remaining members
// (2^13 bags) and hit the node cap; now the candidates are the bound
// class's own bag nodes.
test "ring conversion?: pre-bound binder cancels a sub-sum without enumerating subsets" {
    try expectFoundAndCompiles(
        \\theorem thm (a b c d e f g h i j k l m n: R):
        \\  $ a + b + c + d + e + f + g + h + i + j + k + l + m
        \\    + -(a + b + c + d + e + f + g + h + i + j + k + l) + n
        \\    = m + n $;
    ,
        \\a + b + c + d + e + f + g + h + i + j + k + l + m
        \\    + -(a + b + c + d + e + f + g + h + i + j + k + l) + n
        \\    = m + n
    );
}

// Cardano's substitution in textbook form. The written goal `(u+v)^3 +
// p*(u+v)` is a sum whose first member's class acquires the expanded
// product, so re-adding the written formula after saturation splices
// past the written tree and interns to the flat sum: extraction must
// start from the seed-time term re-paired to the current member order.
test "ring conversion?: Cardano substitution (extraction from the refreshed seed term)" {
    try expectFoundAndCompiles(
        \\theorem thm (u v p q: R)
        \\  (hp: $ p = -(3 * u * v) $)
        \\  (hq: $ u * u * u + v * v * v = -q $):
        \\  $ (u + v) * (u + v) * (u + v) + p * (u + v) = -q $;
    ,
        \\(u + v) * (u + v) * (u + v) + p * (u + v) = -q
    );
}

// Hypotheses spliced into the goal sum, then `add_neg` and `add_zero`
// on the debris. `add_zero` (`a + 0 = a`) puts `{q, q, q, 0}` and its
// residual `{q, q, q}` in one class, and the debris bag is the older
// node. Rendering the binder `a` as a sub-bag used to keep the first
// candidate that claimed fully — the enclosing bag itself — leaving no
// member for the pattern's `0`; the chain then failed to extract.
test "ring conversion?: residual binder skips a sub-bag that starves later pattern members" {
    try expectFoundAndCompiles(
        \\theorem thm (u v w q s: R)
        \\  (hu: $ u * u * u = q + s $)
        \\  (hv: $ v * v * v = q + -s $)
        \\  (hw: $ w * w * w = q $):
        \\  $ u * u * u + v * v * v + w * w * w = 3 * q $;
    ,
        \\u * u * u + v * v * v + w * w * w = 3 * q
    );
}

// Cardano's formula in radical form: the cubes of `u` and `v` are given
// as `-(q/2) ± s`, so their classes hold a product bag AND a sum. A
// product of such factors used to intern straight to its flat member
// list, and a `distrib` target whose summand class already held a sum
// was recorded as a flat sum too; the 2-member pattern then had no node
// to lay over and the conversion was found but never extracted.
// Intern-time splicing now keeps the nested node beside the flat twin.
test "ring conversion?: radical Cardano (nested node kept at intern-time splicing)" {
    try expectFoundAndCompilesIn(radical_theory,
        \\theorem thm (u v p q s: R)
        \\  (hp: $ p = -(3 * u * v) $)
        \\  (hu: $ u * u * u = -(q / 2) + s $)
        \\  (hv: $ v * v * v = -(q / 2) + -s $):
        \\  $ (u + v) * (u + v) * (u + v) + p * (u + v) = -q $;
    ,
        \\(u + v) * (u + v) * (u + v) + p * (u + v) = -q
    );
}

// The same theorem with `neg_add` enrolled as a FOLD. Its firings leave
// the goal class self-containing (`-q = 3uv² + vp + 0 + (-q)` after `add_neg`),
// and an `add_zero` edge whose binder is bound to that very class then
// rendered its bare-binder side over the creating node: the binder took
// the self member and the rest passed as leftovers the other side did
// not state, so the lowering declined the step. Both sides must now
// agree on their extension, and a binder bound to the bag's own class
// tries the sub-bag decompositions before the self member. About half a
// second in ReleaseFast.
test "ring conversion?: radical Cardano with neg_add (self-containing goal class)" {
    try expectFoundAndCompilesIn(radical_theory,
        \\--| @compute ltr
        \\axiom neg_add (a b: R): $ -(a + b) = -a + -b $;
        \\theorem thm (u v p q s: R)
        \\  (hp: $ p = -(3 * u * v) $)
        \\  (hu: $ u * u * u = -(q / 2) + s $)
        \\  (hv: $ v * v * v = -(q / 2) + -s $):
        \\  $ (u + v) * (u + v) * (u + v) + p * (u + v) = -q $;
    ,
        \\(u + v) * (u + v) * (u + v) + p * (u + v) = -q
    );
}

// A hypothesis that rewrites a PROPER sub-sum of the goal into structure a
// rule needs as one member. The goal is seeded flat before the pool union
// lands, so `x + y` is two members of `{x, y, w, v}`; its class holds
// `-w`, but `add_neg`'s `-a` matched members only. The structured member
// now claims the sub-bag covering that class's own sum, and the union
// anchors on the regrouped twin `{(x + y), w, v}`.
test "ring conversion?: sub-bag claim cancels a hypothesis-rewritten sub-sum" {
    try expectFoundAndCompiles(
        \\theorem thm (x y w v: R) (h: $ x + y = -w $): $ x + y + w + v = v $;
    ,
        \\x + y + w + v = v
    );
}

// The zero instance: `add_zero`'s `0` claims the sub-sum whose class holds
// `0`. A tiny graph — the zero-class blow-up (#244) needs a bag with a
// zero-valued MEMBER, which folds create inside larger sums.
test "ring conversion?: sub-bag claim absorbs a sub-sum equal to zero" {
    try expectFoundAndCompiles(
        \\theorem thm (x y v: R) (h: $ x + y = 0 $): $ x + y + v = v $;
    ,
        \\x + y + v = v
    );
}

// A product whose factor class acquired a sum: `distrib`'s `(b + c)`
// claims the `u * u` sub-product and matches the sum its class holds.
test "ring conversion?: sub-bag claim distributes through a hypothesis-rewritten sub-product" {
    try expectFoundAndCompiles(
        \\theorem thm (u q s: R) (h: $ u * u = -q + s $): $ u * u * u = -q * u + s * u $;
    ,
        \\u * u * u = -q * u + s * u
    );
}

// A goal equal to zero (#244). Once the cancellation cascade joins the
// left side with zero's class, each `0 + rest` intermediate is twinned
// through the classes the hypotheses put sums into, and a twin used to
// fire its own copy of the cascade's redex in a different pair order —
// every intermediate spawned a second chain, twinned in turn: thousands
// of nodes, eleven seconds. A node and its twins now share one fold
// ledger entry.
test "ring conversion?: Cardano substitution as a goal equal to zero" {
    try expectFoundAndCompiles(
        \\theorem thm (u v p q: R)
        \\  (hp: $ p = -(3 * u * v) $)
        \\  (hq: $ q = -(u * u * u + v * v * v) $):
        \\  $ (u + v) * (u + v) * (u + v) + p * (u + v) + q = 0 $;
    ,
        \\(u + v) * (u + v) * (u + v) + p * (u + v) + q = 0
    );
}

// The Cardano resolvent: `u³v³ = (-(p/3))³` from `s² = (q/2)² + (p/3)³` and
// the two cubes, with `neg_add` as `@conversion ltr`. Cancelling `(q/2)²`
// against `-(q/2)²` leaves the goal class self-containing (`-(p/3)³ =
// (q/2)² + -(q/2)² + -(p/3)³`), and its representative is the chain's
// own source `u³v³`: rendered inside a route endpoint it re-posed the
// alignment in flight and the active guard killed every route. A member
// of a self-containing class now renders as the destination of the
// alignment in flight on that class (`memberTerm`). The chain also
// crosses a `div` opening into a product bag, which the checker's ACUI
// comparison has to see through (`normalizer/acui/target.zig`).
test "ring conversion?: resolvent (destination rendering on a self-containing class)" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const mm0_src = radical_theory ++
        \\--| @conversion ltr
        \\axiom neg_add (a b: R): $ -(a + b) = -a + -b $;
        \\theorem resolvent (u v p q s: R)
        \\  (hs: $ s * s = (q / 2) * (q / 2) + (p / 3) * (p / 3) * (p / 3) $)
        \\  (hu: $ u * u * u = -(q / 2) + s $)
        \\  (hv: $ v * v * v = -(q / 2) + -s $):
        \\  $ (u * u * u) * (v * v * v) = -(p / 3) * -(p / 3) * -(p / 3) $;
        \\
    ;
    const proof_src =
        \\resolvent
        \\---------
        \\prod: $ (u * u * u) * (v * v * v) = (-(q / 2) + s) * (-(q / 2) + -s) $ by mul_congr [#2, #3]
        \\goal: $ (u * u * u) * (v * v * v) = -(p / 3) * -(p / 3) * -(p / 3) $ by conversion?
        \\
    ;
    var found = try conversionSuggestions(&arena, mm0_src, proof_src, .{
        .status_detail = true,
    });
    defer found.deinit();
    if (found.status != .found) {
        std.debug.print("status: {s}\n{s}\n", .{
            @tagName(found.status),
            found.status_detail orelse "",
        });
        return error.ConversionMiss;
    }
    try expectConversionCompiles(&arena, mm0_src, proof_src, found.items[0]);
}
