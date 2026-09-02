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

fn expectFoundAndCompiles(
    comptime statement: []const u8,
    comptime goal: []const u8,
) !void {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const mm0_src = theory ++ statement;
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

