//! Conditional `@conversion` rules (rules with premises), tasks #236/#237.
//!
//! The theory is `fixtures/conditional_cancel.mm0`; each test appends one
//! theorem and drives a single `conversion?` search over it. The battery
//! pins the v1 design in docs/design_notes/conversion_conditional_rules.md:
//! fact premises discharge at class level (lowered through `@congr` and
//! the bundle's transport), equational premises discharge by e-class
//! equality, a non-discharging match is deferred rather than consumed, a
//! saturated miss stays a forced negative, and a premise-bound binder is
//! an enrollment error. A second group of `mul_div` cases stresses the
//! same mechanisms: stacked firings, a materialized compound premise
//! node, a backwards pool equation, a premise proven by another
//! conditional firing (nested premise chains), a two-sided equation
//! goal, and a fact about the wrong term.
//!
//! Before #237 the registry rejected every hyps rule at enrollment
//! (`ConversionRuleHasHypotheses`), so the fixture could not even load.
//! The gate test below pins whichever state `conditional_rules_enrolled`
//! names; the target tests skip while it is false.

const helpers = @import("./helpers.zig");
const std = helpers.std;
const types = helpers.types;
const conversionSuggestions = helpers.conversionSuggestions;
const expectConversionCompiles = helpers.expectConversionCompiles;

const theory = @embedFile("../fixtures/conditional_cancel.mm0");

/// Flipped by #237. Every target test skips while this is false; the
/// gate test asserts the opposite behavior so the flip is not forgotten.
const conditional_rules_enrolled = true;

fn contains(haystack: []const u8, needle: []const u8) bool {
    return std.mem.indexOf(u8, haystack, needle) != null;
}

test "conditional @conversion: enrollment gate (flips with #237)" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const mm0_src = theory ++
        \\theorem gate (a: nat) (h: $ a ≠ 0 $): $ a / a = 1 $;
    ;
    const proof_src =
        \\gate
        \\----
        \\goal: $ a / a = 1 $ by conversion?
        \\
    ;
    if (conditional_rules_enrolled) {
        var found = try conversionSuggestions(&arena, mm0_src, proof_src, .{});
        defer found.deinit();
        try std.testing.expectEqual(types.SearchStatus.found, found.status);
    } else {
        try std.testing.expectError(
            error.ConversionRuleHasHypotheses,
            conversionSuggestions(&arena, mm0_src, proof_src, .{}),
        );
    }
}

test "conditional @conversion: direct fact premise cited from a hypothesis" {
    if (!conditional_rules_enrolled) return error.SkipZigTest;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    // `div_self` needs `a ≠ 0`, which is the hypothesis verbatim; the
    // unconditional `add_zero` joins the same chain.
    const mm0_src = theory ++
        \\theorem direct_fact (a: nat) (h: $ a ≠ 0 $): $ a / a + 0 = 1 $;
    ;
    const proof_src =
        \\direct_fact
        \\----
        \\goal: $ a / a + 0 = 1 $ by conversion?
        \\
    ;
    var found = try conversionSuggestions(&arena, mm0_src, proof_src, .{});
    defer found.deinit();
    try std.testing.expectEqual(types.SearchStatus.found, found.status);
    const replacement = found.items[0].replacement;
    try std.testing.expect(contains(replacement, "by div_self [#1]"));
    try std.testing.expect(contains(replacement, "by add_zero"));
    try expectConversionCompiles(&arena, mm0_src, proof_src, found.items[0]);
}

test "conditional @conversion: class-level discharge lowers through ne_congr + mpbi" {
    if (!conditional_rules_enrolled) return error.SkipZigTest;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    // The premise instance is `b ≠ 0`; the pool fact is `a ≠ 0`. Under
    // `a = b` congruence merges them, so the premise's CLASS is proven,
    // and the lowering must carry the fact across: lift `a = b` through
    // `ne_congr`, then transport with `mpbi`.
    const mm0_src = theory ++
        \\theorem class_transport (a b: nat) (h1: $ a ≠ 0 $) (h2: $ a = b $):
        \\  $ b / b = 1 $;
    ;
    const proof_src =
        \\class_transport
        \\----
        \\goal: $ b / b = 1 $ by conversion?
        \\
    ;
    var found = try conversionSuggestions(&arena, mm0_src, proof_src, .{});
    defer found.deinit();
    try std.testing.expectEqual(types.SearchStatus.found, found.status);
    const replacement = found.items[0].replacement;
    try std.testing.expect(contains(replacement, "by ne_congr"));
    try std.testing.expect(contains(replacement, "by mpbi"));
    try std.testing.expect(contains(replacement, "by div_self"));
    try expectConversionCompiles(&arena, mm0_src, proof_src, found.items[0]);
}

test "conditional @conversion: equational premise fed by an earlier firing" {
    if (!conditional_rules_enrolled) return error.SkipZigTest;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    // `min_le` fires on the fact `a ≤ b` and unions `min a b ~ a`; that
    // union is exactly the equational premise of `max_of_min`, which is
    // discharged by e-class equality (no pool entry states it).
    const mm0_src = theory ++
        \\theorem chained_equation (a b: nat) (h: $ a ≤ b $): $ max a b = b $;
    ;
    const proof_src =
        \\chained_equation
        \\----
        \\goal: $ max a b = b $ by conversion?
        \\
    ;
    var found = try conversionSuggestions(&arena, mm0_src, proof_src, .{});
    defer found.deinit();
    try std.testing.expectEqual(types.SearchStatus.found, found.status);
    const replacement = found.items[0].replacement;
    try std.testing.expect(contains(replacement, "by min_le [#1]"));
    try std.testing.expect(contains(replacement, "by max_of_min"));
    try expectConversionCompiles(&arena, mm0_src, proof_src, found.items[0]);
}

test "conditional @conversion: deferred match fires after a later union" {
    if (!conditional_rules_enrolled) return error.SkipZigTest;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    // `div_self` matches `a / a` on the first pass, but `a ≠ 0` is not
    // proven yet: the pool holds `a * 1 ≠ 0`. Only after `mul_one`
    // unions `a * 1 ~ a` and rebuild merges the `≠` nodes does the
    // premise class become proven. The deferred match must be
    // re-checked (not recorded as applied) and fire on a later
    // iteration.
    const mm0_src = theory ++
        \\theorem deferred_firing (a: nat) (h: $ a * 1 ≠ 0 $): $ a / a = 1 $;
    ;
    const proof_src =
        \\deferred_firing
        \\----
        \\goal: $ a / a = 1 $ by conversion?
        \\
    ;
    var found = try conversionSuggestions(&arena, mm0_src, proof_src, .{});
    defer found.deinit();
    try std.testing.expectEqual(types.SearchStatus.found, found.status);
    const replacement = found.items[0].replacement;
    try std.testing.expect(contains(replacement, "by mul_one"));
    try std.testing.expect(contains(replacement, "by ne_congr"));
    try std.testing.expect(contains(replacement, "by div_self"));
    try expectConversionCompiles(&arena, mm0_src, proof_src, found.items[0]);
}

test "conditional @conversion: premise discharged from an earlier proof line" {
    if (!conditional_rules_enrolled) return error.SkipZigTest;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    // The fact is a labelled line, not a hypothesis; the pool includes
    // lines, so `mul_div` cites the label.
    const mm0_src = theory ++
        \\theorem line_premise (a: nat): $ (a * 1) / 1 = a $;
    ;
    const proof_src =
        \\line_premise
        \\----
        \\fact: $ 1 ≠ 0 $ by one_ne_zero
        \\goal: $ (a * 1) / 1 = a $ by conversion?
        \\
    ;
    var found = try conversionSuggestions(&arena, mm0_src, proof_src, .{});
    defer found.deinit();
    try std.testing.expectEqual(types.SearchStatus.found, found.status);
    const replacement = found.items[0].replacement;
    try std.testing.expect(contains(replacement, "by mul_div [fact]"));
    try expectConversionCompiles(&arena, mm0_src, proof_src, found.items[0]);
}

test "conditional @conversion: stacked cancellations, outer match opened by the inner union" {
    if (!conditional_rules_enrolled) return error.SkipZigTest;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    // `mul_div` first fires on the inner `((a * b) * c) / c ~ a * b`; only
    // then does the outer node `(… / c) / b` match `(x * y) / y`, through
    // the class that now contains `a * b`. Two firings, two distinct
    // premises, both cited from hypotheses.
    const mm0_src = theory ++
        \\theorem stacked_cancel (a b c: nat) (hb: $ b ≠ 0 $) (hc: $ c ≠ 0 $):
        \\  $ ((a * b) * c) / c / b = a $;
    ;
    const proof_src =
        \\stacked_cancel
        \\----
        \\goal: $ ((a * b) * c) / c / b = a $ by conversion?
        \\
    ;
    var found = try conversionSuggestions(&arena, mm0_src, proof_src, .{});
    defer found.deinit();
    try std.testing.expectEqual(types.SearchStatus.found, found.status);
    const replacement = found.items[0].replacement;
    try std.testing.expect(contains(replacement, "by mul_div [#2]"));
    try std.testing.expect(contains(replacement, "by mul_div [#1]"));
    try expectConversionCompiles(&arena, mm0_src, proof_src, found.items[0]);
}

test "conditional @conversion: premise instance materialized as a node and merged by rebuild" {
    if (!conditional_rules_enrolled) return error.SkipZigTest;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    // The match binds `y := b + 0`, so the premise instance is
    // `b + 0 ≠ 0` — a node nothing in the pool states. It must be
    // added to the egraph on the deferred match so that, once
    // `add_zero` unions `b + 0 ~ b`, rebuild congruence merges it with
    // the hypothesis `b ≠ 0`.
    const mm0_src = theory ++
        \\theorem compound_divisor (a b: nat) (h: $ b ≠ 0 $):
        \\  $ (a * (b + 0)) / (b + 0) = a $;
    ;
    const proof_src =
        \\compound_divisor
        \\----
        \\goal: $ (a * (b + 0)) / (b + 0) = a $ by conversion?
        \\
    ;
    var found = try conversionSuggestions(&arena, mm0_src, proof_src, .{});
    defer found.deinit();
    try std.testing.expectEqual(types.SearchStatus.found, found.status);
    const replacement = found.items[0].replacement;
    try std.testing.expect(contains(replacement, "by add_zero"));
    try std.testing.expect(contains(replacement, "by ne_congr"));
    try std.testing.expect(contains(replacement, "by mul_div"));
    try expectConversionCompiles(&arena, mm0_src, proof_src, found.items[0]);
}

test "conditional @conversion: premise carried across a pool equation stated backwards" {
    if (!conditional_rules_enrolled) return error.SkipZigTest;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    // The fact is `c ≠ 0`, the premise instance is `b ≠ 0`, and the
    // pool equation is `b = c` — oriented against the lift `ne_congr`
    // needs, so the premise chain has to flip it with `eq_symm`.
    const mm0_src = theory ++
        \\theorem backwards_equation (a b c: nat) (h1: $ c ≠ 0 $) (h2: $ b = c $):
        \\  $ (a * b) / b = a $;
    ;
    const proof_src =
        \\backwards_equation
        \\----
        \\goal: $ (a * b) / b = a $ by conversion?
        \\
    ;
    var found = try conversionSuggestions(&arena, mm0_src, proof_src, .{});
    defer found.deinit();
    try std.testing.expectEqual(types.SearchStatus.found, found.status);
    const replacement = found.items[0].replacement;
    try std.testing.expect(contains(replacement, "by eq_symm [#2]"));
    try std.testing.expect(contains(replacement, "by ne_congr"));
    try std.testing.expect(contains(replacement, "by mul_div"));
    try expectConversionCompiles(&arena, mm0_src, proof_src, found.items[0]);
}

test "conditional @conversion: a conditional firing proves another rule's premise" {
    if (!conditional_rules_enrolled) return error.SkipZigTest;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    // The divisor is `b / b`, so `mul_div` needs `b / b ≠ 0`. That is
    // proven only because `div_self` (itself conditional, premise
    // `b ≠ 0`) unions `b / b ~ 1` and congruence merges the premise
    // node with the line `1 ≠ 0`. The premise chain therefore contains
    // a conditional step of its own: premises nest.
    const mm0_src = theory ++
        \\theorem nested_premise (a b: nat) (h: $ b ≠ 0 $):
        \\  $ (a * (b / b)) / (b / b) = a $;
    ;
    const proof_src =
        \\nested_premise
        \\----
        \\fact: $ 1 ≠ 0 $ by one_ne_zero
        \\goal: $ (a * (b / b)) / (b / b) = a $ by conversion?
        \\
    ;
    var found = try conversionSuggestions(&arena, mm0_src, proof_src, .{});
    defer found.deinit();
    try std.testing.expectEqual(types.SearchStatus.found, found.status);
    const replacement = found.items[0].replacement;
    try std.testing.expect(contains(replacement, "by div_self [#1]"));
    try std.testing.expect(contains(replacement, "by ne_congr"));
    try std.testing.expect(contains(replacement, "fact]"));
    try std.testing.expect(contains(replacement, "by mul_div"));
    try expectConversionCompiles(&arena, mm0_src, proof_src, found.items[0]);
}

test "conditional @conversion: equation goal closed by a reversed conditional step" {
    if (!conditional_rules_enrolled) return error.SkipZigTest;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    // Both sides cancel to `a`, with different premises. The lowering
    // walks lhs → a → rhs, so the second `mul_div` step is emitted
    // reversed and must still carry its premise label.
    const mm0_src = theory ++
        \\theorem both_sides (a c d: nat) (hc: $ c ≠ 0 $) (hd: $ d ≠ 0 $):
        \\  $ (a * c) / c = (a * d) / d $;
    ;
    const proof_src =
        \\both_sides
        \\----
        \\goal: $ (a * c) / c = (a * d) / d $ by conversion?
        \\
    ;
    var found = try conversionSuggestions(&arena, mm0_src, proof_src, .{});
    defer found.deinit();
    try std.testing.expectEqual(types.SearchStatus.found, found.status);
    const replacement = found.items[0].replacement;
    try std.testing.expect(contains(replacement, "by mul_div [#1]"));
    try std.testing.expect(contains(replacement, "by mul_div [#2]"));
    try std.testing.expect(contains(replacement, "by eq_symm"));
    try expectConversionCompiles(&arena, mm0_src, proof_src, found.items[0]);
}

test "conditional @conversion: a fact about the wrong term does not discharge" {
    if (!conditional_rules_enrolled) return error.SkipZigTest;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    // `mul_div` needs `b ≠ 0`; the pool proves `a ≠ 0`, a different
    // class. Class-level discharge must not confuse the two: the match
    // stays deferred, saturation reaches fixpoint, and the report says
    // the premise was never licensed.
    const mm0_src = theory ++
        \\theorem wrong_fact (a b: nat) (h: $ a ≠ 0 $): $ (a * b) / b = a $;
    ;
    const proof_src =
        \\wrong_fact
        \\----
        \\goal: $ (a * b) / b = a $ by conversion?
        \\
    ;
    var miss = try conversionSuggestions(&arena, mm0_src, proof_src, .{
        .status_detail = true,
    });
    defer miss.deinit();
    try std.testing.expectEqual(types.SearchStatus.miss, miss.status);
    const detail = miss.status_detail orelse return error.MissingStatusDetail;
    try std.testing.expect(contains(detail, "the egraph saturated"));
    try std.testing.expect(contains(detail, "conditional-rule matches stayed deferred"));
    try std.testing.expect(!contains(detail, "NOT a forced negative"));
}

test "conditional @conversion: undischargeable premise is a forced negative" {
    if (!conditional_rules_enrolled) return error.SkipZigTest;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    // No hypothesis at all: `div_self` matches but its premise never
    // becomes proven. Saturation must still reach fixpoint — a
    // permanently deferred match is not a budget event — and the miss
    // must be reported unhedged.
    const mm0_src = theory ++
        \\theorem no_hypothesis (a: nat): $ a / a = 1 $;
    ;
    const proof_src =
        \\no_hypothesis
        \\----
        \\goal: $ a / a = 1 $ by conversion?
        \\
    ;
    var miss = try conversionSuggestions(&arena, mm0_src, proof_src, .{
        .status_detail = true,
    });
    defer miss.deinit();
    try std.testing.expectEqual(types.SearchStatus.miss, miss.status);
    const detail = miss.status_detail orelse return error.MissingStatusDetail;
    try std.testing.expect(contains(detail, "the egraph saturated"));
    try std.testing.expect(!contains(detail, "NOT a forced negative"));
}

test "conditional @conversion: premise-bound binder is rejected at enrollment" {
    if (!conditional_rules_enrolled) return error.SkipZigTest;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    // lhs-only coverage: `y` occurs only in the premise, so after the
    // match side `x / x` is bound the premise is not ground and
    // discharge would be a join, not a lookup (#239 lifts this). The
    // diagnostic must name the binder.
    const mm0_src = theory ++
        \\--| @conversion ltr
        \\axiom self_div_sq (x y: nat): $ x = y * y $ > $ x / x = 1 $;
        \\theorem sq (a: nat): $ a / a = 1 $;
    ;
    const proof_src =
        \\sq
        \\----
        \\goal: $ a / a = 1 $ by conversion?
        \\
    ;
    try std.testing.expectError(
        error.ConversionPremiseBinderNotCovered,
        conversionSuggestions(&arena, mm0_src, proof_src, .{}),
    );
}
