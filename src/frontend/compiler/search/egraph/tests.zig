//! Tests for the conversion? egraph (split out of egraph.zig; everything
//! here exercises the egraph through its public API).

const std = @import("std");
const TemplateExpr = @import("../../../rules.zig").TemplateExpr;

const egraph = @import("../egraph.zig");
const EGraph = egraph.EGraph;
const Child = egraph.Child;
const ENode = egraph.ENode;
const EClassId = egraph.EClassId;
const LeafId = egraph.LeafId;
const Rule = egraph.Rule;
const Justification = egraph.Justification;
const SaturateOutcome = egraph.SaturateOutcome;
const SaturateOptions = egraph.SaturateOptions;
const Term = egraph.Term;
const termEql = egraph.termEql;
const Step = egraph.Step;

const testing = std.testing;

const ADD: u32 = 1;
const F: u32 = 2;
const ALL: u32 = 3;

fn testAdd2(eg: *EGraph, term_id: u32, a: Child, b: Child) !EClassId {
    return eg.add(.{ .app = .{
        .term_id = term_id,
        .children = &.{ a, b },
    } });
}

test "egraph hashcons dedupes structurally equal nodes" {
    var arena_state = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena_state.deinit();
    var eg = EGraph.init(arena_state.allocator());

    const x = try eg.add(.{ .leaf = 10 });
    const y = try eg.add(.{ .leaf = 11 });
    const first = try testAdd2(&eg, ADD, .{ .class = x }, .{ .class = y });
    const classes_before = eg.parents.items.len;
    const second = try testAdd2(&eg, ADD, .{ .class = x }, .{ .class = y });
    try testing.expectEqual(first, second);
    try testing.expectEqual(classes_before, eg.parents.items.len);
    try testing.expectEqual(@as(usize, 3), eg.eNodeCount());
}

test "egraph rebuild closes congruence only for enrolled heads" {
    var arena_state = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena_state.deinit();

    // Enrolled: f(a) and f(b) merge once a ~ b.
    var eg = EGraph.init(arena_state.allocator());
    try eg.congr_heads.put(eg.allocator, F, {});
    const a = try eg.add(.{ .leaf = 1 });
    const b = try eg.add(.{ .leaf = 2 });
    const fa = try testAdd2(&eg, F, .{ .class = a }, .{ .class = a });
    const fb = try testAdd2(&eg, F, .{ .class = b }, .{ .class = b });
    try testing.expect(!eg.sameClass(fa, fb));
    _ = try eg.merge(a, b, .{ .congruence = .{ .left = 0, .right = 1 } });
    const ids_before = eg.parents.items.len;
    _ = try eg.rebuild();
    try testing.expect(eg.sameClass(fa, fb));
    // Rebuild reuses ids — the microegg pitfall.
    try testing.expectEqual(ids_before, eg.parents.items.len);

    // Not enrolled: same setup stays split.
    var eg2 = EGraph.init(arena_state.allocator());
    const a2 = try eg2.add(.{ .leaf = 1 });
    const b2 = try eg2.add(.{ .leaf = 2 });
    const fa2 = try testAdd2(&eg2, F, .{ .class = a2 }, .{ .class = a2 });
    const fb2 = try testAdd2(&eg2, F, .{ .class = b2 }, .{ .class = b2 });
    _ = try eg2.merge(a2, b2, .{ .congruence = .{ .left = 0, .right = 1 } });
    _ = try eg2.rebuild();
    try testing.expect(!eg2.sameClass(fa2, fb2));
}

test "egraph keeps bound-position children rigid" {
    var arena_state = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena_state.deinit();
    var eg = EGraph.init(arena_state.allocator());
    try eg.congr_heads.put(eg.allocator, ALL, {});
    try eg.bound_masks.put(eg.allocator, ALL, 0b01);

    const p = try eg.add(.{ .leaf = 20 });
    const q = try eg.add(.{ .leaf = 21 });
    // all x. p / all y. p: identical body class, different bound atom —
    // congruence must NOT merge them (no @congr lemma can).
    const all_x_p = try testAdd2(&eg, ALL, .{ .bound = 1 }, .{ .class = p });
    const all_y_p = try testAdd2(&eg, ALL, .{ .bound = 2 }, .{ .class = p });
    // all x. p / all x. q with p ~ q: same bound atom — merges.
    const all_x_q = try testAdd2(&eg, ALL, .{ .bound = 1 }, .{ .class = q });
    _ = try eg.merge(p, q, .{ .congruence = .{ .left = 0, .right = 1 } });
    _ = try eg.rebuild();
    try testing.expect(!eg.sameClass(all_x_p, all_y_p));
    try testing.expect(eg.sameClass(all_x_p, all_x_q));
}

const BINDER_A = TemplateExpr{ .binder = 0 };
const BINDER_B = TemplateExpr{ .binder = 1 };
const BINDER_C = TemplateExpr{ .binder = 2 };

fn app2(comptime term_id: u32, comptime a: TemplateExpr, comptime b: TemplateExpr) TemplateExpr {
    return .{ .app = .{ .term_id = term_id, .args = &.{ a, b } } };
}

// add(a, b) ~ add(b, a)
const COMM_MATCH = app2(ADD, BINDER_A, BINDER_B);
const COMM_TARGET = app2(ADD, BINDER_B, BINDER_A);
// add(add(a, b), c) ~ add(a, add(b, c))
const ASSOC_MATCH = app2(ADD, app2(ADD, BINDER_A, BINDER_B), BINDER_C);
const ASSOC_TARGET = app2(ADD, BINDER_A, app2(ADD, BINDER_B, BINDER_C));

const AC_RULES = [_]Rule{
    .{
        .rule_id = 100,
        .reversed = false,
        .match_side = ASSOC_MATCH,
        .target_side = ASSOC_TARGET,
        .num_binders = 3,
    },
    .{
        .rule_id = 100,
        .reversed = true,
        .match_side = ASSOC_TARGET,
        .target_side = ASSOC_MATCH,
        .num_binders = 3,
    },
    .{
        .rule_id = 101,
        .reversed = false,
        .match_side = COMM_MATCH,
        .target_side = COMM_TARGET,
        .num_binders = 2,
    },
};

test "egraph saturation applies a commutativity rule to fixpoint" {
    var arena_state = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena_state.deinit();
    var eg = EGraph.init(arena_state.allocator());
    try eg.congr_heads.put(eg.allocator, ADD, {});

    const x = try eg.add(.{ .leaf = 1 });
    const y = try eg.add(.{ .leaf = 2 });
    const xy = try testAdd2(&eg, ADD, .{ .class = x }, .{ .class = y });
    const yx = try testAdd2(&eg, ADD, .{ .class = y }, .{ .class = x });
    try testing.expect(!eg.sameClass(xy, yx));

    const stats = try eg.saturate(AC_RULES[2..], .{});
    try testing.expectEqual(SaturateOutcome.saturated, stats.outcome);
    try testing.expect(eg.sameClass(xy, yx));
    try testing.expect(!eg.sameClass(xy, x));
}

test "egraph binder consistency: idempotent contraction matches only squares" {
    var arena_state = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena_state.deinit();
    var eg = EGraph.init(arena_state.allocator());
    try eg.congr_heads.put(eg.allocator, ADD, {});

    // add(a, a) ~ a
    const idem = [_]Rule{.{
        .rule_id = 102,
        .reversed = false,
        .match_side = app2(ADD, BINDER_A, BINDER_A),
        .target_side = BINDER_A,
        .num_binders = 1,
    }};

    const x = try eg.add(.{ .leaf = 1 });
    const y = try eg.add(.{ .leaf = 2 });
    const xy = try testAdd2(&eg, ADD, .{ .class = x }, .{ .class = y });
    const xx = try testAdd2(&eg, ADD, .{ .class = x }, .{ .class = x });

    const stats = try eg.saturate(&idem, .{});
    try testing.expectEqual(SaturateOutcome.saturated, stats.outcome);
    try testing.expect(eg.sameClass(xx, x));
    try testing.expect(!eg.sameClass(xy, x));
    try testing.expect(!eg.sameClass(xy, y));
}

test "egraph node cap stops saturation with a capped outcome" {
    var arena_state = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena_state.deinit();
    var eg = EGraph.init(arena_state.allocator());
    try eg.congr_heads.put(eg.allocator, ADD, {});

    // add(a, b) ~ add(f(a, b), b): each round the F node lands in a fresh
    // class (F is not a rule head and not congruence-enrolled), so the
    // matched ADD class accrues a genuinely new member every iteration and
    // the node cap must trip. (An `add(a,b) ~ add(add(a,b),b)` rule would
    // NOT work here: the unrolling collapses into one cyclic e-class and
    // saturates — that is the egraph working as intended.)
    const grow = [_]Rule{.{
        .rule_id = 103,
        .reversed = false,
        .match_side = app2(ADD, BINDER_A, BINDER_B),
        .target_side = app2(ADD, app2(F, BINDER_A, BINDER_B), BINDER_B),
        .num_binders = 2,
    }};

    const x = try eg.add(.{ .leaf = 1 });
    const y = try eg.add(.{ .leaf = 2 });
    _ = try testAdd2(&eg, ADD, .{ .class = x }, .{ .class = y });

    const stats = try eg.saturate(&grow, .{ .max_nodes = 32 });
    try testing.expectEqual(SaturateOutcome.node_capped, stats.outcome);
}

/// Left-comb sum of `n` fresh leaves: add(x1, add(x2, ... add(x_{n-1}, x_n))).
fn seedSum(eg: *EGraph, n: u32) !EClassId {
    var acc = try eg.add(.{ .leaf = n });
    var i: u32 = n - 1;
    while (true) {
        const leaf = try eg.add(.{ .leaf = i });
        acc = try testAdd2(eg, ADD, .{ .class = leaf }, .{ .class = acc });
        if (i == 1) break;
        i -= 1;
    }
    return acc;
}

/// The microegg closed-form AC oracle: a sum of n variables under
/// assoc(both) + comm saturates to exactly 2^n - 1 e-classes and
/// 3^n - 2^(n+1) + 1 add-nodes plus n leaf nodes.
fn checkAcOracle(n: u32, opts: SaturateOptions) !void {
    var arena_state = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena_state.deinit();
    var eg = EGraph.init(arena_state.allocator());
    try eg.congr_heads.put(eg.allocator, ADD, {});

    _ = try seedSum(&eg, n);
    const stats = try eg.saturate(&AC_RULES, opts);
    try testing.expectEqual(SaturateOutcome.saturated, stats.outcome);

    const expected_classes = (std.math.pow(usize, 2, n)) - 1;
    const expected_nodes = std.math.pow(usize, 3, n) -
        std.math.pow(usize, 2, n + 1) + 1 + n;
    try testing.expectEqual(expected_classes, eg.classCount());
    try testing.expectEqual(expected_nodes, eg.eNodeCount());
}

// --- Explanation tests -------------------------------------------------

fn termClassOf(eg: *const EGraph, term: *const Term) EClassId {
    return eg.find(eg.nodes.items[term.node].class);
}

fn tLeaf(eg: *EGraph, leaf: u32) !*const Term {
    _ = try eg.add(.{ .leaf = leaf });
    const node = (try eg.lookupNode(.{ .leaf = leaf })).?;
    const term = try eg.allocator.create(Term);
    term.* = .{ .node = node, .children = &.{} };
    return term;
}

fn tApp2(
    eg: *EGraph,
    term_id: u32,
    a: *const Term,
    b: *const Term,
) !*const Term {
    const shape = ENode{ .app = .{ .term_id = term_id, .children = &.{
        .{ .class = termClassOf(eg, a) },
        .{ .class = termClassOf(eg, b) },
    } } };
    _ = try eg.add(shape);
    const node = (try eg.lookupNode(shape)).?;
    const children = try eg.allocator.alloc(?*const Term, 2);
    children[0] = a;
    children[1] = b;
    const term = try eg.allocator.create(Term);
    term.* = .{ .node = node, .children = children };
    return term;
}

/// Replay validator: apply each step's rewrite at its position, requiring
/// the redex to match `before` exactly. Returns the final term.
fn applyStepAt(
    eg: *EGraph,
    term: *const Term,
    position: []const u32,
    before: *const Term,
    after: *const Term,
) !?*const Term {
    if (position.len == 0) {
        if (!termEql(eg, term, before)) return null;
        return after;
    }
    const idx = position[0];
    const child = term.children[idx] orelse return null;
    const replaced = (try applyStepAt(
        eg,
        child,
        position[1..],
        before,
        after,
    )) orelse return null;
    const children = try eg.allocator.dupe(?*const Term, term.children);
    children[idx] = replaced;
    const rebuilt = try eg.allocator.create(Term);
    rebuilt.* = .{ .node = term.node, .children = children };
    return rebuilt;
}

fn applySteps(
    eg: *EGraph,
    from: *const Term,
    steps: []const Step,
) !?*const Term {
    var current = from;
    for (steps) |step| {
        current = (try applyStepAt(
            eg,
            current,
            step.position,
            step.before,
            step.after,
        )) orelse return null;
    }
    return current;
}

fn expectValidChain(
    eg: *EGraph,
    from: *const Term,
    to: *const Term,
    steps: []const Step,
) !void {
    const final = (try applySteps(eg, from, steps)) orelse {
        return error.ChainBroken;
    };
    try testing.expect(termEql(eg, final, to));
}

test "egraph explains a root commutativity step" {
    var arena_state = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena_state.deinit();
    var eg = EGraph.init(arena_state.allocator());
    try eg.congr_heads.put(eg.allocator, ADD, {});

    const x = try tLeaf(&eg, 1);
    const y = try tLeaf(&eg, 2);
    const from = try tApp2(&eg, ADD, x, y);
    const to = try tApp2(&eg, ADD, y, x);

    const rules = AC_RULES[2..];
    _ = try eg.saturate(rules, .{});
    const steps = (try eg.explain(rules, from, to, .{})) orelse {
        return error.ExpectedExplanation;
    };
    try testing.expectEqual(@as(usize, 1), steps.len);
    try testing.expectEqual(@as(u32, 101), steps[0].source.rule);
    try testing.expect(!steps[0].needs_symm);
    try testing.expectEqual(@as(usize, 0), steps[0].position.len);
    try expectValidChain(&eg, from, to, steps);
}

test "egraph explains a congruence-lifted step at a position" {
    var arena_state = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena_state.deinit();
    var eg = EGraph.init(arena_state.allocator());
    try eg.congr_heads.put(eg.allocator, ADD, {});
    try eg.congr_heads.put(eg.allocator, F, {});

    const x = try tLeaf(&eg, 1);
    const y = try tLeaf(&eg, 2);
    const z = try tLeaf(&eg, 3);
    const from = try tApp2(&eg, F, try tApp2(&eg, ADD, x, y), z);
    const to = try tApp2(&eg, F, try tApp2(&eg, ADD, y, x), z);

    const rules = AC_RULES[2..];
    _ = try eg.saturate(rules, .{});
    const steps = (try eg.explain(rules, from, to, .{})) orelse {
        return error.ExpectedExplanation;
    };
    try testing.expectEqual(@as(usize, 1), steps.len);
    try testing.expectEqualSlices(u32, &.{0}, steps[0].position);
    try expectValidChain(&eg, from, to, steps);
}

test "egraph explains bare-binder contraction in both directions" {
    var arena_state = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena_state.deinit();
    var eg = EGraph.init(arena_state.allocator());
    try eg.congr_heads.put(eg.allocator, ADD, {});

    // add(a, a) ~ a
    const idem = [_]Rule{.{
        .rule_id = 102,
        .reversed = false,
        .match_side = app2(ADD, BINDER_A, BINDER_A),
        .target_side = BINDER_A,
        .num_binders = 1,
    }};

    const x = try tLeaf(&eg, 1);
    const xx = try tApp2(&eg, ADD, x, x);
    _ = try eg.saturate(&idem, .{});

    // Forward: the contraction as annotated.
    const forward = (try eg.explain(&idem, xx, x, .{})) orelse {
        return error.ExpectedExplanation;
    };
    try testing.expectEqual(@as(usize, 1), forward.len);
    try testing.expect(!forward[0].needs_symm);
    try testing.expect(termEql(&eg, forward[0].after, x));
    try expectValidChain(&eg, xx, x, forward);
    // The binding renders the contracted class's representative.
    try testing.expect(forward[0].bindings[0] != null);
    try testing.expect(termEql(&eg, forward[0].bindings[0].?.term, x));

    // Reverse traversal: the same edge lowers through symm.
    const reverse = (try eg.explain(&idem, x, xx, .{})) orelse {
        return error.ExpectedExplanation;
    };
    try testing.expectEqual(@as(usize, 1), reverse.len);
    try testing.expect(reverse[0].needs_symm);
    try expectValidChain(&eg, x, xx, reverse);
}

test "egraph explains through a pool-equation ground union" {
    var arena_state = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena_state.deinit();
    var eg = EGraph.init(arena_state.allocator());
    try eg.congr_heads.put(eg.allocator, F, {});

    const x = try tLeaf(&eg, 1);
    const y = try tLeaf(&eg, 2);
    const fx = try tApp2(&eg, F, x, x);
    const fy = try tApp2(&eg, F, y, y);
    _ = try eg.merge(
        termClassOf(&eg, x),
        termClassOf(&eg, y),
        .{ .pool_equation = .{ .pool_index = 3, .lhs = x, .rhs = y } },
    );
    _ = try eg.saturate(&.{}, .{});
    try testing.expect(eg.sameClass(
        termClassOf(&eg, fx),
        termClassOf(&eg, fy),
    ));

    // Forward: both congruence positions rewrite x -> y, citing the pool
    // entry as-is.
    const forward = (try eg.explain(&.{}, fx, fy, .{})) orelse {
        return error.ExpectedExplanation;
    };
    try testing.expectEqual(@as(usize, 2), forward.len);
    for (forward) |step| {
        try testing.expectEqual(@as(u32, 3), step.source.pool_equation);
        try testing.expect(!step.needs_symm);
        try testing.expectEqual(@as(usize, 1), step.position.len);
    }
    try expectValidChain(&eg, fx, fy, forward);

    // Reverse traversal of the same edge needs symm.
    const reverse = (try eg.explain(&.{}, fy, fx, .{})) orelse {
        return error.ExpectedExplanation;
    };
    try testing.expectEqual(@as(usize, 2), reverse.len);
    for (reverse) |step| {
        try testing.expectEqual(@as(u32, 3), step.source.pool_equation);
        try testing.expect(step.needs_symm);
    }
    try expectValidChain(&eg, fy, fx, reverse);
}

/// `all` term for tests: a bound atom at position 0, the body class at
/// position 1 (mirror of `tApp2` for a binder-headed term).
fn tAll(eg: *EGraph, atom: LeafId, body: *const Term) !*const Term {
    const shape = ENode{ .app = .{ .term_id = ALL, .children = &.{
        .{ .bound = atom },
        .{ .class = termClassOf(eg, body) },
    } } };
    _ = try eg.add(shape);
    const node = (try eg.lookupNode(shape)).?;
    const children = try eg.allocator.alloc(?*const Term, 2);
    children[0] = null;
    children[1] = body;
    const term = try eg.allocator.create(Term);
    term.* = .{ .node = node, .children = children };
    return term;
}

// all x. p ~ p, with the verifier's obligation that x not occur in p
// (binder 1 does not depend on binder 0).
const DROP_ALL = [_]Rule{.{
    .rule_id = 104,
    .reversed = false,
    .match_side = app2(ALL, BINDER_A, BINDER_B),
    .target_side = BINDER_B,
    .num_binders = 2,
    .bound_slots = &.{0},
    .restrictions = &.{.{ .bound_slot = 0, .term_slot = 1 }},
}};

test "dep gate refuses a match with no avoiding representative" {
    var arena_state = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena_state.deinit();
    var eg = EGraph.init(arena_state.allocator());
    try eg.bound_masks.put(eg.allocator, ALL, 0b01);

    // all v. f(v, v): the body class denotes only v-containing terms, so
    // the vacuous-quantifier drop must not fire.
    const v = try tLeaf(&eg, 1);
    const body = try tApp2(&eg, F, v, v);
    const all_v = try tAll(&eg, 1, body);

    const stats = try eg.saturate(&DROP_ALL, .{});
    try testing.expectEqual(SaturateOutcome.saturated, stats.outcome);
    try testing.expect(stats.dep_deferred > 0);
    try testing.expect(!eg.sameClass(
        termClassOf(&eg, all_v),
        termClassOf(&eg, body),
    ));

    // Control: without the declared restriction the same match unions —
    // the refusal above is the gate, not the matcher.
    var eg2 = EGraph.init(arena_state.allocator());
    try eg2.bound_masks.put(eg2.allocator, ALL, 0b01);
    const v2 = try tLeaf(&eg2, 1);
    const body2 = try tApp2(&eg2, F, v2, v2);
    const all_v2 = try tAll(&eg2, 1, body2);
    const ungated = [_]Rule{.{
        .rule_id = 104,
        .reversed = false,
        .match_side = app2(ALL, BINDER_A, BINDER_B),
        .target_side = BINDER_B,
        .num_binders = 2,
    }};
    _ = try eg2.saturate(&ungated, .{});
    try testing.expect(eg2.sameClass(
        termClassOf(&eg2, all_v2),
        termClassOf(&eg2, body2),
    ));
}

test "dep gate admits via a ground union and extraction cites the avoiding representative" {
    var arena_state = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena_state.deinit();
    var eg = EGraph.init(arena_state.allocator());
    try eg.bound_masks.put(eg.allocator, ALL, 0b01);

    // all v. f(v, v) with a local equation f(v, v) ~ c: the body class
    // now denotes the v-free `c`, so the drop is justified — and the
    // extracted instance must cite `c`, never f(v, v).
    const v = try tLeaf(&eg, 1);
    const body = try tApp2(&eg, F, v, v);
    const c = try tLeaf(&eg, 2);
    _ = try eg.merge(
        termClassOf(&eg, body),
        termClassOf(&eg, c),
        .{ .pool_equation = .{ .pool_index = 0, .lhs = body, .rhs = c } },
    );
    const all_v = try tAll(&eg, 1, body);

    const stats = try eg.saturate(&DROP_ALL, .{});
    try testing.expectEqual(SaturateOutcome.saturated, stats.outcome);
    try testing.expect(eg.sameClass(
        termClassOf(&eg, all_v),
        termClassOf(&eg, c),
    ));

    const steps = (try eg.explain(&DROP_ALL, all_v, c, .{})) orelse {
        return error.ExpectedExplanation;
    };
    try expectValidChain(&eg, all_v, c, steps);
    var saw_rule = false;
    for (steps) |step| switch (step.source) {
        .rule => {
            saw_rule = true;
            // The restricted binding extracts under the avoid-mask.
            try testing.expect(termEql(&eg, step.bindings[1].?.term, c));
        },
        .pool_equation, .ac_flatten => {},
    };
    try testing.expect(saw_rule);
}

test "dep gate requires pairwise-distinct bound atoms" {
    var arena_state = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena_state.deinit();

    // all x. all y. p ~ all y. all x. p (p depends on both, so no
    // restrictions — only the distinctness half applies).
    const swap = [_]Rule{.{
        .rule_id = 105,
        .reversed = false,
        .match_side = app2(ALL, BINDER_A, app2(ALL, BINDER_B, BINDER_C)),
        .target_side = app2(ALL, BINDER_B, app2(ALL, BINDER_A, BINDER_C)),
        .num_binders = 3,
        .bound_slots = &.{ 0, 1 },
    }};

    // Same atom twice: all v. all v. q must defer.
    var eg = EGraph.init(arena_state.allocator());
    try eg.bound_masks.put(eg.allocator, ALL, 0b01);
    const q = try tLeaf(&eg, 3);
    const inner = try tAll(&eg, 1, q);
    _ = try tAll(&eg, 1, inner);
    const stats = try eg.saturate(&swap, .{});
    try testing.expectEqual(SaturateOutcome.saturated, stats.outcome);
    try testing.expect(stats.dep_deferred > 0);
    try testing.expectEqual(@as(usize, 0), stats.unions_applied);

    // Distinct atoms admit: all v. all w. q gains the swapped form.
    var eg2 = EGraph.init(arena_state.allocator());
    try eg2.bound_masks.put(eg2.allocator, ALL, 0b01);
    const q2 = try tLeaf(&eg2, 3);
    const inner2 = try tAll(&eg2, 2, q2);
    const outer2 = try tAll(&eg2, 1, inner2);
    const stats2 = try eg2.saturate(&swap, .{});
    try testing.expectEqual(@as(usize, 0), stats2.dep_deferred);
    const swapped_inner = try tAll(&eg2, 1, q2);
    const swapped_outer = try tAll(&eg2, 2, swapped_inner);
    try testing.expect(eg2.sameClass(
        termClassOf(&eg2, outer2),
        termClassOf(&eg2, swapped_outer),
    ));
}

test "egraph explains a two-step nested rewrite chain" {
    var arena_state = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena_state.deinit();
    var eg = EGraph.init(arena_state.allocator());
    try eg.congr_heads.put(eg.allocator, ADD, {});

    const x = try tLeaf(&eg, 1);
    const y = try tLeaf(&eg, 2);
    const z = try tLeaf(&eg, 3);
    const from = try tApp2(&eg, ADD, try tApp2(&eg, ADD, x, y), z);
    const to = try tApp2(&eg, ADD, z, try tApp2(&eg, ADD, y, x));

    const rules = AC_RULES[2..];
    _ = try eg.saturate(rules, .{});
    const steps = (try eg.explain(rules, from, to, .{})) orelse {
        return error.ExpectedExplanation;
    };
    try testing.expectEqual(@as(usize, 2), steps.len);
    try expectValidChain(&eg, from, to, steps);
}

test "egraph AC oracle: four-variable closed form" {
    try checkAcOracle(4, .{});
}

test "egraph AC oracle: seven-variable closed form" {
    // Deliberately exhaustive: the closed form needs the full tree-mode
    // flood the production match budgets exist to throttle, so lift them
    // along with the node/iteration caps.
    try checkAcOracle(7, .{
        .max_iterations = 64,
        .max_nodes = 1_000_000,
        .ac_match_budget = std.math.maxInt(usize),
        .ac_iter_match_budget = std.math.maxInt(usize),
    });
}

// --- AC bag-representation tests ----------------------------------------

fn leafClassOf(eg: *EGraph, id: u32) !EClassId {
    return eg.add(.{ .leaf = id });
}

fn leftCombOf(eg: *EGraph, ids: []const u32) !EClassId {
    var acc = try leafClassOf(eg, ids[0]);
    for (ids[1..]) |id| {
        const next = try leafClassOf(eg, id);
        acc = try testAdd2(eg, ADD, .{ .class = acc }, .{ .class = next });
    }
    return acc;
}

fn rightCombOf(eg: *EGraph, ids: []const u32) !EClassId {
    var acc = try leafClassOf(eg, ids[ids.len - 1]);
    var i = ids.len - 1;
    while (i > 0) {
        i -= 1;
        const prev = try leafClassOf(eg, ids[i]);
        acc = try testAdd2(eg, ADD, .{ .class = prev }, .{ .class = acc });
    }
    return acc;
}

/// The three deterministic tree shapes per member list used by the bag
/// tests: ascending left comb, descending right comb, and (for three or
/// more members) a split pairing left and right combs of the halves.
fn shapeVariants(
    eg: *EGraph,
    ids: []const u32,
    reversed_buf: []u32,
    out: *std.ArrayListUnmanaged(EClassId),
) !void {
    try out.append(eg.allocator, try leftCombOf(eg, ids));
    for (ids, 0..) |id, i| reversed_buf[ids.len - 1 - i] = id;
    try out.append(eg.allocator, try rightCombOf(eg, reversed_buf[0..ids.len]));
    if (ids.len >= 3) {
        const half = ids.len / 2;
        const left = try leftCombOf(eg, ids[0..half]);
        const right = try rightCombOf(eg, ids[half..]);
        try out.append(eg.allocator, try testAdd2(
            eg,
            ADD,
            .{ .class = left },
            .{ .class = right },
        ));
    }
}

test "bag interning makes the AC closure definitional" {
    var arena_state = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena_state.deinit();
    var eg = EGraph.init(arena_state.allocator());
    try eg.congr_heads.put(eg.allocator, ADD, {});
    try eg.ac_heads.put(eg.allocator, ADD, {});

    const n: u5 = 5;
    var subset_classes: std.ArrayListUnmanaged(EClassId) = .{};
    var mask: u32 = 1;
    while (mask < (@as(u32, 1) << n)) : (mask += 1) {
        var ids: std.ArrayListUnmanaged(u32) = .{};
        for (1..n + 1) |id| {
            if ((mask >> @intCast(id - 1)) & 1 == 1) {
                try ids.append(eg.allocator, @intCast(id));
            }
        }
        var reversed_buf: [8]u32 = undefined;
        var variants: std.ArrayListUnmanaged(EClassId) = .{};
        if (ids.items.len == 1) {
            try variants.append(
                eg.allocator,
                try leafClassOf(&eg, ids.items[0]),
            );
        } else {
            try shapeVariants(&eg, ids.items, &reversed_buf, &variants);
        }
        // Every grouping and order of one subset is one class at intern
        // time — no saturation ran at all.
        for (variants.items[1..]) |variant| {
            try testing.expect(eg.sameClass(variants.items[0], variant));
        }
        try subset_classes.append(eg.allocator, variants.items[0]);
    }
    // Distinct subsets stay distinct.
    for (subset_classes.items, 0..) |a, i| {
        for (subset_classes.items[i + 1 ..]) |b| {
            try testing.expect(!eg.sameClass(a, b));
        }
    }
    // ~2^n representation: one bag per compound subset plus the leaves,
    // where the tree representation's closure needs 3^n-ish nodes.
    const expected: usize = (std.math.pow(usize, 2, n)) - 1;
    try testing.expectEqual(expected, eg.classCount());
    try testing.expectEqual(expected, eg.eNodeCount());
}

test "bag egraph agrees with saturated tree egraph (differential oracle)" {
    var arena_state = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena_state.deinit();

    const n: u5 = 5;
    var tree = EGraph.init(arena_state.allocator());
    try tree.congr_heads.put(tree.allocator, ADD, {});
    var bagged = EGraph.init(arena_state.allocator());
    try bagged.congr_heads.put(bagged.allocator, ADD, {});
    try bagged.ac_heads.put(bagged.allocator, ADD, {});

    var tree_classes: std.ArrayListUnmanaged(EClassId) = .{};
    var bag_classes: std.ArrayListUnmanaged(EClassId) = .{};
    var mask: u32 = 1;
    while (mask < (@as(u32, 1) << n)) : (mask += 1) {
        var ids: std.ArrayListUnmanaged(u32) = .{};
        for (1..n + 1) |id| {
            if ((mask >> @intCast(id - 1)) & 1 == 1) {
                try ids.append(arena_state.allocator(), @intCast(id));
            }
        }
        var reversed_buf: [8]u32 = undefined;
        if (ids.items.len == 1) {
            try tree_classes.append(
                tree.allocator,
                try leafClassOf(&tree, ids.items[0]),
            );
            try bag_classes.append(
                bagged.allocator,
                try leafClassOf(&bagged, ids.items[0]),
            );
            continue;
        }
        var tree_variants: std.ArrayListUnmanaged(EClassId) = .{};
        try shapeVariants(&tree, ids.items, &reversed_buf, &tree_variants);
        try tree_classes.appendSlice(tree.allocator, tree_variants.items);
        var bag_variants: std.ArrayListUnmanaged(EClassId) = .{};
        try shapeVariants(&bagged, ids.items, &reversed_buf, &bag_variants);
        try bag_classes.appendSlice(bagged.allocator, bag_variants.items);
    }

    // The tree side must saturate comm+assoc to see the equalities the
    // bag side gets at intern time — exhaustively, so lift the match
    // budgets that throttle exactly this workload in production.
    const stats = try tree.saturate(&AC_RULES, .{
        .max_iterations = 64,
        .max_nodes = 100_000,
        .ac_match_budget = std.math.maxInt(usize),
        .ac_iter_match_budget = std.math.maxInt(usize),
    });
    try testing.expectEqual(SaturateOutcome.saturated, stats.outcome);

    try testing.expectEqual(tree_classes.items.len, bag_classes.items.len);
    for (tree_classes.items, bag_classes.items, 0..) |ta, ba, i| {
        for (
            tree_classes.items[i + 1 ..],
            bag_classes.items[i + 1 ..],
        ) |tb, bb| {
            try testing.expectEqual(
                tree.sameClass(ta, tb),
                bagged.sameClass(ba, bb),
            );
        }
    }
}

test "bag matching applies idempotence with extension semantics" {
    var arena_state = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena_state.deinit();
    var eg = EGraph.init(arena_state.allocator());
    try eg.congr_heads.put(eg.allocator, ADD, {});
    try eg.ac_heads.put(eg.allocator, ADD, {});

    // add(a, a) ~ a over bag {x, x, y}: the redex is a sub-multiset; the
    // leftover member rejoins the contracted target.
    const idem = [_]Rule{.{
        .rule_id = 102,
        .reversed = false,
        .match_side = app2(ADD, BINDER_A, BINDER_A),
        .target_side = BINDER_A,
        .num_binders = 1,
    }};

    const x = try eg.add(.{ .leaf = 1 });
    const y = try eg.add(.{ .leaf = 2 });
    const inner = try testAdd2(&eg, ADD, .{ .class = x }, .{ .class = y });
    const xxy = try testAdd2(&eg, ADD, .{ .class = x }, .{ .class = inner });
    const xy = try testAdd2(&eg, ADD, .{ .class = x }, .{ .class = y });
    try testing.expect(!eg.sameClass(xxy, xy));

    const stats = try eg.saturate(&idem, .{});
    try testing.expectEqual(SaturateOutcome.saturated, stats.outcome);
    try testing.expect(eg.sameClass(xxy, xy));
    try testing.expect(!eg.sameClass(xy, x));
    try testing.expect(!eg.sameClass(xy, y));
}

test "bag absorption saturates instead of minting to the cap" {
    var arena_state = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena_state.deinit();
    var eg = EGraph.init(arena_state.allocator());
    try eg.congr_heads.put(eg.allocator, ADD, {});
    try eg.congr_heads.put(eg.allocator, F, {});
    try eg.ac_heads.put(eg.allocator, ADD, {});
    try eg.ac_heads.put(eg.allocator, F, {});

    // Absorption or(a, an(a, b)) ~ a (ADD as or, F as an) unions p with a
    // compound containing p's class. In tree representation comm/assoc
    // then mint fresh nodes from the cyclic class up to any cap; the bag
    // cycle guard keeps the class atomic inside its own bag instead.
    const absorb = [_]Rule{.{
        .rule_id = 106,
        .reversed = false,
        .match_side = app2(ADD, BINDER_A, app2(F, BINDER_A, BINDER_B)),
        .target_side = BINDER_A,
        .num_binders = 2,
    }};

    const p = try eg.add(.{ .leaf = 1 });
    const q = try eg.add(.{ .leaf = 2 });
    const an_pq = try testAdd2(&eg, F, .{ .class = p }, .{ .class = q });
    const or_p = try testAdd2(&eg, ADD, .{ .class = p }, .{ .class = an_pq });

    const stats = try eg.saturate(&absorb, .{});
    try testing.expectEqual(SaturateOutcome.saturated, stats.outcome);
    try testing.expect(eg.sameClass(or_p, p));
    try testing.expect(eg.eNodeCount() < 10);
    // The guard forfeits merges, so the honesty stat must record it: a
    // saturated miss here is not a forced negative.
    try testing.expect(stats.ac_cyclic_dropped != 0);
}

test "bag matching binds a residual binder to a materialized sub-bag" {
    var arena_state = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena_state.deinit();
    var eg = EGraph.init(arena_state.allocator());
    try eg.congr_heads.put(eg.allocator, ADD, {});
    try eg.congr_heads.put(eg.allocator, F, {});
    try eg.ac_heads.put(eg.allocator, ADD, {});

    // add(a, b) ~ f(a, b) over bag {x, y, z}: in tree land the rule hits
    // add(x, add(y, z)), so `b` must be able to bind the {y, z} sub-bag.
    const fold = [_]Rule{.{
        .rule_id = 107,
        .reversed = false,
        .match_side = app2(ADD, BINDER_A, BINDER_B),
        .target_side = app2(F, BINDER_A, BINDER_B),
        .num_binders = 2,
    }};

    const x = try eg.add(.{ .leaf = 1 });
    const y = try eg.add(.{ .leaf = 2 });
    const z = try eg.add(.{ .leaf = 3 });
    const yz = try testAdd2(&eg, ADD, .{ .class = y }, .{ .class = z });
    const xyz = try testAdd2(&eg, ADD, .{ .class = x }, .{ .class = yz });

    // One iteration is enough for the root-level fold (the rule is
    // generative under further iterations, which is not under test).
    _ = try eg.saturate(&fold, .{ .max_iterations = 1 });
    const f_x_yz = try testAdd2(&eg, F, .{ .class = x }, .{ .class = yz });
    try testing.expect(eg.sameClass(xyz, f_x_yz));
}

/// Build a policied binary application the way the driver's seed
/// translation does: the node interns as a bag; the term's children are
/// the flattened members sorted by class root (mirroring the node).
fn tAc2(
    eg: *EGraph,
    term_id: u32,
    a: *const Term,
    b: *const Term,
) !*const Term {
    const shape = ENode{ .app = .{ .term_id = term_id, .children = &.{
        .{ .class = termClassOf(eg, a) },
        .{ .class = termClassOf(eg, b) },
    } } };
    _ = try eg.add(shape);
    const node = (try eg.lookupNode(shape)).?;
    var members: std.ArrayListUnmanaged(*const Term) = .{};
    try collectAcMembers(eg, term_id, a, &members);
    try collectAcMembers(eg, term_id, b, &members);
    std.mem.sort(*const Term, members.items, eg, termClassLess);
    const children = try eg.allocator.alloc(?*const Term, members.items.len);
    for (members.items, 0..) |member, idx| children[idx] = member;
    const term = try eg.allocator.create(Term);
    term.* = .{ .node = node, .children = children };
    return term;
}

fn collectAcMembers(
    eg: *EGraph,
    term_id: u32,
    term: *const Term,
    out: *std.ArrayListUnmanaged(*const Term),
) !void {
    switch (eg.nodes.items[term.node].node) {
        .bag => |bag| if (bag.term_id == term_id) {
            for (term.children) |child| {
                try collectAcMembers(eg, term_id, child.?, out);
            }
            return;
        },
        else => {},
    }
    try out.append(eg.allocator, term);
}

fn termClassLess(eg: *EGraph, a: *const Term, b: *const Term) bool {
    return termClassOf(eg, a) < termClassOf(eg, b);
}

test "bag explain: pure AC difference needs zero steps" {
    var arena_state = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena_state.deinit();
    var eg = EGraph.init(arena_state.allocator());
    try eg.congr_heads.put(eg.allocator, ADD, {});
    try eg.ac_heads.put(eg.allocator, ADD, {});

    const x = try tLeaf(&eg, 1);
    const y = try tLeaf(&eg, 2);
    const z = try tLeaf(&eg, 3);
    const from = try tAc2(&eg, ADD, try tAc2(&eg, ADD, x, y), z);
    const to = try tAc2(&eg, ADD, z, try tAc2(&eg, ADD, y, x));

    // Reassociation and permutation are one interned node: the terms are
    // already identical, so the extraction has nothing to prove — the AC
    // debt is paid at the lowering seams, not here.
    const steps = (try eg.explain(&.{}, from, to, .{})) orelse {
        return error.ExpectedExplanation;
    };
    try testing.expectEqual(@as(usize, 0), steps.len);
}

test "bag explain: idempotence step with extension replays" {
    var arena_state = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena_state.deinit();
    var eg = EGraph.init(arena_state.allocator());
    try eg.congr_heads.put(eg.allocator, ADD, {});
    try eg.ac_heads.put(eg.allocator, ADD, {});

    const idem = [_]Rule{.{
        .rule_id = 102,
        .reversed = false,
        .match_side = app2(ADD, BINDER_A, BINDER_A),
        .target_side = BINDER_A,
        .num_binders = 1,
    }};

    const x = try tLeaf(&eg, 1);
    const y = try tLeaf(&eg, 2);
    const from = try tAc2(&eg, ADD, x, try tAc2(&eg, ADD, x, y));
    const to = try tAc2(&eg, ADD, x, y);
    _ = try eg.saturate(&idem, .{});
    try testing.expect(eg.sameClass(
        termClassOf(&eg, from),
        termClassOf(&eg, to),
    ));

    const steps = (try eg.explain(&idem, from, to, .{})) orelse {
        return error.ExpectedExplanation;
    };
    try testing.expectEqual(@as(usize, 1), steps.len);
    try testing.expectEqual(@as(u32, 102), steps[0].source.rule);
    const info = steps[0].bag orelse return error.ExpectedBagInfo;
    try testing.expectEqual(@as(usize, 2), info.matched_before.len);
    try testing.expectEqual(@as(usize, 1), info.matched_after.len);
    try expectValidChain(&eg, from, to, steps);
}

test "bag explain: structured rewrite through a sub-bag pattern replays" {
    var arena_state = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena_state.deinit();
    var eg = EGraph.init(arena_state.allocator());
    try eg.congr_heads.put(eg.allocator, ADD, {});
    try eg.congr_heads.put(eg.allocator, F, {});
    try eg.ac_heads.put(eg.allocator, ADD, {});

    // Distributivity-style: f(a, add(b, c)) ~ add(f(a, b), f(a, c)); the
    // match side's add-subpattern must cover a bag member exactly, and
    // the target instantiates to a fresh bag.
    const distr = [_]Rule{.{
        .rule_id = 108,
        .reversed = false,
        .match_side = app2(F, BINDER_A, app2(ADD, BINDER_B, BINDER_C)),
        .target_side = app2(
            ADD,
            app2(F, BINDER_A, BINDER_B),
            app2(F, BINDER_A, BINDER_C),
        ),
        .num_binders = 3,
    }};

    const x = try tLeaf(&eg, 1);
    const y = try tLeaf(&eg, 2);
    const z = try tLeaf(&eg, 3);
    const yz = try tAc2(&eg, ADD, y, z);
    const fx_yz = try tApp2(&eg, F, x, yz);
    const to = try tAc2(
        &eg,
        ADD,
        try tApp2(&eg, F, x, y),
        try tApp2(&eg, F, x, z),
    );

    _ = try eg.saturate(&distr, .{ .max_iterations = 4 });
    try testing.expect(eg.sameClass(
        termClassOf(&eg, fx_yz),
        termClassOf(&eg, to),
    ));
    const steps = (try eg.explain(&distr, fx_yz, to, .{})) orelse {
        return error.ExpectedExplanation;
    };
    try expectValidChain(&eg, fx_yz, to, steps);
}

test "bag explain: absorption through a cyclic class replays" {
    var arena_state = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena_state.deinit();
    var eg = EGraph.init(arena_state.allocator());
    try eg.congr_heads.put(eg.allocator, ADD, {});
    try eg.congr_heads.put(eg.allocator, F, {});
    try eg.ac_heads.put(eg.allocator, ADD, {});
    try eg.ac_heads.put(eg.allocator, F, {});

    const absorb = [_]Rule{.{
        .rule_id = 106,
        .reversed = false,
        .match_side = app2(ADD, BINDER_A, app2(F, BINDER_A, BINDER_B)),
        .target_side = BINDER_A,
        .num_binders = 2,
    }};

    const p = try tLeaf(&eg, 1);
    const q = try tLeaf(&eg, 2);
    const an_pq = try tAc2(&eg, F, p, q);
    const or_p = try tAc2(&eg, ADD, p, an_pq);

    const stats = try eg.saturate(&absorb, .{});
    try testing.expectEqual(SaturateOutcome.saturated, stats.outcome);
    try testing.expect(eg.sameClass(
        termClassOf(&eg, or_p),
        termClassOf(&eg, p),
    ));
    const steps = (try eg.explain(&absorb, or_p, p, .{})) orelse {
        return error.ExpectedExplanation;
    };
    try expectValidChain(&eg, or_p, p, steps);
}

test "bag ladder: ten-atom AC closure is free at default caps" {
    // The AC-4 acceptance gate: the tree-representation baseline needs
    // 57,012 e-nodes for the ten-atom closure (5.7x over the default cap;
    // see docs/design_notes/ac_representation.md). With comm/assoc
    // absorbed there is nothing to saturate at all: the closure exists at
    // intern time. Incremental seeding interns each partial sum once (a
    // distinct sub-term, so a distinct e-node): n leaves plus n - 1
    // suffix sums = 2n - 1 nodes, linear where the tree is exponential.
    var arena_state = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena_state.deinit();
    var eg = EGraph.init(arena_state.allocator());
    try eg.congr_heads.put(eg.allocator, ADD, {});
    try eg.ac_heads.put(eg.allocator, ADD, {});

    const n: u32 = 10;
    _ = try seedSum(&eg, n);
    const stats = try eg.saturate(&.{}, .{});
    try testing.expectEqual(SaturateOutcome.saturated, stats.outcome);
    try testing.expectEqual(@as(usize, 0), stats.unions_applied);
    try testing.expectEqual(@as(usize, 2 * n - 1), eg.eNodeCount());

    // Every reassociation and permutation of the same sum interns to the
    // same class with zero additional work: the reversed comb adds only
    // its own n - 2 new prefix sub-sums (the full sum memo-hits), and no
    // union is ever needed.
    var reversed = try eg.add(.{ .leaf = 1 });
    var i: u32 = 2;
    while (i <= n) : (i += 1) {
        const leaf = try eg.add(.{ .leaf = i });
        reversed = try testAdd2(
            &eg,
            ADD,
            .{ .class = reversed },
            .{ .class = leaf },
        );
    }
    const original = try seedSum(&eg, n);
    try testing.expect(eg.sameClass(reversed, original));
    try testing.expectEqual(@as(usize, 3 * n - 3), eg.eNodeCount());
}

test "bag match budget trips are reported, not silent" {
    var arena_state = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena_state.deinit();
    var eg = EGraph.init(arena_state.allocator());
    try eg.congr_heads.put(eg.allocator, ADD, {});
    try eg.congr_heads.put(eg.allocator, F, {});
    try eg.ac_heads.put(eg.allocator, ADD, {});

    const fold = [_]Rule{.{
        .rule_id = 107,
        .reversed = false,
        .match_side = app2(ADD, BINDER_A, BINDER_B),
        .target_side = app2(F, BINDER_A, BINDER_B),
        .num_binders = 2,
    }};

    _ = try seedSum(&eg, 8);
    const stats = try eg.saturate(&fold, .{
        .max_iterations = 1,
        .ac_match_budget = 3,
    });
    try testing.expect(stats.ac_match_capped > 0);
}

test "tree match budget trips are reported, not silent" {
    // solvePairs walks every same-head member of each child class, so a
    // nested pattern against merge-heavy classes goes combinatorial with
    // no bag anywhere in sight (AC-style laws enrolled as plain tree
    // rewrites are the archetype). The per-(rule, node) budget must
    // charge those candidate visits too.
    const assoc = [_]Rule{.{
        .rule_id = 108,
        .reversed = false,
        .match_side = ASSOC_MATCH,
        .target_side = ASSOC_TARGET,
        .num_binders = 3,
    }};

    // add(xy, w) where xy's class also holds xz: the nested add(a, b)
    // sub-pattern has two candidate members to enumerate.
    var arena_state = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena_state.deinit();
    var eg = EGraph.init(arena_state.allocator());
    const x = try eg.add(.{ .leaf = 1 });
    const y = try eg.add(.{ .leaf = 2 });
    const z = try eg.add(.{ .leaf = 3 });
    const w = try eg.add(.{ .leaf = 4 });
    const xy = try testAdd2(&eg, ADD, .{ .class = x }, .{ .class = y });
    const xz = try testAdd2(&eg, ADD, .{ .class = x }, .{ .class = z });
    _ = try eg.merge(xy, xz, .{ .congruence = .{ .left = 0, .right = 1 } });
    _ = try testAdd2(&eg, ADD, .{ .class = xy }, .{ .class = w });
    const stats = try eg.saturate(&assoc, .{
        .max_iterations = 1,
        .ac_match_budget = 1,
    });
    // The budget admits the first candidate's solution and early-outs on
    // the second: one union lands, and the trip is reported.
    try testing.expect(stats.ac_match_capped > 0);
    try testing.expectEqual(@as(usize, 1), stats.unions_applied);

    // Sanity: the default budget enumerates both candidates.
    var eg2 = EGraph.init(arena_state.allocator());
    const x2 = try eg2.add(.{ .leaf = 1 });
    const y2 = try eg2.add(.{ .leaf = 2 });
    const z2 = try eg2.add(.{ .leaf = 3 });
    const w2 = try eg2.add(.{ .leaf = 4 });
    const xy2 = try testAdd2(&eg2, ADD, .{ .class = x2 }, .{ .class = y2 });
    const xz2 = try testAdd2(&eg2, ADD, .{ .class = x2 }, .{ .class = z2 });
    _ = try eg2.merge(xy2, xz2, .{ .congruence = .{ .left = 0, .right = 1 } });
    _ = try testAdd2(&eg2, ADD, .{ .class = xy2 }, .{ .class = w2 });
    const stats2 = try eg2.saturate(&assoc, .{ .max_iterations = 1 });
    try testing.expectEqual(@as(usize, 2), stats2.unions_applied);
    try testing.expectEqual(@as(usize, 0), stats2.ac_match_capped);
}

test "tree iteration match budget throttles and still ratchets to fixpoint" {
    // The per-iteration retained-match budget must apply to tree egraphs
    // too (it was bag-gated once): capped collection stops the flood, and
    // because applied effects are deduped free, later iterations spend
    // their budget on fresh unions until genuine saturation.
    const comm = [_]Rule{.{
        .rule_id = 109,
        .reversed = false,
        .match_side = COMM_MATCH,
        .target_side = COMM_TARGET,
        .num_binders = 2,
    }};

    var arena_state = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena_state.deinit();
    var eg = EGraph.init(arena_state.allocator());
    const a = try eg.add(.{ .leaf = 1 });
    const b = try eg.add(.{ .leaf = 2 });
    const c = try eg.add(.{ .leaf = 3 });
    const d = try eg.add(.{ .leaf = 4 });
    const ab = try testAdd2(&eg, ADD, .{ .class = a }, .{ .class = b });
    const cd = try testAdd2(&eg, ADD, .{ .class = c }, .{ .class = d });
    const stats = try eg.saturate(&comm, .{ .ac_iter_match_budget = 1 });
    try testing.expectEqual(SaturateOutcome.saturated, stats.outcome);
    try testing.expect(stats.ac_match_capped > 0);
    const ba = try testAdd2(&eg, ADD, .{ .class = b }, .{ .class = a });
    const dc = try testAdd2(&eg, ADD, .{ .class = d }, .{ .class = c });
    try testing.expect(eg.sameClass(ab, ba));
    try testing.expect(eg.sameClass(cd, dc));
}

test "pool-equation bag terms survive a member re-sort (regression)" {
    // A union can renumber a member's canonical root, re-sorting the
    // stored bag node's members in place. The seed-time Justification
    // terms must be re-paired at explain time, or a proven conversion
    // degrades to an unexplainable miss.
    var arena_state = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena_state.deinit();
    var eg = EGraph.init(arena_state.allocator());
    try eg.congr_heads.put(eg.allocator, ADD, {});
    try eg.congr_heads.put(eg.allocator, F, {});
    try eg.ac_heads.put(eg.allocator, ADD, {});

    const x = try tLeaf(&eg, 1);
    const y = try tLeaf(&eg, 2);
    const xy = try tAc2(&eg, ADD, x, y);
    const c = try tLeaf(&eg, 3);
    const z = try tLeaf(&eg, 4);
    // h1: (x + y) = c
    _ = try eg.merge(
        termClassOf(&eg, xy),
        termClassOf(&eg, c),
        .{ .pool_equation = .{ .pool_index = 0, .lhs = xy, .rhs = c } },
    );
    // h2: x = z  (x's root merges into z's higher root -> member re-sort)
    _ = try eg.merge(
        termClassOf(&eg, x),
        termClassOf(&eg, z),
        .{ .pool_equation = .{ .pool_index = 1, .lhs = x, .rhs = z } },
    );
    _ = try eg.saturate(&.{}, .{});

    // Goal z + y converts to c via h1 (citing h2 inside).
    const goal = try tAc2(&eg, ADD, z, y);
    const c2 = try tLeaf(&eg, 3);
    try testing.expect(eg.sameClass(
        termClassOf(&eg, goal),
        termClassOf(&eg, c2),
    ));
    const steps = (try eg.explain(&.{}, goal, c2, .{})).?;
    try testing.expect(steps.len != 0);
}

test "pool-equation bag terms explain through a splice twin" {
    // When a seeded equation side's member class later denotes a
    // same-head bag, the stored node keeps its written member count (the
    // flat view is a twin node behind a `.splice` edge), so the citation
    // re-pairs cleanly and the chain crosses the twin via an
    // `.ac_flatten` regroup step plus the member's own equation.
    var arena_state = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena_state.deinit();
    var eg = EGraph.init(arena_state.allocator());
    try eg.congr_heads.put(eg.allocator, ADD, {});
    try eg.ac_heads.put(eg.allocator, ADD, {});

    const x = try tLeaf(&eg, 1);
    const y = try tLeaf(&eg, 2);
    const c = try tLeaf(&eg, 3);
    const xy = try tAc2(&eg, ADD, x, y);
    const a = try tLeaf(&eg, 4);
    const b = try tLeaf(&eg, 5);
    const ab = try tAc2(&eg, ADD, a, b);

    // h1: (x + y) = c
    _ = try eg.merge(
        termClassOf(&eg, xy),
        termClassOf(&eg, c),
        .{ .pool_equation = .{ .pool_index = 0, .lhs = xy, .rhs = c } },
    );
    // h2: x = (a + b)  -> x's class denotes a same-head bag; the stored
    // {x, y} node splices to {a, b, y}.
    _ = try eg.merge(
        termClassOf(&eg, x),
        termClassOf(&eg, ab),
        .{ .pool_equation = .{ .pool_index = 1, .lhs = x, .rhs = ab } },
    );
    _ = try eg.saturate(&.{}, .{});

    const goal = try tAc2(&eg, ADD, a, try tAc2(&eg, ADD, b, y));
    const c2 = try tLeaf(&eg, 3);
    try testing.expect(eg.sameClass(
        termClassOf(&eg, goal),
        termClassOf(&eg, c2),
    ));
    const steps = (try eg.explain(&.{}, goal, c2, .{})) orelse {
        return error.ExpectedExplanation;
    };
    try expectValidChain(&eg, goal, c2, steps);
    // The chain must regroup {a, b, y} into {(a + b), y} before citing
    // the equations; both citations appear.
    var saw_flatten = false;
    var saw_h1 = false;
    var saw_h2 = false;
    for (steps) |step| switch (step.source) {
        .ac_flatten => saw_flatten = true,
        .pool_equation => |pool_idx| {
            if (pool_idx == 0) saw_h1 = true;
            if (pool_idx == 1) saw_h2 = true;
        },
        .rule => {},
    };
    try testing.expect(saw_flatten);
    try testing.expect(saw_h1);
    try testing.expect(saw_h2);
}

// --- alpha scheduler ------------------------------------------------------

const SB: u32 = 40;

fn app3(
    comptime term_id: u32,
    comptime a: TemplateExpr,
    comptime b: TemplateExpr,
    comptime c: TemplateExpr,
) TemplateExpr {
    return .{ .app = .{ .term_id = term_id, .args = &.{ a, b, c } } };
}

// rel(ALL x p, ALL y (SB x y p)) with binder 0 = x (bound), 1 = p,
// 2 = y (bound, target-only). Restriction: y must avoid p (the capture
// side condition, derived from p's absent y-dep at enrollment).
const ALPHA_RULE = Rule{
    .rule_id = 0,
    .reversed = false,
    .match_side = app2(ALL, BINDER_A, BINDER_B),
    .target_side = app2(ALL, BINDER_C, app3(SB, BINDER_A, BINDER_C, BINDER_B)),
    .num_binders = 3,
    .bound_slots = &.{ 0, 2 },
    .restrictions = &.{.{ .bound_slot = 2, .term_slot = 1 }},
    .alpha = true,
    .alpha_old_slot = 0,
    .alpha_new_slot = 2,
};

// rel(SB x a (F x), F a): reduces the substitution image the alpha fire
// mints. Binder 0 = x (bound), 1 = a.
const SB_F_RULE = Rule{
    .rule_id = 1,
    .reversed = false,
    .match_side = app3(SB, BINDER_A, BINDER_B, .{ .app = .{
        .term_id = F,
        .args = &.{BINDER_A},
    } }),
    .target_side = .{ .app = .{ .term_id = F, .args = &.{BINDER_B} } },
    .num_binders = 2,
    .bound_slots = &.{0},
};

fn alphaTestGraph(arena: std.mem.Allocator) !EGraph {
    var eg = EGraph.init(arena);
    try eg.congr_heads.put(eg.allocator, ALL, {});
    try eg.bound_masks.put(eg.allocator, ALL, 1);
    try eg.bound_masks.put(eg.allocator, SB, 1);
    return eg;
}

fn addUnary(eg: *EGraph, term_id: u32, child: Child) !EClassId {
    return eg.add(.{ .app = .{ .term_id = term_id, .children = &.{child} } });
}

test "alpha scheduler merges renamed binder instances" {
    var arena_state = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena_state.deinit();
    var eg = try alphaTestGraph(arena_state.allocator());

    const x: LeafId = 1;
    const z: LeafId = 2;
    const xl = try eg.add(.{ .leaf = x });
    const zl = try eg.add(.{ .leaf = z });
    const fx = try addUnary(&eg, F, .{ .class = xl });
    const fz = try addUnary(&eg, F, .{ .class = zl });
    const all_x = try testAdd2(&eg, ALL, .{ .bound = x }, .{ .class = fx });
    const all_z = try testAdd2(&eg, ALL, .{ .bound = z }, .{ .class = fz });
    try testing.expect(!eg.sameClass(all_x, all_z));

    const rules = [_]Rule{ ALPHA_RULE, SB_F_RULE };
    const stats = try eg.saturate(&rules, .{});
    try testing.expectEqual(SaturateOutcome.saturated, stats.outcome);
    try testing.expect(stats.alpha_applied >= 1);
    try testing.expect(eg.sameClass(all_x, all_z));
}

test "alpha scheduler never merges a capturing rename" {
    var arena_state = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena_state.deinit();
    var eg = try alphaTestGraph(arena_state.allocator());

    // ALL x (add x c) vs ALL c (add c c): renaming x -> c captures the
    // free c, so the dep gate refuses that direction. The reverse fire
    // (c -> x) is sound but mints ALL x ([c/x](add c c)), whose body is
    // (add x x) once reduced — a different formula. Either way the two
    // seeded instances must stay separate.
    const x: LeafId = 1;
    const c: LeafId = 2;
    const xl = try eg.add(.{ .leaf = x });
    const cl = try eg.add(.{ .leaf = c });
    const add_xc = try testAdd2(&eg, ADD, .{ .class = xl }, .{ .class = cl });
    const add_cc = try testAdd2(&eg, ADD, .{ .class = cl }, .{ .class = cl });
    const all_x = try testAdd2(&eg, ALL, .{ .bound = x }, .{ .class = add_xc });
    const all_c = try testAdd2(&eg, ALL, .{ .bound = c }, .{ .class = add_cc });

    const rules = [_]Rule{ ALPHA_RULE, SB_F_RULE };
    const stats = try eg.saturate(&rules, .{});
    _ = stats;
    try testing.expect(!eg.sameClass(all_x, all_c));
}

// rel(SB x a (ADD p q), ADD (SB x a p) (SB x a q)): distributes the
// substitution image through ADD so a fired rename over an ADD body can
// reduce to its partner. Binder 0 = x (bound), 1 = a, 2/3 = the operands.
const SB_ADD_RULE = Rule{
    .rule_id = 2,
    .reversed = false,
    .match_side = app3(SB, BINDER_A, BINDER_B, app2(ADD, BINDER_C, .{
        .binder = 3,
    })),
    .target_side = app2(
        ADD,
        app3(SB, BINDER_A, BINDER_B, BINDER_C),
        app3(SB, BINDER_A, BINDER_B, .{ .binder = 3 }),
    ),
    .num_binders = 4,
    .bound_slots = &.{0},
};

test "alpha rename memo is atom-sensitive (decoy pair cannot poison a later valid pair)" {
    var arena_state = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena_state.deinit();
    var eg = try alphaTestGraph(arena_state.allocator());
    try eg.congr_heads.put(eg.allocator, ADD, {});

    // The decoy ALL y (add (F w) (F x)) is inserted FIRST, so the pair
    // (decoy, ALL w (add (F w) (F w))) is compared before the valid
    // pair. Walking the decoy pair's second operand compares body
    // classes (F x, F w) under y -> w — false. The valid pair
    // (ALL x (add (F x) (F x)), ALL w (add (F w) (F w))) then compares
    // the SAME class pair under x -> w, which is true; an atom-blind
    // memo key inherited the decoy's false verdict and silently killed
    // the fire. The decoy corresponds with neither instance (its free
    // x resp. free w blocks every rename), so no alternate route can
    // mask the miss.
    const x: LeafId = 1;
    const y: LeafId = 2;
    const w: LeafId = 3;
    const xl = try eg.add(.{ .leaf = x });
    const wl = try eg.add(.{ .leaf = w });
    const fx = try addUnary(&eg, F, .{ .class = xl });
    const fw = try addUnary(&eg, F, .{ .class = wl });
    const decoy_body =
        try testAdd2(&eg, ADD, .{ .class = fw }, .{ .class = fx });
    const body_x =
        try testAdd2(&eg, ADD, .{ .class = fx }, .{ .class = fx });
    const body_w =
        try testAdd2(&eg, ADD, .{ .class = fw }, .{ .class = fw });
    const decoy =
        try testAdd2(&eg, ALL, .{ .bound = y }, .{ .class = decoy_body });
    const all_x =
        try testAdd2(&eg, ALL, .{ .bound = x }, .{ .class = body_x });
    const all_w =
        try testAdd2(&eg, ALL, .{ .bound = w }, .{ .class = body_w });

    const rules = [_]Rule{ ALPHA_RULE, SB_F_RULE, SB_ADD_RULE };
    const stats = try eg.saturate(&rules, .{});
    try testing.expectEqual(SaturateOutcome.saturated, stats.outcome);
    try testing.expect(eg.sameClass(all_x, all_w));
    try testing.expect(!eg.sameClass(decoy, all_x));
    try testing.expect(!eg.sameClass(decoy, all_w));
}
