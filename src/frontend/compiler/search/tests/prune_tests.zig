const helpers = @import("./helpers.zig");
const std = helpers.std;
const types = helpers.types;
const fixture_mod = helpers.fixture_mod;
const semantic = helpers.semantic;
const acui = helpers.acui;
const def_match = helpers.def_match;
const MetaStore = helpers.MetaStore;
const TemplateExpr = helpers.TemplateExpr;
const ExprId = helpers.ExprId;
const TheoremContext = helpers.TheoremContext;
const ProofScript = helpers.ProofScript;
const CompilerContext = helpers.CompilerContext;
const Check = helpers.Check;
const DiagnosticSink = helpers.DiagnosticSink;
const Goal = helpers.Goal;
const Context = helpers.Context;
const NameExprMap = helpers.NameExprMap;
const apply = helpers.apply;
const fixtureFor = helpers.fixtureFor;
const ruleArgIndex = helpers.ruleArgIndex;
const parseGoal = helpers.parseGoal;
const readProofCase = helpers.readProofCase;
const ContextHarness = helpers.ContextHarness;
const expectCaseLineSearch = helpers.expectCaseLineSearch;
const expectApplyContains = helpers.expectApplyContains;
const suggestionsAtNeedle = helpers.suggestionsAtNeedle;
const expectOffered = helpers.expectOffered;
const expectOffers = helpers.expectOffers;

// An ordered (associative, unit, not commutative, not idempotent) context
// theory in the martin_lof style, shared by the multiplicity and dependency
// prune tests below.
const ordered_ctx_theory =
    \\delimiter $ ( ) $;
    \\provable sort wff;
    \\sort ctx;
    \\sort tm;
    \\sort ty;
    \\term iff (a b: wff): wff;
    \\infixr iff: $<->$ prec 20;
    \\term ctx_eq (g h: ctx): wff;
    \\term emp: ctx;
    \\--| @acui ctx_assoc _ emp _
    \\term join (g h: ctx): ctx;
    \\term hyp (a: wff): ctx;
    \\term nd (g: ctx) (a: wff): wff;
    \\term has (t: tm) (A: ty): wff;
    \\term Nat: ty;
    \\term suc (n: tm): tm;
    \\def cst (n: tm) (A: ty): ty = $ A $;
    \\
    \\--| @relation wff iff iff_refl iff_trans iff_sym iff_mp
    \\axiom iff_refl (a: wff): $ a <-> a $;
    \\axiom iff_trans (a b c: wff):
    \\  $ a <-> b $ > $ b <-> c $ > $ a <-> c $;
    \\axiom iff_sym (a b: wff): $ a <-> b $ > $ b <-> a $;
    \\axiom iff_mp (a b: wff): $ a <-> b $ > $ a $ > $ b $;
    \\
    \\--| @relation ctx ctx_eq ctx_refl ctx_trans ctx_sym _
    \\axiom ctx_refl (g: ctx): $ ctx_eq g g $;
    \\axiom ctx_trans (g h i: ctx):
    \\  $ ctx_eq g h $ > $ ctx_eq h i $ > $ ctx_eq g i $;
    \\axiom ctx_sym (g h: ctx): $ ctx_eq g h $ > $ ctx_eq h g $;
    \\axiom ctx_assoc (g h i: ctx):
    \\  $ ctx_eq (join (join g h) i) (join g (join h i)) $;
    \\axiom ctx_unit (g: ctx): $ ctx_eq (join emp g) g $;
    \\
;

/// `src` with its one occurrence of `old` replaced by `new`.
fn replaceOnce(
    comptime src: []const u8,
    comptime old: []const u8,
    comptime new: []const u8,
) []const u8 {
    const at = std.mem.indexOf(u8, src, old) orelse @compileError("missing: " ++ old);
    return src[0..at] ++ new ++ src[at + old.len ..];
}

/// A theory with one `@rewrite` head, a substitution: `sb x u t` reduces to
/// `t` when `t` avoids `x`.
const redex_theory =
    \\delimiter $ ( ) $;
    \\provable sort wff;
    \\sort tm;
    \\term iff (a b: wff): wff;
    \\term teq (s t: tm): wff;
    \\term pr (t: tm): wff;
    \\term lam {x: tm} (t: tm x): tm;
    \\term sb {x: tm} (u: tm) (t: tm x): tm;
    \\term z: tm;
    \\term o: tm;
    \\--| @relation wff iff iff_refl iff_trans iff_sym iff_mp
    \\axiom iff_refl (a: wff): $ iff a a $;
    \\axiom iff_trans (a b c: wff): $ iff a b $ > $ iff b c $ > $ iff a c $;
    \\axiom iff_sym (a b: wff): $ iff a b $ > $ iff b a $;
    \\axiom iff_mp (a b: wff): $ iff a b $ > $ a $ > $ b $;
    \\--| @relation tm teq teq_refl teq_trans teq_sym _
    \\axiom teq_refl (s: tm): $ teq s s $;
    \\axiom teq_trans (s t u: tm): $ teq s t $ > $ teq t u $ > $ teq s u $;
    \\axiom teq_sym (s t: tm): $ teq s t $ > $ teq t s $;
    \\--| @congr
    \\axiom pr_congr (s t: tm): $ teq s t $ > $ iff (pr s) (pr t) $;
    \\--| @rewrite
    \\axiom sb_free {x: tm} (u: tm x) (t: tm): $ teq (sb x u t) t $;
    \\axiom sub {x: tm} (t: tm x) (u: tm):
    \\  $ pr (lam x t) $ > $ pr u $ > $ pr (sb x u t) $;
;

test "redex conclusion prune keeps a ref whose redex reduces to the goal" {
    // Here the ref gives `t := o`, and `sb y z o` reduces to the goal.
    const mm0_src = redex_theory ++
        \\theorem t {y: tm}: $ pr (lam y o) $ > $ pr z $ > $ pr o $;
    ;
    const proof_src =
        \\t
        \\------
        \\l1: $ pr o $ by exact?
    ;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var suggestions = try suggestionsAtNeedle(
        &arena,
        mm0_src,
        proof_src,
        "exact?",
        .{},
    );
    defer suggestions.deinit();
    try expectOffered(suggestions.items, &.{"sub [#1, #2]"});
}

// Abstentions of the multiplicity matching (`acuiRequiredMembersPlausible`). Each
// runs `weaken2` against a context that shows one entry after `g`, which the
// ordered theory prunes (see "counts distinct members" above), in a setting
// where the entry count is not fixed.

const weaken2_rule =
    \\axiom weaken2 (g: ctx) {x y: tm} (T U: ty) (J: wff):
    \\  $ nd g J $ > $ nd (join (join g (hyp (has x T))) (hyp (has y U))) J $;
    \\
;

/// `ordered_ctx_theory` with a commutative context combiner and a negation
/// def.
const comm_ctx_theory = replaceOnce(
    ordered_ctx_theory,
    "@acui ctx_assoc _ emp _",
    "@acui ctx_assoc ctx_comm emp _",
) ++
    \\axiom ctx_comm (g h: ctx): $ ctx_eq (join g h) (join h g) $;
    \\term imp (a b: wff): wff;
    \\term bot: wff;
    \\def not (a: wff): wff = $ imp a bot $;
    \\
;

/// A commutative ring's signature: `add` and `mul` are `@acui` with rigid
/// units, `neg` and `inv` are rigid, and `div` and `nil` are defs over them.
const ring_theory =
    \\delimiter $ ( ) $;
    \\provable sort wff;
    \\sort R;
    \\term eq (a b: R): wff;
    \\term zero: R;
    \\term one: R;
    \\--| @acui add_assoc add_comm zero _
    \\term add (a b: R): R;
    \\--| @acui mul_assoc mul_comm one _
    \\term mul (a b: R): R;
    \\term neg (a: R): R;
    \\term inv (a: R): R;
    \\def div (a b: R): R = $ mul a (inv b) $;
    \\def nil: R = $ zero $;
    \\
    \\--| @relation R eq eq_refl eq_trans eq_symm _
    \\axiom eq_refl (a: R): $ eq a a $;
    \\axiom eq_trans (a b c: R): $ eq a b $ > $ eq b c $ > $ eq a c $;
    \\axiom eq_symm (a b: R): $ eq a b $ > $ eq b a $;
    \\axiom add_assoc (a b c: R): $ eq (add (add a b) c) (add a (add b c)) $;
    \\axiom add_comm (a b: R): $ eq (add a b) (add b a) $;
    \\axiom mul_assoc (a b c: R): $ eq (mul (mul a b) c) (mul a (mul b c)) $;
    \\axiom mul_comm (a b: R): $ eq (mul a b) (mul b a) $;
    \\axiom add_congr (a b c d: R): $ eq a b $ > $ eq c d $ > $ eq (add a c) (add b d) $;
    \\theorem t (x y z: R): $ eq x y $;
    \\
;

/// `ring_theory` with an idempotent `add`.
const idempotent_ring_theory = replaceOnce(
    ring_theory,
    "@acui add_assoc add_comm zero _",
    "@acui add_assoc add_comm zero add_idem",
) ++
    \\axiom add_idem (a: R): $ eq (add a a) a $;
    \\
;

/// A `head_class.Screen` over theorem `t` of `mm0_src`, with its terms parsed
/// as the left side of an `eq`.
const ScreenCase = struct {
    arena: std.heap.ArenaAllocator,
    fixture: fixture_mod.Fixture,
    theorem: TheoremContext,
    theorem_vars: NameExprMap,
    harness: ContextHarness,

    fn init(case: *ScreenCase, mm0_src: []const u8) !void {
        case.arena = std.heap.ArenaAllocator.init(std.testing.allocator);
        const allocator = case.arena.allocator();
        case.fixture = try fixtureFor(allocator, mm0_src, "t");
        case.theorem = TheoremContext.init(allocator);
        try case.theorem.seedAssertion(case.fixture.assertion);
        case.theorem_vars = try Check.buildTheoremVarMap(allocator, case.fixture.assertion);
        case.harness = ContextHarness.init(allocator);
    }

    fn deinit(case: *ScreenCase) void {
        case.harness.deinit();
        case.theorem_vars.deinit();
        case.theorem.deinit();
        case.arena.deinit();
    }

    fn expr(case: *ScreenCase, text: []const u8) !ExprId {
        var buf: [256]u8 = undefined;
        const wrapped = try std.fmt.bufPrint(&buf, "eq ({s}) ({s})", .{ text, text });
        const goal = (try parseGoal(&case.fixture, &case.theorem, &case.theorem_vars, wrapped)).concrete;
        return case.theorem.interner.node(goal).app.args[0];
    }

    fn term(case: *ScreenCase, name: []const u8) !u32 {
        return case.fixture.theory.env.term_names.get(name) orelse error.MissingTerm;
    }

    fn screen(case: *ScreenCase, context: *const Context) helpers.head_class.Screen {
        return .init(context.env, context.registry, &case.theorem, context.allocator);
    }

    fn combiner(case: *ScreenCase, name: []const u8) !helpers.AcuiBag.Combiner {
        const env = &case.fixture.theory.env;
        return helpers.AcuiBag.Combiner.of(&case.fixture.theory.registry, env, try case.term(name)) orelse
            error.MissingCombiner;
    }
};

test "screen counts a def chain's shared argument once per term" {
    // `dbl^40 y` holds 2^40 members; each level is counted once.
    var case: ScreenCase = undefined;
    try case.init(comptime replaceOnce(
        ring_theory,
        "def nil: R = $ zero $;",
        "def nil: R = $ zero $;\ndef dbl (a: R): R = $ add a a $;",
    ));
    defer case.deinit();
    const context = case.harness.context(&case.fixture);
    const dbl = try case.term("dbl");
    var chain = try case.expr("y");
    for (0..40) |_| chain = try case.theorem.interner.internApp(dbl, &.{chain});
    var screen = case.screen(&context);
    defer screen.deinit();
    try std.testing.expectEqual(@as(u64, 1) << 40, screen.minMembers(try case.combiner("add"), chain));
}

test "screen reads a deep alternating lattice once per term" {
    // `J_{i+1} = J_i * y + z` under an idempotent `+`: every level keeps
    // its head, and each is read once (unshared, 15 levels cost 4^15).
    var case: ScreenCase = undefined;
    try case.init(idempotent_ring_theory);
    defer case.deinit();
    const context = case.harness.context(&case.fixture);
    const add = try case.term("add");
    const mul = try case.term("mul");
    const y = try case.expr("y");
    const z = try case.expr("z");
    var lattice = try case.expr("x");
    for (0..15) |_| {
        const product = try case.theorem.interner.internApp(mul, &.{ lattice, y });
        lattice = try case.theorem.interner.internApp(add, &.{ product, z });
    }
    var screen = case.screen(&context);
    defer screen.deinit();
    try std.testing.expectEqual(@as(?u32, add), screen.stableHead(lattice));
}

test "screen finds two differing idempotent members in any order" {
    // `- (y * 1)` may be `- x` or `- z`, but those two differ, so the sum
    // keeps its head whichever member comes first.
    var case: ScreenCase = undefined;
    try case.init(idempotent_ring_theory);
    defer case.deinit();
    const context = case.harness.context(&case.fixture);
    const add = try case.term("add");
    for ([_][]const u8{
        "add (neg (mul y one)) (add (neg x) (neg z))",
        "add (neg x) (add (neg (mul y one)) (neg z))",
    }) |text| {
        var screen = case.screen(&context);
        defer screen.deinit();
        try std.testing.expectEqual(@as(?u32, add), screen.stableHead(try case.expr(text)));
    }
}

// The dependency prune's exemption (`ruleMayRechooseBound`): the pruned
// `weaken` instance above, on rules whose bound binder a view, `@fresh`, or
// `@freshen` may re-choose after the conclusion match.

/// Heads of each class: primitive, defs with bodies that keep, drop or
/// move an argument, `@rewrite` and ACUI heads, and an opaque def.
const head_class_mm0 =
    \\delimiter $ ( ) $;
    \\provable sort wff;
    \\sort obj;
    \\sort ctx;
    \\term oeq (a b: obj): wff;
    \\term ctx_eq (g h: ctx): wff;
    \\term f (a b: obj): obj;
    \\term rw (a b: obj): obj;
    \\term emp: ctx;
    \\--| @acui ctx_assoc _ emp _
    \\term join (g h: ctx): ctx;
    \\term pt (a: obj): ctx;
    \\--| @relation obj oeq oeq_refl oeq_trans oeq_sym _
    \\axiom oeq_refl (a: obj): $ oeq a a $;
    \\axiom oeq_trans (a b c: obj): $ oeq a b $ > $ oeq b c $ > $ oeq a c $;
    \\axiom oeq_sym (a b: obj): $ oeq a b $ > $ oeq b a $;
    \\--| @relation ctx ctx_eq ctx_refl ctx_trans ctx_sym _
    \\axiom ctx_refl (g: ctx): $ ctx_eq g g $;
    \\axiom ctx_trans (g h i: ctx):
    \\  $ ctx_eq g h $ > $ ctx_eq h i $ > $ ctx_eq g i $;
    \\axiom ctx_sym (g h: ctx): $ ctx_eq g h $ > $ ctx_eq h g $;
    \\axiom ctx_assoc (g h i: ctx):
    \\  $ ctx_eq (join (join g h) i) (join g (join h i)) $;
    \\axiom ctx_unit (g: ctx): $ ctx_eq (join emp g) g $;
    \\--| @rewrite
    \\axiom rw_red (a b: obj): $ oeq (rw a b) a $;
    \\
    \\def cst (a b: obj): obj = $ a $;
    \\def swp (a b: obj): obj = $ cst b a $;
    \\def wrap (a b: obj): obj = $ f (cst a b) b $;
    \\def via_rw (a b: obj): obj = $ rw a b $;
    \\def in_ctx (a b: obj): ctx = $ join (pt a) (pt b) $;
    \\def opaque (a: obj): obj;
    \\theorem t (a: obj): $ oeq a a $;
;

test "argDetermined reads def bodies, @rewrite and ACUI heads, and bad ids" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var fixture = try fixtureFor(arena.allocator(), head_class_mm0, "t");
    var harness = ContextHarness.init(arena.allocator());
    defer harness.deinit();
    const context = harness.context(&fixture);

    const Row = struct { head: []const u8, determined: []const bool };
    const rows = [_]Row{
        // A primitive head forces every argument.
        .{ .head = "f", .determined = &.{ true, true } },
        // `cst` drops `b`: `cst a t` and `cst a t'` are equal.
        .{ .head = "cst", .determined = &.{ true, false } },
        // Nested: `swp`'s `a` lands in `cst`'s dropped slot.
        .{ .head = "swp", .determined = &.{ false, true } },
        // `wrap`'s `b` is also in `cst`'s dropped slot, but one forced
        // path is enough.
        .{ .head = "wrap", .determined = &.{ true, true } },
        // Under a `@rewrite` head or an ACUI combiner nothing is forced,
        // directly or through a def body.
        .{ .head = "rw", .determined = &.{ false, false } },
        .{ .head = "via_rw", .determined = &.{ false, false } },
        .{ .head = "join", .determined = &.{ false, false } },
        .{ .head = "in_ctx", .determined = &.{ false, false } },
        // A def without a body is opaque, so rigid.
        .{ .head = "opaque", .determined = &.{true} },
    };
    for (rows) |row| {
        const head = fixture.theory.env.term_names.get(row.head) orelse return error.MissingTerm;
        for (row.determined, 0..) |expected, i| {
            std.testing.expectEqual(expected, semantic.argDetermined(&context, head, i)) catch |err| {
                std.debug.print("argDetermined({s}, {d})\n", .{ row.head, i });
                return err;
            };
        }
    }

    // An argument index past a def's parameters.
    const cst = fixture.theory.env.term_names.get("cst") orelse return error.MissingTerm;
    try std.testing.expect(!semantic.argDetermined(&context, cst, 2));
    // A term id past the table, and a term recovery has discarded.
    const len: u32 = @intCast(fixture.theory.env.terms.items.len);
    try std.testing.expect(!semantic.argDetermined(&context, len, 0));
    const f = fixture.theory.env.term_names.get("f") orelse return error.MissingTerm;
    fixture.theory.env.terms.items[f].available = false;
    try std.testing.expect(!semantic.argDetermined(&context, f, 0));
}

test "rigid heads differ only where both unfold to a rigid head" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var fixture = try fixtureFor(arena.allocator(), head_class_mm0, "t");
    var harness = ContextHarness.init(arena.allocator());
    defer harness.deinit();
    const context = harness.context(&fixture);

    const Row = struct { lhs: []const u8, rhs: []const u8, differ: bool };
    const rows = [_]Row{
        .{ .lhs = "f", .rhs = "opaque", .differ = true },
        .{ .lhs = "f", .rhs = "f", .differ = false },
        // `wrap` unfolds to `f`.
        .{ .lhs = "wrap", .rhs = "f", .differ = false },
        .{ .lhs = "wrap", .rhs = "opaque", .differ = true },
        // The rest abstain: `cst` and `swp` unfold to an argument, and
        // `@rewrite` and ACUI heads, directly or under a def, can change.
        .{ .lhs = "cst", .rhs = "f", .differ = false },
        .{ .lhs = "swp", .rhs = "opaque", .differ = false },
        .{ .lhs = "rw", .rhs = "f", .differ = false },
        .{ .lhs = "f", .rhs = "via_rw", .differ = false },
        .{ .lhs = "join", .rhs = "pt", .differ = false },
        .{ .lhs = "pt", .rhs = "in_ctx", .differ = false },
    };
    const names = fixture.theory.env.term_names;
    for (rows) |row| {
        const lhs = names.get(row.lhs) orelse return error.MissingTerm;
        const rhs = names.get(row.rhs) orelse return error.MissingTerm;
        std.testing.expectEqual(row.differ, semantic.rigidHeadsDiffer(&context, lhs, rhs)) catch |err| {
            std.debug.print("rigidHeadsDiffer({s}, {s})\n", .{ row.lhs, row.rhs });
            return err;
        };
    }

    // A term recovery has discarded shows no head.
    const f = names.get("f") orelse return error.MissingTerm;
    const opaque_def = names.get("opaque") orelse return error.MissingTerm;
    fixture.theory.env.terms.items[f].available = false;
    try std.testing.expect(!semantic.rigidHeadsDiffer(&context, f, opaque_def));
}

const lw_rules =
    \\axiom ctx_idem (g: ctx): $ ctx_eq (join g g) g $;
    \\term A: wff;
    \\term B: wff;
    \\axiom lw (g: ctx) (a J: wff): $ nd (join g (hyp a)) J $ > $ nd g J $;
    \\theorem t: $ nd (join (hyp A) (hyp B)) bot $;
    \\theorem t_copies: $ nd (join (hyp A) (hyp A)) bot $;
;
const lw_multiset_theory = comm_ctx_theory ++ lw_rules;
const lw_set_theory = replaceOnce(
    comm_ctx_theory,
    "@acui ctx_assoc ctx_comm emp _",
    "@acui ctx_assoc ctx_comm emp ctx_idem",
) ++ lw_rules;

/// `a` of `lw`'s premise `g , hyp a ⊢ J` as `extractHypPartialBindings`
/// reads it off theorem `name`'s conclusion, with `g` bound to the first
/// member when `bind_g`, under a commutative context combiner that is
/// idempotent or not.
fn extractedLeaf(idempotent: bool, name: []const u8, bind_g: bool) !?[]const u8 {
    const mm0_src = if (idempotent) lw_set_theory else lw_multiset_theory;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    var fixture = try fixtureFor(allocator, mm0_src, name);
    var theorem = TheoremContext.init(allocator);
    defer theorem.deinit();
    try theorem.seedAssertion(fixture.assertion);
    var harness = ContextHarness.init(allocator);
    defer harness.deinit();
    const context = harness.context(&fixture);
    const rule_id = fixture.theory.env.getRuleId("lw") orelse return error.MissingRule;
    const rule = &fixture.theory.env.rules.items[rule_id];
    const ref = try theorem.internParsedExpr(fixture.assertion.concl);
    const ctx = theorem.interner.node(ref).app.args[0];
    const bindings = try allocator.alloc(?ExprId, rule.args.len);
    @memset(bindings, null);
    if (bind_g) bindings[try ruleArgIndex(rule, "g")] = theorem.interner.node(ctx).app.args[0];
    def_match.extractHypPartialBindings(&context, &theorem, rule.hyps[0], ref, bindings);
    const a = bindings[try ruleArgIndex(rule, "a")] orelse return null;
    const a_id = theorem.interner.node(a).app.term_id;
    return fixture.theory.env.terms.items[a_id].name;
}

test "extractHypPartialBindings pins a leaf by elimination only without idempotence" {
    // `g` claims `hyp A`, leaving `hyp B` as the only member for `hyp a`.
    try std.testing.expectEqualStrings("B", (try extractedLeaf(false, "t", true)).?);
    // Under `g , g = g`, `hyp a` may repeat `hyp A` as well: nothing is forced.
    try std.testing.expectEqual(@as(?[]const u8, null), try extractedLeaf(true, "t", true));
}

test "extractHypPartialBindings pins a leaf from copies of one member" {
    // Two copies of `hyp A` are one choice for `hyp a`, with or without
    // idempotence; two different members still compete.
    for ([_]bool{ false, true }) |idempotent| {
        try std.testing.expectEqualStrings("A", (try extractedLeaf(idempotent, "t_copies", false)).?);
        try std.testing.expectEqual(@as(?[]const u8, null), try extractedLeaf(idempotent, "t", false));
    }
}

test "extractHypPartialBindings aligns an ordered context entry by entry" {
    // `lam_i`'s premise context `g , x : A` against the right-nested
    // `G , (k : Nat , m : Nat)`: aligning the flattened entry sequences pins
    // `g := G , k : Nat` and `x : A := m : Nat`, where a positional walk of the
    // spine would bind `g := G` and nothing else. The same holds when the ref's
    // context is folded behind a def (`two`), which is unfolded first.
    const mm0_src = ordered_ctx_theory ++
        \\def two (G: ctx) (a b: wff): ctx = $ join G (join (hyp a) (hyp b)) $;
        \\axiom lam_i (g: ctx) {x: tm} (A: ty) (J: wff):
        \\  $ nd (join g (hyp (has x A))) J $ > $ nd g J $;
        \\theorem t (G: ctx) {k m: tm}:
        \\  $ nd (join G (join (hyp (has k Nat)) (hyp (has m Nat)))) (has m Nat) $;
    ;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    var fixture = try fixtureFor(allocator, mm0_src, "t");
    var theorem = TheoremContext.init(allocator);
    defer theorem.deinit();
    try theorem.seedAssertion(fixture.assertion);
    var theorem_vars = try Check.buildTheoremVarMap(allocator, fixture.assertion);
    defer theorem_vars.deinit();
    var harness = ContextHarness.init(allocator);
    defer harness.deinit();
    const context = harness.context(&fixture);
    const rule_id = fixture.theory.env.getRuleId("lam_i") orelse return error.MissingRule;
    const rule = &fixture.theory.env.rules.items[rule_id];

    const spelled = (try parseGoal(
        &fixture,
        &theorem,
        &theorem_vars,
        "nd (join G (join (hyp (has k Nat)) (hyp (has m Nat)))) (has m Nat)",
    )).concrete;
    const nd = theorem.interner.node(spelled).app;
    const spine = theorem.interner.node(nd.args[0]).app;
    const tail = theorem.interner.node(spine.args[1]).app;
    const k_entry = tail.args[0];
    const m_typing = theorem.interner.node(tail.args[1]).app.args[0];
    const m_has = theorem.interner.node(m_typing).app;
    const join_id = fixture.theory.env.term_names.get("join") orelse return error.MissingTerm;
    const expected_g = try theorem.interner.internApp(join_id, &.{ spine.args[0], k_entry });

    const folded = (try parseGoal(
        &fixture,
        &theorem,
        &theorem_vars,
        "nd (two G (has k Nat) (has m Nat)) (has m Nat)",
    )).concrete;
    for ([_]ExprId{ spelled, folded }) |ref| {
        const bindings = try allocator.alloc(?ExprId, rule.args.len);
        @memset(bindings, null);
        def_match.extractHypPartialBindings(&context, &theorem, rule.hyps[0], ref, bindings);

        try std.testing.expectEqual(@as(?ExprId, expected_g), bindings[0]);
        try std.testing.expectEqual(@as(?ExprId, m_has.args[0]), bindings[1]);
        try std.testing.expectEqual(@as(?ExprId, m_has.args[1]), bindings[2]);
        try std.testing.expectEqual(@as(?ExprId, nd.args[1]), bindings[3]);
    }
}

test "exprUnifiesModuloMeta treats search metas as wildcards but prunes rigid clashes" {
    // The carry-to-leaf witness predicate behind the ACUI plausibility prune:
    // a binding embedding an open `.meta` leaf (e.g. `rim`'s `P ?t`) must stay
    // unifiable with a concrete member (`P c`) so the witness can be pinned at
    // validation, while a genuinely different rigid skeleton still prunes. No
    // env is consulted, so raw term ids and vars suffice.
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    var theorem = TheoremContext.init(allocator);
    defer theorem.deinit();

    const term_p: u32 = 1;
    const term_q: u32 = 2;
    const c = try theorem.interner.internVar(.{ .theorem_var = 0 });
    const d = try theorem.interner.internVar(.{ .theorem_var = 1 });
    const meta = try theorem.addMetaPlaceholderResolved("wff");

    const p_meta = try theorem.interner.internApp(term_p, &.{meta});
    const p_c = try theorem.interner.internApp(term_p, &.{c});
    const p_d = try theorem.interner.internApp(term_p, &.{d});
    const q_c = try theorem.interner.internApp(term_q, &.{c});

    const unifies = acui.exprUnifiesModuloMeta;
    // Meta absorbs the difference — buried (either side) or bare.
    try std.testing.expect(unifies(&theorem, p_meta, p_c));
    try std.testing.expect(unifies(&theorem, p_c, p_meta));
    try std.testing.expect(unifies(&theorem, meta, p_c));
    // Identity always unifies.
    try std.testing.expect(unifies(&theorem, p_c, p_c));
    // Rigid skeleton clashes still prune: differing argument var, differing
    // head, and a head clash that an embedded meta must NOT paper over.
    try std.testing.expect(!unifies(&theorem, p_c, p_d));
    try std.testing.expect(!unifies(&theorem, p_c, q_c));
    try std.testing.expect(!unifies(&theorem, p_meta, q_c));
}

test "search candidate supports view recover with holey goals" {
    try expectCaseLineSearch(
        "pass_hole_view_recover_matrix",
        "view_recover_visible_formula",
        0,
    );
}

test "apply search may list broad whole-line hole candidates" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\--| @hole _wff
        \\provable sort wff;
        \\term P: wff;
        \\axiom p: $ P $;
        \\theorem t: $ P $;
    ;
    try expectApplyContains(mm0_src, "t", "_wff", "p", 0, 0);
}

test "exact search suppresses broad whole-line holes without refs" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\--| @hole _wff
        \\provable sort wff;
        \\term P: wff;
        \\axiom p: $ P $;
        \\theorem t: $ P $;
    ;
    try expectOffers(mm0_src,
        \\t
        \\------
        \\l1: $ _wff $ by exact?
        \\l2: $ P $ by p []
    , "exact?", .{}, &.{});
}

test "hole sort mismatches do not poison later search candidates" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\--| @hole _wff
        \\provable sort wff;
        \\--| @hole _obj
        \\provable sort obj;
        \\term W: wff;
        \\term O: obj;
        \\axiom bad_wff: $ W $;
        \\axiom good_obj: $ O $;
        \\theorem t: $ O $;
    ;
    try expectApplyContains(mm0_src, "t", "_obj", "good_obj", 0, 0);
}

/// A small classical sequent calculus over an ACUI context with idempotence:
/// `not_left` is eager and keeps its principal, so `raa` at an atom whose
/// negation is already a member turns the goal back into the `⊥` it came from,
/// with a duplicate member. The path guards must see that loop.
const loop_theory =
    \\delimiter $ ( ) [ / ] $;
    \\provable sort wff;
    \\sort ctx;
    \\--| @vars x y
    \\sort obj;
    \\term im (a b: wff): wff;
    \\infixr im: $→$ prec 25;
    \\term bi (a b: wff): wff;
    \\infixl bi: $↔$ prec 20;
    \\term all {x: obj} (p: wff x): wff;
    \\prefix all: $∀$ prec 41;
    \\term sb_f {x: obj} (t: obj x) (p: wff x): wff;
    \\notation sb_f {x: obj} (t: obj x) (p: wff x): wff =
    \\  ($[$:41) x ($/$:0) t ($]$:0) p;
    \\term sb_t {x: obj} (t: obj x) (a: obj x): obj;
    \\notation sb_t {x: obj} (t: obj x) (a: obj x): obj =
    \\  ($subst$:41) x ($/$:0) t a;
    \\term P (a: obj): wff;
    \\prefix P: $P$ prec 45;
    \\term Q (a: obj): wff;
    \\prefix Q: $Q$ prec 45;
    \\term R (a: obj): wff;
    \\prefix R: $R$ prec 45;
    \\term cc: obj;
    \\notation cc: obj = ($C$:max);
    \\term dd: obj;
    \\notation dd: obj = ($D$:max);
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
    \\term eq (a b: obj): wff;
    \\term not (a: wff): wff;
    \\prefix not: $¬$ prec 40;
    \\term bot: wff;
    \\notation bot: wff = ($⊥$:max);
    \\infixl eq: $=$ prec 50;
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
    \\--| @relation obj eq eq_refl eq_trans eq_sym _
    \\axiom eq_refl (a: obj): $ a = a $;
    \\axiom eq_trans (a b c: obj): $ a = b $ > $ b = c $ > $ a = c $;
    \\axiom eq_sym (a b: obj): $ a = b $ > $ b = a $;
    \\--| @congr
    \\axiom join_congr (g1 g2 h1 h2: ctx):
    \\  $ ctx_eq g1 g2 $ > $ ctx_eq h1 h2 $ > $ ctx_eq (g1 , h1) (g2 , h2) $;
    \\--| @congr
    \\axiom hyp_congr (a b: wff): $ a ↔ b $ > $ ctx_eq (hyp a) (hyp b) $;
    \\--| @congr
    \\axiom nd_congr (e f: ctx) (a b: wff):
    \\  $ ctx_eq e f $ > $ a ↔ b $ > $ (e ⊢ a) ↔ (f ⊢ b) $;
    \\--| @congr
    \\axiom im_congr (a b c d: wff):
    \\  $ a ↔ b $ > $ c ↔ d $ > $ (a → c) ↔ (b → d) $;
    \\--| @congr
    \\axiom all_congr {x: obj} (p q: wff x): $ p ↔ q $ > $ ∀ x p ↔ ∀ x q $;
    \\--| @congr
    \\axiom not_congr (a b: wff): $ a ↔ b $ > $ ¬ a ↔ ¬ b $;
    \\--| @congr
    \\axiom P_congr (a b: obj): $ a = b $ > $ P a ↔ P b $;
    \\--| @congr
    \\axiom R_congr (a b: obj): $ a = b $ > $ R a ↔ R b $;
    \\--| @congr
    \\axiom Q_congr (a b: obj): $ a = b $ > $ Q a ↔ Q b $;
    \\--| @congr
    \\axiom sb_f_congr {x: obj} (t1 t2: obj x) (p1 p2: wff x):
    \\  $ t1 = t2 $ > $ p1 ↔ p2 $ > $ [x/t1] p1 ↔ [x/t2] p2 $;
    \\--| @rewrite
    \\axiom sb_t_var {x: obj} (t: obj x): $ (subst x / t x) = t $;
    \\--| @rewrite
    \\axiom sb_t_irrel {x: obj} (t: obj x) (a: obj): $ (subst x / t a) = a $;
    \\--| @rewrite
    \\axiom sb_f_im {x: obj} (t: obj x) (p q: wff x):
    \\  $ [x/t] (p → q) ↔ ([x/t] p → [x/t] q) $;
    \\--| @rewrite
    \\axiom sb_f_not {x: obj} (t: obj x) (p: wff x): $ [x/t] (¬ p) ↔ ¬ [x/t] p $;
    \\--| @rewrite
    \\axiom sb_f_bot {x: obj} (t: obj x): $ [x/t] ⊥ ↔ ⊥ $;
    \\--| @rewrite
    \\axiom sb_f_P {x: obj} (t: obj x) (a: obj x):
    \\  $ [x/t] (P a) ↔ P (subst x / t a) $;
    \\--| @rewrite
    \\axiom sb_f_R {x: obj} (t: obj x) (a: obj x):
    \\  $ [x/t] (R a) ↔ R (subst x / t a) $;
    \\--| @rewrite
    \\axiom sb_f_Q {x: obj} (t: obj x) (a: obj x):
    \\  $ [x/t] (Q a) ↔ Q (subst x / t a) $;
    \\axiom ax (g: ctx) (a: wff): $ g , a ⊢ a $;
    \\axiom imp_intro (g: ctx) (a b: wff): $ g , a ⊢ b $ > $ g ⊢ a → b $;
    \\axiom raa (g: ctx) (a: wff): $ g , ¬ a ⊢ ⊥ $ > $ g ⊢ a $;
    \\--| @auto eager
    \\axiom not_left (g: ctx) (a: wff): $ g , ¬ a ⊢ a $ > $ g , ¬ a ⊢ ⊥ $;
    \\axiom imp_left (g: ctx) (a b c: wff):
    \\  $ g , (a → b) ⊢ a $ > $ g , (a → b) , b ⊢ c $ > $ g , (a → b) ⊢ c $;
    \\--| @view {x: obj} (g: ctx x) (t: obj x) (p: wff x) (q c: wff): $ g , (∀ x p) , q ⊢ c $ > $ g , (∀ x p) ⊢ c $
    \\--| @recover t q p x
    \\axiom all_left {x: obj} (g: ctx x) (p: wff x) (t: obj x) (c: wff x):
    \\  $ g , (∀ x p) , [x/t] p ⊢ c $ > $ g , (∀ x p) ⊢ c $;
;

test "auto splits a context without a set law between a weakening leaf and a fixed one" {
    // `two`'s conclusion splits `B , A , B` between its premises. Bound to
    // all its context can take, `la`'s share leaves `lb` nothing; its rest
    // binder must become a share of its own, which keeps one `B` while the
    // other goes to `lb`.
    const mm0_src = comm_ctx_theory ++
        \\--| @congr
        \\axiom join_congr (g1 g2 h1 h2: ctx):
        \\  $ ctx_eq g1 g2 $ > $ ctx_eq h1 h2 $ > $ ctx_eq (join g1 h1) (join g2 h2) $;
        \\--| @congr
        \\axiom hyp_congr (a b: wff): $ a <-> b $ > $ ctx_eq (hyp a) (hyp b) $;
        \\--| @congr
        \\axiom nd_congr (g h: ctx) (a b: wff):
        \\  $ ctx_eq g h $ > $ a <-> b $ > $ nd g a <-> nd h b $;
        \\term A: wff;
        \\term B: wff;
        \\term nd2 (g: ctx) (a: wff): wff;
        \\term ndr (g: ctx) (a: wff): wff;
        \\--| @congr
        \\axiom nd2_congr (g h: ctx) (a b: wff):
        \\  $ ctx_eq g h $ > $ a <-> b $ > $ nd2 g a <-> nd2 h b $;
        \\--| @congr
        \\axiom ndr_congr (g h: ctx) (a b: wff):
        \\  $ ctx_eq g h $ > $ a <-> b $ > $ ndr g a <-> ndr h b $;
        \\axiom two (g h: ctx) (a: wff): $ nd g a $ > $ ndr h a $ > $ nd2 (join g h) a $;
        \\axiom la (g: ctx): $ nd (join g (hyp A)) bot $;
        \\axiom lb: $ ndr (hyp B) bot $;
        \\theorem u: $ nd2 (join (hyp B) (join (hyp A) (hyp B))) bot $;
    ;
    const proof_src =
        \\u
        \\------
        \\l1: $ nd2 (join (hyp B) (join (hyp A) (hyp B))) bot $ by auto?
    ;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var suggestions = try suggestionsAtNeedle(&arena, mm0_src, proof_src, "auto?", .{
        .generate = .{ .enabled = true },
    });
    defer suggestions.deinit();
    try expectOffered(suggestions.items, &.{"two [la (g := $ hyp B $) [], lb []]"});
}

test "auto proves a goal whose search repeats an open goal with a duplicate member" {
    // `raa` re-adds `¬ P C` to an open context that already holds it, and the
    // copy is the same goal.
    const mm0_src = loop_theory ++
        \\
        \\theorem peirce_instance {x: obj}: $ ∀ x ((P x → Q x) → P x) ⊢ P C $;
    ;
    const proof_src =
        \\peirce_instance
        \\---------------
        \\l1: $ ∀ x ((P x → Q x) → P x) ⊢ P C $ by auto?
    ;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var suggestions = try suggestionsAtNeedle(
        &arena,
        mm0_src,
        proof_src,
        "auto?",
        .{ .generate = .{ .enabled = true } },
    );
    defer suggestions.deinit();

    try std.testing.expect(suggestions.items.len > 0);
}

test "auto proves a goal whose search loops through a repeated goal" {
    const mm0_src = loop_theory ++
        \\
        \\theorem chain {x: obj}: $ ∀ x (P x → Q x) , ∀ x (Q x → ¬ P x) , P C ⊢ ⊥ $;
    ;
    const proof_src =
        \\chain
        \\-----
        \\l1: $ ∀ x (P x → Q x) , ∀ x (Q x → ¬ P x) , P C ⊢ ⊥ $ by auto?
    ;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var suggestions = try suggestionsAtNeedle(
        &arena,
        mm0_src,
        proof_src,
        "auto?",
        .{ .generate = .{ .enabled = true } },
    );
    defer suggestions.deinit();

    try std.testing.expect(suggestions.items.len > 0);
}

test "exact keeps ACUI view conclusion split binders open" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    const mm0_src = try readProofCase(allocator, "euclid", "mm0");
    const proof_src =
        \\le_antisym_ax
        \\-------------
        \\l1: $ g ⊢ ∃ k (a + k = b) $ by le_iff_add [#1]
        \\l2: $ h ⊢ ∃ m (b + m = a) $ by le_iff_add [#2]
        \\l3: $ a + k = b ⊢ a + k = b $ by ax
        \\l4: $ b + m = a ⊢ b + m = a $ by ax
        \\l5: $ a + k = b ⊢ b = a + k $ by eq_sym_nd [l3]
        \\l7: $ a + k = b , b + m = a ⊢ (a + k) + m = a $
        \\  by eq_replace [l5, l4]
        \\l8: $ _ ⊢ (a + k) + m = a + (k + m) $ by add_assoc_ax
        \\l9: $ a + k = b , b + m = a ⊢ a + (k + m) = a $
        \\  by exact?
    ;
    var suggestions = try suggestionsAtNeedle(
        &arena,
        mm0_src,
        proof_src,
        "exact?",
        .{},
    );
    defer suggestions.deinit();

    try expectOffered(suggestions.items, &.{"eq_replace [l8, l7]"});
}

test "exact recovers ex_intro with reused named existential binder" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    const mm0_src = try readProofCase(allocator, "euclid", "mm0");
    const proof_src =
        \\le_iff_add
        \\----------
        \\l1: $ x + k = y ⊢ x + k = y $ by ax
        \\l2: $ x + k = y ⊢ ∃ k (x + k = y) $ by exact?
    ;
    var suggestions = try suggestionsAtNeedle(
        &arena,
        mm0_src,
        proof_src,
        "exact?",
        .{},
    );
    defer suggestions.deinit();

    try expectOffered(suggestions.items, &.{"ex_intro [l1]"});
}

test "exact uses view hyp shape to discover ex_intro past substitution head" {
    // The raw hypothesis of `ex_intro` is `[x/t] p` — substitution-headed,
    // so `P c` does not match it syntactically. The @view exposes the
    // hypothesis as just `q` (an unconstrained wff); the checker accepts
    // `ex_intro [l1]` via the `sb_f_P` / `sb_s_var` rewrite axioms (with the
    // help of `P_congr`).
    const mm0_src =
        \\delimiter $ ( ) [ / ] $;
        \\provable sort wff;
        \\--| @vars x y z t
        \\sort nat;
        \\
        \\term ex {x: nat} (p: wff x): wff;
        \\prefix ex: $E$ prec 41;
        \\
        \\term sb_f {x: nat} (t: nat x) (p: wff x): wff;
        \\notation sb_f {x: nat} (t: nat x) (p: wff x): wff =
        \\  ($[$:41) x ($/$:0) t ($]$:0) p;
        \\
        \\term sb_s {x: nat} (t: nat x) (a: nat x): nat;
        \\notation sb_s {x: nat} (t: nat x) (a: nat x): nat =
        \\  ($subst$:41) x ($/$:0) t a;
        \\
        \\term P (a: nat): wff;
        \\term c: nat;
        \\
        \\term iff (a b: wff): wff;
        \\infixr iff: $<->$ prec 20;
        \\term nat_eq (a b: nat): wff;
        \\infixl nat_eq: $==$ prec 35;
        \\
        \\--| @relation wff iff iff_refl iff_trans iff_sym iff_mp
        \\axiom iff_refl (a: wff): $ a <-> a $;
        \\axiom iff_trans (a b c: wff): $ a <-> b $ > $ b <-> c $ > $ a <-> c $;
        \\axiom iff_sym (a b: wff): $ a <-> b $ > $ b <-> a $;
        \\axiom iff_mp (a b: wff): $ a <-> b $ > $ a $ > $ b $;
        \\
        \\--| @relation nat nat_eq eq_refl eq_trans eq_sym _
        \\axiom eq_refl (a: nat): $ a == a $;
        \\axiom eq_trans (a b c: nat): $ a == b $ > $ b == c $ > $ a == c $;
        \\axiom eq_sym (a b: nat): $ a == b $ > $ b == a $;
        \\
        \\--| @congr
        \\axiom P_congr (a b: nat): $ a == b $ > $ P a <-> P b $;
        \\
        \\--| @rewrite
        \\axiom sb_f_P {x: nat} (t a: nat x):
        \\  $ [x/t] (P a) <-> P (subst x / t a) $;
        \\
        \\--| @rewrite
        \\axiom sb_s_var {x: nat} (t: nat x): $ subst x / t x == t $;
        \\
        \\axiom have_Pc: $ P c $;
        \\
        \\--| @view {x: nat} (t: nat x) (p: wff x) (q: wff): $ q $ > $ E x p $
        \\--| @recover t q p x
        \\axiom ex_intro {x: nat} (t: nat x) (p: wff x):
        \\  $ [x/t] p $ > $ E x p $;
        \\
        \\theorem prove_exists {x: nat}: $ E x (P x) $;
    ;
    const proof_src =
        \\prove_exists
        \\------------
        \\l1: $ P c $ by have_Pc
        \\l2: $ E x (P x) $ by exact?
    ;
    try expectOffers(mm0_src, proof_src, "exact?", .{}, &.{ "ex_intro [l1]", "ex_intro [have_Pc []]" });
}

// `all_left` keeps its `∀`, and the goal needs two different instances of
// it (at `C` and at `D`).
test "auto proves a goal that needs two instances of one universal" {
    const mm0_src =
        \\delimiter $ ( ) [ / ] $;
        \\provable sort wff;
        \\sort ctx;
        \\--| @vars x y
        \\sort obj;
        \\term im (a b: wff): wff;
        \\infixr im: $→$ prec 25;
        \\term bi (a b: wff): wff;
        \\infixl bi: $↔$ prec 20;
        \\term all {x: obj} (p: wff x): wff;
        \\prefix all: $∀$ prec 41;
        \\term sb_f {x: obj} (t: obj x) (p: wff x): wff;
        \\notation sb_f {x: obj} (t: obj x) (p: wff x): wff =
        \\  ($[$:41) x ($/$:0) t ($]$:0) p;
        \\term sb_t {x: obj} (t: obj x) (a: obj x): obj;
        \\notation sb_t {x: obj} (t: obj x) (a: obj x): obj =
        \\  ($subst$:41) x ($/$:0) t a;
        \\term P (a: obj): wff;
        \\prefix P: $P$ prec 45;
        \\term Q (a: obj): wff;
        \\prefix Q: $Q$ prec 45;
        \\term cc: obj;
        \\notation cc: obj = ($C$:max);
        \\term dd: obj;
        \\notation dd: obj = ($D$:max);
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
        \\term eq (a b: obj): wff;
        \\infixl eq: $=$ prec 50;
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
        \\--| @relation obj eq eq_refl eq_trans eq_sym _
        \\axiom eq_refl (a: obj): $ a = a $;
        \\axiom eq_trans (a b c: obj): $ a = b $ > $ b = c $ > $ a = c $;
        \\axiom eq_sym (a b: obj): $ a = b $ > $ b = a $;
        \\--| @congr
        \\axiom join_congr (g1 g2 h1 h2: ctx):
        \\  $ ctx_eq g1 g2 $ > $ ctx_eq h1 h2 $ > $ ctx_eq (g1 , h1) (g2 , h2) $;
        \\--| @congr
        \\axiom hyp_congr (a b: wff): $ a ↔ b $ > $ ctx_eq (hyp a) (hyp b) $;
        \\--| @congr
        \\axiom nd_congr (e f: ctx) (a b: wff):
        \\  $ ctx_eq e f $ > $ a ↔ b $ > $ (e ⊢ a) ↔ (f ⊢ b) $;
        \\--| @congr
        \\axiom im_congr (a b c d: wff):
        \\  $ a ↔ b $ > $ c ↔ d $ > $ (a → c) ↔ (b → d) $;
        \\--| @congr
        \\axiom all_congr {x: obj} (p q: wff x): $ p ↔ q $ > $ ∀ x p ↔ ∀ x q $;
        \\--| @congr
        \\axiom P_congr (a b: obj): $ a = b $ > $ P a ↔ P b $;
        \\--| @congr
        \\axiom Q_congr (a b: obj): $ a = b $ > $ Q a ↔ Q b $;
        \\--| @congr
        \\axiom sb_f_congr {x: obj} (t1 t2: obj x) (p1 p2: wff x):
        \\  $ t1 = t2 $ > $ p1 ↔ p2 $ > $ [x/t1] p1 ↔ [x/t2] p2 $;
        \\--| @rewrite
        \\axiom sb_t_var {x: obj} (t: obj x): $ (subst x / t x) = t $;
        \\--| @rewrite
        \\axiom sb_t_irrel {x: obj} (t: obj x) (a: obj): $ (subst x / t a) = a $;
        \\--| @rewrite
        \\axiom sb_f_im {x: obj} (t: obj x) (p q: wff x):
        \\  $ [x/t] (p → q) ↔ ([x/t] p → [x/t] q) $;
        \\--| @rewrite
        \\axiom sb_f_P {x: obj} (t: obj x) (a: obj x):
        \\  $ [x/t] (P a) ↔ P (subst x / t a) $;
        \\--| @rewrite
        \\axiom sb_f_Q {x: obj} (t: obj x) (a: obj x):
        \\  $ [x/t] (Q a) ↔ Q (subst x / t a) $;
        \\axiom ax (g: ctx) (a: wff): $ g , a ⊢ a $;
        \\axiom imp_left (g: ctx) (a b c: wff):
        \\  $ g , (a → b) ⊢ a $ > $ g , (a → b) , b ⊢ c $ > $ g , (a → b) ⊢ c $;
        \\--| @view {x: obj} (g: ctx x) (t: obj x) (p: wff x) (q c: wff): $ g , (∀ x p) , q ⊢ c $ > $ g , (∀ x p) ⊢ c $
        \\--| @recover t q p x
        \\axiom all_left {x: obj} (g: ctx x) (p: wff x) (t: obj x) (c: wff x):
        \\  $ g , (∀ x p) , [x/t] p ⊢ c $ > $ g , (∀ x p) ⊢ c $;
        \\theorem two_instances {x: obj}:
        \\  $ ∀ x (P x → Q x) , P C , P D , (Q C → Q D → P x) ⊢ P x $;
    ;
    const proof_src =
        \\two_instances
        \\-------------
        \\l1: $ ∀ x (P x → Q x) , P C , P D , (Q C → Q D → P x) ⊢ P x $ by auto?
    ;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var suggestions = try suggestionsAtNeedle(
        &arena,
        mm0_src,
        proof_src,
        "auto?",
        .{ .generate = .{ .enabled = true } },
    );
    defer suggestions.deinit();
    try expectOffered(suggestions.items, &.{
        "all_left [imp_left [all_left [imp_left [ax (g := $ ∀ x (P x → Q x) , (P D , (Q C → Q D → P x , (P D → Q D , P C → Q C))) $, a := $ P C $) [], " ++
            "ax (g := $ ∀ x (P x → Q x) , (P C , (P D , (Q C → Q D → P x , (P C → Q C , P D → Q D)))) $, a := $ Q C $) []]], " ++
            "imp_left [imp_left [ax (g := $ ∀ x (P x → Q x) , (P C , (Q C → Q D → P x , (Q D → P x , P D → Q D))) $, a := $ P D $) [], " ++
            "ax (g := $ ∀ x (P x → Q x) , (P C , (P D , (Q C → Q D → P x , (Q D → P x , P D → Q D)))) $, a := $ Q D $) []], " ++
            "ax (g := $ ∀ x (P x → Q x) , (P C , (P D , (Q C → Q D → P x , (Q D → P x , P D → Q D)))) $, a := $ P x $) []]]]",
    });
}
