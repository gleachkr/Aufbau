const helpers = @import("./helpers.zig");
const std = helpers.std;
const types = helpers.types;
const fixture_mod = helpers.fixture_mod;
const backtrack = helpers.backtrack;
const semantic = helpers.semantic;
const abstract_prune = helpers.abstract_prune;
const context_prune = helpers.context_prune;
const seed = helpers.seed;
const acui = helpers.acui;
const def_match = helpers.def_match;
const Witness = helpers.Witness;
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
const exact = helpers.exact;
const fixtureFor = helpers.fixtureFor;
const ruleArgIndex = helpers.ruleArgIndex;
const parseGoal = helpers.parseGoal;
const readProofCase = helpers.readProofCase;
const ContextHarness = helpers.ContextHarness;
const expectCaseLineSearch = helpers.expectCaseLineSearch;
const expectApplyContains = helpers.expectApplyContains;
const expectExactRuleOrder = helpers.expectExactRuleOrder;
const expectFirstExactRefs = helpers.expectFirstExactRefs;
const suggestionsAtNeedle = helpers.suggestionsAtNeedle;
const expectOffered = helpers.expectOffered;

test "conclusion seed unfolds transparent template head" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\strict provable sort wff;
        \\sort type;
        \\term bool: type;
        \\sort term;
        \\term eqc (A: type) (t u: term): term;
        \\def bic (p q: term): term = $ eqc bool p q $;
        \\term thm (p: term): wff;
        \\
        \\axiom ded (p q: term):
        \\  $ thm p $ > $ thm q $ > $ thm (bic p q) $;
        \\theorem t (a b: term): $ thm (eqc bool a b) $;
    ;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    var fixture = try fixtureFor(allocator, mm0_src, "t");
    var theorem = TheoremContext.init(allocator);
    defer theorem.deinit();
    try theorem.seedAssertion(fixture.assertion);
    var harness = ContextHarness.init(allocator);
    defer harness.deinit();
    const context = harness.context(&fixture);
    const goal_expr = try theorem.internParsedExpr(fixture.assertion.concl);
    const goal: Goal = .{ .concrete = goal_expr };
    const rule_id = fixture.env.getRuleId("ded") orelse return error.MissingRule;
    var candidate = try seed.makeExactRuleCandidate(
        allocator,
        &context,
        goal,
        &theorem,
        rule_id,
    );
    defer candidate.deinit();

    const rule = &fixture.env.rules.items[@intCast(rule_id)];
    const p_idx = blk: {
        for (rule.arg_names, 0..) |maybe_name, idx| {
            const name = maybe_name orelse continue;
            if (std.mem.eql(u8, name, "p")) break :blk idx;
        }
        return error.MissingArg;
    };
    const q_idx = blk: {
        for (rule.arg_names, 0..) |maybe_name, idx| {
            const name = maybe_name orelse continue;
            if (std.mem.eql(u8, name, "q")) break :blk idx;
        }
        return error.MissingArg;
    };
    const a_expr = theorem.theorem_vars.items[0];
    const b_expr = theorem.theorem_vars.items[1];

    try std.testing.expectEqual(@as(?ExprId, a_expr), candidate.bindings[p_idx]);
    try std.testing.expectEqual(@as(?ExprId, b_expr), candidate.bindings[q_idx]);
}

/// Dependency slots the `ex_i` candidate for theorem `name`'s goal spends
/// beyond the theorem's own.
fn seedSlotSpend(comptime name: []const u8) !u32 {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\sort tm;
        \\term ex {x: tm} (p: wff x): wff;
        \\term pr (t: tm): wff;
        \\term z: tm;
        \\def ez {.x: tm}: wff = $ ex x (pr z) $;
        \\def ex_self {.x: tm}: wff = $ ex x (pr x) $;
        \\def ex_low {.x .y: tm}: wff = $ ex x (ex y (pr y)) $;
        \\def ex_high {.x .y: tm}: wff = $ ex y (ex x (pr x)) $;
        \\axiom ex_i {x: tm} (p: wff x): $ p $ > $ ex x p $;
        \\theorem scrubbed: $ ez $;
        \\theorem kept: $ ex_self $;
        \\theorem low_scrubbed: $ ex_low $;
        \\theorem high_scrubbed: $ ex_high $;
    ;
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
    const goal: Goal = .{ .concrete = try theorem.internParsedExpr(fixture.assertion.concl) };
    const rule_id = fixture.env.getRuleId("ex_i") orelse return error.MissingRule;
    var candidate = try seed.makeExactRuleCandidate(allocator, &context, goal, &theorem, rule_id);
    defer candidate.deinit();
    return theorem.depSlotsLeft() - candidate.theorem.depSlotsLeft();
}

test "rule seed gives back the dependency slots of the def dummies it scrubs" {
    // Unfolding `ez` pins `x` to its hidden variable alone, which the seed
    // scrubs: the slot comes back. In `ex_self` the hidden variable also sits
    // in `p := pr x`, kept as a reconciliation meta on the same bit: the slot
    // stays.
    try std.testing.expectEqual(@as(u32, 0), try seedSlotSpend("scrubbed"));
    try std.testing.expectEqual(@as(u32, 1), try seedSlotSpend("kept"));
    // Two hidden variables take slots 0 (`x`) and 1 (`y`); the one bound by
    // `ex_i`'s own `x` is scrubbed, the one inside `p` is kept. Release gives
    // back only slots past the newest one held: a scrubbed last slot comes
    // back, a scrubbed slot below a held one stays.
    try std.testing.expectEqual(@as(u32, 1), try seedSlotSpend("high_scrubbed"));
    try std.testing.expectEqual(@as(u32, 2), try seedSlotSpend("low_scrubbed"));
}

test "multiHypBinderMask flags binders occurring in more than one hypothesis" {
    // arg0 in hyp0 & hyp1 (multi); arg1 in hyp0 only (single); arg2 in hyp0 &
    // hyp1 (multi); arg3 in hyp1 only (single).
    const hyp0_args = [_]TemplateExpr{
        .{ .binder = 0 },
        .{ .binder = 1 },
        .{ .binder = 2 },
    };
    const hyp1_args = [_]TemplateExpr{
        .{ .binder = 0 },
        .{ .binder = 2 },
        .{ .binder = 3 },
    };
    const hyps = [_]TemplateExpr{
        .{ .app = .{ .term_id = 0, .args = &hyp0_args } },
        .{ .app = .{ .term_id = 0, .args = &hyp1_args } },
    };
    const mask = seed.multiHypBinderMask(&hyps);
    try std.testing.expect(!mask.overflow);
    try std.testing.expectEqual(@as(u64, 0b0101), mask.mask); // bits 0 and 2
}

// Regression for the eliminator-reconciliation seed partition (code review):
// a def-unfold dummy threaded across >1 hypothesis is kept as a reconciliation
// meta; a single-hypothesis dummy is scrubbed to null; and a BARE meta leaf is
// scrubbed even in a multi-hypothesis slot (it constrains nothing — it must not
// ride forward as an unresolved, non-reconciliation pin).
test "partitionSeedBindings: keep multi-hyp dummy as reconciliation meta, scrub single-hyp and bare meta" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    var theorem = TheoremContext.init(allocator);
    defer theorem.deinit();

    // arg0: hyp0 & hyp1 (multi). arg1: hyp0 only (single). arg2: hyp0 & hyp1 (multi).
    const hyp0_args = [_]TemplateExpr{
        .{ .binder = 0 },
        .{ .binder = 1 },
        .{ .binder = 2 },
    };
    const hyp1_args = [_]TemplateExpr{
        .{ .binder = 0 },
        .{ .binder = 2 },
    };
    const hyps = [_]TemplateExpr{
        .{ .app = .{ .term_id = 0, .args = &hyp0_args } },
        .{ .app = .{ .term_id = 0, .args = &hyp1_args } },
    };

    const d0 = try theorem.addPlaceholderResolved("tm"); // standard dummy, multi → keep
    const d1 = try theorem.addPlaceholderResolved("tm"); // standard dummy, single → scrub
    const m2 = try theorem.addMetaPlaceholderResolved("tm"); // bare meta, multi → scrub
    var bindings = [_]?ExprId{ d0, d1, m2 };

    try seed.partitionSeedBindings(allocator, &theorem, &hyps, &bindings);

    // arg0 kept and converted to a reconciliation meta.
    try std.testing.expect(bindings[0] != null);
    const pid0 = switch (theorem.interner.node(bindings[0].?).*) {
        .placeholder => |id| id,
        else => return error.ExpectedPlaceholder,
    };
    try std.testing.expect(theorem.placeholderClass(pid0) == .meta);
    try std.testing.expect(theorem.placeholderInfo(pid0).?.reconciliation_meta);
    try std.testing.expect(theorem.hasReconciliationMetas());

    // arg1 (single-hyp dummy) scrubbed; arg2 (bare meta) scrubbed despite multi.
    try std.testing.expectEqual(@as(?ExprId, null), bindings[1]);
    try std.testing.expectEqual(@as(?ExprId, null), bindings[2]);
}

// `nat_ind_elim`'s step term: a single-hypothesis binder holding a term is
// kept (`s` under `ih`), sharing the meta with the dummy's own binder, which is
// kept because the term mentions it. A term over a dummy no binder holds (a
// `λ` variable inside an unfolded body) is kept too, with its own meta.
test "partitionSeedBindings: keep single-hyp terms and the dummies they share" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    var theorem = TheoremContext.init(allocator);
    defer theorem.deinit();

    // arg0 `ih` and arg1 `s` occur in hyp0 only; arg2 `t` in hyp1 only.
    const hyp0_args = [_]TemplateExpr{ .{ .binder = 0 }, .{ .binder = 1 } };
    const hyp1_args = [_]TemplateExpr{.{ .binder = 2 }};
    const hyps = [_]TemplateExpr{
        .{ .app = .{ .term_id = 0, .args = &hyp0_args } },
        .{ .app = .{ .term_id = 0, .args = &hyp1_args } },
    };

    const ih = try theorem.addPlaceholderResolved("tm");
    const stray = try theorem.addPlaceholderResolved("tm");
    const s = try theorem.interner.internApp(1, &.{ih});
    const t = try theorem.interner.internApp(1, &.{stray});
    var bindings = [_]?ExprId{ ih, s, t };

    try seed.partitionSeedBindings(allocator, &theorem, &hyps, &bindings);

    const meta = bindings[0] orelse return error.ExpectedKept;
    const pid = switch (theorem.interner.node(meta).*) {
        .placeholder => |id| id,
        else => return error.ExpectedPlaceholder,
    };
    try std.testing.expect(theorem.placeholderInfo(pid).?.reconciliation_meta);
    try std.testing.expectEqual(
        @as(?ExprId, try theorem.interner.internApp(1, &.{meta})),
        bindings[1],
    );
    const kept_t = bindings[2] orelse return error.ExpectedKept;
    const stray_meta = switch (theorem.interner.node(kept_t).*) {
        .app => |app| app.args[0],
        else => return error.ExpectedApp,
    };
    const stray_pid = switch (theorem.interner.node(stray_meta).*) {
        .placeholder => |id| id,
        else => return error.ExpectedPlaceholder,
    };
    try std.testing.expect(theorem.placeholderInfo(stray_pid).?.reconciliation_meta);
    try std.testing.expect(stray_meta != meta);
}

// A two-sided sequent calculus with an ACUI context, a two-premise
// left-implication rule (`lim`, principal `im a b` selected from the
// antecedent), and a one-premise left-conjunction rule (`lan`). Each fan-out
// test appends its own `theorem t` line whose conclusion is the search goal.
const fanout_seq_prefix =
    \\delimiter $ ( ) $;
    \\provable sort wff;
    \\sort ctx;
    \\term im (a b: wff): wff;
    \\term an (a b: wff): wff;
    \\term ctx_eq (g h: ctx): wff;
    \\term emp: ctx;
    \\--| @acui ctx_assoc ctx_comm emp ctx_idem
    \\term join (g h: ctx): ctx;
    \\term hyp (a: wff): ctx;
    \\term seq (g d: ctx): wff;
    \\term P: wff;
    \\term Q: wff;
    \\term R: wff;
    \\term S: wff;
    \\
    \\--| @relation ctx ctx_eq ctx_refl ctx_trans ctx_sym _
    \\axiom ctx_refl (g: ctx): $ ctx_eq g g $;
    \\axiom ctx_trans (g h i: ctx):
    \\  $ ctx_eq g h $ > $ ctx_eq h i $ > $ ctx_eq g i $;
    \\axiom ctx_sym (g h: ctx): $ ctx_eq g h $ > $ ctx_eq h g $;
    \\axiom ctx_assoc (g h i: ctx):
    \\  $ ctx_eq (join (join g h) i) (join g (join h i)) $;
    \\axiom ctx_comm (g h: ctx): $ ctx_eq (join g h) (join h g) $;
    \\axiom ctx_idem (g: ctx): $ ctx_eq (join g g) g $;
    \\axiom ctx_unit (g: ctx): $ ctx_eq (join emp g) g $;
    \\
    \\axiom lim (g d: ctx) (a b: wff):
    \\  $ seq g (join (hyp a) d) $ >
    \\  $ seq (join g (hyp b)) d $ >
    \\  $ seq (join g (hyp (im a b))) d $;
    \\axiom lan (g d: ctx) (a b: wff):
    \\  $ seq (join (join g (hyp a)) (hyp b)) d $ >
    \\  $ seq (join g (hyp (an a b))) d $;
    \\
;

// Build a `Context` over `fanout_seq_prefix ++ theorem_line`, take theorem `t`'s
// conclusion as the search goal, and append `rule_name`'s candidates to `list`.
// Everything allocates through `allocator` (an arena), so the caller's arena
// owns all of it; `holder.*` must outlive the candidates' use.
const FanoutHolder = struct {
    fixture: fixture_mod.Fixture = undefined,
    theorem: TheoremContext = undefined,
    harness: ContextHarness = undefined,
};

fn collectFanoutCandidates(
    allocator: std.mem.Allocator,
    holder: *FanoutHolder,
    mm0_src: []const u8,
    rule_name: []const u8,
    list: *std.ArrayListUnmanaged(types.ApplyCandidate),
) !void {
    holder.fixture = try fixtureFor(allocator, mm0_src, "t");
    holder.theorem = TheoremContext.init(allocator);
    try holder.theorem.seedAssertion(holder.fixture.assertion);
    holder.harness = ContextHarness.init(allocator);
    const context = holder.harness.context(&holder.fixture);
    const goal_expr = try holder.theorem.internParsedExpr(holder.fixture.assertion.concl);
    const goal: Goal = .{ .concrete = goal_expr };
    const rule_id = holder.fixture.env.getRuleId(rule_name) orelse
        return error.MissingRule;
    try seed.appendRuleCandidates(
        list,
        allocator,
        &context,
        goal,
        &holder.theorem,
        rule_id,
    );
}

test "principal fan-out: ambiguous two-premise principal yields one candidate per member" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    var holder: FanoutHolder = .{};
    var list = std.ArrayListUnmanaged(types.ApplyCandidate){};
    // Antecedent holds two implication members, so `lim`'s principal `(im a b)`
    // is shape-compatible with both — the case the plain seed abstains on.
    try collectFanoutCandidates(
        allocator,
        &holder,
        fanout_seq_prefix ++
            "theorem t: $ seq (join (join (hyp (im P Q)) (hyp (im R S))) (hyp Q)) (hyp Q) $;",
        "lim",
        &list,
    );

    try std.testing.expectEqual(@as(usize, 2), list.items.len);
    const rule = &holder.fixture.env.rules.items[
        @intCast(holder.fixture.env.getRuleId("lim").?)
    ];
    const a_idx = try ruleArgIndex(rule, "a");
    const b_idx = try ruleArgIndex(rule, "b");
    // Every variant pins both principal binders...
    for (list.items) |cand| {
        try std.testing.expect(cand.bindings[a_idx] != null);
        try std.testing.expect(cand.bindings[b_idx] != null);
    }
    // ...and the two variants pin DISTINCT principals (one per member).
    try std.testing.expect(
        list.items[0].bindings[a_idx].? != list.items[1].bindings[a_idx].?,
    );
}

test "principal fan-out: single matching member keeps one candidate" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    var holder: FanoutHolder = .{};
    var list = std.ArrayListUnmanaged(types.ApplyCandidate){};
    // Only one implication member ⇒ the seed pins it uniquely; no fan-out.
    try collectFanoutCandidates(
        allocator,
        &holder,
        fanout_seq_prefix ++
            "theorem t: $ seq (join (hyp (im P Q)) (hyp Q)) (hyp Q) $;",
        "lim",
        &list,
    );
    try std.testing.expectEqual(@as(usize, 1), list.items.len);
}

test "principal fan-out: one-premise rule is not fanned out" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    var holder: FanoutHolder = .{};
    var list = std.ArrayListUnmanaged(types.ApplyCandidate){};
    // Two conjunction members would make `lan`'s principal ambiguous, but `lan`
    // has a single premise: its loose backtrack is linear, so the premises≥2
    // gate keeps it a single candidate (the spurious-overhead guard the
    // budget-edge `drinker` case needs).
    try collectFanoutCandidates(
        allocator,
        &holder,
        fanout_seq_prefix ++
            "theorem t: $ seq (join (join (hyp (an P Q)) (hyp (an R S))) (hyp Q)) (hyp Q) $;",
        "lan",
        &list,
    );
    try std.testing.expectEqual(@as(usize, 1), list.items.len);
}

test "ACUI conclusion member prune scans below semantic container" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\sort ctx;
        \\term iff (a b: wff): wff;
        \\infixr iff: $<->$ prec 20;
        \\term ctx_eq (g h: ctx): wff;
        \\term emp: ctx;
        \\--| @acui ctx_assoc ctx_comm emp ctx_idem
        \\term join (g h: ctx): ctx;
        \\term hyp (a: wff): ctx;
        \\term nd (g: ctx) (a: wff): wff;
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
        \\axiom ctx_comm (g h: ctx): $ ctx_eq (join g h) (join h g) $;
        \\axiom ctx_idem (g: ctx): $ ctx_eq (join g g) g $;
        \\axiom ctx_unit (g: ctx): $ ctx_eq (join emp g) g $;
        \\
        \\axiom use_assump (g: ctx) (p: wff):
        \\  $ nd (join g (hyp p)) p $;
        \\theorem t (a b c: wff):
        \\  $ nd (join (hyp a) (hyp b)) c $;
    ;
    const proof_src =
        \\t
        \\------
        \\l1: $ nd (join (hyp a) (hyp b)) c $ by exact?
    ;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    var suggestions = try suggestionsAtNeedle(
        &arena,
        mm0_src,
        proof_src,
        "exact?",
        .{ .counters = &counters },
    );
    defer suggestions.deinit();

    try std.testing.expectEqual(@as(usize, 0), suggestions.items.len);
    try std.testing.expectEqual(
        @as(usize, 0),
        counters.full_try_candidate_calls,
    );
    try std.testing.expect(counters.conclusion_member_prunes > 0);
}

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

/// `ordered_ctx_theory` with an idempotent (still ordered) context combiner.
const idempotent_ctx_theory = replaceOnce(
    ordered_ctx_theory,
    "@acui ctx_assoc _ emp _",
    "@acui ctx_assoc _ emp ctx_idem",
) ++
    \\axiom ctx_idem (g: ctx): $ ctx_eq (join g g) g $;
    \\
;

/// Runs `exact?` at the proof's `exact?` needle; returns the suggestion count.
fn exactSuggestionCount(
    mm0_src: []const u8,
    proof_src: []const u8,
    counters: *types.SearchCounters,
) !usize {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var suggestions = try suggestionsAtNeedle(
        &arena,
        mm0_src,
        proof_src,
        "exact?",
        .{ .counters = counters },
    );
    defer suggestions.deinit();
    return suggestions.items.len;
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

test "redex conclusion prune reads rewrite-head binders off the selected refs" {
    // `sub`'s conclusion has a `@rewrite` head, so the goal alone says nothing.
    // The ref `pr (lam y z)` gives `t := z`, and `sb y ?u z` reduces to `z`,
    // not the goal's `o`: pruned before the full check.
    const mm0_src = redex_theory ++
        \\theorem t {y: tm}: $ pr (lam y z) $ > $ pr z $ > $ pr o $;
    ;
    const proof_src =
        \\t
        \\------
        \\l1: $ pr o $ by exact?
    ;
    var counters = types.SearchCounters{};
    const count = try exactSuggestionCount(mm0_src, proof_src, &counters);

    try std.testing.expectEqual(@as(usize, 0), count);
    try std.testing.expectEqual(@as(usize, 0), counters.full_try_candidate_calls);
    try std.testing.expect(counters.redex_conclusion_prunes > 0);
}

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

test "redex conclusion prune abstains on a rewrite-headed premise" {
    // `via`'s premise `pr (fst t u)` reduces to `pr t`, so the ref
    // `pr (fst o z)` forces `t := o` and leaves `u` open; `u := o` proves the
    // goal. Read position by position, the ref would give `u := z`, and the
    // conclusion `fst z o` would reduce to `z`, not the goal's `o`.
    const mm0_src = redex_theory ++
        \\term fst (a b: tm): tm;
        \\--| @rewrite
        \\axiom fst_red (a b: tm): $ teq (fst a b) a $;
        \\axiom via (t u: tm): $ pr (fst t u) $ > $ pr (fst u t) $;
        \\theorem t: $ pr (fst o z) $ > $ pr o $;
    ;
    const proof_src =
        \\t
        \\------
        \\l1: $ pr o $ by exact?
    ;
    // The checker does not yet read `u` back through the `@rewrite` head
    // (`via (u := $ o $) [#1]` checks; `via [#1]` does not), so there is no
    // suggestion to count; the test checks only that the candidate reaches
    // validation.
    var counters = types.SearchCounters{};
    _ = try exactSuggestionCount(mm0_src, proof_src, &counters);

    try std.testing.expectEqual(@as(usize, 0), counters.redex_conclusion_prunes);
    try std.testing.expect(counters.full_try_candidate_calls > 0);
}

test "redex conclusion prune holds when the theorem has no dependency slots left" {
    // The ref gives `x := y` and `t := z`, and `sb y ?u z` reduces to `z`, not
    // the goal's `o`. The hole for the unbound `u` spends no dependency slot,
    // so the prune holds even with every slot already taken.
    const mm0_src = redex_theory ++
        \\theorem t {y: tm}: $ pr (lam y z) $ > $ pr z $ > $ pr o $;
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
    const rule_id = fixture.env.getRuleId("sub") orelse return error.MissingRule;
    const rule = &fixture.env.rules.items[rule_id];
    const ref = (try parseGoal(&fixture, &theorem, &theorem_vars, "pr (lam y z)")).concrete;
    const goal = (try parseGoal(&fixture, &theorem, &theorem_vars, "pr o")).concrete;
    const bindings = try allocator.alloc(?ExprId, rule.args.len);
    @memset(bindings, null);
    while (theorem.depSlotsLeft() > 0) _ = try theorem.addPlaceholderResolved("tm");

    try std.testing.expect(helpers.plausible.redexConclusionMismatch(&context, &theorem, rule, goal, bindings, &.{ ref, null }));
}

test "ACUI member prune counts distinct members without idempotence" {
    // `weaken2` needs two entries after `g`; the goal context has one. Each
    // required `hyp` leaf finds a compatible member on its own, but not a
    // distinct one, so the candidate is pruned before validation.
    const mm0_src = ordered_ctx_theory ++
        \\axiom weaken2 (g: ctx) {x y: tm} (T U: ty) (J: wff):
        \\  $ nd g J $ > $ nd (join (join g (hyp (has x T))) (hyp (has y U))) J $;
        \\theorem t (g: ctx) {k: tm} (z: tm):
        \\  $ nd g (has z Nat) $ > $ nd (join g (hyp (has k Nat))) (has z Nat) $;
    ;
    const proof_src =
        \\t
        \\------
        \\l1: $ nd (join g (hyp (has k Nat))) (has z Nat) $ by exact?
    ;
    var counters = types.SearchCounters{};
    const count = try exactSuggestionCount(mm0_src, proof_src, &counters);

    try std.testing.expectEqual(@as(usize, 0), count);
    try std.testing.expectEqual(@as(usize, 0), counters.full_try_candidate_calls);
    try std.testing.expect(counters.conclusion_member_prunes > 0);
}

test "ACUI member prune does not count a unit leaf as a required member" {
    // `emp` in `join g emp` is the unit: it needs no goal entry of its own.
    // Counting it would demand two members of a one-entry context.
    const mm0_src = ordered_ctx_theory ++
        \\axiom emp_right (g: ctx) (J: wff): $ nd g J $ > $ nd (join g emp) J $;
        \\theorem t {k: tm} (z: tm):
        \\  $ nd (hyp (has k Nat)) (has z Nat) $ >
        \\  $ nd (join (hyp (has k Nat)) emp) (has z Nat) $;
    ;
    const proof_src =
        \\t
        \\------
        \\l1: $ nd (join (hyp (has k Nat)) emp) (has z Nat) $ by exact?
    ;
    var counters = types.SearchCounters{};
    const count = try exactSuggestionCount(mm0_src, proof_src, &counters);

    try std.testing.expect(count > 0);
    try std.testing.expectEqual(@as(usize, 0), counters.conclusion_member_prunes);
}

test "dependency prune drops a rule whose binding rigidly mentions its bound binder" {
    // `weaken`'s `J` does not depend on `x`, but the goal forces `x := k` and
    // `J := has (suc k) Nat`. No conversion removes `k`, so every assembly is
    // a DepViolation: pruned at seed time.
    const mm0_src = ordered_ctx_theory ++
        \\axiom weaken (g: ctx) {x: tm} (T: ty) (J: wff):
        \\  $ nd g J $ > $ nd (join g (hyp (has x T))) J $;
        \\theorem t (g: ctx) {k: tm}:
        \\  $ nd g (has (suc k) Nat) $ >
        \\  $ nd (join g (hyp (has k Nat))) (has (suc k) Nat) $;
    ;
    const proof_src =
        \\t
        \\------
        \\l1: $ nd (join g (hyp (has k Nat))) (has (suc k) Nat) $ by exact?
    ;
    var counters = types.SearchCounters{};
    const count = try exactSuggestionCount(mm0_src, proof_src, &counters);

    try std.testing.expectEqual(@as(usize, 0), count);
    try std.testing.expectEqual(@as(usize, 0), counters.full_try_candidate_calls);
    try std.testing.expect(counters.dep_violation_prunes > 0);
}

test "dependency prune keeps an occurrence a def unfold can remove" {
    // Here `k` reaches `J` only through the def `cst`, whose body drops its
    // first argument, so conversion may remove it: no prune. The checker does
    // not yet unfold `cst` to clear the dependency (it reports the
    // DepViolation), so there is no suggestion to count; the test checks only
    // that the candidate reaches validation.
    const mm0_src = ordered_ctx_theory ++
        \\axiom weaken (g: ctx) {x: tm} (T: ty) (J: wff):
        \\  $ nd g J $ > $ nd (join g (hyp (has x T))) J $;
        \\theorem t (g: ctx) {k: tm} (z: tm):
        \\  $ nd g (has z Nat) $ >
        \\  $ nd (join g (hyp (has k Nat))) (has z (cst k Nat)) $;
    ;
    const proof_src =
        \\t
        \\------
        \\l1: $ nd (join g (hyp (has k Nat))) (has z (cst k Nat)) $ by exact?
    ;
    var counters = types.SearchCounters{};
    _ = try exactSuggestionCount(mm0_src, proof_src, &counters);

    try std.testing.expectEqual(@as(usize, 0), counters.dep_violation_prunes);
    try std.testing.expect(counters.full_try_candidate_calls > 0);
}

test "dependency prune sees through a def that keeps the occurrence" {
    // `sc k` unfolds to `suc k`: the body keeps its argument along rigid
    // heads, so no conversion removes `k` and the instance is pruned as in
    // the `suc k` case.
    const mm0_src = ordered_ctx_theory ++
        \\def sc (n: tm): tm = $ suc n $;
        \\axiom weaken (g: ctx) {x: tm} (T: ty) (J: wff):
        \\  $ nd g J $ > $ nd (join g (hyp (has x T))) J $;
        \\theorem t (g: ctx) {k: tm}:
        \\  $ nd g (has (sc k) Nat) $ >
        \\  $ nd (join g (hyp (has k Nat))) (has (sc k) Nat) $;
    ;
    const proof_src =
        \\t
        \\------
        \\l1: $ nd (join g (hyp (has k Nat))) (has (sc k) Nat) $ by exact?
    ;
    var counters = types.SearchCounters{};
    const count = try exactSuggestionCount(mm0_src, proof_src, &counters);

    try std.testing.expectEqual(@as(usize, 0), count);
    try std.testing.expectEqual(@as(usize, 0), counters.full_try_candidate_calls);
    try std.testing.expect(counters.dep_violation_prunes > 0);
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

test "ACUI member prune does not count members under an idempotent combiner" {
    // `join a a = a`: one visible entry may stand for both of the rule's.
    const mm0_src = idempotent_ctx_theory ++ weaken2_rule ++
        \\theorem t (g: ctx) {k: tm} (z: tm):
        \\  $ nd g (has z Nat) $ > $ nd (join g (hyp (has k Nat))) (has z Nat) $;
    ;
    const proof_src =
        \\t
        \\------
        \\l1: $ nd (join g (hyp (has k Nat))) (has z Nat) $ by exact?
    ;
    var counters = types.SearchCounters{};
    _ = try exactSuggestionCount(mm0_src, proof_src, &counters);

    try std.testing.expectEqual(@as(usize, 0), counters.conclusion_member_prunes);
    try std.testing.expect(counters.full_try_candidate_calls > 0);
}

test "ACUI member prune does not count a def-headed member" {
    // `hyp2 a b` unfolds to two entries, so the goal context has three.
    const mm0_src = ordered_ctx_theory ++ weaken2_rule ++
        \\def hyp2 (a b: wff): ctx = $ join (hyp a) (hyp b) $;
        \\theorem t (g: ctx) {k m: tm} (z: tm):
        \\  $ nd g (has z Nat) $ >
        \\  $ nd (join g (hyp2 (has k Nat) (has m Nat))) (has z Nat) $;
    ;
    const proof_src =
        \\t
        \\------
        \\l1: $ nd (join g (hyp2 (has k Nat) (has m Nat))) (has z Nat) $ by exact?
    ;
    var counters = types.SearchCounters{};
    _ = try exactSuggestionCount(mm0_src, proof_src, &counters);

    try std.testing.expectEqual(@as(usize, 0), counters.conclusion_member_prunes);
    try std.testing.expect(counters.full_try_candidate_calls > 0);
}

test "ACUI member prune does not count a placeholder member" {
    // `weaken2` needs two entries after `g`, and `g , k : Nat` has one. With
    // an open meta after `k : Nat`, the meta may stand for the second entry
    // (or for any number of them), so the count has no opinion.
    const mm0_src = ordered_ctx_theory ++ weaken2_rule ++
        \\theorem t (g: ctx) {k: tm} (z: tm): $ nd g (has z Nat) $;
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
    const rule_id = fixture.env.getRuleId("weaken2") orelse return error.MissingRule;
    const rule = &fixture.env.rules.items[rule_id];

    const one_entry = (try parseGoal(
        &fixture,
        &theorem,
        &theorem_vars,
        "nd (join g (hyp (has k Nat))) (has z Nat)",
    )).concrete;
    const nd = theorem.interner.node(one_entry).app;
    const g = theorem.interner.node(nd.args[0]).app.args[0];
    // The goal pins `weaken2`'s context binder `g` (argument 0), as seeding would.
    const bindings = try allocator.alloc(?ExprId, rule.args.len);
    @memset(bindings, null);
    bindings[0] = g;
    try std.testing.expect(!acui.acuiBoundMembersPlausible(
        &context,
        &theorem,
        rule.concl,
        one_entry,
        bindings,
    ));

    var store = MetaStore.init(allocator, &fixture.env);
    defer store.deinit();
    const meta = try store.mint(&theorem, "ctx", std.math.maxInt(u55), .existential);
    const join_id = fixture.env.term_names.get("join") orelse return error.MissingTerm;
    const open_ctx = try theorem.interner.internApp(join_id, &.{ nd.args[0], meta });
    const open_goal = try theorem.interner.internApp(nd.term_id, &.{ open_ctx, nd.args[1] });
    try std.testing.expect(acui.acuiBoundMembersPlausible(
        &context,
        &theorem,
        rule.concl,
        open_goal,
        bindings,
    ));
}

test "ACUI member prune keeps a required member an open meta may supply" {
    // `weaken` needs a `hyp` entry after `g`. Bare `g` has none, so the rule
    // is pruned. A meta after `g`, such as a context a premise left open,
    // may stand for one, so it is kept.
    const mm0_src = ordered_ctx_theory ++
        \\axiom weaken (g: ctx) {x: tm} (T: ty) (J: wff):
        \\  $ nd g J $ > $ nd (join g (hyp (has x T))) J $;
        \\theorem t (g: ctx) (z: tm): $ nd g (has z Nat) $;
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
    const rule_id = fixture.env.getRuleId("weaken") orelse return error.MissingRule;
    const rule = &fixture.env.rules.items[rule_id];

    const bare = (try parseGoal(&fixture, &theorem, &theorem_vars, "nd g (has z Nat)")).concrete;
    const nd = theorem.interner.node(bare).app;
    const g = nd.args[0];
    const bindings = try allocator.alloc(?ExprId, rule.args.len);
    @memset(bindings, null);
    bindings[0] = g;
    try std.testing.expect(!acui.acuiBoundMembersPlausible(&context, &theorem, rule.concl, bare, bindings));

    var store = MetaStore.init(allocator, &fixture.env);
    defer store.deinit();
    const meta = try store.mint(&theorem, "ctx", std.math.maxInt(u55), .existential);
    const join_id = fixture.env.term_names.get("join") orelse return error.MissingTerm;
    const open_ctx = try theorem.interner.internApp(join_id, &.{ g, meta });
    const open_goal = try theorem.interner.internApp(nd.term_id, &.{ open_ctx, nd.args[1] });
    try std.testing.expect(acui.acuiBoundMembersPlausible(&context, &theorem, rule.concl, open_goal, bindings));
}

test "ACUI member prunes keep a def leaf that unfolds to the unit" {
    // `nil` unfolds to `emp`, so `g , nil` matches the empty context with
    // `g := emp`: the leaf needs no member, and the goal has none to offer.
    const mm0_src = ordered_ctx_theory ++
        \\def nil: ctx = $ emp $;
        \\axiom wk_nil (g: ctx) (J: wff): $ nd g J $ > $ nd (join g nil) J $;
        \\theorem t (z: tm): $ nd emp (has z Nat) $;
    ;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    var fixture = try fixtureFor(allocator, mm0_src, "t");
    var theorem = TheoremContext.init(allocator);
    defer theorem.deinit();
    try theorem.seedAssertion(fixture.assertion);
    var harness = ContextHarness.init(allocator);
    defer harness.deinit();
    const context = harness.context(&fixture);
    const rule_id = fixture.env.getRuleId("wk_nil") orelse return error.MissingRule;
    const rule = &fixture.env.rules.items[rule_id];
    const goal = try theorem.internParsedExpr(fixture.assertion.concl);
    const bindings = try allocator.alloc(?ExprId, rule.args.len);
    @memset(bindings, null);

    try std.testing.expect(acui.acuiBoundMembersPlausible(&context, &theorem, rule.concl, goal, bindings));
    try std.testing.expect(!acui.acuiBoundMembersDeepMismatch(
        &context,
        &theorem,
        rule.concl,
        goal,
        bindings,
        helpers.plausible.unfoldedExprMismatch,
        null,
    ));
}

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

/// `comm_ctx_theory` with two `ax`-shaped rules whose `a` sits in two
/// context members.
const repeated_binder_theory = comm_ctx_theory ++
    \\axiom cax (a: wff) (d: ctx): $ nd (join (hyp a) (join (hyp (not a)) d)) bot $;
    \\axiom cax_imp (a: wff) (d: ctx): $ nd (join (hyp a) (join (hyp (imp a bot)) d)) bot $;
    \\theorem t (p q: wff): $ nd emp bot $;
;

/// `conclusionTemplatePlausible` of rule `rule_name` against `goal_src`, with
/// every binder unbound, as the seed leaves an ACUI region's binders. With
/// `meta_for`, that variable of the goal is replaced by an open meta first.
fn repeatedBinderPlausible(rule_name: []const u8, goal_src: []const u8, meta_for: ?[]const u8) !bool {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    var fixture = try fixtureFor(allocator, repeated_binder_theory, "t");
    var theorem = TheoremContext.init(allocator);
    defer theorem.deinit();
    try theorem.seedAssertion(fixture.assertion);
    var theorem_vars = try Check.buildTheoremVarMap(allocator, fixture.assertion);
    defer theorem_vars.deinit();
    var harness = ContextHarness.init(allocator);
    defer harness.deinit();
    const context = harness.context(&fixture);
    const rule_id = fixture.env.getRuleId(rule_name) orelse return error.MissingRule;
    const rule = &fixture.env.rules.items[rule_id];
    var goal = (try parseGoal(&fixture, &theorem, &theorem_vars, goal_src)).concrete;
    var store = MetaStore.init(allocator, &fixture.env);
    defer store.deinit();
    if (meta_for) |name| {
        const meta = try store.mint(&theorem, "wff", std.math.maxInt(u55), .existential);
        const leaf = try theorem.internParsedExpr(theorem_vars.get(name).?);
        goal = try helpers.forward.leafSwap(&theorem, goal, leaf, meta);
    }
    const bindings = try allocator.alloc(?ExprId, rule.args.len);
    @memset(bindings, null);
    return helpers.plausible.conclusionTemplatePlausible(&context, &theorem, rule.concl, goal, bindings);
}

test "repeated-binder prune refutes a goal no value of the binder covers" {
    try std.testing.expect(!try repeatedBinderPlausible(
        "cax_imp",
        "nd (join (hyp p) (hyp (imp q bot))) bot",
        null,
    ));
}

test "repeated-binder prune abstains on a def member" {
    // `not p` unfolds to `imp p bot`, which the goal holds.
    try std.testing.expect(try repeatedBinderPlausible(
        "cax",
        "nd (join (hyp p) (hyp (imp p bot))) bot",
        null,
    ));
}

test "repeated-binder prune abstains on a goal member holding a meta" {
    // The meta may become `p`.
    try std.testing.expect(try repeatedBinderPlausible(
        "cax_imp",
        "nd (join (hyp p) (hyp (imp q bot))) bot",
        "q",
    ));
}

test "auto? hands a generated context split to the checker as explicit bindings" {
    // Both premises of `two` are generated, and `la`'s conclusion depends on
    // the context it is given, so only the search knows which members each
    // side took. The checker's positional reading of `B , (A , B)` gives
    // `g := hyp B`, against which `la` cannot be checked.
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
        \\axiom two (g h: ctx) (a: wff): $ nd g a $ > $ nd h a $ > $ nd (join g h) a $;
        \\axiom la (g: ctx): $ nd (join g (hyp A)) bot $;
        \\axiom lb: $ nd (hyp B) bot $;
        \\theorem u: $ nd (join (hyp B) (join (hyp A) (hyp B))) bot $;
    ;
    const proof_src =
        \\u
        \\------
        \\l1: $ nd (join (hyp B) (join (hyp A) (hyp B))) bot $ by auto?
    ;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var suggestions = try suggestionsAtNeedle(&arena, mm0_src, proof_src, "auto?", .{
        .generate = .{ .enabled = true },
    });
    defer suggestions.deinit();
    try expectOffered(suggestions.items, &.{"two (h := $ hyp B $) [la [], lb []]"});
}

test "unfolded mismatch gives back the dependency slots its def unfolds spend" {
    // Both sides present a `lam` head, so telling `z` from `o` means unfolding
    // `lz`, which mints a placeholder for its hidden `x`. The verdict holds
    // none of it, so the slot comes back.
    const mm0_src = redex_theory ++
        \\def lz {.x: tm}: tm = $ lam x z $;
        \\theorem t {w: tm}: $ teq lz (lam w o) $;
    ;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    var fixture = try fixtureFor(allocator, mm0_src, "t");
    var theorem = TheoremContext.init(allocator);
    defer theorem.deinit();
    try theorem.seedAssertion(fixture.assertion);
    var harness = ContextHarness.init(allocator);
    defer harness.deinit();
    const context = harness.context(&fixture);
    const goal = theorem.interner.node(try theorem.internParsedExpr(fixture.assertion.concl)).app;
    const slots = theorem.depSlotsLeft();

    try std.testing.expect(helpers.plausible.unfoldedExprMismatch(&context, &theorem, goal.args[0], goal.args[1], 0));
    try std.testing.expectEqual(slots, theorem.depSlotsLeft());
}

test "unfolded mismatch compares a shared def head's arguments without unfolding it" {
    // Both sides apply `wrap`, so they differ only where their arguments do:
    // `lz` against `lam w o`. Telling those apart unfolds `lz`, one
    // placeholder for its hidden `x`. Unfolding `wrap` on each side as well
    // would mint one more per side.
    const mm0_src = redex_theory ++
        \\def lz {.x: tm}: tm = $ lam x z $;
        \\def wrap (a: tm) {.y: tm}: tm = $ lam y a $;
        \\theorem t {w: tm}: $ teq (wrap lz) (wrap (lam w o)) $;
    ;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    var fixture = try fixtureFor(allocator, mm0_src, "t");
    var theorem = TheoremContext.init(allocator);
    defer theorem.deinit();
    try theorem.seedAssertion(fixture.assertion);
    var harness = ContextHarness.init(allocator);
    defer harness.deinit();
    const context = harness.context(&fixture);
    const goal = theorem.interner.node(try theorem.internParsedExpr(fixture.assertion.concl)).app;
    const minted = theorem.next_placeholder_id;

    try std.testing.expect(helpers.plausible.unfoldedExprMismatch(&context, &theorem, goal.args[0], goal.args[1], 0));
    try std.testing.expectEqual(minted + 1, theorem.next_placeholder_id);
}

test "conclusion plausibility gives back the dependency slots its def unfolds spend" {
    // `lam_o`'s conclusion has a `lam` head where the goal has `lz`, so the
    // folded-goal check unfolds `lz`, minting a placeholder for its hidden
    // `x`. The verdict holds none of it, so the slot comes back.
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\sort tm;
        \\term teq (s t: tm): wff;
        \\term lam {x: tm} (t: tm x): tm;
        \\term z: tm;
        \\term o: tm;
        \\def lz {.x: tm}: tm = $ lam x z $;
        \\axiom lam_o {x: tm} (t: tm x): $ teq (lam x t) o $;
        \\theorem t: $ teq lz o $;
    ;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    var fixture = try fixtureFor(allocator, mm0_src, "t");
    var theorem = TheoremContext.init(allocator);
    defer theorem.deinit();
    try theorem.seedAssertion(fixture.assertion);
    var harness = ContextHarness.init(allocator);
    defer harness.deinit();
    const context = harness.context(&fixture);
    const goal: Goal = .{ .concrete = try theorem.internParsedExpr(fixture.assertion.concl) };
    const rule_id = fixture.env.getRuleId("lam_o") orelse return error.MissingRule;
    const bindings = try allocator.alloc(?ExprId, context.env.rules.items[rule_id].args.len);
    @memset(bindings, null);
    var candidate = types.ApplyCandidate{
        .allocator = allocator,
        .rule_id = rule_id,
        .rule_name = "lam_o",
        .declaration_order = 0,
        .theorem = try theorem.clone(),
        .bindings = try allocator.alloc(?ExprId, 0),
        .conclusion = goal.concrete,
        .unresolved_hyps = try allocator.alloc(types.UnresolvedHypothesis, 0),
    };
    defer candidate.deinit();
    const slots = candidate.theorem.depSlotsLeft();

    try std.testing.expect(helpers.plausible.finalConclusionPlausible(&context, &candidate, goal, bindings, .{}, null));
    try std.testing.expectEqual(slots, candidate.theorem.depSlotsLeft());
}

// The dependency prune's exemption (`ruleMayRechooseBound`): the pruned
// `weaken` instance above, on rules whose bound binder a view, `@fresh`, or
// `@freshen` may re-choose after the conclusion match.

const dep_hit_theorem =
    \\theorem t (g: ctx) {k: tm}:
    \\  $ nd g (has (suc k) Nat) $ >
    \\  $ nd (join g (hyp (has k Nat))) (has (suc k) Nat) $;
;

const dep_hit_proof =
    \\t
    \\------
    \\l1: $ nd (join g (hyp (has k Nat))) (has (suc k) Nat) $ by exact?
;

fn expectDepPruneAbstains(comptime annotation: []const u8) !void {
    const mm0_src = ordered_ctx_theory ++ annotation ++
        \\axiom weaken (g: ctx) {x: tm} (T: ty) (J: wff):
        \\  $ nd g J $ > $ nd (join g (hyp (has x T))) J $;
        \\
    ++ dep_hit_theorem;
    var counters = types.SearchCounters{};
    _ = try exactSuggestionCount(mm0_src, dep_hit_proof, &counters);

    try std.testing.expectEqual(@as(usize, 0), counters.dep_violation_prunes);
    try std.testing.expect(counters.full_try_candidate_calls > 0);
}

test "dependency prune abstains on a rule with a view" {
    try expectDepPruneAbstains(
        \\--| @view (g: ctx) {x: tm} (T: ty) (J: wff): $ nd g J $ > $ nd (join g (hyp (has x T))) J $
        \\
    );
}

test "dependency prune abstains on a rule with @fresh" {
    try expectDepPruneAbstains(
        \\--| @fresh x
        \\
    );
}

test "dependency prune abstains on a rule with @freshen" {
    try expectDepPruneAbstains(
        \\--| @freshen J x
        \\
    );
}

test "argDetermined reads def bodies, @rewrite and ACUI heads, and bad ids" {
    const mm0_src =
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
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var fixture = try fixtureFor(arena.allocator(), mm0_src, "t");
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
        const head = fixture.env.term_names.get(row.head) orelse return error.MissingTerm;
        for (row.determined, 0..) |expected, i| {
            std.testing.expectEqual(expected, semantic.argDetermined(&context, head, i)) catch |err| {
                std.debug.print("argDetermined({s}, {d})\n", .{ row.head, i });
                return err;
            };
        }
    }

    // An argument index past a def's parameters.
    const cst = fixture.env.term_names.get("cst") orelse return error.MissingTerm;
    try std.testing.expect(!semantic.argDetermined(&context, cst, 2));
    // A term id past the table, and a term recovery has discarded.
    const len: u32 = @intCast(fixture.env.terms.items.len);
    try std.testing.expect(!semantic.argDetermined(&context, len, 0));
    const f = fixture.env.term_names.get("f") orelse return error.MissingTerm;
    fixture.env.terms.items[f].available = false;
    try std.testing.expect(!semantic.argDetermined(&context, f, 0));
}

const lw_rules =
    \\axiom ctx_idem (g: ctx): $ ctx_eq (join g g) g $;
    \\term A: wff;
    \\term B: wff;
    \\axiom lw (g: ctx) (a J: wff): $ nd (join g (hyp a)) J $ > $ nd g J $;
    \\theorem t: $ nd (join (hyp A) (hyp B)) bot $;
;
const lw_multiset_theory = comm_ctx_theory ++ lw_rules;
const lw_set_theory = replaceOnce(
    comm_ctx_theory,
    "@acui ctx_assoc ctx_comm emp _",
    "@acui ctx_assoc ctx_comm emp ctx_idem",
) ++ lw_rules;

/// `a` of `lw`'s premise `g , hyp a ⊢ J` as `extractHypPartialBindings`
/// reads it off `hyp A , hyp B ⊢ bot` with `g := hyp A` bound, under a
/// commutative context combiner that is idempotent or not.
fn extractedLeafAfterBoundSibling(idempotent: bool) !?[]const u8 {
    const mm0_src = if (idempotent) lw_set_theory else lw_multiset_theory;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    var fixture = try fixtureFor(allocator, mm0_src, "t");
    var theorem = TheoremContext.init(allocator);
    defer theorem.deinit();
    try theorem.seedAssertion(fixture.assertion);
    var harness = ContextHarness.init(allocator);
    defer harness.deinit();
    const context = harness.context(&fixture);
    const rule_id = fixture.env.getRuleId("lw") orelse return error.MissingRule;
    const rule = &fixture.env.rules.items[rule_id];
    const ref = try theorem.internParsedExpr(fixture.assertion.concl);
    const ctx = theorem.interner.node(ref).app.args[0];
    const bindings = try allocator.alloc(?ExprId, rule.args.len);
    @memset(bindings, null);
    bindings[try ruleArgIndex(rule, "g")] = theorem.interner.node(ctx).app.args[0];
    def_match.extractHypPartialBindings(&context, &theorem, rule.hyps[0], ref, bindings);
    const a = bindings[try ruleArgIndex(rule, "a")] orelse return null;
    const a_id = theorem.interner.node(a).app.term_id;
    return fixture.env.terms.items[a_id].name;
}

test "extractHypPartialBindings pins a leaf by elimination only without idempotence" {
    // `g` claims `hyp A`, leaving `hyp B` as the only member for `hyp a`.
    try std.testing.expectEqualStrings("B", (try extractedLeafAfterBoundSibling(false)).?);
    // Under `g , g = g`, `hyp a` may repeat `hyp A` as well: nothing is forced.
    try std.testing.expectEqual(@as(?[]const u8, null), try extractedLeafAfterBoundSibling(true));
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
    const rule_id = fixture.env.getRuleId("lam_i") orelse return error.MissingRule;
    const rule = &fixture.env.rules.items[rule_id];

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
    const join_id = fixture.env.term_names.get("join") orelse return error.MissingTerm;
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

test "ACUI member prune allows transparent def matching variable member" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\sort ctx;
        \\term iff (a b: wff): wff;
        \\infixr iff: $<->$ prec 20;
        \\term ctx_eq (g h: ctx): wff;
        \\term emp: ctx;
        \\--| @acui ctx_assoc ctx_comm emp ctx_idem
        \\term join (g h: ctx): ctx;
        \\term holds (g: ctx): wff;
        \\term nd (g: ctx) (a: wff): wff;
        \\
        \\def idctx (g: ctx): ctx = $ g $;
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
        \\axiom ctx_comm (g h: ctx): $ ctx_eq (join g h) (join h g) $;
        \\axiom ctx_idem (g: ctx): $ ctx_eq (join g g) g $;
        \\axiom ctx_unit (g: ctx): $ ctx_eq (join emp g) g $;
        \\
        \\axiom use_idctx (g h: ctx):
        \\  $ nd (join h (idctx g)) (holds g) $;
        \\theorem t (G H: ctx):
        \\  $ nd (join H G) (holds G) $;
    ;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    var fixture = try fixtureFor(allocator, mm0_src, "t");
    var theorem = TheoremContext.init(allocator);
    defer theorem.deinit();
    try theorem.seedAssertion(fixture.assertion);
    var harness = ContextHarness.init(allocator);
    defer harness.deinit();
    const context = harness.context(&fixture);
    const goal_expr = try theorem.internParsedExpr(fixture.assertion.concl);
    const goal: Goal = .{ .concrete = goal_expr };
    const rule_id = fixture.env.getRuleId("use_idctx") orelse
        return error.MissingRule;
    var candidate = try seed.makeExactRuleCandidate(
        allocator,
        &context,
        goal,
        &theorem,
        rule_id,
    );
    defer candidate.deinit();
    const rule = &fixture.env.rules.items[@intCast(rule_id)];

    try std.testing.expect(acui.acuiBoundMembersPlausible(
        &context,
        &candidate.theorem,
        rule.concl,
        goal_expr,
        candidate.bindings,
    ));
}

test "closed-region prune refutes a ref context unequal to a bound context binder" {
    // A bare ACUI binder already bound (e.g. an ND rule's `g`, pinned by the
    // conclusion) must meet a ref context holding exactly its members; a ref
    // proved under a larger or smaller context can never fill that slot.
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\sort ctx;
        \\term ctx_eq (g h: ctx): wff;
        \\term emp: ctx;
        \\--| @acui ctx_assoc ctx_comm emp ctx_idem
        \\term join (g h: ctx): ctx;
        \\term hyp (a: wff): ctx;
        \\term nd (g: ctx) (a: wff): wff;
        \\def idw (a: wff): wff = $ a $;
        \\
        \\--| @relation ctx ctx_eq ctx_refl ctx_trans ctx_sym _
        \\axiom ctx_refl (g: ctx): $ ctx_eq g g $;
        \\axiom ctx_trans (g h i: ctx):
        \\  $ ctx_eq g h $ > $ ctx_eq h i $ > $ ctx_eq g i $;
        \\axiom ctx_sym (g h: ctx): $ ctx_eq g h $ > $ ctx_eq h g $;
        \\axiom ctx_assoc (g h i: ctx):
        \\  $ ctx_eq (join (join g h) i) (join g (join h i)) $;
        \\axiom ctx_comm (g h: ctx): $ ctx_eq (join g h) (join h g) $;
        \\axiom ctx_idem (g: ctx): $ ctx_eq (join g g) g $;
        \\axiom ctx_unit (g: ctx): $ ctx_eq (join emp g) g $;
        \\
        \\theorem t (G: ctx) (a b c: wff): $ nd G a $;
    ;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    var fixture = try fixtureFor(allocator, mm0_src, "t");
    var theorem = TheoremContext.init(allocator);
    defer theorem.deinit();
    try theorem.seedAssertion(fixture.assertion);
    var harness = ContextHarness.init(allocator);
    defer harness.deinit();
    const context = harness.context(&fixture);

    const join = fixture.env.term_names.get("join") orelse return error.MissingTerm;
    const hyp = fixture.env.term_names.get("hyp") orelse return error.MissingTerm;
    const idw = fixture.env.term_names.get("idw") orelse return error.MissingTerm;
    const g_var = try theorem.interner.internVar(.{ .theorem_var = 0 });
    const a = try theorem.interner.internVar(.{ .theorem_var = 1 });
    const b = try theorem.interner.internVar(.{ .theorem_var = 2 });
    const c = try theorem.interner.internVar(.{ .theorem_var = 3 });
    const ha = try theorem.interner.internApp(hyp, &.{a});
    const hb = try theorem.interner.internApp(hyp, &.{b});
    const hc = try theorem.interner.internApp(hyp, &.{c});
    const h_ida = try theorem.interner.internApp(hyp, &.{
        try theorem.interner.internApp(idw, &.{a}),
    });
    const ab = try theorem.interner.internApp(join, &.{ ha, hb });
    const ba = try theorem.interner.internApp(join, &.{ hb, ha });
    const abc = try theorem.interner.internApp(join, &.{ ab, hc });

    const template: TemplateExpr = .{ .binder = 0 };
    const plausible = struct {
        fn f(ctx: *const Context, th: *const TheoremContext, t: TemplateExpr, bound: ExprId, ref: ExprId) bool {
            const bindings = [_]?ExprId{bound};
            return acui.acuiClosedRegionPlausible(ctx, th, t, ref, &bindings);
        }
    }.f;

    // Same members in another order: plausible.
    try std.testing.expect(plausible(&context, &theorem, template, ab, ba));
    // An extra or a missing member: refuted, in either representation.
    try std.testing.expect(!plausible(&context, &theorem, template, ab, abc));
    try std.testing.expect(!plausible(&context, &theorem, template, ab, ha));
    try std.testing.expect(!plausible(&context, &theorem, template, ha, ab));
    // Abstains on an opaque ref member and on a member conversion could
    // change (a transparent def), where identity is not decisive.
    const g_b = try theorem.interner.internApp(join, &.{ g_var, hb });
    try std.testing.expect(plausible(&context, &theorem, template, ab, g_b));
    const ida_b = try theorem.interner.internApp(join, &.{ h_ida, hb });
    try std.testing.expect(plausible(&context, &theorem, template, ab, ida_b));
    // A bound value of open metas may be empty, so it meets the empty context;
    // a rigid member beside them may not.
    const emp = try theorem.interner.internApp(
        fixture.env.term_names.get("emp") orelse return error.MissingTerm,
        &.{},
    );
    const m1 = try theorem.addMetaPlaceholderResolved("ctx");
    const m2 = try theorem.addMetaPlaceholderResolved("ctx");
    const metas = try theorem.interner.internApp(join, &.{ m1, m2 });
    try std.testing.expect(plausible(&context, &theorem, template, metas, emp));
    const a_meta = try theorem.interner.internApp(join, &.{ ha, m1 });
    try std.testing.expect(!plausible(&context, &theorem, template, a_meta, emp));
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

test "solveCorrespondenceAcui matches commutative regions member-wise" {
    // The member-wise read-back matcher: a child conclusion ACUI-equal to the
    // open target but reordered/reassociated must still solve the target's
    // metas, while genuinely different multisets and non-commutative subsets
    // must not. Regions are matched as multisets only under a COMMUTATIVE
    // registered combiner (`join`); `join2` declares `_` for commutativity and
    // must stay positional.
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\sort ctx;
        \\term P: wff;
        \\term Q: wff;
        \\term R: wff;
        \\term emp: ctx;
        \\--| @acui ctx_assoc ctx_comm emp _
        \\term join (g h: ctx): ctx;
        \\term emp2: ctx;
        \\--| @acui ctx2_assoc _ emp2 _
        \\term join2 (g h: ctx): ctx;
        \\term hyp (a: wff): ctx;
        \\term boxed (g: ctx): ctx;
        \\theorem t: $ P $;
    ;
    var fixture = try fixtureFor(allocator, mm0_src, "t");
    var sink = DiagnosticSink.init(mm0_src, "");
    var compiler = CompilerContext.init(mm0_src, "", .none, &sink);
    _ = &compiler;
    var theorem = TheoremContext.init(allocator);
    defer theorem.deinit();
    try theorem.seedAssertion(fixture.assertion);
    var harness = ContextHarness.init(allocator);
    defer harness.deinit();
    const context = harness.context(&fixture);

    const join_id = fixture.env.term_names.get("join").?;
    const join2_id = fixture.env.term_names.get("join2").?;
    const emp_id = fixture.env.term_names.get("emp").?;
    const hyp_id = fixture.env.term_names.get("hyp").?;
    const p_id = fixture.env.term_names.get("P").?;
    const q_id = fixture.env.term_names.get("Q").?;
    const r_id = fixture.env.term_names.get("R").?;
    const hp = try theorem.interner.internApp(
        hyp_id,
        &.{try theorem.interner.internApp(p_id, &.{})},
    );
    const hq = try theorem.interner.internApp(
        hyp_id,
        &.{try theorem.interner.internApp(q_id, &.{})},
    );
    const hr = try theorem.interner.internApp(
        hyp_id,
        &.{try theorem.interner.internApp(r_id, &.{})},
    );

    var store = MetaStore.init(allocator, &fixture.env);
    defer store.deinit();
    const solve = Witness.solveCorrespondenceAcui;

    // Pure reassociation + reorder, no metas: (hp,hq),hr vs hq,(hr,hp).
    const left_nested = try theorem.interner.internApp(
        join_id,
        &.{ try theorem.interner.internApp(join_id, &.{ hp, hq }), hr },
    );
    const rotated = try theorem.interner.internApp(
        join_id,
        &.{ hq, try theorem.interner.internApp(join_id, &.{ hr, hp }) },
    );
    try std.testing.expect(try solve(&context, &store, &theorem, rotated, left_nested));

    // A whole-member meta absorbs the reordered complement: hp,?m vs
    // hq,(hr,hp) forces ?m := hq,hr (right-fold of the leftover members).
    const meta = try store.mint(&theorem, "ctx", std.math.maxInt(u55), .existential);
    const pat_meta = try theorem.interner.internApp(join_id, &.{ hp, meta });
    const mark = store.mark();
    try std.testing.expect(try solve(&context, &store, &theorem, rotated, pat_meta));
    try std.testing.expectEqual(
        try theorem.interner.internApp(join_id, &.{ hq, hr }),
        try store.materialize(&theorem, meta),
    );
    store.rollbackTo(mark);

    // Nothing left over: the meta takes the combiner's unit.
    try std.testing.expect(try solve(&context, &store, &theorem, hp, pat_meta));
    try std.testing.expectEqual(
        try theorem.interner.internApp(emp_id, &.{}),
        try store.materialize(&theorem, meta),
    );
    store.rollbackTo(mark);

    // Genuinely different multisets still conflict.
    const pq = try theorem.interner.internApp(join_id, &.{ hp, hq });
    const pr = try theorem.interner.internApp(join_id, &.{ hp, hr });
    try std.testing.expect(!(try solve(&context, &store, &theorem, pr, pq)));

    // Non-commutative subset (`join2`, comm declared `_`): reordering is NOT
    // reconcilable — the matcher must stay positional and reject.
    const pq2 = try theorem.interner.internApp(join2_id, &.{ hp, hq });
    const qp2 = try theorem.interner.internApp(join2_id, &.{ hq, hp });
    try std.testing.expect(!(try solve(&context, &store, &theorem, qp2, pq2)));

    // Foreign unit: `join2`'s unit `emp2` inside a `join` region is a REAL
    // member (join(emp2, X) is not ACUI-equal to X under join's laws), so a
    // source carrying it cannot cancel against a pattern without it.
    const emp2_id = fixture.env.term_names.get("emp2").?;
    const emp2 = try theorem.interner.internApp(emp2_id, &.{});
    const p_with_foreign_unit = try theorem.interner.internApp(join_id, &.{ hp, emp2 });
    try std.testing.expect(!(try solve(&context, &store, &theorem, p_with_foreign_unit, hp)));

    // The meta may absorb a foreign unit, though — it is a member like any
    // other.
    try std.testing.expect(try solve(&context, &store, &theorem, p_with_foreign_unit, pat_meta));
    try std.testing.expectEqual(emp2, try store.materialize(&theorem, meta));
    store.rollbackTo(mark);

    // Repeated meta, bare AND nested inside a structured member of the same
    // region: pass 2 solves `?m := hp` through `boxed ?m`, and the
    // whole-member complement branch must CONSISTENCY-CHECK the already-solved
    // meta against the leftover (`hp`) instead of failing the blind re-assign.
    const boxed_id = fixture.env.term_names.get("boxed").?;
    const boxed_meta = try theorem.interner.internApp(boxed_id, &.{meta});
    const boxed_hp = try theorem.interner.internApp(boxed_id, &.{hp});
    const pat_nested = try theorem.interner.internApp(join_id, &.{ meta, boxed_meta });
    const src_nested = try theorem.interner.internApp(join_id, &.{ boxed_hp, hp });
    try std.testing.expect(try solve(&context, &store, &theorem, src_nested, pat_nested));
    try std.testing.expectEqual(hp, try store.materialize(&theorem, meta));
    store.rollbackTo(mark);

    // Two DISTINCT whole-member metas in one region: no forced partition —
    // the matcher must abstain rather than guess.
    const meta2 = try store.mint(&theorem, "ctx", std.math.maxInt(u55), .existential);
    const pat_two_metas = try theorem.interner.internApp(join_id, &.{ meta, meta2 });
    try std.testing.expect(!(try solve(&context, &store, &theorem, rotated, pat_two_metas)));
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

test "exact search accepts broad whole-line holes with useful refs" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\--| @hole _wff
        \\provable sort wff;
        \\term P: wff;
        \\axiom id (p: wff): $ p $ > $ p $;
        \\theorem t: $ P $ > $ P $;
    ;
    try expectFirstExactRefs(
        mm0_src,
        "",
        "t",
        "_wff",
        0,
        "id",
        &[_]ProofScript.Ref{.{ .hyp = .{
            .index = 1,
            .span = .{ .start = 0, .end = 0 },
        } }},
    );
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
    try expectExactRuleOrder(mm0_src, "t", "_wff", &[_][]const u8{});
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

test "abstract pruner skips rigid-bad broad refs before validation" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term imp (a b: wff): wff;
        \\infixr imp: $->$ prec 25;
        \\term iff (a b: wff): wff;
        \\infixr iff: $<->$ prec 20;
        \\term top: wff;
        \\term sb (t x: wff) (r: wff x): wff;
        \\--| @relation wff iff iff_refl iff_trans iff_sym iff_mp
        \\axiom iff_refl (a: wff): $ a <-> a $;
        \\axiom iff_trans (a b c: wff): $ a <-> b $ > $ b <-> c $ > $ a <-> c $;
        \\axiom iff_sym (a b: wff): $ a <-> b $ > $ b <-> a $;
        \\axiom iff_mp (a b: wff): $ a <-> b $ > $ a $ > $ b $;
        \\--| @rewrite
        \\axiom sb_var (t x: wff): $ sb t x x <-> t $;
        \\--| @rewrite
        \\axiom sb_top (t x: wff): $ sb t x top <-> top $;
        \\--| @rewrite
        \\axiom sb_imp (t x: wff) (a b: wff x):
        \\  $ sb t x (a -> b) <-> (sb t x a -> sb t x b) $;
        \\--| @congr
        \\axiom imp_congr (a b c d: wff):
        \\  $ a <-> b $ > $ c <-> d $ > $ (a -> c) <-> (b -> d) $;
        \\--| @view (a b: wff) (r: wff a) (p q: wff): $ a <-> b $ > $ p $ > $ q $
        \\--| @abstract r p q a a b
        \\axiom ax_ctx (a b: wff) (r: wff a):
        \\  $ a <-> b $ > $ sb a a r $ > $ sb b a r $;
        \\theorem t (a b c: wff):
        \\  $ a <-> b $ > $ a -> top $ > $ c -> top $ >
        \\  $ b -> top $;
    ;
    const proof_src =
        \\t
        \\------
        \\l1: $ b -> top $ by exact?
    ;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    var suggestions = try suggestionsAtNeedle(
        &arena,
        mm0_src,
        proof_src,
        "exact?",
        .{ .counters = &counters },
    );
    defer suggestions.deinit();

    try expectOffered(suggestions.items, &.{"ax_ctx [#1, #2]"});
    try std.testing.expect(counters.abstract_prunes > 0);
}

test "abstract pruner resolves def heads to rigid roots, abstains on reducible heads" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term imp (a b: wff): wff;
        \\infixr imp: $->$ prec 25;
        \\term iff (a b: wff): wff;
        \\infixr iff: $<->$ prec 20;
        \\term top: wff;
        \\term sb (t x: wff) (r: wff x): wff;
        \\def hold (p: wff): wff = $ p $;
        \\def wrapiff (a b: wff): wff = $ a <-> b $;
        \\def wrapimp (a b: wff): wff = $ a -> b $;
        \\term pair (x y: wff): wff;
        \\def box {.x: wff} (a: wff): wff = $ pair x (a -> top) $;
        \\--| @relation wff iff iff_refl iff_trans iff_sym iff_mp
        \\axiom iff_refl (a: wff): $ a <-> a $;
        \\axiom iff_trans (a b c: wff): $ a <-> b $ > $ b <-> c $ > $ a <-> c $;
        \\axiom iff_sym (a b: wff): $ a <-> b $ > $ b <-> a $;
        \\axiom iff_mp (a b: wff): $ a <-> b $ > $ a $ > $ b $;
        \\--| @rewrite
        \\axiom sb_var (t x: wff): $ sb t x x <-> t $;
        \\--| @rewrite
        \\axiom sb_top (t x: wff): $ sb t x top <-> top $;
        \\--| @rewrite
        \\axiom sb_imp (t x: wff) (a b: wff x):
        \\  $ sb t x (a -> b) <-> (sb t x a -> sb t x b) $;
        \\--| @congr
        \\axiom imp_congr (a b c d: wff):
        \\  $ a <-> b $ > $ c <-> d $ > $ (a -> c) <-> (b -> d) $;
        \\--| @view (a b: wff) (r: wff a) (p q: wff): $ a <-> b $ > $ p $ > $ q $
        \\--| @abstract r p q a a b
        \\axiom ax_ctx (a b: wff) (r: wff a):
        \\  $ a <-> b $ > $ sb a a r $ > $ sb b a r $;
        \\theorem t (a b c: wff):
        \\  $ a <-> b $ > $ a -> top $ > $ c -> top $ >
        \\  $ hold (c -> top) $ > $ b -> top $;
    ;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    var fixture = try fixtureFor(allocator, mm0_src, "t");
    var theorem = TheoremContext.init(allocator);
    defer theorem.deinit();
    try theorem.seedAssertion(fixture.assertion);
    var theorem_vars = try Check.buildTheoremVarMap(
        allocator,
        fixture.assertion,
    );
    defer theorem_vars.deinit();
    var harness = ContextHarness.init(allocator);
    defer harness.deinit();
    const context = harness.context(&fixture);
    const rule_id = fixture.env.getRuleId("ax_ctx") orelse
        return error.MissingRule;
    const view = fixture.views.get(rule_id) orelse return error.MissingView;
    const goal_expr = try parseConcreteGoal(
        &fixture,
        &theorem,
        &theorem_vars,
        "b -> top",
    );
    const eq_expr = try parseConcreteGoal(
        &fixture,
        &theorem,
        &theorem_vars,
        "a <-> b",
    );
    const good_expr = try parseConcreteGoal(
        &fixture,
        &theorem,
        &theorem_vars,
        "a -> top",
    );
    const rigid_bad_expr = try parseConcreteGoal(
        &fixture,
        &theorem,
        &theorem_vars,
        "c -> top",
    );
    // A transparent-def-headed ref whose head resolves (through the def's body)
    // to a *rigid root* that clashes with the goal: `wrapiff c c` has head
    // `wrapiff`, a `def … = $ a <-> b $`, so its rigid root is `iff`, which
    // differs from the goal's `imp`. The prune now (soundly) fires on this, where
    // the committed code abstained on every non-rigid def head. Doomed:
    // with left_plug == hole, the motive is forced to the ref, and `[a:=b]` of
    // `c <-> c` (no `a`) is `c <-> c` ≠ the goal `b -> top`.
    const def_clash_expr = try parseConcreteGoal(
        &fixture,
        &theorem,
        &theorem_vars,
        "wrapiff c c",
    );
    // A transparent identity def whose body is a bare binder. Head-only
    // resolution sees no rigid root, but the body walk can compare the
    // concrete argument and reject `c -> top` against the goal `b -> top`.
    const def_opaque_expr = try parseConcreteGoal(
        &fixture,
        &theorem,
        &theorem_vars,
        "hold (c -> top)",
    );
    // A genuinely reducible (`@rewrite`) head: `sb` is not a transparent def, so
    // it has no rigid root and a `@rewrite` rule could rewrite it to any head.
    // The prune must abstain rather than treat `sb` as a rigid root (the
    // `resolveRigidHead` `rewrites_by_head` guard).
    const reducible_expr = try parseConcreteGoal(
        &fixture,
        &theorem,
        &theorem_vars,
        "sb a a (c -> top)",
    );
    // Same transparent-def head on both sides: head resolution sees `imp` on
    // each side and used to abstain. The body walk can still find the definite
    // mismatch `c` vs `b` away from the plug pair (`a`, `b`).
    const same_def_bad_expr = try parseConcreteGoal(
        &fixture,
        &theorem,
        &theorem_vars,
        "wrapimp c top",
    );
    const same_def_good_expr = try parseConcreteGoal(
        &fixture,
        &theorem,
        &theorem_vars,
        "wrapimp a top",
    );
    const same_def_goal = try parseConcreteGoal(
        &fixture,
        &theorem,
        &theorem_vars,
        "wrapimp b top",
    );
    // Cross-def/raw comparison: `box c` unfolds to `pair x (c -> top)`,
    // so comparing against raw `pair a (b -> top)` can reject on `c` vs `b`
    // while ignoring the hidden dummy argument.
    const cross_def_bad_expr = try parseConcreteGoal(
        &fixture,
        &theorem,
        &theorem_vars,
        "box c",
    );
    const cross_def_good_expr = try parseConcreteGoal(
        &fixture,
        &theorem,
        &theorem_vars,
        "box a",
    );
    const cross_def_goal = try parseConcreteGoal(
        &fixture,
        &theorem,
        &theorem_vars,
        "pair a (b -> top)",
    );

    const eq_fill = abstract_prune.Fill{ .hyp_index = 0, .ref_expr = eq_expr };
    try std.testing.expect(!abstract_prune.abstractInfeasible(
        &theorem,
        &context,
        view,
        goal_expr,
        &.{ eq_fill, .{ .hyp_index = 1, .ref_expr = good_expr } },
    ));
    try std.testing.expect(abstract_prune.abstractInfeasible(
        &theorem,
        &context,
        view,
        goal_expr,
        &.{ eq_fill, .{ .hyp_index = 1, .ref_expr = rigid_bad_expr } },
    ));
    try std.testing.expect(abstract_prune.abstractInfeasible(
        &theorem,
        &context,
        view,
        goal_expr,
        &.{ eq_fill, .{ .hyp_index = 1, .ref_expr = def_clash_expr } },
    ));
    try std.testing.expect(abstract_prune.abstractInfeasible(
        &theorem,
        &context,
        view,
        goal_expr,
        &.{ eq_fill, .{ .hyp_index = 1, .ref_expr = def_opaque_expr } },
    ));
    try std.testing.expect(!abstract_prune.abstractInfeasible(
        &theorem,
        &context,
        view,
        goal_expr,
        &.{ eq_fill, .{ .hyp_index = 1, .ref_expr = reducible_expr } },
    ));
    try std.testing.expect(abstract_prune.abstractInfeasible(
        &theorem,
        &context,
        view,
        same_def_goal,
        &.{ eq_fill, .{ .hyp_index = 1, .ref_expr = same_def_bad_expr } },
    ));
    try std.testing.expect(!abstract_prune.abstractInfeasible(
        &theorem,
        &context,
        view,
        same_def_goal,
        &.{ eq_fill, .{ .hyp_index = 1, .ref_expr = same_def_good_expr } },
    ));
    try std.testing.expect(abstract_prune.abstractInfeasible(
        &theorem,
        &context,
        view,
        cross_def_goal,
        &.{ eq_fill, .{ .hyp_index = 1, .ref_expr = cross_def_bad_expr } },
    ));
    try std.testing.expect(!abstract_prune.abstractInfeasible(
        &theorem,
        &context,
        view,
        cross_def_goal,
        &.{ eq_fill, .{ .hyp_index = 1, .ref_expr = cross_def_good_expr } },
    ));

    // Reducible-PLUG cases. The equation ref `wrapiff c c <-> b` binds the
    // plug/hole `a` to `wrapiff c c` — a transparent-def-headed (reducible) term,
    // so the raw-ExprId hole test is unreliable and the committed code bailed the
    // whole decl. The walk now switches to the head-aware hole guard.
    const eq_reducible_expr = try parseConcreteGoal(
        &fixture,
        &theorem,
        &theorem_vars,
        "wrapiff c c <-> b",
    );
    const eq_reducible_fill = abstract_prune.Fill{
        .hyp_index = 0,
        .ref_expr = eq_reducible_expr,
    };
    // The replaced hypothesis `wrapiff c c -> top`: the plug occurs at `imp`'s
    // first arg, in folded form here (and unfolds to `c <-> c`).
    const imp_wrap_expr = try parseConcreteGoal(
        &fixture,
        &theorem,
        &theorem_vars,
        "wrapiff c c -> top",
    );
    // PRUNE: conclusion `b <-> top` clashes at the top `imp` (hyp) vs `iff` (goal)
    // — a rigid-root clash at a node the head-aware guard proves is NOT the hole
    // (`imp`/`iff` ≠ the plug's resolved root `iff`/… is irrelevant: the clash is
    // above any hole). Replacing `wrapiff c c` by `b` in `wrapiff c c -> top`
    // yields `b -> top` (`imp`), never `b <-> top`, so the candidate is doomed.
    const goal_iff = try parseConcreteGoal(
        &fixture,
        &theorem,
        &theorem_vars,
        "b <-> top",
    );
    try std.testing.expect(abstract_prune.abstractInfeasible(
        &theorem,
        &context,
        view,
        goal_iff,
        &.{ eq_reducible_fill, .{ .hyp_index = 1, .ref_expr = imp_wrap_expr } },
    ));
    // ABSTAIN: the genuinely valid replacement — `wrapiff c c -> top` with
    // `wrapiff c c` ↦ `b` is exactly the goal `b -> top`. At the plug position the
    // head-aware guard sees the folded occurrence share the plug's rigid root and
    // holds no opinion, so the prune must NOT fire.
    try std.testing.expect(!abstract_prune.abstractInfeasible(
        &theorem,
        &context,
        view,
        goal_expr,
        &.{ eq_reducible_fill, .{ .hyp_index = 1, .ref_expr = imp_wrap_expr } },
    ));
}

test "context pruner counts absent members against the discharge budget" {
    const mm0_src =
        \\delimiter $ ( ) , $;
        \\strict provable sort wff;
        \\sort ctx;
        \\term ctx_eq (G H: ctx): wff;
        \\term emp: ctx;
        \\notation emp: ctx = ($_$:max);
        \\--| @acui ctx_assoc ctx_comm emp ctx_idem
        \\term join (G H: ctx): ctx;
        \\infixl join: $,$ prec 5;
        \\term hyp (p: wff): ctx;
        \\coercion hyp: wff > ctx;
        \\term nd (G: ctx) (p: wff): wff;
        \\infixl nd: $⊢$ prec 0;
        \\term A: wff;
        \\term B: wff;
        \\term C: wff;
        \\term D: wff;
        \\term Q: wff;
        \\axiom ctx_assoc (G H K: ctx): $ ctx_eq ((G , H) , K) (G , (H , K)) $;
        \\axiom ctx_comm (G H: ctx): $ ctx_eq (G , H) (H , G) $;
        \\axiom ctx_idem (G: ctx): $ ctx_eq (G , G) G $;
        \\--| @view (G H: ctx) (p q r: wff): $ G ⊢ p $ > $ H ⊢ q $ > $ G , H ⊢ r $
        \\axiom carry (G H: ctx) (p q r: wff):
        \\  $ G ⊢ p $ > $ H ⊢ q $ > $ G , H ⊢ r $;
        \\--| @view (G H: ctx) (p c: wff): $ G ⊢ p $ > $ H , p ⊢ c $ > $ G , H ⊢ c $
        \\axiom discharge (G H: ctx) (p c: wff):
        \\  $ G ⊢ p $ > $ H , p ⊢ c $ > $ G , H ⊢ c $;
        \\--| @view (G H K: ctx) (p q r: wff): $ G ⊢ p $ > $ K ⊢ q $ > $ G , H ⊢ r $
        \\axiom drop (G H K: ctx) (p q r: wff):
        \\  $ G ⊢ p $ > $ K ⊢ q $ > $ G , H ⊢ r $;
        \\theorem t (G H: ctx): $ G , H ⊢ Q $;
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

    const carry_view = fixture.views.get(
        fixture.env.getRuleId("carry") orelse return error.MissingRule,
    ) orelse return error.MissingView;
    const discharge_view = fixture.views.get(
        fixture.env.getRuleId("discharge") orelse return error.MissingRule,
    ) orelse return error.MissingView;

    const drop_view = fixture.views.get(
        fixture.env.getRuleId("drop") orelse return error.MissingRule,
    ) orelse return error.MissingView;

    const carry_info = context_prune.analyzeView(&context, carry_view) orelse
        return error.AnalyzeFailed;
    const discharge_info = context_prune.analyzeView(&context, discharge_view) orelse
        return error.AnalyzeFailed;
    const drop_info = context_prune.analyzeView(&context, drop_view) orelse
        return error.AnalyzeFailed;
    // `carry` keeps every hypothesis context member; `discharge`'s second hyp
    // (`H , p`) drops the coerced `hyp(p)`, so its budget is one.
    try std.testing.expectEqual(@as(?u8, 0), carry_info.hyp_budgets[1]);
    try std.testing.expectEqual(@as(?u8, 1), discharge_info.hyp_budgets[1]);
    // `drop`'s second hyp context (`K`) is a bare binder absent from the
    // conclusion context (`G , H`): it discharges a WHOLE sub-context, which can
    // stand for unboundedly many concrete members, so the budget is null
    // (abstain — no prune may fire for that hypothesis).
    try std.testing.expectEqual(@as(?u8, null), drop_info.hyp_budgets[1]);

    const goal = try parseConcreteGoal(&fixture, &theorem, &theorem_vars, "A , B ⊢ Q");
    const ref_B = try parseConcreteGoal(&fixture, &theorem, &theorem_vars, "B ⊢ Q");
    const ref_C = try parseConcreteGoal(&fixture, &theorem, &theorem_vars, "C ⊢ Q");
    const ref_BC = try parseConcreteGoal(&fixture, &theorem, &theorem_vars, "B , C ⊢ Q");
    const ref_CD = try parseConcreteGoal(&fixture, &theorem, &theorem_vars, "C , D ⊢ Q");

    // Non-discharging (budget 0): a ref-context member absent from the goal
    // context (`C`) prunes; one already present (`B`) abstains.
    try std.testing.expect(context_prune.contextInfeasible(
        &theorem,
        &context,
        carry_info,
        goal,
        &.{.{ .hyp_index = 1, .ref_expr = ref_C }},
        null,
    ));
    try std.testing.expect(!context_prune.contextInfeasible(
        &theorem,
        &context,
        carry_info,
        goal,
        &.{.{ .hyp_index = 1, .ref_expr = ref_B }},
        null,
    ));

    // Discharging (budget 1): one absent member (`C`, the discharged assumption)
    // is under budget and abstains; two absent members (`C`, `D`) exceed it.
    try std.testing.expect(!context_prune.contextInfeasible(
        &theorem,
        &context,
        discharge_info,
        goal,
        &.{.{ .hyp_index = 1, .ref_expr = ref_BC }},
        null,
    ));
    try std.testing.expect(context_prune.contextInfeasible(
        &theorem,
        &context,
        discharge_info,
        goal,
        &.{.{ .hyp_index = 1, .ref_expr = ref_CD }},
        null,
    ));

    // Null budget (abstain): `drop`'s second hyp could discharge any number of
    // members, so even a ref-context full of absent members (`C , D`) must NOT
    // prune — the analyzer holds no opinion on that hypothesis.
    try std.testing.expect(!context_prune.contextInfeasible(
        &theorem,
        &context,
        drop_info,
        goal,
        &.{.{ .hyp_index = 1, .ref_expr = ref_CD }},
        null,
    ));

    // The ACUI unit (`emp`, written `_`) contributes no member: a ref context
    // `B , emp` flattens to just `B`, which is present in the goal, so the
    // budget-0 `carry` hyp abstains rather than counting `emp` as absent.
    const ref_B_emp = try parseConcreteGoal(&fixture, &theorem, &theorem_vars, "B , _ ⊢ Q");
    try std.testing.expect(!context_prune.contextInfeasible(
        &theorem,
        &context,
        carry_info,
        goal,
        &.{.{ .hyp_index = 1, .ref_expr = ref_B_emp }},
        null,
    ));
}

test "raw context pruner matches discharged member shape" {
    const mm0_src =
        \\delimiter $ ( ) , $;
        \\strict provable sort wff;
        \\sort ctx;
        \\term ctx_eq (G H: ctx): wff;
        \\term emp: ctx;
        \\notation emp: ctx = ($_$:max);
        \\--| @acui ctx_assoc ctx_comm emp ctx_idem
        \\term join (G H: ctx): ctx;
        \\infixl join: $,$ prec 5;
        \\term hyp (p: wff): ctx;
        \\coercion hyp: wff > ctx;
        \\term nd (G: ctx) (p: wff): wff;
        \\infixl nd: $⊢$ prec 0;
        \\term eq (p q: wff): wff;
        \\infixl eq: $=$ prec 10;
        \\term Q: wff;
        \\term T: wff;
        \\term U: wff;
        \\term X: wff;
        \\axiom ctx_assoc (G H K: ctx): $ ctx_eq ((G , H) , K) (G , (H , K)) $;
        \\axiom ctx_comm (G H: ctx): $ ctx_eq (G , H) (H , G) $;
        \\axiom ctx_idem (G: ctx): $ ctx_eq (G , G) G $;
        \\axiom inst (G: ctx) {x: wff} (t a: wff x):
        \\  $ G ⊢ t $ > $ G , x = t ⊢ a $ > $ G ⊢ a $;
        \\theorem th (G: ctx) {X: wff}: $ G ⊢ Q $;
    ;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    var fixture = try fixtureFor(allocator, mm0_src, "th");
    var theorem = TheoremContext.init(allocator);
    defer theorem.deinit();
    try theorem.seedAssertion(fixture.assertion);
    var theorem_vars = try Check.buildTheoremVarMap(allocator, fixture.assertion);
    defer theorem_vars.deinit();
    var harness = ContextHarness.init(allocator);
    defer harness.deinit();
    const context = harness.context(&fixture);

    const rule_id = fixture.env.getRuleId("inst") orelse return error.MissingRule;
    const rule = fixture.env.rules.items[rule_id];
    const info = context_prune.analyzeRule(&context, rule) orelse
        return error.AnalyzeFailed;
    try std.testing.expectEqual(@as(?u8, 1), info.hyp_budgets[1]);

    const goal = try parseConcreteGoal(&fixture, &theorem, &theorem_vars, "G ⊢ Q");
    const ref_good = try parseConcreteGoal(
        &fixture,
        &theorem,
        &theorem_vars,
        "G , X = T ⊢ Q",
    );
    const ref_bad = try parseConcreteGoal(
        &fixture,
        &theorem,
        &theorem_vars,
        "G , X = U ⊢ Q",
    );
    const t_jdg = try parseConcreteGoal(&fixture, &theorem, &theorem_vars, "G ⊢ T");
    const t_expr = theorem.interner.node(t_jdg).app.args[1];
    var bindings = [_]?ExprId{null} ** 4;
    bindings[2] = t_expr;

    try std.testing.expect(!context_prune.contextInfeasible(
        &theorem,
        &context,
        info,
        goal,
        &.{.{ .hyp_index = 1, .ref_expr = ref_good }},
        &bindings,
    ));
    try std.testing.expect(context_prune.contextInfeasible(
        &theorem,
        &context,
        info,
        goal,
        &.{.{ .hyp_index = 1, .ref_expr = ref_bad }},
        &bindings,
    ));

    // Idempotent case: the selected ref contributes no absent member because
    // the goal already carries `X = T`. With `x` still open, requiring explicit
    // support for the bound-binder discharge prunes `x = U` but keeps `x = T`.
    const goal_with_eq = try parseConcreteGoal(
        &fixture,
        &theorem,
        &theorem_vars,
        "G , X = T ⊢ Q",
    );
    const u_jdg = try parseConcreteGoal(&fixture, &theorem, &theorem_vars, "G ⊢ U");
    const u_expr = theorem.interner.node(u_jdg).app.args[1];
    bindings[2] = u_expr;
    try std.testing.expect(context_prune.contextInfeasible(
        &theorem,
        &context,
        info,
        goal_with_eq,
        &.{.{ .hyp_index = 1, .ref_expr = goal_with_eq }},
        &bindings,
    ));
    bindings[2] = t_expr;
    try std.testing.expect(!context_prune.contextInfeasible(
        &theorem,
        &context,
        info,
        goal_with_eq,
        &.{.{ .hyp_index = 1, .ref_expr = goal_with_eq }},
        &bindings,
    ));
}

fn parseConcreteGoal(
    fixture: anytype,
    theorem: *TheoremContext,
    theorem_vars: *NameExprMap,
    text: []const u8,
) !ExprId {
    return switch (try parseGoal(fixture, theorem, theorem_vars, text)) {
        .concrete => |expr| expr,
        .implicit_whole_conclusion, .holey => error.ExpectedConcreteGoal,
    };
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
    // The raw hypothesis of `ex_intro` is `[x/t] p` — substitution-headed.
    // The theorem hypothesis `P c` does not have `sb_f` at the head, so both
    // the ref-index lookup and per-hyp matching using the raw template skip
    // it, leaving `exact?` with no candidate. The @view exposes the
    // hypothesis as just `q` (an unconstrained wff), making the ref
    // discoverable. The full validator then accepts `ex_intro [l1]` via the
    // `sb_f_P` / `sb_s_var` rewrite axioms (with the help of `P_congr`).
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
    try expectFirstExactRefs(
        mm0_src,
        proof_src,
        "prove_exists",
        "E x (P x)",
        1,
        "ex_intro",
        &[_]ProofScript.Ref{.{ .line = .{
            .label = "l1",
            .span = .{ .start = 0, .end = 0 },
        } }},
    );
}

// ============================================================
// Single-layer forward saturation with universal metas
// (META.md). Forward firing is gated on `@auto forward` metadata
// and runs only inside the `auto?` generation driver.
// ============================================================
