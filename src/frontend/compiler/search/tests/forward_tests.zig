const helpers = @import("./helpers.zig");
const std = helpers.std;
const types = helpers.types;
const source = helpers.source;
const Witness = helpers.Witness;
const MetaStore = helpers.MetaStore;
const ExprId = helpers.ExprId;
const TheoremContext = helpers.TheoremContext;
const Goal = helpers.Goal;
const exact = helpers.exact;
const tryCandidate = helpers.tryCandidate;
const fixtureFor = helpers.fixtureFor;
const ContextHarness = helpers.ContextHarness;
const tunables = helpers.tunables;

// Concrete forward chain: `pq` is fired forward on hyp #1 (`P K`),
// deriving `Q K` with recipe `pq (x := $ K $) [#1]`. The backward
// `qr` premise `Q x` is open (x does not appear in the conclusion
// `R`), so neither the pool nor concrete generation can fill it —
// only the derived ref can.
const fwd_concrete_mm0 =
    \\delimiter $ ( ) $;
    \\provable sort wff;
    \\sort obj;
    \\term P (x: obj): wff;
    \\term Q (x: obj): wff;
    \\term R: wff;
    \\term K: obj;
    \\term pr (a b: obj): obj;
    \\--| @auto forward
    \\axiom pq (x: obj): $ P x $ > $ Q x $;
    \\--| @auto forward
    \\axiom pq2 (x y: obj): $ P x $ > $ Q (pr x y) $;
    \\axiom qr (x: obj): $ Q x $ > $ R $;
    \\theorem t: $ P K $ > $ R $;
;

test "forward saturation derives a concrete ref usable by auto" {
    const proof_src =
        \\t
        \\----
        \\l1: $ R $ by auto?
    ;
    const offset = std.mem.indexOf(u8, proof_src, "auto?") orelse
        return error.MissingNeedle;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    var suggestions = try source.suggestionsAtSourceOffset(
        arena.allocator(),
        fwd_concrete_mm0,
        proof_src,
        offset,
        .{ .counters = &counters, .generate = .{ .enabled = true } },
    );
    defer suggestions.deinit();

    var found = false;
    for (suggestions.items) |item| {
        if (std.mem.eql(
            u8,
            item.replacement,
            "qr [pq (x := $ K $) [#1]]",
        )) found = true;
    }
    try std.testing.expect(found);
    // `pq` fired on `P K` concretely. `pq2`'s unbound conclusion binder `y`
    // is deferred as a universal meta, deriving the family fact
    // `Q (pr K ?y)` — nothing solves `?y` here (the goal `R` never shows a
    // witness), so the family fact fails cleanly and adds no suggestion.
    try std.testing.expectEqual(@as(usize, 2), counters.derived_ref_count);
    try std.testing.expect(counters.forward_rule_attempts > 0);
    try std.testing.expectEqual(@as(usize, 1), counters.universal_metas_created);
}

// Family-fact derivation from an unbound conclusion binder (the bot_elim
// shape): `seq g bot > seq g a` fires forward on a `⊥`-style fact as
// `seq G ?a`, and a later goal solves the hole positionally — the same
// use-time discipline as a `@recover`-deferred witness. The `anything`
// rule's conclusion is a bare binder, so its surface would be a bare meta
// (an absorber, not a fact): it must derive nothing.
const fwd_family_mm0 =
    \\delimiter $ ( ) $;
    \\provable sort jdg;
    \\sort wff;
    \\sort ctx;
    \\term seq (g: ctx) (a: wff): jdg;
    \\term bot: wff;
    \\term G: ctx;
    \\term q: wff;
    \\--| @auto forward
    \\axiom bot_elim (g: ctx) (a: wff): $ seq g bot $ > $ seq g a $;
    \\--| @auto forward
    \\axiom anything (j: jdg) (g: ctx): $ seq g bot $ > $ j $;
    \\theorem t: $ seq G bot $ > $ seq G q $;
;

test "forward family fact from unbound conclusion binder solves at the goal" {
    const proof_src =
        \\t
        \\----
        \\l1: $ seq G q $ by auto?
    ;
    const offset = std.mem.indexOf(u8, proof_src, "auto?") orelse
        return error.MissingNeedle;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    var suggestions = try source.suggestionsAtSourceOffset(
        arena.allocator(),
        fwd_family_mm0,
        proof_src,
        offset,
        .{ .counters = &counters, .generate = .{ .enabled = true } },
    );
    defer suggestions.deinit();

    var found = false;
    for (suggestions.items) |item| {
        if (std.mem.eql(
            u8,
            item.replacement,
            "bot_elim (g := $ G $, a := $ q $) [#1]",
        )) found = true;
    }
    try std.testing.expect(found);
    // `bot_elim` derived the family fact; `anything`'s bare-meta surface
    // was rejected by the absorber guard.
    try std.testing.expectEqual(@as(usize, 1), counters.derived_ref_count);
}

// Forward JOIN grounding a nested source's universal meta. `genimp` fires on
// `Trigger`, deferring its unbound conclusion binder `x` to derive the universal
// FAMILY fact `imp (P ?x) (Q ?x)`. `mp` (forward) then joins that family's
// major premise with the concrete `P c`: matching the already-bound `a := P ?x`
// against `P c` grounds `?x := c` in the join overlay, so the consequent
// dereferences to the concrete fact `Q c` (`?x := c` baked as a pin on `Q c`'s
// recipe). The backward `qr` premise `Q x` (x absent from its conclusion) can
// only be filled by that derived `Q c` — so finding the proof at all proves the
// join produced a concrete consequent (without the join, no `Q` fact exists).
const fwd_join_mm0 =
    \\delimiter $ ( ) $;
    \\provable sort wff;
    \\sort obj;
    \\term imp (a b: wff): wff;
    \\term P (x: obj): wff;
    \\term Q (x: obj): wff;
    \\term Trigger: wff;
    \\term Goal: wff;
    \\term c: obj;
    \\--| @auto forward
    \\axiom genimp (x: obj): $ Trigger $ > $ imp (P x) (Q x) $;
    \\--| @auto forward
    \\axiom mp (a b: wff): $ imp a b $ > $ a $ > $ b $;
    \\axiom qr (x: obj): $ Q x $ > $ Goal $;
    \\theorem t: $ Trigger $ > $ P c $ > $ Goal $;
;

test "forward join grounds a nested family meta into a concrete fact" {
    const proof_src =
        \\t
        \\----
        \\l1: $ Goal $ by auto?
    ;
    const offset = std.mem.indexOf(u8, proof_src, "auto?") orelse
        return error.MissingNeedle;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    var suggestions = try source.suggestionsAtSourceOffset(
        arena.allocator(),
        fwd_join_mm0,
        proof_src,
        offset,
        .{ .counters = &counters, .generate = .{ .enabled = true } },
    );
    defer suggestions.deinit();

    // The witness `c` must ride the join into the nested family instance: the
    // recipe renders `genimp (x := $ c $)` (the pin), wrapped by `mp` and `qr`.
    var found = false;
    for (suggestions.items) |item| {
        if (std.mem.indexOf(u8, item.replacement, "genimp (x := $ c $)") != null and
            std.mem.indexOf(u8, item.replacement, "mp ") != null)
        {
            found = true;
        }
    }
    try std.testing.expect(found);
    // Two derived facts: the `imp (P ?x) (Q ?x)` family and the join's `Q c`.
    try std.testing.expectEqual(@as(usize, 2), counters.derived_ref_count);
}

// Negative: the forward join must not FABRICATE a witness. Same chain as the
// join test but with NO base fact — only the implication families `imp (P ?x)
// (Q ?x)` and `imp (Q ?y) (S ?y)` are derivable from `Trigger`, and nothing
// seeds a concrete `P`/`Q`/`S`. So `Goal` (which needs some `S x`) is genuinely
// underivable (countermodel: one element, P=Q=S false). The engine must return
// no proof — search may only PROPOSE; `tryCandidate` validates, so a returned
// suggestion would have to be a real proof, which cannot exist here.
const fwd_no_anchor_mm0 =
    \\delimiter $ ( ) $;
    \\provable sort wff;
    \\sort obj;
    \\term imp (a b: wff): wff;
    \\term P (x: obj): wff;
    \\term Q (x: obj): wff;
    \\term S (x: obj): wff;
    \\term Trigger: wff;
    \\term Goal: wff;
    \\--| @auto forward
    \\axiom genPQ (x: obj): $ Trigger $ > $ imp (P x) (Q x) $;
    \\--| @auto forward
    \\axiom genQS (x: obj): $ Trigger $ > $ imp (Q x) (S x) $;
    \\--| @auto forward
    \\axiom mp (a b: wff): $ imp a b $ > $ a $ > $ b $;
    \\axiom sr (x: obj): $ S x $ > $ Goal $;
    \\theorem t: $ Trigger $ > $ Goal $;
;

test "forward join does not fabricate a witness without a base fact" {
    const proof_src =
        \\t
        \\----
        \\l1: $ Goal $ by auto?
    ;
    const offset = std.mem.indexOf(u8, proof_src, "auto?") orelse
        return error.MissingNeedle;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    var suggestions = try source.suggestionsAtSourceOffset(
        arena.allocator(),
        fwd_no_anchor_mm0,
        proof_src,
        offset,
        .{ .counters = &counters, .generate = .{ .enabled = true } },
    );
    defer suggestions.deinit();

    // No proof exists: the engine must offer none (and not loop/crash trying to
    // invent the impossible witness). The two implication families derive; the
    // join finds no concrete antecedent to fire on.
    try std.testing.expectEqual(@as(usize, 0), suggestions.items.len);
}

test "forward premise matching unfolds nested concrete defs on demand" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\sort obj;
        \\term P (x: obj): wff;
        \\term Q (x: obj): wff;
        \\term box (p: wff): wff;
        \\term R: wff;
        \\term K: obj;
        \\def folded (x: obj): wff = $ P x $;
        \\--| @auto forward
        \\axiom pq_box (x: obj): $ box (P x) $ > $ Q x $;
        \\axiom qr (x: obj): $ Q x $ > $ R $;
        \\theorem t: $ box (folded K) $ > $ R $;
    ;
    const proof_src =
        \\t
        \\----
        \\l1: $ R $ by auto?
    ;
    const offset = std.mem.indexOf(u8, proof_src, "auto?") orelse
        return error.MissingNeedle;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    var suggestions = try source.suggestionsAtSourceOffset(
        arena.allocator(),
        mm0_src,
        proof_src,
        offset,
        .{ .counters = &counters, .generate = .{ .enabled = true } },
    );
    defer suggestions.deinit();

    var found = false;
    for (suggestions.items) |item| {
        if (std.mem.eql(
            u8,
            item.replacement,
            "qr [pq_box (x := $ K $) [#1]]",
        )) found = true;
    }
    try std.testing.expect(found);
    try std.testing.expectEqual(@as(usize, 1), counters.derived_ref_count);
    try std.testing.expect(counters.forward_match_tuples > 0);
}

test "exact does not run forward saturation or use derived refs" {
    const proof_src =
        \\t
        \\----
        \\l1: $ R $ by exact?
    ;
    const offset = std.mem.indexOf(u8, proof_src, "exact?") orelse
        return error.MissingNeedle;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    var suggestions = try source.suggestionsAtSourceOffset(
        arena.allocator(),
        fwd_concrete_mm0,
        proof_src,
        offset,
        .{ .counters = &counters, .generate = .{ .enabled = true } },
    );
    defer suggestions.deinit();
    try std.testing.expectEqual(@as(usize, 0), suggestions.items.len);
    try std.testing.expectEqual(@as(usize, 0), counters.derived_ref_count);
    try std.testing.expectEqual(@as(usize, 0), counters.forward_rule_attempts);
}

// Universal-meta theory: a self-contained copy of the bench `all_elim`
// theory (no `mono` def), so the forward premise match is DIRECT (no
// unfold) and the derived shape carries the witness meta at two
// positions: `pair f ?t = pair ?t f`.
const fwd_universal_mm0 =
    \\delimiter $ ( ) [ / ] $;
    \\provable sort wff;
    \\sort obj;
    \\term imp (a b: wff): wff;
    \\infixr imp: $→$ prec 25;
    \\term iff (a b: wff): wff;
    \\infixr iff: $↔$ prec 20;
    \\term all {x: obj} (p: wff x): wff;
    \\prefix all: $∀$ prec 41;
    \\term eq (a b: obj): wff;
    \\infixl eq: $=$ prec 35;
    \\term pair (a b: obj): obj;
    \\term sb_t {x: obj} (t: obj x) (a: obj x): obj;
    \\notation sb_t {x: obj} (t: obj x) (a: obj x): obj =
    \\  ($subst$:41) x ($/$:0) t a;
    \\term sb_f {x: obj} (t: obj x) (p: wff x): wff;
    \\notation sb_f {x: obj} (t: obj x) (p: wff x): wff =
    \\  ($[$:41) x ($/$:0) t ($]$:0) p;
    \\--| @relation wff iff iff_refl iff_trans iff_sym iff_mp
    \\axiom iff_refl (a: wff): $ a ↔ a $;
    \\axiom iff_trans (a b c: wff): $ a ↔ b $ > $ b ↔ c $ > $ a ↔ c $;
    \\axiom iff_sym (a b: wff): $ a ↔ b $ > $ b ↔ a $;
    \\axiom iff_mp (a b: wff): $ a ↔ b $ > $ a $ > $ b $;
    \\--| @relation obj eq eq_refl eq_trans eq_sym _
    \\axiom eq_refl (a: obj): $ a = a $;
    \\axiom eq_trans (a b c: obj): $ a = b $ > $ b = c $ > $ a = c $;
    \\axiom eq_sym (a b: obj): $ a = b $ > $ b = a $;
    \\--| @congr
    \\axiom pair_congr (a b c d: obj):
    \\  $ a = b $ > $ c = d $ > $ pair a c = pair b d $;
    \\--| @congr
    \\axiom eq_congr (a b c d: obj):
    \\  $ a = b $ > $ c = d $ > $ (a = c) ↔ (b = d) $;
    \\--| @rewrite
    \\axiom sb_t_var {x: obj} (t: obj x): $ subst x / t x = t $;
    \\--| @rewrite
    \\axiom sb_t_pair {x: obj} (t: obj x) (a b: obj x):
    \\  $ subst x / t (pair a b) = pair (subst x / t a) (subst x / t b) $;
    \\--| @rewrite
    \\axiom sb_t_irrel {x: obj} (t: obj x) (a: obj): $ subst x / t a = a $;
    \\--| @rewrite
    \\axiom sb_f_eq {x: obj} (t: obj x) (a b: obj x):
    \\  $ [x/t] (a = b) ↔ (subst x / t a = subst x / t b) $;
    \\--| @view {x: obj} (t: obj x) (p: wff x) (q: wff): $ ∀ x p $ > $ q $
    \\--| @recover t q p x
    \\--| @auto forward
    \\axiom all_elim {x: obj} (t: obj x) (p: wff x):
    \\  $ ∀ x p $ > $ [x/t] p $;
    \\theorem fwd_match {x u: obj} (f: obj):
    \\  $ ∀ x (pair f x = pair x f) $ > $ pair f u = pair u f $;
    \\theorem fwd_mismatch {x u v: obj} (f: obj):
    \\  $ ∀ x (pair f x = pair x f) $ > $ pair f u = pair v f $;
;

test "derived ref with universal meta matches a later concrete goal" {
    const proof_src =
        \\fwd_match
        \\---------
        \\l1: $ pair f u = pair u f $ by auto?
    ;
    const offset = std.mem.indexOf(u8, proof_src, "auto?") orelse
        return error.MissingNeedle;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    var suggestions = try source.suggestionsAtSourceOffset(
        arena.allocator(),
        fwd_universal_mm0,
        proof_src,
        offset,
        .{ .counters = &counters, .generate = .{ .enabled = true } },
    );
    defer suggestions.deinit();

    // The goal-direct derived use renders explicit bindings for the solved
    // universal meta (`t := u`) and the premise-match binders. The plain
    // backward `all_elim [#1]` is also offered (supported boundary).
    var found_derived = false;
    var found_direct = false;
    for (suggestions.items) |item| {
        if (std.mem.eql(
            u8,
            item.replacement,
            "all_elim (x := $ x $, t := $ u $, " ++
                "p := $ pair f x = pair x f $) [#1]",
        )) found_derived = true;
        if (std.mem.eql(u8, item.replacement, "all_elim [#1]")) {
            found_direct = true;
        }
    }
    try std.testing.expect(found_direct);
    try std.testing.expect(found_derived);
    try std.testing.expectEqual(@as(usize, 1), counters.derived_ref_count);
    try std.testing.expectEqual(@as(usize, 1), counters.universal_metas_created);
    // The repeated meta occurrence (`pair f ?t` / `pair ?t f`) was assigned
    // once and checked consistent at the second position.
    try std.testing.expect(counters.meta_assignments > 0);
    try std.testing.expect(counters.meta_rollbacks > 0);
}

test "inconsistent repeated universal meta occurrence rejects the use" {
    const proof_src =
        \\fwd_mismatch
        \\------------
        \\l1: $ pair f u = pair v f $ by auto?
    ;
    const offset = std.mem.indexOf(u8, proof_src, "auto?") orelse
        return error.MissingNeedle;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    var suggestions = try source.suggestionsAtSourceOffset(
        arena.allocator(),
        fwd_universal_mm0,
        proof_src,
        offset,
        .{ .counters = &counters, .generate = .{ .enabled = true } },
    );
    defer suggestions.deinit();
    // The derived shape demands the same witness at both positions; the goal
    // shows u and v, so no derived use (and no other proof) exists. The
    // forward layer still ran and derived the ref — bounded clean no-result.
    try std.testing.expectEqual(@as(usize, 0), suggestions.items.len);
    try std.testing.expectEqual(@as(usize, 1), counters.derived_ref_count);
}

test "auto solves the nested forward-instantiation flagship (Stage 7)" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    const mm0_src = try std.fs.cwd().readFileAlloc(
        allocator,
        "tests/search_bench_cases/all_elim_forward.mm0",
        std.math.maxInt(usize),
    );
    const proof_src =
        \\all_elim_forward_inst
        \\---------------------
        \\l1: $ (pair f u = pair f v) → (u = v) $ by auto?
    ;
    const offset = std.mem.indexOf(u8, proof_src, "auto?") orelse
        return error.MissingNeedle;
    var counters = types.SearchCounters{};
    var suggestions = try source.suggestionsAtSourceOffset(
        allocator,
        mm0_src,
        proof_src,
        offset,
        .{ .counters = &counters, .generate = .{ .enabled = true } },
    );
    defer suggestions.deinit();

    // The forward layer unfolds `mono f` (transparent binder def), defers the
    // witness as a universal meta, and the derived ref fills the backward
    // `all_elim` premise slot; the `@recover` correspondence solves `?t := u`
    // from the goal. The hidden unfold dummies are named from the theorem's
    // unused bound vars (a, b).
    var found = false;
    for (suggestions.items) |item| {
        if (std.mem.eql(
            u8,
            item.replacement,
            "all_elim [all_elim (x := $ a $, t := $ u $, " ++
                "p := $ ∀ b (pair f a = pair f b → a = b) $) [#1]]",
        )) found = true;
    }
    try std.testing.expect(found);
    try std.testing.expect(counters.derived_ref_count > 0);
    try std.testing.expect(counters.universal_metas_created > 0);
    try std.testing.expect(counters.forward_rule_attempts > 0);
}

// Full flagship theory (bench copy) plus a conjunction, so one assembly
// must select the SAME derived ref twice at two different witnesses.
const fwd_twice_mm0 =
    \\delimiter $ ( ) [ / ] $;
    \\provable sort wff;
    \\sort obj;
    \\term imp (a b: wff): wff;
    \\infixr imp: $→$ prec 25;
    \\term iff (a b: wff): wff;
    \\infixr iff: $↔$ prec 20;
    \\term and (a b: wff): wff;
    \\infixl and: $∧$ prec 21;
    \\term all {x: obj} (p: wff x): wff;
    \\prefix all: $∀$ prec 41;
    \\term eq (a b: obj): wff;
    \\infixl eq: $=$ prec 35;
    \\term pair (a b: obj): obj;
    \\term sb_t {x: obj} (t: obj x) (a: obj x): obj;
    \\notation sb_t {x: obj} (t: obj x) (a: obj x): obj =
    \\  ($subst$:41) x ($/$:0) t a;
    \\term sb_f {x: obj} (t: obj x) (p: wff x): wff;
    \\notation sb_f {x: obj} (t: obj x) (p: wff x): wff =
    \\  ($[$:41) x ($/$:0) t ($]$:0) p;
    \\--| @relation wff iff iff_refl iff_trans iff_sym iff_mp
    \\axiom iff_refl (a: wff): $ a ↔ a $;
    \\axiom iff_trans (a b c: wff): $ a ↔ b $ > $ b ↔ c $ > $ a ↔ c $;
    \\axiom iff_sym (a b: wff): $ a ↔ b $ > $ b ↔ a $;
    \\axiom iff_mp (a b: wff): $ a ↔ b $ > $ a $ > $ b $;
    \\--| @relation obj eq eq_refl eq_trans eq_sym _
    \\axiom eq_refl (a: obj): $ a = a $;
    \\axiom eq_trans (a b c: obj): $ a = b $ > $ b = c $ > $ a = c $;
    \\axiom eq_sym (a b: obj): $ a = b $ > $ b = a $;
    \\axiom and_intro (p q: wff): $ p $ > $ q $ > $ p ∧ q $;
    \\--| @congr
    \\axiom pair_congr (a b c d: obj):
    \\  $ a = b $ > $ c = d $ > $ pair a c = pair b d $;
    \\--| @congr
    \\axiom eq_congr (a b c d: obj):
    \\  $ a = b $ > $ c = d $ > $ (a = c) ↔ (b = d) $;
    \\--| @congr
    \\axiom imp_congr (a b c d: wff):
    \\  $ a ↔ b $ > $ c ↔ d $ > $ (a → c) ↔ (b → d) $;
    \\--| @congr
    \\axiom all_congr {x: obj} (p q: wff x):
    \\  $ p ↔ q $ > $ ∀ x p ↔ ∀ x q $;
    \\--| @rewrite
    \\axiom sb_t_var {x: obj} (t: obj x): $ subst x / t x = t $;
    \\--| @rewrite
    \\axiom sb_t_pair {x: obj} (t: obj x) (a b: obj x):
    \\  $ subst x / t (pair a b) = pair (subst x / t a) (subst x / t b) $;
    \\--| @rewrite
    \\axiom sb_t_other {x y: obj} (t: obj x): $ subst x / t y = y $;
    \\--| @rewrite
    \\axiom sb_t_irrel {x: obj} (t: obj x) (a: obj): $ subst x / t a = a $;
    \\--| @rewrite
    \\axiom sb_f_eq {x: obj} (t: obj x) (a b: obj x):
    \\  $ [x/t] (a = b) ↔ (subst x / t a = subst x / t b) $;
    \\--| @rewrite
    \\axiom sb_f_imp {x: obj} (t: obj x) (p q: wff x):
    \\  $ [x/t] (p → q) ↔ ([x/t] p → [x/t] q) $;
    \\--| @rewrite
    \\axiom sb_f_all {x y: obj} (t: obj x) (p: wff x y):
    \\  $ [x/t] (∀ y p) ↔ ∀ y ([x/t] p) $;
    \\--| @view {x: obj} (t: obj x) (p: wff x) (q: wff): $ ∀ x p $ > $ q $
    \\--| @recover t q p x
    \\--| @auto forward
    \\axiom all_elim {x: obj} (t: obj x) (p: wff x):
    \\  $ ∀ x p $ > $ [x/t] p $;
    \\def mono {.a .b: obj} (f: obj): wff =
    \\  $ ∀ a ∀ b ((pair f a = pair f b) → (a = b)) $;
    \\theorem fwd_twice {u v a b : obj} (f: obj):
    \\  $ mono f $ >
    \\  $ ((pair f u = pair f v) → (u = v)) ∧ ((pair f a = pair f b) → (a = b)) $;
    \\theorem fwd_nested {u v a b: obj} (f: obj):
    \\  $ ∀ a ∀ b ((pair f a = pair f b) → (a = b)) $ >
    \\  $ (pair f u = pair f v) → (u = v) $;
;

test "same derived ref is selected twice at two different witnesses" {
    const proof_src =
        \\fwd_twice
        \\---------
        \\l1: $ ((pair f u = pair f v) → (u = v)) ∧ ((pair f a = pair f b) → (a = b)) $ by auto?
    ;
    const offset = std.mem.indexOf(u8, proof_src, "auto?") orelse
        return error.MissingNeedle;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    var suggestions = try source.suggestionsAtSourceOffset(
        arena.allocator(),
        fwd_twice_mm0,
        proof_src,
        offset,
        .{ .counters = &counters, .generate = .{ .enabled = true } },
    );
    defer suggestions.deinit();

    // The single-layer derived ref (all_elim fired once on `mono f`) is used
    // twice in the same assembly with independent transient instantiations:
    // `?t := u` in the left conjunct and `?t := a` in the right.
    var found = false;
    for (suggestions.items) |item| {
        const r = item.replacement;
        if (std.mem.startsWith(u8, r, "and_intro [") and
            std.mem.indexOf(u8, r, "t := $ u $") != null and
            std.mem.indexOf(u8, r, "t := $ a $") != null)
        {
            found = true;
        }
    }
    try std.testing.expect(found);
    // Multi-layer saturation also fires `all_elim` on the layer-1
    // shape `∀ b (…?t…)`, deriving the fully instantiated two-hole surface
    // as a second fact.
    try std.testing.expectEqual(@as(usize, 2), counters.derived_ref_count);
}

// ============================================================
// Multi-premise and multi-layer forward saturation
// (META.md). Layered semi-naive firing over pool + derived
// sources, configurable bounds, recipe/shape dedupe, nested
// recipe materialization.
// ============================================================

// Two-step chain: layer 1 fires `pq` on `P K` (deriving `Q K`), layer 2
// fires `qr` on the derived `Q K` (deriving `R K` whose recipe nests the
// layer-1 recipe). The backward `rs` premise `R x` is open (x not in the
// conclusion `S`), so only the two-layer derived ref can fill it.
const fwd_chain_mm0 =
    \\delimiter $ ( ) $;
    \\provable sort wff;
    \\sort obj;
    \\term P (x: obj): wff;
    \\term Q (x: obj): wff;
    \\term R (x: obj): wff;
    \\term S: wff;
    \\term K: obj;
    \\--| @auto forward
    \\axiom pq (x: obj): $ P x $ > $ Q x $;
    \\--| @auto forward
    \\axiom qr (x: obj): $ Q x $ > $ R x $;
    \\axiom rs (x: obj): $ R x $ > $ S $;
    \\theorem t: $ P K $ > $ S $;
;

test "two-step forward chain renders a nested recipe" {
    const proof_src =
        \\t
        \\----
        \\l1: $ S $ by auto?
    ;
    const offset = std.mem.indexOf(u8, proof_src, "auto?") orelse
        return error.MissingNeedle;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    var suggestions = try source.suggestionsAtSourceOffset(
        arena.allocator(),
        fwd_chain_mm0,
        proof_src,
        offset,
        .{ .counters = &counters, .generate = .{ .enabled = true } },
    );
    defer suggestions.deinit();

    var found = false;
    for (suggestions.items) |item| {
        if (std.mem.eql(
            u8,
            item.replacement,
            "rs [qr (x := $ K $) [pq (x := $ K $) [#1]]]",
        )) found = true;
    }
    try std.testing.expect(found);
    // Layer 1: `Q K`; layer 2: `R K`; layer 3 derives nothing (fixpoint —
    // a clean stop, not budget exhaustion).
    try std.testing.expectEqual(@as(usize, 2), counters.derived_ref_count);
    try std.testing.expect(counters.forward_layers_run >= 2);
    try std.testing.expect(!counters.forward_saturation_exhausted);
}

test "multi-premise forward rule fires on a source tuple" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\sort obj;
        \\term P (x: obj): wff;
        \\term Q (x: obj): wff;
        \\term R (x: obj): wff;
        \\term S: wff;
        \\term K: obj;
        \\--| @auto forward
        \\axiom pqr (x: obj): $ P x $ > $ Q x $ > $ R x $;
        \\axiom rs (x: obj): $ R x $ > $ S $;
        \\theorem t: $ P K $ > $ Q K $ > $ S $;
    ;
    const proof_src =
        \\t
        \\----
        \\l1: $ S $ by auto?
    ;
    const offset = std.mem.indexOf(u8, proof_src, "auto?") orelse
        return error.MissingNeedle;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    var suggestions = try source.suggestionsAtSourceOffset(
        arena.allocator(),
        mm0_src,
        proof_src,
        offset,
        .{ .counters = &counters, .generate = .{ .enabled = true } },
    );
    defer suggestions.deinit();

    var found = false;
    for (suggestions.items) |item| {
        if (std.mem.eql(
            u8,
            item.replacement,
            "rs [pqr (x := $ K $) [#1, #2]]",
        )) found = true;
    }
    try std.testing.expect(found);
    // One tuple (#1, #2) matches both premises consistently (x := K at both
    // positions); the cross pairings reject on the shared binder.
    try std.testing.expectEqual(@as(usize, 1), counters.derived_ref_count);
}

test "duplicate derivations collapse to one derived ref" {
    // Two pool refs state the same fact `P K`; the recipe key is the source
    // EXPRESSION, so `pq` fires once, not twice.
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\sort obj;
        \\term P (x: obj): wff;
        \\term Q (x: obj): wff;
        \\term R: wff;
        \\term K: obj;
        \\--| @auto forward
        \\axiom pq (x: obj): $ P x $ > $ Q x $;
        \\axiom qr (x: obj): $ Q x $ > $ R $;
        \\theorem t: $ P K $ > $ P K $ > $ R $;
    ;
    const proof_src =
        \\t
        \\----
        \\l1: $ R $ by auto?
    ;
    const offset = std.mem.indexOf(u8, proof_src, "auto?") orelse
        return error.MissingNeedle;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    var suggestions = try source.suggestionsAtSourceOffset(
        arena.allocator(),
        mm0_src,
        proof_src,
        offset,
        .{ .counters = &counters, .generate = .{ .enabled = true } },
    );
    defer suggestions.deinit();

    var found = false;
    for (suggestions.items) |item| {
        if (std.mem.eql(
            u8,
            item.replacement,
            "qr [pq (x := $ K $) [#1]]",
        )) found = true;
    }
    try std.testing.expect(found);
    try std.testing.expectEqual(@as(usize, 1), counters.derived_ref_count);
}

// Self-feeding loop theory: `step` derives `P (f K)`, then `P (f (f K))`,
// ... — one new fact per layer, forever. Only the bounds stop it.
const fwd_loop_mm0 =
    \\delimiter $ ( ) $;
    \\provable sort wff;
    \\sort obj;
    \\term P (x: obj): wff;
    \\term f (x: obj): obj;
    \\term K: obj;
    \\term R: wff;
    \\--| @auto forward
    \\axiom step (x: obj): $ P x $ > $ P (f x) $;
    \\theorem t: $ P K $ > $ R $;
;

test "layer bound stops a self-feeding forward loop" {
    const proof_src =
        \\t
        \\----
        \\l1: $ R $ by auto?
    ;
    const offset = std.mem.indexOf(u8, proof_src, "auto?") orelse
        return error.MissingNeedle;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    var suggestions = try source.suggestionsAtSourceOffset(
        arena.allocator(),
        fwd_loop_mm0,
        proof_src,
        offset,
        .{ .counters = &counters, .generate = .{ .enabled = true } },
    );
    defer suggestions.deinit();

    // No proof exists; saturation stops at the layer cap with the frontier
    // still productive, and reports that as exhaustion — distinct from the
    // chain test's clean fixpoint.
    try std.testing.expectEqual(@as(usize, 0), suggestions.items.len);
    const default_layers = (types.ForwardOptions{}).max_forward_layers;
    try std.testing.expectEqual(default_layers, counters.derived_ref_count);
    try std.testing.expectEqual(default_layers, counters.forward_layers_run);
    try std.testing.expect(counters.forward_saturation_exhausted);
}

test "fact bound stops a forward explosion" {
    const proof_src =
        \\t
        \\----
        \\l1: $ R $ by auto?
    ;
    const offset = std.mem.indexOf(u8, proof_src, "auto?") orelse
        return error.MissingNeedle;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    var suggestions = try source.suggestionsAtSourceOffset(
        arena.allocator(),
        fwd_loop_mm0,
        proof_src,
        offset,
        .{
            .counters = &counters,
            .generate = .{
                .enabled = true,
                .forward = .{ .max_forward_facts = 1 },
            },
        },
    );
    defer suggestions.deinit();

    try std.testing.expectEqual(@as(usize, 0), suggestions.items.len);
    try std.testing.expectEqual(@as(usize, 1), counters.derived_ref_count);
    try std.testing.expect(counters.forward_saturation_exhausted);
}

test "two-layer derived ref solves a shared hole in both recipe layers" {
    // The nested universal sits directly in the hypothesis (no def unfold).
    // Layer 1 derives `∀ b ((pair f ?t = pair f b) → (?t = b))`; layer 2
    // fires on that shape, deriving `(pair f ?t = pair f ?t2) → (?t = ?t2)`
    // with the layer-1 hole ?t shared. The goal-direct use solves ?t := u,
    // ?t2 := v in ONE walk, and the rendered two-layer recipe shows the
    // shared witness consistently: inner `t := u`, outer `p` mentioning `u`.
    const proof_src =
        \\fwd_nested
        \\----------
        \\l1: $ (pair f u = pair f v) → (u = v) $ by auto?
    ;
    const offset = std.mem.indexOf(u8, proof_src, "auto?") orelse
        return error.MissingNeedle;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    var suggestions = try source.suggestionsAtSourceOffset(
        arena.allocator(),
        fwd_twice_mm0,
        proof_src,
        offset,
        .{ .counters = &counters, .generate = .{ .enabled = true } },
    );
    defer suggestions.deinit();

    var found = false;
    for (suggestions.items) |item| {
        if (std.mem.eql(
            u8,
            item.replacement,
            "all_elim (x := $ b $, t := $ v $, " ++
                "p := $ pair f u = pair f b → u = b $) " ++
                "[all_elim (x := $ a $, t := $ u $, " ++
                "p := $ ∀ b (pair f a = pair f b → a = b) $) " ++
                "[#1]]",
        )) found = true;
    }
    try std.testing.expect(found);
    try std.testing.expectEqual(@as(usize, 2), counters.derived_ref_count);
    try std.testing.expectEqual(@as(usize, 2), counters.universal_metas_created);
}

// ---------------------------------------------------------------------------
// `@auto trigger` seeding (phase 6). The fixture is the guarded bench theory
// (tests/search_bench_cases/nd_minimal.*): the pure repro of the
// elimination-major left-rule gap, closed by ground `ax` seeds harvested
// from the goal's subterms.
// ---------------------------------------------------------------------------

fn readBenchCase(
    allocator: std.mem.Allocator,
    stem: []const u8,
    ext: []const u8,
) ![]u8 {
    const path = try std.fmt.allocPrint(
        allocator,
        "tests/search_bench_cases/{s}.{s}",
        .{ stem, ext },
    );
    defer allocator.free(path);
    return try std.fs.cwd().readFileAlloc(
        allocator,
        path,
        std.math.maxInt(usize),
    );
}

test "auto trigger seeds close an elimination major from an empty pool" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    const mm0_src = try readBenchCase(allocator, "nd_minimal", "mm0");

    // The pure left-rule repro: `p → q , p ⊢ q` from an EMPTY ref pool.
    // Without seeding this is a clean miss at any budget (imp_elim's `p` is
    // premise-only, so backward search has no ref to pin it); the `(hyp p)`
    // trigger seeds `p → q ⊢ p → q` and `p ⊢ p`, which pin it.
    const proof_src =
        "nd_mp_inner\n" ++
        "-----------\n" ++
        "l1: $ p → q , p ⊢ q $ by auto?\n";
    const offset = std.mem.indexOf(u8, proof_src, "auto?") orelse
        return error.MissingNeedle;
    var counters = types.SearchCounters{};
    var suggestions = try source.suggestionsAtSourceOffset(
        allocator,
        mm0_src,
        proof_src,
        offset,
        .{ .counters = &counters, .generate = .{ .enabled = true } },
    );
    defer suggestions.deinit();

    try std.testing.expect(suggestions.items.len > 0);
    try std.testing.expect(counters.trigger_seed_count > 0);
    var found_imp_elim = false;
    for (suggestions.items) |item| {
        if (std.mem.indexOf(u8, item.replacement, "imp_elim") != null) {
            found_imp_elim = true;
        }
    }
    try std.testing.expect(found_imp_elim);
}

test "theories without trigger annotations mint no seeds on a miss" {
    // A clean full-ladder miss in a trigger-free theory: the phase-6 gate
    // (`triggerRuleCount() > 0`) must skip the harvest entirely.
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term P: wff;
        \\term Q: wff;
        \\term R: wff;
        \\axiom p: $ P $;
        \\axiom pq: $ P $ > $ Q $;
        \\theorem t: $ R $;
    ;
    const proof_src =
        \\t
        \\----
        \\l1: $ R $ by auto?
    ;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const offset = std.mem.indexOf(u8, proof_src, "auto?") orelse
        return error.MissingNeedle;
    var counters = types.SearchCounters{};
    var suggestions = try source.suggestionsAtSourceOffset(
        arena.allocator(),
        mm0_src,
        proof_src,
        offset,
        .{ .counters = &counters, .generate = .{ .enabled = true } },
    );
    defer suggestions.deinit();

    try std.testing.expectEqual(@as(usize, 0), suggestions.items.len);
    try std.testing.expectEqual(@as(usize, 0), counters.trigger_seed_count);
}

test "verdict memo counts distinct rejects once" {
    var memo = types.VerdictMemo{ .allocator = std.testing.allocator };
    defer memo.deinit();

    memo.recordReject(11);
    memo.recordReject(22);
    memo.recordReject(11);
    try std.testing.expect(memo.rejectedBefore(11));
    try std.testing.expect(memo.rejectedBefore(22));
    try std.testing.expect(!memo.rejectedBefore(33));
    try std.testing.expectEqual(@as(usize, 3), memo.reject_total);
    try std.testing.expectEqual(@as(usize, 2), memo.reject_distinct);
    try std.testing.expectEqual(memo.seen.count(), memo.reject_distinct);
}

fn contentHashOf(theorem: *const TheoremContext, id: ExprId) u64 {
    var h = std.hash.Wyhash.init(0);
    types.hashCanonicalContent(theorem, id, &h);
    return h.final();
}

test "canonical content hash is stable across an interner-scope discard" {
    // The invariant that lets the concrete/verdict/deep memos skip scope-exit
    // eviction entirely: keys hash canonical CONTENT, so a `hookSolveOpen`
    // scope discard — which re-mints the same raw ExprIds with different
    // content — can never alias a surviving entry.
    var base = TheoremContext.init(std.testing.allocator);
    defer base.deinit();
    const d0 = try base.addDummyVarResolved("wff", 0);

    // Scope 1: a COW clone interns `f(d0)` (term_id 7).
    var scope1 = try base.clone();
    const a1 = try scope1.interner.internApp(7, &.{d0});
    const hash_f = contentHashOf(&scope1, a1);
    scope1.deinit();

    // Scope 2: same base, so the discarded id is re-minted — this time for
    // `g(d0)` (term_id 8). Same raw ExprId, different content: the raw id is
    // ABA-ambiguous, the content hash is not.
    var scope2 = try base.clone();
    defer scope2.deinit();
    const b2 = try scope2.interner.internApp(8, &.{d0});
    try std.testing.expectEqual(a1, b2);
    try std.testing.expect(contentHashOf(&scope2, b2) != hash_f);

    // Re-interning the SAME content in the new scope reproduces the hash.
    const a2 = try scope2.interner.internApp(7, &.{d0});
    try std.testing.expectEqual(hash_f, contentHashOf(&scope2, a2));
}

test "canonical content hash keys dummies by index and sort" {
    // Dummy leaves hash (index, sort), the pair that fully determines a
    // dummy's semantics — so a same-index same-sort re-mint after a scope
    // discard deliberately collides (it is interchangeable), while a
    // different-sort re-mint at the same index does not.
    var base = TheoremContext.init(std.testing.allocator);
    defer base.deinit();

    var scope1 = try base.clone();
    const d_wff = try scope1.addDummyVarResolved("wff", 0);
    const app1 = try scope1.interner.internApp(7, &.{d_wff});
    const hash_wff = contentHashOf(&scope1, app1);
    scope1.deinit();

    var scope2 = try base.clone();
    defer scope2.deinit();
    const d_nat = try scope2.addDummyVarResolved("nat", 1);
    const app2 = try scope2.interner.internApp(7, &.{d_nat});
    try std.testing.expectEqual(app1, app2);
    try std.testing.expect(contentHashOf(&scope2, app2) != hash_wff);

    var scope3 = try base.clone();
    defer scope3.deinit();
    const d_wff_again = try scope3.addDummyVarResolved("wff", 0);
    const app3 = try scope3.interner.internApp(7, &.{d_wff_again});
    try std.testing.expectEqual(hash_wff, contentHashOf(&scope3, app3));
}

test "complement shapes derive from ax's repeated-binder template pair" {
    // tait's `ax (d: ctx) (a: wff): ⊢ a , (¬ a) , d` repeats binder `a`
    // (arg index 1) across two region members — coercion-wrapped as
    // `hyp(a)` / `hyp(¬ a)`, so neither member is a bare binder. It must be
    // the fixture's ONLY complement shape: the ctx_eq axioms repeat `g`
    // only as identical bare members (excluded), and every other repeated
    // binder sits outside an ACUI carrier region.
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    const mm0 = try std.fs.cwd().readFileAlloc(
        allocator,
        "tests/search_bench_cases/tait.mm0",
        std.math.maxInt(usize),
    );
    var fixture = try fixtureFor(allocator, mm0, "ex_all_to_all_ex");
    var harness = ContextHarness.init(allocator);
    defer harness.deinit();
    const context = harness.context(&fixture);

    var shapes: [Witness.max_complement_shapes]Witness.ComplementShape = undefined;
    const count = Witness.collectComplementShapes(&context, &shapes);
    try std.testing.expectEqual(@as(usize, 1), count);
    try std.testing.expectEqual(@as(usize, 1), shapes[0].hole);
    // Both members are compound (coercion-wrapped), not bare binders.
    try std.testing.expect(shapes[0].first.* == .app);
    try std.testing.expect(shapes[0].second.* == .app);
}

test "auto co-solves a complementary two-meta ax leaf through the rule template" {
    // Regenerating `⊢ (∃ x ¬ R x y) , (∃ w R z w)` from the bare goal takes
    // two nested `rex` slots whose witnesses only the `ax` leaf forces: the
    // leaf goal members `¬ R ?x y` / `R z ?w` BOTH carry metas (no rigid
    // anchor), so closure requires co-solving `?x := z`, `?w := y` through
    // ax's repeated-binder template pair — the complementary coupled pass.
    // Without it this is a clean miss (the tait ex_all_to_all_ex gap).
    const proof_src =
        \\ex_all_to_all_ex
        \\----------------
        \\l1: $ ⊢ (∃ x (¬ R x y)) , (∃ w R z w) $ by auto?
    ;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    const mm0 = try std.fs.cwd().readFileAlloc(
        allocator,
        "tests/search_bench_cases/tait.mm0",
        std.math.maxInt(usize),
    );
    const offset = std.mem.indexOf(u8, proof_src, "auto?").?;
    var suggestions = try source.suggestionsAtSourceOffset(
        allocator,
        mm0,
        proof_src,
        offset,
        .{ .generate = .{ .enabled = true } },
    );
    defer suggestions.deinit();

    try std.testing.expect(suggestions.items.len > 0);
    // The regenerated chain goes through rex and closes at the ax leaf.
    var found = false;
    for (suggestions.items) |item| {
        if (std.mem.indexOf(u8, item.replacement, "rex") != null and
            std.mem.indexOf(u8, item.replacement, "ax") != null)
        {
            found = true;
        }
    }
    try std.testing.expect(found);
}

test "member witness match rejects values captured under a member binder" {
    // A meta-bearing fragment may ground its witness off any *free* subterm
    // of a domain member, but not off a subterm under the member's own
    // intact binder: that value escapes its scope (the materialized target
    // would mention the variable free while the sibling member still binds
    // it), so the fill can never validate — before the capture check each
    // one launched a full doomed child search (the forall_mono node flood).
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\sort ctx;
        \\sort obj;
        \\term not (a: wff): wff;
        \\term ex {x: obj} (p: wff x): wff;
        \\term Q (a: obj): wff;
        \\term hyp (a: wff): ctx;
        \\term T: wff;
        \\theorem t: $ T $;
    ;
    var fixture = try fixtureFor(allocator, mm0_src, "t");
    var theorem = TheoremContext.init(allocator);
    defer theorem.deinit();
    try theorem.seedAssertion(fixture.assertion);
    var harness = ContextHarness.init(allocator);
    defer harness.deinit();
    const context = harness.context(&fixture);

    const not_id = fixture.env.term_names.get("not").?;
    const ex_id = fixture.env.term_names.get("ex").?;
    const q_id = fixture.env.term_names.get("Q").?;
    const hyp_id = fixture.env.term_names.get("hyp").?;

    var store = MetaStore.init(allocator, &fixture.env);
    defer store.deinit();
    const meta = try store.mint(&theorem, "obj", std.math.maxInt(u55), .existential);
    const fragment = try theorem.interner.internApp(q_id, &.{meta});

    // Captured anchor: hyp(∃ x ¬(Q x)) — the only Q-node sits under the
    // member's own binder, so ?w := x must be refused outright (the old
    // descent read it off and returned true).
    const x = try theorem.interner.internVar(.{ .theorem_var = 0 });
    const captured = try theorem.interner.internApp(hyp_id, &.{
        try theorem.interner.internApp(ex_id, &.{
            x,
            try theorem.interner.internApp(not_id, &.{
                try theorem.interner.internApp(q_id, &.{x}),
            }),
        }),
    });
    const mark = store.mark();
    try std.testing.expect(!Witness.matchFragmentToMember(
        &context,
        &store,
        &theorem,
        fragment,
        captured,
    ));
    store.rollbackTo(mark);

    // Free anchor: hyp(Q z) with z free in the member still forces ?w := z
    // (the ordinary member-force, e.g. off a rall eigenvariable).
    const z = try theorem.interner.internVar(.{ .theorem_var = 1 });
    const free_anchor = try theorem.interner.internApp(hyp_id, &.{
        try theorem.interner.internApp(q_id, &.{z}),
    });
    try std.testing.expect(Witness.matchFragmentToMember(
        &context,
        &store,
        &theorem,
        fragment,
        free_anchor,
    ));
    try std.testing.expectEqual(z, try store.materialize(&theorem, meta));
    store.rollbackTo(mark);
}

// ---------------------------------------------------------------------------
// Per-call tunables + failure detail (search/tunables.zig, buildStatusDetail)
