const helpers = @import("./helpers.zig");
const std = helpers.std;
const types = helpers.types;
const def_match = helpers.def_match;
const acui = helpers.acui;
const TemplateExpr = helpers.TemplateExpr;
const ExprId = helpers.ExprId;
const TheoremContext = helpers.TheoremContext;
const CompilerContext = helpers.CompilerContext;
const Check = helpers.Check;
const DiagnosticSink = helpers.DiagnosticSink;
const Goal = helpers.Goal;
const Context = helpers.Context;
const apply = helpers.apply;
const fixtureFor = helpers.fixtureFor;
const parseGoal = helpers.parseGoal;
const readProofCase = helpers.readProofCase;
const expectTimingCounter = helpers.expectTimingCounter;
const ContextHarness = helpers.ContextHarness;
const auto_chain_mm0 = helpers.auto_chain_mm0;
const auto_inline_mm0 = helpers.auto_inline_mm0;
const suggestionsAtNeedle = helpers.suggestionsAtNeedle;
const expectOffered = helpers.expectOffered;
const ruleArgIndex = helpers.ruleArgIndex;

fn autoChainSuggestions(
    arena: *std.heap.ArenaAllocator,
    proof_src: []const u8,
    needle: []const u8,
    options: types.SourceSuggestionOptions,
) !types.SourceSuggestions {
    return suggestionsAtNeedle(
        arena,
        auto_chain_mm0,
        proof_src,
        needle,
        options,
    );
}

test "auto generates a depth-1 inline chain" {
    const proof_src =
        \\t
        \\----
        \\l1: $ Q $ by auto?
    ;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    var suggestions = try autoChainSuggestions(&arena, proof_src, "auto?", .{
        .counters = &counters,
        .generate = .{ .enabled = true },
    });
    defer suggestions.deinit();

    try expectOffered(suggestions.items, &.{"pq [p []]"});
    // Generation found it, not the direct exact pass.
    try std.testing.expect(counters.core_ran);
}

/// Whether `T` holds no pointer anywhere in its layout (through optionals,
/// arrays, and nested structs/unions).
fn holdsNoPointers(comptime T: type) bool {
    return switch (@typeInfo(T)) {
        .pointer => false,
        .optional => |o| holdsNoPointers(o.child),
        .array => |a| holdsNoPointers(a.child),
        .vector => |v| holdsNoPointers(v.child),
        .@"struct" => |s| blk: {
            inline for (s.field_types) |field_type| {
                if (!holdsNoPointers(field_type)) break :blk false;
            }
            break :blk true;
        },
        .@"union" => |u| blk: {
            inline for (u.field_types) |field_type| {
                if (!holdsNoPointers(field_type)) break :blk false;
            }
            break :blk true;
        },
        else => true,
    };
}

test "search counters are value-only statistics" {
    // A counters block may be reused across calls or omitted without
    // changing what the search does. Pin that no borrowed pointer or policy
    // switch creeps onto the sink.
    comptime {
        if (!holdsNoPointers(types.SearchCounters)) {
            @compileError("SearchCounters must hold no pointers");
        }
        for (std.meta.fieldNames(types.SearchCounters)) |field_name| {
            if (std.mem.endsWith(u8, field_name, "_enabled")) {
                @compileError("SearchCounters." ++ field_name ++
                    " is a policy switch; policy belongs on GenerateOptions");
            }
        }
    }
}

fn autoInlineSuggestions(
    arena: *std.heap.ArenaAllocator,
    proof_src: []const u8,
    needle: []const u8,
    options: types.SourceSuggestionOptions,
) !types.SourceSuggestions {
    return suggestionsAtNeedle(
        arena,
        auto_inline_mm0,
        proof_src,
        needle,
        options,
    );
}

test "auto generates a depth-1 chain inside a slot" {
    // The `auto?` fills `qr`'s only hypothesis (goal `Q`). No single rule proves
    // `Q` over the empty pool, so the slot must generate `pq [p []]`, yielding a
    // whole line of `qr [pq [p []]]`.
    const proof_src =
        \\t
        \\----
        \\l1: $ R $ by qr [auto?]
    ;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    var suggestions = try autoInlineSuggestions(&arena, proof_src, "auto?", .{
        .counters = &counters,
        .generate = .{ .enabled = true },
    });
    defer suggestions.deinit();

    try expectOffered(suggestions.items, &.{"pq [p []]"});
    // The slot span is what gets replaced, not the whole line.
    try std.testing.expect(suggestions.target_span != null);
    const auto_offset = std.mem.indexOf(u8, proof_src, "auto?").?;
    try std.testing.expect(suggestions.target_span.?.start <= auto_offset);
    try std.testing.expect(suggestions.target_span.?.end >= auto_offset);
    // Generation actually fired (this is not a plain direct match).
    try std.testing.expect(counters.core_ran);
}

test "inline auto generates a longer chain in a slot" {
    // Outer rule `rx` needs a proof of `R` in its slot. `R` is only reachable by
    // a two-level chain `qr [pq [p]]`, so the slot must recurse twice, producing
    // a strictly longer inline application than the depth-1 case.
    const proof_src =
        \\tX
        \\----
        \\l1: $ X $ by rx [auto?]
    ;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    // Without the earlier theorem `t`, which would close the slot at once.
    const mm0_src = try std.mem.replaceOwned(
        u8,
        arena.allocator(),
        auto_inline_mm0,
        "theorem t: $ R $;\n",
        "",
    );
    try std.testing.expect(mm0_src.len < auto_inline_mm0.len);
    var suggestions = try suggestionsAtNeedle(&arena, mm0_src, proof_src, "auto?", .{
        .generate = .{ .enabled = true },
    });
    defer suggestions.deinit();

    try expectOffered(suggestions.items, &.{"qr [pq [p []]]"});
}

test "inline auto still resolves a slot from a direct ref without generating" {
    // Here the slot goal `P` is provable directly by `p` (a single rule), so the
    // direct exact pass supplies it; generation must not be required.
    const proof_src =
        \\t
        \\----
        \\l1: $ Q $ by pq [auto?]
    ;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    var suggestions = try autoInlineSuggestions(&arena, proof_src, "auto?", .{
        .counters = &counters,
        .generate = .{ .enabled = true },
    });
    defer suggestions.deinit();

    // The point is that a directly-provable slot does not depend on
    // generation. Inline, a no-ref rule keeps its `[]` so it does not read as
    // a line label.
    try expectOffered(suggestions.items, &.{"p []"});
}

test "inline auto reports a miss on an unprovable slot" {
    // `sq`'s only hypothesis is `S`, and no rule concludes `S`, so the slot goal
    // has no proof at all — both the direct exact pass and the generated pass
    // come up empty and the search is a definitive inline miss.
    const proof_src =
        \\t
        \\----
        \\l1: $ Q $ by sq [auto?]
    ;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    var suggestions = try autoInlineSuggestions(&arena, proof_src, "auto?", .{
        .counters = &counters,
        .generate = .{ .enabled = true },
    });
    defer suggestions.deinit();

    try std.testing.expectEqual(@as(usize, 0), suggestions.items.len);
}

// Real Zermelo natural-deduction theory: `,` (the sequent context) is a full
// `@acui` combiner, so `and_intro`'s conclusion context `G , H` splits
// ambiguously against a single-member goal context. See the ACUI-combiner guard
// in `expectedRefForApplication`. Read from disk (unit tests run at repo root);
// the full congruence/@relation machinery it carries is what makes the ordinary
// exact search resolve these sequent goals, so a hand-trimmed fixture won't do.
fn andCommSlotSuggestions(
    arena: *std.heap.ArenaAllocator,
    proof_src: []const u8,
) !types.SourceSuggestions {
    const mm0 = try std.Io.Dir.cwd().readFileAlloc(std.testing.io, "tests/proof_cases/zermelo.mm0", arena.allocator(), .unlimited);
    return suggestionsAtNeedle(arena, mm0, proof_src, "exact?", .{});
}

test "inline exact resolves either and_intro premise slot (ACUI context split)" {
    // `and_intro`'s conclusion context `G , H` matches the goal's single context
    // `p ∧ q` ambiguously. The probe commits one canonical ACUI split — whole
    // context to the last operand, `emp` to earlier ones — which used to leave a
    // *first*-premise slot goal as `emp ⊢ q`, matching nothing. Both slot
    // orderings must resolve symmetrically now.
    const first_slot =
        \\nd_and_comm
        \\----
        \\l1: $ p ∧ q ⊢ p ∧ q $ by ax
        \\l2: $ p ∧ q ⊢ p $ by and_elim_l [l1]
        \\l3: $ p ∧ q ⊢ q $ by and_elim_r [l1]
        \\l4: $ p ∧ q ⊢ q ∧ p $ by and_intro [exact?, l2]
    ;
    const second_slot =
        \\nd_and_comm
        \\----
        \\l1: $ p ∧ q ⊢ p ∧ q $ by ax
        \\l2: $ p ∧ q ⊢ p $ by and_elim_l [l1]
        \\l3: $ p ∧ q ⊢ q $ by and_elim_r [l1]
        \\l4: $ p ∧ q ⊢ q ∧ p $ by and_intro [l3, exact?]
    ;

    var arena_a = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena_a.deinit();
    var first = try andCommSlotSuggestions(&arena_a, first_slot);
    defer first.deinit();
    try std.testing.expectEqual(types.SearchStatus.found, first.status);
    try expectOffered(first.items, &.{"l3"});

    var arena_b = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena_b.deinit();
    var second = try andCommSlotSuggestions(&arena_b, second_slot);
    defer second.deinit();
    try std.testing.expectEqual(types.SearchStatus.found, second.status);
    try expectOffered(second.items, &.{"l2"});
}

// `red` rewrites `f p` to `g p`, but `feq` has no `@congr`, so the checker
// cannot convert inside an `feq` judgment. The generated premise of `feq_sym`
// must keep its redex `f p ~= g p` for `red` to prove it; reduced to
// `g p ~= g p`, no proof of it would check as that premise.
test "auto keeps a redex the checker cannot convert in a generated premise" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\sort form;
        \\term iff (a b: wff): wff;
        \\infixr iff: $<->$ prec 20;
        \\term feq (p q: form): wff;
        \\infixr feq: $~=$ prec 20;
        \\term f (p: form): form;
        \\term g (p: form): form;
        \\--| @relation wff iff iff_refl iff_trans iff_sym iff_mp
        \\axiom iff_refl (a: wff): $ a <-> a $;
        \\axiom iff_trans (a b c: wff): $ a <-> b $ > $ b <-> c $ > $ a <-> c $;
        \\axiom iff_sym (a b: wff): $ a <-> b $ > $ b <-> a $;
        \\axiom iff_mp (a b: wff): $ a <-> b $ > $ a $ > $ b $;
        \\--| @relation form feq feq_refl feq_trans feq_sym _
        \\axiom feq_refl (p: form): $ p ~= p $;
        \\axiom feq_trans (p q r: form): $ p ~= q $ > $ q ~= r $ > $ p ~= r $;
        \\axiom feq_sym (p q: form): $ p ~= q $ > $ q ~= p $;
        \\--| @rewrite
        \\axiom red (p: form): $ f p ~= g p $;
        \\theorem red_sym (p: form): $ g p ~= f p $;
    ;
    const proof_src =
        \\red_sym
        \\-------
        \\
        \\l1: $ g p ~= f p $ by auto?
    ;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var suggestions = try suggestionsAtNeedle(&arena, mm0_src, proof_src, "auto?", .{
        .generate = .{ .enabled = true },
    });
    defer suggestions.deinit();

    try expectOffered(suggestions.items, &.{"feq_sym [red []]"});
    try helpers.expectConversionCompiles(&arena, mm0_src, proof_src, suggestions.items[0]);
}

// Forward saturation derives `?G , p ⊢ q` from `⊨ p → q` and `p ⊢ p`: the
// context `?G` of `valid_elim`'s conclusion is fixed by no premise. That fact
// proves the goal `p ⊢ q` only with `?G := ∅`, which a positional match of
// `?G , p` against `p` cannot find.
test "auto closes a goal with a forward-derived fact modulo ACUI on its context meta" {
    const mm0_src =
        \\delimiter $ ( ) , $;
        \\strict provable sort wff;
        \\sort ctx;
        \\term im (p q: wff): wff;
        \\infixr im: $→$ prec 25;
        \\term bi (p q: wff): wff;
        \\infixr bi: $↔$ prec 20;
        \\term valid (p: wff): wff;
        \\prefix valid: $⊨$ prec 3;
        \\term ctx_eq (G H: ctx): wff;
        \\term emp: ctx;
        \\notation emp: ctx = ($∅$:max);
        \\--| @acui ctx_assoc ctx_comm emp ctx_idem
        \\term join (G H: ctx): ctx;
        \\infixl join: $,$ prec 5;
        \\term hyp (p: wff): ctx;
        \\coercion hyp: wff > ctx;
        \\term nd (G: ctx) (p: wff): wff;
        \\infixl nd: $⊢$ prec 0;
        \\--| @relation wff bi biid bitr bisym mpbi
        \\axiom biid (p: wff): $ p ↔ p $;
        \\axiom bitr (p q r: wff): $ p ↔ q $ > $ q ↔ r $ > $ p ↔ r $;
        \\axiom bisym (p q: wff): $ p ↔ q $ > $ q ↔ p $;
        \\axiom mpbi (p q: wff): $ p ↔ q $ > $ p $ > $ q $;
        \\--| @relation ctx ctx_eq ctx_refl ctx_trans ctx_sym _
        \\axiom ctx_refl (G: ctx): $ ctx_eq G G $;
        \\axiom ctx_trans (G H K: ctx):
        \\  $ ctx_eq G H $ > $ ctx_eq H K $ > $ ctx_eq G K $;
        \\axiom ctx_sym (G H: ctx): $ ctx_eq G H $ > $ ctx_eq H G $;
        \\axiom ctx_assoc (G H K: ctx):
        \\  $ ctx_eq ((G , H) , K) (G , (H , K)) $;
        \\axiom ctx_comm (G H: ctx): $ ctx_eq (G , H) (H , G) $;
        \\axiom ctx_idem (G: ctx): $ ctx_eq (G , G) G $;
        \\axiom ctx_unit (G: ctx): $ ctx_eq (∅ , G) G $;
        \\--| @congr
        \\axiom join_congr (G1 G2 H1 H2: ctx):
        \\  $ ctx_eq G1 G2 $ > $ ctx_eq H1 H2 $ >
        \\  $ ctx_eq (G1 , H1) (G2 , H2) $;
        \\--| @congr
        \\axiom hyp_congr (p q: wff): $ p ↔ q $ > $ ctx_eq (hyp p) (hyp q) $;
        \\--| @congr
        \\axiom nd_congr (G H: ctx) (p q: wff):
        \\  $ ctx_eq G H $ > $ p ↔ q $ > $ (G ⊢ p) ↔ (H ⊢ q) $;
        \\axiom ax (G: ctx) (p: wff): $ G , p ⊢ p $;
        \\--| @auto forward
        \\axiom imp_elim (G H: ctx) (p q: wff):
        \\  $ G ⊢ p → q $ > $ H ⊢ p $ > $ G , H ⊢ q $;
        \\--| @auto forward
        \\axiom valid_elim (G: ctx) (p: wff): $ ⊨ p $ > $ G ⊢ p $;
        \\theorem valid_mp (p q: wff): $ ⊨ p → q $ > $ p ⊢ q $;
    ;
    const proof_src =
        \\valid_mp
        \\--------
        \\
        \\l1: $ p ⊢ p $ by ax []
        \\l2: $ p ⊢ q $ by auto?
    ;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var suggestions = try suggestionsAtNeedle(&arena, mm0_src, proof_src, "auto?", .{
        .generate = .{ .enabled = true },
    });
    defer suggestions.deinit();

    try expectOffered(suggestions.items, &.{"imp_elim [valid_elim [#1], l1]"});
    try helpers.expectConversionCompiles(&arena, mm0_src, proof_src, suggestions.items[0]);
}

/// `auto?` in place of `theorem`'s last proof line in the proof case `stem`,
/// whose assertion leaves the type as the hole `_ty`. Requires the first
/// suggestion to compile in place: the line is the theorem's last, so the type
/// it fills must be the stated one.
fn expectHoleyTypeInferred(stem: []const u8, theorem: []const u8, expected: []const u8) !void {
    const allocator = std.testing.allocator;
    const mm0_src = try readProofCase(allocator, stem, "mm0");
    defer allocator.free(mm0_src);
    const full_proof = try readProofCase(allocator, stem, "auf");
    defer allocator.free(full_proof);

    var arena = std.heap.ArenaAllocator.init(allocator);
    defer arena.deinit();
    const header = try std.fmt.allocPrint(arena.allocator(), "{s}\n", .{theorem});
    const header_pos = std.mem.indexOf(u8, full_proof, header) orelse return error.MissingTheorem;
    // The proof lines run from under the header's underline to the next blank
    // line.
    const underline = (std.mem.indexOfScalarPos(u8, full_proof, header_pos + header.len, '\n') orelse
        return error.MissingProof) + 1;
    const block = underline + @intFromBool(std.mem.startsWith(u8, full_proof[underline..], "\n"));
    const block_end = std.mem.indexOfPos(u8, full_proof, block, "\n\n") orelse full_proof.len;
    const by = block + (std.mem.lastIndexOf(u8, full_proof[block..block_end], " $ by ") orelse
        return error.MissingProof) + " $ by ".len;
    const line_end = std.mem.indexOfScalarPos(u8, full_proof, by, '\n') orelse full_proof.len;
    // The last line is searched alone: an earlier line stating the same
    // typing would answer it (`t_weak [l1]`).
    const line_start = if (std.mem.lastIndexOfScalar(u8, full_proof[block..by], '\n')) |at| block + at + 1 else block;
    const proof_src = try std.mem.concat(arena.allocator(), u8, &.{
        full_proof[0..block], full_proof[line_start..by], "auto?", full_proof[line_end..],
    });

    var suggestions = try suggestionsAtNeedle(&arena, mm0_src, proof_src, "auto?", .{
        .generate = .{ .enabled = true },
    });
    defer suggestions.deinit();
    try expectOffered(suggestions.items, &.{expected});
    try helpers.expectConversionCompiles(&arena, mm0_src, proof_src, suggestions.items[0]);
}

test "auto infers the type of a holey typing goal" {
    try expectHoleyTypeInferred(
        "pass_holey_type_inference",
        "infer_compose",
        "t_lam [t_lam [t_lam [t_app [t_var [], t_app [t_var [], t_var []]]]]]",
    );
}

// The function position `f · x` is itself open: its type `?A → ?T` carries
// the root's hole meta `?T` into a constrained open slot, where `f`'s context
// entry solves it two levels down.
test "auto infers a type through a nested application" {
    try expectHoleyTypeInferred(
        "pass_holey_type_inference",
        "infer_app2",
        "t_app [t_app [t_var [], t_var []], t_var []]",
    );
}

// With the generic `ax` (`g , a ⊢ a`) as the variable rule, every elimination
// rule's conclusion `g ⊢ b` also fits each open typing goal `g ⊢ t : ?T`, and
// under the holey root their cuts carry to full depth. The candidate order
// tries the rule whose conclusion matches more of the goal first: `t_lam` for
// a λ, `t_app` for an application.
test "auto infers a type with the generic ax as the variable rule" {
    try expectHoleyTypeInferred(
        "pass_hole_generic_ax_typing",
        "compose",
        "t_lam [t_lam [t_lam [t_app [ax [], t_app [ax [], ax []]]]]]",
    );
}

/// `auto_chain_mm0` one step longer: `R` needs `qr [pq [p []]]`, two steps
/// above the closer `p`.
const auto_chain3_mm0 =
    \\delimiter $ ( ) $;
    \\provable sort wff;
    \\term P: wff;
    \\term Q: wff;
    \\term R: wff;
    \\axiom p: $ P $;
    \\axiom pq: $ P $ > $ Q $;
    \\axiom qr: $ Q $ > $ R $;
    \\theorem t: $ R $;
;

test "exact proves one step, its premises closed by references and closers" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    // `exact?` never generates, even with the permit set: `pq [p []]` is one
    // step whose premise a closer closes, `qr [pq [p []]]` is two.
    var one = try autoChainSuggestions(&arena,
        \\t
        \\----
        \\l1: $ Q $ by exact?
    , "exact?", .{ .generate = .{ .enabled = true } });
    defer one.deinit();
    try expectOffered(one.items, &.{"pq [p []]"});
    var two = try suggestionsAtNeedle(&arena, auto_chain3_mm0,
        \\t
        \\----
        \\l1: $ R $ by exact?
    , "exact?", .{ .generate = .{ .enabled = true } });
    defer two.deinit();
    try std.testing.expectEqual(@as(usize, 0), two.items.len);
}

test "auto without the generation permit proves only one step" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var suggestions = try suggestionsAtNeedle(&arena, auto_chain3_mm0,
        \\t
        \\----
        \\l1: $ R $ by auto?
    , "auto?", .{});
    defer suggestions.deinit();
    try std.testing.expectEqual(@as(usize, 0), suggestions.items.len);
}

// Open-hypothesis grounding. `r2`'s first hypothesis `a` is not
// pinned by its conclusion `R`, so it must be grounded from a ref (#1 = P) by the
// backtracker; once it is, the sibling hypothesis `Q` is concrete and gets a
// generated sub-proof (`pq [#1]`). Step 1 (pinned-only) could not do this.
const auto_open_mm0 =
    \\delimiter $ ( ) $;
    \\provable sort wff;
    \\term P: wff;
    \\term Q: wff;
    \\term R: wff;
    \\axiom p: $ P $;
    \\axiom pq: $ P $ > $ Q $;
    \\axiom r2 (a: wff): $ a $ > $ Q $ > $ R $;
    \\theorem t: $ P $ > $ R $;
;

test "auto grounds an open hypothesis from a ref and generates a sibling" {
    const proof_src =
        \\t
        \\----
        \\l1: $ R $ by auto?
    ;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var suggestions = try suggestionsAtNeedle(
        &arena,
        auto_open_mm0,
        proof_src,
        "auto?",
        .{ .generate = .{ .enabled = true } },
    );
    defer suggestions.deinit();

    try expectOffered(suggestions.items, &.{"r2 [#1, pq [#1]]"});
}

// Iterative deepening. `R` needs a two-level chain
// `qr [pq [p]]` (depth 1 finds nothing because `pq`'s `P` can't be closed by a
// leaf search), so the driver must escalate from depth 1 to depth 2.
const auto_depth2_mm0 =
    \\delimiter $ ( ) $;
    \\provable sort wff;
    \\term P: wff;
    \\term Q: wff;
    \\term R: wff;
    \\axiom p: $ P $;
    \\axiom pq: $ P $ > $ Q $;
    \\axiom qr: $ Q $ > $ R $;
    \\theorem t: $ R $;
;

test "auto escalates depth to find a two-level chain" {
    const proof_src =
        \\t
        \\----
        \\l1: $ R $ by auto?
    ;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var suggestions = try suggestionsAtNeedle(
        &arena,
        auto_depth2_mm0,
        proof_src,
        "auto?",
        .{ .generate = .{ .enabled = true } },
    );
    defer suggestions.deinit();

    try expectOffered(suggestions.items, &.{"qr [pq [p []]]"});
}

test "auto depth cap stops escalation" {
    const proof_src =
        \\t
        \\----
        \\l1: $ R $ by auto?
    ;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    // With the depth capped at 1, the two-level chain is unreachable.
    var suggestions = try suggestionsAtNeedle(
        &arena,
        auto_depth2_mm0,
        proof_src,
        "auto?",
        .{ .generate = .{ .enabled = true, .max_depth = 1 } },
    );
    defer suggestions.deinit();
    try std.testing.expectEqual(@as(usize, 0), suggestions.items.len);
}

test "auto global budget stop raises the budget" {
    const proof_src =
        \\t
        \\----
        \\l1: $ R $ by auto?
    ;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    // A one-tick budget runs out at the first candidate.
    const gen = types.GenerateOptions{ .enabled = true, .global_budget = 1 };
    var suggestions = try suggestionsAtNeedle(
        &arena,
        auto_depth2_mm0,
        proof_src,
        "auto?",
        .{ .counters = &counters, .generate = gen },
    );
    defer suggestions.deinit();
    try std.testing.expectEqual(@as(usize, 0), suggestions.items.len);
    try std.testing.expect(counters.work_budget_exhausted);
    const retry = helpers.miss.retryFor(helpers.miss.MissReport.of(&counters), gen) orelse
        return error.MissingRetry;
    try std.testing.expect(retry.budget != null);
}

/// The drinker on nd_fol with its `@vars` line replaced by `vars`.
fn drinkerWithVars(arena: *std.heap.ArenaAllocator, vars: []const u8) !types.SourceSuggestions {
    const allocator = arena.allocator();
    const fixture = try std.Io.Dir.cwd().readFileAlloc(std.testing.io, "tests/search_bench_cases/nd_fol.mm0", allocator, .unlimited);
    const line = "--| @vars x y z u v w z1 z2 z3 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12\n";
    const at = std.mem.indexOf(u8, fixture, line) orelse return error.MissingVarsLine;
    const mm0_src = try std.mem.concat(allocator, u8, &.{ fixture[0..at], vars, fixture[at + line.len ..] });
    const proof_src =
        \\drinker
        \\-------
        \\l1: $ ∅ ⊢ ∃ x (P x → ∀ y P y) $ by auto?
    ;
    return suggestionsAtNeedle(arena, mm0_src, proof_src, "auto?", .{
        .status_detail = true,
        .generate = .{ .enabled = true },
    });
}

test "auto miss report names a @vars pool that ran out" {
    // The theorem's own `x` and `y` are the whole pool, so `all_intro` finds
    // no name for its eigenvariable: no limit explains that miss, the pool
    // does.
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var miss = try drinkerWithVars(&arena, "--| @vars x y\n");
    defer miss.deinit();
    try std.testing.expectEqual(@as(usize, 0), miss.items.len);
    const detail = miss.status_detail orelse return error.MissingStatusDetail;
    try std.testing.expect(std.mem.indexOf(u8, detail, "ran out of `obj` variables: all 2 names") != null);

    var found = try drinkerWithVars(&arena, "--| @vars x y u v\n");
    defer found.deinit();
    try std.testing.expect(found.items.len > 0);
}

// `@auto eager` set-commit cut. `e1` reaches its subgoal `A` (via `aD`)
// and fails; `n1` proves the goal through `bC`.
fn eagerCutSuggestions(
    arena: *std.heap.ArenaAllocator,
    e1: []const u8,
    n1: []const u8,
) !types.SourceSuggestions {
    const mm0_template =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term G: wff; term A: wff; term B: wff; term C: wff; term D: wff;
        \\--| @auto backward
        \\axiom aD: $ D $ > $ A $;
        \\--| @auto backward
        \\axiom bC: $ C $ > $ B $;
        \\--| @auto E1
        \\axiom e1: $ A $ > $ G $;
        \\--| @auto N1
        \\axiom n1: $ B $ > $ G $;
        \\theorem t (h: $ C $): $ G $;
    ;
    var mm0 = try std.mem.replaceOwned(u8, arena.allocator(), mm0_template, "E1", e1);
    mm0 = try std.mem.replaceOwned(u8, arena.allocator(), mm0, "N1", n1);
    const proof_src =
        \\t
        \\---
        \\
        \\l1: $ G $ by auto?
    ;
    return suggestionsAtNeedle(arena, mm0, proof_src, "auto?", .{
        .generate = .{ .enabled = true },
    });
}

test "an @auto eager step that reaches its subgoals skips the non-eager rules" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    // Without the cut, `n1` proves the goal.
    var uncut = try eagerCutSuggestions(&arena, "backward", "backward");
    defer uncut.deinit();
    try expectOffered(uncut.items, &.{"n1 [bC [#1]]"});
    // `e1` is declared invertible, so once it applies, its failure is the
    // goal's: `n1` is not tried.
    var cut = try eagerCutSuggestions(&arena, "eager", "backward");
    defer cut.deinit();
    try std.testing.expectEqual(@as(usize, 0), cut.items.len);
}

test "the @auto eager cut still tries the other eager rules" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var suggestions = try eagerCutSuggestions(&arena, "eager", "eager 2");
    defer suggestions.deinit();
    try expectOffered(suggestions.items, &.{"n1 [bC [#1]]"});
}

test "the @auto eager cut still tries an eager rule that splits the context" {
    // Every eager rule that applies is tried before the goal gives up, and
    // `wk` not at all once `rleft` or `ror` applies at the root: the proof
    // is `mix`'s, which splits the context into `g , h`. Under `ctx_idem`
    // a share may take the whole context, the `&` with it, so `mix` would
    // grow its own premise without end unless the goal it repeats is seen
    // as such.
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\sort ctx;
        \\term or (a b: wff): wff;
        \\infixr or: $|$ prec 30;
        \\term an (a b: wff): wff;
        \\infixr an: $&$ prec 35;
        \\term P: wff; term Q: wff; term R: wff; term S1: wff; term S2: wff;
        \\term bi (a b: wff): wff;
        \\infixl bi: $<->$ prec 20;
        \\--| @relation wff bi biid bitr bisym mpbi
        \\axiom biid (a: wff): $ a <-> a $;
        \\axiom bitr (a b c: wff): $ a <-> b $ > $ b <-> c $ > $ a <-> c $;
        \\axiom bisym (a b: wff): $ a <-> b $ > $ b <-> a $;
        \\axiom mpbi (a b: wff): $ a <-> b $ > $ a $ > $ b $;
        \\term ctx_eq (g h: ctx): wff;
        \\term emp: ctx;
        \\--| @acui ctx_assoc ctx_comm emp ctx_idem
        \\term join (g h: ctx): ctx;
        \\infixl join: $,$ prec 5;
        \\term hyp (a: wff): ctx;
        \\coercion hyp: wff > ctx;
        \\term seq (d: ctx): wff;
        \\prefix seq: $|-$ prec 1;
        \\--| @relation ctx ctx_eq ctx_refl ctx_trans ctx_sym _
        \\axiom ctx_refl (g: ctx): $ ctx_eq g g $;
        \\axiom ctx_trans (g h i: ctx): $ ctx_eq g h $ > $ ctx_eq h i $ > $ ctx_eq g i $;
        \\axiom ctx_sym (g h: ctx): $ ctx_eq g h $ > $ ctx_eq h g $;
        \\axiom ctx_assoc (g h i: ctx): $ ctx_eq ((g , h) , i) (g , (h , i)) $;
        \\axiom ctx_comm (g h: ctx): $ ctx_eq (g , h) (h , g) $;
        \\axiom ctx_idem (g: ctx): $ ctx_eq (g , g) g $;
        \\axiom ctx_unit (g: ctx): $ ctx_eq (emp , g) g $;
        \\--| @congr
        \\axiom join_congr (g1 g2 h1 h2: ctx): $ ctx_eq g1 g2 $ > $ ctx_eq h1 h2 $ > $ ctx_eq (g1 , h1) (g2 , h2) $;
        \\--| @congr
        \\axiom seq_congr (e f: ctx): $ ctx_eq e f $ > $ (|- e) <-> (|- f) $;
        \\--| @auto eager
        \\axiom rleft (d: ctx) (a b: wff): $ |- a , d $ > $ |- (a | b) , d $;
        \\--| @auto eager 2
        \\axiom ror (d: ctx) (a b: wff): $ |- a , b , d $ > $ |- (a | b) , d $;
        \\--| @auto eager 3
        \\axiom mix (g h: ctx) (a b: wff): $ |- a , g $ > $ |- b , h $ > $ |- (a & b) , g , h $;
        \\--| @auto backward
        \\axiom wk (d: ctx) (a: wff): $ |- d $ > $ |- a , d $;
        \\theorem split_after_cut (h1: $ |- R , (P | Q) $) (h2: $ |- S1 , S2 $): $ |- (P | Q) , (R & (S1 | S2)) $;
    ;
    const proof_src =
        \\split_after_cut
        \\---
        \\
        \\l1: $ |- (P | Q) , (R & (S1 | S2)) $ by auto?
    ;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var suggestions = try suggestionsAtNeedle(&arena, mm0_src, proof_src, "auto?", .{
        .generate = .{ .enabled = true },
    });
    defer suggestions.deinit();
    try expectOffered(suggestions.items, &.{"mix [#1, ror [#2]]"});
}

test "an @auto focus failure does not cover the same goal unfocused" {
    // `imp_left` on the first member leaves `… ⊢ A | B` focused, where only
    // `or_r1`/`or_r2` apply and both fail. The second member's `&` releases
    // focus, so `and_intro` reaches the same goal unfocused at the same
    // depth, where `or_comm` proves it. A failure memo keyed without the
    // focus would skip that goal and miss the proof.
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\sort ctx;
        \\term or (a b: wff): wff;
        \\infixr or: $|$ prec 30;
        \\term an (a b: wff): wff;
        \\infixr an: $&$ prec 35;
        \\term im (a b: wff): wff;
        \\infixr im: $->$ prec 25;
        \\term A: wff; term B: wff; term C: wff;
        \\term bi (a b: wff): wff;
        \\infixl bi: $<->$ prec 20;
        \\--| @relation wff bi biid bitr bisym mpbi
        \\axiom biid (a: wff): $ a <-> a $;
        \\axiom bitr (a b c: wff): $ a <-> b $ > $ b <-> c $ > $ a <-> c $;
        \\axiom bisym (a b: wff): $ a <-> b $ > $ b <-> a $;
        \\axiom mpbi (a b: wff): $ a <-> b $ > $ a $ > $ b $;
        \\term ctx_eq (g h: ctx): wff;
        \\term emp: ctx;
        \\--| @acui ctx_assoc ctx_comm emp ctx_idem
        \\term join (g h: ctx): ctx;
        \\infixl join: $,$ prec 5;
        \\term hyp (a: wff): ctx;
        \\coercion hyp: wff > ctx;
        \\term nd (g: ctx) (a: wff): wff;
        \\infixl nd: $|-$ prec 2;
        \\--| @relation ctx ctx_eq ctx_refl ctx_trans ctx_sym _
        \\axiom ctx_refl (g: ctx): $ ctx_eq g g $;
        \\axiom ctx_trans (g h i: ctx): $ ctx_eq g h $ > $ ctx_eq h i $ > $ ctx_eq g i $;
        \\axiom ctx_sym (g h: ctx): $ ctx_eq g h $ > $ ctx_eq h g $;
        \\axiom ctx_assoc (g h i: ctx): $ ctx_eq ((g , h) , i) (g , (h , i)) $;
        \\axiom ctx_comm (g h: ctx): $ ctx_eq (g , h) (h , g) $;
        \\axiom ctx_idem (g: ctx): $ ctx_eq (g , g) g $;
        \\axiom ctx_unit (g: ctx): $ ctx_eq (emp , g) g $;
        \\--| @congr
        \\axiom join_congr (g1 g2 h1 h2: ctx): $ ctx_eq g1 g2 $ > $ ctx_eq h1 h2 $ > $ ctx_eq (g1 , h1) (g2 , h2) $;
        \\--| @congr
        \\axiom nd_congr (e f: ctx) (a b: wff): $ ctx_eq e f $ > $ a <-> b $ > $ (e |- a) <-> (f |- b) $;
        \\axiom ax (g: ctx) (a: wff): $ g , a |- a $;
        \\--| @auto eager
        \\axiom and_intro (g: ctx) (a b: wff): $ g |- a $ > $ g |- b $ > $ g |- a & b $;
        \\--| @auto focus $ a | b $ : $ a $
        \\axiom or_r1 (g: ctx) (a b: wff): $ g |- a $ > $ g |- a | b $;
        \\--| @auto focus $ a | b $ : $ b $
        \\axiom or_r2 (g: ctx) (a b: wff): $ g |- b $ > $ g |- a | b $;
        \\--| @auto backward
        \\axiom or_comm (g: ctx) (a b: wff): $ g |- b | a $ > $ g |- a | b $;
        \\--| @auto focus $ a -> b $ : $ a $ $ b $
        \\axiom imp_left (g: ctx) (a b c: wff):
        \\  $ g , (a -> b) |- a $ > $ g , b |- c $ > $ g , (a -> b) |- c $;
        \\theorem t: $ ((A | B) -> C) , (((A | B) & (A | B)) -> C) , (B | A) |- C $;
    ;
    const proof_src =
        \\t
        \\---
        \\l1: $ ((A | B) -> C) , (((A | B) & (A | B)) -> C) , (B | A) |- C $ by auto?
    ;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var suggestions = try suggestionsAtNeedle(&arena, mm0_src, proof_src, "auto?", .{
        .generate = .{ .enabled = true },
    });
    defer suggestions.deinit();
    try std.testing.expect(suggestions.items.len > 0);
}

test "auto finds the chain without tripping the stack guard" {
    const proof_src =
        \\t
        \\----
        \\l1: $ R $ by auto?
    ;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{};
    var suggestions = try suggestionsAtNeedle(
        &arena,
        auto_depth2_mm0,
        proof_src,
        "auto?",
        .{ .counters = &counters, .generate = .{ .enabled = true } },
    );
    defer suggestions.deinit();

    try expectOffered(suggestions.items, &.{"qr [pq [p []]]"});
    // The default call-stack guard is generous; a normal proof never trips
    // it.
    try std.testing.expect(counters.core_end == null);
    try std.testing.expectEqual(types.SearchStatus.found, suggestions.status);
}

test "exact does not ground-and-generate the open-hyp chain" {
    const proof_src =
        \\t
        \\----
        \\l1: $ R $ by exact?
    ;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var suggestions = try suggestionsAtNeedle(
        &arena,
        auto_open_mm0,
        proof_src,
        "exact?",
        .{ .generate = .{ .enabled = true } },
    );
    defer suggestions.deinit();
    try std.testing.expectEqual(@as(usize, 0), suggestions.items.len);
}

test "source exact completes inline application from parent expected goal" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term P: wff;
        \\term Q: wff;
        \\axiom p: $ P $;
        \\axiom use: $ P $ > $ Q $;
        \\theorem t: $ Q $;
    ;
    const proof_src =
        \\t
        \\------
        \\l1: $ Q $ by use [exact?]
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

    try std.testing.expect(suggestions.items.len > 0);
    // `[]` keeps the inline rule from re-parsing as a line label.
    try std.testing.expectEqualStrings("p []", suggestions.items[0].replacement);
}

test "source exact inside inline application can resolve to direct ref" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term P: wff;
        \\axiom id (p: wff): $ p $ > $ p $;
        \\theorem t: $ P $ > $ P $;
    ;
    const proof_src =
        \\t
        \\------
        \\l1: $ P $ by id [exact?]
    ;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var counters = types.SearchCounters{ .timing = true };
    var suggestions = try suggestionsAtNeedle(
        &arena,
        mm0_src,
        proof_src,
        "exact?",
        .{ .counters = &counters },
    );
    defer suggestions.deinit();

    try std.testing.expect(suggestions.items.len > 0);
    try std.testing.expectEqualStrings(
        "#1",
        suggestions.items[0].replacement,
    );
    try expectTimingCounter(counters.ref_index_build_ns);
    try expectTimingCounter(counters.ref_lookup_ns);
}

test "source apply completes inline application with unresolved subrefs" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term P: wff;
        \\term Q: wff;
        \\axiom id (p: wff): $ p $ > $ p $;
        \\axiom use: $ P $ > $ Q $;
        \\theorem t: $ P $ > $ Q $;
    ;
    const proof_src =
        \\t
        \\------
        \\l1: $ Q $ by use [apply?]
    ;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var suggestions = try suggestionsAtNeedle(
        &arena,
        mm0_src,
        proof_src,
        "apply?",
        .{},
    );
    defer suggestions.deinit();

    try std.testing.expect(suggestions.items.len > 0);
    try std.testing.expectEqualStrings(
        "id [ref1]",
        suggestions.items[0].replacement,
    );
}

test "source exact inside inline application requires useful parent goal" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term P: wff;
        \\term Q: wff;
        \\term R: wff;
        \\term imp (p q: wff): wff;
        \\infixr imp: $->$ prec 25;
        \\axiom mp (p q: wff): $ p $ > $ p -> q $ > $ q $;
        \\axiom q_imp (p: wff): $ p -> Q $;
        \\theorem t: $ Q $;
    ;
    const proof_src =
        \\t
        \\------
        \\l1: $ Q $ by mp [exact?, exact?]
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

    try std.testing.expectEqual(@as(usize, 0), suggestions.items.len);
}

test "source exact nested inline edit is local" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term P: wff;
        \\term Q: wff;
        \\term R: wff;
        \\axiom id (p: wff): $ p $ > $ p $;
        \\axiom use: $ P $ > $ P $ > $ R $;
        \\theorem t: $ P $ > $ R $;
    ;
    const proof_src =
        \\t
        \\------
        \\l1: $ R $ by use [id [exact?], #1]
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

    try std.testing.expect(suggestions.items.len > 0);
    try std.testing.expectEqualStrings(
        "#1",
        suggestions.items[0].replacement,
    );
    const expected_span = std.mem.indexOf(u8, proof_src, "exact?") orelse {
        return error.MissingNeedle;
    };
    try std.testing.expectEqual(
        expected_span,
        suggestions.items[0].replace_span.start,
    );
    try std.testing.expectEqual(
        expected_span + "exact?".len,
        suggestions.items[0].replace_span.end,
    );
}

test "source exact inside inline ex elim uses sibling and goal" {
    const mm0_src =
        \\delimiter $ ( ) , $;
        \\strict provable sort wff;
        \\sort set;
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
        \\term ex {x: set} (p: wff x): wff;
        \\prefix ex: $∃$ prec 41;
        \\term P (x: set): wff;
        \\term Q: wff;
        \\axiom ctx_refl (G: ctx): $ ctx_eq G G $;
        \\axiom ctx_trans (G H K: ctx):
        \\  $ ctx_eq G H $ > $ ctx_eq H K $ > $ ctx_eq G K $;
        \\axiom ctx_sym (G H: ctx): $ ctx_eq G H $ > $ ctx_eq H G $;
        \\axiom ctx_assoc (G H K: ctx):
        \\  $ ctx_eq ((G , H) , K) (G , (H , K)) $;
        \\axiom ctx_comm (G H: ctx): $ ctx_eq (G , H) (H , G) $;
        \\axiom ctx_idem (G: ctx): $ ctx_eq (G , G) G $;
        \\axiom make_q (H: ctx) {x: set}: $ H , P x ⊢ Q $;
        \\axiom ex_elim {x: set} (G H: ctx x) (p: wff x) (c: wff):
        \\  $ G ⊢ ∃ x p $ > $ H , p ⊢ c $ > $ G , H ⊢ c $;
        \\theorem t (G H: ctx) {x: set}:
        \\  $ G ⊢ ∃ x (P x) $ > $ G , H ⊢ Q $;
    ;
    const proof_src =
        \\t
        \\------
        \\l1: $ H , P x ⊢ Q $ by make_q
        \\l2: $ G , H ⊢ Q $ by ex_elim [#1, exact?]
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

    try std.testing.expect(suggestions.items.len > 0);
    try std.testing.expectEqualStrings(
        "l1",
        suggestions.items[0].replacement,
    );
}

test "source exact inside inline ex elim uses later sibling" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    const mm0_src = try readProofCase(allocator, "zermelo", "mm0");
    const proof_src =
        \\nd_exists_elim_const
        \\--------------------
        \\l1: $ ∃ x p ⊢ ∃ x p $ by ax
        \\l2: $ p → q ⊢ p → q $ by ax
        \\l3: $ p ⊢ p $ by ax
        \\l4: $ p → q , p ⊢ q $ by imp_elim [l2, l3]
        \\l5: $ ∃ x p , p → q ⊢ q $ by ex_elim [exact?, l4]
        \\l6: $ ∃ x p ⊢ (p → q) → q $ by imp_intro [l5]
        \\l7: $ _ ⊢ (∃ x p) → ((p → q) → q) $ by imp_intro [l6]
    ;
    var counters = types.SearchCounters{ .timing = true };
    var suggestions = try suggestionsAtNeedle(
        &arena,
        mm0_src,
        proof_src,
        "exact?",
        .{ .counters = &counters },
    );
    defer suggestions.deinit();

    try expectOffered(suggestions.items, &.{"l1"});
    try expectTimingCounter(counters.ref_lookup_ns);
}

test "extractHypPartialBindings keeps an ACUI binder open for an eigenvariable sibling" {
    // Regression for the `ex_elim` eigenvariable / commutative-ACUI-context
    // interaction (zermelo `cb_branch_fg_injective_mixed l16`). The body
    // hypothesis template `H , p` (= `join(H, hyp(p))`, `H` a bare context
    // binder, `p` the eigenvariable wff) is extracted against a ref whose join
    // is associated so the eigenvariable member `hyp(P s)` sits inside the first
    // positional arg and the trailing arg is a bare (non-`hyp`) context term.
    //
    // The old positional walk pinned `H` to the ref's first arg — swallowing the
    // `hyp(P s)` member — which left `p` unpinnable (no remaining `hyp`-shaped
    // member) and carried the eigenvariable into the rule's context binder.
    // Under a commutative ACUI head the positional walk is now skipped, so the
    // member extractor pins `p` to the unique `hyp` member and leaves the bare
    // binder `H` open for the validator's ACUI weakening.
    const mm0_src =
        \\delimiter $ ( ) , $;
        \\strict provable sort wff;
        \\sort set;
        \\sort ctx;
        \\term ctx_eq (G H: ctx): wff;
        \\term emp: ctx;
        \\notation emp: ctx = ($_$:max);
        \\--| @acui ctx_assoc ctx_comm emp ctx_idem
        \\term join (G H: ctx): ctx;
        \\infixl join: $,$ prec 5;
        \\term hyp (p: wff): ctx;
        \\coercion hyp: wff > ctx;
        \\term ca: ctx;
        \\term cb: ctx;
        \\term s0: set;
        \\term P (x: set): wff;
        \\axiom ctx_assoc (G H K: ctx):
        \\  $ ctx_eq ((G , H) , K) (G , (H , K)) $;
        \\axiom ctx_comm (G H: ctx): $ ctx_eq (G , H) (H , G) $;
        \\axiom ctx_idem (G: ctx): $ ctx_eq (G , G) G $;
        \\theorem t (G: ctx): $ ctx_eq G G $;
    ;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();

    var fixture = try fixtureFor(allocator, mm0_src, "t");
    var harness = ContextHarness.init(allocator);
    defer harness.deinit();
    const context = harness.context(&fixture);

    const ti_join = fixture.theory.env.term_names.get("join").?;
    const ti_hyp = fixture.theory.env.term_names.get("hyp").?;
    const ti_ca = fixture.theory.env.term_names.get("ca").?;
    const ti_cb = fixture.theory.env.term_names.get("cb").?;
    const ti_s0 = fixture.theory.env.term_names.get("s0").?;
    const ti_P = fixture.theory.env.term_names.get("P").?;

    var theorem = TheoremContext.init(allocator);
    defer theorem.deinit();
    const s0 = try theorem.interner.internApp(ti_s0, &.{});
    const px = try theorem.interner.internApp(ti_P, &.{s0});
    const hyp_px = try theorem.interner.internApp(ti_hyp, &.{px});
    const ca = try theorem.interner.internApp(ti_ca, &.{});
    const cb = try theorem.interner.internApp(ti_cb, &.{});
    // Ref: `join(join(ca, hyp(P s)), cb)` — eigenvariable member buried in the
    // first positional arg, trailing arg a bare (non-`hyp`) context term.
    const inner = try theorem.interner.internApp(ti_join, &.{ ca, hyp_px });
    const ref = try theorem.interner.internApp(ti_join, &.{ inner, cb });

    // Template `join(binder0, hyp(binder1))`: binder0 = bare context `H`,
    // binder1 = the eigenvariable wff `p`.
    const hyp_p_args = [_]TemplateExpr{.{ .binder = 1 }};
    const hyp_p = TemplateExpr{ .app = .{ .term_id = ti_hyp, .args = &hyp_p_args } };
    const join_args = [_]TemplateExpr{ .{ .binder = 0 }, hyp_p };
    const template = TemplateExpr{ .app = .{ .term_id = ti_join, .args = &join_args } };

    var bindings = [_]?ExprId{ null, null };
    def_match.extractHypPartialBindings(
        &context,
        &theorem,
        template,
        ref,
        &bindings,
    );

    // `p` (binder 1) is pinned to the unique `hyp` member; the bare context
    // binder `H` (binder 0) stays open rather than swallowing it.
    try std.testing.expectEqual(@as(?ExprId, px), bindings[1]);
    try std.testing.expectEqual(@as(?ExprId, null), bindings[0]);
}

test "extractHypPartialBindings reads only arguments the head determines" {
    // `kst` drops its second argument, so `kst a b` against `kst a c` forces
    // the first binder but not the second: `kst a x` matches `kst a c` for any
    // `x`. The redex prune turns these bindings into rejects, so a guess here
    // would discard a provable candidate.
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\sort obj;
        \\term pr (a: obj): wff;
        \\term a0: obj;
        \\term c0: obj;
        \\def kst (a b: obj): obj = $ a $;
        \\theorem t: $ pr a0 $;
    ;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();

    var fixture = try fixtureFor(allocator, mm0_src, "t");
    var harness = ContextHarness.init(allocator);
    defer harness.deinit();
    const context = harness.context(&fixture);

    const ti_pr = fixture.theory.env.term_names.get("pr").?;
    const ti_kst = fixture.theory.env.term_names.get("kst").?;
    var theorem = TheoremContext.init(allocator);
    defer theorem.deinit();
    const a0 = try theorem.interner.internApp(fixture.theory.env.term_names.get("a0").?, &.{});
    const c0 = try theorem.interner.internApp(fixture.theory.env.term_names.get("c0").?, &.{});
    const kst_ref = try theorem.interner.internApp(ti_kst, &.{ a0, c0 });
    const ref = try theorem.interner.internApp(ti_pr, &.{kst_ref});

    // Template `pr (kst binder0 binder1)`.
    const kst_args = [_]TemplateExpr{ .{ .binder = 0 }, .{ .binder = 1 } };
    const kst_t = TemplateExpr{ .app = .{ .term_id = ti_kst, .args = &kst_args } };
    const pr_args = [_]TemplateExpr{kst_t};
    const template = TemplateExpr{ .app = .{ .term_id = ti_pr, .args = &pr_args } };

    var bindings = [_]?ExprId{ null, null };
    def_match.extractHypPartialBindings(&context, &theorem, template, ref, &bindings);

    try std.testing.expectEqual(@as(?ExprId, a0), bindings[0]);
    try std.testing.expectEqual(@as(?ExprId, null), bindings[1]);
}

test "source exact inside inline or_elim uses sibling branch" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    const mm0_src = try readProofCase(allocator, "zermelo", "mm0");
    const proof_src =
        \\nd_or_comm
        \\----------
        \\l1: $ p ∨ q ⊢ p ∨ q $ by ax
        \\l2: $ p ⊢ p $ by ax
        \\l3: $ p ⊢ q ∨ p $ by or_intro_r [l2]
        \\l4: $ q ⊢ q $ by ax
        \\l5: $ q ⊢ q ∨ p $ by or_intro_l [l4]
        \\l6: $ p ∨ q ⊢ q ∨ p $ by or_elim [l1, exact?, l5]
        \\l7: $ _ ⊢ (p ∨ q) → (q ∨ p) $ by imp_intro [l6]
    ;
    var suggestions = try suggestionsAtNeedle(
        &arena,
        mm0_src,
        proof_src,
        "exact?",
        .{},
    );
    defer suggestions.deinit();

    try expectOffered(suggestions.items, &.{"l3"});
}

test "source exact inline search supports view candidates" {
    const mm0_src =
        \\delimiter $ ( ) [ / ] $;
        \\provable sort wff;
        \\--| @vars x y z t
        \\sort nat;
        \\term ex {x: nat} (p: wff x): wff;
        \\prefix ex: $E$ prec 41;
        \\term sb_f {x: nat} (t: nat x) (p: wff x): wff;
        \\notation sb_f {x: nat} (t: nat x) (p: wff x): wff =
        \\  ($[$:41) x ($/$:0) t ($]$:0) p;
        \\term sb_s {x: nat} (t: nat x) (a: nat x): nat;
        \\notation sb_s {x: nat} (t: nat x) (a: nat x): nat =
        \\  ($subst$:41) x ($/$:0) t a;
        \\term P (a: nat): wff;
        \\term c: nat;
        \\term Goal: wff;
        \\term iff (a b: wff): wff;
        \\infixr iff: $<->$ prec 20;
        \\term nat_eq (a b: nat): wff;
        \\infixl nat_eq: $==$ prec 35;
        \\--| @relation wff iff iff_refl iff_trans iff_sym iff_mp
        \\axiom iff_refl (a: wff): $ a <-> a $;
        \\axiom iff_trans (a b c: wff):
        \\  $ a <-> b $ > $ b <-> c $ > $ a <-> c $;
        \\axiom iff_sym (a b: wff): $ a <-> b $ > $ b <-> a $;
        \\axiom iff_mp (a b: wff): $ a <-> b $ > $ a $ > $ b $;
        \\--| @relation nat nat_eq eq_refl eq_trans eq_sym _
        \\axiom eq_refl (a: nat): $ a == a $;
        \\axiom eq_trans (a b c: nat): $ a == b $ > $ b == c $ > $ a == c $;
        \\axiom eq_sym (a b: nat): $ a == b $ > $ b == a $;
        \\--| @congr
        \\axiom P_congr (a b: nat): $ a == b $ > $ P a <-> P b $;
        \\--| @rewrite
        \\axiom sb_f_P {x: nat} (t a: nat x):
        \\  $ [x/t] (P a) <-> P (subst x / t a) $;
        \\--| @rewrite
        \\axiom sb_s_var {x: nat} (t: nat x): $ subst x / t x == t $;
        \\axiom have_Pc: $ P c $;
        \\--| @view {x: nat} (t: nat x) (p: wff x) (q: wff): $ q $ > $ E x p $
        \\--| @recover t q p x
        \\axiom ex_intro {x: nat} (t: nat x) (p: wff x):
        \\  $ [x/t] p $ > $ E x p $;
        \\axiom use_exists {x: nat}: $ E x (P x) $ > $ Goal $;
        \\theorem prove_goal {x: nat}: $ Goal $;
    ;
    const proof_src =
        \\prove_goal
        \\----------
        \\l1: $ P c $ by have_Pc
        \\l2: $ Goal $ by use_exists (x := $ x $) [exact?]
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

    try expectOffered(suggestions.items, &.{"ex_intro [l1]"});
}

// Guard for the `recoverGuardRejects` soundness fix: a `@recover` whose target
// is already pinned (here `t` from the conclusion match) must NOT be used as a
// pruning guard. `myrule` mirrors `sep_intro_imp2`: its `@recover t q p x` names
// the shared implication antecedent `q` as the source, which is NOT the
// substituted motive, so walking `q` against the motive pattern `p` "provably
// fails". Before the fix the search pruned both valid refs and never assembled
// `myrule [l1, l2]`; `applyRecover` skips the (target-resolved) law during real
// validation, so the prune was unsound.
test "exact search keeps view candidate when a pinned-target recover diverges" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\--| @vars x y z
        \\sort set;
        \\term imp (a b: wff): wff;
        \\term Mem (t A: set): wff;
        \\term Sep {x: set} (A: set) (p: wff x): set;
        \\term Phi: wff;
        \\term Psi: wff;
        \\term AA: set;
        \\term TT: set;
        \\axiom ref1: $ imp Psi (Mem TT AA) $;
        \\axiom ref2: $ imp Psi Phi $;
        \\--| @view {x: set} (t A: set) (p: wff x) (q r s: wff): $ imp q r $ > $ imp q s $ > $ imp q (Mem t (Sep x A p)) $
        \\--| @recover t q p x
        \\axiom myrule {x: set} (t A: set) (p: wff x) (q: wff):
        \\  $ imp q (Mem t A) $ > $ imp q p $ > $ imp q (Mem t (Sep x A p)) $;
        \\theorem prove_goal {x: set}: $ imp Psi (Mem TT (Sep x AA Phi)) $;
    ;
    const proof_src =
        \\prove_goal
        \\----------
        \\l1: $ imp Psi (Mem TT AA) $ by ref1
        \\l2: $ imp Psi Phi $ by ref2
        \\l3: $ imp Psi (Mem TT (Sep x AA Phi)) $ by exact?
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

    try expectOffered(suggestions.items, &.{"myrule [l1, l2]"});
}

test "recover member injection skips pinned-target laws" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\sort ctx;
        \\sort set;
        \\term ctx_eq (G H: ctx): wff;
        \\term emp: ctx;
        \\--| @acui ctx_assoc ctx_comm emp ctx_idem
        \\term join (G H: ctx): ctx;
        \\term hyp (p: wff): ctx;
        \\term nd (G: ctx) (p: wff): wff;
        \\term Mem (t A: set): wff;
        \\term Sep {x: set} (A: set) (p: wff x): set;
        \\term Phi: wff;
        \\term Psi: wff;
        \\term AA: set;
        \\term TT: set;
        \\axiom ctx_refl (G: ctx): $ ctx_eq G G $;
        \\axiom ctx_trans (G H K: ctx):
        \\  $ ctx_eq G H $ > $ ctx_eq H K $ > $ ctx_eq G K $;
        \\axiom ctx_sym (G H: ctx): $ ctx_eq G H $ > $ ctx_eq H G $;
        \\axiom ctx_assoc (G H K: ctx):
        \\  $ ctx_eq (join (join G H) K) (join G (join H K)) $;
        \\axiom ctx_comm (G H: ctx): $ ctx_eq (join G H) (join H G) $;
        \\axiom ctx_idem (G: ctx): $ ctx_eq (join G G) G $;
        \\axiom ref1: $ nd (join emp (hyp Psi)) (Mem TT AA) $;
        \\axiom ref2: $ nd (join emp (hyp Psi)) Phi $;
        \\--| @view {x: set} (t A: set) (p: wff x) (q r s: wff): $ nd (join emp (hyp q)) r $ > $ nd (join emp (hyp q)) s $ > $ nd emp (Mem t (Sep x A p)) $
        \\--| @recover t q p x
        \\axiom myrule {x: set} (t A: set) (p: wff x) (q: wff):
        \\  $ nd (join emp (hyp q)) (Mem t A) $ >
        \\  $ nd (join emp (hyp q)) p $ >
        \\  $ nd emp (Mem t (Sep x A p)) $;
        \\theorem prove_goal {x: set}: $ nd emp (Mem TT (Sep x AA Phi)) $;
    ;
    const proof_src =
        \\prove_goal
        \\----------
        \\l1: $ nd (join emp (hyp Psi)) (Mem TT AA) $ by ref1
        \\l2: $ nd (join emp (hyp Psi)) Phi $ by ref2
        \\l3: $ nd emp (Mem TT (Sep x AA Phi)) $ by exact?
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

    try expectOffered(suggestions.items, &.{"myrule [l1, l2]"});
}

// `@auto bridge`: `wk` fills its premise from the pool only. `rleft [wk [#1]]`
// pushes the weakening to the leaf, where the pool closes it; `wk [dbl [#1]]`
// would have `wk` generate its premise, which a bridge rule never does.
fn bridgeSuggestions(
    arena: *std.heap.ArenaAllocator,
    wk_mode: []const u8,
    goal: []const u8,
) !types.SourceSuggestions {
    const mm0_template =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\sort ctx;
        \\term or (a b: wff): wff;
        \\infixr or: $|$ prec 30;
        \\term an (a b: wff): wff;
        \\infixr an: $&$ prec 35;
        \\term P: wff; term Q: wff; term R: wff;
        \\term bi (a b: wff): wff;
        \\infixl bi: $<->$ prec 20;
        \\--| @relation wff bi biid bitr bisym mpbi
        \\axiom biid (a: wff): $ a <-> a $;
        \\axiom bitr (a b c: wff): $ a <-> b $ > $ b <-> c $ > $ a <-> c $;
        \\axiom bisym (a b: wff): $ a <-> b $ > $ b <-> a $;
        \\axiom mpbi (a b: wff): $ a <-> b $ > $ a $ > $ b $;
        \\term ctx_eq (g h: ctx): wff;
        \\term emp: ctx;
        \\--| @acui ctx_assoc ctx_comm emp ctx_idem
        \\term join (g h: ctx): ctx;
        \\infixl join: $,$ prec 5;
        \\term hyp (a: wff): ctx;
        \\coercion hyp: wff > ctx;
        \\term seq (d: ctx): wff;
        \\prefix seq: $|-$ prec 1;
        \\--| @relation ctx ctx_eq ctx_refl ctx_trans ctx_sym _
        \\axiom ctx_refl (g: ctx): $ ctx_eq g g $;
        \\axiom ctx_trans (g h i: ctx): $ ctx_eq g h $ > $ ctx_eq h i $ > $ ctx_eq g i $;
        \\axiom ctx_sym (g h: ctx): $ ctx_eq g h $ > $ ctx_eq h g $;
        \\axiom ctx_assoc (g h i: ctx): $ ctx_eq ((g , h) , i) (g , (h , i)) $;
        \\axiom ctx_comm (g h: ctx): $ ctx_eq (g , h) (h , g) $;
        \\axiom ctx_idem (g: ctx): $ ctx_eq (g , g) g $;
        \\axiom ctx_unit (g: ctx): $ ctx_eq (emp , g) g $;
        \\--| @congr
        \\axiom join_congr (g1 g2 h1 h2: ctx): $ ctx_eq g1 g2 $ > $ ctx_eq h1 h2 $ > $ ctx_eq (g1 , h1) (g2 , h2) $;
        \\--| @congr
        \\axiom seq_congr (e f: ctx): $ ctx_eq e f $ > $ (|- e) <-> (|- f) $;
        \\--| @auto eager
        \\axiom rleft (d: ctx) (a b: wff): $ |- a , d $ > $ |- (a | b) , d $;
        \\--| @auto backward
        \\axiom dbl (a: wff): $ |- a $ > $ |- a & a $;
        \\--| @auto WK
        \\axiom wk (d: ctx) (a: wff): $ |- d $ > $ |- a , d $;
        \\theorem t (h1: $ |- Q $): $ GOAL $;
    ;
    var mm0 = try std.mem.replaceOwned(u8, arena.allocator(), mm0_template, "WK", wk_mode);
    mm0 = try std.mem.replaceOwned(u8, arena.allocator(), mm0, "GOAL", goal);
    const proof_template =
        \\t
        \\---
        \\
        \\l1: $ GOAL $ by auto?
    ;
    const proof_src = try std.mem.replaceOwned(u8, arena.allocator(), proof_template, "GOAL", goal);
    return suggestionsAtNeedle(arena, mm0, proof_src, "auto?", .{
        .generate = .{ .enabled = true },
    });
}

test "an @auto bridge rule closes a generated premise from the pool" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var suggestions = try bridgeSuggestions(&arena, "bridge", "|- (Q | P) , R");
    defer suggestions.deinit();
    try expectOffered(suggestions.items, &.{"rleft [wk [#1]]"});
}

test "an @auto bridge rule never generates its premise" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    // `dbl`'s conclusion carries no context, so only `wk` generating its
    // premise reaches `dbl`: a backward `wk` finds it, a bridge `wk` does not.
    var backward = try bridgeSuggestions(&arena, "backward", "|- (Q & Q) , R");
    defer backward.deinit();
    try expectOffered(backward.items, &.{"wk [dbl [#1]]"});
    var bridge = try bridgeSuggestions(&arena, "bridge", "|- (Q & Q) , R");
    defer bridge.deinit();
    try std.testing.expectEqual(@as(usize, 0), bridge.items.len);
}
