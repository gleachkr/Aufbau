const helpers = @import("./helpers.zig");
const std = helpers.std;
const types = helpers.types;
const source = helpers.source;
const acui = helpers.acui;
const ExprId = helpers.ExprId;
const Canonicalizer = @import("../../../normalizer.zig").Canonicalizer;
const Analyze = @import("../../pipeline/analyze.zig");
const ProofScript = @import("../../../proof_script.zig");
const CompilerContext = @import("../../context.zig").CompilerContext;
const DiagnosticSink = @import("../../diagnostic_sink.zig").DiagnosticSink;
const TheoremContext = helpers.TheoremContext;
const Check = helpers.Check;
const apply = helpers.apply;
const fixtureFor = helpers.fixtureFor;
const parseGoal = helpers.parseGoal;
const expectTimingCounter = helpers.expectTimingCounter;
const ContextHarness = helpers.ContextHarness;
const expectApplyContains = helpers.expectApplyContains;
const expectInlineSearch = helpers.expectInlineSearch;
const suggestionsAtNeedle = helpers.suggestionsAtNeedle;
const expectOffered = helpers.expectOffered;

test "search candidate matches exactly" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term P: wff;
        \\axiom p: $ P $;
        \\theorem t: $ P $;
    ;
    const proof_src =
        \\t
        \\------
        \\l1: $ P $ by p
    ;
    try expectInlineSearch(mm0_src, proof_src, "t", 0);
}

test "apply search finds exact zero-hypothesis candidates" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term P: wff;
        \\term Q: wff;
        \\axiom p: $ P $;
        \\axiom q: $ Q $;
        \\theorem t: $ P $;
    ;
    try expectApplyContains(mm0_src, "t", "P", "p", 0, 0);
}

test "source search records search counters" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term P: wff;
        \\axiom p: $ P $;
        \\axiom id (p: wff): $ p $ > $ p $;
        \\theorem t: $ P $ > $ P $;
    ;
    const proof_src =
        \\t
        \\----
        \\l1: $ P $ by exact?
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

    // `p`; `id [#1]` proves `P` by itself, a repeat.
    try std.testing.expectEqual(@as(usize, 1), suggestions.items.len);
    try std.testing.expectEqual(@as(usize, 0), counters.conclusion_probes);
    try std.testing.expectEqual(@as(usize, 1), counters.ref_pool_size);
    try std.testing.expect(counters.full_try_candidate_calls > 0);
    try expectTimingCounter(counters.cold_setup_ns);
    try expectTimingCounter(counters.warm_search_ns);
}

test "a line takes the offset its newline ends at" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term P: wff;
        \\term Q: wff;
        \\axiom p: $ P $;
        \\axiom q: $ Q $;
        \\theorem t: $ P $;
        \\theorem u: $ Q $;
    ;
    const t = "t\n----\nl1: $ P $ by auto?\n";
    const u = "u\n----\nl1: $ Q $ by auto?\n";
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    for ([_]struct { offset: usize, target: ?usize }{
        .{ .offset = t.len - 1, .target = 0 },
        .{ .offset = t.len, .target = 0 },
        .{ .offset = t.len + 1, .target = null },
        .{ .offset = t.len + u.len, .target = t.len },
    }) |case| {
        const suggestions = try source.suggestionsAtSourceOffset(
            allocator,
            mm0_src,
            t ++ u,
            case.offset,
            .{ .generate = .{ .enabled = true } },
        );
        const start: ?usize = if (case.target) |block| block + "t\n----\n".len else null;
        try std.testing.expectEqual(
            start,
            if (suggestions.target_span) |span| span.start else null,
        );
    }
}

test "source suggestions can apply at an ordinary rule offset" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term P: wff;
        \\term Q: wff;
        \\axiom p: $ P $;
        \\axiom q: $ Q $;
        \\axiom keep (a: wff): $ a $ > $ a $;
        \\theorem t: $ P $;
    ;
    const proof_src =
        \\t
        \\----
        \\l1: $ P $ by ke
    ;
    const rule_start = std.mem.indexOf(u8, proof_src, "ke") orelse {
        return error.MissingNeedle;
    };
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var suggestions = try source.suggestionsAtSourceOffset(
        arena.allocator(),
        mm0_src,
        proof_src,
        rule_start + "ke".len,
        .{ .apply_at_offset = true },
    );
    defer suggestions.deinit();

    try std.testing.expect(suggestions.target_span != null);
    var found_p = false;
    var found_keep = false;
    for (suggestions.items) |item| {
        try std.testing.expectEqualStrings(
            "ke",
            proof_src[item.replace_span.start..item.replace_span.end],
        );
        if (std.mem.eql(u8, item.replacement, "p")) found_p = true;
        if (std.mem.eql(u8, item.replacement, "keep")) found_keep = true;
        try std.testing.expect(!std.mem.startsWith(
            u8,
            item.replacement,
            "q",
        ));
    }
    try std.testing.expect(found_p);
    try std.testing.expect(found_keep);
}

test "source suggestions report found and miss status" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term P: wff;
        \\term Q: wff;
        \\axiom p: $ P $;
        \\theorem t: $ P $;
    ;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    // Provable goal, no caller counters: the local counters block still
    // derives the status.
    const found_src =
        \\t
        \\----
        \\l1: $ P $ by exact?
    ;
    var found = try suggestionsAtNeedle(
        &arena,
        mm0_src,
        found_src,
        "exact?",
        .{},
    );
    defer found.deinit();
    try std.testing.expect(found.items.len > 0);
    try std.testing.expectEqual(types.SearchStatus.found, found.status);

    // No rule concludes `Q`: the search runs to completion empty-handed.
    const miss_src =
        \\t
        \\----
        \\l1: $ Q $ by exact?
    ;
    var miss = try suggestionsAtNeedle(
        &arena,
        mm0_src,
        miss_src,
        "exact?",
        .{},
    );
    defer miss.deinit();
    try std.testing.expectEqual(@as(usize, 0), miss.items.len);
    try std.testing.expectEqual(types.SearchStatus.miss, miss.status);
    try std.testing.expect(miss.target_span != null);
}

// #156: a broken sibling line must not cost the block its search actions.
// The lenient parse keeps the block; the incomplete line contributes nothing
// to the checked context (same as a placeholder), and the target still
// searches.
test "source suggestions survive a broken sibling line" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term P: wff;
        \\term Q: wff;
        \\axiom p: $ P $;
        \\axiom q: $ Q $;
        \\theorem t: $ Q $;
    ;
    const proof_src =
        \\t
        \\----
        \\l1: $ P $ by p []
        \\l2: $ P $ by [#1]
        \\l3: $ Q $ by exact?
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
    try std.testing.expectEqual(types.SearchStatus.found, suggestions.status);
}

// An earlier placeholder line is admitted like `sorry!` when its assertion
// is concrete, so a later search can cite it. A holey one is unfinished; a
// line citing it is admitted on its own concrete assertion.
test "source suggestions cite earlier placeholder lines" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\--| @hole HOLE
        \\provable sort wff;
        \\term P: wff;
        \\term Q: wff;
        \\term R: wff;
        \\axiom pq: $ P $ > $ Q $;
        \\axiom qr: $ Q $ > $ R $;
        \\theorem t: $ R $;
    ;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    const concrete_src =
        \\t
        \\---
        \\l1: $ Q $ by ?
        \\l2: $ R $ by exact?
    ;
    var concrete = try suggestionsAtNeedle(
        &arena,
        mm0_src,
        concrete_src,
        "exact?",
        .{},
    );
    defer concrete.deinit();
    try std.testing.expectEqual(types.SearchStatus.found, concrete.status);
    try expectOffered(concrete.items, &.{"qr [l1]"});

    const holey_src =
        \\t
        \\---
        \\l1: $ HOLE $ by ?
        \\l2: $ Q $ by pq [l1]
        \\l3: $ R $ by exact?
    ;
    var holey = try suggestionsAtNeedle(
        &arena,
        mm0_src,
        holey_src,
        "exact?",
        .{},
    );
    defer holey.deinit();
    try std.testing.expectEqual(types.SearchStatus.found, holey.status);
    try expectOffered(holey.items, &.{"qr [l2]"});
}

// The search replays earlier lines through the checker's own walk, so a line
// the checker rejects blocks the search rather than joining its context: a
// `sorry!` with arguments, and a duplicate label.
test "source suggestions are blocked by a line the checker rejects" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term P: wff;
        \\term Q: wff;
        \\term R: wff;
        \\axiom qr: $ Q $ > $ R $;
        \\theorem t: $ P $ > $ R $;
    ;
    const cases = [_]struct { src: []const u8, blocker: []const u8 }{
        .{
            .src =
            \\t
            \\---
            \\l1: $ Q $ by sorry! [#1]
            \\l2: $ R $ by exact?
            ,
            .blocker = "l1",
        },
        .{
            .src =
            \\t
            \\---
            \\l1: $ Q $ by sorry!
            \\l1: $ Q $ by sorry!
            \\l2: $ R $ by exact?
            ,
            .blocker = "l1: $ Q $ by sorry!\nl1",
        },
    };
    for (cases) |case| {
        var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
        defer arena.deinit();
        var suggestions = try suggestionsAtNeedle(
            &arena,
            mm0_src,
            case.src,
            "exact?",
            .{},
        );
        defer suggestions.deinit();
        try std.testing.expectEqual(@as(usize, 0), suggestions.items.len);
        const blocker_end = std.mem.indexOf(u8, case.src, case.blocker).? +
            case.blocker.len;
        try std.testing.expectEqual(blocker_end - "l1".len, suggestions.blocked_by.?.start);
    }

    // A well-formed `sorry!` stays citable: the search explores what follows
    // from it.
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var cited = try suggestionsAtNeedle(
        &arena,
        mm0_src,
        \\t
        \\---
        \\l1: $ Q $ by sorry!
        \\l2: $ R $ by exact?
    ,
        "exact?",
        .{},
    );
    defer cited.deinit();
    try std.testing.expectEqual(types.SearchStatus.found, cited.status);
    try expectOffered(cited.items, &.{"qr [l1]"});
}

// Same story one block earlier: a local lemma before the target holds the
// broken line. The lenient proof stream keeps the fixture build alive.
test "source suggestions survive a broken line in a preceding local lemma" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term P: wff;
        \\term Q: wff;
        \\axiom p: $ P $;
        \\axiom q: $ Q $;
        \\theorem t: $ Q $;
    ;
    const proof_src =
        \\lemma h: $ P $
        \\----
        \\h1: $ P $ by [#1]
        \\
        \\t
        \\----
        \\l1: $ Q $ by exact?
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
    try std.testing.expectEqual(types.SearchStatus.found, suggestions.status);
}

test "searchPlaceholders survives a broken sibling line" {
    const proof_src =
        \\t
        \\----
        \\l1: $ P $ by [#1]
        \\l2: $ Q $ by auto?
    ;
    const placeholders = try source.searchPlaceholders(
        std.testing.allocator,
        proof_src,
    );
    defer std.testing.allocator.free(placeholders);

    try std.testing.expectEqual(@as(usize, 1), placeholders.len);
    try std.testing.expectEqual(
        source.SearchPlaceholder.Kind.auto,
        placeholders[0].kind,
    );
}

// A malformed block header costs only its own block: the scanners and the
// search walk skip to the next item, as the analysis walk does, so the
// lemma after it stays in scope for the marker below.
test "source search survives a broken block header before its target" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term P: wff;
        \\term Q: wff;
        \\axiom p: $ P $;
        \\axiom q: $ Q $;
        \\theorem s: $ P $;
        \\theorem t: $ Q $;
    ;
    const proof_src =
        \\s
        \\-
        \\l1: $ P $ by p []
        \\
        \\lemma h: $ Q $
        \\----
        \\h1: $ Q $ by q []
        \\
        \\t
        \\----
        \\l1: $ Q $ by exact?
    ;
    const placeholders = try source.searchPlaceholders(
        std.testing.allocator,
        proof_src,
    );
    defer std.testing.allocator.free(placeholders);
    try std.testing.expectEqual(@as(usize, 1), placeholders.len);
    try std.testing.expectEqualStrings("t", placeholders[0].theorem);

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
    try expectOffered(suggestions.items, &.{"h"});
}

test "placeholderNotices warns per placeholder and rejects bad parameters" {
    const proof_src =
        \\t
        \\----
        \\l1: $ P $ by exact?
        \\l2: $ Q $ by auto? (depht: 8, depth: 2)
    ;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const notices = try source.placeholderNotices(arena.allocator(), proof_src);

    try std.testing.expectEqual(@as(usize, 3), notices.len);
    try std.testing.expectEqual(.placeholder, notices[0].kind);
    try std.testing.expectEqualStrings(
        "exact? placeholder: search not yet run " ++
            "(request code actions here to search)",
        notices[0].message,
    );
    try std.testing.expectEqual(.placeholder, notices[1].kind);
    try std.testing.expectEqual(
        source.SearchPlaceholder.Kind.auto,
        notices[1].placeholder.kind,
    );
    // Only the misspelt name is rejected, on its own span.
    try std.testing.expectEqual(.parameter, notices[2].kind);
    try std.testing.expectEqualStrings(
        "depht",
        proof_src[notices[2].span.start..notices[2].span.end],
    );
}

// Local def and notation items are not blocks. The editor-facing walkers must
// step over them rather than stop (enumeration) or fail (targeting) there.
test "searchPlaceholders enumerates past local def and notation items" {
    const proof_src =
        \\def limp (a b: wff): wff = $ a -> b $
        \\infixr limp: $=>$ prec 25;
        \\
        \\t
        \\----
        \\l1: $ Q $ by auto?
    ;
    const placeholders = try source.searchPlaceholders(
        std.testing.allocator,
        proof_src,
    );
    defer std.testing.allocator.free(placeholders);

    try std.testing.expectEqual(@as(usize, 1), placeholders.len);
    try std.testing.expectEqual(
        source.SearchPlaceholder.Kind.auto,
        placeholders[0].kind,
    );
}

test "source suggestions target a line after local def and notation items" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term imp (a b: wff): wff;
        \\infixr imp: $->$ prec 25;
        \\term P: wff;
        \\term Q: wff;
        \\axiom p: $ P $;
        \\axiom q: $ Q $;
        \\theorem t: $ Q $;
    ;
    const proof_src =
        \\def limp (a b: wff): wff = $ a -> b $
        \\infixr limp: $=>$ prec 25;
        \\
        \\t
        \\----
        \\l1: $ Q $ by exact?
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
    try std.testing.expectEqual(types.SearchStatus.found, suggestions.status);
}

// A trailing local lemma has no public anchor block; its search scope is the
// whole mm0 (mirrors `drainTrailingLocalProofItems` on the compile path).
test "source suggestions work in a trailing local lemma" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term P: wff;
        \\axiom p: $ P $;
        \\theorem t: $ P $;
    ;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    // Lemmas-only proof source: no public block at all.
    const solo_src =
        \\lemma l: $ P $
        \\----
        \\l1: $ P $ by exact?
    ;
    var solo = try suggestionsAtNeedle(
        &arena,
        mm0_src,
        solo_src,
        "exact?",
        .{},
    );
    defer solo.deinit();
    try std.testing.expect(solo.items.len > 0);
    try std.testing.expectEqual(types.SearchStatus.found, solo.status);

    // A lemma after the last public block (trailing, not anchored).
    const trailing_src =
        \\t
        \\----
        \\l1: $ P $ by p []
        \\
        \\lemma l: $ P $
        \\----
        \\l1: $ P $ by exact?
    ;
    var trailing = try suggestionsAtNeedle(
        &arena,
        mm0_src,
        trailing_src,
        "exact?",
        .{},
    );
    defer trailing.deinit();
    try std.testing.expect(trailing.items.len > 0);
    try std.testing.expectEqual(types.SearchStatus.found, trailing.status);
}

// Three rules share the shape `P (f y x) x` and differ only in the head `f`:
// a primitive `h`, a def `K` that drops its second argument, and a `@rewrite`
// head `k2` that reduces to its first. Against `P (f a b) c` the re-pin may pin
// `x := b` only through `h`: `K a b ≡ K a c` and `k2 a b ≡ k2 a c`, so there
// `x := c` is still possible and pinning `x := b` would refute it.
const repin_heads_mm0 =
    \\delimiter $ ( ) $;
    \\provable sort wff;
    \\sort obj;
    \\term bi (a b: wff): wff;
    \\infixl bi: $<->$ prec 5;
    \\--| @relation wff bi biid bitr bisym mpbi
    \\axiom biid (a: wff): $ a <-> a $;
    \\axiom bitr (a b c: wff): $ a <-> b $ > $ b <-> c $ > $ a <-> c $;
    \\axiom bisym (a b: wff): $ a <-> b $ > $ b <-> a $;
    \\axiom mpbi (a b: wff): $ a <-> b $ > $ a $ > $ b $;
    \\term oeq (a b: obj): wff;
    \\infixl oeq: $==$ prec 10;
    \\--| @relation obj oeq oeq_refl oeq_trans oeq_sym _
    \\axiom oeq_refl (a: obj): $ a == a $;
    \\axiom oeq_trans (a b c: obj): $ a == b $ > $ b == c $ > $ a == c $;
    \\axiom oeq_sym (a b: obj): $ a == b $ > $ b == a $;
    \\term P (a b: obj): wff;
    \\--| @congr
    \\axiom P_congr (a b c d: obj): $ a == b $ > $ c == d $ > $ P a c <-> P b d $;
    \\term h (a b: obj): obj;
    \\def K (a b: obj): obj = $ a $;
    \\term k2 (a b: obj): obj;
    \\--| @congr
    \\axiom k2_congr (a b c d: obj): $ a == b $ > $ c == d $ > $ k2 a c == k2 b d $;
    \\--| @rewrite
    \\axiom k2_drop (a b: obj): $ k2 a b == a $;
    \\axiom r_h (y x: obj): $ P (h y x) x $;
    \\axiom r_K (y x: obj): $ P (K y x) x $;
    \\axiom r_k2 (y x: obj): $ P (k2 y x) x $;
    \\term R (a: obj): wff;
    \\term Q (a: obj): wff;
    \\axiom r3 (y x: obj): $ R y $ > $ Q x $ > $ P (k2 y x) x $;
    \\axiom r3K (y x: obj): $ R y $ > $ Q x $ > $ P (K y x) x $;
    \\theorem t (a b c: obj): $ P (k2 a b) c $;
    \\theorem t3 (a b c: obj): $ R a $ > $ Q c $ > $ P (k2 a b) c $;
    \\theorem t3K (a b c: obj): $ R a $ > $ Q c $ > $ P (K a b) c $;
;

// End to end: a rule that repeats `x` proves `P (_ a b) c` with `x := c`
// when the head drops its second argument, so the conclusion prunes must not
// force `x := b` from the goal.
// - `k2` is a `@rewrite` head: normalization reduces both `k2` sides to `a`,
//   so the hypothesis-free `r_k2` and `r3` (whose `x` comes from `Q c`) both
//   prove `P (k2 a b) c`.
// - `K` is an erasing def: `K a b ≡ K a c` once `K` unfolds, so
//   `r3K [#1, #2]` proves `P (K a b) c` (the checker accepts it).
test "exact? meets a rule whose conclusion is a definition of the goal's head" {
    // `refl_P`'s conclusion `dp P` unfolds to `P -> P`, the goal: a goal
    // headed by `->` meets the rules listed under `dp` too.
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term P: wff;
        \\term imp (a b: wff): wff;
        \\infixr imp: $->$ prec 25;
        \\def dp (a: wff): wff = $ a -> a $;
        \\axiom refl_P: $ dp P $;
        \\theorem t: $ P -> P $;
    ;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var found = try suggestionsAtNeedle(&arena, mm0_src,
        \\t
        \\----
        \\l1: $ P -> P $ by exact?
    , "exact?", .{});
    defer found.deinit();
    try expectOffered(found.items, &.{"refl_P"});
}

test "search keeps a rule whose repeated binder sits under an erasing head" {
    const cases = [_]struct { proof: []const u8, offered: []const []const u8 }{
        .{
            .proof =
            \\t3
            \\----
            \\l1: $ P (k2 a b) c $ by exact?
            ,
            .offered = &.{ "r_k2", "r3 [#1, #2]" },
        },
        .{
            .proof =
            \\t3K
            \\-----
            \\l1: $ P (K a b) c $ by exact?
            ,
            .offered = &.{"r3K [#1, #2]"},
        },
    };
    for (cases) |case| {
        var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
        defer arena.deinit();
        var found = try suggestionsAtNeedle(
            &arena,
            repin_heads_mm0,
            case.proof,
            "exact?",
            .{},
        );
        defer found.deinit();
        try expectOffered(found.items, case.offered);
    }
}

test "searchPlaceholders enumerates top-level and nested placeholders" {
    const proof_src =
        \\t
        \\----
        \\l1: $ P $ by exact?
        \\l2: $ Q $ by keep [auto?]
        \\l3: $ R $ by conversion?
    ;
    const placeholders = try source.searchPlaceholders(
        std.testing.allocator,
        proof_src,
    );
    defer std.testing.allocator.free(placeholders);

    try std.testing.expectEqual(@as(usize, 3), placeholders.len);
    try std.testing.expectEqual(
        source.SearchPlaceholder.Kind.exact,
        placeholders[0].kind,
    );
    try std.testing.expectEqual(
        source.SearchPlaceholder.Kind.auto,
        placeholders[1].kind,
    );
    try std.testing.expectEqual(
        source.SearchPlaceholder.Kind.conversion,
        placeholders[2].kind,
    );
    // Each span covers the placeholder application text itself.
    const auto_offset = std.mem.indexOf(u8, proof_src, "auto?").?;
    try std.testing.expectEqual(auto_offset, placeholders[1].span.start);
    try std.testing.expectEqualStrings(
        "exact?",
        proof_src[placeholders[0].span.start..placeholders[0].span.end],
    );
}

fn suggestionStartingWith(
    suggestions: []const types.SourceSuggestion,
    prefix: []const u8,
) ?types.SourceSuggestion {
    for (suggestions) |item| {
        if (std.mem.startsWith(u8, item.replacement, prefix)) return item;
    }
    return null;
}

// #262: the search fixture walks the `.mm0` through the same helper as the
// compile and analyze paths, so it mirrors the parser's coercions into its
// env. `ex_intro`'s @recover crosses sorts (a `tm` hole recovered from a
// `name` instance), which enrolls only when the env knows `name > tm`;
// without the mirror the fixture rejected the axiom's annotations and every
// search in the theory failed before it started. The search's own recover
// pre-filter then has to read a coercion chain around the hole as the
// recovery site it is, or `ex_intro` is never tried.
test "source search sees coercions: a cross-sort @recover rule is searchable" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    const mm0_src = try helpers.readProofCase(
        allocator,
        "pass_ex_elim_infer_two_sort",
        "mm0",
    );

    // The fixture's env carries the theory's three coercions.
    var fixture = try fixtureFor(allocator, mm0_src, "ex_open");
    try std.testing.expectEqual(@as(usize, 3), fixture.theory.env.coercions.items.len);
    try std.testing.expect(fixture.theory.env.getRuleId("ex_intro") != null);

    const proof_src =
        \\ex_open
        \\-------
        \\
        \\l1: $ ∃ x (F x) ⊢ ∃ x (F x) $ by ax
        \\l2: $ F b ⊢ F b $ by ax
        \\l3: $ F b ⊢ ∃ x (F x) $ by exact?
        \\l4: $ ∃ x (F x) ⊢ ∃ x (F x) $ by ex_elim [l1, l3]
    ;
    var suggestions = try suggestionsAtNeedle(
        &arena,
        mm0_src,
        proof_src,
        "exact?",
        .{},
    );
    defer suggestions.deinit();

    const suggestion = suggestionStartingWith(suggestions.items, "ex_intro") orelse {
        return error.MissingSuggestion;
    };
    try std.testing.expectEqualStrings("ex_intro [l2]", suggestion.replacement);
    // What the search offers is exactly what the compile path accepts.
    try helpers.expectConversionCompiles(&arena, mm0_src, proof_src, suggestion);
}

// #262: the fixture recovers the way the analysis does, so a broken
// declaration or local item earlier in the file no longer silences the
// search of every theorem after it. The four failures here take the four
// recovery routes: an `.mm0` parse error, rejected annotations, a duplicate
// rule, and a lemma whose proof does not check.
test "source search survives broken statements before the target" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term P: wff;
        \\term Q: wff;
        \\axiom p: $ P $;
        \\axiom bad_parse: $ R $;
        \\--| @fallback missing
        \\axiom bad_annotation: $ Q $;
        \\axiom dup: $ Q $;
        \\axiom dup: $ Q $;
        \\theorem t: $ P $;
    ;
    const proof_src =
        \\lemma wrong: $ Q $
        \\------------------
        \\l1: $ Q $ by p
        \\
        \\t
        \\----
        \\l1: $ P $ by exact?
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

    try std.testing.expect(suggestions.target_span != null);
    const suggestion = suggestionStartingWith(suggestions.items, "p") orelse {
        return error.MissingSuggestion;
    };
    try std.testing.expectEqualStrings("p", suggestion.replacement);
    // The dropped declarations left no rule behind for the search to cite.
    try std.testing.expect(suggestionStartingWith(suggestions.items, "dup") == null);
    try std.testing.expect(suggestionStartingWith(suggestions.items, "wrong") == null);
}

// Whatever they prove, the lemma and the theorem before the target are in
// scope, so the walk leaves both proofs unchecked: neither failure is
// reported.
test "the walk to a block checks no proof before it" {
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term P: wff;
        \\term Q: wff;
        \\axiom p: $ P $;
        \\theorem s: $ Q $;
        \\theorem t: $ Q $;
    ;
    const proof_src =
        \\lemma wrong: $ Q $
        \\------------------
        \\l1: $ Q $ by p
        \\
        \\s
        \\----
        \\l1: $ Q $ by p
        \\
        \\t
        \\----
        \\l1: $ Q $ by exact?
    ;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var sink = DiagnosticSink.init(mm0_src, proof_src);
    var compiler = CompilerContext.init(mm0_src, proof_src, .none, &sink);
    const block = try ProofScript.blockTouching(
        arena.allocator(),
        proof_src,
        std.mem.indexOf(u8, proof_src, "exact?").?,
    );
    const point = try Analyze.analyzeToBlock(&compiler, arena.allocator(), block.?);
    try std.testing.expectEqual(@as(usize, 0), sink.primaryDiagnostics().len);
    try std.testing.expect(point.theory.env.getRuleId("wrong") != null);
    try std.testing.expect(point.theory.env.getRuleId("s") != null);
}

// The target itself must be intact: a theorem that names a declaration the
// walk dropped is what the analysis marks invalid without checking.
test "source search declines a target that depends on a dropped declaration" {
    // `bad`'s body depends on a dummy its result type does not declare:
    // the parser accepts it, definition validation rejects it.
    const mm0_src =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\sort obj;
        \\term P (a: obj): wff;
        \\def bad {.x: obj}: obj = $ x $;
        \\axiom p (a: obj): $ P a $;
        \\theorem t: $ P bad $;
    ;
    const proof_src =
        \\t
        \\----
        \\l1: $ P bad $ by exact?
    ;
    const offset = std.mem.indexOf(u8, proof_src, "exact?") orelse {
        return error.MissingNeedle;
    };
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    try std.testing.expectError(
        error.UnavailableDependency,
        source.suggestionsAtSourceOffset(
            arena.allocator(),
            mm0_src,
            proof_src,
            offset,
            .{},
        ),
    );
}

// ---------------------------------------------------------------------------
// Binding trimming through the `BindingOracle` (#374). Each case is an nd_fol
// line whose bare suggestion fails, so trimming needs the oracle, and needs
// the named part of it; `suggestionsAtNeedle` fails any suggestion that comes
// back untrimmed. The cases are built on the goal-switching `not_left`
// (`g , ¬ a ⊢ a > g , ¬ a ⊢ ⊥`, whose conclusion fixes no `a`), which nd_fol
// has since replaced with signed negation rules; the fixture gets it back.
// ---------------------------------------------------------------------------

fn expectNdFolTrim(proof_src: []const u8, expected: []const u8) !void {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    const fixture = try std.Io.Dir.cwd().readFileAlloc(std.testing.io, "tests/search_bench_cases/nd_fol.mm0", allocator, .unlimited);
    const first = "-- Contradictory hypotheses close any goal";
    const last = "$ g , ¬ (∃ x p) ⊢ c $;\n";
    const start = std.mem.indexOf(u8, fixture, first) orelse return error.MissingNegationRules;
    const end = (std.mem.indexOfPos(u8, fixture, start, last) orelse return error.MissingNegationRules) + last.len;
    const mm0_src = try std.mem.concat(allocator, u8, &.{
        fixture[0..start],
        "--| @auto eager 3\ntheorem not_left (g: ctx) (a: wff): $ g , ¬ a ⊢ a $ > $ g , ¬ a ⊢ ⊥ $;\n",
        fixture[end..],
    });
    var suggestions = try suggestionsAtNeedle(&arena, mm0_src, proof_src, "auto?", .{
        .max_results = 3,
        .exact_result_limit = 1,
        .generate = .{ .enabled = true },
    });
    defer suggestions.deinit();
    try expectOffered(suggestions.items, &.{expected});
}

test "trimming supplies an inline sub-proof the binders its hint lacks" {
    try expectNdFolTrim(
        \\vac_all_or
        \\----------
        \\l1: $ s0 ⊢ s0 $ by ax
        \\l2: $ (s0 ∨ s0) ⊢ s0 $ by or_left [l1, l1]
        \\l4: $ ∅ ⊢ (∀ x (s0 ∨ s0)) → s0 $ by auto?
    ,
        "imp_intro [all_left (t := $ u $) [weak (h := $ ∀ x (s0 ∨ s0) $) [l2]]]",
    );
}

test "trimming forces the binders an inline sub-proof proved past" {
    try expectNdFolTrim(
        \\not_ex_to_all_not
        \\-----------------
        \\l6: $ ∅ ⊢ (¬ ∃ x P x) → ∀ y (¬ P y) $ by auto?
    ,
        "imp_intro [all_intro [not_intro [not_left [ex_intro (x := $ x $, p := $ P x $) " ++
            "[ax (g := $ ¬ ∃ x P x $, a := $ P u $) []]]]]]",
    );
}

test "trimming accepts an inferred binder equal to the search's up to ACUI" {
    try expectNdFolTrim(
        \\drinker
        \\-------
        \\l1: $ ¬ ∃ x (P x → ∀ y P y) , P C , ¬ P u , P u , ¬ ∀ y P y ⊢ P u $ by ax
        \\l2: $ ¬ ∃ x (P x → ∀ y P y) , P C , ¬ P u , P u , ¬ ∀ y P y ⊢ ⊥ $ by not_left [l1]
        \\l3: $ ¬ ∃ x (P x → ∀ y P y) , P C , ¬ P u , P u ⊢ ∀ y P y $ by raa [l2]
        \\l4: $ ¬ ∃ x (P x → ∀ y P y) , P C , ¬ P u ⊢ P u → ∀ y P y $ by imp_intro [l3]
        \\l5: $ ¬ ∃ x (P x → ∀ y P y) , P C , ¬ P u ⊢ ∃ x (P x → ∀ y P y) $ by ex_intro [l4]
        \\l6: $ ¬ ∃ x (P x → ∀ y P y) , P C , ¬ P u ⊢ ⊥ $ by not_left [l5]
        \\l7: $ ¬ ∃ x (P x → ∀ y P y) , P C ⊢ P u $ by raa [l6]
        \\l12: $ ∅ ⊢ ∃ x (P x → ∀ y P y) $ by auto?
    ,
        "raa [not_left [ex_intro [imp_intro [all_intro (x := $ y $, p := $ P y $) [l7]]]]]",
    );
}

test "trimming checks again with the kept bindings stated" {
    try expectNdFolTrim(
        \\drinker
        \\-------
        \\l1: $ ¬ ∃ x (P x → ∀ y P y) , P C , ¬ P u , P u , ¬ ∀ y P y ⊢ P u $ by ax
        \\l2: $ ¬ ∃ x (P x → ∀ y P y) , P C , ¬ P u , P u , ¬ ∀ y P y ⊢ ⊥ $ by not_left [l1]
        \\l3: $ ¬ ∃ x (P x → ∀ y P y) , P C , ¬ P u , P u ⊢ ∀ y P y $ by raa [l2]
        \\l4: $ ¬ ∃ x (P x → ∀ y P y) , P C , ¬ P u ⊢ P u → ∀ y P y $ by imp_intro [l3]
        \\l8: $ ¬ ∃ x (P x → ∀ y P y) , P C ⊢ ∀ y P y $ by auto?
    ,
        "all_intro [raa [not_left (g := $ P C , ¬ P u $) " ++
            "[ex_intro (x := $ x $, p := $ P x → ∀ y P y $) [l4]]]]",
    );
}
