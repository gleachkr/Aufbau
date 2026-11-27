const std = @import("std");
const Index = @import("index.zig");

const support = @import("./test_support.zig");
const buildSnapshot = support.buildSnapshot;
const completionNamed = support.completionNamed;

fn expectSortPrefix(
    item: Index.CompletionItem,
    prefix: []const u8,
) !void {
    try std.testing.expect(std.mem.startsWith(u8, item.sort_text, prefix));
}

test "completion uses parsed prefixes before malformed suffixes" {
    const mm0_text =
        \\provable sort wff;
        \\term top: wff;
        \\axiom top_i: $ top $;
        \\theorem main: $ to $;
        \\not a valid statement
    ;
    const proof_text =
        \\main
        \\----
        \\l1: $ top $ by top_i []
        \\l2: $ top $ by ke
        \\
        \\bad_block
    ;
    var snapshot = try buildSnapshot(mm0_text, proof_text);
    defer snapshot.deinit();

    const math_offset = std.mem.indexOf(u8, mm0_text, "to $") orelse {
        return error.MissingMalformedMathContext;
    };
    const math_items = try snapshot.completionsAt(
        std.testing.allocator,
        .mm0,
        math_offset + "to".len,
        .{},
    );
    defer std.testing.allocator.free(math_items);
    try std.testing.expect(completionNamed(math_items, "top") != null);

    const rule_offset = std.mem.indexOf(u8, proof_text, "ke") orelse {
        return error.MissingMalformedRuleContext;
    };
    const rule_items = try snapshot.completionsAt(
        std.testing.allocator,
        .proof,
        rule_offset + "ke".len,
        .{},
    );
    defer std.testing.allocator.free(rule_items);
    try std.testing.expect(completionNamed(rule_items, "top_i") != null);
}

test "completion returns top-level mm0 keywords" {
    const text = "the";
    var snapshot = try buildSnapshot(text, null);
    defer snapshot.deinit();

    const completions = try snapshot.completionsAt(
        std.testing.allocator,
        .mm0,
        text.len,
        .{},
    );
    defer std.testing.allocator.free(completions);
    const item = completionNamed(completions, "theorem") orelse {
        return error.MissingTheoremCompletion;
    };
    try std.testing.expectEqual(Index.CompletionKind.keyword, item.kind);
    try std.testing.expectEqual(@as(usize, 0), item.replacement.start);
    try std.testing.expectEqual(@as(usize, 3), item.replacement.end);
}

test "completion completes partially typed mm0 sorts" {
    const text =
        \\provable sort wff;
        \\term other: wf
    ;
    var snapshot = try buildSnapshot(text, null);
    defer snapshot.deinit();

    const completions = try snapshot.completionsAt(
        std.testing.allocator,
        .mm0,
        text.len,
        .{},
    );
    defer std.testing.allocator.free(completions);
    const wff = completionNamed(completions, "wff") orelse {
        return error.MissingPrefixedSortCompletion;
    };
    try std.testing.expectEqual(Index.CompletionKind.sort, wff.kind);
    try std.testing.expectEqualStrings(
        "wf",
        text[wff.replacement.start..wff.replacement.end],
    );
}

test "completion omits ordinary mm0 comments" {
    const text =
        \\provable sort wff;
        \\-- theorem:
        \\term top: wff;
    ;
    var snapshot = try buildSnapshot(text, null);
    defer snapshot.deinit();

    const keyword_offset = std.mem.indexOf(u8, text, "theorem") orelse {
        return error.MissingCommentKeywordContext;
    };
    const keyword_items = try snapshot.completionsAt(
        std.testing.allocator,
        .mm0,
        keyword_offset + "theorem".len,
        .{},
    );
    defer std.testing.allocator.free(keyword_items);
    try std.testing.expectEqual(@as(usize, 0), keyword_items.len);

    const sort_offset = std.mem.indexOf(u8, text, "theorem:") orelse {
        return error.MissingCommentSortContext;
    };
    const sort_items = try snapshot.completionsAt(
        std.testing.allocator,
        .mm0,
        sort_offset + "theorem:".len,
        .{},
    );
    defer std.testing.allocator.free(sort_items);
    try std.testing.expectEqual(@as(usize, 0), sort_items.len);
}

test "completion omits proof comments" {
    const mm0_text =
        \\provable sort wff;
        \\term top: wff;
        \\axiom ax: $ top $;
        \\theorem main: $ top $;
    ;
    const proof_text =
        \\-- ma
        \\main
        \\----
        \\l1: $ top $ by ax [] -- ma
    ;
    var snapshot = try buildSnapshot(mm0_text, proof_text);
    defer snapshot.deinit();

    const standalone_offset = std.mem.indexOf(u8, proof_text, "ma") orelse {
        return error.MissingStandaloneProofComment;
    };
    const standalone_items = try snapshot.completionsAt(
        std.testing.allocator,
        .proof,
        standalone_offset + "ma".len,
        .{},
    );
    defer std.testing.allocator.free(standalone_items);
    try std.testing.expectEqual(@as(usize, 0), standalone_items.len);

    const trailing_offset = std.mem.lastIndexOf(u8, proof_text, "ma") orelse {
        return error.MissingTrailingProofComment;
    };
    const trailing_items = try snapshot.completionsAt(
        std.testing.allocator,
        .proof,
        trailing_offset + "ma".len,
        .{},
    );
    defer std.testing.allocator.free(trailing_items);
    try std.testing.expectEqual(@as(usize, 0), trailing_items.len);
}

test "completion returns sorts and math symbols in mm0 contexts" {
    const text =
        \\provable sort wff;
        \\term top: wff;
        \\theorem main (p: wff): $ p  $;
        \\term other:
    ;
    var snapshot = try buildSnapshot(text, null);
    defer snapshot.deinit();

    const sort_offset = std.mem.indexOf(u8, text, "term other:") orelse {
        return error.MissingSortContext;
    };
    const sort_items = try snapshot.completionsAt(
        std.testing.allocator,
        .mm0,
        sort_offset + "term other:".len,
        .{},
    );
    defer std.testing.allocator.free(sort_items);
    try std.testing.expect(completionNamed(sort_items, "wff") != null);

    const math_offset = std.mem.indexOf(u8, text, "  $") orelse {
        return error.MissingMathContext;
    };
    const math_items = try snapshot.completionsAt(
        std.testing.allocator,
        .mm0,
        math_offset,
        .{},
    );
    defer std.testing.allocator.free(math_items);
    const top = completionNamed(math_items, "top") orelse {
        return error.MissingTopCompletion;
    };
    const p = completionNamed(math_items, "p") orelse {
        return error.MissingBinderCompletion;
    };
    try expectSortPrefix(p, "00");
    try expectSortPrefix(top, "08");
}

test "completion returns notation tokens and aliases in mm0 math" {
    const text =
        \\delimiter $ ( [ $ $ ) ] $;
        \\provable sort wff;
        \\term forall (p: wff): wff;
        \\term imp (p q: wff): wff;
        \\term box (p: wff): wff;
        \\theorem main (p q: wff): $ forall p $;
        \\prefix forall: $∀$ prec 40;
        \\infixr imp: $->$ prec 25;
        \\notation box (p: wff): wff = ($[$:20) p ($]$:20);
    ;
    var snapshot = try buildSnapshot(text, null);
    defer snapshot.deinit();

    const alias_offset = std.mem.indexOf(u8, text, "$ forall p") orelse {
        return error.MissingAliasContext;
    };
    const alias_items = try snapshot.completionsAt(
        std.testing.allocator,
        .mm0,
        alias_offset + "$ forall".len,
        .{},
    );
    defer std.testing.allocator.free(alias_items);
    const forall = completionNamed(alias_items, "∀") orelse {
        return error.MissingForallNotationCompletion;
    };
    try std.testing.expectEqualStrings("∀", forall.replacement_text);
    try std.testing.expectEqualStrings(
        "forall",
        text[forall.replacement.start..forall.replacement.end],
    );
    try std.testing.expect(forall.filter_text != null);
    try std.testing.expectEqualStrings(
        "forall ∀",
        forall.filter_text.?,
    );
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        forall.detail,
        1,
        "forall",
    ));
    try std.testing.expect(forall.documentation_markdown != null);

    const raw_forall = completionNamed(alias_items, "forall") orelse {
        return error.MissingRawTermCompletion;
    };
    try expectSortPrefix(forall, "05");
    try expectSortPrefix(raw_forall, "08");
    try std.testing.expect(std.mem.order(
        u8,
        forall.sort_text,
        raw_forall.sort_text,
    ) == .lt);

    try std.testing.expect(completionNamed(alias_items, "->") != null);
    const open_bracket = completionNamed(alias_items, "[") orelse {
        return error.MissingBracketNotationCompletion;
    };
    try expectSortPrefix(open_bracket, "06");
}

test "snippet escaping protects snippet metacharacters" {
    const escaped = try Index.escapeSnippetText(
        std.testing.allocator,
        "a$b}c\\d",
    );
    defer std.testing.allocator.free(escaped);
    try std.testing.expectEqualSlices(
        u8,
        &[_]u8{ 'a', '\\', '$', 'b', '\\', '}', 'c', '\\', '\\', 'd' },
        escaped,
    );
}

test "completion returns prefix notation snippets when supported" {
    const text =
        \\provable sort wff;
        \\term forall (p: wff): wff;
        \\theorem main (p: wff): $ fo $;
        \\prefix forall: $∀$ prec 40;
    ;
    var snapshot = try buildSnapshot(text, null);
    defer snapshot.deinit();

    const offset = std.mem.indexOf(u8, text, "fo $") orelse {
        return error.MissingSnippetContext;
    };
    const items = try snapshot.completionsAt(
        std.testing.allocator,
        .mm0,
        offset + "fo".len,
        .{ .snippet_support = true },
    );
    defer std.testing.allocator.free(items);
    const snippet = completionNamed(items, "∀ …") orelse {
        return error.MissingPrefixSnippetCompletion;
    };
    try std.testing.expectEqual(Index.CompletionKind.snippet, snippet.kind);
    try std.testing.expectEqualStrings("∀", snippet.replacement_text);
    try std.testing.expectEqualStrings(
        "∀ ${1:p}$0",
        snippet.snippet_replacement_text orelse "",
    );
    try expectSortPrefix(snippet, "07");
    try std.testing.expect(snippet.filter_text != null);
    try std.testing.expectEqualStrings(
        "forall ∀",
        snippet.filter_text.?,
    );
}

test "completion omits notation snippets without client support" {
    const text =
        \\provable sort wff;
        \\term forall (p: wff): wff;
        \\theorem main (p: wff): $ fo $;
        \\prefix forall: $∀$ prec 40;
    ;
    var snapshot = try buildSnapshot(text, null);
    defer snapshot.deinit();

    const offset = std.mem.indexOf(u8, text, "fo $") orelse {
        return error.MissingSnippetContext;
    };
    const items = try snapshot.completionsAt(
        std.testing.allocator,
        .mm0,
        offset + "fo".len,
        .{},
    );
    defer std.testing.allocator.free(items);
    try std.testing.expect(completionNamed(items, "∀ …") == null);
    for (items) |item| {
        try std.testing.expect(item.snippet_replacement_text == null);
    }
}

test "completion returns general notation snippets" {
    const text =
        \\delimiter $ ( [ ] ) $;
        \\provable sort wff;
        \\term box (p: wff): wff;
        \\theorem main (p: wff): $ bo $;
        \\notation box (p: wff): wff = ($[$:20) p ($]$:20);
    ;
    var snapshot = try buildSnapshot(text, null);
    defer snapshot.deinit();

    const offset = std.mem.indexOf(u8, text, "bo $") orelse {
        return error.MissingSnippetContext;
    };
    const items = try snapshot.completionsAt(
        std.testing.allocator,
        .mm0,
        offset + "bo".len,
        .{ .snippet_support = true },
    );
    defer std.testing.allocator.free(items);
    const snippet = completionNamed(items, "[ … ]") orelse {
        return error.MissingGeneralSnippetCompletion;
    };
    try std.testing.expectEqualStrings(
        "[ ${1:p} ]$0",
        snippet.snippet_replacement_text orelse "",
    );
    try std.testing.expect(snippet.filter_text != null);
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        snippet.filter_text.?,
        1,
        "box",
    ));
}

test "snippet placeholders follow binder order" {
    const text =
        \\provable sort wff;
        \\term pair (z a: wff): wff;
        \\theorem main (z a: wff): $ pa $;
        \\notation pair (z a: wff): wff = ($pair$:10) a z;
    ;
    var snapshot = try buildSnapshot(text, null);
    defer snapshot.deinit();

    const offset = std.mem.indexOf(u8, text, "pa $") orelse {
        return error.MissingSnippetContext;
    };
    const items = try snapshot.completionsAt(
        std.testing.allocator,
        .mm0,
        offset + "pa".len,
        .{ .snippet_support = true },
    );
    defer std.testing.allocator.free(items);
    const snippet = completionNamed(items, "pair … …") orelse {
        return error.MissingOrderSnippetCompletion;
    };
    try std.testing.expectEqualStrings(
        "pair ${2:a} ${1:z}$0",
        snippet.snippet_replacement_text orelse "",
    );
}

test "anonymous term arguments get readable snippet placeholders" {
    const text =
        \\provable sort wff;
        \\term anon (_: wff): wff;
        \\theorem main (p: wff): $ an $;
        \\prefix anon: $anon$ prec 40;
    ;
    var snapshot = try buildSnapshot(text, null);
    defer snapshot.deinit();

    const offset = std.mem.indexOf(u8, text, "an $") orelse {
        return error.MissingSnippetContext;
    };
    const items = try snapshot.completionsAt(
        std.testing.allocator,
        .mm0,
        offset + "an".len,
        .{ .snippet_support = true },
    );
    defer std.testing.allocator.free(items);
    const snippet = completionNamed(items, "anon …") orelse {
        return error.MissingAnonymousSnippetCompletion;
    };
    try std.testing.expectEqualStrings(
        "anon ${1:arg1}$0",
        snippet.snippet_replacement_text orelse "",
    );
}

test "completion returns notation tokens in proof math" {
    const mm0_text =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term imp (p q: wff): wff;
        \\infixr imp: $->$ prec 25;
        \\axiom ax (p q: wff): $ p -> q $;
        \\theorem main (p q: wff): $ p -> q $;
    ;
    const proof_text =
        \\main
        \\----
        \\l1: $ p im q $ by ax []
    ;
    var snapshot = try buildSnapshot(mm0_text, proof_text);
    defer snapshot.deinit();

    const offset = std.mem.indexOf(u8, proof_text, "im q") orelse {
        return error.MissingProofAliasContext;
    };
    const items = try snapshot.completionsAt(
        std.testing.allocator,
        .proof,
        offset + "im".len,
        .{},
    );
    defer std.testing.allocator.free(items);
    const imp = completionNamed(items, "->") orelse {
        return error.MissingProofNotationCompletion;
    };
    try std.testing.expectEqualStrings("->", imp.replacement_text);
    try std.testing.expectEqualStrings(
        "im",
        proof_text[imp.replacement.start..imp.replacement.end],
    );
}

test "completion offers proof-side notation in proof math only" {
    // A local notation rides on the local def's declaration, which lives in
    // the proof document, so the availability check keeps both the token
    // and the def out of .mm0 contexts.
    const mm0_text =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term imp (p q: wff): wff;
        \\infixr imp: $->$ prec 25;
        \\axiom ax (p q: wff): $ p -> q $;
        \\theorem main (p q: wff): $ p -> q $;
        \\theorem later (p q: wff): $ p -> q $;
    ;
    const proof_text =
        \\def limp (p q: wff): wff = $ p -> q $
        \\infixr limp: $=>$ prec 25;
        \\
        \\main
        \\----
        \\l1: $ p li q $ by ax []
        \\
        \\later
        \\-----
        \\l1: $ p -> q $ by ax []
    ;
    var snapshot = try buildSnapshot(mm0_text, proof_text);
    defer snapshot.deinit();

    const proof_offset = std.mem.indexOf(u8, proof_text, "li q") orelse {
        return error.MissingProofAliasContext;
    };
    const proof_items = try snapshot.completionsAt(
        std.testing.allocator,
        .proof,
        proof_offset + "li".len,
        .{},
    );
    defer std.testing.allocator.free(proof_items);
    const local = completionNamed(proof_items, "=>") orelse {
        return error.MissingLocalNotationCompletion;
    };
    try std.testing.expectEqualStrings("=>", local.replacement_text);
    try std.testing.expect(completionNamed(proof_items, "limp") != null);

    const mm0_offset = std.mem.indexOf(u8, mm0_text, "theorem later") orelse {
        return error.MissingMm0Context;
    };
    const mm0_math = std.mem.indexOfPos(u8, mm0_text, mm0_offset, "q $") orelse {
        return error.MissingMm0MathContext;
    };
    const mm0_items = try snapshot.completionsAt(
        std.testing.allocator,
        .mm0,
        mm0_math + "q".len,
        .{},
    );
    defer std.testing.allocator.free(mm0_items);
    try std.testing.expect(completionNamed(mm0_items, "->") != null);
    try std.testing.expect(completionNamed(mm0_items, "=>") == null);
    try std.testing.expect(completionNamed(mm0_items, "limp") == null);
}

test "completion offers proof-side notation only past its declaration" {
    // The def is available from its own position; the token only from the
    // notation item's, which may come later.
    const mm0_text =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term imp (p q: wff): wff;
        \\infixr imp: $->$ prec 25;
        \\axiom ax (p q: wff): $ p -> q $;
        \\theorem main (p q: wff): $ p -> q $;
        \\theorem later (p q: wff): $ p -> q $;
    ;
    const proof_text =
        \\def limp (p q: wff): wff = $ p -> q $
        \\
        \\main
        \\----
        \\l1: $ p li q $ by ax []
        \\
        \\infixr limp: $=>$ prec 25;
        \\
        \\later
        \\-----
        \\l1: $ p la q $ by ax []
    ;
    var snapshot = try buildSnapshot(mm0_text, proof_text);
    defer snapshot.deinit();

    const early = std.mem.indexOf(u8, proof_text, "li q") orelse {
        return error.MissingProofAliasContext;
    };
    const early_items = try snapshot.completionsAt(
        std.testing.allocator,
        .proof,
        early + "li".len,
        .{},
    );
    defer std.testing.allocator.free(early_items);
    try std.testing.expect(completionNamed(early_items, "limp") != null);
    try std.testing.expect(completionNamed(early_items, "=>") == null);

    const late = std.mem.indexOf(u8, proof_text, "la q") orelse {
        return error.MissingProofAliasContext;
    };
    const late_items = try snapshot.completionsAt(
        std.testing.allocator,
        .proof,
        late + "la".len,
        .{},
    );
    defer std.testing.allocator.free(late_items);
    try std.testing.expect(completionNamed(late_items, "=>") != null);
}

test "completion returns @vars dummies in proof math" {
    const mm0_text =
        \\--| @vars x y
        \\provable sort obj;
        \\term eq (a b: obj): obj;
        \\axiom eq_refl (a: obj): $ eq a a $;
        \\theorem main (z: obj): $ eq z z $;
    ;
    const proof_text =
        \\main
        \\----
        \\l1: $ eq z x $ by eq_refl []
    ;
    var snapshot = try buildSnapshot(mm0_text, proof_text);
    defer snapshot.deinit();

    const offset = std.mem.indexOf(u8, proof_text, "x $") orelse {
        return error.MissingVarsCompletionContext;
    };
    const items = try snapshot.completionsAt(
        std.testing.allocator,
        .proof,
        offset + "x".len,
        .{},
    );
    defer std.testing.allocator.free(items);

    const x = completionNamed(items, "x") orelse {
        return error.MissingVarsCompletion;
    };
    const z = completionNamed(items, "z") orelse {
        return error.MissingProofBinderCompletion;
    };
    try std.testing.expectEqual(Index.CompletionKind.binder, x.kind);
    try std.testing.expectEqual(Index.CompletionKind.binder, z.kind);
    try std.testing.expectEqualStrings(
        "sort variable",
        x.detail,
    );
    try std.testing.expectEqualStrings(
        "x",
        proof_text[x.replacement.start..x.replacement.end],
    );
    try expectSortPrefix(x, "00");
}

test "completion uses math replacement ranges for operator prefixes" {
    const text =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term imp (p q: wff): wff;
        \\infixr imp: $->$ prec 25;
        \\theorem main (p q: wff): $ p - q $;
    ;
    var snapshot = try buildSnapshot(text, null);
    defer snapshot.deinit();

    const offset = (std.mem.indexOf(u8, text, "- q") orelse {
        return error.MissingOperatorContext;
    }) + 1;
    const items = try snapshot.completionsAt(
        std.testing.allocator,
        .mm0,
        offset,
        .{},
    );
    defer std.testing.allocator.free(items);
    const imp = completionNamed(items, "->") orelse {
        return error.MissingOperatorNotationCompletion;
    };
    try std.testing.expectEqualStrings(
        "-",
        text[imp.replacement.start..imp.replacement.end],
    );
}

test "completion returns annotation directives" {
    const text =
        \\--| @re
        \\provable sort wff;
    ;
    var snapshot = try buildSnapshot(text, null);
    defer snapshot.deinit();

    const offset = std.mem.indexOf(u8, text, "@re") orelse unreachable;
    const completions = try snapshot.completionsAt(
        std.testing.allocator,
        .mm0,
        offset + 3,
        .{},
    );
    defer std.testing.allocator.free(completions);
    try std.testing.expect(completionNamed(completions, "@rewrite") != null);
    try std.testing.expect(completionNamed(completions, "@relation") != null);
}

test "completion returns proof rules, references, and binders" {
    const mm0_text =
        \\provable sort wff;
        \\axiom use (p: wff): $ p $;
        \\theorem main (p: wff): $ p $ > $ p $;
        \\axiom later (p: wff): $ p $;
    ;
    const proof_text =
        \\main
        \\----
        \\l1: $ p $ by use (p := $ p $) []
        \\l2: $ p $ by ke []
        \\l3: $ p $ by use [l]
    ;
    var snapshot = try buildSnapshot(mm0_text, proof_text);
    defer snapshot.deinit();

    const rule_offset = std.mem.indexOf(u8, proof_text, "ke []") orelse {
        return error.MissingRuleContext;
    };
    const rule_items = try snapshot.completionsAt(
        std.testing.allocator,
        .proof,
        rule_offset + "ke".len,
        .{},
    );
    defer std.testing.allocator.free(rule_items);
    try std.testing.expect(completionNamed(rule_items, "use") != null);
    try std.testing.expect(completionNamed(rule_items, "later") == null);

    const l2_refs = std.mem.indexOf(u8, proof_text, "ke []") orelse {
        return error.MissingEmptyRefContext;
    };
    var early_ref_arena_state = std.heap.ArenaAllocator.init(
        std.testing.allocator,
    );
    defer early_ref_arena_state.deinit();
    const early_ref_items = try snapshot.completionsAt(
        early_ref_arena_state.allocator(),
        .proof,
        l2_refs + "ke [".len,
        .{},
    );
    try std.testing.expect(completionNamed(early_ref_items, "l1") != null);
    try std.testing.expect(completionNamed(early_ref_items, "l2") == null);
    try std.testing.expect(completionNamed(early_ref_items, "l3") == null);

    const ref_offset = std.mem.lastIndexOf(u8, proof_text, "l]") orelse {
        return error.MissingRefContext;
    };
    var ref_arena_state = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer ref_arena_state.deinit();
    const ref_items = try snapshot.completionsAt(
        ref_arena_state.allocator(),
        .proof,
        ref_offset + 1,
        .{},
    );
    try std.testing.expect(completionNamed(ref_items, "l1") != null);
    try std.testing.expect(completionNamed(ref_items, "l2") != null);
    try std.testing.expect(completionNamed(ref_items, "l3") == null);
    try std.testing.expect(completionNamed(ref_items, "#1") != null);

    const bind_offset = std.mem.indexOf(u8, proof_text, "p :=") orelse {
        return error.MissingBindingContext;
    };
    const bind_items = try snapshot.completionsAt(
        std.testing.allocator,
        .proof,
        bind_offset + 1,
        .{},
    );
    defer std.testing.allocator.free(bind_items);
    try std.testing.expect(completionNamed(bind_items, "p") != null);
}

test "a half-typed proof line does not blank its block" {
    const mm0_text =
        \\provable sort wff;
        \\axiom use (p: wff): $ p $;
        \\theorem main (p: wff): $ p $ > $ p $;
    ;
    // `by a?` is what the file looks like partway through typing `auto?`, and
    // it does not parse. The block around it still has to work.
    const proof_text =
        \\main
        \\----
        \\l1: $ p $ by use []
        \\l2: $ p $ by a?
        \\l3: $ p $ by use []
    ;
    var snapshot = try buildSnapshot(mm0_text, proof_text);
    defer snapshot.deinit();

    const broken_offset = std.mem.indexOf(u8, proof_text, "a?") orelse {
        return error.MissingRuleContext;
    };
    var broken_arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer broken_arena.deinit();
    const broken_items = try snapshot.completionsAt(
        broken_arena.allocator(),
        .proof,
        broken_offset + "a?".len,
        .{},
    );
    if (completionNamed(broken_items, "auto?") == null) {
        return error.MissingSearchTacticCompletion;
    }
    // A token holding a `?` can only become a placeholder, so the theory's
    // rules drop out — no rule name can contain one.
    if (completionNamed(broken_items, "use") != null) {
        return error.UnexpectedRuleCompletion;
    }

    // The broken line's own label survives, so the lines after it can still
    // cite it — the whole point of keeping the partial line.
    const ref_offset = std.mem.lastIndexOf(u8, proof_text, "use [") orelse {
        return error.MissingRefContext;
    };
    var ref_arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer ref_arena.deinit();
    const ref_items = try snapshot.completionsAt(
        ref_arena.allocator(),
        .proof,
        ref_offset + "use [".len,
        .{},
    );
    for ([_][]const u8{ "l1", "l2" }) |label| {
        if (completionNamed(ref_items, label) == null) {
            return error.MissingProofLineCompletion;
        }
    }
}

test "a token holding a question mark completes only to search tactics" {
    const mm0_text =
        \\provable sort wff;
        \\axiom use (p: wff): $ p $;
        \\theorem main (p: wff): $ p $ > $ p $;
    ;
    const proof_text =
        \\main
        \\----
        \\l1: $ p $ by use []
        \\l2: $ p $ by ?
        \\l3: $ p $ by use [auto?]
    ;
    var snapshot = try buildSnapshot(mm0_text, proof_text);
    defer snapshot.deinit();

    // A bare `?` in the rule position, and a placeholder in a reference slot:
    // both are committed, so both offer the three tactics and nothing else.
    // (A *bare* `?` in a reference slot does not parse at all, so that line
    // is incomplete and offers no reference context — a separate gap.)
    for ([_][]const u8{ "by ?", "use [auto?" }) |prefix| {
        const offset = std.mem.indexOf(u8, proof_text, prefix) orelse {
            return error.MissingPlaceholderContext;
        };
        const typed = prefix[std.mem.lastIndexOfScalar(
            u8,
            prefix,
            if (std.mem.indexOfScalar(u8, prefix, '[') != null) '[' else ' ',
        ).? + 1 ..];
        var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
        defer arena.deinit();
        const items = try snapshot.completionsAt(
            arena.allocator(),
            .proof,
            offset + prefix.len,
            .{},
        );
        try std.testing.expectEqual(@as(usize, 3), items.len);
        for ([_][]const u8{
            "auto?",
            "exact?",
            "conversion?",
        }) |label| {
            const item = completionNamed(items, label) orelse {
                return error.MissingSearchTacticCompletion;
            };
            // The replacement swallows the token the reader already typed,
            // trailing `?` included.
            try std.testing.expectEqualStrings(
                typed,
                proof_text[item.replacement.start..item.replacement.end],
            );
        }
    }
}

test "completion offers search tactics in rule and reference positions" {
    const mm0_text =
        \\provable sort wff;
        \\axiom use (p: wff): $ p $;
        \\theorem main (p: wff): $ p $ > $ p $;
    ;
    const proof_text =
        \\main
        \\----
        \\l1: $ p $ by use (p := $ p $) []
        \\l2: $ p $ by au
        \\l3: $ p $ by auto?
        \\l4: $ p $ by use [auto?]
    ;
    var snapshot = try buildSnapshot(mm0_text, proof_text);
    defer snapshot.deinit();

    const stem_offset = std.mem.indexOf(u8, proof_text, "au\n") orelse {
        return error.MissingRuleContext;
    };
    const stem_items = try snapshot.completionsAt(
        std.testing.allocator,
        .proof,
        stem_offset + "au".len,
        .{},
    );
    defer std.testing.allocator.free(stem_items);

    const auto = completionNamed(stem_items, "auto?") orelse {
        return error.MissingSearchTacticCompletion;
    };
    try std.testing.expectEqual(Index.CompletionKind.keyword, auto.kind);
    try std.testing.expect(auto.documentation_markdown != null);
    try std.testing.expectEqualStrings("auto?", auto.replacement_text);
    try std.testing.expectEqualStrings(
        "au",
        proof_text[auto.replacement.start..auto.replacement.end],
    );
    for ([_][]const u8{ "exact?", "conversion?" }) |label| {
        if (completionNamed(stem_items, label) == null) {
            return error.MissingSearchTacticCompletion;
        }
    }

    // Tactics lead the rule list: three fixed entries a reader can learn, ahead
    // of the theory's own rules.
    const use_rule = completionNamed(stem_items, "use") orelse {
        return error.MissingRuleCompletion;
    };
    try std.testing.expect(std.mem.order(
        u8,
        auto.sort_text,
        use_rule.sort_text,
    ) == .lt);

    // Completing over a placeholder takes its trailing `?` with it, so swapping
    // one tactic for another does not leave `auto?exact?`.
    const rule_offset = std.mem.indexOf(u8, proof_text, "auto?") orelse {
        return error.MissingPlaceholderRuleContext;
    };
    var rule_arena_state = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer rule_arena_state.deinit();
    const rule_items = try snapshot.completionsAt(
        rule_arena_state.allocator(),
        .proof,
        rule_offset + "auto?".len,
        .{},
    );
    const exact = completionNamed(rule_items, "exact?") orelse {
        return error.MissingSearchTacticCompletion;
    };
    try std.testing.expectEqualStrings(
        "auto?",
        proof_text[exact.replacement.start..exact.replacement.end],
    );

    // A reference slot takes a placeholder too (`use [auto?]`).
    const ref_offset = std.mem.lastIndexOf(u8, proof_text, "auto?") orelse {
        return error.MissingRefContext;
    };
    var ref_arena_state = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer ref_arena_state.deinit();
    const ref_items = try snapshot.completionsAt(
        ref_arena_state.allocator(),
        .proof,
        ref_offset + "auto?".len,
        .{},
    );
    const ref_exact = completionNamed(ref_items, "exact?") orelse {
        return error.MissingRefTacticCompletion;
    };
    try std.testing.expectEqualStrings(
        "auto?",
        proof_text[ref_exact.replacement.start..ref_exact.replacement.end],
    );
}

test "completion returns proof rules inside nested applications" {
    const mm0_text =
        \\provable sort wff;
        \\term top: wff;
        \\axiom top_i: $ top $;
        \\axiom keep: $ top $ > $ top $;
        \\theorem main: $ top $;
    ;
    const proof_text =
        \\main
        \\----
        \\l1: $ top $ by top_i []
        \\l2: $ top $ by keep [to []]
    ;
    var snapshot = try buildSnapshot(mm0_text, proof_text);
    defer snapshot.deinit();

    const nested_offset = std.mem.indexOf(u8, proof_text, "to []") orelse {
        return error.MissingNestedRuleContext;
    };
    const items = try snapshot.completionsAt(
        std.testing.allocator,
        .proof,
        nested_offset + "to".len,
        .{},
    );
    defer std.testing.allocator.free(items);
    const top_i = completionNamed(items, "top_i") orelse {
        return error.MissingNestedRuleCompletion;
    };
    try std.testing.expectEqual(Index.CompletionKind.axiom, top_i.kind);
    try std.testing.expectEqualStrings(
        "to",
        proof_text[top_i.replacement.start..top_i.replacement.end],
    );
    try std.testing.expect(completionNamed(items, "l1") == null);
}

test "rule completion writes an open goal per premise" {
    const mm0_text =
        \\provable sort wff;
        \\term top: wff;
        \\axiom top_i: $ top $;
        \\axiom both: $ top $ > $ top $ > $ top $;
        \\theorem main: $ top $;
    ;
    const proof_text =
        \\main
        \\----
        \\l1: $ top $ by top_i
        \\l2: $ top $ by bo
        \\l3: $ top $ by bo [l1, l1]
        \\l4: $ top $ by  [l1, l1]
    ;
    var snapshot = try buildSnapshot(mm0_text, proof_text);
    defer snapshot.deinit();
    var arena_state = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();

    const bare = (std.mem.indexOf(u8, proof_text, "bo\n") orelse
        return error.MissingRuleContext) + "bo".len;
    const plain = try snapshot.completionsAt(arena, .proof, bare, .{});
    const both = completionNamed(plain, "both") orelse
        return error.MissingRuleCompletion;
    try std.testing.expectEqualStrings("both [?, ?]", both.replacement_text);
    try std.testing.expect(both.snippet_replacement_text == null);
    const top_i = completionNamed(plain, "top_i") orelse
        return error.MissingRuleCompletion;
    try std.testing.expectEqualStrings("top_i", top_i.replacement_text);

    const snippets = try snapshot.completionsAt(
        arena,
        .proof,
        bare,
        .{ .snippet_support = true },
    );
    const both_snippet = completionNamed(snippets, "both") orelse
        return error.MissingRuleCompletion;
    try std.testing.expectEqualStrings(
        "both [${1:?}, ${2:?}]",
        both_snippet.snippet_replacement_text orelse "",
    );
    const top_i_snippet = completionNamed(snippets, "top_i") orelse
        return error.MissingRuleCompletion;
    try std.testing.expect(top_i_snippet.snippet_replacement_text == null);

    // Over an application that has its references, only the name changes.
    const written = (std.mem.indexOf(u8, proof_text, "bo [") orelse
        return error.MissingRuleContext) + "bo".len;
    const renamed = try snapshot.completionsAt(
        arena,
        .proof,
        written,
        .{ .snippet_support = true },
    );
    const both_renamed = completionNamed(renamed, "both") orelse
        return error.MissingRuleCompletion;
    try std.testing.expectEqualStrings("both", both_renamed.replacement_text);
    try std.testing.expect(both_renamed.snippet_replacement_text == null);

    // No application parses without a name, but the references after the
    // cursor are still there.
    const unnamed = (std.mem.indexOf(u8, proof_text, "by  [") orelse
        return error.MissingRuleContext) + "by ".len;
    const named = try snapshot.completionsAt(
        arena,
        .proof,
        unnamed,
        .{ .snippet_support = true },
    );
    const both_named = completionNamed(named, "both") orelse
        return error.MissingRuleCompletion;
    try std.testing.expectEqualStrings("both", both_named.replacement_text);
    try std.testing.expect(both_named.snippet_replacement_text == null);
}

test "completion returns theorem names at proof headers" {
    const mm0_text =
        \\provable sort wff;
        \\term top: wff;
        \\theorem main: $ top $;
        \\axiom ax: $ top $;
    ;
    const proof_text = "ma";
    var snapshot = try buildSnapshot(mm0_text, proof_text);
    defer snapshot.deinit();

    const completions = try snapshot.completionsAt(
        std.testing.allocator,
        .proof,
        proof_text.len,
        .{},
    );
    defer std.testing.allocator.free(completions);
    try std.testing.expect(completionNamed(completions, "main") != null);
    try std.testing.expect(completionNamed(completions, "ax") == null);
}

test "completion returns binders for unavailable forward rules" {
    const mm0_text =
        \\provable sort wff;
        \\theorem main (p: wff): $ p $;
        \\axiom later (p: wff): $ p $;
    ;
    const proof_text =
        \\main
        \\----
        \\l1: $ p $ by later (p := $ p $) []
    ;
    var snapshot = try buildSnapshot(mm0_text, proof_text);
    defer snapshot.deinit();

    const rule_offset = std.mem.indexOf(u8, proof_text, "later") orelse {
        return error.MissingForwardRuleContext;
    };
    const rule_items = try snapshot.completionsAt(
        std.testing.allocator,
        .proof,
        rule_offset + "later".len,
        .{},
    );
    defer std.testing.allocator.free(rule_items);
    try std.testing.expect(completionNamed(rule_items, "later") == null);

    const bind_offset = std.mem.indexOf(u8, proof_text, "p :=") orelse {
        return error.MissingForwardBindingContext;
    };
    const bind_items = try snapshot.completionsAt(
        std.testing.allocator,
        .proof,
        bind_offset + 1,
        .{},
    );
    defer std.testing.allocator.free(bind_items);
    try std.testing.expect(completionNamed(bind_items, "p") != null);
}

test "completion excludes future local proof defs" {
    const mm0_text =
        \\provable sort wff;
        \\term top: wff;
    ;
    const proof_text =
        \\def earlier: wff = $ loc $
        \\def local_top: wff = $ top $
        \\def later: wff = $ loc $
    ;
    var snapshot = try buildSnapshot(mm0_text, proof_text);
    defer snapshot.deinit();

    const early_offset = std.mem.indexOf(u8, proof_text, "loc") orelse {
        return error.MissingEarlyLocalDefContext;
    };
    const early_items = try snapshot.completionsAt(
        std.testing.allocator,
        .proof,
        early_offset + "loc".len,
        .{},
    );
    defer std.testing.allocator.free(early_items);
    try std.testing.expect(completionNamed(early_items, "local_top") == null);

    const late_offset = std.mem.lastIndexOf(u8, proof_text, "loc") orelse {
        return error.MissingLateLocalDefContext;
    };
    const late_items = try snapshot.completionsAt(
        std.testing.allocator,
        .proof,
        late_offset + "loc".len,
        .{},
    );
    defer std.testing.allocator.free(late_items);
    try std.testing.expect(completionNamed(late_items, "local_top") != null);
}
