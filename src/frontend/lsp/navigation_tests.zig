const std = @import("std");
const Index = @import("index.zig");
const Snapshot = Index.Snapshot;

const support = @import("./test_support.zig");
const buildSnapshot = support.buildSnapshot;
const completionNamed = support.completionNamed;

test "definition lookup resolves declaration and simple global use" {
    const text =
        \\provable sort wff;
        \\term imp (a b: wff): wff;
        \\theorem imp_refl (a: wff): $ imp a a $;
    ;
    var snapshot = try buildSnapshot(text, null);
    defer snapshot.deinit();

    const decl_offset =
        (std.mem.indexOf(u8, text, "imp") orelse unreachable) + 1;
    const decl_def = try snapshot.definitionAt(.mm0, decl_offset) orelse {
        return error.MissingDefinition;
    };
    try std.testing.expectEqual(Index.DocumentId.mm0, decl_def.document);
    try std.testing.expectEqualStrings(
        "imp",
        snapshot.mm0_text[decl_def.start..decl_def.end],
    );

    const use_offset =
        (std.mem.lastIndexOf(u8, text, "imp") orelse unreachable) + 1;
    const use_def = try snapshot.definitionAt(.mm0, use_offset) orelse {
        return error.MissingDefinition;
    };
    try std.testing.expectEqual(decl_def.start, use_def.start);
    try std.testing.expectEqual(decl_def.end, use_def.end);
}

test "hover returns markdown and source token range" {
    const text =
        \\provable sort wff;
        \\term top: wff;
    ;
    var snapshot = try buildSnapshot(text, null);
    defer snapshot.deinit();

    const offset =
        (std.mem.indexOf(u8, text, "top") orelse unreachable) + 1;
    const hover = try snapshot.hoverAt(.mm0, offset) orelse {
        return error.MissingHover;
    };
    try std.testing.expectEqualStrings(
        "top",
        snapshot.mm0_text[hover.range.start..hover.range.end],
    );
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        hover.markdown,
        1,
        "term top",
    ));
}

test "global hover shows definition bodies and assertion formulas" {
    const text =
        \\provable sort wff;
        \\term imp (a b: wff): wff;
        \\infixr imp: $->$ prec 25;
        \\def id (a: wff): wff = $ a -> a $;
        \\axiom mp (a b: wff): $ a -> b $ > $ a $ > $ b $;
    ;
    var snapshot = try buildSnapshot(text, null);
    defer snapshot.deinit();

    const def_offset =
        (std.mem.indexOf(u8, text, "id") orelse unreachable) + 1;
    const def_hover = try snapshot.hoverAt(.mm0, def_offset) orelse {
        return error.MissingDefinitionHover;
    };
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        def_hover.markdown,
        1,
        "$ a -> a $",
    ));
    try std.testing.expect(!std.mem.containsAtLeast(
        u8,
        def_hover.markdown,
        1,
        "Binders:",
    ));

    const ax_offset =
        (std.mem.indexOf(u8, text, "axiom mp") orelse unreachable) +
        "axiom ".len + 1;
    const ax_hover = try snapshot.hoverAt(.mm0, ax_offset) orelse {
        return error.MissingAssertionHover;
    };
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        ax_hover.markdown,
        1,
        "2 hypotheses, conclusion sort `wff`",
    ));
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        ax_hover.markdown,
        1,
        "axiom mp (a b: wff):",
    ));
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        ax_hover.markdown,
        1,
        "$ a -> b $ >",
    ));
}

test "global hover renders dependency masks as bound names" {
    const text =
        \\sort ctx;
        \\sort tm;
        \\sort ty;
        \\provable sort jdg;
        \\term ok: jdg;
        \\axiom dep_rule (g: ctx) {k ih: tm} (C: ty k)
        \\  (s: tm k ih): $ ok $;
    ;
    var snapshot = try buildSnapshot(text, null);
    defer snapshot.deinit();

    const offset =
        (std.mem.indexOf(u8, text, "dep_rule") orelse unreachable) + 1;
    const hover = try snapshot.hoverAt(.mm0, offset) orelse {
        return error.MissingDependencyHover;
    };
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        hover.markdown,
        1,
        "(C: ty k)",
    ));
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        hover.markdown,
        1,
        "(s: tm k ih)",
    ));
}

test "sort references in signatures resolve explicitly" {
    const text =
        \\provable sort wff;
        \\term top: wff;
    ;
    var snapshot = try buildSnapshot(text, null);
    defer snapshot.deinit();

    const offset =
        (std.mem.lastIndexOf(u8, text, "wff") orelse unreachable) + 1;
    const def = try snapshot.definitionAt(.mm0, offset) orelse {
        return error.MissingSortDefinition;
    };
    try std.testing.expectEqual(Index.DocumentId.mm0, def.document);
    try std.testing.expectEqualStrings(
        "wff",
        snapshot.mm0_text[def.start..def.end],
    );

    const hover = try snapshot.hoverAt(.mm0, offset) orelse {
        return error.MissingSortHover;
    };
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        hover.markdown,
        1,
        "Sort `wff`.",
    ));
}

test "comments do not produce global hovers" {
    const text =
        \\provable sort wff;
        \\term top: wff;
        \\-- top should not be a hover target here
    ;
    var snapshot = try buildSnapshot(text, null);
    defer snapshot.deinit();

    const offset =
        (std.mem.lastIndexOf(u8, text, "top") orelse unreachable) + 1;
    try std.testing.expect(try snapshot.hoverAt(.mm0, offset) == null);
    try std.testing.expect(try snapshot.definitionAt(.mm0, offset) == null);
}

test "proof block header resolves to matching theorem" {
    const mm0_text =
        \\provable sort wff;
        \\term top: wff;
        \\axiom top_i: $ top $;
        \\theorem main: $ top $;
    ;
    const proof_text =
        \\main
        \\----
        \\l1: $ top $ by top_i []
    ;
    var snapshot = try buildSnapshot(mm0_text, proof_text);
    defer snapshot.deinit();

    const offset =
        (std.mem.indexOf(u8, proof_text, "main") orelse unreachable) + 1;
    const def = try snapshot.definitionAt(.proof, offset) orelse {
        return error.MissingDefinition;
    };
    try std.testing.expectEqual(Index.DocumentId.mm0, def.document);
    try std.testing.expectEqualStrings(
        "main",
        snapshot.mm0_text[def.start..def.end],
    );
}

test "implementation lookup resolves theorem declarations to proof blocks" {
    const mm0_text =
        \\provable sort wff;
        \\term top: wff;
        \\axiom top_i: $ top $;
        \\theorem main: $ top $;
    ;
    const proof_text =
        \\main
        \\----
        \\l1: $ top $ by top_i []
    ;
    var snapshot = try buildSnapshot(mm0_text, proof_text);
    defer snapshot.deinit();

    const offset =
        (std.mem.indexOf(u8, mm0_text, "main") orelse unreachable) + 1;
    const implementation = snapshot.implementationAt(.mm0, offset) orelse {
        return error.MissingImplementation;
    };
    try std.testing.expectEqual(Index.DocumentId.proof, implementation.document);
    try std.testing.expectEqualStrings(
        "main",
        snapshot.proof_text.?[implementation.start..implementation.end],
    );

    const axiom_offset =
        (std.mem.indexOf(u8, mm0_text, "top_i") orelse unreachable) + 1;
    try std.testing.expect(
        snapshot.implementationAt(.mm0, axiom_offset) == null,
    );
}

test "references lookup returns matching indexed symbol uses" {
    const mm0_text =
        \\provable sort wff;
        \\term top: wff;
        \\axiom top_i: $ top $;
        \\theorem main: $ top $;
    ;
    const proof_text =
        \\main
        \\----
        \\l1: $ top $ by top_i []
        \\l2: $ top $ by top_i []
    ;
    var snapshot = try buildSnapshot(mm0_text, proof_text);
    defer snapshot.deinit();

    const rule_offset =
        (std.mem.lastIndexOf(u8, proof_text, "top_i") orelse unreachable) + 1;
    const rule_refs = try snapshot.referencesAt(
        std.testing.allocator,
        .proof,
        rule_offset,
        true,
    );
    defer std.testing.allocator.free(rule_refs);
    try std.testing.expectEqual(@as(usize, 3), rule_refs.len);
    try std.testing.expectEqual(Index.DocumentId.mm0, rule_refs[0].document);
    try std.testing.expectEqual(Index.DocumentId.proof, rule_refs[1].document);
    try std.testing.expectEqual(Index.DocumentId.proof, rule_refs[2].document);
    for (rule_refs) |range| {
        const text = snapshot.textForDocument(range.document) orelse unreachable;
        try std.testing.expectEqualStrings("top_i", text[range.start..range.end]);
    }

    const rule_uses = try snapshot.referencesAt(
        std.testing.allocator,
        .proof,
        rule_offset,
        false,
    );
    defer std.testing.allocator.free(rule_uses);
    try std.testing.expectEqual(@as(usize, 2), rule_uses.len);
    for (rule_uses) |range| {
        try std.testing.expectEqual(Index.DocumentId.proof, range.document);
    }

    const theorem_offset =
        (std.mem.indexOf(u8, mm0_text, "main") orelse unreachable) + 1;
    const theorem_refs = try snapshot.referencesAt(
        std.testing.allocator,
        .mm0,
        theorem_offset,
        true,
    );
    defer std.testing.allocator.free(theorem_refs);
    try std.testing.expectEqual(@as(usize, 2), theorem_refs.len);
    try std.testing.expectEqual(Index.DocumentId.mm0, theorem_refs[0].document);
    try std.testing.expectEqual(Index.DocumentId.proof, theorem_refs[1].document);

    const theorem_uses = try snapshot.referencesAt(
        std.testing.allocator,
        .mm0,
        theorem_offset,
        false,
    );
    defer std.testing.allocator.free(theorem_uses);
    try std.testing.expectEqual(@as(usize, 1), theorem_uses.len);
    try std.testing.expectEqual(Index.DocumentId.proof, theorem_uses[0].document);
}

test "proof block header ignores non-theorem globals" {
    const mm0_text =
        \\provable sort wff;
        \\term main: wff;
    ;
    const proof_text =
        \\main
        \\----
        \\l1: $ main $ by main []
    ;
    var snapshot = try buildSnapshot(mm0_text, proof_text);
    defer snapshot.deinit();

    const offset =
        (std.mem.indexOf(u8, proof_text, "main") orelse unreachable) + 1;
    try std.testing.expect(try snapshot.definitionAt(.proof, offset) == null);
    try std.testing.expect(try snapshot.hoverAt(.proof, offset) == null);
}

test "proof rule applications ignore non-rule globals" {
    const mm0_text =
        \\provable sort wff;
        \\term top: wff;
        \\theorem main: $ top $;
    ;
    const proof_text =
        \\main
        \\----
        \\l1: $ top $ by top []
    ;
    var snapshot = try buildSnapshot(mm0_text, proof_text);
    defer snapshot.deinit();

    const offset =
        (std.mem.lastIndexOf(u8, proof_text, "top") orelse unreachable) + 1;
    const hover = try snapshot.hoverAt(.proof, offset) orelse {
        return error.MissingUnknownRuleHover;
    };
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        hover.markdown,
        1,
        "unknown rule `top`",
    ));
    try std.testing.expect(try snapshot.definitionAt(.proof, offset) == null);
}

test "forward global proof rules hover but do not define" {
    const mm0_text =
        \\provable sort wff;
        \\term top: wff;
        \\theorem main: $ top $;
        \\axiom later: $ top $;
    ;
    const proof_text =
        \\main
        \\----
        \\l1: $ top $ by later []
    ;
    var snapshot = try buildSnapshot(mm0_text, proof_text);
    defer snapshot.deinit();

    const offset =
        (std.mem.indexOf(u8, proof_text, "later") orelse unreachable) + 1;
    const hover = try snapshot.hoverAt(.proof, offset) orelse {
        return error.MissingForwardRuleHover;
    };
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        hover.markdown,
        1,
        "axiom later",
    ));
    try std.testing.expect(try snapshot.definitionAt(.proof, offset) == null);
}

test "current theorem is not available as a proof rule" {
    const mm0_text =
        \\provable sort wff;
        \\term top: wff;
        \\theorem main: $ top $;
    ;
    const proof_text =
        \\main
        \\----
        \\l1: $ top $ by main []
    ;
    var snapshot = try buildSnapshot(mm0_text, proof_text);
    defer snapshot.deinit();

    const offset =
        (std.mem.lastIndexOf(u8, proof_text, "main") orelse unreachable) + 1;
    const hover = try snapshot.hoverAt(.proof, offset) orelse {
        return error.MissingSelfRuleHover;
    };
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        hover.markdown,
        1,
        "theorem main",
    ));
    try std.testing.expect(try snapshot.definitionAt(.proof, offset) == null);
}

test "proof rule and line references resolve" {
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
        \\l2: $ top $ by keep [l1]
    ;
    var snapshot = try buildSnapshot(mm0_text, proof_text);
    defer snapshot.deinit();

    const rule_offset =
        (std.mem.lastIndexOf(u8, proof_text, "keep") orelse unreachable) + 1;
    const rule_def = try snapshot.definitionAt(.proof, rule_offset) orelse {
        return error.MissingRuleDefinition;
    };
    try std.testing.expectEqual(Index.DocumentId.mm0, rule_def.document);
    try std.testing.expectEqualStrings(
        "keep",
        snapshot.mm0_text[rule_def.start..rule_def.end],
    );

    const ref_offset =
        (std.mem.lastIndexOf(u8, proof_text, "l1") orelse unreachable) + 1;
    const ref_def = try snapshot.definitionAt(.proof, ref_offset) orelse {
        return error.MissingLineDefinition;
    };
    try std.testing.expectEqual(Index.DocumentId.proof, ref_def.document);
    try std.testing.expectEqualStrings(
        "l1",
        snapshot.proof_text.?[ref_def.start..ref_def.end],
    );
}

test "local lemma rule resolves in later proof block" {
    const mm0_text =
        \\provable sort wff;
        \\term top: wff;
        \\axiom top_i: $ top $;
        \\theorem main: $ top $;
    ;
    const proof_text =
        \\lemma helper: $ top $
        \\-------------------
        \\l1: $ top $ by top_i []
        \\
        \\main
        \\----
        \\l1: $ top $ by helper []
    ;
    var snapshot = try buildSnapshot(mm0_text, proof_text);
    defer snapshot.deinit();

    const rule_offset =
        (std.mem.lastIndexOf(u8, proof_text, "helper") orelse unreachable) + 1;
    const def = try snapshot.definitionAt(.proof, rule_offset) orelse {
        return error.MissingDefinition;
    };
    try std.testing.expectEqual(Index.DocumentId.proof, def.document);
    const decl_start = std.mem.indexOf(u8, proof_text, "helper") orelse {
        return error.MissingLemmaHeader;
    };
    try std.testing.expectEqual(decl_start, def.start);
}

test "local proof defs navigate, hover, complete, and outline" {
    const mm0_text =
        \\provable sort wff;
        \\term top: wff;
        \\axiom top_i: $ top $;
        \\theorem main: $ top $;
    ;
    const proof_text =
        \\def local_top: wff = $ top $
        \\
        \\main
        \\----
        \\l1: $ local_top $ by top_i []
    ;
    var snapshot = try buildSnapshot(mm0_text, proof_text);
    defer snapshot.deinit();

    const use_offset = std.mem.lastIndexOf(u8, proof_text, "local_top") orelse {
        return error.MissingLocalDefUse;
    };
    const completions = try snapshot.completionsAt(
        std.testing.allocator,
        .proof,
        use_offset + "local".len,
        .{},
    );
    defer std.testing.allocator.free(completions);
    const item = completionNamed(completions, "local_top") orelse {
        return error.MissingLocalDefCompletion;
    };
    try std.testing.expectEqual(Index.CompletionKind.def, item.kind);

    const def = try snapshot.definitionAt(.proof, use_offset) orelse {
        return error.MissingLocalDefDefinition;
    };
    try std.testing.expectEqual(Index.DocumentId.proof, def.document);
    const decl_offset = std.mem.indexOf(u8, proof_text, "local_top") orelse {
        return error.MissingLocalDefDecl;
    };
    try std.testing.expectEqual(decl_offset, def.start);

    const hover = try snapshot.hoverAt(.proof, use_offset) orelse {
        return error.MissingLocalDefHover;
    };
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        hover.markdown,
        1,
        "Definition `local_top`",
    ));

    const outline = snapshot.outline(.proof);
    try std.testing.expectEqual(@as(usize, 2), outline.len);
    try std.testing.expectEqualStrings("local_top", outline[0].name);
    try std.testing.expectEqual(Index.DeclarationKind.def, outline[0].kind);
}

test "local proof def binders navigate from bodies" {
    const mm0_text =
        \\sort obj;
    ;
    const proof_text =
        \\def choose (.d: obj) (x: obj): obj = $ d $
    ;
    var snapshot = try buildSnapshot(mm0_text, proof_text);
    defer snapshot.deinit();

    const body_offset = std.mem.lastIndexOf(u8, proof_text, "d") orelse {
        return error.MissingLocalDummyUse;
    };
    const def = try snapshot.definitionAt(.proof, body_offset) orelse {
        return error.MissingLocalDummyDefinition;
    };
    const dummy_offset = std.mem.indexOf(u8, proof_text, ".d") orelse {
        return error.MissingLocalDummyDecl;
    };
    try std.testing.expectEqual(dummy_offset + 1, def.start);
    try std.testing.expectEqualStrings(
        "d",
        snapshot.proof_text.?[def.start..def.end],
    );
}

test "public proof def bodies navigate to mm0 declarations" {
    const mm0_text =
        \\sort obj;
        \\def hold (x: obj): obj;
    ;
    const proof_text =
        \\def hold = $ x $
    ;
    var snapshot = try buildSnapshot(mm0_text, proof_text);
    defer snapshot.deinit();

    const name_offset = std.mem.indexOf(u8, proof_text, "hold") orelse {
        return error.MissingPublicDefBodyName;
    };
    const name_def = try snapshot.definitionAt(.proof, name_offset) orelse {
        return error.MissingPublicDefBodyDefinition;
    };
    try std.testing.expectEqual(Index.DocumentId.mm0, name_def.document);
    try std.testing.expectEqualStrings(
        "hold",
        snapshot.mm0_text[name_def.start..name_def.end],
    );

    const body_offset = std.mem.indexOf(u8, proof_text, "x") orelse {
        return error.MissingPublicDefBodyBinder;
    };
    const binder_def = try snapshot.definitionAt(.proof, body_offset) orelse {
        return error.MissingPublicDefBodyBinderDefinition;
    };
    try std.testing.expectEqual(Index.DocumentId.mm0, binder_def.document);
    try std.testing.expectEqualStrings(
        "x",
        snapshot.mm0_text[binder_def.start..binder_def.end],
    );
}

test "hypothesis refs hover and jump to exact theorem hypothesis" {
    const mm0_text =
        \\provable sort wff;
        \\term first: wff;
        \\term second: wff;
        \\term top: wff;
        \\axiom keep: $ second $ > $ top $;
        \\theorem main: $ first $ > $ second $ > $ top $;
    ;
    const proof_text =
        \\main
        \\----
        \\l1: $ top $ by keep [#2]
    ;
    var snapshot = try buildSnapshot(mm0_text, proof_text);
    defer snapshot.deinit();

    const offset =
        (std.mem.indexOf(u8, proof_text, "#2") orelse unreachable) + 1;
    const hover = try snapshot.hoverAt(.proof, offset) orelse {
        return error.MissingHover;
    };
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        hover.markdown,
        1,
        "$ second $",
    ));
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        hover.markdown,
        1,
        "hypothesis #2",
    ));
    const def = try snapshot.definitionAt(.proof, offset) orelse {
        return error.MissingDefinition;
    };
    const second_hyp = std.mem.lastIndexOf(u8, mm0_text, "$ second $") orelse {
        return error.MissingSecondHypothesis;
    };
    try std.testing.expectEqual(Index.DocumentId.mm0, def.document);
    try std.testing.expectEqual(second_hyp + 1, def.start);
    try std.testing.expectEqualStrings(
        " second ",
        snapshot.mm0_text[def.start..def.end],
    );
}

test "named hypothesis refs validate and jump to the theorem binder" {
    const mm0_text =
        \\provable sort wff;
        \\term first: wff;
        \\term second: wff;
        \\term top: wff;
        \\axiom keep: $ second $ > $ top $;
        \\theorem main (h1: $ first $) (h2: $ second $): $ top $;
    ;
    const proof_text =
        \\main
        \\----
        \\l1: $ top $ by keep [#h2]
        \\l2: $ top $ by keep [#nope]
        \\l3: $ top $ by keep []
    ;
    var snapshot = try buildSnapshot(mm0_text, proof_text);
    defer snapshot.deinit();

    const named_offset =
        (std.mem.indexOf(u8, proof_text, "#h2") orelse unreachable) + 1;
    const hover = try snapshot.hoverAt(.proof, named_offset) orelse {
        return error.MissingHover;
    };
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        hover.markdown,
        1,
        "$ second $",
    ));
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        hover.markdown,
        1,
        "hypothesis `h2` (#2)",
    ));
    const def = try snapshot.definitionAt(.proof, named_offset) orelse {
        return error.MissingDefinition;
    };
    try std.testing.expectEqual(Index.DocumentId.mm0, def.document);
    try std.testing.expectEqualStrings(
        "h2",
        snapshot.mm0_text[def.start..def.end],
    );

    const unknown_offset =
        (std.mem.indexOf(u8, proof_text, "#nope") orelse unreachable) + 1;
    const unknown_hover = try snapshot.hoverAt(.proof, unknown_offset) orelse {
        return error.MissingUnknownHover;
    };
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        unknown_hover.markdown,
        1,
        "unknown hypothesis #nope",
    ));
    try std.testing.expect(
        try snapshot.definitionAt(.proof, unknown_offset) == null,
    );

    const slot_offset =
        (std.mem.indexOf(u8, proof_text, "keep []") orelse unreachable) +
        "keep [".len;
    var ref_arena_state = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer ref_arena_state.deinit();
    const ref_items = try snapshot.completionsAt(
        ref_arena_state.allocator(),
        .proof,
        slot_offset,
        .{},
    );
    try std.testing.expect(completionNamed(ref_items, "#1") != null);
    try std.testing.expect(completionNamed(ref_items, "#h1") != null);
    const named_item = completionNamed(ref_items, "#h2") orelse {
        return error.MissingNamedHypCompletion;
    };
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        named_item.documentation_markdown orelse "",
        1,
        "$ second $",
    ));
}

test "multi-name hypothesis groups pair with their own formula" {
    // `(h1 h2: $ first $)` declares one formula for two hypotheses, so the
    // hypothesis list is longer than the statement's math strings. Pairing
    // one hypothesis per formula would slide h2 onto `$ second $` and h3
    // onto the conclusion.
    const mm0_text =
        \\provable sort wff;
        \\term first: wff;
        \\term second: wff;
        \\term top: wff;
        \\axiom keep: $ second $ > $ top $;
        \\theorem grouped (h1 h2: $ first $) (h3: $ second $): $ top $;
    ;
    const proof_text =
        \\grouped
        \\----
        \\l1: $ top $ by keep [#h2]
        \\l2: $ top $ by keep [#h3]
        \\l3: $ top $ by keep [#2]
    ;
    var snapshot = try buildSnapshot(mm0_text, proof_text);
    defer snapshot.deinit();

    // h2 shares its group's formula, and jumps to its own name token.
    const h2_offset =
        (std.mem.indexOf(u8, proof_text, "#h2") orelse unreachable) + 1;
    const h2_hover = try snapshot.hoverAt(.proof, h2_offset) orelse {
        return error.MissingGroupedHover;
    };
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        h2_hover.markdown,
        1,
        "$ first $",
    ));
    const h2_def = try snapshot.definitionAt(.proof, h2_offset) orelse {
        return error.MissingGroupedDefinition;
    };
    try std.testing.expectEqualStrings(
        "h2",
        snapshot.mm0_text[h2_def.start..h2_def.end],
    );

    // The hypothesis after the group keeps its own formula.
    const h3_offset =
        (std.mem.indexOf(u8, proof_text, "#h3") orelse unreachable) + 1;
    const h3_hover = try snapshot.hoverAt(.proof, h3_offset) orelse {
        return error.MissingAfterGroupHover;
    };
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        h3_hover.markdown,
        1,
        "$ second $",
    ));

    // Positional refs pair the same way.
    const second_offset =
        (std.mem.indexOf(u8, proof_text, "#2") orelse unreachable) + 1;
    const second_hover = try snapshot.hoverAt(.proof, second_offset) orelse {
        return error.MissingPositionalHover;
    };
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        second_hover.markdown,
        1,
        "$ first $",
    ));
}

test "duplicate hypothesis names make a named ref ambiguous" {
    const mm0_text =
        \\provable sort wff;
        \\term first: wff;
        \\term top: wff;
        \\axiom keep: $ first $ > $ top $;
        \\theorem dup (h: $ first $) (h: $ first $): $ top $;
    ;
    const proof_text =
        \\dup
        \\----
        \\l1: $ top $ by keep [#h]
        \\l2: $ top $ by keep []
    ;
    var snapshot = try buildSnapshot(mm0_text, proof_text);
    defer snapshot.deinit();

    const ref_offset =
        (std.mem.indexOf(u8, proof_text, "#h]") orelse unreachable) + 1;
    const hover = try snapshot.hoverAt(.proof, ref_offset) orelse {
        return error.MissingHover;
    };
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        hover.markdown,
        1,
        "matches more than one hypothesis",
    ));
    try std.testing.expect(try snapshot.definitionAt(.proof, ref_offset) == null);

    const slot_offset =
        (std.mem.indexOf(u8, proof_text, "keep []") orelse unreachable) +
        "keep [".len;
    var ref_arena_state = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer ref_arena_state.deinit();
    const ref_items = try snapshot.completionsAt(
        ref_arena_state.allocator(),
        .proof,
        slot_offset,
        .{},
    );
    try std.testing.expect(completionNamed(ref_items, "#1") != null);
    try std.testing.expect(completionNamed(ref_items, "#2") != null);
    try std.testing.expect(completionNamed(ref_items, "#h") == null);
}

test "named hypothesis refs resolve in lemma headers" {
    const mm0_text =
        \\provable sort wff;
        \\term first: wff;
        \\term top: wff;
        \\axiom keep: $ first $ > $ top $;
        \\theorem main: $ top $;
    ;
    const proof_text =
        \\lemma lem (hf: $ first $): $ top $
        \\----
        \\l1: $ top $ by keep [#hf]
        \\
        \\main
        \\----
        \\l1: $ top $ by keep []
    ;
    var snapshot = try buildSnapshot(mm0_text, proof_text);
    defer snapshot.deinit();

    const ref_offset =
        (std.mem.indexOf(u8, proof_text, "#hf") orelse unreachable) + 1;
    const hover = try snapshot.hoverAt(.proof, ref_offset) orelse {
        return error.MissingHover;
    };
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        hover.markdown,
        1,
        "$ first $",
    ));
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        hover.markdown,
        1,
        "hypothesis `hf` (#1)",
    ));
    const def = try snapshot.definitionAt(.proof, ref_offset) orelse {
        return error.MissingDefinition;
    };
    try std.testing.expectEqual(Index.DocumentId.proof, def.document);
    const header_binder = std.mem.indexOf(u8, proof_text, "hf") orelse {
        return error.MissingHeaderBinder;
    };
    try std.testing.expectEqual(header_binder, def.start);
    try std.testing.expectEqual(header_binder + "hf".len, def.end);
}

test "unresolved proof symbols still hover" {
    const mm0_text =
        \\provable sort wff;
        \\term top: wff;
        \\theorem main: $ top $;
    ;
    const proof_text =
        \\main
        \\----
        \\l1: $ top $ by missing [future, #1]
    ;
    var snapshot = try buildSnapshot(mm0_text, proof_text);
    defer snapshot.deinit();

    const rule_offset =
        (std.mem.indexOf(u8, proof_text, "missing") orelse unreachable) + 1;
    const rule_hover = try snapshot.hoverAt(.proof, rule_offset) orelse {
        return error.MissingRuleHover;
    };
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        rule_hover.markdown,
        1,
        "unknown rule `missing`",
    ));
    try std.testing.expect(try snapshot.definitionAt(.proof, rule_offset) == null);

    const line_offset =
        (std.mem.indexOf(u8, proof_text, "future") orelse unreachable) + 1;
    const line_hover = try snapshot.hoverAt(.proof, line_offset) orelse {
        return error.MissingLineHover;
    };
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        line_hover.markdown,
        1,
        "unknown line `future`",
    ));

    const hyp_offset =
        (std.mem.indexOf(u8, proof_text, "#1") orelse unreachable) + 1;
    const hyp_hover = try snapshot.hoverAt(.proof, hyp_offset) orelse {
        return error.MissingHypHover;
    };
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        hyp_hover.markdown,
        1,
        "unknown hypothesis #1",
    ));
    try std.testing.expect(try snapshot.definitionAt(.proof, hyp_offset) == null);
}

test "explicit proof bindings resolve to rule binders" {
    const mm0_text =
        \\sort obj;
        \\provable sort wff;
        \\axiom use {x: obj} (p: wff x): $ p $;
        \\theorem main {x: obj} (p: wff x): $ p $;
    ;
    const proof_text =
        \\main
        \\----
        \\l1: $ p $ by use (x := $ x $, p := $ p $)
    ;
    var snapshot = try buildSnapshot(mm0_text, proof_text);
    defer snapshot.deinit();

    const binding_offset =
        (std.mem.indexOf(u8, proof_text, "x :=") orelse unreachable);
    const hover = try snapshot.hoverAt(.proof, binding_offset) orelse {
        return error.MissingBindingHover;
    };
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        hover.markdown,
        1,
        "Expected sort: `obj`. Bound variable.",
    ));

    const def = try snapshot.definitionAt(.proof, binding_offset) orelse {
        return error.MissingBindingDefinition;
    };
    try std.testing.expectEqual(Index.DocumentId.mm0, def.document);
    try std.testing.expectEqualStrings(
        "x",
        snapshot.mm0_text[def.start..def.end],
    );

    const free_offset =
        (std.mem.indexOf(u8, proof_text, "p :=") orelse unreachable);
    const free_hover = try snapshot.hoverAt(.proof, free_offset) orelse {
        return error.MissingFreeBindingHover;
    };
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        free_hover.markdown,
        1,
        "Expected sort: `wff`. Free variable.",
    ));
}

test "math notation tokens resolve to defining terms" {
    const mm0_text =
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\term imp (p q: wff): wff;
        \\infixr imp: $->$ prec 25;
        \\theorem main (p q: wff): $ p -> q $;
    ;
    var snapshot = try buildSnapshot(mm0_text, null);
    defer snapshot.deinit();

    const offset =
        (std.mem.lastIndexOf(u8, mm0_text, "->") orelse unreachable) + 1;
    const def = try snapshot.definitionAt(.mm0, offset) orelse {
        return error.MissingNotationDefinition;
    };
    try std.testing.expectEqual(Index.DocumentId.mm0, def.document);
    try std.testing.expectEqualStrings(
        "imp",
        snapshot.mm0_text[def.start..def.end],
    );

    const hover = try snapshot.hoverAt(.mm0, offset) orelse {
        return error.MissingNotationHover;
    };
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        hover.markdown,
        1,
        "term imp",
    ));
}

test "general notation tokens resolve to defining terms" {
    const mm0_text =
        \\provable sort wff;
        \\term top: wff;
        \\notation top: wff = ($⊤$:max);
        \\theorem main: $ ⊤ $;
    ;
    var snapshot = try buildSnapshot(mm0_text, null);
    defer snapshot.deinit();

    const offset =
        (std.mem.lastIndexOf(u8, mm0_text, "⊤") orelse unreachable) + 1;
    const def = try snapshot.definitionAt(.mm0, offset) orelse {
        return error.MissingGeneralNotationDefinition;
    };
    try std.testing.expectEqualStrings(
        "top",
        snapshot.mm0_text[def.start..def.end],
    );
}

test "proof math term definitions use mm0 declaration scope" {
    const mm0_text =
        \\-- padding keeps the mm0 declaration after the proof token offset
        \\provable sort wff;
        \\term top: wff;
        \\axiom top_i: $ top $;
        \\theorem main: $ top $;
    ;
    const proof_text =
        \\main
        \\----
        \\l1: $ top $ by top_i []
    ;
    var snapshot = try buildSnapshot(mm0_text, proof_text);
    defer snapshot.deinit();

    const proof_top = std.mem.indexOf(u8, proof_text, "$ top $") orelse {
        return error.MissingProofMath;
    };
    const offset = proof_top + 2;
    const def = try snapshot.definitionAt(.proof, offset) orelse {
        return error.MissingProofTermDefinition;
    };
    try std.testing.expectEqual(Index.DocumentId.mm0, def.document);
    try std.testing.expectEqualStrings(
        "top",
        snapshot.mm0_text[def.start..def.end],
    );
}

test "proof math notation definitions use mm0 declaration scope" {
    const mm0_text =
        \\-- padding keeps the mm0 declaration after the proof token offset
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
        \\l1: $ p -> q $ by ax []
    ;
    var snapshot = try buildSnapshot(mm0_text, proof_text);
    defer snapshot.deinit();

    const offset = std.mem.indexOf(u8, proof_text, "->") orelse {
        return error.MissingProofNotation;
    };
    const def = try snapshot.definitionAt(.proof, offset) orelse {
        return error.MissingProofNotationDefinition;
    };
    try std.testing.expectEqual(Index.DocumentId.mm0, def.document);
    try std.testing.expectEqualStrings(
        "imp",
        snapshot.mm0_text[def.start..def.end],
    );
}

test "forward proof math globals hover without definition" {
    const mm0_text =
        \\provable sort wff;
        \\term top: wff;
        \\axiom top_i: $ top $;
        \\theorem main: $ top $;
        \\term later: wff;
    ;
    const proof_text =
        \\main
        \\----
        \\l1: $ later $ by top_i []
    ;
    var snapshot = try buildSnapshot(mm0_text, proof_text);
    defer snapshot.deinit();

    const proof_later = std.mem.indexOf(u8, proof_text, "later") orelse {
        return error.MissingForwardProofMath;
    };
    const hover = try snapshot.hoverAt(.proof, proof_later) orelse {
        return error.MissingForwardProofMathHover;
    };
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        hover.markdown,
        1,
        "term later",
    ));
    try std.testing.expect(try snapshot.definitionAt(.proof, proof_later) == null);
}

test "proof math binder references resolve to theorem binders" {
    const mm0_text =
        \\provable sort wff;
        \\axiom use (p: wff): $ p $;
        \\theorem main (p: wff): $ p $;
    ;
    const proof_text =
        \\main
        \\----
        \\l1: $ p $ by use (p := $ p $) []
    ;
    var snapshot = try buildSnapshot(mm0_text, proof_text);
    defer snapshot.deinit();

    const line_assertion = std.mem.indexOf(u8, proof_text, "$ p $") orelse {
        return error.MissingProofMath;
    };
    const offset = line_assertion + 2;
    const def = try snapshot.definitionAt(.proof, offset) orelse {
        return error.MissingBinderDefinition;
    };
    try std.testing.expectEqual(Index.DocumentId.mm0, def.document);
    try std.testing.expectEqualStrings(
        "p",
        snapshot.mm0_text[def.start..def.end],
    );

    const hover = try snapshot.hoverAt(.proof, offset) orelse {
        return error.MissingBinderHover;
    };
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        hover.markdown,
        1,
        "Expected sort: `wff`. Free variable.",
    ));
}

test "proof @vars dummies hover and jump to pool token" {
    const mm0_text =
        \\provable sort wff;
        \\--| @vars x y
        \\sort obj;
        \\term eq (a b: obj): wff;
        \\axiom eq_refl (a: obj): $ eq a a $;
        \\theorem main (t: obj): $ eq t t $;
    ;
    const proof_text =
        \\main
        \\----
        \\l1: $ eq x x $ by eq_refl []
    ;
    var snapshot = try buildSnapshot(mm0_text, proof_text);
    defer snapshot.deinit();

    const proof_token =
        std.mem.indexOf(u8, proof_text, "x x") orelse unreachable;
    const hover = try snapshot.hoverAt(.proof, proof_token) orelse {
        return error.MissingVarsHover;
    };
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        hover.markdown,
        1,
        "Theorem-local dummy `x`",
    ));
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        hover.markdown,
        1,
        "Sort: `obj`",
    ));

    const def = try snapshot.definitionAt(.proof, proof_token) orelse {
        return error.MissingVarsDefinition;
    };
    try std.testing.expectEqual(Index.DocumentId.mm0, def.document);
    const vars_token = std.mem.indexOf(u8, mm0_text, "x y") orelse {
        return error.MissingVarsAnnotation;
    };
    try std.testing.expectEqual(vars_token, def.start);
    try std.testing.expectEqualStrings(
        "x",
        snapshot.mm0_text[def.start..def.end],
    );

    const decl_hover = try snapshot.hoverAt(.mm0, vars_token) orelse {
        return error.MissingVarsDeclHover;
    };
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        decl_hover.markdown,
        1,
        "Available in proof-body math.",
    ));
}

test "global hover shows the declaration's annotations in full" {
    const mm0_text =
        \\delimiter $ ( ) $;
        \\--| @vars u v
        \\provable sort wff;
        \\sort ctx;
        \\term top: wff;
        \\term imp (a b: wff): wff;
        \\infixr imp: $->$ prec 25;
        \\term seq (g: ctx) (a: wff): wff;
        \\infixl seq: $|-$ prec 10;
        \\--| @rewrite
        \\axiom top_i: $ top $;
        \\--| @view (g: ctx) (p q: wff): $ g |- p $ > $ g |- q $
        \\--| @abstract p q $ top $ $ top -> top $
        \\--| @auto forward
        \\axiom weaken (g: ctx) (p: wff): $ g |- p $ > $ g |- top -> p $;
    ;
    var snapshot = try buildSnapshot(mm0_text, null);
    defer snapshot.deinit();

    // A single annotation sits on the line above the declaration, exactly as
    // in the source; the old "Metadata: `@rewrite`." name-only summary is gone.
    const rewrite_offset =
        (std.mem.indexOf(u8, mm0_text, "top_i") orelse unreachable) + 1;
    const rewrite_hover = try snapshot.hoverAt(.mm0, rewrite_offset) orelse {
        return error.MissingAnnotatedHover;
    };
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        rewrite_hover.markdown,
        1,
        "```mm0\n--| @rewrite\naxiom top_i:",
    ));
    try std.testing.expect(!std.mem.containsAtLeast(
        u8,
        rewrite_hover.markdown,
        1,
        "Metadata:",
    ));

    // Several annotations keep their source order and their full text — the
    // view signature and the abstract patterns are what explain the rule.
    const view_offset =
        (std.mem.indexOf(u8, mm0_text, "axiom weaken") orelse unreachable) +
        "axiom ".len + 1;
    const view_hover = try snapshot.hoverAt(.mm0, view_offset) orelse {
        return error.MissingViewHover;
    };
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        view_hover.markdown,
        1,
        "```mm0\n" ++
            "--| @view (g: ctx) (p q: wff): $ g |- p $ > $ g |- q $\n" ++
            "--| @abstract p q $ top $ $ top -> top $\n" ++
            "--| @auto forward\n" ++
            "axiom weaken (g: ctx) (p: wff):",
    ));

    // Sorts carry theirs too.
    const sort_offset =
        (std.mem.indexOf(u8, mm0_text, "sort wff") orelse unreachable) +
        "sort ".len + 1;
    const sort_hover = try snapshot.hoverAt(.mm0, sort_offset) orelse {
        return error.MissingSortHover;
    };
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        sort_hover.markdown,
        1,
        "```mm0\n--| @vars u v\nprovable sort wff;",
    ));
}

test "global hover renders prose annotations as a doc comment" {
    const mm0_text =
        \\delimiter $ ( ) $;
        \\--| The sort of propositions.
        \\--| @vars u v
        \\provable sort wff;
        \\term top: wff;
        \\--| Truth is provable outright.
        \\--|
        \\--|
        \\--| Enrolled as a rewrite so `top` folds away.
        \\--| @rewrite
        \\--| Prose may follow a directive too.
        \\--|
        \\axiom top_i: $ top $;
    ;
    var snapshot = try buildSnapshot(mm0_text, null);
    defer snapshot.deinit();

    // Directives stay in the code fence; the prose becomes markdown
    // paragraphs after it. A blank `--|` line is a paragraph break (repeated
    // and trailing blanks collapse), and prose lines separated only by a
    // directive join into one paragraph.
    const axiom_offset =
        (std.mem.indexOf(u8, mm0_text, "top_i") orelse unreachable) + 1;
    const axiom_hover = try snapshot.hoverAt(.mm0, axiom_offset) orelse {
        return error.MissingAxiomHover;
    };
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        axiom_hover.markdown,
        1,
        "```mm0\n--| @rewrite\naxiom top_i:",
    ));
    try std.testing.expect(std.mem.endsWith(
        u8,
        axiom_hover.markdown,
        "$ top $;\n```\n\n" ++
            "Truth is provable outright.\n\n" ++
            "Enrolled as a rewrite so `top` folds away.\n" ++
            "Prose may follow a directive too.",
    ));
    try std.testing.expect(!std.mem.containsAtLeast(
        u8,
        axiom_hover.markdown,
        1,
        "--| Truth",
    ));

    // Sorts: summary line, fence, doc.
    const sort_offset =
        (std.mem.indexOf(u8, mm0_text, "sort wff") orelse unreachable) +
        "sort ".len + 1;
    const sort_hover = try snapshot.hoverAt(.mm0, sort_offset) orelse {
        return error.MissingSortHover;
    };
    try std.testing.expectEqualStrings(
        "Sort `wff`.\n\n```mm0\n--| @vars u v\nprovable sort wff;\n```\n\n" ++
            "The sort of propositions.",
        sort_hover.markdown,
    );
}

test "sorry! hovers as an admitted line and is offered with the tactics" {
    const mm0_text =
        \\provable sort wff;
        \\axiom use (p: wff): $ p $;
        \\theorem main (p: wff): $ p $ > $ p $;
    ;
    const proof_text =
        \\main
        \\----
        \\l1: $ p $ by sorry!
        \\l2: $ p $ by so
    ;
    var snapshot = try buildSnapshot(mm0_text, proof_text);
    defer snapshot.deinit();

    const sorry_offset =
        (std.mem.indexOf(u8, proof_text, "sorry!") orelse unreachable) + 1;
    const hover = try snapshot.hoverAt(.proof, sorry_offset) orelse {
        return error.MissingSorryHover;
    };
    try std.testing.expectEqualStrings(
        "sorry!",
        snapshot.proof_text.?[hover.range.start..hover.range.end],
    );
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        hover.markdown,
        1,
        "admits this line",
    ));

    const stem_offset = std.mem.indexOf(u8, proof_text, "by so") orelse {
        return error.MissingRuleContext;
    };
    const items = try snapshot.completionsAt(
        std.testing.allocator,
        .proof,
        stem_offset + "by so".len,
        .{},
    );
    defer std.testing.allocator.free(items);
    const sorry = completionNamed(items, "sorry!") orelse {
        return error.MissingSorryCompletion;
    };
    try std.testing.expectEqual(Index.CompletionKind.keyword, sorry.kind);
    try std.testing.expectEqualStrings("sorry!", sorry.replacement_text);
}

/// Expect the references in the proof to what is at `offset` to start at
/// `expected`.
fn expectReferences(
    snapshot: *Snapshot,
    document: Index.DocumentId,
    offset: usize,
    expected: []const usize,
) !void {
    const ranges = try snapshot.referencesAt(std.testing.allocator, document, offset, true);
    defer std.testing.allocator.free(ranges);
    var in_proof = std.ArrayListUnmanaged(usize).empty;
    defer in_proof.deinit(std.testing.allocator);
    for (ranges) |range| {
        if (range.document == .proof) try in_proof.append(std.testing.allocator, range.start);
    }
    try std.testing.expectEqualSlices(usize, expected, in_proof.items);
}

test "references reach every body that refers to the declaration" {
    const mm0_text =
        \\delimiter $ x ( ) $;
        \\provable sort wff;
        \\term a: wff;
        \\term neg (p: wff): wff;
        \\prefix neg: $x$ prec 10;
        \\axiom ax (p: wff) (h: $ p $): $ xp $;
        \\theorem one (h: $ a $): $ xa $;
        \\theorem two (h: $ a $): $ xa $;
    ;
    const proof_text =
        \\one
        \\---
        \\l1: $ xa $ by ax (p := $ a $) [#1]
        \\l2: $ xa $ by ax (p := $ a $) [#h]
        \\
        \\two
        \\---
        \\l1: $ xa $ by ax (p := $ a $) [#1]
        \\
    ;
    var snapshot = try buildSnapshot(mm0_text, proof_text);
    defer snapshot.deinit();
    try std.testing.expect(snapshot.complete);

    const line = "l1: $ xa $ by ax (p := $ a $) [#1]\n";
    const one = std.mem.indexOf(u8, proof_text, "l1").?;
    const lines = [_]usize{ one, one + line.len, std.mem.lastIndexOf(u8, proof_text, "l1").? };
    const at = struct {
        fn all(starts: [3]usize, comptime use: []const u8) [3]usize {
            var result = starts;
            for (&result) |*start| start.* += comptime std.mem.indexOf(u8, line, use).?;
            return result;
        }
    }.all;

    // A letter that is a delimiter ends a token.
    const a_uses = at(lines, "a $ by");
    const a_bound = at(lines, "a $) [");
    try expectReferences(&snapshot, .proof, a_uses[0], &.{
        a_uses[0], a_bound[0], a_uses[1], a_bound[1], a_uses[2], a_bound[2],
    });
    // A notation token.
    try expectReferences(&snapshot, .proof, at(lines, "xa")[2], &at(lines, "xa"));
    // A rule, and its binder.
    try expectReferences(&snapshot, .proof, at(lines, "ax (")[2], &at(lines, "ax ("));
    try expectReferences(&snapshot, .proof, at(lines, "p :=")[2], &at(lines, "p :="));
    // A hypothesis by position and by name, each in its own block.
    const refs = at(lines, "#1");
    try expectReferences(&snapshot, .proof, refs[0], refs[0..1]);
    try expectReferences(&snapshot, .proof, refs[1], refs[1..2]);
    try expectReferences(&snapshot, .proof, refs[2], refs[2..3]);
    // A line.
    try expectReferences(&snapshot, .proof, lines[0], lines[0..1]);

    // Highlights read only the ranges asked for.
    const two = std.mem.indexOf(u8, proof_text, "two").?;
    const highlights = try snapshot.highlightsAt(std.testing.allocator, .proof, a_uses[0], &.{
        .{ .document = .proof, .start = 0, .end = lines[1] },
        .{ .document = .proof, .start = two, .end = proof_text.len },
    });
    defer std.testing.allocator.free(highlights);
    var starts: [4]usize = undefined;
    try std.testing.expectEqual(starts.len, highlights.len);
    for (&starts, highlights) |*start, highlight| start.* = highlight.range.start;
    try std.testing.expectEqualSlices(
        usize,
        &.{ a_uses[0], a_bound[0], a_uses[2], a_bound[2] },
        &starts,
    );
}

test "a line reference means the nearest earlier line with its label" {
    const mm0_text =
        \\provable sort wff;
        \\term top: wff;
        \\axiom top_i: $ top $;
        \\axiom keep (h: $ top $): $ top $;
        \\theorem main: $ top $;
    ;
    const proof_text =
        \\main
        \\----
        \\l1: $ top $ by top_i []
        \\l1: $ top $ by keep [l1]
        \\l2: $ top $ by keep [l1]
    ;
    var snapshot = try buildSnapshot(mm0_text, proof_text);
    defer snapshot.deinit();

    const first = std.mem.indexOf(u8, proof_text, "l1:").?;
    const second = std.mem.lastIndexOf(u8, proof_text, "l1:").?;
    const in_second = std.mem.indexOf(u8, proof_text, "l1]").?;
    const in_last = std.mem.lastIndexOf(u8, proof_text, "l1]").?;
    for ([_]usize{ in_second, in_last }, [_]usize{ first, second }) |use, line| {
        const def = (try snapshot.definitionAt(.proof, use)).?;
        try std.testing.expectEqual(line, def.start);
    }
}
