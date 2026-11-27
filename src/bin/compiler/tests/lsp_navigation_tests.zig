const std = @import("std");
const lsp = @import("lsp");
const mm0 = @import("mm0");
const lsp_server = @import("../lsp.zig");
const types = lsp.types.flat;
const Handler = lsp_server.Handler;

const support = @import("./lsp_support.zig");
const Session = support.Session;
const testPosition = support.testPosition;
const testLastPosition = support.testLastPosition;
const expectRangeText = support.expectRangeText;
const expectDefinitionLocation = support.expectDefinitionLocation;
const expectImplementationLocation = support.expectImplementationLocation;
const expectDocumentSymbols = support.expectDocumentSymbols;
const lsp_navigation_mm0_text = support.lsp_navigation_mm0_text;
const lsp_navigation_proof_text = support.lsp_navigation_proof_text;
const putLspNavigationDocuments = support.putLspNavigationDocuments;
const lsp_import_lib_text = support.lsp_import_lib_text;
const lsp_import_main_text = support.lsp_import_main_text;
const lsp_import_proof_text = support.lsp_import_proof_text;

fn expectCompletionItems(
    result: lsp.ResultType("textDocument/completion"),
) ![]const types.CompletionItem {
    const value = result orelse return error.ExpectedCompletions;
    return switch (value) {
        // Always a list, and always incomplete: the items depend on the token
        // under the cursor, so a client must re-query rather than filter the
        // previous answer.
        .completion_list => |list| blk: {
            if (!list.isIncomplete) return error.ExpectedIncompleteCompletions;
            break :blk list.items;
        },
        else => error.ExpectedCompletions,
    };
}

fn completionItemNamed(
    items: []const types.CompletionItem,
    label: []const u8,
) ?types.CompletionItem {
    for (items) |item| {
        if (std.mem.eql(u8, item.label, label)) return item;
    }
    return null;
}

fn expectCompletionEditText(
    text: []const u8,
    item: types.CompletionItem,
    expected_old: []const u8,
    expected_new: []const u8,
) !void {
    const edit = item.textEdit orelse return error.ExpectedTextEdit;
    const text_edit = switch (edit) {
        .text_edit => |value| value,
        else => return error.ExpectedTextEdit,
    };
    try expectRangeText(text, text_edit.range, expected_old);
    try std.testing.expectEqualStrings(expected_new, text_edit.newText);
}

test "LSP proof hover accepts UTF-16 positions after non-ASCII text" {
    const mm0_uri = "file:///tmp/lsp-utf16.mm0";
    const proof_uri = "file:///tmp/lsp-utf16.auf";
    const proof_text =
        \\main
        \\----
        \\l1: $ 💡 top $ by top_i []
        \\l2: $ top $ by keep [l1]
    ;

    var session: Session = undefined;
    session.init();
    defer session.deinit();
    try session.handler.putDocument(mm0_uri, lsp_navigation_mm0_text, 1);
    try session.handler.putDocument(proof_uri, proof_text, 1);

    const hover_result = try session.handler.@"textDocument/hover"(
        session.arena(),
        .{
            .textDocument = .{ .uri = proof_uri },
            .position = try testPosition(proof_text, "top_i"),
        },
    );
    const hover = hover_result orelse return error.ExpectedHover;
    const range = hover.range orelse return error.ExpectedHoverRange;
    try expectRangeText(proof_text, range, "top_i");

    const markdown = switch (hover.contents) {
        .markup_content => |content| content.value,
        else => return error.ExpectedMarkdownHover,
    };
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        markdown,
        1,
        "axiom top_i",
    ));
}

test "LSP proof hover resolves rule applications" {
    const mm0_uri = "file:///tmp/lsp-stage2.mm0";
    const proof_uri = "file:///tmp/lsp-stage2.auf";

    var session: Session = undefined;
    session.init();
    defer session.deinit();
    try putLspNavigationDocuments(&session.handler, mm0_uri, proof_uri);

    const hover_result = try session.handler.@"textDocument/hover"(
        session.arena(),
        .{
            .textDocument = .{ .uri = proof_uri },
            .position = try testLastPosition(lsp_navigation_proof_text, "keep"),
        },
    );
    const hover = hover_result orelse return error.ExpectedHover;
    const range = hover.range orelse return error.ExpectedHoverRange;
    try expectRangeText(lsp_navigation_proof_text, range, "keep");

    const markdown = switch (hover.contents) {
        .markup_content => |content| content.value,
        else => return error.ExpectedMarkdownHover,
    };
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        markdown,
        1,
        "axiom keep",
    ));
}

test "LSP completion returns only rules applicable to the line goal" {
    const mm0_uri = "file:///tmp/lsp-applicable-completion.mm0";
    const proof_uri = "file:///tmp/lsp-applicable-completion.auf";
    const mm0_text =
        \\provable sort wff;
        \\term top: wff;
        \\term bot: wff;
        \\axiom top_i: $ top $;
        \\axiom bot_i: $ bot $;
        \\axiom keep: $ top $ > $ top $;
        \\theorem main: $ top $;
    ;
    const proof_text =
        \\main
        \\----
        \\l1: $ top $ by ke
    ;

    var session: Session = undefined;
    session.init();
    defer session.deinit();
    try session.handler.putDocument(mm0_uri, mm0_text, 1);
    try session.handler.putDocument(proof_uri, proof_text, 1);

    const result = try session.handler.@"textDocument/completion"(
        session.arena(),
        .{
            .textDocument = .{ .uri = proof_uri },
            .position = lsp.offsets.indexToPosition(
                proof_text,
                proof_text.len,
                .@"utf-16",
            ),
        },
    );
    const items = try expectCompletionItems(result);
    try std.testing.expect(completionItemNamed(items, "top_i") != null);
    try std.testing.expect(completionItemNamed(items, "keep") != null);
    try std.testing.expect(completionItemNamed(items, "bot_i") == null);

    const keep = completionItemNamed(items, "keep") orelse {
        return error.MissingApplicableKeepCompletion;
    };
    try expectCompletionEditText(proof_text, keep, "ke", "keep [?]");
}

test "LSP completion filters rules inside nested applications" {
    const mm0_uri = "file:///tmp/lsp-nested-applicable-completion.mm0";
    const proof_uri = "file:///tmp/lsp-nested-applicable-completion.auf";
    const mm0_text =
        \\provable sort wff;
        \\term top: wff;
        \\term bot: wff;
        \\axiom top_i: $ top $;
        \\axiom bot_i: $ bot $;
        \\axiom keep: $ top $ > $ top $;
        \\theorem main: $ top $;
    ;
    const proof_text =
        \\main
        \\----
        \\l1: $ top $ by keep [to []]
    ;
    const offset = (std.mem.indexOf(u8, proof_text, "to []") orelse {
        return error.MissingNestedCompletionContext;
    }) + "to".len;

    var session: Session = undefined;
    session.init();
    defer session.deinit();
    try session.handler.putDocument(mm0_uri, mm0_text, 1);
    try session.handler.putDocument(proof_uri, proof_text, 1);

    const result = try session.handler.@"textDocument/completion"(
        session.arena(),
        .{
            .textDocument = .{ .uri = proof_uri },
            .position = lsp.offsets.indexToPosition(
                proof_text,
                offset,
                .@"utf-16",
            ),
        },
    );
    const items = try expectCompletionItems(result);
    try std.testing.expect(completionItemNamed(items, "top_i") != null);
    try std.testing.expect(completionItemNamed(items, "bot_i") == null);
}

test "LSP completion returns explicit edits" {
    const mm0_uri = "file:///tmp/lsp-completion.mm0";
    const proof_uri = "file:///tmp/lsp-completion.auf";
    const proof_text =
        \\main
        \\----
        \\l1: $ top $ by top_i []
        \\l2: $ top $ by ke
    ;

    var session: Session = undefined;
    session.init();
    defer session.deinit();
    try session.handler.putDocument(mm0_uri, lsp_navigation_mm0_text, 1);
    try session.handler.putDocument(proof_uri, proof_text, 1);

    const result = try session.handler.@"textDocument/completion"(
        session.arena(),
        .{
            .textDocument = .{ .uri = proof_uri },
            .position = lsp.offsets.indexToPosition(
                proof_text,
                proof_text.len,
                .@"utf-16",
            ),
        },
    );
    const items = try expectCompletionItems(result);
    const keep = completionItemNamed(items, "keep") orelse {
        return error.MissingKeepCompletion;
    };
    try std.testing.expectEqual(types.CompletionItemKind.Constant, keep.kind.?);
    try expectCompletionEditText(proof_text, keep, "ke", "keep [?]");
}

test "LSP completion uses UTF-16 ranges after non-ASCII text" {
    const mm0_uri = "file:///tmp/lsp-completion-utf16.mm0";
    const proof_uri = "file:///tmp/lsp-completion-utf16.auf";
    const proof_text =
        \\main
        \\----
        \\l1: $ top $ by top_i []
        \\l2: $ 💡 top $ by ke
    ;
    const offset = (std.mem.indexOf(u8, proof_text, "ke") orelse {
        return error.MissingUtf16CompletionContext;
    }) + "ke".len;

    var session: Session = undefined;
    session.init();
    defer session.deinit();
    try session.handler.putDocument(mm0_uri, lsp_navigation_mm0_text, 1);
    try session.handler.putDocument(proof_uri, proof_text, 1);

    const result = try session.handler.@"textDocument/completion"(
        session.arena(),
        .{
            .textDocument = .{ .uri = proof_uri },
            .position = lsp.offsets.indexToPosition(
                proof_text,
                offset,
                .@"utf-16",
            ),
        },
    );
    const items = try expectCompletionItems(result);
    const keep = completionItemNamed(items, "keep") orelse {
        return error.MissingKeepUtf16Completion;
    };
    try expectCompletionEditText(proof_text, keep, "ke", "keep [?]");
}

test "LSP completion returns notation snippets for snippet clients" {
    const mm0_uri = "file:///tmp/lsp-snippet.mm0";
    const mm0_text =
        \\provable sort wff;
        \\term forall (p: wff): wff;
        \\theorem main (p: wff): $ fo $;
        \\prefix forall: $∀$ prec 40;
    ;
    const offset = (std.mem.indexOf(u8, mm0_text, "fo $") orelse {
        return error.MissingSnippetContext;
    }) + "fo".len;

    var session: Session = undefined;
    session.init();
    defer session.deinit();
    _ = session.handler.initialize(std.testing.allocator, .{
        .capabilities = .{
            .textDocument = .{
                .completion = .{
                    .completionItem = .{
                        .snippetSupport = true,
                    },
                },
            },
        },
    });
    try session.handler.putDocument(mm0_uri, mm0_text, 1);

    const result = try session.handler.@"textDocument/completion"(
        session.arena(),
        .{
            .textDocument = .{ .uri = mm0_uri },
            .position = lsp.offsets.indexToPosition(
                mm0_text,
                offset,
                .@"utf-16",
            ),
        },
    );
    const items = try expectCompletionItems(result);
    const snippet = completionItemNamed(items, "∀ …") orelse {
        return error.MissingSnippetCompletion;
    };
    try std.testing.expectEqual(types.CompletionItemKind.Snippet, snippet.kind.?);
    try std.testing.expectEqual(
        types.InsertTextFormat.Snippet,
        snippet.insertTextFormat.?,
    );
    try expectCompletionEditText(mm0_text, snippet, "fo", "∀ ${1:p}$0");
    try std.testing.expectEqualStrings(
        "forall ∀",
        snippet.filterText orelse "",
    );
    const term = completionItemNamed(items, "forall") orelse {
        return error.MissingTermCompletion;
    };
    try std.testing.expectEqual(types.CompletionItemKind.Constructor, term.kind.?);
}

test "LSP completion avoids snippets for plain completion clients" {
    const mm0_uri = "file:///tmp/lsp-no-snippet.mm0";
    const mm0_text =
        \\provable sort wff;
        \\term forall (p: wff): wff;
        \\theorem main (p: wff): $ fo $;
        \\prefix forall: $∀$ prec 40;
    ;
    const offset = (std.mem.indexOf(u8, mm0_text, "fo $") orelse {
        return error.MissingSnippetContext;
    }) + "fo".len;

    var session: Session = undefined;
    session.init();
    defer session.deinit();
    _ = session.handler.initialize(std.testing.allocator, .{
        .capabilities = .{},
    });
    try session.handler.putDocument(mm0_uri, mm0_text, 1);

    const result = try session.handler.@"textDocument/completion"(
        session.arena(),
        .{
            .textDocument = .{ .uri = mm0_uri },
            .position = lsp.offsets.indexToPosition(
                mm0_text,
                offset,
                .@"utf-16",
            ),
        },
    );
    const items = try expectCompletionItems(result);
    try std.testing.expect(completionItemNamed(items, "∀ …") == null);
    for (items) |item| {
        if (item.insertTextFormat) |format| {
            try std.testing.expect(format != .Snippet);
        }
    }
}

test "LSP proof definition resolves rules and line references" {
    const mm0_uri = "file:///tmp/lsp-stage2.mm0";
    const proof_uri = "file:///tmp/lsp-stage2.auf";

    var session: Session = undefined;
    session.init();
    defer session.deinit();
    try putLspNavigationDocuments(&session.handler, mm0_uri, proof_uri);

    const arena = session.arena();

    const rule_location = try expectDefinitionLocation(
        try session.handler.@"textDocument/definition"(arena, .{
            .textDocument = .{ .uri = proof_uri },
            .position = try testLastPosition(lsp_navigation_proof_text, "keep"),
        }),
    );
    try std.testing.expectEqualStrings(mm0_uri, rule_location.uri);
    try expectRangeText(lsp_navigation_mm0_text, rule_location.range, "keep");

    const line_location = try expectDefinitionLocation(
        try session.handler.@"textDocument/definition"(arena, .{
            .textDocument = .{ .uri = proof_uri },
            .position = try testLastPosition(lsp_navigation_proof_text, "l1"),
        }),
    );
    try std.testing.expectEqualStrings(proof_uri, line_location.uri);
    try expectRangeText(lsp_navigation_proof_text, line_location.range, "l1");
}

test "LSP implementation resolves theorem declarations to proofs" {
    const mm0_uri = "file:///tmp/lsp-stage2.mm0";
    const proof_uri = "file:///tmp/lsp-stage2.auf";

    var session: Session = undefined;
    session.init();
    defer session.deinit();
    try putLspNavigationDocuments(&session.handler, mm0_uri, proof_uri);

    const arena = session.arena();

    const location = try expectImplementationLocation(
        try session.handler.@"textDocument/implementation"(arena, .{
            .textDocument = .{ .uri = mm0_uri },
            .position = try testLastPosition(lsp_navigation_mm0_text, "main"),
        }),
    );
    try std.testing.expectEqualStrings(proof_uri, location.uri);
    try expectRangeText(lsp_navigation_proof_text, location.range, "main");

    const axiom = try session.handler.@"textDocument/implementation"(arena, .{
        .textDocument = .{ .uri = mm0_uri },
        .position = try testLastPosition(lsp_navigation_mm0_text, "keep"),
    });
    try std.testing.expect(axiom == null);
}

test "LSP references returns matching indexed symbol uses" {
    const mm0_uri = "file:///tmp/lsp-stage2.mm0";
    const proof_uri = "file:///tmp/lsp-stage2.auf";

    var session: Session = undefined;
    session.init();
    defer session.deinit();
    try putLspNavigationDocuments(&session.handler, mm0_uri, proof_uri);

    const arena = session.arena();

    const rule_refs = (try session.handler.@"textDocument/references"(arena, .{
        .textDocument = .{ .uri = proof_uri },
        .position = try testPosition(lsp_navigation_proof_text, "top_i"),
        .context = .{ .includeDeclaration = true },
    })) orelse return error.ExpectedReferences;
    try std.testing.expectEqual(@as(usize, 2), rule_refs.len);
    try std.testing.expectEqualStrings(mm0_uri, rule_refs[0].uri);
    try expectRangeText(lsp_navigation_mm0_text, rule_refs[0].range, "top_i");
    try std.testing.expectEqualStrings(proof_uri, rule_refs[1].uri);
    try expectRangeText(lsp_navigation_proof_text, rule_refs[1].range, "top_i");

    const rule_uses = (try session.handler.@"textDocument/references"(arena, .{
        .textDocument = .{ .uri = proof_uri },
        .position = try testPosition(lsp_navigation_proof_text, "top_i"),
        .context = .{ .includeDeclaration = false },
    })) orelse return error.ExpectedReferences;
    try std.testing.expectEqual(@as(usize, 1), rule_uses.len);
    try std.testing.expectEqualStrings(proof_uri, rule_uses[0].uri);
    try expectRangeText(lsp_navigation_proof_text, rule_uses[0].range, "top_i");

    const theorem_uses = (try session.handler.@"textDocument/references"(arena, .{
        .textDocument = .{ .uri = mm0_uri },
        .position = try testLastPosition(lsp_navigation_mm0_text, "main"),
        .context = .{ .includeDeclaration = false },
    })) orelse return error.ExpectedReferences;
    try std.testing.expectEqual(@as(usize, 1), theorem_uses.len);
    try std.testing.expectEqualStrings(proof_uri, theorem_uses[0].uri);
    try expectRangeText(lsp_navigation_proof_text, theorem_uses[0].range, "main");
}

test "LSP document symbols returns quiet proof outline" {
    const mm0_uri = "file:///tmp/lsp-stage2.mm0";
    const proof_uri = "file:///tmp/lsp-stage2.auf";

    var session: Session = undefined;
    session.init();
    defer session.deinit();
    try putLspNavigationDocuments(&session.handler, mm0_uri, proof_uri);

    const arena = session.arena();

    const symbols = try expectDocumentSymbols(
        try session.handler.@"textDocument/documentSymbol"(arena, .{
            .textDocument = .{ .uri = proof_uri },
        }),
    );
    try std.testing.expectEqual(@as(usize, 1), symbols.len);
    try std.testing.expectEqualStrings("main", symbols[0].name);
    try std.testing.expectEqual(types.SymbolKind.Method, symbols[0].kind);
    try std.testing.expect(symbols[0].children == null);
}

test "LSP navigation cache invalidates changed mm0 sibling" {
    const mm0_uri = "file:///tmp/lsp-stage5.mm0";
    const proof_uri = "file:///tmp/lsp-stage5.auf";
    const changed_mm0_text =
        \\provable sort wff;
        \\term top: wff;
        \\axiom top_i: $ top $;
        \\axiom keep2: $ top $ > $ top $;
        \\theorem main: $ top $ > $ top $;
    ;

    var session: Session = undefined;
    session.init();
    defer session.deinit();
    try putLspNavigationDocuments(&session.handler, mm0_uri, proof_uri);

    const arena = session.arena();

    const first_hover = try session.handler.@"textDocument/hover"(arena, .{
        .textDocument = .{ .uri = proof_uri },
        .position = try testLastPosition(lsp_navigation_proof_text, "keep"),
    });
    try std.testing.expect(first_hover != null);
    try std.testing.expectEqual(@as(usize, 1), session.indexedRoots());

    try session.handler.@"textDocument/didChange"(arena, .{
        .textDocument = .{ .uri = mm0_uri, .version = 2 },
        .contentChanges = &.{
            .{ .text_document_content_change_whole_document = .{ .text = changed_mm0_text } },
        },
    });
    try std.testing.expectEqual(@as(usize, 0), session.indexedRoots());

    const hover_result = try session.handler.@"textDocument/hover"(arena, .{
        .textDocument = .{ .uri = proof_uri },
        .position = try testLastPosition(lsp_navigation_proof_text, "keep"),
    });
    const hover = hover_result orelse return error.ExpectedHover;
    const markdown = switch (hover.contents) {
        .markup_content => |content| content.value,
        else => return error.ExpectedMarkdownHover,
    };
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        markdown,
        1,
        "unknown rule `keep`",
    ));
}

test "LSP navigation cache invalidates closed proof sibling" {
    const mm0_uri = "file:///tmp/lsp-stage5-close.mm0";
    const proof_uri = "file:///tmp/lsp-stage5-close.auf";

    var session: Session = undefined;
    session.init();
    defer session.deinit();
    try putLspNavigationDocuments(&session.handler, mm0_uri, proof_uri);

    const arena = session.arena();

    const hover_result = try session.handler.@"textDocument/hover"(arena, .{
        .textDocument = .{ .uri = proof_uri },
        .position = try testLastPosition(lsp_navigation_proof_text, "keep"),
    });
    try std.testing.expect(hover_result != null);
    try std.testing.expectEqual(@as(usize, 1), session.indexedRoots());

    try session.handler.@"textDocument/didClose"(arena, .{
        .textDocument = .{ .uri = proof_uri },
    });
    try std.testing.expectEqual(@as(usize, 0), session.indexedRoots());
}

test "LSP proof unknown rule has hover but no definition" {
    const mm0_uri = "file:///tmp/lsp-stage2-unknown.mm0";
    const proof_uri = "file:///tmp/lsp-stage2-unknown.auf";
    const mm0_text =
        \\provable sort wff;
        \\term top: wff;
        \\theorem main: $ top $;
    ;
    const proof_text =
        \\main
        \\----
        \\l1: $ top $ by missing []
    ;

    var session: Session = undefined;
    session.init();
    defer session.deinit();
    try session.handler.putDocument(mm0_uri, mm0_text, 1);
    try session.handler.putDocument(proof_uri, proof_text, 1);

    const arena = session.arena();

    const hover_result = try session.handler.@"textDocument/hover"(arena, .{
        .textDocument = .{ .uri = proof_uri },
        .position = try testPosition(proof_text, "missing"),
    });
    const hover = hover_result orelse return error.ExpectedHover;
    const markdown = switch (hover.contents) {
        .markup_content => |content| content.value,
        else => return error.ExpectedMarkdownHover,
    };
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        markdown,
        1,
        "unknown rule `missing`",
    ));

    const definition = try session.handler.@"textDocument/definition"(arena, .{
        .textDocument = .{ .uri = proof_uri },
        .position = try testPosition(proof_text, "missing"),
    });
    try std.testing.expect(definition == null);
}

fn openImportUnit(
    handler: *Handler,
    arena: std.mem.Allocator,
    lib_uri: []const u8,
    mm0_uri: []const u8,
    proof_uri: []const u8,
) !void {
    try handler.putDocument(lib_uri, lsp_import_lib_text, 1);
    try handler.putDocument(mm0_uri, lsp_import_main_text, 1);
    try handler.@"textDocument/didOpen"(arena, .{ .textDocument = .{
        .uri = proof_uri,
        .languageId = .{ .custom_value = "aufbau" },
        .version = 1,
        .text = lsp_import_proof_text,
    } });
}

fn renameEditsFor(edit: types.WorkspaceEdit, uri: []const u8) []const types.TextEdit {
    const changes = edit.changes orelse return &.{};
    return changes.map.get(uri) orelse &.{};
}

test "LSP rename edits every file of the unit" {
    const lib_uri = "file:///tmp/lsp-rename/lib.mm0";
    const mm0_uri = "file:///tmp/lsp-rename/main.mm0";
    const proof_uri = "file:///tmp/lsp-rename/main.auf";

    var session: Session = undefined;
    session.init();
    defer session.deinit();
    const arena = session.arena();
    try openImportUnit(&session.handler, arena, lib_uri, mm0_uri, proof_uri);

    const prepared = (try session.handler.@"textDocument/prepareRename"(arena, .{
        .textDocument = .{ .uri = proof_uri },
        .position = try testLastPosition(lsp_import_proof_text, "top_i"),
    })) orelse return error.ExpectedPrepareRename;
    switch (prepared) {
        .prepare_rename_placeholder => |placeholder| {
            try std.testing.expectEqualStrings("top_i", placeholder.placeholder);
            try expectRangeText(lsp_import_proof_text, placeholder.range, "top_i");
        },
        else => return error.ExpectedPlaceholder,
    }

    // A rule: its declaration in the imported file and its citation.
    const rule_edit = (try session.handler.@"textDocument/rename"(arena, .{
        .textDocument = .{ .uri = proof_uri },
        .position = try testLastPosition(lsp_import_proof_text, "top_i"),
        .newName = "truth",
    })) orelse return error.ExpectedRename;
    const lib_edits = renameEditsFor(rule_edit, lib_uri);
    try std.testing.expectEqual(@as(usize, 1), lib_edits.len);
    try expectRangeText(lsp_import_lib_text, lib_edits[0].range, "top_i");
    try std.testing.expectEqualStrings("truth", lib_edits[0].newText);
    const proof_edits = renameEditsFor(rule_edit, proof_uri);
    try std.testing.expectEqual(@as(usize, 1), proof_edits.len);
    try expectRangeText(lsp_import_proof_text, proof_edits[0].range, "top_i");
    try std.testing.expectEqual(@as(usize, 0), renameEditsFor(rule_edit, mm0_uri).len);

    // A term, from the root theory: every file names it.
    const term_edit = (try session.handler.@"textDocument/rename"(arena, .{
        .textDocument = .{ .uri = mm0_uri },
        .position = try testLastPosition(lsp_import_main_text, "top"),
        .newName = "T",
    })) orelse return error.ExpectedRename;
    try std.testing.expectEqual(@as(usize, 2), renameEditsFor(term_edit, lib_uri).len);
    try std.testing.expectEqual(@as(usize, 1), renameEditsFor(term_edit, mm0_uri).len);
    try std.testing.expectEqual(@as(usize, 1), renameEditsFor(term_edit, proof_uri).len);

    // Nothing to rename in an import statement.
    try std.testing.expect((try session.handler.@"textDocument/prepareRename"(arena, .{
        .textDocument = .{ .uri = mm0_uri },
        .position = try testPosition(lsp_import_main_text, "lib.mm0"),
    })) == null);
}

test "LSP rename says why it refuses" {
    const lib_uri = "file:///tmp/lsp-rename-refuse/lib.mm0";
    const mm0_uri = "file:///tmp/lsp-rename-refuse/main.mm0";
    const proof_uri = "file:///tmp/lsp-rename-refuse/main.auf";

    var session: Session = undefined;
    session.init();
    defer session.deinit();
    const arena = session.arena();
    try openImportUnit(&session.handler, arena, lib_uri, mm0_uri, proof_uri);

    session.transport.clearMessages();
    try std.testing.expect((try session.handler.@"textDocument/rename"(arena, .{
        .textDocument = .{ .uri = proof_uri },
        .position = try testLastPosition(lsp_import_proof_text, "top_i"),
        .newName = "top",
    })) == null);
    try std.testing.expect(session.transport.containsMessage("window/showMessage"));
    try std.testing.expect(session.transport.containsMessage("`top` is already in use."));

    session.transport.clearMessages();
    try std.testing.expect((try session.handler.@"textDocument/rename"(arena, .{
        .textDocument = .{ .uri = proof_uri },
        .position = try testLastPosition(lsp_import_proof_text, "by"),
        .newName = "x",
    })) == null);
    try std.testing.expect(session.transport.containsMessage("Nothing here can be renamed."));
}

test "LSP highlights a name's uses in the requested file only" {
    const lib_uri = "file:///tmp/lsp-highlight/lib.mm0";
    const mm0_uri = "file:///tmp/lsp-highlight/main.mm0";
    const proof_uri = "file:///tmp/lsp-highlight/main.auf";

    var session: Session = undefined;
    session.init();
    defer session.deinit();
    const arena = session.arena();
    try openImportUnit(&session.handler, arena, lib_uri, mm0_uri, proof_uri);

    const in_root = (try session.handler.@"textDocument/documentHighlight"(arena, .{
        .textDocument = .{ .uri = mm0_uri },
        .position = try testLastPosition(lsp_import_main_text, "top"),
    })) orelse return error.ExpectedHighlights;
    try std.testing.expectEqual(@as(usize, 1), in_root.len);
    try expectRangeText(lsp_import_main_text, in_root[0].range, "top");
    try std.testing.expectEqual(types.DocumentHighlight.Kind.Read, in_root[0].kind.?);

    const in_lib = (try session.handler.@"textDocument/documentHighlight"(arena, .{
        .textDocument = .{ .uri = lib_uri },
        .position = try testPosition(lsp_import_lib_text, "top"),
    })) orelse return error.ExpectedHighlights;
    try std.testing.expectEqual(@as(usize, 2), in_lib.len);
    try std.testing.expectEqual(types.DocumentHighlight.Kind.Write, in_lib[0].kind.?);
    try std.testing.expectEqual(types.DocumentHighlight.Kind.Read, in_lib[1].kind.?);
}
