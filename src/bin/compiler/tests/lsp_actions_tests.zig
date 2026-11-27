const std = @import("std");
const lsp = @import("lsp");
const mm0 = @import("mm0");
const types = lsp.types.flat;
const CodeActionResult = lsp.ResultType("textDocument/codeAction");
const CodeActionItems = @typeInfo(CodeActionResult).optional.child;
const CodeActionItem = @typeInfo(CodeActionItems).pointer.child;

const support = @import("./lsp_support.zig");
const Session = support.Session;
const testPosition = support.testPosition;
const expectRangeText = support.expectRangeText;
const expectCodeActionItems = support.expectCodeActionItems;
const codeActionSingleEdit = support.codeActionSingleEdit;
const codeActionParamsAt = support.codeActionParamsAt;
const lsp_navigation_proof_text = support.lsp_navigation_proof_text;
const putLspNavigationDocuments = support.putLspNavigationDocuments;
const lsp_search_mm0_text = support.lsp_search_mm0_text;

fn firstCodeAction(items: []const CodeActionItem) ?types.CodeAction {
    for (items) |item| switch (item) {
        .code_action => |action| return action,
        .command => {},
    };
    return null;
}

fn codeActionWithReplacement(
    items: []const CodeActionItem,
    uri: []const u8,
    expected_new: []const u8,
) ?types.CodeAction {
    for (items) |item| switch (item) {
        .code_action => |action| {
            const edit = codeActionSingleEdit(action, uri) orelse continue;
            if (std.mem.eql(u8, edit.newText, expected_new)) {
                return action;
            }
        },
        .command => {},
    };
    return null;
}

// Verify the (uncapped) search API offers `expected_replacement` at `marker`.
// Used where the LSP code action caps results below the rank of the suggestion
// under test (e.g. a local lemma outranked by an axiom), so the indexing must be
// checked at the search layer rather than the capped action list.
fn expectSearchOffers(
    allocator: std.mem.Allocator,
    proof_text: []const u8,
    marker: []const u8,
    expected_replacement: []const u8,
) !void {
    const Search = mm0.CompilerSupport.Search;
    const offset = std.mem.indexOf(u8, proof_text, marker) orelse
        return error.MissingMarker;
    var suggestions = try Search.suggestionsAtSourceOffset(
        allocator,
        lsp_search_mm0_text,
        proof_text,
        offset,
        .{},
    );
    defer suggestions.deinit();
    for (suggestions.items) |item| {
        if (std.mem.eql(u8, item.replacement, expected_replacement)) return;
    }
    return error.SearchDidNotOfferExpected;
}

const lsp_search_exact_proof_text =
    \\main
    \\----
    \\l1: $ top $ by exact?
;

test "LSP code action replaces exact placeholder" {
    const mm0_uri = "file:///tmp/lsp-code-action-exact.mm0";
    const proof_uri = "file:///tmp/lsp-code-action-exact.auf";

    var session: Session = undefined;
    session.init();
    defer session.deinit();
    try session.handler.putDocument(mm0_uri, lsp_search_mm0_text, 1);
    try session.handler.putDocument(proof_uri, lsp_search_exact_proof_text, 1);

    const actions = try session.codeActions(proof_uri, lsp_search_exact_proof_text, "exact?");
    const action = codeActionWithReplacement(actions, proof_uri, "top_i") orelse {
        return error.MissingExactCodeAction;
    };
    try std.testing.expectEqual(types.CodeActionKind.quickfix, action.kind.?);
    const edit = codeActionSingleEdit(action, proof_uri) orelse {
        return error.ExpectedCodeActionEdit;
    };
    try expectRangeText(lsp_search_exact_proof_text, edit.range, "exact?");
}

test "LSP code action applies a rule to an open goal" {
    const mm0_uri = "file:///tmp/lsp-code-action-open-goal.mm0";
    const proof_uri = "file:///tmp/lsp-code-action-open-goal.auf";
    const proof_text =
        \\main
        \\----
        \\l1: $ top $ by ?
    ;

    var session: Session = undefined;
    session.init();
    defer session.deinit();
    try session.handler.putDocument(mm0_uri, lsp_search_mm0_text, 1);
    try session.handler.putDocument(proof_uri, proof_text, 1);

    const actions = try session.codeActions(proof_uri, proof_text, "?");
    const action = codeActionWithReplacement(
        actions,
        proof_uri,
        "l1: $ top $ by keep [#1]",
    ) orelse return error.MissingApplyRuleAction;
    try std.testing.expectEqualStrings("Apply keep [#1]", action.title);
    try std.testing.expect(codeActionWithReplacement(actions, proof_uri, "sorry!") != null);
    // No search ran, so there is no outcome to show.
    try std.testing.expectEqual(@as(usize, 0), session.searchOutcomes(proof_uri));
}

test "LSP open goal action ends on the open goal it adds" {
    const mm0_uri = "file:///tmp/lsp-code-action-open-goal-cursor.mm0";
    const proof_uri = "file:///tmp/lsp-code-action-open-goal-cursor.auf";
    const mm0_text =
        \\provable sort wff;
        \\term top: wff;
        \\axiom keep: $ top $ > $ top $;
        \\theorem main: $ top $;
    ;
    const proof_text =
        \\main
        \\----
        \\l1: $ top $ by ?
    ;

    var session: Session = undefined;
    session.init();
    defer session.deinit();
    const result = session.handler.initialize(std.testing.allocator, .{
        .capabilities = .{ .window = .{ .showDocument = .{ .support = true } } },
    });
    const execute = result.capabilities.executeCommandProvider orelse
        return error.ExpectedExecuteCommandProvider;
    try std.testing.expectEqualStrings("aufbau.showOpenGoal", execute.commands[0]);
    try session.handler.putDocument(mm0_uri, mm0_text, 1);
    try session.handler.putDocument(proof_uri, proof_text, 1);

    const arena = session.arena();
    const actions = try expectCodeActionItems(
        try session.handler.@"textDocument/codeAction"(arena, try codeActionParamsAt(proof_uri, proof_text, "?")),
    );
    const action = codeActionWithReplacement(
        actions,
        proof_uri,
        "l1_1: $ top $ by ?\nl1: $ top $ by keep [l1_1]",
    ) orelse return error.MissingApplyRuleAction;
    // The new line's `?`, in the edited document.
    const command = action.command orelse return error.ExpectedCommand;
    try std.testing.expectEqualStrings("aufbau.showOpenGoal", command.command);
    const arguments = command.arguments orelse return error.ExpectedArguments;
    try std.testing.expectEqualStrings(proof_uri, arguments[0].string);
    const selection = try std.json.parseFromValueLeaky(types.Range, arena, arguments[1], .{});
    try std.testing.expectEqual(@as(u32, 2), selection.start.line);
    try std.testing.expectEqual(@as(u32, "l1_1: $ top $ by ".len), selection.start.character);
    try std.testing.expectEqual(selection.start.character + 1, selection.end.character);
    // `sorry!` adds no open goal.
    const sorry = codeActionWithReplacement(actions, proof_uri, "sorry!") orelse
        return error.MissingSorryAction;
    try std.testing.expect(sorry.command == null);

    session.transport.clearMessages();
    _ = try session.handler.@"workspace/executeCommand"(arena, .{
        .command = command.command,
        .arguments = arguments,
    });
    try std.testing.expect(session.transport.containsMessage("\"method\":\"window/showDocument\""));
    try std.testing.expect(session.transport.containsMessage("\"selection\":{\"start\":{\"line\":2,\"character\":17}"));
}

test "LSP code action offers unpack for inline applications" {
    const mm0_uri = "file:///tmp/lsp-code-action-unpack.mm0";
    const proof_uri = "file:///tmp/lsp-code-action-unpack.auf";
    const proof_text =
        \\main
        \\----
        \\l1: $ top $ by keep [top_i []]
        \\
    ;

    var session: Session = undefined;
    session.init();
    defer session.deinit();
    try session.handler.putDocument(mm0_uri, lsp_search_mm0_text, 1);
    try session.handler.putDocument(proof_uri, proof_text, 1);

    const actions = try session.codeActions(proof_uri, proof_text, "keep [top_i");
    const expected_replacement =
        \\l1_1: $ top $ by top_i
        \\l1: $ top $ by keep [l1_1]
        \\
    ;
    const action = codeActionWithReplacement(
        actions,
        proof_uri,
        expected_replacement,
    ) orelse return error.MissingUnpackCodeAction;
    try std.testing.expectEqual(
        types.CodeActionKind.@"refactor.rewrite",
        action.kind.?,
    );
    try std.testing.expectEqualStrings(
        "Unpack inline application",
        action.title,
    );
    const edit = codeActionSingleEdit(action, proof_uri) orelse {
        return error.ExpectedCodeActionEdit;
    };
    try expectRangeText(
        proof_text,
        edit.range,
        "l1: $ top $ by keep [top_i []]\n",
    );
}

/// `keep [keep [... top_i [] ...]]` nested `depth` reference lists deep.
fn nestedKeepProof(allocator: std.mem.Allocator, depth: usize) ![]u8 {
    var text: std.ArrayListUnmanaged(u8) = .empty;
    try text.appendSlice(allocator, "main\n----\nl1: $ top $ by ");
    for (1..depth) |_| try text.appendSlice(allocator, "keep [");
    try text.appendSlice(allocator, "top_i []");
    try text.appendNTimes(allocator, ']', depth - 1);
    try text.append(allocator, '\n');
    return text.toOwnedSlice(allocator);
}

test "LSP survives proofs nested to the parser's limit and past it" {
    const mm0_uri = "file:///tmp/lsp-deep-nesting.mm0";
    const proof_uri = "file:///tmp/lsp-deep-nesting.auf";
    var session: Session = undefined;
    session.init();
    defer session.deinit();
    const arena = session.arena();

    try session.open(mm0_uri, lsp_search_mm0_text);

    // The deepest nesting the parser accepts: the checker's stack guard
    // stops it, and every editor feature still walks the parsed tree.
    const deepest = try nestedKeepProof(arena, mm0.ProofScript.max_inline_depth);
    session.transport.clearMessages();
    try session.open(proof_uri, deepest);
    try std.testing.expect(session.transport.containsMessage("too deeply to check"));
    const position = try testPosition(deepest, "top_i");
    _ = try session.handler.@"textDocument/hover"(arena, .{
        .textDocument = .{ .uri = proof_uri },
        .position = position,
    });
    _ = try session.codeActionsAt(proof_uri, deepest, "top_i");
    _ = try session.handler.@"textDocument/documentSymbol"(arena, .{
        .textDocument = .{ .uri = proof_uri },
    });

    // One level more is a parse error.
    const too_deep = try nestedKeepProof(arena, mm0.ProofScript.max_inline_depth + 1);
    session.transport.clearMessages();
    try session.change(proof_uri, 2, too_deep);
    try std.testing.expect(session.transport.containsMessage("more than 1024 levels"));
}

test "LSP code action caches search results across identical requests" {
    const mm0_uri = "file:///tmp/lsp-code-action-cache.mm0";
    const proof_uri = "file:///tmp/lsp-code-action-cache.auf";

    var session: Session = undefined;
    session.init();
    defer session.deinit();
    try session.handler.putDocument(mm0_uri, lsp_search_mm0_text, 1);
    try session.handler.putDocument(proof_uri, lsp_search_exact_proof_text, 1);

    const first = try session.codeActions(proof_uri, lsp_search_exact_proof_text, "exact?");
    try std.testing.expect(session.searchResults(proof_uri) != null);
    const cached_ptr = session.searchResults(proof_uri).?;
    const first_action =
        codeActionWithReplacement(first, proof_uri, "top_i") orelse
        return error.MissingExactCodeAction;

    // A second identical request must reuse the cached entry (same backing
    // suggestions, no eviction/recompute) rather than re-running the search.
    const second = try session.codeActions(proof_uri, lsp_search_exact_proof_text, "exact?");
    try std.testing.expect(session.searchResults(proof_uri) != null);
    try std.testing.expectEqual(
        cached_ptr,
        session.searchResults(proof_uri).?,
    );
    const second_action =
        codeActionWithReplacement(second, proof_uri, "top_i") orelse
        return error.MissingExactCodeAction;

    const first_edit =
        codeActionSingleEdit(first_action, proof_uri).?;
    const second_edit =
        codeActionSingleEdit(second_action, proof_uri).?;
    try std.testing.expectEqualStrings(
        first_edit.newText,
        second_edit.newText,
    );
}

test "LSP code action cache hits across different offsets on the same step" {
    const mm0_uri = "file:///tmp/lsp-code-action-cache-offset.mm0";
    const proof_uri = "file:///tmp/lsp-code-action-cache-offset.auf";

    var session: Session = undefined;
    session.init();
    defer session.deinit();
    try session.handler.putDocument(mm0_uri, lsp_search_mm0_text, 1);
    try session.handler.putDocument(proof_uri, lsp_search_exact_proof_text, 1);

    // First request lands inside the goal text `$ top $`...
    _ = try session.codeActions(proof_uri, lsp_search_exact_proof_text, "top");
    try std.testing.expect(session.searchResults(proof_uri) != null);
    const cached_ptr = session.searchResults(proof_uri).?;

    // ...a second request at a different column of the SAME proof step (the
    // `exact?` keyword) must reuse the cached result via its placeholder span,
    // not re-run the search and evict.
    const second = try session.codeActions(proof_uri, lsp_search_exact_proof_text, "exact?");
    try std.testing.expect(session.searchResults(proof_uri) != null);
    try std.testing.expectEqual(
        cached_ptr,
        session.searchResults(proof_uri).?,
    );
    try std.testing.expect(
        codeActionWithReplacement(second, proof_uri, "top_i") != null,
    );
}

test "LSP code action search cache is freed when the document closes" {
    const mm0_uri = "file:///tmp/lsp-code-action-cache-close.mm0";
    const proof_uri = "file:///tmp/lsp-code-action-cache-close.auf";

    var session: Session = undefined;
    session.init();
    defer session.deinit();
    try session.handler.putDocument(mm0_uri, lsp_search_mm0_text, 1);
    try session.handler.putDocument(proof_uri, lsp_search_exact_proof_text, 1);

    _ = try session.codeActions(proof_uri, lsp_search_exact_proof_text, "exact?");
    try std.testing.expect(session.searchResults(proof_uri) != null);

    try session.close(proof_uri);
    try std.testing.expect(session.searchResults(proof_uri) == null);
}

test "LSP code action replaces entire placeholder application" {
    const mm0_uri = "file:///tmp/lsp-code-action-stale-ref.mm0";
    const proof_uri = "file:///tmp/lsp-code-action-stale-ref.auf";
    const proof_text =
        \\main
        \\----
        \\l1: $ top $ by exact? [#1]
    ;

    var session: Session = undefined;
    session.init();
    defer session.deinit();
    try session.handler.putDocument(mm0_uri, lsp_search_mm0_text, 1);
    try session.handler.putDocument(proof_uri, proof_text, 1);

    const actions = try session.codeActions(proof_uri, proof_text, "exact?");
    const action = codeActionWithReplacement(actions, proof_uri, "top_i") orelse {
        return error.MissingWholeApplicationCodeAction;
    };
    const edit = codeActionSingleEdit(action, proof_uri) orelse {
        return error.ExpectedCodeActionEdit;
    };
    try expectRangeText(proof_text, edit.range, "exact? [#1]");
}

test "LSP code action completes inline exact placeholder" {
    const mm0_uri = "file:///tmp/lsp-code-action-inline-exact.mm0";
    const proof_uri = "file:///tmp/lsp-code-action-inline-exact.auf";
    const proof_text =
        \\main
        \\----
        \\l1: $ top $ by keep [exact?]
    ;

    var session: Session = undefined;
    session.init();
    defer session.deinit();
    try session.handler.putDocument(mm0_uri, lsp_search_mm0_text, 1);
    try session.handler.putDocument(proof_uri, proof_text, 1);

    const actions = try session.codeActions(proof_uri, proof_text, "exact?");
    const action = codeActionWithReplacement(actions, proof_uri, "#1") orelse {
        return error.MissingInlineExactCodeAction;
    };
    const edit = codeActionSingleEdit(action, proof_uri) orelse {
        return error.ExpectedCodeActionEdit;
    };
    try expectRangeText(proof_text, edit.range, "exact?");
}

test "LSP diagnostics ignore inline search placeholders" {
    const mm0_uri = "file:///tmp/lsp-inline-placeholder-diag.mm0";
    const proof_uri = "file:///tmp/lsp-inline-placeholder-diag.auf";
    const proof_text =
        \\main
        \\----
        \\l1: $ top $ by keep [exact?]
    ;

    var session: Session = undefined;
    session.init();
    defer session.deinit();

    try session.open(mm0_uri, lsp_search_mm0_text);
    session.transport.clearMessages();
    try session.open(proof_uri, proof_text);

    try std.testing.expect(session.transport.message_count > 0);
    try std.testing.expect(!session.transport.containsMessage("unknown rule"));
}

test "LSP placeholder status diagnostics upgrade after code action search" {
    const mm0_uri = "file:///tmp/lsp-status-diag.mm0";
    const proof_uri = "file:///tmp/lsp-status-diag.auf";

    var session: Session = undefined;
    session.init();
    defer session.deinit();

    try session.open(mm0_uri, lsp_search_mm0_text);
    session.transport.clearMessages();
    try session.open(proof_uri, lsp_search_exact_proof_text);

    // An unsearched placeholder publishes a warning (severity 2).
    try std.testing.expect(
        session.transport.containsMessage("search not yet run"),
    );
    try std.testing.expect(session.transport.containsMessage("\"severity\":2"));

    // Running the search via code actions records the outcome and re-publishes
    // the placeholder diagnostic as info (severity 3) with the found proof.
    session.transport.clearMessages();
    _ = try session.codeActionsAt(proof_uri, lsp_search_exact_proof_text, "exact?");
    try std.testing.expectEqual(@as(usize, 1), session.searchOutcomes(proof_uri));
    try std.testing.expectEqual(
        mm0.CompilerSupport.Search.SearchStatus.found,
        session.searchOutcome(proof_uri),
    );
    try std.testing.expect(
        session.transport.containsMessage("exact? search succeeded: top_i"),
    );
    try std.testing.expect(session.transport.containsMessage("\"severity\":3"));
    try std.testing.expect(
        !session.transport.containsMessage("search not yet run"),
    );

    // A cache-hit code action publishes nothing new (the outcome is already
    // recorded and published).
    session.transport.clearMessages();
    _ = try session.codeActionsAt(proof_uri, lsp_search_exact_proof_text, "exact?");
    try std.testing.expectEqual(@as(usize, 0), session.transport.message_count);

    // An edit drops the recorded outcome: the placeholder returns to the
    // "not yet searched" warning.
    session.transport.clearMessages();
    try session.change(proof_uri, 2, lsp_search_exact_proof_text);
    try std.testing.expectEqual(@as(usize, 0), session.searchOutcomes(proof_uri));
    try std.testing.expect(
        session.transport.containsMessage("search not yet run"),
    );
    try std.testing.expect(
        !session.transport.containsMessage("search succeeded"),
    );
}

test "LSP placeholder status diagnostics report a search miss as error" {
    const mm0_uri = "file:///tmp/lsp-status-miss.mm0";
    const proof_uri = "file:///tmp/lsp-status-miss.auf";
    // `bot` has no proof rule, so the placeholder search runs to completion
    // without a result.
    const miss_mm0_text =
        \\provable sort wff;
        \\term top: wff;
        \\term bot: wff;
        \\axiom top_i: $ top $;
        \\theorem main: $ top $;
    ;
    const miss_proof_text =
        \\main
        \\----
        \\l1: $ bot $ by exact?
    ;

    var session: Session = undefined;
    session.init();
    defer session.deinit();

    try session.open(mm0_uri, miss_mm0_text);
    try session.open(proof_uri, miss_proof_text);

    session.transport.clearMessages();
    _ = try session.codeActionsAt(proof_uri, miss_proof_text, "exact?");
    try std.testing.expect(session.transport.containsMessage(
        "exact? search failed: no rule application closes this goal",
    ));
    // The failure detail elaborates the coverage and points at auto?.
    try std.testing.expect(session.transport.containsMessage(
        "auto? can additionally synthesize sub-proofs",
    ));
    try std.testing.expect(session.transport.containsMessage("\"severity\":1"));
    // The code is how a client running its own compile (the browser editor)
    // tells search status apart from the diagnostics it already has.
    try std.testing.expect(session.transport.containsMessage(
        "\"code\":\"search-status\"",
    ));
}

test "LSP code action offers a retry with raised limits after an auto? miss" {
    const mm0_uri = "file:///tmp/lsp-retry-miss.mm0";
    const proof_uri = "file:///tmp/lsp-retry-miss.auf";
    const proof_text =
        \\main
        \\----
        \\l1: $ bot $ by auto? (depth: 1)
    ;

    var session: Session = undefined;
    session.init();
    defer session.deinit();
    try session.handler.putDocument(mm0_uri,
        \\provable sort wff;
        \\term top: wff;
        \\term mid: wff;
        \\term bot: wff;
        \\axiom top_i: $ top $;
        \\axiom top_mid: $ top $ > $ mid $;
        \\axiom mid_bot: $ mid $ > $ bot $;
        \\theorem main: $ top $;
    , 1);
    try session.handler.putDocument(proof_uri, proof_text, 1);

    const actions = try session.codeActions(proof_uri, proof_text, "auto?");
    // The proof is two steps deep, so depth 1 cuts the search short: the
    // retry raises depth and, since a deeper search spends more, the budget
    // with it.
    const action = codeActionWithReplacement(
        actions,
        proof_uri,
        "auto? (depth: 3, budget: 6)",
    ) orelse return error.MissingRetryCodeAction;
    try std.testing.expectEqualStrings(
        "Retry with depth: 3, budget: 6",
        action.title,
    );
    const edit = codeActionSingleEdit(action, proof_uri) orelse {
        return error.ExpectedCodeActionEdit;
    };
    try expectRangeText(proof_text, edit.range, "auto? (depth: 1)");
}

test "LSP placeholder diagnostics report invalid search parameters" {
    const mm0_uri = "file:///tmp/lsp-status-params.mm0";
    const proof_uri = "file:///tmp/lsp-status-params.auf";
    const mm0_text =
        \\provable sort wff;
        \\term top: wff;
        \\axiom top_i: $ top $;
        \\theorem main: $ top $;
    ;
    // One typo'd name and one out-of-range value: each gets its own error
    // diagnostic straight from the analyze pass, no search required.
    const proof_text =
        \\main
        \\----
        \\l1: $ top $ by auto? (depht: 8, depth: 0)
    ;

    var session: Session = undefined;
    session.init();
    defer session.deinit();

    try session.open(mm0_uri, mm0_text);
    try session.open(proof_uri, proof_text);

    try std.testing.expect(session.transport.containsMessage(
        "unknown auto? parameter 'depht'",
    ));
    try std.testing.expect(session.transport.containsMessage(
        "'depth' must be between 1 and 64",
    ));
}

test "LSP placeholder diagnostics stay on bodies the check memo knows" {
    const mm0_uri = "file:///tmp/lsp-status-known.mm0";
    const proof_uri = "file:///tmp/lsp-status-known.auf";
    const mm0_text =
        \\provable sort wff;
        \\term top: wff;
        \\axiom top_i: $ top $;
        \\theorem first: $ top $;
        \\theorem second: $ top $;
        \\theorem third: $ top $;
    ;
    // After the first check the memo knows every body, two of which spell
    // a placeholder; the edit changes only `second`.
    const before =
        \\first
        \\-----
        \\l1: $ top $ by auto?
        \\
        \\second
        \\------
        \\l1: $ top $ by top_i []
        \\
        \\third
        \\-----
        \\l1: $ top $ by exact?
    ;
    const after =
        \\first
        \\-----
        \\l1: $ top $ by auto?
        \\
        \\second
        \\------
        \\l1: $ top $ by top_i [ ]
        \\
        \\third
        \\-----
        \\l1: $ top $ by exact?
    ;

    var session: Session = undefined;
    session.init();
    defer session.deinit();

    const arena = session.arena();

    try session.open(mm0_uri, mm0_text);
    try session.open(proof_uri, before);
    try std.testing.expect(session.checks().kept == 3);

    session.transport.clearMessages();
    try session.change(proof_uri, 2, after);
    const ranges = try session.transport.publishedRanges(arena, proof_uri);
    try std.testing.expectEqual(@as(usize, 2), ranges.len);
    try expectRangeText(after, ranges[0], "auto?");
    try expectRangeText(after, ranges[1], "exact?");
}

test "LSP code action uses UTF-16 ranges after non-ASCII text" {
    const mm0_uri = "file:///tmp/lsp-code-action-utf16.mm0";
    const proof_uri = "file:///tmp/lsp-code-action-utf16.auf";
    const proof_text =
        \\-- 💡
        \\main
        \\----
        \\l1: $ top $ by exact?
    ;

    var session: Session = undefined;
    session.init();
    defer session.deinit();
    try session.handler.putDocument(mm0_uri, lsp_search_mm0_text, 1);
    try session.handler.putDocument(proof_uri, proof_text, 1);

    const actions = try session.codeActions(proof_uri, proof_text, "exact?");
    const action = codeActionWithReplacement(actions, proof_uri, "top_i") orelse {
        return error.MissingUtf16CodeAction;
    };
    const edit = codeActionSingleEdit(action, proof_uri) orelse {
        return error.ExpectedCodeActionEdit;
    };
    try expectRangeText(proof_text, edit.range, "exact?");
}

test "LSP code action is absent outside search placeholders" {
    const mm0_uri = "file:///tmp/lsp-code-action-none.mm0";
    const proof_uri = "file:///tmp/lsp-code-action-none.auf";

    var session: Session = undefined;
    session.init();
    defer session.deinit();
    try putLspNavigationDocuments(&session.handler, mm0_uri, proof_uri);

    const result = try session.handler.@"textDocument/codeAction"(
        session.arena(),
        try codeActionParamsAt(proof_uri, lsp_navigation_proof_text, "top_i"),
    );
    try std.testing.expect(result == null);
}

test "LSP code action is absent for invalid search contexts" {
    const mm0_uri = "file:///tmp/lsp-code-action-invalid.mm0";
    const proof_uri = "file:///tmp/lsp-code-action-invalid.auf";
    const proof_text =
        \\main
        \\----
        \\l1: $ unknown_token $ by exact?
    ;

    var session: Session = undefined;
    session.init();
    defer session.deinit();
    try session.handler.putDocument(mm0_uri, lsp_search_mm0_text, 1);
    try session.handler.putDocument(proof_uri, proof_text, 1);

    const result = try session.handler.@"textDocument/codeAction"(
        session.arena(),
        try codeActionParamsAt(proof_uri, proof_text, "exact?"),
    );
    try std.testing.expect(result == null);
}

test "LSP code action is absent without sibling mm0" {
    const proof_uri = "file:///tmp/lsp-code-action-missing-sibling.auf";

    var session: Session = undefined;
    session.init();
    defer session.deinit();
    try session.handler.putDocument(proof_uri, lsp_search_exact_proof_text, 1);

    const result = try session.handler.@"textDocument/codeAction"(
        session.arena(),
        try codeActionParamsAt(
            proof_uri,
            lsp_search_exact_proof_text,
            "exact?",
        ),
    );
    try std.testing.expect(result == null);
}

test "LSP code action uses prior local lemma in theorem search" {
    const mm0_uri = "file:///tmp/lsp-code-action-local-theorem.mm0";
    const proof_uri = "file:///tmp/lsp-code-action-local-theorem.auf";
    const proof_text =
        \\lemma local_top: $ top $
        \\---------
        \\h1: $ top $ by top_i
        \\
        \\main
        \\----
        \\l1: $ top $ by exact?
    ;

    var session: Session = undefined;
    session.init();
    defer session.deinit();
    try session.handler.putDocument(mm0_uri, lsp_search_mm0_text, 1);
    try session.handler.putDocument(proof_uri, proof_text, 1);

    const actions = try session.codeActions(proof_uri, proof_text, "exact?");
    // Local-lemma *indexing* is a search-layer property; verify it with the
    // uncapped search API. The LSP code action caps `exact?` at one best result,
    // where the `top_i` axiom outranks the local lemma, so the capped action list
    // need not contain `local_top` — but the search must still find it.
    try expectSearchOffers(session.arena(), proof_text, "exact?", "local_top");
    const action = firstCodeAction(actions) orelse return error.ExpectedCodeAction;
    const edit = codeActionSingleEdit(action, proof_uri) orelse {
        return error.ExpectedCodeActionEdit;
    };
    try expectRangeText(proof_text, edit.range, "exact?");
}

test "LSP code action works inside local lemma blocks" {
    const mm0_uri = "file:///tmp/lsp-code-action-local-target.mm0";
    const proof_uri = "file:///tmp/lsp-code-action-local-target.auf";
    const proof_text =
        \\lemma local_top: $ top $
        \\---------
        \\h1: $ top $ by top_i
        \\
        \\lemma use_local: $ top $
        \\---------
        \\u1: $ top $ by exact?
        \\
        \\main
        \\----
        \\l1: $ top $ by top_i
    ;

    var session: Session = undefined;
    session.init();
    defer session.deinit();
    try session.handler.putDocument(mm0_uri, lsp_search_mm0_text, 1);
    try session.handler.putDocument(proof_uri, proof_text, 1);

    const actions = try session.codeActions(proof_uri, proof_text, "exact?");
    // See the prior test: local-lemma indexing is verified at the (uncapped)
    // search layer; the capped LSP action need not surface the outranked lemma.
    try expectSearchOffers(session.arena(), proof_text, "exact?", "local_top");
    const action = firstCodeAction(actions) orelse return error.ExpectedCodeAction;
    const edit = codeActionSingleEdit(action, proof_uri) orelse {
        return error.ExpectedCodeActionEdit;
    };
    try expectRangeText(proof_text, edit.range, "exact?");
}

test "LSP code action excludes future local lemmas" {
    const mm0_uri = "file:///tmp/lsp-code-action-local-future.mm0";
    const proof_uri = "file:///tmp/lsp-code-action-local-future.auf";
    const proof_text =
        \\lemma use_future: $ top $
        \\---------
        \\u1: $ top $ by exact?
        \\
        \\lemma future_top: $ top $
        \\---------
        \\f1: $ top $ by top_i
        \\
        \\main
        \\----
        \\l1: $ top $ by top_i
    ;

    var session: Session = undefined;
    session.init();
    defer session.deinit();
    try session.handler.putDocument(mm0_uri, lsp_search_mm0_text, 1);
    try session.handler.putDocument(proof_uri, proof_text, 1);

    const actions = try session.codeActions(proof_uri, proof_text, "exact?");
    try std.testing.expect(
        codeActionWithReplacement(actions, proof_uri, "future_top") == null,
    );
}

test "LSP code action uses open unsaved mm0 and proof documents" {
    const mm0_uri = "file:///tmp/lsp-code-action-unsaved.mm0";
    const proof_uri = "file:///tmp/lsp-code-action-unsaved.auf";
    const mm0_text =
        \\provable sort wff;
        \\term top: wff;
        \\axiom unsaved_i: $ top $;
        \\theorem main: $ top $;
    ;
    const proof_text =
        \\main
        \\----
        \\l1: $ top $ by exact?
    ;

    var session: Session = undefined;
    session.init();
    defer session.deinit();
    try session.handler.putDocument(mm0_uri, mm0_text, 1);
    try session.handler.putDocument(proof_uri, proof_text, 1);

    const actions = try session.codeActions(proof_uri, proof_text, "exact?");
    const action = codeActionWithReplacement(
        actions,
        proof_uri,
        "unsaved_i",
    ) orelse return error.MissingUnsavedCodeAction;
    const edit = codeActionSingleEdit(action, proof_uri) orelse {
        return error.ExpectedCodeActionEdit;
    };
    try expectRangeText(proof_text, edit.range, "exact?");
}
