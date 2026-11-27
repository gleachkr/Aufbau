const std = @import("std");
const lsp = @import("lsp");
const mm0 = @import("mm0");
const lsp_server = @import("../lsp.zig");
const protocol = @import("../lsp/protocol.zig");
const types = lsp.types.flat;
const DocumentKind = lsp_server.DocumentKind;
const DiagnosticContext = protocol.DiagnosticContext;
const locateCompilerDiagnostics = protocol.locateCompilerDiagnostics;
const compilerDiagnosticToLsp = protocol.compilerDiagnosticToLsp;
const diagnosticSeverityToLsp = protocol.diagnosticSeverityToLsp;
const pathToUri = lsp_server.pathToUri;
const uriToPath = lsp_server.uriToPath;
const siblingPathForProof = lsp_server.siblingPathForProof;
const documentKind = lsp_server.documentKind;

const support = @import("./lsp_support.zig");
const Session = support.Session;
const testPosition = support.testPosition;
const lsp_search_mm0_text = support.lsp_search_mm0_text;

test "LSP initialize advertises navigation capabilities" {
    var session: Session = undefined;
    session.init();
    defer session.deinit();

    const result = session.handler.initialize(std.testing.allocator, .{
        .capabilities = .{
            .textDocument = .{
                .documentSymbol = .{
                    .hierarchicalDocumentSymbolSupport = true,
                },
            },
        },
    });

    const hover = result.capabilities.hoverProvider orelse {
        return error.ExpectedHoverProvider;
    };
    switch (hover) {
        .bool => |enabled| try std.testing.expect(enabled),
        else => return error.ExpectedBooleanHoverProvider,
    }

    const definition = result.capabilities.definitionProvider orelse {
        return error.ExpectedDefinitionProvider;
    };
    switch (definition) {
        .bool => |enabled| try std.testing.expect(enabled),
        else => return error.ExpectedBooleanDefinitionProvider,
    }

    const implementation = result.capabilities.implementationProvider orelse {
        return error.ExpectedImplementationProvider;
    };
    switch (implementation) {
        .bool => |enabled| try std.testing.expect(enabled),
        else => return error.ExpectedBooleanImplementationProvider,
    }

    const references = result.capabilities.referencesProvider orelse {
        return error.ExpectedReferencesProvider;
    };
    switch (references) {
        .bool => |enabled| try std.testing.expect(enabled),
        else => return error.ExpectedBooleanReferencesProvider,
    }

    const completion = result.capabilities.completionProvider orelse {
        return error.ExpectedCompletionProvider;
    };
    try std.testing.expectEqual(false, completion.resolveProvider.?);
    // `?` must be declared: clients only auto-open the popup on identifier
    // characters otherwise, and several close it when a non-word character
    // lands in the token — which is every keystroke that finishes `auto?`.
    const triggers = completion.triggerCharacters orelse {
        return error.ExpectedCompletionTriggerCharacters;
    };
    try std.testing.expectEqual(@as(usize, 1), triggers.len);
    try std.testing.expectEqualStrings("?", triggers[0]);

    const code_action = result.capabilities.codeActionProvider orelse {
        return error.ExpectedCodeActionProvider;
    };
    switch (code_action) {
        .bool => |enabled| try std.testing.expect(enabled),
        else => return error.ExpectedBooleanCodeActionProvider,
    }

    const document_symbol = result.capabilities.documentSymbolProvider orelse {
        return error.ExpectedDocumentSymbolProvider;
    };
    switch (document_symbol) {
        .bool => |enabled| try std.testing.expect(enabled),
        else => return error.ExpectedBooleanDocumentSymbolProvider,
    }

    const highlight = result.capabilities.documentHighlightProvider orelse {
        return error.ExpectedDocumentHighlightProvider;
    };
    switch (highlight) {
        .bool => |enabled| try std.testing.expect(enabled),
        else => return error.ExpectedBooleanDocumentHighlightProvider,
    }

    // Without `prepareSupport` the client gets a plain flag.
    const rename = result.capabilities.renameProvider orelse {
        return error.ExpectedRenameProvider;
    };
    switch (rename) {
        .bool => |enabled| try std.testing.expect(enabled),
        else => return error.ExpectedBooleanRenameProvider,
    }
}

test "LSP initialize offers prepare-rename to clients that support it" {
    var session: Session = undefined;
    session.init();
    defer session.deinit();

    const result = session.handler.initialize(std.testing.allocator, .{
        .capabilities = .{
            .textDocument = .{ .rename = .{ .prepareSupport = true } },
        },
    });
    const rename = result.capabilities.renameProvider orelse {
        return error.ExpectedRenameProvider;
    };
    switch (rename) {
        .rename_options => |options| try std.testing.expect(options.prepareProvider.?),
        else => return error.ExpectedRenameOptions,
    }
}

test "LSP initialize omits document symbols for non-hierarchical clients" {
    var session: Session = undefined;
    session.init();
    defer session.deinit();

    const result = session.handler.initialize(std.testing.allocator, .{
        .capabilities = .{},
    });

    try std.testing.expect(result.capabilities.documentSymbolProvider == null);
}

test "LSP applies ranged edits, including reversed and past-the-end ranges" {
    const uri = "file:///tmp/lsp-ranged-edit.mm0";

    var session: Session = undefined;
    session.init();
    defer session.deinit();

    const arena = session.arena();

    try session.open(uri, "sort s;\nsort t;\n");

    const Edit = struct { start: types.Position, end: types.Position, text: []const u8, expected: []const u8 };
    const edits = [_]Edit{
        // Ordered: replace `s` with `a`.
        .{ .start = .{ .line = 0, .character = 5 }, .end = .{ .line = 0, .character = 6 }, .text = "a", .expected = "sort a;\nsort t;\n" },
        // Reversed: the same span as its reverse, the whole first line.
        .{ .start = .{ .line = 1, .character = 0 }, .end = .{ .line = 0, .character = 0 }, .text = "", .expected = "sort t;\n" },
        // Past the end: both endpoints clamp to the end of the text.
        .{ .start = .{ .line = 7, .character = 3 }, .end = .{ .line = 9, .character = 0 }, .text = "sort u;\n", .expected = "sort t;\nsort u;\n" },
    };
    for (edits, 2..) |edit, version| {
        try session.handler.@"textDocument/didChange"(arena, .{
            .textDocument = .{ .uri = uri, .version = @intCast(version) },
            .contentChanges = &.{.{ .text_document_content_change_partial = .{
                .range = .{ .start = edit.start, .end = edit.end },
                .text = edit.text,
            } }},
        });
        try std.testing.expectEqualStrings(edit.expected, session.documentText(uri));
    }
}

test "uri path roundtrip" {
    const allocator = std.testing.allocator;
    const path = "/tmp/a path/example.mm0";
    const uri = try pathToUri(allocator, path);
    defer allocator.free(uri);

    const roundtrip = try uriToPath(allocator, uri);
    defer allocator.free(roundtrip);
    try std.testing.expectEqualStrings(path, roundtrip);
}

test "uri path rejects an escaped NUL byte" {
    try std.testing.expectError(
        error.InvalidFormat,
        uriToPath(std.testing.allocator, "file:///tmp/a%00b.auf"),
    );
}

test "proof sibling path" {
    const allocator = std.testing.allocator;
    const path = try siblingPathForProof(allocator, "/tmp/demo.auf");
    defer allocator.free(path);
    try std.testing.expectEqualStrings("/tmp/demo.mm0", path);
}

test "document kind" {
    try std.testing.expectEqual(DocumentKind.mm0, documentKind("/tmp/a.mm0"));
    try std.testing.expectEqual(DocumentKind.proof, documentKind("/tmp/a.auf"));
    try std.testing.expectEqual(DocumentKind.other, documentKind("/tmp/a.txt"));
}

test "compiler diagnostic severity maps to LSP severity" {
    try std.testing.expectEqual(
        types.DiagnosticSeverity.Error,
        diagnosticSeverityToLsp(mm0.CompilerDiagnosticSeverity.@"error"),
    );
    try std.testing.expectEqual(
        types.DiagnosticSeverity.Warning,
        diagnosticSeverityToLsp(mm0.CompilerDiagnosticSeverity.warning),
    );
}

test "compiler diagnostics filter by source for LSP publishing" {
    var arena_state = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena_state.deinit();
    const allocator = arena_state.allocator();
    const diags = [_]mm0.CompilerDiagnostic{
        .{
            .severity = .warning,
            .kind = .generic,
            .err = error.AmbiguousAcuiMatch,
            .source = .proof,
        },
        .{
            .severity = .warning,
            .kind = .generic,
            .err = error.UnknownTerm,
            .source = .mm0,
        },
    };
    const diag_context: DiagnosticContext = .{
        .mm0 = .{
            .uri = "file:///tmp/test.mm0",
            .text = "",
            .version = 1,
        },
        .proof = .{
            .uri = "file:///tmp/test.auf",
            .text = "",
            .version = 1,
        },
    };
    var converter = protocol.RangeConverter{ .arena = allocator, .encoding = .@"utf-16" };
    const located = try locateCompilerDiagnostics(
        &converter,
        diag_context,
        &.{},
        &diags,
        null,
        null,
        null,
    );
    try std.testing.expectEqual(@as(usize, 2), located.len);
    try std.testing.expectEqualStrings("file:///tmp/test.auf", located[0].uri);
    try std.testing.expectEqualStrings("file:///tmp/test.mm0", located[1].uri);
    for (located) |item| {
        try std.testing.expectEqual(
            types.DiagnosticSeverity.Warning,
            item.diagnostic.severity.?,
        );
    }
}

test "compiler source diagnostics merge primaries and warnings" {
    var arena_state = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena_state.deinit();
    const allocator = arena_state.allocator();

    const primary = [_]mm0.CompilerDiagnostic{
        .{
            .kind = .generic,
            .err = error.UnknownTerm,
            .source = .mm0,
        },
    };
    const warnings = [_]mm0.CompilerDiagnostic{
        .{
            .severity = .warning,
            .kind = .generic,
            .err = error.AmbiguousAcuiMatch,
            .source = .mm0,
        },
        .{
            .severity = .warning,
            .kind = .generic,
            .err = error.UnknownLabel,
            .source = .proof,
        },
    };
    const extra: mm0.CompilerDiagnostic = .{
        .kind = .generic,
        .err = error.ExpectedIdent,
        .source = .mm0,
    };
    const diag_context: DiagnosticContext = .{
        .mm0 = .{
            .uri = "file:///tmp/test.mm0",
            .text = "",
            .version = 1,
        },
        .proof = .{
            .uri = "file:///tmp/test.auf",
            .text = "",
            .version = 1,
        },
    };

    var converter = protocol.RangeConverter{ .arena = allocator, .encoding = .@"utf-16" };
    const located = try locateCompilerDiagnostics(
        &converter,
        diag_context,
        &primary,
        &warnings,
        extra,
        null,
        null,
    );
    // Proof-side first, then `.mm0`-side: the extra diagnostic, primaries,
    // then warnings.
    try std.testing.expectEqual(@as(usize, 4), located.len);
    try std.testing.expectEqualStrings("file:///tmp/test.auf", located[0].uri);
    const expected = [_]types.DiagnosticSeverity{ .Error, .Error, .Warning };
    for (located[1..], expected) |item, severity| {
        try std.testing.expectEqualStrings("file:///tmp/test.mm0", item.uri);
        try std.testing.expectEqual(severity, item.diagnostic.severity.?);
    }
}

test "compiler source diagnostics append omitted summary" {
    var arena_state = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena_state.deinit();
    const allocator = arena_state.allocator();

    const primary = [_]mm0.CompilerDiagnostic{
        .{
            .kind = .generic,
            .err = error.UnknownTerm,
            .source = .mm0,
        },
    };
    const omitted: mm0.CompilerDiagnostic = .{
        .kind = .omitted_diagnostics,
        .err = error.DiagnosticsOmitted,
        .source = .mm0,
        .detail = .{ .omitted_diagnostics = .{ .count = 17 } },
    };
    const diag_context: DiagnosticContext = .{
        .mm0 = .{
            .uri = "file:///tmp/test.mm0",
            .text = "",
            .version = 1,
        },
    };

    var converter = protocol.RangeConverter{ .arena = allocator, .encoding = .@"utf-16" };
    const located = try locateCompilerDiagnostics(
        &converter,
        diag_context,
        &primary,
        &.{},
        null,
        null,
        omitted,
    );
    try std.testing.expectEqual(@as(usize, 2), located.len);
    try std.testing.expectEqualStrings(
        "17 more diagnostics omitted",
        located[1].diagnostic.message.string,
    );
}

test "compiler diagnostics publish related information" {
    var arena_state = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena_state.deinit();
    const allocator = arena_state.allocator();

    const mm0_text =
        \\provable sort wff;
        \\term top: wff;
        \\theorem first: $ top $;
        \\theorem second: $ top $;
    ;
    const proof_text =
        \\first
        \\-----
        \\l1: $ top $ by second []
    ;

    const rule_start = std.mem.indexOf(u8, mm0_text, "second") orelse {
        return error.MissingNeedle;
    };
    const use_start = std.mem.lastIndexOf(u8, proof_text, "second") orelse {
        return error.MissingNeedle;
    };

    var diag: mm0.CompilerDiagnostic = .{
        .kind = .rule_not_yet_available,
        .err = error.RuleNotYetAvailable,
        .source = .proof,
        .phase = .theorem_application,
        .theorem_name = "first",
        .line_label = "l1",
        .rule_name = "second",
        .span = .{
            .start = use_start,
            .end = use_start + "second".len,
        },
    };
    diag.note_count = 1;
    diag.notes[0] = .{
        .message = .rule_declared_later,
        .source = .mm0,
    };
    diag.related_count = 1;
    diag.related[0] = .{
        .label = .rule_declaration_here,
        .source = .mm0,
        .span = .{
            .start = rule_start,
            .end = rule_start + "second".len,
        },
    };

    const diag_context: DiagnosticContext = .{
        .mm0 = .{
            .uri = "file:///tmp/test.mm0",
            .text = mm0_text,
            .version = 1,
        },
        .proof = .{
            .uri = "file:///tmp/test.auf",
            .text = proof_text,
            .version = 1,
        },
    };

    var converter = protocol.RangeConverter{ .arena = allocator, .encoding = .@"utf-16" };
    const lsp_diag = try compilerDiagnosticToLsp(&converter, diag_context, diag);
    const related = lsp_diag.relatedInformation orelse {
        return error.ExpectedRelatedInformation;
    };
    try std.testing.expectEqual(@as(usize, 1), related.len);
    try std.testing.expectEqualStrings(
        "file:///tmp/test.mm0",
        related[0].location.uri,
    );
    try std.testing.expectEqualStrings(
        "rule declaration is here",
        related[0].message,
    );
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        lsp_diag.message.string,
        1,
        "phase: theorem application",
    ));
}

test "compiler dependency diagnostics render detail in LSP messages" {
    var arena_state = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena_state.deinit();
    const allocator = arena_state.allocator();

    const proof_text =
        \\rel_bad
        \\-------
        \\l1: $ rel z z $ by rel_ax (x := $ z $, y := $ z $) []
    ;

    const diag_context: DiagnosticContext = .{
        .proof = .{
            .uri = "file:///tmp/test.auf",
            .text = proof_text,
            .version = 1,
        },
    };
    var converter = protocol.RangeConverter{ .arena = allocator, .encoding = .@"utf-16" };
    const lsp_diag = try compilerDiagnosticToLsp(
        &converter,
        diag_context,
        .{
            .kind = .generic,
            .err = error.DepViolation,
            .source = .proof,
            .phase = .theorem_application,
            .theorem_name = "rel_bad",
            .line_label = "l1",
            .rule_name = "rel_ax",
            .span = .{ .start = 17, .end = 23 },
            .detail = .{ .dep_violation = .{
                .first_arg_idx = 0,
                .second_arg_idx = 1,
                .first_arg_name = "x",
                .second_arg_name = "y",
                .first_deps = 1,
                .second_deps = 1,
                .first_bound = true,
                .second_bound = true,
                .first_rule_bound = true,
                .second_rule_bound = true,
                .first_binding_text = "z",
                .second_binding_text = "z",
            } },
        },
    );

    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        lsp_diag.message.string,
        1,
        "dependency violation: bound variables x and y " ++
            "must be assigned distinct variables",
    ));
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        lsp_diag.message.string,
        1,
        "x was assigned: z",
    ));
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        lsp_diag.message.string,
        1,
        "y was assigned: z",
    ));
}

test "compiler dependency diagnostics explain one-sided violations" {
    var arena_state = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena_state.deinit();
    const allocator = arena_state.allocator();

    const proof_text =
        \\gen_bad
        \\-------
        \\l1: $ rel z z $ by gen (x := $ z $, p := $ rel z z $) []
    ;

    const diag_context: DiagnosticContext = .{
        .proof = .{
            .uri = "file:///tmp/test.auf",
            .text = proof_text,
            .version = 1,
        },
    };
    var converter = protocol.RangeConverter{ .arena = allocator, .encoding = .@"utf-16" };
    const lsp_diag = try compilerDiagnosticToLsp(
        &converter,
        diag_context,
        .{
            .kind = .generic,
            .err = error.DepViolation,
            .source = .proof,
            .phase = .theorem_application,
            .theorem_name = "gen_bad",
            .line_label = "l1",
            .rule_name = "gen",
            .span = .{ .start = 16, .end = 22 },
            .detail = .{ .dep_violation = .{
                .first_arg_idx = 0,
                .second_arg_idx = 1,
                .first_arg_name = "x",
                .second_arg_name = "p",
                .first_deps = 1,
                .second_deps = 1,
                .first_bound = true,
                .second_bound = false,
                .first_rule_bound = true,
                .second_rule_bound = false,
                .first_binding_text = "z",
                .second_binding_text = "rel z z",
            } },
        },
    );

    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        lsp_diag.message.string,
        1,
        "dependency violation: the rule does not allow p " ++
            "to mention the variable assigned to x",
    ));
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        lsp_diag.message.string,
        1,
        "x was assigned: z",
    ));
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        lsp_diag.message.string,
        1,
        "p was assigned: rel z z",
    ));
}

// Multi-file units: imports and includes resolved through the document
// store (what the browser host relies on) and through disk.

test "LSP serial host analyses a change before the next message" {
    const mm0_uri = "file:///tmp/lsp-serial-host.mm0";
    const proof_uri = "file:///tmp/lsp-serial-host.auf";
    const proof_text =
        \\main
        \\----
        \\l1: $ top $ by nope []
    ;

    var session: Session = undefined;
    session.initSerial();
    defer session.deinit();
    // The session runs no analysis itself.
    session.analyzeLater();

    try session.open(mm0_uri, lsp_search_mm0_text);
    try session.open(proof_uri, proof_text);
    try std.testing.expect(!session.handler.hasPendingAnalysis());
    try std.testing.expect(session.transport.published(proof_uri, "nope"));
}

test "LSP diagnostic on a stray non-ASCII character covers the whole character" {
    const mm0_uri = "file:///tmp/lsp-stray-unicode.mm0";
    const proof_uri = "file:///tmp/lsp-stray-unicode.auf";
    // `⊢` outside `$ … $`: the parser's error span covers its first byte
    // only, which the UTF-16 conversion must not split.
    const proof_text =
        \\main
        \\----
        \\l1: $ top $ by ⊢
    ;

    var session: Session = undefined;
    session.init();
    defer session.deinit();

    const arena = session.arena();

    try session.open(mm0_uri, lsp_search_mm0_text);
    try session.open(proof_uri, proof_text);

    const ranges = try session.transport.publishedRanges(arena, proof_uri);
    const stray = try testPosition(proof_text, "⊢");
    var covered = false;
    for (ranges) |range| {
        if (range.start.line == stray.line and range.start.character == stray.character) {
            try std.testing.expectEqual(stray.character + 1, range.end.character);
            covered = true;
        }
    }
    try std.testing.expect(covered);
}

test "LSP reports on a closed sibling mm0 that is not valid UTF-8" {
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    var session: Session = undefined;
    session.init();
    defer session.deinit();
    const arena = session.arena();

    // A Latin-1 `é` on the line of the error: read from disk, never
    // decoded by a client.
    const dir = try tmp.dir.realPathFileAlloc(std.testing.io, ".", arena);
    try tmp.dir.writeFile(std.testing.io, .{
        .sub_path = "main.mm0",
        .data = "provable sort wff;\nterm caf\xe9 (a b: wff): wff; zzz\n",
    });
    const mm0_uri = try pathToUri(arena, try std.fs.path.join(arena, &.{ dir, "main.mm0" }));
    const proof_uri = try pathToUri(arena, try std.fs.path.join(arena, &.{ dir, "main.auf" }));

    try session.open(proof_uri, "");

    const ranges = try session.transport.publishedRanges(arena, mm0_uri);
    try std.testing.expect(ranges.len > 0);
    for (ranges) |range| try std.testing.expectEqual(@as(u32, 1), range.start.line);
}
