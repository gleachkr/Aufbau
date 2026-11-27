const std = @import("std");
const lsp = @import("lsp");
const lsp_server = @import("../lsp.zig");
const types = lsp.types.flat;
const pathToUri = lsp_server.pathToUri;

const support = @import("./lsp_support.zig");
const Session = support.Session;
const testPosition = support.testPosition;
const testLastPosition = support.testLastPosition;
const expectRangeText = support.expectRangeText;
const expectDefinitionLocation = support.expectDefinitionLocation;
const expectImplementationLocation = support.expectImplementationLocation;
const expectDocumentSymbols = support.expectDocumentSymbols;
const lsp_import_lib_text = support.lsp_import_lib_text;
const lsp_import_main_text = support.lsp_import_main_text;
const lsp_import_proof_text = support.lsp_import_proof_text;

fn hoverMarkdown(result: lsp.ResultType("textDocument/hover")) ![]const u8 {
    const hover = result orelse return error.ExpectedHover;
    return switch (hover.contents) {
        .markup_content => |content| content.value,
        else => error.ExpectedMarkdownHover,
    };
}

test "LSP resolves imports against open documents" {
    const lib_uri = "file:///tmp/lsp-import/lib.mm0";
    const mm0_uri = "file:///tmp/lsp-import/main.mm0";
    const proof_uri = "file:///tmp/lsp-import/main.auf";

    var session: Session = undefined;
    session.init();
    defer session.deinit();
    const arena = session.arena();

    try session.handler.putDocument(lib_uri, lsp_import_lib_text, 1);
    try session.handler.putDocument(mm0_uri, lsp_import_main_text, 1);
    try session.open(proof_uri, lsp_import_proof_text);
    // The proof checks against the imported theory: a clean set for both
    // roots, nothing for the open library (it reports on itself).
    try std.testing.expect(session.transport.publishedNone(proof_uri));
    try std.testing.expect(session.transport.publishedNone(mm0_uri));
    try std.testing.expect(!session.transport.containsMessage(lib_uri));

    // Navigation crosses into the imported file.
    const rule_location = try expectDefinitionLocation(
        try session.handler.@"textDocument/definition"(arena, .{
            .textDocument = .{ .uri = proof_uri },
            .position = try testLastPosition(lsp_import_proof_text, "top_i"),
        }),
    );
    try std.testing.expectEqualStrings(lib_uri, rule_location.uri);
    try expectRangeText(lsp_import_lib_text, rule_location.range, "top_i");

    // A position in the root after the import statement maps through the
    // join: `top` in the theorem is the library's term.
    const term_location = try expectDefinitionLocation(
        try session.handler.@"textDocument/definition"(arena, .{
            .textDocument = .{ .uri = mm0_uri },
            .position = try testLastPosition(lsp_import_main_text, "top"),
        }),
    );
    try std.testing.expectEqualStrings(lib_uri, term_location.uri);
    try expectRangeText(lsp_import_lib_text, term_location.range, "top");

    const markdown = try hoverMarkdown(try session.handler.@"textDocument/hover"(arena, .{
        .textDocument = .{ .uri = proof_uri },
        .position = try testLastPosition(lsp_import_proof_text, "top_i"),
    }));
    try std.testing.expect(std.mem.containsAtLeast(u8, markdown, 1, "top_i"));

    // Inside the import statement there is nothing to hover.
    try std.testing.expect((try session.handler.@"textDocument/hover"(arena, .{
        .textDocument = .{ .uri = mm0_uri },
        .position = try testPosition(lsp_import_main_text, "lib.mm0"),
    })) == null);

    // The outline of the root lists its own declarations only.
    const symbols = try expectDocumentSymbols(
        try session.handler.@"textDocument/documentSymbol"(arena, .{
            .textDocument = .{ .uri = mm0_uri },
        }),
    );
    try std.testing.expectEqual(@as(usize, 1), symbols.len);
    try std.testing.expectEqualStrings("main", symbols[0].name);
    try expectRangeText(lsp_import_main_text, symbols[0].selectionRange, "main");
}

test "LSP re-analyses importers when an imported document changes" {
    const lib_uri = "file:///tmp/lsp-import-change/lib.mm0";
    const mm0_uri = "file:///tmp/lsp-import-change/main.mm0";
    const proof_uri = "file:///tmp/lsp-import-change/main.auf";

    var session: Session = undefined;
    session.init();
    defer session.deinit();
    const arena = session.arena();

    try session.handler.putDocument(lib_uri, lsp_import_lib_text, 1);
    try session.handler.putDocument(mm0_uri, lsp_import_main_text, 1);
    try session.open(proof_uri, lsp_import_proof_text);
    const first_hover = try session.handler.@"textDocument/hover"(arena, .{
        .textDocument = .{ .uri = proof_uri },
        .position = try testLastPosition(lsp_import_proof_text, "top_i"),
    });
    try std.testing.expect(first_hover != null);
    try std.testing.expectEqual(@as(usize, 1), session.indexedRoots());

    session.transport.clearMessages();
    try session.change(lib_uri, 2, "provable sort wff;\nterm top: wff;\n");
    // The library's own set, then the proof re-checked against it.
    try std.testing.expect(session.transport.publishedNone(lib_uri));
    try std.testing.expect(session.transport.containsMessage(proof_uri));
    try std.testing.expect(session.transport.containsMessage("top_i"));
    // The unit's index was keyed on the library too.
    try std.testing.expectEqual(@as(usize, 0), session.indexedRoots());
}

test "LSP check memo replays library blocks across roots" {
    const lib_mm0_uri = "file:///tmp/lsp-memo/lib.mm0";
    const lib_auf_uri = "file:///tmp/lsp-memo/lib.auf";
    const main_mm0_uri = "file:///tmp/lsp-memo/main.mm0";
    const main_auf_uri = "file:///tmp/lsp-memo/main.auf";
    const lib_mm0_text =
        \\-- A library.
        \\provable sort wff;
        \\term top: wff;
        \\axiom ax_top: $ top $;
        \\theorem lib_thm: $ top $;
        \\term bot: wff;
        \\prefix bot: $_|_$ prec max;
        \\-- the end
    ;
    const lib_auf_text =
        \\lib_thm
        \\---
        \\p: $ top $ by ax_top []
        \\
    ;
    const main_mm0_text =
        \\-- Each file starts with a comment of its own.
        \\import "lib.mm0";
        \\theorem main_thm: $ top $;
        \\
    ;
    const main_auf_text =
        \\main_thm
        \\---
        \\p: $ top $ by lib_thm []
        \\
    ;

    var session: Session = undefined;
    session.init();
    defer session.deinit();

    try session.handler.putDocument(lib_mm0_uri, lib_mm0_text, 1);
    try session.handler.putDocument(main_mm0_uri, main_mm0_text, 1);
    // The library root checks its own theorem: one miss, recorded.
    try session.open(lib_auf_uri, lib_auf_text);
    try std.testing.expect(session.transport.publishedNone(lib_auf_uri));
    try std.testing.expectEqual(@as(usize, 0), session.checks().replayed);
    try std.testing.expectEqual(@as(usize, 1), session.checks().run);

    // The importing root walks the library's theorem again but replays
    // it; only its own theorem is checked.
    session.transport.clearMessages();
    try session.open(main_auf_uri, main_auf_text);
    try std.testing.expect(session.transport.publishedNone(main_auf_uri));
    try std.testing.expectEqual(@as(usize, 1), session.checks().replayed);
    try std.testing.expectEqual(@as(usize, 2), session.checks().run);

    // An edit to the root's proof re-checks that block alone.
    session.transport.clearMessages();
    try session.change(main_auf_uri, 2, "main_thm\n---\np: $ top $ by lib_thm [] \n");
    try std.testing.expect(session.transport.publishedNone(main_auf_uri));
    try std.testing.expectEqual(@as(usize, 2), session.checks().replayed);
    try std.testing.expectEqual(@as(usize, 3), session.checks().run);

    // A library edit that keeps its outcome re-checks the library block
    // once, and the root's block replays.
    session.transport.clearMessages();
    try session.change(lib_auf_uri, 2, "lib_thm\n---\np: $ top $ by ax_top [] \n");
    try std.testing.expect(session.transport.publishedNone(lib_auf_uri));
    try std.testing.expect(session.transport.publishedNone(main_auf_uri));
    // Library root: 1 miss. Importing root: library block hit (same body
    // as the library's own run), root block hit.
    try std.testing.expectEqual(@as(usize, 4), session.checks().replayed);
    try std.testing.expectEqual(@as(usize, 4), session.checks().run);
}

test "LSP reports an unresolved import on its statement and keeps going" {
    const mm0_uri = "file:///tmp/lsp-import-missing/main.mm0";
    const mm0_text =
        \\provable sort wff;
        \\import "missing.mm0";
        \\term top: wff;
        \\theorem main: $ top $;
    ;

    var session: Session = undefined;
    session.init();
    defer session.deinit();
    const arena = session.arena();

    try session.open(mm0_uri, mm0_text);
    try std.testing.expect(session.transport.containsMessage(
        "unable to import 'missing.mm0': FileNotFound",
    ));

    // The root is still analysed on its own: navigation works past the
    // failed statement.
    const location = try expectDefinitionLocation(
        try session.handler.@"textDocument/definition"(arena, .{
            .textDocument = .{ .uri = mm0_uri },
            .position = try testLastPosition(mm0_text, "top"),
        }),
    );
    try std.testing.expectEqualStrings(mm0_uri, location.uri);
    try expectRangeText(mm0_text, location.range, "top");
}

test "LSP keys a root URI with dot segments like its imports" {
    // `x/../main.mm0` is `main.mm0`: importing it from itself is a cycle,
    // not a second, missing file.
    const mm0_uri = "file:///tmp/lsp-import-dots/x/../main.mm0";
    const mm0_text =
        \\provable sort wff;
        \\import "main.mm0";
        \\term top: wff;
    ;

    var session: Session = undefined;
    session.init();
    defer session.deinit();

    try session.open(mm0_uri, mm0_text);
    try std.testing.expect(session.transport.containsMessage(
        "import cycle: 'main.mm0' is already being imported",
    ));
}

test "LSP resolves imports from disk and reports on the imported file" {
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    var session: Session = undefined;
    session.init();
    defer session.deinit();
    const arena = session.arena();

    const dir = try tmp.dir.realPathFileAlloc(std.testing.io, ".", arena);
    try tmp.dir.writeFile(std.testing.io, .{
        .sub_path = "lib.mm0",
        .data = "provable sort wff;\nterm top: wff;\naxiom bad: $ nope $;\n",
    });
    const lib_path = try std.fs.path.join(arena, &.{ dir, "lib.mm0" });
    const lib_uri = try pathToUri(arena, lib_path);
    const mm0_path = try std.fs.path.join(arena, &.{ dir, "main.mm0" });
    const mm0_uri = try pathToUri(arena, mm0_path);

    try session.open(mm0_uri, lsp_import_main_text);

    // The error sits in the closed library: published on that file.
    var lib_message: ?[]const u8 = null;
    for (session.transport.messages[0..session.transport.message_count]) |message| {
        if (std.mem.containsAtLeast(u8, message, 1, lib_uri)) lib_message = message;
    }
    const message = lib_message orelse return error.ExpectedLibraryDiagnostics;
    try std.testing.expect(std.mem.containsAtLeast(u8, message, 1, "nope"));

    // Closing the root clears what it published for the library.
    session.transport.clearMessages();
    try session.close(mm0_uri);
    try std.testing.expect(session.transport.publishedNone(lib_uri));
}

test "LSP keeps a closed library's diagnostics up while its root is checked again" {
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    var session: Session = undefined;
    session.init();
    defer session.deinit();
    const arena = session.arena();

    const dir = try tmp.dir.realPathFileAlloc(std.testing.io, ".", arena);
    try tmp.dir.writeFile(std.testing.io, .{
        .sub_path = "lib.mm0",
        .data = "provable sort wff;\nterm top: wff;\naxiom bad: $ nope $;\n",
    });
    const lib_uri = try pathToUri(arena, try std.fs.path.join(arena, &.{ dir, "lib.mm0" }));
    const mm0_uri = try pathToUri(arena, try std.fs.path.join(arena, &.{ dir, "main.mm0" }));
    const proof_uri = try pathToUri(arena, try std.fs.path.join(arena, &.{ dir, "main.auf" }));

    try session.handler.putDocument(mm0_uri, lsp_import_main_text, 1);
    try session.open(proof_uri, lsp_import_proof_text);
    try std.testing.expect(session.transport.published(lib_uri, "nope"));

    session.transport.clearMessages();
    try session.change(proof_uri, 2, lsp_import_proof_text ++ "\n");
    try std.testing.expect(session.transport.published(lib_uri, "nope"));
    try std.testing.expect(!session.transport.publishedNone(lib_uri));
}

test "LSP proof hole hover shows what the analysis found past a broken statement" {
    const mm0_uri = "file:///tmp/lsp-hole-broken.mm0";
    const proof_uri = "file:///tmp/lsp-hole-broken.auf";
    const mm0_text =
        \\delimiter $ ( ) $;
        \\axiom bad (a:: $ a $;
        \\--| @hole _wff
        \\provable sort wff;
        \\term imp (a b: wff): wff;
        \\infixr imp: $->$ prec 25;
        \\axiom mp (a b: wff): $ a -> b $ > $ a $ > $ b $;
        \\theorem main (p q: wff): $ p -> q $ > $ p $ > $ q $;
    ;
    const proof_text =
        \\main
        \\----
        \\l1: $ _wff $ by mp [#1, #2]
    ;
    var session: Session = undefined;
    session.init();
    defer session.deinit();
    const arena = session.arena();
    try session.handler.putDocument(mm0_uri, mm0_text, 1);
    try session.open(proof_uri, proof_text);
    const hover = try session.handler.@"textDocument/hover"(arena, .{
        .textDocument = .{ .uri = proof_uri },
        .position = try testPosition(proof_text, "_wff"),
    });
    try std.testing.expect(std.mem.containsAtLeast(u8, try hoverMarkdown(hover), 1, "$ q $"));
}

test "LSP resolves proof includes against open library files" {
    const mm0_uri = "file:///tmp/lsp-include/main.mm0";
    const lib_uri = "file:///tmp/lsp-include/lemmas.auf";
    const proof_uri = "file:///tmp/lsp-include/main.auf";
    const lib_text =
        \\lemma lib_top: $ top $
        \\-------
        \\l1: $ top $ by top_i []
    ;
    const proof_text =
        \\include "lemmas.auf";
        \\main
        \\----
        \\l1: $ top $ by lib_top []
    ;

    var session: Session = undefined;
    session.init();
    defer session.deinit();
    const arena = session.arena();

    try session.handler.putDocument(mm0_uri, lsp_import_lib_text ++ "\ntheorem main: $ top $;\n", 1);
    // A library proof file has no theory of its own.
    try session.open(lib_uri, lib_text);
    try std.testing.expect(session.transport.containsMessage(
        "could not find sibling .mm0 file",
    ));

    session.transport.clearMessages();
    try session.open(proof_uri, proof_text);
    // The including root reports on the library: its note is cleared.
    try std.testing.expect(session.transport.publishedNone(proof_uri));
    try std.testing.expect(session.transport.publishedNone(lib_uri));

    const location = try expectDefinitionLocation(
        try session.handler.@"textDocument/definition"(arena, .{
            .textDocument = .{ .uri = proof_uri },
            .position = try testLastPosition(proof_text, "lib_top"),
        }),
    );
    try std.testing.expectEqualStrings(lib_uri, location.uri);
    try expectRangeText(lib_text, location.range, "lib_top");

    // The library navigates through the root that includes it.
    const rule_location = try expectDefinitionLocation(
        try session.handler.@"textDocument/definition"(arena, .{
            .textDocument = .{ .uri = lib_uri },
            .position = try testLastPosition(lib_text, "top_i"),
        }),
    );
    try std.testing.expectEqualStrings(mm0_uri, rule_location.uri);

    // Editing the library re-checks the root; breaking the lemma is the
    // root's problem to show.
    session.transport.clearMessages();
    try session.change(lib_uri, 2, "lemma lib_top: $ top $\n-------\nl1: $ top $ by nope []\n");
    try std.testing.expect(session.transport.containsMessage(lib_uri));
    try std.testing.expect(session.transport.containsMessage("nope"));
    // Its own analysis, which finds no theory, leaves it to the root.
    try std.testing.expect(!session.transport.containsMessage(
        "could not find sibling .mm0 file",
    ));
}

test "LSP reports a failing include in an imported theory's proof file" {
    const lib_uri = "file:///tmp/lsp-include-paired/lib.mm0";
    const lib_proof_uri = "file:///tmp/lsp-include-paired/lib.auf";
    const mm0_uri = "file:///tmp/lsp-include-paired/main.mm0";
    const proof_uri = "file:///tmp/lsp-include-paired/main.auf";
    const lib_proof_text =
        \\include "gone.auf";
        \\lib_top
        \\-------
        \\l1: $ top $ by top_i []
    ;

    var session: Session = undefined;
    session.init();
    defer session.deinit();

    try session.handler.putDocument(lib_uri, lsp_import_lib_text ++ "\ntheorem lib_top: $ top $;\n", 1);
    try session.handler.putDocument(lib_proof_uri, lib_proof_text, 1);
    try session.handler.putDocument(mm0_uri, lsp_import_main_text, 1);
    try session.open(proof_uri, lsp_import_proof_text);
    // No statement of the root leads to lib.auf: it is joined because
    // main.mm0 imports lib.mm0. The root proof file names it.
    try std.testing.expect(session.transport.published(
        proof_uri,
        "unable to load the proof file 'lib.auf': unable to include 'gone.auf': FileNotFound",
    ));
}

test "LSP reports a missing nested include" {
    const mm0_uri = "file:///tmp/lsp-include-nested/main.mm0";
    const lib_uri = "file:///tmp/lsp-include-nested/lemmas.auf";
    const proof_uri = "file:///tmp/lsp-include-nested/main.auf";
    const lib_text =
        \\include "gone.auf";
        \\lemma lib_top: $ top $
        \\-------
        \\l1: $ top $ by top_i []
    ;
    const proof_text =
        \\include "lemmas.auf";
        \\main
        \\----
        \\l1: $ top $ by lib_top []
    ;

    var session: Session = undefined;
    session.init();
    defer session.deinit();

    try session.handler.putDocument(mm0_uri, lsp_import_lib_text ++ "\ntheorem main: $ top $;\n", 1);
    try session.handler.putDocument(lib_uri, lib_text, 1);
    try session.open(proof_uri, proof_text);
    // The failing statement's file, though the degraded unit no longer
    // includes it, and the root's statement leading there both report it.
    try std.testing.expect(session.transport.published(
        lib_uri,
        "unable to include 'gone.auf': FileNotFound",
    ));
    try std.testing.expect(session.transport.published(
        proof_uri,
        "unable to include 'lemmas.auf': unable to include 'gone.auf': FileNotFound",
    ));

    // Fixing the library re-checks the root and clears both.
    session.transport.clearMessages();
    try session.change(lib_uri, 2, lib_text["include \"gone.auf\";\n".len..]);
    try std.testing.expect(session.transport.publishedNone(lib_uri));
    try std.testing.expect(session.transport.publishedNone(proof_uri));
}

/// A session.handler over a directory of files on disk.
const DiskUnit = struct {
    tmp: std.testing.TmpDir,
    session: Session,
    dir: []const u8,
    /// The seconds of the next file's mtime, so that no two are the same.
    clock: i64,

    fn init(self: *DiskUnit) !void {
        self.* = .{
            .tmp = std.testing.tmpDir(.{}),
            .session = undefined,
            .dir = undefined,
            .clock = 1_000_000,
        };
        self.session.init();
        self.dir = try self.tmp.dir.realPathFileAlloc(
            std.testing.io,
            ".",
            self.session.arena(),
        );
    }

    fn deinit(self: *DiskUnit) void {
        self.session.deinit();
        self.tmp.cleanup();
    }

    fn write(self: *DiskUnit, name: []const u8, text: []const u8) !void {
        const io = std.testing.io;
        try self.tmp.dir.writeFile(io, .{ .sub_path = name, .data = text });
        self.clock += 1;
        try self.tmp.dir.setTimestamps(io, name, .{
            .modify_timestamp = .{ .new = .fromNanoseconds(self.clock * std.time.ns_per_s) },
        });
    }

    fn remove(self: *DiskUnit, name: []const u8) !void {
        try self.tmp.dir.deleteFile(std.testing.io, name);
    }

    fn uri(self: *DiskUnit, name: []const u8) ![]const u8 {
        const arena = self.session.arena();
        return pathToUri(arena, try std.fs.path.join(arena, &.{ self.dir, name }));
    }

    fn open(self: *DiskUnit, name: []const u8, text: []const u8) !void {
        try self.session.open(try self.uri(name), text);
    }

    fn change(self: *DiskUnit, name: []const u8, version: i32, text: []const u8) !void {
        try self.session.change(try self.uri(name), version, text);
    }

    fn close(self: *DiskUnit, name: []const u8) !void {
        try self.session.close(try self.uri(name));
    }

    /// Expect the last `needle` of `name`, a document with text `text`, to be
    /// defined on line `line` of `target`.
    fn expectDefined(
        self: *DiskUnit,
        name: []const u8,
        text: []const u8,
        needle: []const u8,
        target: []const u8,
        line: u32,
    ) !void {
        const location = try expectDefinitionLocation(
            try self.definition(name, text, needle),
        );
        try std.testing.expectEqualStrings(try self.uri(target), location.uri);
        try std.testing.expectEqual(line, location.range.start.line);
    }

    fn definition(
        self: *DiskUnit,
        name: []const u8,
        text: []const u8,
        needle: []const u8,
    ) !lsp.ResultType("textDocument/definition") {
        return self.session.handler.@"textDocument/definition"(self.session.arena(), .{
            .textDocument = .{ .uri = try self.uri(name) },
            .position = try testLastPosition(text, needle),
        });
    }

    /// Where the joined theory that requests on main.mm0 read lies.
    fn joinedTheory(self: *DiskUnit) !*const u8 {
        return self.session.joinedTheory(try self.uri("main.mm0"));
    }

    /// The text of lib.mm0 that requests on `root` read.
    fn libraryText(self: *DiskUnit, root: []const u8) ![]const u8 {
        return self.session.theoryFileText(try self.uri(root), try self.uri("lib.mm0"));
    }
};

test "LSP requests see an import change on disk" {
    var unit: DiskUnit = undefined;
    try unit.init();
    defer unit.deinit();
    const main = lsp_import_main_text;
    try unit.write("lib.mm0", lsp_import_lib_text);
    try unit.open("main.mm0", main);
    try unit.expectDefined("main.mm0", main, "top", "lib.mm0", 1);

    // Requests share the joined text while nothing changes.
    const joined = try unit.joinedTheory();
    try unit.expectDefined("main.mm0", main, "top", "lib.mm0", 1);
    try std.testing.expectEqual(joined, try unit.joinedTheory());

    try unit.write("lib.mm0", "-- A comment.\n" ++ lsp_import_lib_text);
    try unit.expectDefined("main.mm0", main, "top", "lib.mm0", 2);

    // A missing import is looked for again, and the root alone is shared.
    try unit.remove("lib.mm0");
    try std.testing.expectEqual(null, try unit.definition("main.mm0", main, "top"));
    const alone = try unit.joinedTheory();
    try std.testing.expectEqual(null, try unit.definition("main.mm0", main, "top"));
    try std.testing.expectEqual(alone, try unit.joinedTheory());
    try unit.write("lib.mm0", lsp_import_lib_text);
    try unit.expectDefined("main.mm0", main, "top", "lib.mm0", 1);

    // An open document hides the file, until it is closed.
    try unit.open("lib.mm0", "-- One.\n-- Two.\n" ++ lsp_import_lib_text);
    try unit.expectDefined("main.mm0", main, "top", "lib.mm0", 3);
    try unit.change("lib.mm0", 2, "-- One.\n" ++ lsp_import_lib_text);
    try unit.expectDefined("main.mm0", main, "top", "lib.mm0", 2);
    try unit.close("lib.mm0");
    try unit.expectDefined("main.mm0", main, "top", "lib.mm0", 1);
}

test "LSP roots share the text of a file they both import" {
    var unit: DiskUnit = undefined;
    try unit.init();
    defer unit.deinit();
    const main = lsp_import_main_text;
    const other =
        \\import "lib.mm0";
        \\theorem other: $ top $;
    ;
    try unit.write("lib.mm0", lsp_import_lib_text);
    try unit.open("main.mm0", main);
    try unit.open("other.mm0", other);
    try unit.expectDefined("main.mm0", main, "top", "lib.mm0", 1);
    try unit.expectDefined("other.mm0", other, "top", "lib.mm0", 1);
    const read = try unit.libraryText("main.mm0");
    try expectSameText(read, try unit.libraryText("other.mm0"));

    // A root built again takes the text over while the file is unchanged.
    try unit.change("main.mm0", 2, "-- A comment.\n" ++ main);
    try unit.expectDefined("main.mm0", "-- A comment.\n" ++ main, "top", "lib.mm0", 1);
    try expectSameText(read, try unit.libraryText("main.mm0"));

    // A changed file is read again; the root that read it before keeps its
    // text until it is built again.
    try unit.write("lib.mm0", "-- A comment.\n" ++ lsp_import_lib_text);
    try unit.expectDefined("main.mm0", "-- A comment.\n" ++ main, "top", "lib.mm0", 2);
    const changed = try unit.libraryText("main.mm0");
    try std.testing.expect(changed.ptr != read.ptr);
    try expectSameText(read, try unit.libraryText("other.mm0"));
    try std.testing.expectEqualStrings(lsp_import_lib_text, read);
    try unit.expectDefined("other.mm0", other, "top", "lib.mm0", 2);
    try expectSameText(changed, try unit.libraryText("other.mm0"));

    // An open document's text is shared too.
    try unit.open("lib.mm0", lsp_import_lib_text);
    try unit.expectDefined("main.mm0", "-- A comment.\n" ++ main, "top", "lib.mm0", 1);
    try unit.expectDefined("other.mm0", other, "top", "lib.mm0", 1);
    const opened = try unit.libraryText("main.mm0");
    try expectSameText(opened, try unit.libraryText("other.mm0"));
}

/// `a` and `b` are the same copy of a text.
fn expectSameText(a: []const u8, b: []const u8) !void {
    try std.testing.expectEqual(a.ptr, b.ptr);
    try std.testing.expectEqual(a.len, b.len);
}

test "LSP requests see an import's proof file come and go on disk" {
    var unit: DiskUnit = undefined;
    try unit.init();
    defer unit.deinit();
    const proof =
        \\main
        \\----
        \\l1: $ top $ by lib_top []
    ;
    const lib_proof =
        \\lemma lib_top: $ top $
        \\----
        \\l1: $ top $ by top_i []
        \\
    ;
    try unit.write("lib.mm0", lsp_import_lib_text);
    try unit.write("main.mm0", lsp_import_main_text);
    try unit.open("main.auf", proof);
    try std.testing.expectEqual(null, try unit.definition("main.auf", proof, "lib_top"));
    try unit.write("lib.auf", lib_proof);
    try unit.expectDefined("main.auf", proof, "lib_top", "lib.auf", 0);
    try unit.write("lib.auf", "-- A comment.\n" ++ lib_proof);
    try unit.expectDefined("main.auf", proof, "lib_top", "lib.auf", 1);
    try unit.remove("lib.auf");
    try std.testing.expectEqual(null, try unit.definition("main.auf", proof, "lib_top"));
}

test "LSP requests see the root's proof file come and go on disk" {
    var unit: DiskUnit = undefined;
    try unit.init();
    defer unit.deinit();
    const main = lsp_import_main_text;
    try unit.write("lib.mm0", lsp_import_lib_text);
    try unit.open("main.mm0", main);
    const params: types.ImplementationParams = .{
        .textDocument = .{ .uri = try unit.uri("main.mm0") },
        .position = try testLastPosition(main, "main"),
    };
    const arena = unit.session.arena();
    const handler = &unit.session.handler;
    try std.testing.expectEqual(
        null,
        try handler.@"textDocument/implementation"(arena, params),
    );
    try unit.write("main.auf", lsp_import_proof_text);
    const location = try expectImplementationLocation(
        try handler.@"textDocument/implementation"(arena, params),
    );
    try std.testing.expectEqualStrings(try unit.uri("main.auf"), location.uri);
    try unit.remove("main.auf");
    try std.testing.expectEqual(
        null,
        try handler.@"textDocument/implementation"(arena, params),
    );
}

test "LSP requests see a file reopened that only a failed join has read" {
    var unit: DiskUnit = undefined;
    try unit.init();
    defer unit.deinit();
    const main = lsp_import_main_text;
    try unit.open("lib.mm0", "import \"gone.mm0\";\n" ++ lsp_import_lib_text);
    try unit.open("main.mm0", main);
    try std.testing.expectEqual(null, try unit.definition("main.mm0", main, "top"));
    // The same version of another text.
    try unit.close("lib.mm0");
    try unit.open("lib.mm0", lsp_import_lib_text);
    try unit.expectDefined("main.mm0", main, "top", "lib.mm0", 1);
}

test "LSP requests from a proof file spelled another way join that file" {
    var unit: DiskUnit = undefined;
    try unit.init();
    defer unit.deinit();
    const arena = unit.session.arena();
    const main = lsp_import_main_text;
    const proof = lsp_import_proof_text;
    try unit.write("lib.mm0", lsp_import_lib_text);
    try unit.write("main.mm0", main);
    // `main.auf` with an escaped `a`, which the server's own URIs never have.
    const plain = try unit.uri("main.auf");
    const spelled = try std.mem.concat(arena, u8, &.{
        plain[0 .. plain.len - "ain.auf".len], "%61in.auf",
    });
    try unit.session.open(spelled, proof);
    // The unit joined from main.mm0 has main.auf as it is on disk: absent.
    try unit.expectDefined("main.mm0", main, "top", "lib.mm0", 1);
    const location = try expectDefinitionLocation(
        try unit.session.handler.@"textDocument/definition"(arena, .{
            .textDocument = .{ .uri = spelled },
            .position = try testLastPosition(proof, "top_i"),
        }),
    );
    try std.testing.expectEqualStrings(try unit.uri("lib.mm0"), location.uri);
    try std.testing.expectEqual(@as(u32, 2), location.range.start.line);
}

test "LSP analyses the files as they are, whatever the last request read" {
    var unit: DiskUnit = undefined;
    try unit.init();
    defer unit.deinit();
    const main = lsp_import_main_text;
    const main_uri = try unit.uri("main.auf");
    const lib_uri = try unit.uri("lib.mm0");
    try unit.write("lib.mm0", lsp_import_lib_text);
    try unit.write("main.mm0", main);
    unit.session.analyzeLater();
    try unit.open("main.auf", lsp_import_proof_text);

    // The analysis reads what the request has joined.
    try unit.expectDefined("main.auf", lsp_import_proof_text, "top_i", "lib.mm0", 2);
    const joined = try unit.joinedTheory();
    try unit.session.handler.analyzePending();
    try std.testing.expect(unit.session.transport.publishedNone(main_uri));
    try std.testing.expectEqual(joined, try unit.joinedTheory());

    // But not once a file has changed since.
    unit.session.transport.clearMessages();
    try unit.change("main.auf", 2, lsp_import_proof_text ++ "\n");
    try unit.expectDefined("main.auf", lsp_import_proof_text, "top_i", "lib.mm0", 2);
    try unit.write("lib.mm0", lsp_import_lib_text ++ "\naxiom bad: $ nope $;\n");
    try unit.session.handler.analyzePending();
    try std.testing.expect(unit.session.transport.published(lib_uri, "nope"));

    // Nor what a request read for the same file opened under another URI.
    unit.session.transport.clearMessages();
    try unit.write("lib.mm0", lsp_import_lib_text);
    try unit.expectDefined("main.auf", lsp_import_proof_text, "top_i", "lib.mm0", 2);
    try unit.open("x/../main.auf", "main\n----\nl1: $ top $ by nope []\n");
    try unit.session.handler.analyzePending();
    const other_uri = try unit.uri("x/../main.auf");
    try std.testing.expect(unit.session.transport.published(other_uri, "nope"));
}
