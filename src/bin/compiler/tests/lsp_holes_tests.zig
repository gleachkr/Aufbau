const std = @import("std");
const lsp = @import("lsp");
const mm0 = @import("mm0");
const lsp_server = @import("../lsp.zig");
const types = lsp.types.flat;
const Handler = lsp_server.Handler;

const support = @import("./lsp_support.zig");
const Session = support.Session;
const testPosition = support.testPosition;
const expectRangeText = support.expectRangeText;
const codeActionSingleEdit = support.codeActionSingleEdit;

/// Hover `_wff` in a one-line holey proof. With `open`, the proof is
/// opened first, so the hover's snapshot takes the holes the diagnostics
/// pass collected and checks nothing again; without, the snapshot runs
/// the analysis itself.
fn expectProofHoleHover(open: bool) !void {
    const mm0_uri = "file:///tmp/lsp-hole-hover.mm0";
    const proof_uri = "file:///tmp/lsp-hole-hover.auf";
    const mm0_text =
        \\delimiter $ ( ) $;
        \\--| @hole _wff
        \\provable sort wff;
        \\term pair (a b: wff): wff;
        \\term imp (a b: wff): wff;
        \\infixr imp: $->$ prec 25;
        \\axiom select_right (a b: wff): $ pair a b $ > $ b $;
        \\theorem main (p r s: wff):
        \\  $ pair p (r -> s) $ > $ r -> s $;
    ;
    const proof_text =
        \\main
        \\----
        \\l1: $ _wff $ by select_right [#1]
    ;

    var session: Session = undefined;
    session.init();
    defer session.deinit();
    try session.handler.putDocument(mm0_uri, mm0_text, 1);
    if (open) {
        try session.open(proof_uri, proof_text);
        try std.testing.expect(session.transport.publishedNone(proof_uri));
        try std.testing.expectEqual(@as(usize, 0), session.checks().replayed);
    } else {
        try session.handler.putDocument(proof_uri, proof_text, 1);
    }
    const misses_before_hover = session.checks().run;

    const hover_result = try session.handler.@"textDocument/hover"(
        session.arena(),
        .{
            .textDocument = .{ .uri = proof_uri },
            .position = try testPosition(proof_text, "_wff"),
        },
    );
    const hover = hover_result orelse return error.ExpectedHover;
    const range = hover.range orelse return error.ExpectedHoverRange;
    try expectRangeText(proof_text, range, "_wff");

    const rendered = switch (hover.contents) {
        .markup_content => |content| content.value,
        else => return error.ExpectedMarkdownHover,
    };
    try std.testing.expect(std.mem.containsAtLeast(
        u8,
        rendered,
        1,
        "$ r -> s $",
    ));
    if (open) {
        try std.testing.expectEqual(misses_before_hover, session.checks().run);
        try std.testing.expectEqual(@as(usize, 0), session.checks().replayed);
    }
}

test "LSP proof hole hover shows the inferred expression" {
    try expectProofHoleHover(false);
}

test "LSP proof hole hover survives the diagnostics pass's check memo" {
    try expectProofHoleHover(true);
}

/// The fill-holes code action offered at `offset` of the proof text, or
/// null when there is none.
fn fillHolesAction(
    handler: *Handler,
    arena: std.mem.Allocator,
    proof_uri: []const u8,
    proof_text: []const u8,
    offset: usize,
) !?types.CodeAction {
    const position = lsp.offsets.indexToPosition(proof_text, offset, .@"utf-16");
    const result = try handler.@"textDocument/codeAction"(arena, .{
        .textDocument = .{ .uri = proof_uri },
        .range = .{ .start = position, .end = position },
        .context = .{ .diagnostics = &.{} },
    });
    const items = result orelse return null;
    for (items) |item| switch (item) {
        .code_action => |action| {
            if (std.mem.eql(u8, action.title, "Fill in the holes")) return action;
        },
        .command => {},
    };
    return null;
}

/// A proof whose line k doubles line k - 1 (`$ _w $ by dup [lk-1]`): the
/// values are linear as DAGs and exponential as text.
fn dupChainProof(allocator: std.mem.Allocator, lines: usize) ![]const u8 {
    var out: std.ArrayListUnmanaged(u8) = .empty;
    try out.appendSlice(allocator, "main\n----\nl1: $ _w $ by dup [#1]\n");
    for (2..lines + 1) |k| {
        try out.print(allocator, "l{d}: $ _w $ by dup [l{d}]\n", .{ k, k - 1 });
    }
    return out.toOwnedSlice(allocator);
}

test "LSP hover and fill stay bounded on values that double per line" {
    const mm0_uri = "file:///tmp/lsp-dup-chain.mm0";
    const proof_uri = "file:///tmp/lsp-dup-chain.auf";
    const mm0_text =
        \\delimiter $ ( ) $;
        \\--| @hole _w
        \\provable sort wff;
        \\term an (a b: wff): wff;
        \\infixl an: $/\$ prec 20;
        \\axiom dup (a: wff): $ a $ > $ a /\ a $;
        \\theorem main (p: wff): $ p $ > $ p $;
    ;

    var session: Session = undefined;
    session.init();
    defer session.deinit();
    const arena = session.arena();

    // The last value prints as 2^60 copies of `p`.
    const proof_text = try dupChainProof(arena, 60);
    try session.handler.putDocument(mm0_uri, mm0_text, 1);
    try session.open(proof_uri, proof_text);

    const hoverText = struct {
        fn at(h: *Handler, a: std.mem.Allocator, uri: []const u8, text: []const u8, needle: []const u8) ![]const u8 {
            const offset = std.mem.indexOf(u8, text, needle).? + needle.len - "_w $".len;
            const result = try h.@"textDocument/hover"(a, .{
                .textDocument = .{ .uri = uri },
                .position = lsp.offsets.indexToPosition(text, offset, .@"utf-16"),
            });
            const hover = result orelse return error.ExpectedHover;
            return switch (hover.contents) {
                .markup_content => |content| content.value,
                else => error.ExpectedMarkdownHover,
            };
        }
    }.at;

    // A short value prints whole; a long one is cut.
    const short = try hoverText(&session.handler, arena, proof_uri, proof_text, "l2: $ _w $");
    try std.testing.expect(std.mem.indexOf(u8, short, "p /\\ p /\\ (p /\\ p)") != null);
    const long = try hoverText(&session.handler, arena, proof_uri, proof_text, "l60: $ _w $");
    try std.testing.expect(std.mem.indexOf(u8, long, "…") != null);
    try std.testing.expect(long.len < 2 * mm0.PrettyPrint.Limit.default_max_len);

    // A fill must be whole, so only the short one is offered.
    const l2 = std.mem.indexOf(u8, proof_text, "l2:").?;
    try std.testing.expect((try fillHolesAction(&session.handler, arena, proof_uri, proof_text, l2)) != null);
    const l60 = std.mem.indexOf(u8, proof_text, "l60:").?;
    try std.testing.expect((try fillHolesAction(&session.handler, arena, proof_uri, proof_text, l60)) == null);
}

const FillSetup = enum {
    /// The proof is never opened, so nothing has checked it.
    closed,
    /// The proof is opened first, so the diagnostics pass has checked it
    /// and its check memo holds the blocks. The code action checks the
    /// proof again, filling its lines in, without the memo.
    open,
    /// As `open`, but the proof is opened with another text and then
    /// edited into this one, so the action must check the edit's text.
    edited,
};

/// Fill a holey line's holes from the code action.
fn expectFillHolesAction(setup: FillSetup) !void {
    const mm0_uri = "file:///tmp/lsp-fill-holes.mm0";
    const proof_uri = "file:///tmp/lsp-fill-holes.auf";
    const mm0_text =
        \\delimiter $ ( ) $;
        \\--| @hole _wff
        \\provable sort wff;
        \\term pair (a b: wff): wff;
        \\term imp (a b: wff): wff;
        \\infixr imp: $->$ prec 25;
        \\term and (a b: wff): wff;
        \\infixr and: $/\$ prec 30;
        \\axiom select_left (a b: wff): $ pair a b $ > $ a $;
        \\axiom select_right (a b: wff): $ pair a b $ > $ b $;
        \\axiom and_i (a b: wff): $ a $ > $ b $ > $ a /\ b $;
        \\theorem main (p r s: wff):
        \\  $ pair p (r -> s) $ > $ (r -> s) /\ p $;
    ;
    // No newline at the end: the last line's range ends with the text.
    const proof_text =
        \\main
        \\----
        \\l1: $ p $ by select_left [#1]
        \\l2: $ _wff $ by select_right [#1]
        \\l3: $ _wff /\ p $ by and_i [l2, l1]
    ;

    var session: Session = undefined;
    session.init();
    defer session.deinit();
    const arena = session.arena();
    try session.handler.putDocument(mm0_uri, mm0_text, 1);
    switch (setup) {
        .closed => try session.handler.putDocument(proof_uri, proof_text, 1),
        .open, .edited => {
            try session.handler.@"textDocument/didOpen"(arena, .{ .textDocument = .{
                .uri = proof_uri,
                .languageId = .{ .custom_value = "aufbau" },
                .version = 1,
                .text = if (setup == .open)
                    proof_text
                else
                    try std.mem.replaceOwned(u8, arena, proof_text, "_wff $", "p $"),
            } });
            if (setup == .edited) {
                try session.handler.@"textDocument/didChange"(arena, .{
                    .textDocument = .{ .uri = proof_uri, .version = 2 },
                    .contentChanges = &.{.{ .text_document_content_change_whole_document = .{ .text = proof_text } }},
                });
            }
            try std.testing.expect(session.transport.publishedNone(proof_uri));
        },
    }
    const misses_before_actions = session.checks().run;

    const l1 = std.mem.indexOf(u8, proof_text, "l1:").?;
    const l2 = std.mem.indexOf(u8, proof_text, "l2:").?;
    const l3 = std.mem.indexOf(u8, proof_text, "l3:").?;

    // A line without holes offers nothing.
    try std.testing.expect(
        (try fillHolesAction(&session.handler, arena, proof_uri, proof_text, l1)) == null,
    );

    const whole = (try fillHolesAction(
        &session.handler,
        arena,
        proof_uri,
        proof_text,
        l2 + 8,
    )) orelse return error.ExpectedFillAction;
    try std.testing.expectEqual(
        types.CodeActionKind.@"refactor.rewrite",
        whole.kind.?,
    );
    const whole_edit = codeActionSingleEdit(whole, proof_uri) orelse
        return error.ExpectedCodeActionEdit;
    try expectRangeText(proof_text, whole_edit.range, "$ _wff $");
    try std.testing.expectEqualStrings("$ r -> s $", whole_edit.newText);

    // The start of l3 is just past l2's newline: the fill is l3's, and the
    // looser `->` filling gets parentheses under `/\`.
    for ([_]usize{ l3, proof_text.len }) |offset| {
        const nested = (try fillHolesAction(
            &session.handler,
            arena,
            proof_uri,
            proof_text,
            offset,
        )) orelse return error.ExpectedFillAction;
        const nested_edit = codeActionSingleEdit(nested, proof_uri) orelse
            return error.ExpectedCodeActionEdit;
        try expectRangeText(proof_text, nested_edit.range, "$ _wff /\\ p $");
        try std.testing.expectEqualStrings(
            "$ (r -> s) /\\ p $",
            nested_edit.newText,
        );
    }
    if (setup != .closed) {
        try std.testing.expectEqual(misses_before_actions, session.checks().run);
    }
}

test "LSP code action fills a holey line's holes" {
    try expectFillHolesAction(.closed);
}

test "LSP fill-holes code action survives the diagnostics pass's check memo" {
    try expectFillHolesAction(.open);
}

test "LSP fill-holes code action checks the text of an edit" {
    try expectFillHolesAction(.edited);
}

/// The fill on the second line of pass_prawitz_holes, `$ _ctx ⊢ ∀ z … $`
/// by `all_elim [l1]`, where `l1` proves the unreduced substitution
/// `[x/w] ∀ y …`. With `congr`, the theory declares `all_congr` as a
/// congruence; without it, the substitution cannot be pushed under the
/// outer `∀`, so the written-out line does not check.
fn prawitzCitingLineFill(arena: std.mem.Allocator, congr: bool) !?types.CodeAction {
    const mm0_uri = "file:///tmp/lsp-fill-holes-sb.mm0";
    const proof_uri = "file:///tmp/lsp-fill-holes-sb.auf";
    const fixture_mm0 = try std.Io.Dir.cwd().readFileAlloc(std.testing.io, "tests/proof_cases/pass_prawitz_holes.mm0", arena, .unlimited);
    const proof_text = try std.Io.Dir.cwd().readFileAlloc(std.testing.io, "tests/proof_cases/pass_prawitz_holes.auf", arena, .unlimited);
    const annotated = "--| @congr\naxiom all_congr";
    if (std.mem.indexOf(u8, fixture_mm0, annotated) == null) return error.FixtureChanged;
    const mm0_text = if (congr)
        fixture_mm0
    else
        try std.mem.replaceOwned(u8, arena, fixture_mm0, annotated, "axiom all_congr");

    var session: Session = undefined;
    session.init();
    defer session.deinit();
    try session.handler.putDocument(mm0_uri, mm0_text, 1);
    try session.handler.putDocument(proof_uri, proof_text, 1);
    const l2 = std.mem.indexOf(u8, proof_text, "l2:").?;
    const l8 = std.mem.indexOf(u8, proof_text, "l8:").?;
    // A line that does not need the congruence offers its fill either way.
    _ = (try fillHolesAction(&session.handler, arena, proof_uri, proof_text, l8)) orelse
        return error.ExpectedFillAction;
    return try fillHolesAction(&session.handler, arena, proof_uri, proof_text, l2);
}

test "LSP fill-holes code action is offered only when the filled line checks" {
    var arena_state = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();
    if ((try prawitzCitingLineFill(arena, true)) == null) return error.FillMissingWithCongr;
    if ((try prawitzCitingLineFill(arena, false)) != null) return error.FillOfferedWithoutCongr;
}

test "LSP fill-holes code action keeps a definition the rule unfolds" {
    const mm0_uri = "file:///tmp/lsp-fill-holes-def.mm0";
    const proof_uri = "file:///tmp/lsp-fill-holes-def.auf";
    const mm0_text =
        \\delimiter $ ( ) $;
        \\--| @hole _wff
        \\provable sort wff;
        \\--| @vars x y z
        \\sort set;
        \\term im (a b: wff): wff;
        \\infixr im: $->$ prec 25;
        \\term mem (a b: set): wff;
        \\infixl mem: $e.$ prec 50;
        \\term R (a b: set): wff;
        \\term sep {x: set} (A: set) (p: wff x): set;
        \\def img (f B: set) {.y: set}: set = $ sep y B (R f y) $;
        \\axiom sep_in_imp {x: set} (t A: set) (p: wff x):
        \\  $ t e. A $ > $ t e. A -> t e. sep x A p $;
        \\theorem main (f B c: set): $ c e. B $ > $ c e. B -> c e. img f B $;
    ;
    const proof_text =
        \\main
        \\----
        \\l1: $ _wff -> c e. img f B $ by sep_in_imp [#1]
    ;

    var session: Session = undefined;
    session.init();
    defer session.deinit();
    const arena = session.arena();
    try session.handler.putDocument(mm0_uri, mm0_text, 1);
    try session.handler.putDocument(proof_uri, proof_text, 1);

    // The rule's conclusion has `img` unfolded; the fill keeps the line's
    // `img f B` and fills only the hole.
    const l1 = std.mem.indexOf(u8, proof_text, "l1:").?;
    const action = (try fillHolesAction(
        &session.handler,
        arena,
        proof_uri,
        proof_text,
        l1 + 8,
    )) orelse return error.ExpectedFillAction;
    const edit = codeActionSingleEdit(action, proof_uri) orelse
        return error.ExpectedCodeActionEdit;
    try std.testing.expectEqualStrings(
        "$ c e. B -> c e. img f B $",
        edit.newText,
    );
}
