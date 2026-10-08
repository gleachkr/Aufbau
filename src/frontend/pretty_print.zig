const std = @import("std");
const parse = @import("../trusted/parse.zig");
const ExprMod = @import("./expr.zig");
const text_util = @import("./text_util.zig");

const Notation = parse.Notation;
const MAX_PRECEDENCE = parse.MAX_PRECEDENCE;
const APP_PRECEDENCE = parse.APP_PRECEDENCE;

/// The render functions are mutually recursive, so their error set is stated
/// explicitly rather than inferred: allocation can fail, and the internal
/// `TooLong` stops a render that has passed its `Limit`.
const Error = std.mem.Allocator.Error;
const RenderError = Error || error{TooLong};

/// Text produced within a theorem is not bounded by the source: an expression
/// a chain of lines builds by doubling has linear DAG size and exponential
/// printed size. A render stops once its output passes `max_len` bytes, so it
/// costs O(`max_len` + depth) whatever the expression.
pub const Limit = struct {
    max_len: usize = default_max_len,
    /// What a render past `max_len` returns: null (text that must be whole,
    /// e.g. to be spliced into the source) or its first `max_len` bytes
    /// followed by `…` (text that is only read).
    overflow: enum { fail, truncate },

    pub const default_max_len = 64 * 1024;
};

/// Output of a render: fails with `TooLong` once past `max_len`.
const Out = struct {
    list: std.ArrayListUnmanaged(u8) = .{},
    arena: std.mem.Allocator,
    max_len: usize,

    fn append(self: *Out, byte: u8) RenderError!void {
        try self.list.append(self.arena, byte);
        if (self.list.items.len > self.max_len) return error.TooLong;
    }

    fn appendSlice(self: *Out, bytes: []const u8) RenderError!void {
        try self.list.appendSlice(self.arena, bytes);
        if (self.list.items.len > self.max_len) return error.TooLong;
    }
};

/// Classification of one expression node, returned by a view adapter's
/// `nodeInfo`. Generic over the adapter's node-handle type so the printer can
/// serve any expression representation (the frontend interner's `ExprId`, the
/// trusted pointer-based `Expr`, a test mock, …).
pub fn NodeInfo(comptime NodeT: type) type {
    return union(enum) {
        /// A leaf already resolved to its printable name (variable, placeholder,
        /// nullary atom). Bound at `MAX_PRECEDENCE`; never parenthesized.
        atom: []const u8,
        /// A term application: `term_id` plus positional argument handles.
        app: App,
        /// The node cannot be rendered (e.g. an unnamed variable or leftover
        /// metavariable); the whole render fails and `render` returns null.
        missing,

        pub const App = struct {
            term_id: u32,
            args: []const NodeT,
        };
    };
}

/// Render `root` as parseable math text using the notation declared in the
/// `.mm0` source, with minimal parenthesization. Falls back to prefix
/// application form (`term arg (inner arg) …`) for terms without notation, and
/// elides coercions (printing their argument transparently).
///
/// `notation` is a notation provider exposing `notationForTerm(term_id)
/// ?parse.Notation` and `isCoercionTerm(term_id) bool` (the trusted
/// `MM0Parser` satisfies this). `view` is an adapter exposing `pub const Node`,
/// `nodeInfo(node) NodeInfo(Node)`, and `termName(term_id) ?[]const u8`. When
/// the adapter lives in another file, those methods must be `pub`.
///
/// Returns null when any subnode is unrenderable, matching the caller's
/// existing "render or give up cleanly" contract.
pub fn render(
    arena: std.mem.Allocator,
    notation: anytype,
    view: anytype,
    root: @TypeOf(view).Node,
    limit: Limit,
) Error!?[]const u8 {
    var out: Out = .{ .arena = arena, .max_len = limit.max_len };
    errdefer out.list.deinit(arena);
    const rendered = renderNode(&out, notation, view, root, 0) catch |err| switch (err) {
        error.OutOfMemory => return error.OutOfMemory,
        error.TooLong => switch (limit.overflow) {
            .fail => {
                out.list.deinit(arena);
                return null;
            },
            .truncate => {
                const keep = text_util.truncateUtf8(out.list.items, limit.max_len);
                out.list.shrinkRetainingCapacity(keep.len);
                try out.list.appendSlice(arena, "…");
                return try out.list.toOwnedSlice(arena);
            },
        },
    };
    if (!rendered) {
        out.list.deinit(arena);
        return null;
    }
    return try out.list.toOwnedSlice(arena);
}

/// Render `node` in a context that accepts subexpressions of precedence
/// `min_prec` or higher; a node binding looser than `min_prec` is wrapped in
/// parentheses. This mirrors the parser's precedence climbing exactly, so the
/// output re-parses to the same expression with the fewest parentheses.
fn renderNode(
    out: *Out,
    notation: anytype,
    view: anytype,
    node: @TypeOf(view).Node,
    min_prec: u16,
) RenderError!bool {
    ExprMod.work_ticks_walk +%= 1;
    switch (view.nodeInfo(node)) {
        .missing => return false,
        .atom => |name| {
            try out.appendSlice(name);
            return true;
        },
        .app => |app| {
            // Coercions are inserted implicitly and never written in source, so
            // print the argument transparently at the same precedence.
            if (app.args.len == 1 and notation.isCoercionTerm(app.term_id)) {
                return renderNode(out, notation, view, app.args[0], min_prec);
            }
            if (notation.notationForTerm(app.term_id)) |notn| switch (notn) {
                .infix => |ix| {
                    if (app.args.len == 2) {
                        return renderInfix(out, notation, view, ix, app.args, min_prec);
                    }
                },
                .prefix => |px| {
                    return renderPrefix(out, notation, view, px, app.args, min_prec);
                },
            };
            return renderFallback(out, notation, view, app.term_id, app.args, min_prec);
        },
    }
}

fn renderInfix(
    out: *Out,
    notation: anytype,
    view: anytype,
    ix: anytype,
    args: []const @TypeOf(view).Node,
    min_prec: u16,
) RenderError!bool {
    // Left-associative: the right operand must bind tighter (prec + 1); the left
    // operand may share the operator's precedence. Right-associative is the
    // mirror. (parse.zig parses the rhs at `prec` / `prec + 1` accordingly.)
    const left_prec = if (ix.right_assoc) ix.prec + 1 else ix.prec;
    const right_prec = if (ix.right_assoc) ix.prec else ix.prec + 1;
    const wrap = ix.prec < min_prec;
    if (wrap) try out.append('(');
    if (!try renderNode(out, notation, view, args[0], left_prec)) return false;
    try out.append(' ');
    try out.appendSlice(ix.token);
    try out.append(' ');
    if (!try renderNode(out, notation, view, args[1], right_prec)) return false;
    if (wrap) try out.append(')');
    return true;
}

fn renderPrefix(
    out: *Out,
    notation: anytype,
    view: anytype,
    px: anytype,
    args: []const @TypeOf(view).Node,
    min_prec: u16,
) RenderError!bool {
    const wrap = px.prec < min_prec;
    if (wrap) try out.append('(');
    try out.appendSlice(px.token);
    for (px.lits) |lit| {
        try out.append(' ');
        switch (lit) {
            .constant => |tok| try out.appendSlice(tok),
            .variable => |v| {
                if (v.arg_index >= args.len) return false;
                if (!try renderNode(
                    out,
                    notation,
                    view,
                    args[v.arg_index],
                    v.prec,
                )) return false;
            },
        }
    }
    if (wrap) try out.append(')');
    return true;
}

fn renderFallback(
    out: *Out,
    notation: anytype,
    view: anytype,
    term_id: u32,
    args: []const @TypeOf(view).Node,
    min_prec: u16,
) RenderError!bool {
    const name = view.termName(term_id) orelse return false;
    if (args.len == 0) {
        // Nullary atom: bound at MAX_PRECEDENCE, never parenthesized.
        try out.appendSlice(name);
        return true;
    }
    const wrap = APP_PRECEDENCE < min_prec;
    if (wrap) try out.append('(');
    try out.appendSlice(name);
    for (args) |arg| {
        try out.append(' ');
        // Application arguments are parsed at MAX_PRECEDENCE, so any compound
        // argument is parenthesized while atoms are left bare.
        if (!try renderNode(out, notation, view, arg, MAX_PRECEDENCE)) return false;
    }
    if (wrap) try out.append(')');
    return true;
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

const testing = std.testing;

/// A tiny hand-built expression tree for exercising the printer's notation and
/// parenthesization logic in isolation (no parser required).
const MockNode = union(enum) {
    atom: []const u8,
    missing,
    app: struct { term_id: u32, args: []const u32 },
};

const MockView = struct {
    nodes: []const MockNode,
    term_names: []const []const u8,

    pub const Node = u32;

    fn nodeInfo(self: MockView, node: u32) NodeInfo(u32) {
        return switch (self.nodes[node]) {
            .atom => |name| .{ .atom = name },
            .missing => .missing,
            .app => |app| .{ .app = .{ .term_id = app.term_id, .args = app.args } },
        };
    }

    fn termName(self: MockView, term_id: u32) ?[]const u8 {
        if (term_id >= self.term_names.len) return null;
        return self.term_names[term_id];
    }
};

const MockNotation = struct {
    entries: []const ?Notation,
    coercions: []const u32 = &.{},

    fn notationForTerm(self: MockNotation, term_id: u32) ?Notation {
        if (term_id >= self.entries.len) return null;
        return self.entries[term_id];
    }

    fn isCoercionTerm(self: MockNotation, term_id: u32) bool {
        for (self.coercions) |c| if (c == term_id) return true;
        return false;
    }
};

fn expectRender(
    expected: []const u8,
    notation: MockNotation,
    view: MockView,
    root: u32,
) !void {
    const out = try render(testing.allocator, notation, view, root, .{ .overflow = .fail });
    defer if (out) |o| testing.allocator.free(o);
    try testing.expect(out != null);
    try testing.expectEqualStrings(expected, out.?);
}

test "fallback prefix application matches legacy form" {
    // and(or(a, b), c) with no notation -> "and (or a b) c"
    const view = MockView{
        .nodes = &.{
            .{ .atom = "a" }, // 0
            .{ .atom = "b" }, // 1
            .{ .atom = "c" }, // 2
            .{ .app = .{ .term_id = 1, .args = &.{ 0, 1 } } }, // 3: or a b
            .{ .app = .{ .term_id = 0, .args = &.{ 3, 2 } } }, // 4: and (or a b) c
        },
        .term_names = &.{ "and", "or" },
    };
    const notation = MockNotation{ .entries = &.{ null, null } };
    try expectRender("and (or a b) c", notation, view, 4);
}

test "infix left-associative omits redundant left parens" {
    // +(+(a, b), c) with infixl "+" prec 64 -> "a + b + c"
    const view = MockView{
        .nodes = &.{
            .{ .atom = "a" }, // 0
            .{ .atom = "b" }, // 1
            .{ .atom = "c" }, // 2
            .{ .app = .{ .term_id = 0, .args = &.{ 0, 1 } } }, // 3
            .{ .app = .{ .term_id = 0, .args = &.{ 3, 2 } } }, // 4
        },
        .term_names = &.{"add"},
    };
    const notation = MockNotation{ .entries = &.{
        .{ .infix = .{ .token = "+", .prec = 64, .right_assoc = false } },
    } };
    try expectRender("a + b + c", notation, view, 4);
}

test "infix left-associative parenthesizes right nesting" {
    // +(a, +(b, c)) with infixl -> "a + (b + c)"
    const view = MockView{
        .nodes = &.{
            .{ .atom = "a" }, // 0
            .{ .atom = "b" }, // 1
            .{ .atom = "c" }, // 2
            .{ .app = .{ .term_id = 0, .args = &.{ 1, 2 } } }, // 3
            .{ .app = .{ .term_id = 0, .args = &.{ 0, 3 } } }, // 4
        },
        .term_names = &.{"add"},
    };
    const notation = MockNotation{ .entries = &.{
        .{ .infix = .{ .token = "+", .prec = 64, .right_assoc = false } },
    } };
    try expectRender("a + (b + c)", notation, view, 4);
}

test "infix right-associative omits redundant right parens" {
    // ->(a, ->(b, c)) with infixr "->" prec 25 -> "a -> b -> c"
    const view = MockView{
        .nodes = &.{
            .{ .atom = "a" }, // 0
            .{ .atom = "b" }, // 1
            .{ .atom = "c" }, // 2
            .{ .app = .{ .term_id = 0, .args = &.{ 1, 2 } } }, // 3
            .{ .app = .{ .term_id = 0, .args = &.{ 0, 3 } } }, // 4
        },
        .term_names = &.{"imp"},
    };
    const notation = MockNotation{ .entries = &.{
        .{ .infix = .{ .token = "->", .prec = 25, .right_assoc = true } },
    } };
    try expectRender("a -> b -> c", notation, view, 4);
}

test "infix right-associative parenthesizes left nesting" {
    // ->(->(a, b), c) with infixr -> "(a -> b) -> c"
    const view = MockView{
        .nodes = &.{
            .{ .atom = "a" }, // 0
            .{ .atom = "b" }, // 1
            .{ .atom = "c" }, // 2
            .{ .app = .{ .term_id = 0, .args = &.{ 0, 1 } } }, // 3
            .{ .app = .{ .term_id = 0, .args = &.{ 3, 2 } } }, // 4
        },
        .term_names = &.{"imp"},
    };
    const notation = MockNotation{ .entries = &.{
        .{ .infix = .{ .token = "->", .prec = 25, .right_assoc = true } },
    } };
    try expectRender("(a -> b) -> c", notation, view, 4);
}

test "mixed precedence: lower-prec operand under higher-prec operator" {
    // *(a, +(b, c)) with * prec 70, + prec 64 -> "a * (b + c)"
    const view = MockView{
        .nodes = &.{
            .{ .atom = "a" }, // 0
            .{ .atom = "b" }, // 1
            .{ .atom = "c" }, // 2
            .{ .app = .{ .term_id = 1, .args = &.{ 1, 2 } } }, // 3: b + c
            .{ .app = .{ .term_id = 0, .args = &.{ 0, 3 } } }, // 4: a * (b + c)
        },
        .term_names = &.{ "mul", "add" },
    };
    const notation = MockNotation{ .entries = &.{
        .{ .infix = .{ .token = "*", .prec = 70, .right_assoc = false } },
        .{ .infix = .{ .token = "+", .prec = 64, .right_assoc = false } },
    } };
    try expectRender("a * (b + c)", notation, view, 4);
}

test "prefix notation renders leading token then operands" {
    // neg(a) with prefix "~" prec 40 -> "~ a"
    const lits = [_]parse.PrefixLit{
        .{ .variable = .{ .arg_index = 0, .prec = 40 } },
    };
    const view = MockView{
        .nodes = &.{
            .{ .atom = "a" }, // 0
            .{ .app = .{ .term_id = 0, .args = &.{0} } }, // 1
        },
        .term_names = &.{"neg"},
    };
    const notation = MockNotation{ .entries = &.{
        .{ .prefix = .{ .token = "~", .prec = 40, .lits = &lits } },
    } };
    try expectRender("~ a", notation, view, 1);
}

test "prefix notation operand wraps a looser infix" {
    // neg(+(a, b)): the prefix lit demands its operand bind at prec >= 65, and
    // the inner "+" binds at 64 (< 65), so it must be parenthesized -> "~ (a + b)".
    const lits = [_]parse.PrefixLit{
        .{ .variable = .{ .arg_index = 0, .prec = 65 } },
    };
    const view = MockView{
        .nodes = &.{
            .{ .atom = "a" }, // 0
            .{ .atom = "b" }, // 1
            .{ .app = .{ .term_id = 1, .args = &.{ 0, 1 } } }, // 2: a + b
            .{ .app = .{ .term_id = 0, .args = &.{2} } }, // 3: neg(a + b)
        },
        .term_names = &.{ "neg", "add" },
    };
    const notation = MockNotation{ .entries = &.{
        .{ .prefix = .{ .token = "~", .prec = 40, .lits = &lits } },
        .{ .infix = .{ .token = "+", .prec = 64, .right_assoc = false } },
    } };
    try expectRender("~ (a + b)", notation, view, 3);
}

test "coercion application is elided" {
    // coe(a) where term 0 is a coercion -> "a"
    const view = MockView{
        .nodes = &.{
            .{ .atom = "a" }, // 0
            .{ .app = .{ .term_id = 0, .args = &.{0} } }, // 1: coe a
        },
        .term_names = &.{"coe"},
    };
    const notation = MockNotation{ .entries = &.{null}, .coercions = &.{0} };
    try expectRender("a", notation, view, 1);
}

test "coercion under infix prints transparently" {
    // +(coe(a), b) -> "a + b"
    const view = MockView{
        .nodes = &.{
            .{ .atom = "a" }, // 0
            .{ .atom = "b" }, // 1
            .{ .app = .{ .term_id = 1, .args = &.{0} } }, // 2: coe a
            .{ .app = .{ .term_id = 0, .args = &.{ 2, 1 } } }, // 3: (coe a) + b
        },
        .term_names = &.{ "add", "coe" },
    };
    const notation = MockNotation{
        .entries = &.{
            .{ .infix = .{ .token = "+", .prec = 64, .right_assoc = false } },
            null,
        },
        .coercions = &.{1},
    };
    try expectRender("a + b", notation, view, 3);
}

test "missing subnode makes the whole render fail" {
    const view = MockView{
        .nodes = &.{
            .{ .atom = "a" }, // 0
            .missing, // 1
            .{ .app = .{ .term_id = 0, .args = &.{ 0, 1 } } }, // 2
        },
        .term_names = &.{"add"},
    };
    const notation = MockNotation{ .entries = &.{
        .{ .infix = .{ .token = "+", .prec = 64, .right_assoc = false } },
    } };
    const out = try render(testing.allocator, notation, view, 2, .{ .overflow = .fail });
    defer if (out) |o| testing.allocator.free(o);
    try testing.expect(out == null);
}

test "a render stops at its limit on a doubling DAG" {
    // Node k + 1 is `k ∧ k`: 41 nodes, 2^40 leaves when printed.
    var nodes: [41]MockNode = undefined;
    var args: [40][2]u32 = undefined;
    nodes[0] = .{ .atom = "p" };
    for (0..40) |k| {
        args[k] = .{ @intCast(k), @intCast(k) };
        nodes[k + 1] = .{ .app = .{ .term_id = 0, .args = &args[k] } };
    }
    const view = MockView{ .nodes = &nodes, .term_names = &.{"an"} };
    const notation = MockNotation{ .entries = &.{
        .{ .infix = .{ .token = "∧", .prec = 20, .right_assoc = false } },
    } };

    const failed = try render(testing.allocator, notation, view, 40, .{ .max_len = 100, .overflow = .fail });
    try testing.expect(failed == null);

    const cut = (try render(testing.allocator, notation, view, 40, .{ .max_len = 100, .overflow = .truncate })).?;
    defer testing.allocator.free(cut);
    try testing.expect(std.mem.endsWith(u8, cut, "…"));
    try testing.expect(std.unicode.utf8ValidateSlice(cut));
    try testing.expect(cut.len <= 100 + "…".len);
    try testing.expect(std.mem.startsWith(u8, cut, "p ∧ p ∧ (p ∧ p)"));
}

test "atom renders without parens at top level" {
    const view = MockView{
        .nodes = &.{.{ .atom = "x" }},
        .term_names = &.{},
    };
    const notation = MockNotation{ .entries = &.{} };
    try expectRender("x", notation, view, 0);
}

test "parser reverse index keeps last-declared notation and records coercions" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const src =
        \\sort wff;
        \\sort nat;
        \\term imp (a b: wff): wff;
        \\infixr imp: $->$ prec 25;
        \\term tonat (a: wff): nat;
        \\coercion tonat: wff > nat;
        \\term wb (a b: wff): wff;
        \\infixl wb: $<+>$ prec 30;
        \\infixl wb: $<*>$ prec 40;
    ;
    var parser = parse.MM0Parser.init(src, arena.allocator());
    while (try parser.next()) |_| {}

    const imp_id = parser.term_names.get("imp").?;
    const imp_notn = parser.notationForTerm(imp_id).?;
    try testing.expect(imp_notn == .infix);
    try testing.expectEqualStrings("->", imp_notn.infix.token);
    try testing.expectEqual(@as(u16, 25), imp_notn.infix.prec);
    try testing.expect(imp_notn.infix.right_assoc);

    const tonat_id = parser.term_names.get("tonat").?;
    try testing.expect(parser.isCoercionTerm(tonat_id));
    try testing.expect(!parser.isCoercionTerm(imp_id));

    // wb has two notations; the last one declared wins.
    const wb_id = parser.term_names.get("wb").?;
    const wb_notn = parser.notationForTerm(wb_id).?;
    try testing.expect(wb_notn == .infix);
    try testing.expectEqualStrings("<*>", wb_notn.infix.token);
    try testing.expectEqual(@as(u16, 40), wb_notn.infix.prec);
}

test "non-lexable notation token is skipped in favor of an earlier lexable one" {
    // `/` is a delimiter, so the ASCII alt token `\/` cannot lex back as a
    // single token; the printer must keep the lexable unicode `∨`.
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const src =
        \\delimiter $ ( ) { } [ / ] , | $;
        \\provable sort wff;
        \\term or (a b: wff): wff;
        \\infixr or: $∨$ prec 28;
        \\infixr or: $\/$ prec 28;
    ;
    var parser = parse.MM0Parser.init(src, arena.allocator());
    while (try parser.next()) |_| {}

    const or_id = parser.term_names.get("or").?;
    const notn = parser.notationForTerm(or_id).?;
    try testing.expect(notn == .infix);
    try testing.expectEqualStrings("∨", notn.infix.token);
}
