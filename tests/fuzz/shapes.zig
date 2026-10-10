//! Fuzz target: generated inputs of a chosen shape and size.
//!
//! Small edits to real proofs never nest deeply or share heavily, so the
//! classes found by hand in #398 (unbounded recursion on deep nesting) and
//! #399/#408 (walking the expression DAG as a tree, combinatorial ACU
//! matching) need inputs built for them. Each shape takes a size from the
//! fuzzer:
//!
//! - depth: inline proofs `keep [keep [… top_i [] …]]`, math parentheses,
//!   prefix operators, a conclusion grown one rule at a time behind holes,
//!   and definitions that each apply the previous one twice;
//! - sharing: doubling chains (`dup` on whole-line holes, on holey shapes,
//!   inline, and through a definition), and an ACU context of identical
//!   members.
//!
//! Every input goes through the compile target's oracles (checkPair). Too
//! deep is fine as a diagnostic, never as a signal, and time and memory
//! must stay within the harness limits however large the size. A shape
//! that is valid by construction must also compile while it is small.
const std = @import("std");
const harness = @import("harness.zig");
const checkPair = @import("compile.zig").checkPair;

/// Sizes up to this must compile when the shape is valid.
const must_compile_below = 48;

/// The largest size. Linear costs stay well inside the time limit here,
/// even in Debug.
const max_size = 2048;

/// Known costs that would otherwise trip the time limit. ACU matching of n
/// identical members is still about n^4 in time and memory (the solution
/// dedup left over from #408, tracked in #406): 256 copies take a minute.
/// Rejecting a wrong proof of a chain of k nested definitions is about k^2,
/// one transparent search per unfolding step (#431): 512 take 1.2 s in
/// Debug.
const max_acu_copies = 48;
const max_nested_defs = 512;

const Shape = enum(u8) {
    inline_depth,
    paren_depth,
    prefix_depth,
    grown_conclusion,
    nested_defs,
    doubling,
    holey_doubling,
    inline_doubling,
    def_doubling,
    acu_copies,
};

const theory =
    \\delimiter $ ( ) $;
    \\--| @hole _w
    \\provable sort w;
    \\term top: w;
    \\term and (a b: w): w;
    \\infixl and: $/\$ prec 10;
    \\term neg (a: w): w;
    \\prefix neg: $~$ prec 20;
    \\term s (a: w): w;
    \\def dd (a b: w): w = $ a /\ b $;
    \\axiom top_i: $ top $;
    \\axiom keep (a: w): $ a $ > $ a $;
    \\axiom dup (a: w): $ a $ > $ a /\ a $;
    \\axiom dupd (a: w): $ a $ > $ dd a a $;
    \\axiom fst (a b: w): $ a /\ b $ > $ a $;
    \\axiom grow (a: w): $ a $ > $ s a $;
    \\axiom neg_i (a: w): $ a $ > $ ~ a $;
    \\
;

fn shapes(_: void, input: harness.Input) !void {
    const gpa = input.gpa;
    const smith = input.smith;
    const shape = smith.value(Shape);
    const size: usize = switch (smith.valueRangeAtMost(u8, 0, 3)) {
        0 => smith.valueRangeAtMost(u16, 1, 16),
        1 => smith.valueRangeAtMost(u16, 1, 64),
        2 => smith.valueRangeAtMost(u16, 1, 512),
        else => smith.valueRangeAtMost(u16, 1, max_size),
    };

    var mm0: std.Io.Writer.Allocating = .init(gpa);
    defer mm0.deinit();
    var auf: std.Io.Writer.Allocating = .init(gpa);
    defer auf.deinit();
    const valid = try generate(shape, size, &mm0.writer, &auf.writer);
    input.dump("case.mm0", mm0.written());
    input.dump("case.auf", auf.written());

    var name_buf: [64]u8 = undefined;
    const name = std.fmt.bufPrint(&name_buf, "{t} {d}", .{ shape, size }) catch unreachable;
    const compiled = try checkPair(gpa, name, mm0.written(), auf.written());
    if (valid and size < must_compile_below and !compiled) {
        std.debug.print("{s}: a valid input does not compile\n", .{name});
        @panic("shapes oracle failed");
    }
}

/// Write the pair for `shape` at `size`; whether it is valid.
fn generate(shape: Shape, size: usize, mm0: *std.Io.Writer, auf: *std.Io.Writer) !bool {
    if (shape == .acu_copies) return acuCopies(@min(size, max_acu_copies), mm0, auf);
    try mm0.writeAll(theory);
    switch (shape) {
        .inline_depth => {
            try mm0.writeAll("theorem thm: $ top $;\n");
            try header(auf);
            try auf.writeAll("l1: $ top $ by ");
            try auf.splatBytesAll("keep [", size);
            try auf.writeAll("top_i []");
            try auf.splatBytesAll("]", size);
            try auf.writeAll("\n");
        },
        .paren_depth => {
            try mm0.writeAll("theorem thm: $ ");
            try mm0.splatBytesAll("( ", size);
            try mm0.writeAll("top");
            try mm0.splatBytesAll(" )", size);
            try mm0.writeAll(" $;\n");
            try header(auf);
            try auf.writeAll("l1: $ ");
            try auf.splatBytesAll("(", size);
            try auf.writeAll("top");
            try auf.splatBytesAll(")", size);
            try auf.writeAll(" $ by top_i []\n");
        },
        .prefix_depth => {
            try mm0.writeAll("theorem thm: $ ");
            try mm0.splatBytesAll("~ ", size);
            try mm0.writeAll("top $;\n");
            try header(auf);
            try auf.writeAll("l0: $ top $ by top_i []\n");
            for (1..size + 1) |k| try auf.print("l{d}: $ _w $ by neg_i [l{d}]\n", .{ k, k - 1 });
        },
        .grown_conclusion => {
            try mm0.writeAll("theorem thm: $ ");
            try mm0.splatBytesAll("s (", size);
            try mm0.writeAll("top");
            try mm0.splatBytesAll(")", size);
            try mm0.writeAll(" $;\n");
            try header(auf);
            try auf.writeAll("l0: $ top $ by top_i []\n");
            for (1..size + 1) |k| try auf.print("l{d}: $ _w $ by grow [l{d}]\n", .{ k, k - 1 });
        },
        .nested_defs => {
            // d(k+1) a unfolds to dk (dk a): 2^k applications of `s`.
            const defs = @min(size, max_nested_defs);
            try mm0.writeAll("def d0 (a: w): w = $ s a $;\n");
            for (1..defs) |k| try mm0.print("def d{d} (a: w): w = $ d{d} (d{d} a) $;\n", .{ k, k - 1, k - 1 });
            try mm0.print("theorem thm: $ d{d} top $;\n", .{defs - 1});
            try header(auf);
            // Not provable this way: the checker must say so without
            // unfolding the tree.
            try auf.print("l1: $ d{d} top $ by top_i []\n", .{defs - 1});
            return false;
        },
        .doubling, .holey_doubling, .def_doubling => {
            // Line k holds a value of DAG size k and tree size 2^k; the
            // second half takes it apart again.
            try mm0.writeAll("theorem thm: $ top $;\n");
            try header(auf);
            try auf.writeAll("l0: $ top $ by top_i []\n");
            for (1..size + 1) |k| {
                const pattern = if (shape == .holey_doubling) "_w /\\ _w" else "_w";
                const rule = if (shape == .def_doubling) "dupd" else "dup";
                try auf.print("l{d}: $ {s} $ by {s} [l{d}]\n", .{ k, pattern, rule, k - 1 });
            }
            for (size + 1..2 * size) |k| try auf.print("l{d}: $ _w $ by fst [l{d}]\n", .{ k, k - 1 });
            try auf.print("l{d}: $ top $ by fst [l{d}]\n", .{ 2 * size, 2 * size - 1 });
        },
        .inline_doubling => {
            try mm0.writeAll("theorem thm: $ top $;\n");
            try header(auf);
            try auf.writeAll("l1: $ top $ by ");
            try auf.splatBytesAll("fst [", size);
            try auf.splatBytesAll("dup [", size);
            try auf.writeAll("top_i []");
            try auf.splatBytesAll("]", 2 * size);
            try auf.writeAll("\n");
        },
        .acu_copies => unreachable,
    }
    return true;
}

fn header(auf: *std.Io.Writer) !void {
    try auf.writeAll("thm\n---\n\n");
}

/// A hypothesis whose context holds `size` copies of one member, weakened
/// by a rule whose context splits in two (#408).
fn acuCopies(size: usize, mm0: *std.Io.Writer, auf: *std.Io.Writer) !bool {
    try mm0.writeAll(
        \\delimiter $ ( ) $;
        \\provable sort wff;
        \\--| @hole _c
        \\sort ctx;
        \\term ctx_eq (g h: ctx): wff;
        \\term emp: ctx;
        \\--| @acui ctx_assoc ctx_comm emp _
        \\term join (g h: ctx): ctx;
        \\infixl join: $,$ prec 5;
        \\term hyp (a: wff): ctx;
        \\coercion hyp: wff > ctx;
        \\term seq (g d: ctx): wff;
        \\infixl seq: $==>$ prec 0;
        \\term iff (a b: wff): wff;
        \\infixr iff: $<->$ prec 20;
        \\--| @relation wff iff iff_refl iff_trans iff_sym iff_mp
        \\axiom iff_refl (a: wff): $ a <-> a $;
        \\axiom iff_trans (a b c: wff): $ a <-> b $ > $ b <-> c $ > $ a <-> c $;
        \\axiom iff_sym (a b: wff): $ a <-> b $ > $ b <-> a $;
        \\axiom iff_mp (a b: wff): $ a <-> b $ > $ a $ > $ b $;
        \\--| @relation ctx ctx_eq ctx_refl ctx_trans ctx_sym _
        \\axiom ctx_refl (g: ctx): $ ctx_eq g g $;
        \\axiom ctx_trans (g h i: ctx): $ ctx_eq g h $ > $ ctx_eq h i $ > $ ctx_eq g i $;
        \\axiom ctx_sym (g h: ctx): $ ctx_eq g h $ > $ ctx_eq h g $;
        \\axiom ctx_assoc (g h i: ctx): $ ctx_eq ((g , h) , i) (g , (h , i)) $;
        \\axiom ctx_comm (g h: ctx): $ ctx_eq (g , h) (h , g) $;
        \\axiom ctx_unit (g: ctx): $ ctx_eq (emp , g) g $;
        \\--| @congr
        \\axiom join_congr (g1 g2 h1 h2: ctx):
        \\  $ ctx_eq g1 g2 $ > $ ctx_eq h1 h2 $ > $ ctx_eq (g1 , h1) (g2 , h2) $;
        \\--| @congr
        \\axiom seq_congr (g1 g2 d1 d2: ctx):
        \\  $ ctx_eq g1 g2 $ > $ ctx_eq d1 d2 $ > $ (g1 ==> d1) <-> (g2 ==> d2) $;
        \\axiom weaken (g h d: ctx): $ g , h ==> d $ > $ g ==> d $;
        \\
    );
    try mm0.writeAll("theorem thm (x u: wff) (h: $ x");
    try mm0.splatBytesAll(" , x", size - 1);
    try mm0.writeAll(" ==> u $): $ x");
    try mm0.splatBytesAll(" , x", size - 1);
    try mm0.writeAll(" ==> u $;\n");
    try header(auf);
    try auf.writeAll("l1: $ _c ==> u $ by weaken [#1]\n");
    return true;
}

test "fuzz generated shapes" {
    try harness.run("shapes", {}, shapes);
}

test "every shape generates a pair that compiles at size 2" {
    const gpa = std.testing.allocator;
    for (std.enums.values(Shape)) |shape| {
        var mm0: std.Io.Writer.Allocating = .init(gpa);
        defer mm0.deinit();
        var auf: std.Io.Writer.Allocating = .init(gpa);
        defer auf.deinit();
        const valid = try generate(shape, 2, &mm0.writer, &auf.writer);
        const compiled = try checkPair(gpa, @tagName(shape), mm0.written(), auf.written());
        if (valid != compiled) {
            std.debug.print("{t}: valid {}, compiled {}\n", .{ shape, valid, compiled });
            return error.TestUnexpectedResult;
        }
    }
}
