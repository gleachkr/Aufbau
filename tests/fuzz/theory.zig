//! Fuzz target: generated theories with proofs that are valid by
//! construction.
//!
//! Mutating the proof cases keeps to the vocabulary they already use. This
//! target writes new theories instead: sorts, terms with random arities and
//! notations (infix of either associativity, prefix), definitions, and
//! axioms with hypotheses, all over random expressions. Each theorem is a
//! substitution instance of an axiom, proved in one step by that axiom,
//! with each binding written out or left to inference when the statement
//! determines it. So every generated pair must compile, verify, pass the
//! compile target's other oracles (checkPair), and pass mm0-c too when it
//! is on PATH.
const std = @import("std");
const mm0 = @import("mm0");
const harness = @import("harness.zig");
const mm0c = @import("mm0c.zig");
const checkPair = @import("compile.zig").checkPair;

const Smith = std.testing.Smith;

const max_sorts = 3;
const max_terms = 8;
const max_axioms = 6;
const max_theorems = 6;
const max_arity = 3;
const max_hyps = 2;
const max_depth = 4;

const infix_tokens = [_][]const u8{ "+", "*", "->", "&", "|", "<>", "=>", "@@" };
const prefix_tokens = [_][]const u8{ "~", "!", "-", "?" };

const Notation = union(enum) {
    none,
    infix: struct { token: []const u8, prec: u16, right: bool },
    prefix: struct { token: []const u8, prec: u16 },
};

const Term = struct {
    args: []const u8,
    ret: u8,
    notation: Notation,
    /// A definition's body, over its arguments `a0`, `a1`, …
    body: ?[]const u8,
};

/// A variable or binder: its name and sort.
const Var = struct { name: []const u8, sort: u8 };

/// An axiom's statement; theorems instantiate it.
const Axiom = struct {
    vars: []const Var,
    hyps: []const Expr,
    concl: Expr,
};

/// An expression tree; `Var` leaves name a binder.
const Expr = union(enum) {
    variable: usize,
    app: struct { term: usize, args: []const Expr },
};

const Theory = struct {
    arena: std.mem.Allocator,
    smith: *Smith,
    sorts: usize,
    terms: std.ArrayList(Term) = .empty,

    fn randomExpr(self: *Theory, sort: u8, vars: []const Var, depth: usize) !Expr {
        var candidates: std.ArrayList(usize) = .empty;
        for (vars, 0..) |v, i| if (v.sort == sort) try candidates.append(self.arena, i);
        const leaf = depth == 0 or self.smith.valueRangeAtMost(u8, 0, 2) == 0;
        if (leaf and candidates.items.len != 0 and self.smith.value(bool))
            return .{ .variable = candidates.items[self.smith.index(candidates.items.len)] };
        var apps: std.ArrayList(usize) = .empty;
        for (self.terms.items, 0..) |term, i| {
            if (term.ret != sort) continue;
            if (leaf and term.args.len != 0) continue;
            try apps.append(self.arena, i);
        }
        if (apps.items.len == 0)
            return .{ .variable = candidates.items[self.smith.index(candidates.items.len)] };
        const index = apps.items[self.smith.index(apps.items.len)];
        const term = self.terms.items[index];
        const args = try self.arena.alloc(Expr, term.args.len);
        for (args, term.args) |*arg, arg_sort| arg.* = try self.randomExpr(arg_sort, vars, depth -| 1);
        return .{ .app = .{ .term = index, .args = args } };
    }

    /// `expr` with variable i replaced by `with[i]`.
    fn substitute(self: *Theory, expr: Expr, with: []const Expr) !Expr {
        return switch (expr) {
            .variable => |i| with[i],
            .app => |app| app: {
                const args = try self.arena.alloc(Expr, app.args.len);
                for (args, app.args) |*arg, old| arg.* = try self.substitute(old, with);
                break :app .{ .app = .{ .term = app.term, .args = args } };
            },
        };
    }

    fn print(self: *Theory, w: *std.Io.Writer, expr: Expr, vars: []const Var) !void {
        switch (expr) {
            .variable => |i| try w.writeAll(vars[i].name),
            .app => |app| {
                const term = self.terms.items[app.term];
                switch (term.notation) {
                    .infix => |infix| {
                        try w.writeAll("(");
                        try self.print(w, app.args[0], vars);
                        try w.print(" {s} ", .{infix.token});
                        try self.print(w, app.args[1], vars);
                        try w.writeAll(")");
                    },
                    .prefix => |prefix| {
                        try w.print("({s} ", .{prefix.token});
                        try self.print(w, app.args[0], vars);
                        try w.writeAll(")");
                    },
                    .none => if (app.args.len == 0) {
                        try w.print("t{d}", .{app.term});
                    } else {
                        try w.print("(t{d}", .{app.term});
                        for (app.args) |arg| {
                            try w.writeAll(" ");
                            try self.print(w, arg, vars);
                        }
                        try w.writeAll(")");
                    },
                }
            },
        }
    }
};

fn uses(expr: Expr, variable: usize) bool {
    return switch (expr) {
        .variable => |i| i == variable,
        .app => |app| for (app.args) |arg| {
            if (uses(arg, variable)) break true;
        } else false,
    };
}

/// Write a generated theory and its proofs.
fn generate(arena: std.mem.Allocator, smith: *Smith, mm0_out: *std.Io.Writer, auf_out: *std.Io.Writer) !void {
    var theory: Theory = .{
        .arena = arena,
        .smith = smith,
        .sorts = smith.valueRangeAtMost(u8, 1, max_sorts),
    };
    try mm0_out.writeAll("delimiter $ ( ) $;\n");
    for (0..theory.sorts) |s| try mm0_out.print("{s}sort s{d};\n", .{ if (s == 0) "provable " else "", s });

    // A constant of every sort, so every expression can bottom out.
    for (0..theory.sorts) |s| try theory.terms.append(arena, .{ .args = &.{}, .ret = @intCast(s), .notation = .none, .body = null });
    var used_infix: [infix_tokens.len]bool = @splat(false);
    var used_prefix: [prefix_tokens.len]bool = @splat(false);
    var used_prec: std.ArrayList(u16) = .empty;
    const extra = smith.valueRangeAtMost(u8, 0, max_terms);
    for (0..extra) |_| {
        const arity = smith.valueRangeAtMost(u8, 0, max_arity);
        const args = try arena.alloc(u8, arity);
        for (args) |*arg| arg.* = smith.valueRangeAtMost(u8, 0, @intCast(theory.sorts - 1));
        const ret = smith.valueRangeAtMost(u8, 0, @intCast(theory.sorts - 1));
        var notation: Notation = .none;
        // A distinct precedence per notation keeps the declarations consistent.
        const prec = smith.valueRangeAtMost(u16, 1, 1000);
        const prec_free = std.mem.indexOfScalar(u16, used_prec.items, prec) == null;
        if (prec_free and arity == 2 and args[0] == ret and args[1] == ret and smith.value(bool)) {
            const t = smith.index(infix_tokens.len);
            if (!used_infix[t]) {
                used_infix[t] = true;
                try used_prec.append(arena, prec);
                notation = .{ .infix = .{ .token = infix_tokens[t], .prec = prec, .right = smith.value(bool) } };
            }
        } else if (prec_free and arity == 1 and args[0] == ret and smith.value(bool)) {
            const t = smith.index(prefix_tokens.len);
            if (!used_prefix[t]) {
                used_prefix[t] = true;
                try used_prec.append(arena, prec);
                notation = .{ .prefix = .{ .token = prefix_tokens[t], .prec = prec } };
            }
        }
        var body: ?[]const u8 = null;
        if (theory.terms.items.len > theory.sorts and smith.valueRangeAtMost(u8, 0, 3) == 0) {
            // A definition over the terms so far.
            const params = try arena.alloc(Var, arity);
            for (params, args, 0..) |*p, sort, i| p.* = .{ .name = try std.fmt.allocPrint(arena, "a{d}", .{i}), .sort = sort };
            const expr = try theory.randomExpr(ret, params, 2);
            var text: std.Io.Writer.Allocating = .init(arena);
            try theory.print(&text.writer, expr, params);
            body = text.written();
        }
        try theory.terms.append(arena, .{ .args = args, .ret = ret, .notation = notation, .body = body });
    }
    for (theory.terms.items, 0..) |term, i| {
        try mm0_out.print("{s} t{d}", .{ if (term.body == null) "term" else "def", i });
        for (term.args, 0..) |sort, a| try mm0_out.print(" (a{d}: s{d})", .{ a, sort });
        try mm0_out.print(": s{d}", .{term.ret});
        if (term.body) |body| try mm0_out.print(" = $ {s} $", .{body});
        try mm0_out.writeAll(";\n");
        switch (term.notation) {
            .none => {},
            .infix => |infix| try mm0_out.print("infix{s} t{d}: ${s}$ prec {d};\n", .{
                if (infix.right) "r" else "l", i, infix.token, infix.prec,
            }),
            .prefix => |prefix| try mm0_out.print("prefix t{d}: ${s}$ prec {d};\n", .{ i, prefix.token, prefix.prec }),
        }
    }

    // Axioms over their own variables.
    const axioms = try arena.alloc(Axiom, smith.valueRangeAtMost(u8, 1, max_axioms));
    for (axioms, 0..) |*axiom, i| {
        const vars = try arena.alloc(Var, smith.valueRangeAtMost(u8, 0, 4));
        for (vars, 0..) |*v, k| v.* = .{
            .name = try std.fmt.allocPrint(arena, "x{d}", .{k}),
            .sort = smith.valueRangeAtMost(u8, 0, @intCast(theory.sorts - 1)),
        };
        const hyps = try arena.alloc(Expr, smith.valueRangeAtMost(u8, 0, max_hyps));
        for (hyps) |*hyp| hyp.* = try theory.randomExpr(0, vars, max_depth);
        axiom.* = .{ .vars = vars, .hyps = hyps, .concl = try theory.randomExpr(0, vars, max_depth) };
        try mm0_out.print("axiom ax{d}", .{i});
        for (vars) |v| try mm0_out.print(" ({s}: s{d})", .{ v.name, v.sort });
        try mm0_out.writeAll(":");
        for (hyps) |hyp| {
            try mm0_out.writeAll(" $ ");
            try theory.print(mm0_out, hyp, vars);
            try mm0_out.writeAll(" $ >");
        }
        try mm0_out.writeAll(" $ ");
        try theory.print(mm0_out, axiom.concl, vars);
        try mm0_out.writeAll(" $;\n");
    }

    // Theorems: instances of an axiom over two variables of each sort.
    const theorem_vars = try arena.alloc(Var, 2 * theory.sorts);
    for (theorem_vars, 0..) |*v, k| v.* = .{ .name = try std.fmt.allocPrint(arena, "v{d}", .{k}), .sort = @intCast(k / 2) };
    for (0..smith.valueRangeAtMost(u8, 1, max_theorems)) |i| {
        const axiom_index = smith.index(axioms.len);
        const axiom = axioms[axiom_index];
        const with = try arena.alloc(Expr, axiom.vars.len);
        for (with, axiom.vars) |*e, v| e.* = try theory.randomExpr(v.sort, theorem_vars, 2);

        try mm0_out.print("theorem th{d}", .{i});
        for (theorem_vars) |v| try mm0_out.print(" ({s}: s{d})", .{ v.name, v.sort });
        for (axiom.hyps, 0..) |hyp, h| {
            try mm0_out.print(" (h{d}: $ ", .{h});
            try theory.print(mm0_out, try theory.substitute(hyp, with), theorem_vars);
            try mm0_out.writeAll(" $)");
        }
        const concl = try theory.substitute(axiom.concl, with);
        try mm0_out.writeAll(": $ ");
        try theory.print(mm0_out, concl, theorem_vars);
        try mm0_out.writeAll(" $;\n");

        try auf_out.print("th{d}\n---\n\nl1: $ ", .{i});
        try theory.print(auf_out, concl, theorem_vars);
        try auf_out.print(" $ by ax{d}", .{axiom_index});
        // Each binding is written out, or left to inference when the
        // statement pins it down.
        var first = true;
        for (axiom.vars, with, 0..) |v, e, k| {
            var pinned = uses(axiom.concl, k);
            for (axiom.hyps) |hyp| pinned = pinned or uses(hyp, k);
            if (pinned and smith.value(bool)) continue;
            try auf_out.print("{s}{s} := $ ", .{ if (first) " (" else ", ", v.name });
            try theory.print(auf_out, e, theorem_vars);
            try auf_out.writeAll(" $");
            first = false;
        }
        if (!first) try auf_out.writeAll(")");
        try auf_out.writeAll(" [");
        for (0..axiom.hyps.len) |h| try auf_out.print("{s}#{d}", .{ if (h == 0) "" else ", ", h + 1 });
        try auf_out.writeAll("]\n\n");
    }
}

fn generated(_: void, input: harness.Input) !void {
    var arena: std.heap.ArenaAllocator = .init(input.gpa);
    defer arena.deinit();
    var mm0_out: std.Io.Writer.Allocating = .init(arena.allocator());
    var auf_out: std.Io.Writer.Allocating = .init(arena.allocator());
    try generate(arena.allocator(), input.smith, &mm0_out.writer, &auf_out.writer);
    const mm0_src = mm0_out.written();
    const auf_src = auf_out.written();
    input.dump("case.mm0", mm0_src);
    input.dump("case.auf", auf_src);

    if (!try checkPair(input.gpa, "generated theory", mm0_src, auf_src))
        fail("a theory valid by construction does not compile", .{});
    if (!mm0c.present()) return;
    var compiler = mm0.Compiler.initWithProof(input.gpa, mm0_src, auf_src);
    const mmb = try compiler.compileMmb(input.gpa);
    defer input.gpa.free(mmb);
    if (try mm0c.verdict(mm0_src, mmb) == .reject) fail("mm0-c rejects the compiled theory", .{});
}

fn fail(comptime format: []const u8, args: anytype) noreturn {
    std.debug.print(format ++ "\n", args);
    @panic("theory oracle failed");
}

test "fuzz generated theories" {
    try harness.run("theory", .{}, {}, generated);
}
