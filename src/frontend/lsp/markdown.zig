const std = @import("std");
const parse = @import("../parse_recovery.zig");
const proof_script = @import("../proof_script.zig");
const source = @import("source.zig");
const Types = @import("types.zig");

const BinderDecl = Types.BinderDecl;
const Declaration = Types.Declaration;
const DeclarationKind = Types.DeclarationKind;
const findStatementByte = source.findStatementByte;
const nextMathStringIn = source.nextMathStringIn;
const trimMathWhitespace = source.trimMathWhitespace;

pub fn inferredHoleMarkdown(
    allocator: std.mem.Allocator,
    expression: []const u8,
) ![]const u8 {
    return try std.fmt.allocPrint(
        allocator,
        "Inferred expression:\n\n```mm0\n$ {s} $\n```",
        .{expression},
    );
}

pub fn sortMarkdown(
    allocator: std.mem.Allocator,
    sort: parse.SortStmt,
    annotations: []const []const u8,
) ![]const u8 {
    var buf = std.ArrayListUnmanaged(u8){};
    var writer = buf.writer(allocator);
    try writer.print("Sort `{s}`.\n\n", .{sort.name});
    try writer.writeAll("```mm0\n");
    try writeAnnotationLines(&writer, annotations);
    try writeSortModifiers(&writer, sort.modifiers);
    try writer.print("sort {s};\n```", .{sort.name});
    try writeDocComment(&writer, annotations);
    return try buf.toOwnedSlice(allocator);
}

pub fn termMarkdown(
    allocator: std.mem.Allocator,
    text: []const u8,
    term: parse.TermStmt,
    annotations: []const []const u8,
) ![]const u8 {
    var buf = std.ArrayListUnmanaged(u8){};
    var writer = buf.writer(allocator);
    try writer.print("{s} `{s}`, returns `{s}`.\n\n", .{
        if (term.is_def) "Definition" else "Term",
        term.name,
        term.ret_sort_name,
    });
    try writer.writeAll("```mm0\n");
    try writeAnnotationLines(&writer, annotations);
    try writer.print("{s} {s}", .{
        if (term.is_def) "def" else "term",
        term.name,
    });
    try writeCompactArgList(&writer, term.arg_names, term.args);
    try writer.print(": {s}", .{term.ret_sort_name});
    try writeDeps(&writer, term.ret_deps, term.arg_names, term.args, term.args.len);
    if (term.is_def) {
        if (definitionBodySource(text, term.name_span)) |body| {
            try writer.writeAll(" =\n");
            try writeMathLine(&writer, "  ", body);
        } else {
            try writer.writeAll(" = …");
        }
    }
    try writer.writeAll(";\n```");
    try writeDocComment(&writer, annotations);
    return try buf.toOwnedSlice(allocator);
}

pub fn assertionMarkdown(
    allocator: std.mem.Allocator,
    text: []const u8,
    assertion: parse.AssertionStmt,
    concl_sort_name: ?[]const u8,
    annotations: []const []const u8,
) ![]const u8 {
    var buf = std.ArrayListUnmanaged(u8){};
    var writer = buf.writer(allocator);
    const kind: DeclarationKind = switch (assertion.kind) {
        .axiom => .axiom,
        .theorem => .theorem,
    };
    try writer.print("{s} `{s}`: {d} {s}", .{
        declarationTitle(kind),
        assertion.name,
        assertion.hyps.len,
        if (assertion.hyps.len == 1) "hypothesis" else "hypotheses",
    });
    if (concl_sort_name) |sort_name| {
        try writer.print(", conclusion sort `{s}`", .{sort_name});
    }
    try writer.writeAll(".");
    if (assertion.is_local) try writer.writeAll(" Local assertion.");
    try writer.writeAll("\n\n```mm0\n");
    try writeAnnotationLines(&writer, annotations);
    try writer.print("{s} {s}", .{ kind.label(), assertion.name });
    try writeCompactArgList(&writer, assertion.arg_names, assertion.args);
    try writer.writeAll(":\n");

    const math_strings = try source.mathStringsBeforeByteInContainingStatement(
        allocator,
        text,
        assertion.name_span.start,
        assertion.name_span.end,
        '=',
    );
    defer allocator.free(math_strings);
    const expected = assertion.hyps.len + 1;
    if (math_strings.len >= expected) {
        for (math_strings[0..assertion.hyps.len]) |hyp| {
            try writeMathLine(&writer, "  ", hyp.text);
            try writer.writeAll(" >\n");
        }
        try writeMathLine(
            &writer,
            "  ",
            math_strings[assertion.hyps.len].text,
        );
        try writer.writeAll(";\n```");
    } else {
        try writer.writeAll("  …;\n```");
    }
    try writeDocComment(&writer, annotations);
    return try buf.toOwnedSlice(allocator);
}

pub fn lemmaMarkdown(
    allocator: std.mem.Allocator,
    block: proof_script.ProofBlock,
    hyp_count: usize,
    hyp_count_known: bool,
) ![]const u8 {
    var buf = std.ArrayListUnmanaged(u8){};
    var writer = buf.writer(allocator);
    try writer.print("Local lemma `{s}`.", .{block.name});
    if (hyp_count_known) {
        try writer.print(" {d} {s}.", .{
            hyp_count,
            if (hyp_count == 1) "hypothesis" else "hypotheses",
        });
    }
    try writer.writeAll("\n\n```auf\n");
    try writeAnnotationLines(&writer, block.annotations);
    try writer.print("lemma {s}", .{block.name});
    if (block.header_tail.len != 0) {
        try writer.print(" {s}", .{block.header_tail});
    }
    try writer.writeAll("\n```");
    try writeDocComment(&writer, block.annotations);
    return try buf.toOwnedSlice(allocator);
}

pub fn proofLineMarkdown(
    allocator: std.mem.Allocator,
    line: proof_script.ProofLine,
) ![]const u8 {
    var buf = std.ArrayListUnmanaged(u8){};
    var writer = buf.writer(allocator);
    try writer.writeAll("```auf\n");
    try writer.print("{s}: ${s}$\n```", .{
        line.label,
        line.assertion.text,
    });
    try writer.print("\n\nProof line `{s}`.", .{line.label});
    return try buf.toOwnedSlice(allocator);
}

pub fn hypRefMarkdown(
    allocator: std.mem.Allocator,
    block_name: []const u8,
    hyp_name: ?[]const u8,
    hyp_index: usize,
    hyp_count: usize,
    hyp_count_known: bool,
    hyp_text: ?[]const u8,
) ![]const u8 {
    var buf = std.ArrayListUnmanaged(u8){};
    var writer = buf.writer(allocator);
    if (hyp_text) |text| {
        try writer.writeAll("```mm0\n$");
        try writer.writeAll(text);
        try writer.writeAll("$\n```\n\n");
    }
    if (hyp_name) |name| {
        try writer.print("hypothesis `{s}` (#{d}) of `{s}`.", .{
            name,
            hyp_index,
            block_name,
        });
    } else {
        try writer.print("hypothesis #{d} of `{s}`.", .{
            hyp_index,
            block_name,
        });
    }
    if (hyp_count_known) {
        try writer.print("\n\n{d} of {d} hypotheses.", .{
            hyp_index,
            hyp_count,
        });
    }
    return try buf.toOwnedSlice(allocator);
}

pub fn sortVarMarkdown(
    allocator: std.mem.Allocator,
    token: []const u8,
    sort_name: []const u8,
) ![]const u8 {
    return try std.fmt.allocPrint(
        allocator,
        "Theorem-local dummy `{s}` from the `@vars` pool.\n\n" ++
            "Sort: `{s}`. Available in proof-body math.",
        .{ token, sort_name },
    );
}

pub fn binderMarkdown(
    allocator: std.mem.Allocator,
    decl: Declaration,
    binder: BinderDecl,
) ![]const u8 {
    return try std.fmt.allocPrint(
        allocator,
        "Binder `{s}` for {s} `{s}`.\n\n" ++
            "Expected sort: `{s}`. {s} variable.",
        .{
            binder.name,
            decl.kind.label(),
            decl.name,
            binder.sort_name,
            if (binder.bound) "Bound" else "Free",
        },
    );
}

/// Hover text for the `sorry!` justification, which resolves to no rule.
pub const sorry_markdown =
    \\`sorry!` admits this line: the goal is accepted without a proof.
    \\
    \\The rest of the block is checked as usual and later lines may cite
    \\this one, but the theorem is not verified — the compiler reports a
    \\warning here, and the verifier rejects the output.
;

pub fn unknownRuleMarkdown(
    allocator: std.mem.Allocator,
    name: []const u8,
) ![]const u8 {
    return try std.fmt.allocPrint(allocator, "unknown rule `{s}`", .{name});
}

pub fn unknownLineMarkdown(
    allocator: std.mem.Allocator,
    label: []const u8,
) ![]const u8 {
    return try std.fmt.allocPrint(allocator, "unknown line `{s}`", .{label});
}

pub fn namedHypMarkdown(
    allocator: std.mem.Allocator,
    block_name: []const u8,
    hyp_name: []const u8,
) ![]const u8 {
    return try std.fmt.allocPrint(
        allocator,
        "hypothesis `{s}` of `{s}`.",
        .{ hyp_name, block_name },
    );
}

pub fn unknownHypMarkdown(
    allocator: std.mem.Allocator,
    block_name: []const u8,
    hyp_index: usize,
) ![]const u8 {
    return try std.fmt.allocPrint(
        allocator,
        "unknown hypothesis #{d} of `{s}`",
        .{ hyp_index, block_name },
    );
}

pub fn unknownNamedHypMarkdown(
    allocator: std.mem.Allocator,
    block_name: []const u8,
    hyp_name: []const u8,
) ![]const u8 {
    return try std.fmt.allocPrint(
        allocator,
        "unknown hypothesis #{s} of `{s}` — no hypothesis binder has this name",
        .{ hyp_name, block_name },
    );
}

pub fn ambiguousHypMarkdown(
    allocator: std.mem.Allocator,
    block_name: []const u8,
    hyp_name: []const u8,
) ![]const u8 {
    return try std.fmt.allocPrint(
        allocator,
        "ambiguous hypothesis #{s} of `{s}` — " ++
            "the name matches more than one hypothesis",
        .{ hyp_name, block_name },
    );
}

pub fn unknownBindingMarkdown(
    allocator: std.mem.Allocator,
    binder_name: []const u8,
    rule_name: []const u8,
) ![]const u8 {
    return try std.fmt.allocPrint(
        allocator,
        "unknown binder `{s}` for rule `{s}`",
        .{ binder_name, rule_name },
    );
}

pub fn unresolvedBindingMarkdown(
    allocator: std.mem.Allocator,
    binder_name: []const u8,
    rule_name: []const u8,
) ![]const u8 {
    return try std.fmt.allocPrint(
        allocator,
        "binder `{s}` for unresolved rule `{s}`",
        .{ binder_name, rule_name },
    );
}

fn writeSortModifiers(writer: anytype, modifiers: anytype) !void {
    if (modifiers.strict) try writer.writeAll("strict ");
    if (modifiers.provable) try writer.writeAll("provable ");
    if (modifiers.pure) try writer.writeAll("pure ");
    if (modifiers.free) try writer.writeAll("free ");
}

fn declarationTitle(kind: DeclarationKind) []const u8 {
    return switch (kind) {
        .sort => "Sort",
        .term => "Term",
        .def => "Definition",
        .axiom => "Axiom",
        .theorem => "Theorem",
        .lemma => "Local lemma",
        .proof_line => "Proof line",
        .sort_var => "Theorem-local dummy",
    };
}

/// Every hover has the same shape: a one-line summary, the declaration in a
/// code fence with its `@directive` annotations, then the doc comment as
/// markdown prose. A `--|` line is a directive when it starts with `@` and
/// doc text otherwise (the mm0-rs doc-comment convention, which the MM0 spec
/// calls a "special comment"); the two are interleaved freely in the source
/// and split here.
fn isDirective(annotation: []const u8) bool {
    return annotation.len != 0 and annotation[0] == '@';
}

/// The declaration's directives, one `--| …` line each, exactly as they
/// precede it in the source. They are part of what the declaration means
/// (`@rewrite` makes an axiom a rewrite rule, `@view`/`@recover` decide how
/// a rule's binders get inferred), so the hover shows them in full rather
/// than summarising their names.
fn writeAnnotationLines(
    writer: anytype,
    annotations: []const []const u8,
) !void {
    for (annotations) |annotation| {
        if (!isDirective(annotation)) continue;
        try writer.print("--| {s}\n", .{annotation});
    }
}

/// The doc comment, appended after the code fence as markdown paragraphs.
/// Consecutive prose lines form one paragraph; a blank `--|` line separates
/// paragraphs. Leading, trailing, and repeated blanks are dropped.
fn writeDocComment(
    writer: anytype,
    annotations: []const []const u8,
) !void {
    var wrote_any = false;
    var pending_break = false;
    for (annotations) |annotation| {
        if (isDirective(annotation)) continue;
        if (annotation.len == 0) {
            pending_break = wrote_any;
            continue;
        }
        try writer.writeAll(if (!wrote_any or pending_break) "\n\n" else "\n");
        try writer.writeAll(annotation);
        wrote_any = true;
        pending_break = false;
    }
}

fn definitionBodySource(
    text: []const u8,
    name_span: parse.MathSpan,
) ?[]const u8 {
    const stmt = source.statementContainingSpan(
        text,
        name_span.start,
        name_span.end,
    ) orelse return null;
    const eq = findStatementByte(text, stmt, '=') orelse return null;
    var pos = eq + 1;
    const math = nextMathStringIn(text, stmt.end, &pos) orelse return null;
    return math.text;
}

fn writeMathLine(
    writer: anytype,
    indent: []const u8,
    math: []const u8,
) !void {
    const trimmed = trimMathWhitespace(math);
    try writer.print("{s}$ ", .{indent});
    var pos: usize = 0;
    while (pos < trimmed.len) {
        const nl = std.mem.indexOfScalar(u8, trimmed[pos..], '\n');
        const line_end = if (nl) |rel| pos + rel else trimmed.len;
        if (pos != 0) try writer.print("\n{s}  ", .{indent});
        try writer.writeAll(std.mem.trim(u8, trimmed[pos..line_end], " \t\r"));
        if (nl == null) break;
        pos = line_end + 1;
    }
    try writer.writeAll(" $");
}

fn writeCompactArgList(
    writer: anytype,
    names: []const ?[]const u8,
    args: []const parse.ArgInfo,
) !void {
    var i: usize = 0;
    while (i < args.len) {
        var end = i + 1;
        while (end < args.len and canGroupArgs(names, args, i, end)) {
            end += 1;
        }
        try writeArgGroup(writer, names, args, i, end);
        i = end;
    }
}

fn canGroupArgs(
    names: []const ?[]const u8,
    args: []const parse.ArgInfo,
    first: usize,
    next: usize,
) bool {
    if (first >= names.len or next >= names.len) return false;
    if (names[first] == null or names[next] == null) return false;
    const a = args[first];
    const b = args[next];
    if (a.bound != b.bound) return false;
    if (!std.mem.eql(u8, a.sort_name, b.sort_name)) return false;
    if (a.bound) return true;
    return a.deps == b.deps;
}

fn writeArgGroup(
    writer: anytype,
    names: []const ?[]const u8,
    args: []const parse.ArgInfo,
    start: usize,
    end: usize,
) !void {
    const arg = args[start];
    const open: u8 = if (arg.bound) '{' else '(';
    const close: u8 = if (arg.bound) '}' else ')';
    try writer.print(" {c}", .{open});
    for (start..end) |idx| {
        if (idx != start) try writer.writeAll(" ");
        if (idx < names.len) {
            if (names[idx]) |name| {
                try writer.writeAll(name);
            } else {
                try writer.writeAll("_");
            }
        } else {
            try writer.writeAll("_");
        }
    }
    try writer.print(": {s}", .{arg.sort_name});
    if (!arg.bound) {
        try writeDeps(writer, arg.deps, names, args, start);
    }
    try writer.print("{c}", .{close});
}

fn writeDeps(
    writer: anytype,
    deps: u55,
    names: []const ?[]const u8,
    args: []const parse.ArgInfo,
    before: usize,
) !void {
    if (deps == 0) return;
    var bound_slot: usize = 0;
    var idx: usize = 0;
    while (idx < before) : (idx += 1) {
        if (!args[idx].bound) continue;
        const bit = @as(u55, 1) << @intCast(bound_slot);
        bound_slot += 1;
        if ((deps & bit) == 0) continue;
        if (idx >= names.len) continue;
        const name = names[idx] orelse continue;
        try writer.print(" {s}", .{name});
    }
}
