const std = @import("std");
const parse = @import("../parse_recovery.zig");
const proof_script = @import("../proof_script.zig");

const source = @import("source.zig");
const Types = @import("types.zig");
const completion = @import("completion.zig");

const DocumentId = Types.DocumentId;
const SourceRange = Types.SourceRange;
const DeclarationKind = Types.DeclarationKind;
const BinderDecl = Types.BinderDecl;
const HypothesisDecl = Types.HypothesisDecl;
const Declaration = Types.Declaration;

const StatementIterator = source.StatementIterator;
const sourceRangeFromSlice = source.sourceRangeFromSlice;

const completionSortText = completion.completionSortText;
const sort_group_local_binder = completion.sort_group_local_binder;

pub fn nextStatementRangeForMm0Stmt(
    iter: *StatementIterator,
    parsed: parse.MM0Stmt,
) SourceRange {
    const name_range = mm0StmtNameRange(parsed);
    while (iter.next()) |stmt| {
        if (stmt.start <= name_range.start and stmt.end >= name_range.end) {
            return .{
                .document = .mm0,
                .start = stmt.start,
                .end = stmt.end,
            };
        }
    }
    return name_range;
}

fn mm0StmtNameRange(stmt: parse.MM0Stmt) SourceRange {
    return switch (stmt) {
        .sort => |sort| mathSpanRange(sort.name_span),
        .term => |term| mathSpanRange(term.name_span),
        .assertion => |assertion| mathSpanRange(assertion.name_span),
    };
}

pub fn proofBlockDeclarationKind(kind: proof_script.BlockKind) DeclarationKind {
    return switch (kind) {
        .theorem => .theorem,
        .lemma => .lemma,
    };
}

pub fn mathSpanRange(span: parse.MathSpan) SourceRange {
    return .{
        .document = .mm0,
        .start = span.start,
        .end = span.end,
    };
}

pub fn proofSpanRange(span: proof_script.Span) SourceRange {
    return .{
        .document = .proof,
        .start = span.start,
        .end = span.end,
    };
}

pub fn proofMathTextSpan(span: proof_script.Span) parse.MathSpan {
    return .{
        .start = @min(span.start + 1, span.end),
        .end = if (span.end > span.start) span.end - 1 else span.end,
    };
}

pub fn targetRangeIfAvailable(decl: Declaration, use_start: usize) ?SourceRange {
    if (decl.name_range.start <= use_start) return decl.name_range;
    return null;
}

pub fn targetRangeForUse(
    decl: Declaration,
    document: DocumentId,
    use_start: usize,
    available_before: ?usize,
) ?SourceRange {
    return switch (document) {
        .mm0 => targetRangeIfAvailable(decl, use_start),
        .proof => {
            if (decl.name_range.document == .proof) {
                if (decl.name_range.start <= use_start) return decl.name_range;
                return null;
            }
            const before = available_before orelse return decl.name_range;
            if (decl.name_range.start < before) return decl.name_range;
            return null;
        },
    };
}

pub fn isFatalIndexError(err: anyerror) bool {
    return switch (err) {
        error.OutOfMemory => true,
        else => false,
    };
}

pub fn findBinder(decl: Declaration, name: []const u8) ?BinderDecl {
    return findBinderIn(decl.binders, name);
}

pub fn findBinderIn(binders: []const BinderDecl, name: []const u8) ?BinderDecl {
    for (binders) |binder| {
        if (std.mem.eql(u8, binder.name, name)) return binder;
    }
    return null;
}

pub fn hypothesesFromMm0Assertion(
    allocator: std.mem.Allocator,
    text: []const u8,
    assertion: parse.AssertionStmt,
) ![]const HypothesisDecl {
    const math_strings = try source.mathStringsBeforeByteInContainingStatement(
        allocator,
        text,
        assertion.name_span.start,
        assertion.name_span.end,
        '=',
    );
    defer allocator.free(math_strings);
    return hypothesesFromMathStrings(
        allocator,
        .mm0,
        text,
        text[assertion.name_span.end..],
        math_strings,
        0,
        assertion.hyps.len,
        assertion.hyp_names,
    );
}

pub fn hypothesesFromLemma(
    allocator: std.mem.Allocator,
    block: proof_script.ProofBlock,
    hyp_count: usize,
    hyp_names: []const ?[]const u8,
) ![]const HypothesisDecl {
    if (block.header_tail.len == 0 or hyp_count == 0) return &.{};
    return collectHypotheses(
        allocator,
        .proof,
        block.header_tail,
        0,
        block.header_tail.len,
        block.header_tail_span.start,
        hyp_count,
        hyp_names,
    );
}

fn collectHypotheses(
    allocator: std.mem.Allocator,
    document: DocumentId,
    text: []const u8,
    start: usize,
    end: usize,
    offset_base: usize,
    hyp_count: usize,
    hyp_names: []const ?[]const u8,
) ![]const HypothesisDecl {
    var pos = start;
    var math_strings = std.ArrayListUnmanaged(source.MathStringSpan).empty;
    defer math_strings.deinit(allocator);
    while (math_strings.items.len < hyp_count) {
        const math = source.nextMathStringIn(text, end, &pos) orelse break;
        try math_strings.append(allocator, math);
    }
    return hypothesesFromMathStrings(
        allocator,
        document,
        text,
        text[start..end],
        math_strings.items,
        offset_base,
        hyp_count,
        hyp_names,
    );
}

/// Pair each hypothesis with its formula among `math_strings`, offsets in
/// `text`. `signature`, the slice of `text` after the assertion's name,
/// locates the names of each binder-form hypothesis group.
fn hypothesesFromMathStrings(
    allocator: std.mem.Allocator,
    document: DocumentId,
    text: []const u8,
    signature: []const u8,
    math_strings: []const source.MathStringSpan,
    offset_base: usize,
    hyp_count: usize,
    hyp_names: []const ?[]const u8,
) ![]const HypothesisDecl {
    const tokens = try source.scanSignature(allocator, signature);
    defer allocator.free(tokens);
    var group_names = std.ArrayListUnmanaged(source.SignatureToken).empty;
    defer group_names.deinit(allocator);
    for (tokens) |token| {
        if (token.role == .hypothesis) try group_names.append(allocator, token);
    }

    var result = std.ArrayListUnmanaged(HypothesisDecl).empty;
    var hyp_index: usize = 0;
    var next_name: usize = 0;
    for (math_strings) |math| {
        if (hyp_index >= hyp_count) break;
        const range: SourceRange = .{
            .document = document,
            .start = offset_base + math.inner_start,
            .end = offset_base + math.inner_end,
        };
        // A binder group declares ONE formula for every name in it, so
        // `(h1 h2: $ a $)` yields two hypotheses sharing this span. Pairing
        // one hypothesis per math string would push every name after the
        // first onto the following formula — ultimately the conclusion.
        // The group's names are the hypothesis names before this formula.
        var group_end = next_name;
        while (group_end < group_names.items.len and
            offsetIn(text, group_names.items[group_end].text) < math.inner_start)
        {
            group_end += 1;
        }
        const group = group_names.items[next_name..group_end];
        next_name = group_end;
        var consumed: usize = 0;
        while (consumed < group.len and hyp_index < hyp_count) {
            const declared = if (hyp_index < hyp_names.len)
                hyp_names[hyp_index]
            else
                null;
            // The scan is a source read-back of names the parse already
            // knows; a disagreement means we misread the group, so stop
            // rather than pair a formula with the wrong hypothesis.
            const actual = declared orelse break;
            if (!std.mem.eql(u8, actual, group[consumed].text)) break;
            try result.append(allocator, .{
                .text = math.text,
                .range = range,
                .name = actual,
                .name_range = rangeIn(document, text, offset_base, group[consumed].text),
            });
            consumed += 1;
            hyp_index += 1;
        }
        if (consumed != 0) continue;
        // An arrow-form hypothesis (no binder group), or a group we could
        // not read back: pair one hypothesis with this formula, and leave
        // the name unlocated rather than guessing at a position.
        try result.append(allocator, .{
            .text = math.text,
            .range = range,
            .name = if (hyp_index < hyp_names.len) hyp_names[hyp_index] else null,
            .name_range = null,
        });
        hyp_index += 1;
    }
    return try result.toOwnedSlice(allocator);
}

/// The range of `slice`, a slice of `text`, where `text` starts at
/// `offset_base` in `document`.
fn rangeIn(
    document: DocumentId,
    text: []const u8,
    offset_base: usize,
    slice: []const u8,
) SourceRange {
    const start = offset_base + offsetIn(text, slice);
    return .{ .document = document, .start = start, .end = start + slice.len };
}

fn offsetIn(text: []const u8, slice: []const u8) usize {
    return @intFromPtr(slice.ptr) - @intFromPtr(text.ptr);
}

pub fn bindersFromTerm(
    allocator: std.mem.Allocator,
    document: DocumentId,
    text: []const u8,
    term: parse.TermStmt,
) ![]const BinderDecl {
    var binders = std.ArrayListUnmanaged(BinderDecl).empty;
    try appendBindersFromArgs(
        allocator,
        &binders,
        document,
        text,
        term.arg_names,
        term.args,
        0,
    );
    try appendBindersFromArgs(
        allocator,
        &binders,
        document,
        text,
        term.dummy_names,
        term.dummy_args,
        term.args.len,
    );
    return try binders.toOwnedSlice(allocator);
}

fn appendBindersFromArgs(
    allocator: std.mem.Allocator,
    binders: *std.ArrayListUnmanaged(BinderDecl),
    document: DocumentId,
    text: []const u8,
    names: []const ?[]const u8,
    args: []const parse.ArgInfo,
    ordinal_base: usize,
) !void {
    for (args, 0..) |arg, i| {
        if (i >= names.len) continue;
        const name = names[i] orelse continue;
        try binders.append(allocator, .{
            .name = name,
            .sort_name = arg.sort_name,
            .bound = arg.bound,
            .range = sourceRangeFromSlice(document, text, name),
            .sort_text = try completionSortText(
                allocator,
                sort_group_local_binder,
                ordinal_base + i,
                name,
            ),
        });
    }
}

pub fn bindersFromProofDef(
    allocator: std.mem.Allocator,
    def: proof_script.DefItem,
    term: parse.TermStmt,
) ![]const BinderDecl {
    const header_tail = def.header_tail orelse return &.{};
    const header_span = def.header_tail_span orelse return &.{};
    const tokens = try source.scanSignature(allocator, header_tail);
    defer allocator.free(tokens);

    var binders = std.ArrayListUnmanaged(BinderDecl).empty;
    var arg_index: usize = 0;
    var dummy_index: usize = 0;
    var ordinal: usize = 0;
    for (tokens) |token| {
        if (token.role != .binder) continue;
        const arg = if (token.dummy) blk: {
            if (dummy_index >= term.dummy_args.len) continue;
            const arg = term.dummy_args[dummy_index];
            dummy_index += 1;
            break :blk arg;
        } else blk: {
            if (arg_index >= term.args.len) continue;
            const arg = term.args[arg_index];
            arg_index += 1;
            break :blk arg;
        };
        const maybe_name = if (token.dummy)
            term.dummy_names[dummy_index - 1]
        else
            term.arg_names[arg_index - 1];
        const name = maybe_name orelse continue;
        try binders.append(allocator, .{
            .name = name,
            .sort_name = arg.sort_name,
            .bound = arg.bound,
            .range = rangeIn(.proof, header_tail, header_span.start, token.text),
            .sort_text = try completionSortText(
                allocator,
                sort_group_local_binder,
                ordinal,
                name,
            ),
        });
        ordinal += 1;
    }
    return try binders.toOwnedSlice(allocator);
}

pub fn bindersFromArgs(
    allocator: std.mem.Allocator,
    document: DocumentId,
    text: []const u8,
    names: []const ?[]const u8,
    args: []const parse.ArgInfo,
) ![]const BinderDecl {
    var binders = std.ArrayListUnmanaged(BinderDecl).empty;
    for (args, 0..) |arg, i| {
        if (i >= names.len) continue;
        const name = names[i] orelse continue;
        try binders.append(allocator, .{
            .name = name,
            .sort_name = arg.sort_name,
            .bound = arg.bound,
            .range = sourceRangeFromSlice(document, text, name),
            .sort_text = try completionSortText(
                allocator,
                sort_group_local_binder,
                i,
                name,
            ),
        });
    }
    return try binders.toOwnedSlice(allocator);
}

pub fn completionArgsFromArgs(
    allocator: std.mem.Allocator,
    document: DocumentId,
    text: []const u8,
    names: []const ?[]const u8,
    args: []const parse.ArgInfo,
) ![]const BinderDecl {
    var binders = std.ArrayListUnmanaged(BinderDecl).empty;
    for (args, 0..) |arg, i| {
        const name = if (i < names.len) names[i] else null;
        const label = if (name) |actual|
            actual
        else
            try std.fmt.allocPrint(allocator, "arg{d}", .{i + 1});
        try binders.append(allocator, .{
            .name = label,
            .sort_name = arg.sort_name,
            .bound = arg.bound,
            .range = if (name) |actual|
                sourceRangeFromSlice(document, text, actual)
            else
                null,
            .sort_text = try completionSortText(
                allocator,
                sort_group_local_binder,
                i,
                label,
            ),
        });
    }
    return try binders.toOwnedSlice(allocator);
}

pub fn bindersFromLemma(
    allocator: std.mem.Allocator,
    block: proof_script.ProofBlock,
    names: []const ?[]const u8,
    args: []const parse.ArgInfo,
) ![]const BinderDecl {
    const tokens = try source.scanSignature(allocator, block.header_tail);
    defer allocator.free(tokens);
    var binders = std.ArrayListUnmanaged(BinderDecl).empty;
    var next_token: usize = 0;
    for (args, 0..) |arg, i| {
        if (i >= names.len) continue;
        const name = names[i] orelse continue;
        const range = for (tokens[next_token..], next_token..) |token, at| {
            if (token.role != .binder or !std.mem.eql(u8, token.text, name)) continue;
            next_token = at + 1;
            break rangeIn(.proof, block.header_tail, block.header_tail_span.start, token.text);
        } else null;
        try binders.append(allocator, .{
            .name = name,
            .sort_name = arg.sort_name,
            .bound = arg.bound,
            .range = range,
            .sort_text = try completionSortText(
                allocator,
                sort_group_local_binder,
                i,
                name,
            ),
        });
    }
    return try binders.toOwnedSlice(allocator);
}
