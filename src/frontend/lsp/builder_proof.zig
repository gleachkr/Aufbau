const std = @import("std");
const parse = @import("../parse_recovery.zig");
const proof_script = @import("../proof_script.zig");

const markdown = @import("markdown.zig");
const Types = @import("types.zig");
const completion = @import("completion.zig");
const support = @import("builder_support.zig");

const Declaration = Types.Declaration;

const completionSortText = completion.completionSortText;
const sort_group_proof_lemma = completion.sort_group_proof_lemma;

const lemmaMarkdown = markdown.lemmaMarkdown;

const bindersFromLemma = support.bindersFromLemma;
const hypothesesFromLemma = support.hypothesesFromLemma;
const isFatalIndexError = support.isFatalIndexError;
const proofBlockDeclarationKind = support.proofBlockDeclarationKind;
const proofSpanRange = support.proofSpanRange;

/// Index a block's header. Its body is indexed on demand
/// (`builder_body.zig`).
pub fn addProofBlock(
    self: anytype,
    block: proof_script.ProofBlock,
    global_available_before: ?usize,
) !void {
    const block_index = self.proof_blocks.items.len;
    try self.proof_blocks.append(self.allocator, .{
        .source = block,
        .global_available_before = global_available_before,
    });
    try self.addProofOutline(.{
        .name = block.name,
        .kind = proofBlockDeclarationKind(block.kind),
        .range = proofSpanRange(block.span),
        .selection_range = proofSpanRange(block.name_span),
    });

    switch (block.kind) {
        .theorem => try self.addTheoremBlockHeader(block_index, block),
        .lemma => try self.addLemmaBlockHeader(block_index, block),
    }

    // A known body has no incomplete line.
    for (block.lines) |line| {
        if (line.incomplete) self.complete = false;
    }

    const info = self.proof_blocks.items[block_index];
    if (block.kind == .lemma) {
        if (info.decl_index) |decl_index| {
            try self.proof_rule_by_name.put(
                self.allocator,
                block.name,
                self.proof_rules.items.len,
                self.proof_blocks.items.len,
            );
            try self.proof_rules.append(self.allocator, .{
                .name = block.name,
                .decl_index = decl_index,
                .available_start = block.span.end,
                .sort_text = try completionSortText(
                    self.allocator,
                    sort_group_proof_lemma,
                    block.span.end,
                    block.name,
                ),
            });
        }
    }
}

pub fn addTheoremBlockHeader(
    self: anytype,
    block_index: usize,
    block: proof_script.ProofBlock,
) !void {
    const decl_index = self.theoremDeclIndex(block.name) orelse return;
    const decl = self.declarations.items[decl_index];
    self.proof_blocks.items[block_index].decl_index = decl_index;
    self.proof_blocks.items[block_index].hyp_count = decl.hyp_count;
    self.proof_blocks.items[block_index].hyp_count_known = true;
    try self.addSymbol(.{
        .source_range = proofSpanRange(block.name_span),
        .target_range = decl.name_range,
        .markdown = decl.markdown,
    });
}

pub fn addLemmaBlockHeader(
    self: anytype,
    block_index: usize,
    block: proof_script.ProofBlock,
) !void {
    const maybe_assertion = try self.parseLemmaAssertion(block);
    if (maybe_assertion == null) self.complete = false;
    const hyp_count = if (maybe_assertion) |assertion|
        assertion.hyps.len
    else
        0;
    const binders = if (maybe_assertion) |assertion|
        try bindersFromLemma(
            self.allocator,
            block,
            assertion.arg_names,
            assertion.args,
        )
    else
        &.{};
    const decl: Declaration = .{
        .name = block.name,
        .kind = .lemma,
        .name_range = proofSpanRange(block.name_span),
        .markdown = try lemmaMarkdown(
            self.allocator,
            block,
            hyp_count,
            maybe_assertion != null,
        ),
        .binders = binders,
        .hyp_count = hyp_count,
        .hypotheses = try hypothesesFromLemma(
            self.allocator,
            block,
            hyp_count,
            if (maybe_assertion) |assertion| assertion.hyp_names else &.{},
        ),
    };
    const decl_index = try self.addDeclaration(decl);
    self.proof_blocks.items[block_index].decl_index = decl_index;
    self.proof_blocks.items[block_index].hyp_count = hyp_count;
    self.proof_blocks.items[block_index].hyp_count_known =
        maybe_assertion != null;
    try self.indexLemmaHeaderMath(
        block,
        decl_index,
        self.proof_blocks.items[block_index].global_available_before,
    );
    _ = try self.indexSignature(.proof, block.header_tail, decl_index, binders);
    try self.deferAnnotations(decl_index, block.annotations);
}

pub fn parseLemmaAssertion(
    self: anytype,
    block: proof_script.ProofBlock,
) !?parse.AssertionStmt {
    // Local copy: errors are swallowed here, so the diagnostic state the
    // mutable parse records is not needed.
    var parser = self.mm0_parser orelse return null;
    const src = try std.fmt.allocPrint(
        self.allocator,
        "theorem {s}{s};",
        .{ block.name, block.header_tail },
    );
    return parser.parseAssertionText(src, .theorem, true) catch |err| {
        if (isFatalIndexError(err)) return err;
        return null;
    };
}

pub fn sortNameForId(self: anytype, id: u7) ?[]const u8 {
    const idx: usize = id;
    if (idx >= self.sort_names.items.len) return null;
    return self.sort_names.items[idx];
}

pub fn theoremDeclIndex(self: anytype, name: []const u8) ?usize {
    const decl_index = self.decl_by_name.get(name) orelse return null;
    const decl = self.declarations.items[decl_index];
    if (decl.kind != .theorem) return null;
    return decl_index;
}

pub fn sortDeclIndex(self: anytype, name: []const u8) ?usize {
    const decl_index = self.decl_by_name.get(name) orelse return null;
    const decl = self.declarations.items[decl_index];
    if (decl.kind != .sort) return null;
    return decl_index;
}
