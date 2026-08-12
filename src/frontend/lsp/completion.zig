const std = @import("std");
const proof_script = @import("../proof_script.zig");
const source = @import("source.zig");
const Types = @import("types.zig");
const model = @import("model.zig");
const notation_model = @import("notation.zig");

const DocumentId = Types.DocumentId;
const SourceRange = Types.SourceRange;
const CompletionOptions = Types.CompletionOptions;
const CompletionKind = Types.CompletionKind;
const CompletionItem = Types.CompletionItem;
const DeclarationKind = Types.DeclarationKind;
const Declaration = Types.Declaration;

const SourceSpan = source.SourceSpan;
const StatementIterator = source.StatementIterator;
const MathTokenCursor = source.MathTokenCursor;
const statementHeader = source.statementHeader;
const firstMathStringIn = source.firstMathStringIn;
const isMathWhitespace = source.isMathWhitespace;
const startsLineComment = source.startsLineComment;
const isIdentChar = source.isIdentChar;

const ProofApplicationInfo = model.ProofApplicationInfo;
const ProofRuleDecl = model.ProofRuleDecl;
const RuleResolution = model.RuleResolution;
const NotationCompletionDecl = notation_model.NotationCompletionDecl;

pub fn completionsAt(
    self: anytype,
    allocator: std.mem.Allocator,
    document: DocumentId,
    offset: usize,
    options: CompletionOptions,
) ![]const CompletionItem {
    const text = self.textForDocument(document) orelse return &.{};
    const safe_offset = @min(offset, text.len);
    var list = std.ArrayListUnmanaged(CompletionItem){};
    switch (document) {
        .mm0 => {
            const math = mathStringAt(text, safe_offset);
            const replacement = completionReplacementRange(
                self,
                .mm0,
                text,
                safe_offset,
                math,
                false,
            );
            try mm0CompletionsAt(
                self,
                allocator,
                &list,
                text,
                safe_offset,
                math,
                replacement,
                options,
            );
        },
        .proof => {
            const context = proofContextAt(self, text, safe_offset);
            const math: ?SourceSpan = switch (context) {
                .math => |span| span,
                else => null,
            };
            const replacement = completionReplacementRange(
                self,
                .proof,
                text,
                safe_offset,
                math,
                placeholderPosition(context),
            );
            try proofCompletionsAt(
                self,
                allocator,
                &list,
                text,
                safe_offset,
                context,
                replacement,
                options,
            );
        },
    }
    return try list.toOwnedSlice(allocator);
}

/// The syntactic context of an offset in a proof script. Resolved once per
/// request by `proofContextAt`; the replacement range and the completion
/// branch both derive from it, so the two can never disagree about what the
/// cursor is on.
const ProofContext = union(enum) {
    /// Inside a line comment.
    comment,
    /// Inside a math string (span includes the `$` delimiters).
    math: SourceSpan,
    /// On a theorem-header line.
    header,
    /// On the rule-name token of a parsed application.
    rule_name: ProofApplicationInfo,
    /// Inside a parsed application's binding list.
    binding_slot: ProofApplicationInfo,
    /// Inside a parsed application's reference list.
    reference_slot: ProofApplicationInfo,
    /// After `by` where no application has parsed yet; payload is the index
    /// of the enclosing proof block.
    rule_position: usize,
    none,
};

/// Resolve the completion context at `offset`: comments and math and headers
/// shadow the application slots, which shadow a bare rule position, so
/// consumers do not mistake one for another.
fn proofContextAt(self: anytype, text: []const u8, offset: usize) ProofContext {
    if (lineCommentContextAt(text, offset)) return .comment;
    if (mathStringAt(text, offset)) |math| return .{ .math = math };
    if (proofHeaderContextAt(text, offset)) return .header;
    if (proofRuleApplicationAt(self, offset)) |app| {
        return .{ .rule_name = app };
    }
    if (proofBindingApplicationAt(self, offset)) |app| {
        return .{ .binding_slot = app };
    }
    if (proofReferenceApplicationAt(self, offset)) |app| {
        return .{ .reference_slot = app };
    }
    if (proofRuleContextAt(text, offset)) {
        if (proofBlockNear(self, offset)) |block_index| {
            return .{ .rule_position = block_index };
        }
    }
    return .none;
}

/// Whether `offset` is in a proof-rule completion position.
pub fn isProofRuleCompletionAt(self: anytype, offset: usize) bool {
    const text = self.textForDocument(.proof) orelse return false;
    const safe_offset = @min(offset, text.len);
    return switch (proofContextAt(self, text, safe_offset)) {
        .rule_name, .rule_position => true,
        else => false,
    };
}

fn completionReplacementRange(
    self: anytype,
    document: DocumentId,
    text: []const u8,
    offset: usize,
    math: ?SourceSpan,
    placeholder_position: bool,
) SourceRange {
    if (math) |span| {
        return mathCompletionReplacementRange(
            document,
            text,
            span,
            offset,
            self.left_delims,
            self.right_delims,
        );
    }
    return identifierCompletionReplacementRange(
        document,
        text,
        offset,
        placeholder_position,
    );
}

/// Whether a `?` in this context would be the tail of a search placeholder —
/// true in the positions that accept one, a rule name and a reference slot.
/// Nothing else in a proof script spells `?`, so elsewhere the character is
/// part of the token being completed rather than a boundary.
fn placeholderPosition(context: ProofContext) bool {
    return switch (context) {
        .rule_name, .rule_position, .reference_slot => true,
        else => false,
    };
}

fn mm0CompletionsAt(
    self: anytype,
    allocator: std.mem.Allocator,
    list: *std.ArrayListUnmanaged(CompletionItem),
    text: []const u8,
    offset: usize,
    math: ?SourceSpan,
    replacement: SourceRange,
    options: CompletionOptions,
) !void {
    if (annotationContextAt(text, offset)) {
        try appendAnnotationCompletions(list, allocator, replacement);
        return;
    }
    if (lineCommentContextAt(text, offset)) return;
    if (math != null) {
        try appendCurrentDeclarationBinders(
            self,
            list,
            allocator,
            text,
            offset,
            replacement,
        );
        try appendTermCompletions(
            self,
            list,
            allocator,
            replacement,
            .mm0,
            offset,
            null,
            options,
        );
        return;
    }
    if (mm0SortContextAt(text, offset)) {
        try appendSortCompletions(self, list, allocator, replacement);
        return;
    }
    if (mm0ReferenceContextAt(text, offset)) {
        try appendGlobalDeclarationCompletions(
            self,
            list,
            allocator,
            replacement,
            &.{ .term, .def, .axiom, .theorem },
            .mm0,
            offset,
            null,
        );
        return;
    }
    if (mm0TopLevelContextAt(text, offset)) {
        try appendKeywordCompletions(list, allocator, replacement);
    }
}

fn proofCompletionsAt(
    self: anytype,
    allocator: std.mem.Allocator,
    list: *std.ArrayListUnmanaged(CompletionItem),
    text: []const u8,
    offset: usize,
    context: ProofContext,
    replacement: SourceRange,
    options: CompletionOptions,
) !void {
    switch (context) {
        .comment, .none => {},
        .math => {
            const block = proofBlockNear(self, offset);
            if (block) |block_index| {
                try appendBlockBinders(
                    self,
                    list,
                    allocator,
                    block_index,
                    replacement,
                );
                if (proofLineMathContextAt(text, offset)) {
                    try appendSortVarCompletions(
                        self,
                        list,
                        allocator,
                        replacement,
                        self.proof_blocks[block_index].global_available_before,
                    );
                }
            }
            try appendTermCompletions(
                self,
                list,
                allocator,
                replacement,
                .proof,
                offset,
                if (block) |i|
                    self.proof_blocks[i].global_available_before
                else
                    null,
                options,
            );
        },
        .header => try appendGlobalDeclarationCompletions(
            self,
            list,
            allocator,
            replacement,
            &.{.theorem},
            .proof,
            offset,
            null,
        ),
        .rule_name => |app| try appendProofRuleCompletions(
            self,
            list,
            allocator,
            app.block_index,
            offset,
            replacement,
            placeholderTokenAt(text, replacement),
        ),
        .binding_slot => |app| try appendRuleBinderCompletions(
            self,
            list,
            allocator,
            app,
            replacement,
        ),
        .reference_slot => |app| try appendProofReferenceCompletions(
            self,
            list,
            allocator,
            app.block_index,
            app.line_start,
            replacement,
            placeholderTokenAt(text, replacement),
        ),
        .rule_position => |block_index| try appendProofRuleCompletions(
            self,
            list,
            allocator,
            block_index,
            offset,
            replacement,
            placeholderTokenAt(text, replacement),
        ),
    }
}

fn appendCurrentDeclarationBinders(
    self: anytype,
    list: *std.ArrayListUnmanaged(CompletionItem),
    allocator: std.mem.Allocator,
    text: []const u8,
    offset: usize,
    replacement: SourceRange,
) !void {
    const decl_index = mm0DeclarationIndexAt(self, text, offset) orelse return;
    try appendDeclarationBinders(self, list, allocator, decl_index, replacement);
}

fn appendBlockBinders(
    self: anytype,
    list: *std.ArrayListUnmanaged(CompletionItem),
    allocator: std.mem.Allocator,
    block_index: usize,
    replacement: SourceRange,
) !void {
    const decl_index = self.proof_blocks[block_index].decl_index orelse return;
    try appendDeclarationBinders(self, list, allocator, decl_index, replacement);
}

fn appendSortVarCompletions(
    self: anytype,
    list: *std.ArrayListUnmanaged(CompletionItem),
    allocator: std.mem.Allocator,
    replacement: SourceRange,
    available_before: ?usize,
) !void {
    for (self.declarations) |decl| {
        if (decl.kind != .sort_var) continue;
        if (!globalDeclarationAvailable(
            decl,
            .proof,
            replacement.start,
            available_before,
        )) continue;
        if (completionAlreadyInserts(
            list.items,
            replacement,
            decl.name,
        )) continue;
        try list.append(allocator, .{
            .label = decl.name,
            .kind = .binder,
            .detail = declarationKindName(decl.kind),
            .documentation_markdown = decl.markdown,
            .replacement = replacement,
            .replacement_text = decl.name,
            .sort_text = globalDeclarationSortText(decl),
        });
    }
}

fn appendRuleBinderCompletions(
    self: anytype,
    list: *std.ArrayListUnmanaged(CompletionItem),
    allocator: std.mem.Allocator,
    app: ProofApplicationInfo,
    replacement: SourceRange,
) !void {
    const rule = ruleResolutionAt(
        self,
        app.block_index,
        app.rule_name,
        app.use_start,
    ) orelse return;
    try appendDeclarationBinders(
        self,
        list,
        allocator,
        rule.decl_index,
        replacement,
    );
}

fn appendDeclarationBinders(
    self: anytype,
    list: *std.ArrayListUnmanaged(CompletionItem),
    allocator: std.mem.Allocator,
    decl_index: usize,
    replacement: SourceRange,
) !void {
    const decl = self.declarations[decl_index];
    for (decl.binders) |binder| {
        try list.append(allocator, .{
            .label = binder.name,
            .kind = .binder,
            .detail = binder.sort_name,
            .replacement = replacement,
            .replacement_text = binder.name,
            .sort_text = binder.sort_text,
        });
    }
}

fn appendSortCompletions(
    self: anytype,
    list: *std.ArrayListUnmanaged(CompletionItem),
    allocator: std.mem.Allocator,
    replacement: SourceRange,
) !void {
    try appendGlobalDeclarationCompletions(
        self,
        list,
        allocator,
        replacement,
        &.{.sort},
        .mm0,
        replacement.start,
        null,
    );
}

fn appendTermCompletions(
    self: anytype,
    list: *std.ArrayListUnmanaged(CompletionItem),
    allocator: std.mem.Allocator,
    replacement: SourceRange,
    document: DocumentId,
    use_start: usize,
    available_before: ?usize,
    options: CompletionOptions,
) !void {
    try appendGlobalDeclarationCompletions(
        self,
        list,
        allocator,
        replacement,
        &.{ .term, .def },
        document,
        use_start,
        available_before,
    );
    try appendNotationCompletions(
        self,
        list,
        allocator,
        replacement,
        document,
        use_start,
        available_before,
        options,
    );
}

fn appendNotationCompletions(
    self: anytype,
    list: *std.ArrayListUnmanaged(CompletionItem),
    allocator: std.mem.Allocator,
    replacement: SourceRange,
    document: DocumentId,
    use_start: usize,
    available_before: ?usize,
    options: CompletionOptions,
) !void {
    const replacement_fragment = replacementFragment(self, replacement);
    for (self.notations) |notation| {
        const decl = self.declarations[notation.decl_index];
        if (!globalDeclarationAvailable(
            decl,
            document,
            use_start,
            available_before,
        )) continue;
        if (!completionAlreadyInserts(
            list.items,
            replacement,
            notation.token,
        )) {
            try list.append(allocator, .{
                .label = notation.token,
                .kind = .notation,
                .detail = notation.detail,
                .documentation_markdown = decl.markdown,
                .replacement = replacement,
                .replacement_text = notation.token,
                .filter_text = notationFilterText(
                    notation,
                    decl,
                    replacement_fragment,
                ),
                .sort_text = notationCompletionSortText(
                    notation,
                    decl,
                    replacement_fragment,
                ),
            });
        }
        if (options.snippet_support) {
            try appendNotationSnippetCompletion(
                list,
                allocator,
                replacement,
                notation,
                decl,
                replacement_fragment,
            );
        }
    }
}

fn appendGlobalDeclarationCompletions(
    self: anytype,
    list: *std.ArrayListUnmanaged(CompletionItem),
    allocator: std.mem.Allocator,
    replacement: SourceRange,
    kinds: []const DeclarationKind,
    document: DocumentId,
    use_start: usize,
    available_before: ?usize,
) !void {
    for (self.declarations) |decl| {
        if (!declarationKindIn(decl.kind, kinds)) continue;
        if (!globalDeclarationAvailable(
            decl,
            document,
            use_start,
            available_before,
        )) continue;
        try list.append(allocator, .{
            .label = decl.name,
            .kind = completionKindForDeclaration(decl.kind),
            .detail = declarationKindName(decl.kind),
            .documentation_markdown = decl.markdown,
            .replacement = replacement,
            .replacement_text = decl.name,
            .sort_text = globalDeclarationSortText(decl),
        });
    }
}

const SearchTactic = struct {
    label: []const u8,
    detail: []const u8,
    sort_text: []const u8,
    markdown: []const u8,
};

/// The proof-search placeholders (`proof_script.isSearchPlaceholderRuleName`).
/// They are legal wherever a rule name is, so they ride along with the rule
/// completions instead of forming a context of their own, and they lead the
/// list: four fixed entries a reader can learn, ahead of the theory's rules.
const search_tactics = [_]SearchTactic{
    .{
        .label = "auto?",
        .detail = "search: multi-step proof",
        .sort_text = sort_group_search_tactic ++ " 00",
        .markdown =
        \\Search for a proof of this goal, synthesizing intermediate steps.
        \\
        \\The most capable and the most expensive of the placeholders. Bounded
        \\by a work budget, so it gives up rather than running forever.
        ,
    },
    .{
        .label = "exact?",
        .detail = "search: one step from what is in reach",
        .sort_text = sort_group_search_tactic ++ " 01",
        .markdown =
        \\Close the goal with a single rule whose hypotheses are all discharged
        \\by the hypotheses (`#1`, `#2`, …) and earlier lines already in scope.
        \\
        \\Fast, and its answer is unambiguous. It invents no intermediate steps.
        ,
    },
    .{
        .label = "apply?",
        .detail = "search: apply a rule to what is in reach",
        .sort_text = sort_group_search_tactic ++ " 02",
        .markdown =
        \\A variant of `exact?` oriented toward "apply *a* rule here" rather
        \\than "close this goal outright". It reports candidates the same way.
        ,
    },
    .{
        .label = "conversion?",
        .detail = "search: rewrite to a reference",
        .sort_text = sort_group_search_tactic ++ " 03",
        .markdown =
        \\Rewrite the goal, by a chain of enrolled `@conversion` rules applied
        \\anywhere and in either direction, to a hypothesis or an earlier line.
        \\
        \\On success it expands into ordinary rewrite, congruence, and transport
        \\lines — one per step.
        ,
    },
};

comptime {
    // The placeholders themselves live in `proof_script`; this table only
    // adds the prose. Adding one there must not silently leave it
    // un-offered here.
    if (search_tactics.len != proof_script.search_placeholder_names.len) {
        @compileError("search_tactics is out of sync with " ++
            "proof_script.search_placeholder_names");
    }
    for (search_tactics, proof_script.search_placeholder_names) |tactic, name| {
        if (!std.mem.eql(u8, tactic.label, name)) {
            @compileError("search_tactics is out of sync with " ++
                "proof_script.search_placeholder_names: " ++ tactic.label);
        }
    }
}

fn appendSearchTacticCompletions(
    list: *std.ArrayListUnmanaged(CompletionItem),
    allocator: std.mem.Allocator,
    replacement: SourceRange,
) !void {
    for (search_tactics) |tactic| {
        try list.append(allocator, .{
            .label = tactic.label,
            .kind = .keyword,
            .detail = tactic.detail,
            .documentation_markdown = tactic.markdown,
            .replacement = replacement,
            .replacement_text = tactic.label,
            .sort_text = tactic.sort_text,
        });
    }
}

/// Whether the token being completed already holds a `?`. No rule name can
/// contain one, so the reader has committed to a placeholder and the theory's
/// rules are noise. Narrowing here rather than leaving it to the client keeps
/// the answer the same in every editor: clients disagree about whether `?` is
/// part of a word, and the ones that say no do not filter the list at all.
fn placeholderTokenAt(text: []const u8, replacement: SourceRange) bool {
    const end = @min(replacement.end, text.len);
    const start = @min(replacement.start, end);
    return std.mem.indexOfScalar(u8, text[start..end], '?') != null;
}

fn appendProofRuleCompletions(
    self: anytype,
    list: *std.ArrayListUnmanaged(CompletionItem),
    allocator: std.mem.Allocator,
    block_index: usize,
    use_start: usize,
    replacement: SourceRange,
    placeholder_token: bool,
) !void {
    try appendSearchTacticCompletions(list, allocator, replacement);
    if (placeholder_token) return;
    var seen = std.StringHashMapUnmanaged(void){};
    for (self.proof_rules) |rule| {
        if (rule.available_start > use_start) continue;
        if (seen.contains(rule.name)) continue;
        try seen.put(allocator, rule.name, {});
        const decl = self.declarations[rule.decl_index];
        try list.append(allocator, .{
            .label = rule.name,
            .kind = .lemma,
            .detail = "lemma",
            .documentation_markdown = decl.markdown,
            .replacement = replacement,
            .replacement_text = rule.name,
            .sort_text = rule.sort_text,
        });
    }
    for (self.declarations) |decl| {
        switch (decl.kind) {
            .axiom, .theorem => {},
            else => continue,
        }
        if (seen.contains(decl.name)) continue;
        if (!globalRuleAvailable(self, block_index, decl)) continue;
        try list.append(allocator, .{
            .label = decl.name,
            .kind = completionKindForDeclaration(decl.kind),
            .detail = declarationKindName(decl.kind),
            .documentation_markdown = decl.markdown,
            .replacement = replacement,
            .replacement_text = decl.name,
            .sort_text = globalDeclarationSortText(decl),
        });
    }
}

fn appendProofReferenceCompletions(
    self: anytype,
    list: *std.ArrayListUnmanaged(CompletionItem),
    allocator: std.mem.Allocator,
    block_index: usize,
    line_start: usize,
    replacement: SourceRange,
    placeholder_token: bool,
) !void {
    // A reference slot also accepts a placeholder — `mp [auto?, #1]` fills just
    // the first premise — so the same four tactics belong here.
    try appendSearchTacticCompletions(list, allocator, replacement);
    if (placeholder_token) return;
    const block = self.proof_blocks[block_index];
    if (block.hyp_count_known) {
        var i: usize = 1;
        while (i <= block.hyp_count) : (i += 1) {
            const label = try std.fmt.allocPrint(allocator, "#{d}", .{i});
            try list.append(allocator, .{
                .label = label,
                .kind = .hypothesis,
                .detail = "hypothesis",
                .replacement = replacement,
                .replacement_text = label,
                .sort_text = try completionSortText(
                    allocator,
                    sort_group_proof_reference,
                    i,
                    label,
                ),
            });
        }
        try appendNamedHypCompletions(
            self,
            list,
            allocator,
            block,
            replacement,
        );
    }
    for (self.proof_lines) |line| {
        if (line.block_index != block_index) continue;
        if (line.line_start >= line_start) continue;
        const decl = self.declarations[line.decl_index];
        try list.append(allocator, .{
            .label = line.name,
            .kind = .proof_line,
            .detail = "proof line",
            .documentation_markdown = decl.markdown,
            .replacement = replacement,
            .replacement_text = line.name,
            .sort_text = line.sort_text,
        });
    }
}

fn appendNamedHypCompletions(
    self: anytype,
    list: *std.ArrayListUnmanaged(CompletionItem),
    allocator: std.mem.Allocator,
    block: model.ProofBlockInfo,
    replacement: SourceRange,
) !void {
    const decl_index = block.decl_index orelse return;
    const hypotheses = self.declarations[decl_index].hypotheses;
    const hyp_names = try model.hypNamesFromHypotheses(allocator, hypotheses);
    defer allocator.free(hyp_names);
    for (hypotheses, 0..) |hyp, i| {
        const name = hyp.name orelse continue;
        // Offer a name only when a written `#name` would resolve to this
        // hypothesis: a duplicated name is rejected as ambiguous, so
        // offering it would suggest a ref the compiler refuses.
        if (!hypNameResolvesTo(hyp_names, i, name)) continue;
        const label = try std.fmt.allocPrint(allocator, "#{s}", .{name});
        try list.append(allocator, .{
            .label = label,
            .kind = .hypothesis,
            .detail = "hypothesis",
            .documentation_markdown = try std.fmt.allocPrint(
                allocator,
                "```mm0\n${s}$\n```",
                .{hyp.text},
            ),
            .replacement = replacement,
            .replacement_text = label,
            .sort_text = try completionSortText(
                allocator,
                sort_group_proof_reference,
                i + 1,
                label,
            ),
        });
    }
}

fn hypNameResolvesTo(
    hyp_names: []const ?[]const u8,
    index: usize,
    name: []const u8,
) bool {
    const resolution = proof_script.resolveHypRef(
        hyp_names,
        hyp_names.len,
        .{ .index = 0, .name = name, .span = .{ .start = 0, .end = 0 } },
    );
    return switch (resolution) {
        .index => |resolved| resolved == index,
        .unknown, .ambiguous => false,
    };
}

fn mm0DeclarationIndexAt(
    self: anytype,
    text: []const u8,
    offset: usize,
) ?usize {
    var iter = StatementIterator.init(text);
    while (iter.next()) |stmt| {
        if (offset < stmt.start or offset > stmt.end) continue;
        const header = statementHeader(text, stmt) orelse return null;
        const name = header.name orelse return null;
        return self.decl_by_name.get(name);
    }
    return null;
}

fn proofBlockNear(self: anytype, offset: usize) ?usize {
    var best: ?usize = null;
    for (self.proof_blocks, 0..) |block, i| {
        if (block.span.start > offset) continue;
        if (best == null or
            block.span.start > self.proof_blocks[best.?].span.start)
        {
            best = i;
        }
    }
    return best;
}

fn proofRuleApplicationAt(
    self: anytype,
    offset: usize,
) ?ProofApplicationInfo {
    for (self.proof_applications) |app| {
        if (offset >= app.rule_span.start and offset <= app.rule_span.end) {
            return app;
        }
    }
    return null;
}

fn proofBindingApplicationAt(
    self: anytype,
    offset: usize,
) ?ProofApplicationInfo {
    for (self.proof_applications) |app| {
        const range = app.binding_list_span orelse continue;
        if (offset >= range.start and offset <= range.end) return app;
    }
    return null;
}

fn proofReferenceApplicationAt(
    self: anytype,
    offset: usize,
) ?ProofApplicationInfo {
    for (self.proof_applications) |app| {
        const range = app.refs_span orelse continue;
        if (offset >= range.start and offset <= range.end) return app;
    }
    return null;
}

fn ruleResolutionAt(
    self: anytype,
    block_index: usize,
    name: []const u8,
    use_start: usize,
) ?RuleResolution {
    var best: ?ProofRuleDecl = null;
    for (self.proof_rules) |rule| {
        if (!std.mem.eql(u8, rule.name, name)) continue;
        if (rule.available_start > use_start) continue;
        if (best == null or rule.available_start > best.?.available_start) {
            best = rule;
        }
    }
    if (best) |rule| {
        return .{ .decl_index = rule.decl_index, .available = true };
    }
    const decl_index = self.decl_by_name.get(name) orelse return null;
    const decl = self.declarations[decl_index];
    switch (decl.kind) {
        .axiom, .theorem => {},
        else => return null,
    }
    return .{
        .decl_index = decl_index,
        .available = globalRuleAvailable(self, block_index, decl),
    };
}

fn globalRuleAvailable(
    self: anytype,
    block_index: usize,
    decl: Declaration,
) bool {
    const bound = self.proof_blocks[block_index].global_available_before;
    if (bound) |before| return decl.name_range.start < before;
    return true;
}
const AnnotationDirective = struct {
    label: []const u8,
    detail: []const u8,
    sort_text: []const u8,
};

const annotation_directives = [_]AnnotationDirective{
    .{ .label = "@vars", .detail = "sort variable pool", .sort_text = "10 00" },
    .{ .label = "@relation", .detail = "rewrite relation", .sort_text = "10 01" },
    .{ .label = "@rewrite", .detail = "rewrite rule", .sort_text = "10 02" },
    .{ .label = "@congr", .detail = "congruence rule", .sort_text = "10 03" },
    .{ .label = "@acui", .detail = "ACUI metadata", .sort_text = "10 04" },
    .{ .label = "@view", .detail = "view theorem", .sort_text = "10 05" },
    .{ .label = "@recover", .detail = "recovery theorem", .sort_text = "10 06" },
    .{ .label = "@abstract", .detail = "abstract theorem", .sort_text = "10 07" },
    .{ .label = "@fresh", .detail = "freshness theorem", .sort_text = "10 08" },
    .{ .label = "@hole", .detail = "proof hole", .sort_text = "10 09" },
    .{ .label = "@auto", .detail = "search automation", .sort_text = "10 10" },
    .{ .label = "@freshen", .detail = "fresh-binder repair", .sort_text = "10 11" },
    .{ .label = "@alpha", .detail = "bound-variable renaming rule", .sort_text = "10 12" },
    .{ .label = "@fallback", .detail = "search fallback rule", .sort_text = "10 13" },
    .{ .label = "@conversion", .detail = "conversion? equation", .sort_text = "10 14" },
    .{ .label = "@compute", .detail = "directed computation rule", .sort_text = "10 15" },
};

const CompletionItemSeed = struct {
    label: []const u8,
    kind: CompletionKind,
    detail: []const u8,
    sort_text: []const u8,
};

const top_level_keywords = [_]CompletionItemSeed{
    .{ .label = "sort", .kind = .keyword, .detail = "sort declaration", .sort_text = "10 00" },
    .{ .label = "term", .kind = .keyword, .detail = "term declaration", .sort_text = "10 01" },
    .{ .label = "def", .kind = .keyword, .detail = "definition", .sort_text = "10 02" },
    .{ .label = "axiom", .kind = .keyword, .detail = "axiom", .sort_text = "10 03" },
    .{ .label = "theorem", .kind = .keyword, .detail = "theorem", .sort_text = "10 04" },
    .{ .label = "notation", .kind = .keyword, .detail = "notation", .sort_text = "10 05" },
    .{ .label = "prefix", .kind = .keyword, .detail = "prefix notation", .sort_text = "10 06" },
    .{ .label = "infixl", .kind = .keyword, .detail = "left infix", .sort_text = "10 07" },
    .{ .label = "infixr", .kind = .keyword, .detail = "right infix", .sort_text = "10 08" },
    .{ .label = "delimiter", .kind = .keyword, .detail = "delimiter", .sort_text = "10 09" },
    .{ .label = "pub", .kind = .modifier, .detail = "public", .sort_text = "10 10" },
    .{ .label = "pure", .kind = .modifier, .detail = "pure", .sort_text = "10 11" },
    .{ .label = "strict", .kind = .modifier, .detail = "strict", .sort_text = "10 12" },
    .{ .label = "provable", .kind = .modifier, .detail = "provable", .sort_text = "10 13" },
    .{ .label = "free", .kind = .modifier, .detail = "free", .sort_text = "10 14" },
};

fn appendAnnotationCompletions(
    list: *std.ArrayListUnmanaged(CompletionItem),
    allocator: std.mem.Allocator,
    replacement: SourceRange,
) !void {
    for (annotation_directives) |directive| {
        try list.append(allocator, .{
            .label = directive.label,
            .kind = .annotation,
            .detail = directive.detail,
            .replacement = replacement,
            .replacement_text = directive.label,
            .sort_text = directive.sort_text,
        });
    }
}

fn appendKeywordCompletions(
    list: *std.ArrayListUnmanaged(CompletionItem),
    allocator: std.mem.Allocator,
    replacement: SourceRange,
) !void {
    for (top_level_keywords) |keyword| {
        try list.append(allocator, .{
            .label = keyword.label,
            .kind = keyword.kind,
            .detail = keyword.detail,
            .replacement = replacement,
            .replacement_text = keyword.label,
            .sort_text = keyword.sort_text,
        });
    }
}

pub const sort_group_local_binder = "00";
pub const sort_group_proof_reference = "01";
pub const sort_group_search_tactic = "02";
pub const sort_group_proof_lemma = "03";
pub const sort_group_global_rule = "04";
pub const sort_group_notation_alias = "05";
pub const sort_group_notation_token = "06";
pub const sort_group_notation_snippet = "07";
pub const sort_group_term = "08";
pub const sort_group_sort = "09";
pub const sort_group_keyword = "10";

pub fn completionSortText(
    allocator: std.mem.Allocator,
    group: []const u8,
    ordinal: usize,
    label: []const u8,
) ![]const u8 {
    return try std.fmt.allocPrint(
        allocator,
        "{s} {d:0>10} {s}",
        .{ group, ordinal, label },
    );
}

fn globalDeclarationSortText(decl: Declaration) []const u8 {
    return decl.sort_text;
}

fn notationCompletionSortText(
    notation: NotationCompletionDecl,
    decl: Declaration,
    replacement_fragment: []const u8,
) []const u8 {
    if (completionFragmentMatchesAlias(
        replacement_fragment,
        decl.name,
        notation.token,
    )) {
        return notation.alias_sort_text;
    }
    return notation.token_sort_text;
}

fn notationSnippetSortText(
    notation: NotationCompletionDecl,
    _: Declaration,
) []const u8 {
    return notation.snippet_sort_text orelse notation.token_sort_text;
}

fn notationFilterText(
    notation: NotationCompletionDecl,
    decl: Declaration,
    replacement_fragment: []const u8,
) []const u8 {
    if (completionFragmentMatchesAlias(
        replacement_fragment,
        decl.name,
        notation.token,
    )) {
        return notation.alias_filter_text;
    }
    return notation.filter_text;
}

fn notationSnippetFilterText(
    notation: NotationCompletionDecl,
    decl: Declaration,
    replacement_fragment: []const u8,
) []const u8 {
    if (completionFragmentMatchesAlias(
        replacement_fragment,
        decl.name,
        notation.token,
    )) {
        return notation.snippet_alias_filter_text orelse
            notation.alias_filter_text;
    }
    return notation.snippet_filter_text orelse notation.filter_text;
}

fn replacementFragment(
    self: anytype,
    replacement: SourceRange,
) []const u8 {
    const text = self.textForDocument(replacement.document) orelse return "";
    if (replacement.start > replacement.end or replacement.end > text.len) {
        return "";
    }
    return text[replacement.start..replacement.end];
}

fn completionFragmentMatchesAlias(
    fragment: []const u8,
    decl_name: []const u8,
    token: []const u8,
) bool {
    if (fragment.len == 0) return false;
    if (fragment.len > decl_name.len) return false;
    if (std.mem.eql(u8, fragment, token)) return false;
    return std.mem.startsWith(u8, decl_name, fragment);
}

pub fn sortGroupForDeclaration(kind: DeclarationKind) []const u8 {
    return switch (kind) {
        .sort => sort_group_sort,
        .term, .def => sort_group_term,
        .axiom, .theorem => sort_group_global_rule,
        .lemma => sort_group_proof_lemma,
        .proof_line => sort_group_proof_reference,
        .sort_var => sort_group_local_binder,
    };
}

fn identifierCompletionReplacementRange(
    document: DocumentId,
    text: []const u8,
    offset: usize,
    placeholder_position: bool,
) SourceRange {
    var start = offset;
    while (start > 0 and
        tokenChar(text[start - 1], placeholder_position)) start -= 1;
    var end = offset;
    while (end < text.len and tokenChar(text[end], placeholder_position)) {
        end += 1;
    }
    return .{ .document = document, .start = start, .end = end };
}

fn tokenChar(ch: u8, placeholder_position: bool) bool {
    return completionTokenChar(ch) or (placeholder_position and ch == '?');
}

fn mathCompletionReplacementRange(
    document: DocumentId,
    text: []const u8,
    math: SourceSpan,
    offset: usize,
    left_delims: [256]bool,
    right_delims: [256]bool,
) SourceRange {
    const inner_start = @min(math.start + 1, text.len);
    const raw_inner_end = if (math.end > math.start and
        math.end <= text.len and text[math.end - 1] == '$')
        math.end - 1
    else
        math.end;
    const inner_end = @max(inner_start, @min(raw_inner_end, text.len));
    const safe_offset = @min(@max(offset, inner_start), inner_end);
    const inner = text[inner_start..inner_end];
    const rel_offset = safe_offset - inner_start;
    var cursor = MathTokenCursor{
        .src = inner,
        .left_delims = left_delims,
        .right_delims = right_delims,
    };
    while (cursor.next()) |token| {
        if (rel_offset >= token.start and rel_offset <= token.end) {
            return .{
                .document = document,
                .start = inner_start + token.start,
                .end = inner_start + token.end,
            };
        }
    }
    return .{
        .document = document,
        .start = safe_offset,
        .end = safe_offset,
    };
}

fn completionTokenChar(ch: u8) bool {
    return isIdentChar(ch) or ch == '@' or ch == '#';
}

fn annotationContextAt(text: []const u8, offset: usize) bool {
    const start = lineStart(text, offset);
    if (!startsLineComment(text, start)) return false;
    var pos = start + 2;
    while (pos < offset and pos < text.len and text[pos] == ' ') pos += 1;
    return pos < text.len and text[pos] == '|';
}

fn lineCommentContextAt(text: []const u8, offset: usize) bool {
    const start = lineStart(text, offset);
    const safe_offset = @min(offset, text.len);
    var pos = start;
    while (pos < safe_offset and pos + 1 < text.len) : (pos += 1) {
        if (text[pos] == '\n') return false;
        if (startsLineComment(text, pos)) return true;
    }
    return false;
}

fn mathStringAt(text: []const u8, offset: usize) ?SourceSpan {
    var pos: usize = 0;
    while (pos < text.len) {
        if (startsLineComment(text, pos)) {
            pos = lineEnd(text, pos);
            continue;
        }
        if (text[pos] != '$') {
            pos += 1;
            continue;
        }
        const start = pos;
        pos += 1;
        const inner_start = pos;
        while (pos < text.len and text[pos] != '$') pos += 1;
        const inner_end = pos;
        if (offset >= inner_start and offset <= inner_end) {
            return .{
                .start = start,
                .end = if (pos < text.len) pos + 1 else pos,
            };
        }
        if (pos < text.len) pos += 1;
    }
    return null;
}

fn mm0SortContextAt(text: []const u8, offset: usize) bool {
    const start = statementStartBefore(text, offset);
    var token_start = @min(offset, text.len);
    while (token_start > start and completionTokenChar(text[token_start - 1])) {
        token_start -= 1;
    }
    const before = previousNonSpace(text, start, token_start) orelse return false;
    if (text[before] == ':') return true;
    return before > start and text[before] == ',' and
        hasColonSince(text, start, before);
}

fn mm0ReferenceContextAt(text: []const u8, offset: usize) bool {
    const start = statementStartBefore(text, offset);
    const prefix = text[start..offset];
    return std.mem.indexOf(u8, prefix, "notation") != null or
        std.mem.indexOf(u8, prefix, "prefix") != null or
        std.mem.indexOf(u8, prefix, "infixl") != null or
        std.mem.indexOf(u8, prefix, "infixr") != null;
}

fn mm0TopLevelContextAt(text: []const u8, offset: usize) bool {
    const start = statementStartBefore(text, offset);
    var pos = start;
    while (pos < offset) {
        if (isMathWhitespace(text[pos])) {
            pos += 1;
            continue;
        }
        if (startsLineComment(text, pos)) {
            pos = lineEnd(text, pos);
            continue;
        }
        if (isIdentChar(text[pos])) {
            var end = pos + 1;
            while (end < offset and isIdentChar(text[end])) end += 1;
            if (isTopLevelModifier(text[pos..end])) {
                pos = end;
                continue;
            }
        }
        return rangeTouchesCurrentToken(text, pos, offset);
    }
    return true;
}

fn proofLineMathContextAt(text: []const u8, offset: usize) bool {
    const start = lineStart(text, offset);
    const end = lineEnd(text, offset);
    const line = text[start..end];
    const colon = std.mem.indexOfScalar(u8, line, ':') orelse return false;
    const by = std.mem.indexOf(u8, line, " by") orelse return false;
    return colon < by;
}

fn proofHeaderContextAt(text: []const u8, offset: usize) bool {
    const start = lineStart(text, offset);
    const end = lineEnd(text, offset);
    const line = text[start..end];
    if (std.mem.indexOfScalar(u8, line, ':') != null) return false;
    if (std.mem.indexOf(u8, line, "by") != null) return false;
    if (lineLooksUnderline(line)) return false;
    const prev_end = if (start == 0) 0 else start - 1;
    const prev_start = lineStart(text, prev_end);
    if (prev_start < prev_end and lineLooksUnderline(text[prev_start..prev_end])) {
        return false;
    }
    return true;
}

fn proofRuleContextAt(text: []const u8, offset: usize) bool {
    const start = lineStart(text, offset);
    const prefix = text[start..offset];
    const by_pos = std.mem.lastIndexOf(u8, prefix, "by") orelse return false;
    if (by_pos > 0 and isIdentChar(prefix[by_pos - 1])) return false;
    const after = by_pos + 2;
    if (after < prefix.len and isIdentChar(prefix[after])) return false;
    const suffix = prefix[after..];
    if (std.mem.lastIndexOfScalar(u8, suffix, '[')) |open| {
        if (std.mem.lastIndexOfScalar(u8, suffix, ']')) |close| {
            if (close > open) return false;
        }
        return false;
    }
    if (std.mem.lastIndexOfScalar(u8, suffix, '(')) |open| {
        if (std.mem.lastIndexOfScalar(u8, suffix, ')')) |close| {
            if (close > open) return true;
        }
        return false;
    }
    return true;
}

fn appendNotationSnippetCompletion(
    list: *std.ArrayListUnmanaged(CompletionItem),
    allocator: std.mem.Allocator,
    replacement: SourceRange,
    notation: NotationCompletionDecl,
    decl: Declaration,
    replacement_fragment: []const u8,
) !void {
    const snippet = notation.snippet_text orelse return;
    if (completionAlreadyHasSnippet(list.items, replacement, snippet)) return;
    try list.append(allocator, .{
        .label = notation.snippet_label orelse notation.token,
        .kind = .snippet,
        .detail = notation.detail,
        .documentation_markdown = decl.markdown,
        .replacement = replacement,
        .replacement_text = notation.token,
        .snippet_replacement_text = snippet,
        .filter_text = notationSnippetFilterText(
            notation,
            decl,
            replacement_fragment,
        ),
        .sort_text = notationSnippetSortText(notation, decl),
    });
}

fn completionAlreadyInserts(
    items: []const CompletionItem,
    replacement: SourceRange,
    replacement_text: []const u8,
) bool {
    for (items) |item| {
        if (item.replacement.document != replacement.document or
            item.replacement.start != replacement.start or
            item.replacement.end != replacement.end)
        {
            continue;
        }
        if (std.mem.eql(u8, item.replacement_text, replacement_text)) {
            return true;
        }
    }
    return false;
}

fn completionAlreadyHasSnippet(
    items: []const CompletionItem,
    replacement: SourceRange,
    snippet_text: []const u8,
) bool {
    for (items) |item| {
        if (item.replacement.document != replacement.document or
            item.replacement.start != replacement.start or
            item.replacement.end != replacement.end)
        {
            continue;
        }
        const other = item.snippet_replacement_text orelse continue;
        if (std.mem.eql(u8, other, snippet_text)) return true;
    }
    return false;
}

fn declarationKindIn(kind: DeclarationKind, kinds: []const DeclarationKind) bool {
    for (kinds) |allowed| {
        if (kind == allowed) return true;
    }
    return false;
}

fn globalDeclarationAvailable(
    decl: Declaration,
    document: DocumentId,
    use_start: usize,
    available_before: ?usize,
) bool {
    return switch (document) {
        .mm0 => decl.name_range.document == .mm0 and
            decl.name_range.start <= use_start,
        .proof => if (decl.name_range.document == .proof)
            decl.name_range.start <= use_start
        else if (available_before) |before|
            decl.name_range.start < before
        else
            true,
    };
}

fn completionKindForDeclaration(kind: DeclarationKind) CompletionKind {
    return switch (kind) {
        .sort => .sort,
        .term => .term,
        .def => .def,
        .axiom => .axiom,
        .theorem => .theorem,
        .lemma => .lemma,
        .proof_line => .proof_line,
        .sort_var => .binder,
    };
}

pub fn declarationKindName(kind: DeclarationKind) []const u8 {
    return switch (kind) {
        .sort => "sort",
        .term => "term",
        .def => "def",
        .axiom => "axiom",
        .theorem => "theorem",
        .lemma => "lemma",
        .proof_line => "proof line",
        .sort_var => "sort variable",
    };
}

fn isTopLevelModifier(word: []const u8) bool {
    return std.mem.eql(u8, word, "pub") or
        std.mem.eql(u8, word, "pure") or
        std.mem.eql(u8, word, "strict") or
        std.mem.eql(u8, word, "provable") or
        std.mem.eql(u8, word, "free");
}

fn rangeTouchesCurrentToken(text: []const u8, pos: usize, offset: usize) bool {
    if (pos >= text.len or offset > text.len) return false;
    const repl = identifierCompletionReplacementRange(.mm0, text, offset, false);
    return pos >= repl.start and pos <= repl.end;
}

fn hasColonSince(text: []const u8, start: usize, end: usize) bool {
    var pos = start;
    while (pos < end) : (pos += 1) {
        if (text[pos] == ':') return true;
        if (text[pos] == ';') return false;
    }
    return false;
}

fn previousNonSpace(text: []const u8, start: usize, offset: usize) ?usize {
    var pos = @min(offset, text.len);
    while (pos > start) {
        pos -= 1;
        if (!isMathWhitespace(text[pos])) return pos;
    }
    return null;
}

fn statementStartBefore(text: []const u8, offset: usize) usize {
    var pos = @min(offset, text.len);
    while (pos > 0) {
        pos -= 1;
        if (text[pos] == ';') return pos + 1;
    }
    return 0;
}

fn lineStart(text: []const u8, offset: usize) usize {
    var pos = @min(offset, text.len);
    while (pos > 0 and text[pos - 1] != '\n') pos -= 1;
    return pos;
}

fn lineEnd(text: []const u8, offset: usize) usize {
    var pos = @min(offset, text.len);
    while (pos < text.len and text[pos] != '\n') pos += 1;
    return pos;
}

fn lineLooksUnderline(line: []const u8) bool {
    const trimmed = std.mem.trim(u8, line, " \t\r\n");
    if (trimmed.len == 0) return false;
    for (trimmed) |ch| {
        if (ch != '-') return false;
    }
    return true;
}
