//! Indexing one proof block's body. The snapshot indexes headers, and all
//! of the `.mm0` text, when it is built; a body is indexed when a request
//! needs it.
const std = @import("std");
const proof_script = @import("../proof_script.zig");

const Snapshot = @import("index.zig").Snapshot;
const markdown = @import("markdown.zig");
const math_builder = @import("builder_math.zig");
const model = @import("model.zig");
const completion = @import("completion.zig");
const source = @import("source.zig");
const support = @import("builder_support.zig");
const Types = @import("types.zig");

const Declaration = Types.Declaration;
const NavigationSymbol = model.NavigationSymbol;
const ProofApplicationInfo = model.ProofApplicationInfo;
const ProofBlockInfo = model.ProofBlockInfo;
const ProofBody = model.ProofBody;
const ProofLineDecl = model.ProofLineDecl;
const RuleResolution = model.RuleResolution;

const completionSortText = completion.completionSortText;
const sort_group_proof_reference = completion.sort_group_proof_reference;

const ambiguousHypMarkdown = markdown.ambiguousHypMarkdown;
const binderMarkdown = markdown.binderMarkdown;
const hypRefMarkdown = markdown.hypRefMarkdown;
const namedHypMarkdown = markdown.namedHypMarkdown;
const proofLineMarkdown = markdown.proofLineMarkdown;
const unknownBindingMarkdown = markdown.unknownBindingMarkdown;
const unknownHypMarkdown = markdown.unknownHypMarkdown;
const unknownNamedHypMarkdown = markdown.unknownNamedHypMarkdown;
const unknownLineMarkdown = markdown.unknownLineMarkdown;
const unknownRuleMarkdown = markdown.unknownRuleMarkdown;
const unresolvedBindingMarkdown = markdown.unresolvedBindingMarkdown;

const findBinder = support.findBinder;
const proofSpanRange = support.proofSpanRange;

/// The index of block `block_index`'s body. The result lives in `arena`.
pub fn indexBody(
    arena: std.mem.Allocator,
    snapshot: *const Snapshot,
    block_index: usize,
) std.mem.Allocator.Error!ProofBody {
    const source_block = snapshot.proof_blocks[block_index].source;
    const block = try source_block.withLines(arena, snapshot.proof_text.?);
    var builder: BodyBuilder = .{
        .allocator = arena,
        .index = snapshot,
        .block_index = block_index,
    };
    for (block.lines) |line| try builder.addProofLine(line);
    return .{
        .symbols = builder.symbols.items,
        .lines = builder.lines.items,
        .applications = builder.applications.items,
    };
}

/// Names resolve to what the block sees: what was declared before it.
const BodyBuilder = struct {
    allocator: std.mem.Allocator,
    index: *const Snapshot,
    block_index: usize,
    symbols: std.ArrayListUnmanaged(NavigationSymbol) = .empty,
    lines: std.ArrayListUnmanaged(ProofLineDecl) = .empty,
    applications: std.ArrayListUnmanaged(ProofApplicationInfo) = .empty,

    fn blockInfo(self: *const BodyBuilder) ProofBlockInfo {
        return self.index.proof_blocks[self.block_index];
    }

    pub fn declaration(self: *const BodyBuilder, decl_index: usize) Declaration {
        return self.index.declarations[decl_index];
    }

    pub fn declNamed(self: *const BodyBuilder, name: []const u8) ?usize {
        return self.index.decl_by_name.seenBy(name, self.block_index);
    }

    pub fn declWithNotation(self: *const BodyBuilder, token: []const u8) ?usize {
        return self.index.notation_by_token.seenBy(token, self.block_index);
    }

    pub fn sortVarDecl(self: *const BodyBuilder, token: []const u8) ?usize {
        return self.index.sort_var_by_token.get(token);
    }

    pub fn mathTokens(self: *const BodyBuilder, math: []const u8) source.MathTokenCursor {
        return .{
            .src = math,
            .left_delims = self.index.left_delims,
            .right_delims = self.index.right_delims,
        };
    }

    pub fn addSymbol(self: *BodyBuilder, symbol: NavigationSymbol) !void {
        try self.symbols.append(self.allocator, symbol);
    }

    /// Math in the scope of the block's own declaration.
    fn indexMath(self: *BodyBuilder, math: proof_script.MathString) !void {
        const block = self.blockInfo();
        try math_builder.indexMathString(
            self,
            .proof,
            math.text,
            math.span.start + 1,
            block.decl_index,
            true,
            block.global_available_before,
        );
    }

    fn addProofLine(
        self: *BodyBuilder,
        line: proof_script.ProofLine,
    ) !void {
        const name_range = proofSpanRange(line.label_span);
        const line_markdown = try proofLineMarkdown(self.allocator, line);
        try self.addSymbol(.{
            .source_range = name_range,
            .target_range = name_range,
            .markdown = line_markdown,
        });
        // An incomplete line has no application to speak of — its placeholder
        // would index as an unknown rule and hover as one.
        if (!line.incomplete) {
            try self.indexRuleApplication(line.application, line.span.start);
        }
        try self.indexMath(line.assertion);
        // Last, so that the line cannot refer to itself.
        try self.lines.append(self.allocator, .{
            .name = line.label,
            .name_range = name_range,
            .markdown = line_markdown,
            .line_start = line.span.start,
            .sort_text = try completionSortText(
                self.allocator,
                sort_group_proof_reference,
                line.span.start,
                line.label,
            ),
        });
    }

    fn indexRuleApplication(
        self: *BodyBuilder,
        app: proof_script.RuleApplication,
        line_start: usize,
    ) !void {
        try self.applications.append(self.allocator, .{
            .block_index = self.block_index,
            .rule_name = app.rule_name,
            .rule_span = proofSpanRange(app.rule_span),
            .binding_list_span = if (app.binding_list_span) |span|
                proofSpanRange(span)
            else
                null,
            .refs_span = if (app.refs_span) |span| proofSpanRange(span) else null,
            .span = proofSpanRange(app.span),
            .use_start = app.rule_span.start,
            .line_start = line_start,
        });
        if (proof_script.isSorryRuleName(app.rule_name)) {
            try self.addSymbol(.{
                .source_range = proofSpanRange(app.rule_span),
                .target_range = null,
                .markdown = markdown.sorry_markdown,
            });
            return;
        }
        if (proof_script.isOpenGoalRuleName(app.rule_name)) {
            try self.addSymbol(.{
                .source_range = proofSpanRange(app.rule_span),
                .target_range = null,
                .markdown = markdown.open_goal_markdown,
            });
            return;
        }
        const maybe_rule = self.resolveRule(app.rule_name, app.rule_span.start);
        if (maybe_rule) |rule| {
            const decl = self.declaration(rule.decl_index);
            try self.addSymbol(.{
                .source_range = proofSpanRange(app.rule_span),
                .target_range = if (rule.available) decl.name_range else null,
                .markdown = decl.markdown,
            });
            try self.indexArgBindings(app, rule.decl_index, rule.available);
        } else {
            try self.addSymbol(.{
                .source_range = proofSpanRange(app.rule_span),
                .target_range = null,
                .markdown = try unknownRuleMarkdown(
                    self.allocator,
                    app.rule_name,
                ),
            });
            try self.indexUnknownArgBindings(app);
        }

        for (app.arg_bindings) |binding| try self.indexMath(binding.formula);

        for (app.refs) |ref| {
            switch (ref) {
                .hyp => |hyp| try self.addHypRef(hyp),
                .line => |line| try self.addLineRef(line),
                .application => |child| {
                    try self.indexRuleApplication(child, line_start);
                },
            }
        }
    }

    fn indexArgBindings(
        self: *BodyBuilder,
        app: proof_script.RuleApplication,
        decl_index: usize,
        rule_available: bool,
    ) !void {
        const decl = self.declaration(decl_index);
        for (app.arg_bindings) |binding| {
            const binder = findBinder(decl, binding.name) orelse {
                try self.addSymbol(.{
                    .source_range = proofSpanRange(binding.name_span),
                    .target_range = null,
                    .markdown = try unknownBindingMarkdown(
                        self.allocator,
                        binding.name,
                        decl.name,
                    ),
                });
                continue;
            };
            try self.addSymbol(.{
                .source_range = proofSpanRange(binding.name_span),
                .target_range = if (rule_available)
                    binder.range orelse decl.name_range
                else
                    null,
                .markdown = try binderMarkdown(
                    self.allocator,
                    decl,
                    binder,
                ),
            });
        }
    }

    fn indexUnknownArgBindings(
        self: *BodyBuilder,
        app: proof_script.RuleApplication,
    ) !void {
        for (app.arg_bindings) |binding| {
            try self.addSymbol(.{
                .source_range = proofSpanRange(binding.name_span),
                .target_range = null,
                .markdown = try unresolvedBindingMarkdown(
                    self.allocator,
                    binding.name,
                    app.rule_name,
                ),
            });
        }
    }

    fn addHypRef(
        self: *BodyBuilder,
        hyp: proof_script.HypRef,
    ) !void {
        const block = self.blockInfo();
        if (hyp.name) |name| return self.addNamedHypRef(hyp, name);
        if (hyp.index == 0 or
            (block.hyp_count_known and hyp.index > block.hyp_count))
        {
            try self.addSymbol(.{
                .source_range = proofSpanRange(hyp.span),
                .target_range = null,
                .markdown = try unknownHypMarkdown(
                    self.allocator,
                    block.source.name,
                    hyp.index,
                ),
            });
            return;
        }
        const decl_index = block.decl_index orelse {
            try self.addSymbol(.{
                .source_range = proofSpanRange(hyp.span),
                .target_range = null,
                .markdown = try unknownHypMarkdown(
                    self.allocator,
                    block.source.name,
                    hyp.index,
                ),
            });
            return;
        };
        const decl = self.declaration(decl_index);
        const hyp_decl = if (hyp.index <= decl.hypotheses.len)
            decl.hypotheses[hyp.index - 1]
        else
            null;
        try self.addSymbol(.{
            .source_range = proofSpanRange(hyp.span),
            .target_range = if (hyp_decl) |item| item.range else decl.name_range,
            .markdown = try hypRefMarkdown(
                self.allocator,
                block.source.name,
                null,
                hyp.index,
                block.hyp_count,
                block.hyp_count_known,
                if (hyp_decl) |item| item.text else null,
            ),
        });
    }

    fn addNamedHypRef(
        self: *BodyBuilder,
        hyp: proof_script.HypRef,
        name: []const u8,
    ) !void {
        const block = self.blockInfo();
        const source_range = proofSpanRange(hyp.span);
        const decl_index = block.decl_index orelse {
            try self.addSymbol(.{
                .source_range = source_range,
                .target_range = null,
                .markdown = try namedHypMarkdown(self.allocator, block.source.name, name),
            });
            return;
        };
        const decl = self.declaration(decl_index);
        // Validate only against a complete table: when the header scan came up
        // short, a missed name is indistinguishable from missing data, so fall
        // back to naming the ref without judging it.
        if (!block.hyp_count_known or decl.hypotheses.len < block.hyp_count) {
            try self.addSymbol(.{
                .source_range = source_range,
                .target_range = decl.name_range,
                .markdown = try namedHypMarkdown(self.allocator, block.source.name, name),
            });
            return;
        }
        const hyp_names = try model.hypNamesFromHypotheses(
            self.allocator,
            decl.hypotheses,
        );
        defer self.allocator.free(hyp_names);
        const index = switch (proof_script.resolveHypRef(
            hyp_names,
            decl.hypotheses.len,
            hyp,
        )) {
            .ambiguous => {
                try self.addSymbol(.{
                    .source_range = source_range,
                    .target_range = null,
                    .markdown = try ambiguousHypMarkdown(
                        self.allocator,
                        block.source.name,
                        name,
                    ),
                });
                return;
            },
            .unknown => {
                try self.addSymbol(.{
                    .source_range = source_range,
                    .target_range = null,
                    .markdown = try unknownNamedHypMarkdown(
                        self.allocator,
                        block.source.name,
                        name,
                    ),
                });
                return;
            },
            .index => |idx| idx,
        };
        const item = decl.hypotheses[index];
        try self.addSymbol(.{
            .source_range = source_range,
            .target_range = item.name_range orelse item.range,
            .markdown = try hypRefMarkdown(
                self.allocator,
                block.source.name,
                name,
                index + 1,
                block.hyp_count,
                block.hyp_count_known,
                item.text,
            ),
        });
    }

    fn addLineRef(self: *BodyBuilder, ref: proof_script.LineRef) !void {
        const line = self.resolveLine(ref.label) orelse {
            try self.addSymbol(.{
                .source_range = proofSpanRange(ref.span),
                .target_range = null,
                .markdown = try unknownLineMarkdown(self.allocator, ref.label),
            });
            return;
        };
        try self.addSymbol(.{
            .source_range = proofSpanRange(ref.span),
            .target_range = line.name_range,
            .markdown = line.markdown,
        });
    }

    fn resolveRule(
        self: *const BodyBuilder,
        name: []const u8,
        use_start: usize,
    ) ?RuleResolution {
        if (self.index.proof_rule_by_name.seenBy(name, self.block_index)) |index| {
            const rule = self.index.proof_rules[index];
            if (rule.available_start <= use_start) {
                return .{ .decl_index = rule.decl_index, .available = true };
            }
        }
        return self.globalRuleResolution(name);
    }

    fn globalRuleResolution(
        self: *const BodyBuilder,
        name: []const u8,
    ) ?RuleResolution {
        const decl_index = self.declNamed(name) orelse return null;
        const decl = self.declaration(decl_index);
        switch (decl.kind) {
            .axiom, .theorem => {},
            else => return null,
        }
        const bound = self.blockInfo().global_available_before;
        const available = if (bound) |before|
            decl.name_range.start < before
        else
            true;
        return .{ .decl_index = decl_index, .available = available };
    }

    /// The nearest earlier line labelled `label`.
    fn resolveLine(self: *const BodyBuilder, label: []const u8) ?ProofLineDecl {
        var index = self.lines.items.len;
        while (index > 0) {
            index -= 1;
            const line = self.lines.items[index];
            if (std.mem.eql(u8, line.name, label)) return line;
        }
        return null;
    }
};
