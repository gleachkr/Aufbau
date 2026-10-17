const std = @import("std");
const parse = @import("../parse_recovery.zig");
const proof_script = @import("../proof_script.zig");

const source = @import("source.zig");
const markdown = @import("markdown.zig");
const Types = @import("types.zig");
const model = @import("model.zig");
const completion = @import("completion.zig");
const notation = @import("notation.zig");
const support = @import("builder_support.zig");

const DocumentId = Types.DocumentId;
const SourceRange = Types.SourceRange;
const OutlineSymbol = Types.OutlineSymbol;
const DeclarationKind = Types.DeclarationKind;
const Declaration = Types.Declaration;
const BinderDecl = Types.BinderDecl;

const StatementIterator = source.StatementIterator;
const nextAnnotationToken = source.nextAnnotationToken;
const sourceRangeFromSlice = source.sourceRangeFromSlice;

const sortMarkdown = markdown.sortMarkdown;
const termMarkdown = markdown.termMarkdown;
const assertionMarkdown = markdown.assertionMarkdown;
const sortVarMarkdown = markdown.sortVarMarkdown;
const binderMarkdown = markdown.binderMarkdown;

const NavigationSymbol = model.NavigationSymbol;
const ProofBlockInfo = model.ProofBlockInfo;
const ProofRuleDecl = model.ProofRuleDecl;
const ProofLineDecl = model.ProofLineDecl;
const ProofApplicationInfo = model.ProofApplicationInfo;

const NotationCompletionDecl = notation.NotationCompletionDecl;

const completionSortText = completion.completionSortText;
const sortGroupForDeclaration = completion.sortGroupForDeclaration;

const nextStatementRangeForMm0Stmt = support.nextStatementRangeForMm0Stmt;
const mathSpanRange = support.mathSpanRange;
const proofSpanRange = support.proofSpanRange;
const proofMathTextSpan = support.proofMathTextSpan;
const targetRangeIfAvailable = support.targetRangeIfAvailable;
const targetRangeForUse = support.targetRangeForUse;
const isFatalIndexError = support.isFatalIndexError;
const hypothesesFromMm0Assertion = support.hypothesesFromMm0Assertion;
const bindersFromTerm = support.bindersFromTerm;
const bindersFromProofDef = support.bindersFromProofDef;
const bindersFromArgs = support.bindersFromArgs;
const completionArgsFromArgs = support.completionArgsFromArgs;
pub const Builder = struct {
    allocator: std.mem.Allocator,
    declarations: std.ArrayListUnmanaged(Declaration) = .empty,
    decl_by_name: std.StringHashMapUnmanaged(usize) = .empty,
    symbols: std.ArrayListUnmanaged(NavigationSymbol) = .empty,
    mm0_outline: std.ArrayListUnmanaged(OutlineSymbol) = .empty,
    proof_outline: std.ArrayListUnmanaged(OutlineSymbol) = .empty,
    proof_blocks: std.ArrayListUnmanaged(ProofBlockInfo) = .empty,
    proof_rules: std.ArrayListUnmanaged(ProofRuleDecl) = .empty,
    proof_lines: std.ArrayListUnmanaged(ProofLineDecl) = .empty,
    proof_applications: std.ArrayListUnmanaged(ProofApplicationInfo) = .empty,
    notations: std.ArrayListUnmanaged(NotationCompletionDecl) = .empty,
    notation_by_token: std.StringHashMapUnmanaged(usize) = .empty,
    sort_var_by_token: std.StringHashMapUnmanaged(usize) = .empty,
    sort_names: std.ArrayListUnmanaged([]const u8) = .empty,
    left_delims: [256]bool = @splat(false),
    right_delims: [256]bool = @splat(false),
    mm0_parser: ?parse.MM0Parser = null,
    /// The indexed texts; every range comes from a slice of one of them.
    mm0_text: []const u8 = "",
    proof_text: []const u8 = "",
    /// Whether every statement, proof item and line parsed. A rename needs
    /// every occurrence of a name, and an unparsed one is not indexed.
    complete: bool = true,
    /// Annotations of the document being indexed, indexed once all its
    /// declarations are known: one may name a rule declared after it.
    pending_annotations: std.ArrayListUnmanaged(PendingAnnotations) = .empty,

    const PendingAnnotations = struct {
        decl_index: usize,
        annotations: []const []const u8,
    };

    const proof = @import("builder_proof.zig");
    const notation_builder = @import("builder_notation.zig");
    const math_builder = @import("builder_math.zig");
    const names_builder = @import("builder_names.zig");

    pub const addProofBlock = proof.addProofBlock;
    pub const addTheoremBlockHeader = proof.addTheoremBlockHeader;
    pub const addLemmaBlockHeader = proof.addLemmaBlockHeader;
    pub const parseLemmaAssertion = proof.parseLemmaAssertion;
    pub const addProofLine = proof.addProofLine;
    pub const indexRuleApplication = proof.indexRuleApplication;
    pub const indexArgBindings = proof.indexArgBindings;
    pub const indexUnknownArgBindings = proof.indexUnknownArgBindings;
    pub const addHypRef = proof.addHypRef;
    pub const addLineRef = proof.addLineRef;
    pub const resolveRule = proof.resolveRule;
    pub const globalRuleResolution = proof.globalRuleResolution;
    pub const sortNameForId = proof.sortNameForId;
    pub const theoremDeclIndex = proof.theoremDeclIndex;
    pub const sortDeclIndex = proof.sortDeclIndex;
    pub const resolveLine = proof.resolveLine;

    pub const collectMm0Notation = notation_builder.collectMm0Notation;
    pub const collectNotationStatement =
        notation_builder.collectNotationStatement;
    pub const collectDelimiterStatement =
        notation_builder.collectDelimiterStatement;
    pub const registerDelimiterMath = notation_builder.registerDelimiterMath;
    pub const collectGeneralNotation = notation_builder.collectGeneralNotation;
    pub const addNotationMathToken = notation_builder.addNotationMathToken;
    pub const addNotationToken = notation_builder.addNotationToken;

    pub const indexMm0Math = math_builder.indexMm0Math;
    pub const declIndexForStatement = math_builder.declIndexForStatement;
    pub const indexLemmaHeaderMath = math_builder.indexLemmaHeaderMath;
    pub const indexProofMathString = math_builder.indexProofMathString;
    pub const indexRuleApplicationMath = math_builder.indexRuleApplicationMath;
    pub const indexMathString = math_builder.indexMathString;
    pub const indexMathStringIn = math_builder.indexMathStringIn;

    pub const indexSignature = names_builder.indexSignature;
    pub const indexAnnotations = names_builder.indexAnnotations;

    pub fn init(allocator: std.mem.Allocator) Builder {
        return .{ .allocator = allocator };
    }

    pub fn indexMm0(self: *Builder, text: []const u8) !void {
        self.mm0_text = text;
        var parser = parse.MM0Parser.init(text, self.allocator);
        var statements = StatementIterator.init(text);
        while (true) {
            const stmt = parser.next() catch |err| {
                if (isFatalIndexError(err)) return err;
                self.complete = false;
                break;
            };
            const concrete = stmt orelse break;
            try self.addStatement(
                concrete,
                text,
                nextStatementRangeForMm0Stmt(&statements, concrete),
                parser.last_annotations,
                parser.last_annotation_spans,
            );
        }
        self.mm0_parser = parser;
        try self.collectMm0Notation(text);
        try self.indexMm0Math(text);
        try self.indexPendingAnnotations(.mm0);
    }

    pub fn indexProof(self: *Builder, text: []const u8) !void {
        self.proof_text = text;
        // Index leniently: a line whose rule application is half-typed is the
        // normal state of a file being edited, and the strict parser drops the
        // whole block over it.
        var parser = proof_script.Parser.initLenient(self.allocator, text);
        var items = std.ArrayListUnmanaged(proof_script.TopLevelItem).empty;
        while (true) {
            const next = parser.nextItem() catch |err| {
                if (isFatalIndexError(err)) return err;
                self.complete = false;
                if (!parser.recoverToNextItemBoundary()) break;
                continue;
            };
            const item = next orelse break;
            try items.append(self.allocator, item);
        }

        for (items.items, 0..) |item, i| {
            switch (item) {
                .block => |block| try self.addProofBlock(
                    block,
                    self.globalAvailabilityForProofItem(items.items, i),
                ),
                .def => |def| try self.addProofDefItem(text, def),
                .notation => |local_notation| try self.addProofNotationItem(
                    text,
                    local_notation,
                ),
            }
        }
        try self.indexPendingAnnotations(.proof);
    }

    fn indexPendingAnnotations(self: *Builder, document: DocumentId) !void {
        for (self.pending_annotations.items) |pending| {
            try self.indexAnnotations(document, pending.decl_index, pending.annotations);
        }
        self.pending_annotations.clearRetainingCapacity();
    }

    fn globalAvailabilityForProofItem(
        self: *const Builder,
        items: []const proof_script.TopLevelItem,
        index: usize,
    ) ?usize {
        const item = items[index];
        switch (item) {
            .block => |block| {
                if (block.kind == .theorem) {
                    return self.theoremAvailabilityBound(block.name);
                }
            },
            .def, .notation => {},
        }

        var i = index + 1;
        while (i < items.len) : (i += 1) {
            const block = switch (items[i]) {
                .block => |block| block,
                .def, .notation => continue,
            };
            if (block.kind != .theorem) continue;
            return self.theoremAvailabilityBound(block.name);
        }
        return null;
    }

    fn theoremAvailabilityBound(
        self: *const Builder,
        name: []const u8,
    ) ?usize {
        const decl_index = self.theoremDeclIndex(name) orelse return null;
        return self.declarations.items[decl_index].name_range.start;
    }

    fn addStatement(
        self: *Builder,
        stmt: parse.MM0Stmt,
        text: []const u8,
        statement_range: SourceRange,
        annotations: []const []const u8,
        annotation_spans: []const parse.MathSpan,
    ) !void {
        switch (stmt) {
            .sort => |sort| {
                try self.sort_names.append(self.allocator, sort.name);
                _ = try self.addGlobalDeclaration(.{
                    .name = sort.name,
                    .kind = .sort,
                    .name_range = mathSpanRange(sort.name_span),
                    .markdown = try sortMarkdown(
                        self.allocator,
                        sort,
                        annotations,
                    ),
                });
                try self.addMm0Outline(.{
                    .name = sort.name,
                    .kind = .sort,
                    .range = statement_range,
                    .selection_range = mathSpanRange(sort.name_span),
                });
                try self.addSortVarAnnotations(
                    sort,
                    annotations,
                    annotation_spans,
                );
            },
            .term => |term| {
                const kind: DeclarationKind = if (term.is_def) .def else .term;
                const decl_index = try self.addGlobalDeclaration(.{
                    .name = term.name,
                    .kind = kind,
                    .name_range = mathSpanRange(term.name_span),
                    .markdown = try termMarkdown(
                        self.allocator,
                        text,
                        term,
                        annotations,
                    ),
                    .binders = try bindersFromTerm(
                        self.allocator,
                        .mm0,
                        text,
                        term,
                    ),
                    .completion_args = try completionArgsFromArgs(
                        self.allocator,
                        .mm0,
                        text,
                        term.arg_names,
                        term.args,
                    ),
                });
                try self.addMm0Outline(.{
                    .name = term.name,
                    .kind = kind,
                    .range = statement_range,
                    .selection_range = mathSpanRange(term.name_span),
                });
                try self.indexStatementSignature(
                    text,
                    statement_range,
                    term.name_span.end,
                    decl_index,
                );
                try self.deferAnnotations(decl_index, annotations);
            },
            .assertion => |assertion| {
                const kind: DeclarationKind = switch (assertion.kind) {
                    .axiom => .axiom,
                    .theorem => .theorem,
                };
                const decl_index = try self.addGlobalDeclaration(.{
                    .name = assertion.name,
                    .kind = kind,
                    .name_range = mathSpanRange(assertion.name_span),
                    .markdown = try assertionMarkdown(
                        self.allocator,
                        text,
                        assertion,
                        self.sortNameForId(assertion.concl.sort()),
                        annotations,
                    ),
                    .binders = try bindersFromArgs(
                        self.allocator,
                        .mm0,
                        text,
                        assertion.arg_names,
                        assertion.args,
                    ),
                    .completion_args = try completionArgsFromArgs(
                        self.allocator,
                        .mm0,
                        text,
                        assertion.arg_names,
                        assertion.args,
                    ),
                    .hyp_count = assertion.hyps.len,
                    .hypotheses = try hypothesesFromMm0Assertion(
                        self.allocator,
                        text,
                        assertion,
                    ),
                });
                try self.addMm0Outline(.{
                    .name = assertion.name,
                    .kind = kind,
                    .range = statement_range,
                    .selection_range = mathSpanRange(assertion.name_span),
                });
                try self.indexStatementSignature(
                    text,
                    statement_range,
                    assertion.name_span.end,
                    decl_index,
                );
                try self.deferAnnotations(decl_index, annotations);
            },
        }
    }

    fn addSortVarAnnotations(
        self: *Builder,
        sort: parse.SortStmt,
        annotations: []const []const u8,
        annotation_spans: []const parse.MathSpan,
    ) !void {
        for (annotations, 0..) |annotation, i| {
            if (i >= annotation_spans.len) continue;
            var pos: usize = 0;
            const directive = nextAnnotationToken(annotation, &pos) orelse {
                continue;
            };
            if (!std.mem.eql(u8, directive.text, "@vars")) continue;

            while (nextAnnotationToken(annotation, &pos)) |token| {
                const span = annotation_spans[i];
                try self.addSortVarDeclaration(
                    sort.name,
                    token.text,
                    .{
                        .document = .mm0,
                        .start = span.start + token.start,
                        .end = span.start + token.end,
                    },
                );
            }
        }
    }

    fn addSortVarDeclaration(
        self: *Builder,
        sort_name: []const u8,
        token: []const u8,
        range: SourceRange,
    ) !void {
        const decl_index = try self.addDeclaration(.{
            .name = token,
            .kind = .sort_var,
            .name_range = range,
            .markdown = try sortVarMarkdown(
                self.allocator,
                token,
                sort_name,
            ),
        });
        if (self.sort_var_by_token.get(token) == null) {
            try self.sort_var_by_token.put(
                self.allocator,
                token,
                decl_index,
            );
        }
    }

    fn addGlobalDeclaration(self: *Builder, decl: Declaration) !usize {
        const index = try self.addDeclaration(decl);
        try self.decl_by_name.put(self.allocator, decl.name, index);
        return index;
    }

    pub fn addDeclaration(self: *Builder, decl_arg: Declaration) !usize {
        var decl = decl_arg;
        if (decl.sort_text.len == 0) {
            decl.sort_text = try completionSortText(
                self.allocator,
                sortGroupForDeclaration(decl.kind),
                decl.name_range.start,
                decl.name,
            );
        }
        const index = self.declarations.items.len;
        try self.declarations.append(self.allocator, decl);
        try self.addSymbol(.{
            .source_range = decl.name_range,
            .target_range = decl.name_range,
            .markdown = decl.markdown,
        });
        for (decl.binders) |binder| {
            const range = binder.range orelse continue;
            try self.addSymbol(.{
                .source_range = range,
                .target_range = range,
                .markdown = try binderMarkdown(
                    self.allocator,
                    decl,
                    binder,
                ),
            });
        }
        for (decl.hypotheses, 1..) |hyp, ordinal| {
            const range = hyp.name_range orelse continue;
            try self.addSymbol(.{
                .source_range = range,
                .target_range = range,
                .markdown = try markdown.hypRefMarkdown(
                    self.allocator,
                    decl.name,
                    hyp.name,
                    ordinal,
                    decl.hyp_count,
                    true,
                    hyp.text,
                ),
            });
        }
        return index;
    }

    fn indexStatementSignature(
        self: *Builder,
        text: []const u8,
        statement_range: SourceRange,
        name_end: usize,
        decl_index: usize,
    ) !void {
        if (name_end > statement_range.end) return;
        _ = try self.indexSignature(
            .mm0,
            text[name_end..statement_range.end],
            decl_index,
            self.declarations.items[decl_index].binders,
        );
    }

    pub fn deferAnnotations(
        self: *Builder,
        decl_index: usize,
        annotations: []const []const u8,
    ) !void {
        if (annotations.len == 0) return;
        try self.pending_annotations.append(self.allocator, .{
            .decl_index = decl_index,
            // The parser frees its list at the next statement.
            .annotations = try self.allocator.dupe([]const u8, annotations),
        });
    }

    /// A sort named by `sort_name`, a slice of the `document` text.
    pub fn addSortUse(
        self: *Builder,
        document: DocumentId,
        sort_name: []const u8,
    ) !void {
        const range = self.rangeOf(document, sort_name) orelse return;
        const decl_index = self.sortDeclIndex(sort_name) orelse return;
        const decl = self.declarations.items[decl_index];
        try self.addSymbol(.{
            .source_range = range,
            .target_range = targetRangeForUse(decl, document, range.start, null),
            .markdown = decl.markdown,
        });
    }

    pub fn rangeOf(
        self: *const Builder,
        document: DocumentId,
        slice: []const u8,
    ) ?SourceRange {
        const text = switch (document) {
            .mm0 => self.mm0_text,
            .proof => self.proof_text,
        };
        return sourceRangeFromSlice(document, text, slice);
    }

    /// Binders visible in part of a declaration only: a `@view`'s own, or a
    /// definition filler's dummies.
    pub fn addLocalBinders(
        self: *Builder,
        decl_index: usize,
        binders: []const BinderDecl,
    ) !void {
        if (binders.len == 0) return;
        const decl = &self.declarations.items[decl_index];
        decl.local_binders = try std.mem.concat(
            self.allocator,
            BinderDecl,
            &.{ decl.local_binders, binders },
        );
    }

    pub fn addDeclarationNameUseIn(
        self: *Builder,
        document: DocumentId,
        text: []const u8,
        name: []const u8,
        decl_index: usize,
    ) !void {
        const range = sourceRangeFromSlice(document, text, name) orelse return;
        const decl = self.declarations.items[decl_index];
        try self.addSymbol(.{
            .source_range = range,
            .target_range = targetRangeIfAvailable(decl, range.start),
            .markdown = decl.markdown,
        });
    }

    pub fn addSymbol(self: *Builder, symbol: NavigationSymbol) !void {
        try self.symbols.append(self.allocator, symbol);
    }

    fn addMm0Outline(self: *Builder, symbol: OutlineSymbol) !void {
        try self.mm0_outline.append(self.allocator, symbol);
    }

    pub fn addProofOutline(self: *Builder, symbol: OutlineSymbol) !void {
        try self.proof_outline.append(self.allocator, symbol);
    }

    fn addProofDefItem(
        self: *Builder,
        text: []const u8,
        def: proof_script.DefItem,
    ) !void {
        if (def.isLocalDef()) {
            try self.addLocalProofDef(text, def, def.header_tail.?);
        } else {
            try self.addPublicDefBodyItem(def);
        }
    }

    /// A proof-side notation item on a proof-local def. Registered with the
    /// shared parser so later proof math parses the token, and indexed like
    /// an `.mm0` notation statement but against the proof document, which is
    /// what keeps it out of `.mm0` completions. The item's own position
    /// bounds the token's availability: the def may be declared well before
    /// its notation.
    fn addProofNotationItem(
        self: *Builder,
        text: []const u8,
        item: proof_script.NotationItem,
    ) !void {
        const decl_index = self.decl_by_name.get(item.name) orelse return;
        const decl = self.declarations.items[decl_index];
        if (decl.kind != .def or decl.name_range.document != .proof) return;

        const parser = if (self.mm0_parser) |*parser| parser else return;
        const term_id = parser.lookupTermId(item.name) orelse return;
        _ = parser.parseLocalNotationText(
            item.text,
            item.span.start,
            term_id,
        ) catch |err| {
            if (isFatalIndexError(err)) return err;
            self.complete = false;
            return;
        };

        const stmt = source.SourceSpan{
            .start = item.span.start,
            .end = item.span.start + item.text.len,
        };
        const header = source.statementHeader(text, stmt) orelse return;
        try self.collectNotationStatement(
            text,
            stmt,
            header,
            .proof,
            item.span.start,
        );
    }

    fn addPublicDefBodyItem(
        self: *Builder,
        def: proof_script.DefItem,
    ) !void {
        const decl_index = self.decl_by_name.get(def.name) orelse return;
        const decl = self.declarations.items[decl_index];
        if (decl.kind != .def) return;

        try self.addProofOutline(.{
            .name = def.name,
            .kind = .def,
            .range = proofSpanRange(def.span),
            .selection_range = proofSpanRange(def.name_span),
        });
        try self.addSymbol(.{
            .source_range = proofSpanRange(def.name_span),
            .target_range = decl.name_range,
            .markdown = decl.markdown,
        });
        const dummies = if (def.header_tail) |tail|
            try self.declareFillerDummies(decl_index, tail)
        else
            &.{};
        try self.indexMathStringIn(
            .proof,
            def.body.text,
            def.body.span.start + 1,
            decl_index,
            try std.mem.concat(self.allocator, BinderDecl, &.{ decl.binders, dummies }),
            false,
            decl.name_range.start,
        );
    }

    /// A filler's own dummies, `def name (.d: obj) = $ … $`: binders of its
    /// body only.
    fn declareFillerDummies(
        self: *Builder,
        decl_index: usize,
        header_tail: []const u8,
    ) ![]const BinderDecl {
        const decl = self.declarations.items[decl_index];
        const tokens = try self.indexSignature(.proof, header_tail, decl_index, decl.binders);
        var dummies = std.ArrayListUnmanaged(BinderDecl).empty;
        for (tokens) |token| {
            if (token.role != .binder) continue;
            const range = self.rangeOf(.proof, token.text) orelse continue;
            const dummy: BinderDecl = .{
                .name = token.text,
                .sort_name = token.sort,
                .bound = true,
                .range = range,
            };
            try dummies.append(self.allocator, dummy);
            try self.addSymbol(.{
                .source_range = range,
                .target_range = range,
                .markdown = try binderMarkdown(self.allocator, decl, dummy),
            });
        }
        try self.addLocalBinders(decl_index, dummies.items);
        return dummies.items;
    }

    fn addLocalProofDef(
        self: *Builder,
        text: []const u8,
        def: proof_script.DefItem,
        header_tail: []const u8,
    ) !void {
        var parser = self.mm0_parser orelse return;
        const term = parser.parseLocalDefText(
            def.name,
            .{ .start = def.name_span.start, .end = def.name_span.end },
            header_tail,
            def.body.text,
            proofMathTextSpan(def.body.span),
        ) catch |err| {
            if (isFatalIndexError(err)) return err;
            self.complete = false;
            return;
        };
        self.mm0_parser = parser;

        const decl_index = try self.addDeclaration(.{
            .name = def.name,
            .kind = .def,
            .name_range = proofSpanRange(def.name_span),
            .markdown = try termMarkdown(
                self.allocator,
                text,
                term,
                def.annotations,
            ),
            .binders = try bindersFromProofDef(
                self.allocator,
                def,
                term,
            ),
            .completion_args = try completionArgsFromArgs(
                self.allocator,
                .proof,
                text,
                term.arg_names,
                term.args,
            ),
        });
        try self.addProofOutline(.{
            .name = def.name,
            .kind = .def,
            .range = proofSpanRange(def.span),
            .selection_range = proofSpanRange(def.name_span),
        });
        _ = try self.indexSignature(
            .proof,
            header_tail,
            decl_index,
            self.declarations.items[decl_index].binders,
        );
        try self.deferAnnotations(decl_index, def.annotations);
        try self.indexMathString(
            .proof,
            def.body.text,
            def.body.span.start + 1,
            decl_index,
            false,
            null,
        );
        try self.decl_by_name.put(self.allocator, def.name, decl_index);
    }
};
