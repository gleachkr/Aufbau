const KnownBodies = @import("../proof_script.zig").KnownBodies;

pub const DocumentId = enum {
    mm0,
    proof,
};

/// The texts must outlive the snapshot, which indexes proof bodies on demand.
pub const SnapshotInput = struct {
    mm0_text: []const u8,
    proof_text: ?[]const u8 = null,
    /// The proof bodies earlier analyses of the unit checked
    /// (`CheckMemo.knownBodies`): the proof parse passes over them.
    known_bodies: ?KnownBodies = null,
};

pub const SourceRange = struct {
    document: DocumentId,
    start: usize,
    end: usize,

    pub fn eql(a: SourceRange, b: SourceRange) bool {
        return a.document == b.document and a.start == b.start and a.end == b.end;
    }

    pub fn contains(range: SourceRange, document: DocumentId, offset: usize) bool {
        return range.document == document and offset >= range.start and offset < range.end;
    }

    pub fn overlapsAny(range: SourceRange, ranges: []const SourceRange) bool {
        for (ranges) |other| {
            if (range.document == other.document and
                range.start < other.end and other.start < range.end) return true;
        }
        return false;
    }

    pub fn lessThan(_: void, a: SourceRange, b: SourceRange) bool {
        if (a.document != b.document) return a.document == .mm0;
        return if (a.start != b.start) a.start < b.start else a.end < b.end;
    }
};

pub const HoverResult = struct {
    range: SourceRange,
    markdown: []const u8,
};

pub const CompletionOptions = struct {
    snippet_support: bool = false,
};

pub const CompletionKind = enum {
    keyword,
    modifier,
    sort,
    term,
    def,
    axiom,
    theorem,
    lemma,
    proof_line,
    hypothesis,
    binder,
    annotation,
    notation,
    snippet,
};

pub const CompletionItem = struct {
    label: []const u8,
    kind: CompletionKind,
    detail: []const u8,
    documentation_markdown: ?[]const u8 = null,
    replacement: SourceRange,
    replacement_text: []const u8,
    snippet_replacement_text: ?[]const u8 = null,
    filter_text: ?[]const u8 = null,
    sort_text: []const u8,
};

pub const OutlineSymbol = struct {
    name: []const u8,
    kind: DeclarationKind,
    range: SourceRange,
    selection_range: SourceRange,
    children: []const OutlineSymbol = &.{},
};

pub const DeclarationKind = enum {
    sort,
    term,
    def,
    axiom,
    theorem,
    lemma,
    sort_var,

    pub fn label(self: DeclarationKind) []const u8 {
        return switch (self) {
            .sort => "sort",
            .term => "term",
            .def => "def",
            .axiom => "axiom",
            .theorem => "theorem",
            .lemma => "lemma",
            .sort_var => "@vars token",
        };
    }
};

pub const BinderDecl = struct {
    name: []const u8,
    sort_name: []const u8,
    bound: bool,
    range: ?SourceRange = null,
    sort_text: []const u8 = "",
};

pub const HypothesisDecl = struct {
    text: []const u8,
    range: SourceRange,
    /// Binder name for a binder-form hypothesis (`(h: $ a $)`); null for
    /// arrow-form hypotheses, which are positional only.
    name: ?[]const u8 = null,
    /// Range of the binder name token, when it was located in source.
    name_range: ?SourceRange = null,
};

pub const Declaration = struct {
    name: []const u8,
    kind: DeclarationKind,
    name_range: SourceRange,
    markdown: []const u8,
    binders: []const BinderDecl = &.{},
    /// Binders visible in part of the declaration only: a `@view`'s own
    /// binders and a definition filler's dummies.
    local_binders: []const BinderDecl = &.{},
    completion_args: []const BinderDecl = &.{},
    sort_text: []const u8 = "",
    hyp_count: usize = 0,
    hypotheses: []const HypothesisDecl = &.{},

    /// Whether `range` declares one of the binders.
    pub fn declaresBinder(decl: Declaration, range: SourceRange) bool {
        for ([_][]const BinderDecl{ decl.binders, decl.local_binders }) |binders| {
            for (binders) |binder| {
                const declared = binder.range orelse continue;
                if (declared.eql(range)) return true;
            }
        }
        return false;
    }

    /// Whether `range` declares the name of one of the hypotheses.
    pub fn declaresHypothesis(decl: Declaration, range: SourceRange) bool {
        for (decl.hypotheses) |hyp| {
            const declared = hyp.name_range orelse continue;
            if (declared.eql(range)) return true;
        }
        return false;
    }

    /// Whether `range` is the formula of one of the hypotheses.
    pub fn statesHypothesis(decl: Declaration, range: SourceRange) bool {
        for (decl.hypotheses) |hyp| {
            if (hyp.range.eql(range)) return true;
        }
        return false;
    }
};
