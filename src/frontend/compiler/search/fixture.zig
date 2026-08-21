//! Search fixture builder: constructs a `Fixture` (parser + env + registries +
//! metadata) positioned at a search target, driving the same pipeline passes the
//! compiler uses. Split out of `source.zig`: this machinery is shared by the
//! production LSP entry (`suggestionsAtSourceOffset` builds a fixture via
//! `fixtureForSourceTarget`) and the search unit tests (`fixtureFor*`,
//! `parseGoal`, `runSearchLine`, `readProofCase`). It holds no search logic —
//! only the setup that positions parsing/elaboration state at a proof point.

const std = @import("std");
const types = @import("./types.zig");
const timer = @import("./timer.zig");
const apply_mod = @import("./apply.zig");
const backtrack = @import("./backward/backtrack.zig");
const candidate_mod = @import("./candidate.zig");
const generate_mod = @import("./generate.zig");
const refs_mod = @import("./refs.zig");
const session_mod = @import("./session.zig");
const prune = @import("./backward/prune.zig");
const ExprId = @import("../../expr.zig").ExprId;
const TheoremContext = @import("../../expr.zig").TheoremContext;
const GlobalEnv = @import("../../env.zig").GlobalEnv;
const ParseRecovery = @import("../../parse_recovery.zig");
const AssertionStmt = ParseRecovery.AssertionStmt;
const SortStmt = ParseRecovery.SortStmt;
const TermStmt = ParseRecovery.TermStmt;
const MM0Parser = ParseRecovery.MM0Parser;
const MM0Stmt = ParseRecovery.MM0Stmt;
const ProofScript = @import("../../proof_script.zig");
const RuleApplication = ProofScript.RuleApplication;
const Ref = ProofScript.Ref;
const Span = ProofScript.Span;
const TemplateExpr = @import("../../rules.zig").TemplateExpr;
const RewriteRegistry = @import("../../rewrite_registry.zig").RewriteRegistry;
const RuleCatalog = @import("../rule_catalog.zig");
const CompilerViews = @import("../views.zig");
const FreshSelect = @import("../fresh_select.zig");
const CompilerDiag = @import("../../diag.zig");
const CompilerContext = @import("../context.zig").CompilerContext;
const CheckedIr = @import("../../checked_ir.zig");
const CheckedLine = CheckedIr.CheckedLine;
const Inference = @import("../inference.zig");
const OpenTerms = @import("../inference/open_terms.zig");
const Check = @import("../check.zig");
const CompilerVars = @import("../vars.zig");
const Metadata = @import("../metadata.zig");
const Holes = @import("../holes.zig");
const DiagnosticSink = @import("../diagnostic_sink.zig").DiagnosticSink;
const PipelineCommon = @import("../pipeline/common.zig");
const ProofParser = ProofScript.Parser;
const Goal = types.Goal;
const Context = types.Context;
const ApplyCandidate = types.ApplyCandidate;
const ExactCandidate = types.ExactCandidate;
const SourceSuggestion = types.SourceSuggestion;
const SourceSuggestionOptions = types.SourceSuggestionOptions;
const SourceSuggestions = types.SourceSuggestions;
const AttemptResult = types.AttemptResult;
const NameExprMap = types.NameExprMap;
const LabelIndexMap = types.LabelIndexMap;
const FreshDecl = types.FreshDecl;
const FreshenDecl = types.FreshenDecl;
const ViewDecl = types.ViewDecl;
const SortVarRegistry = types.SortVarRegistry;
const applyWithSession = apply_mod.applyWithSession;
const exactWithSession = backtrack.exactWithSession;
const tryCandidate = candidate_mod.tryCandidate;
const extractHypPartialBindings = prune.extractHypPartialBindings;

/// A search target resolved from a proof source: the enclosing block plus the
/// path to the specific line/inline application to search at. Consumed by
/// `fixtureForSourceTarget`; produced by `source.findSearchLine`.
pub const SourceTarget = struct {
    block: ProofScript.ProofBlock,
    line_index: usize,
    path: []const usize,
};

pub const Fixture = struct {
    parser: MM0Parser,
    env: GlobalEnv,
    registry: RewriteRegistry,
    rule_catalog: RuleCatalog.Catalog,
    fresh_bindings: std.AutoHashMap(u32, []const FreshDecl),
    freshen_bindings: std.AutoHashMap(u32, []const FreshenDecl),
    views: std.AutoHashMap(u32, ViewDecl),
    sort_vars: SortVarRegistry,
    assertion: AssertionStmt,
    available_rule_count: usize,
};

pub fn fixtureFor(
    allocator: std.mem.Allocator,
    mm0_src: []const u8,
    theorem_name: []const u8,
) !Fixture {
    return fixtureForSearchPoint(
        allocator,
        mm0_src,
        theorem_name,
        false,
    );
}

pub fn fixtureForFullEnv(
    allocator: std.mem.Allocator,
    mm0_src: []const u8,
    theorem_name: []const u8,
) !Fixture {
    return fixtureForSearchPoint(
        allocator,
        mm0_src,
        theorem_name,
        true,
    );
}

pub fn fixtureForSourceTarget(
    allocator: std.mem.Allocator,
    mm0_src: []const u8,
    proof_src: []const u8,
    target: SourceTarget,
) !Fixture {
    // A lemma target normally anchors to the next public block; a TRAILING
    // lemma (no following public block) anchors to mm0 EOF instead — every
    // declared rule is in scope, mirroring `drainTrailingLocalProofItems` on
    // the compile path.
    const anchor_name = try sourceTargetAnchorName(
        allocator,
        proof_src,
        target.block,
    );
    if (target.block.kind == .theorem and anchor_name == null) {
        return error.MissingTheorem;
    }
    var fixture = try initSearchFixture(allocator, mm0_src);
    var sink = DiagnosticSink.init(mm0_src, proof_src);
    var compiler = CompilerContext.init(mm0_src, proof_src, .none, &sink);
    // A local lemma before the target may itself hold a placeholder or a
    // half-typed line; tolerate both the way the LSP analysis does, so the
    // target's search survives an unfinished sibling. The stream is lenient
    // to match `findSearchLine`'s parse — the spans compared by
    // `drainLocalItemsBeforeSearchTarget` must come from the same grammar.
    compiler.allow_search_placeholders = true;
    var proof_stream: ?PipelineCommon.ProofItemStream =
        PipelineCommon.ProofItemStream.initLenient(allocator, proof_src);

    while (true) {
        try fixture.parser.prepareNextPublicStatement();
        const maybe_header = fixture.parser.peekNextPublicStmtHeader();
        const lemma_scope_complete = target.block.kind == .lemma and
            if (anchor_name) |name|
                maybe_header != null and publicHeaderNameEql(maybe_header.?, name)
            else
                maybe_header == null;
        if (lemma_scope_complete) {
            const block = try drainLocalItemsBeforeSearchTarget(
                &compiler,
                allocator,
                &fixture,
                &proof_stream,
                target.block.span,
            );
            fixture.assertion = try PipelineCommon.parseLemmaAssertion(
                &compiler,
                allocator,
                &fixture.parser,
                block,
            );
            fixture.available_rule_count = fixture.env.rules.items.len;
            return fixture;
        }
        if (maybe_header == null) return error.MissingTheorem;

        try PipelineCommon.drainAnchoredLocalProofItems(
            &compiler,
            allocator,
            &fixture.parser,
            &fixture.env,
            &fixture.registry,
            &fixture.rule_catalog,
            &fixture.fresh_bindings,
            &fixture.freshen_bindings,
            &fixture.views,
            &fixture.sort_vars,
            &proof_stream,
            null,
        );

        const stmt = try fixture.parser.next() orelse {
            return error.MissingTheorem;
        };
        switch (stmt) {
            .sort => |sort_stmt| try processSearchSortStmt(
                &fixture,
                stmt,
                sort_stmt,
            ),
            .term => |term_stmt| try processSearchTermStmt(
                &compiler,
                allocator,
                &fixture,
                &proof_stream,
                term_stmt,
            ),
            .assertion => |assertion| {
                // For a theorem target the anchor is its own (non-null) name.
                if (target.block.kind == .theorem and
                    std.mem.eql(u8, assertion.name, anchor_name.?))
                {
                    fixture.assertion = assertion;
                    fixture.available_rule_count = fixture.env.rules.items.len;
                    return fixture;
                }
                try processSearchAssertionStmt(
                    &fixture,
                    &proof_stream,
                    assertion,
                );
            },
        }
    }
}

fn initSearchFixture(
    allocator: std.mem.Allocator,
    mm0_src: []const u8,
) !Fixture {
    return .{
        .parser = MM0Parser.init(mm0_src, allocator),
        .env = GlobalEnv.init(allocator),
        .registry = RewriteRegistry.init(allocator),
        .rule_catalog = try RuleCatalog.build(allocator, mm0_src),
        .fresh_bindings = std.AutoHashMap(
            u32,
            []const FreshDecl,
        ).init(allocator),
        .freshen_bindings = std.AutoHashMap(
            u32,
            []const FreshenDecl,
        ).init(allocator),
        .views = std.AutoHashMap(u32, ViewDecl).init(allocator),
        .sort_vars = SortVarRegistry.init(allocator),
        .assertion = undefined,
        .available_rule_count = 0,
    };
}

fn fixtureForSearchPoint(
    allocator: std.mem.Allocator,
    mm0_src: []const u8,
    theorem_name: []const u8,
    include_trailing_rules: bool,
) !Fixture {
    var fixture = try initSearchFixture(allocator, mm0_src);
    var found_theorem = false;

    while (try fixture.parser.next()) |stmt| {
        switch (stmt) {
            .sort => |sort_stmt| {
                try fixture.env.addStmt(stmt);
                try Metadata.processSortMetadata(
                    &fixture.parser,
                    sort_stmt,
                    fixture.parser.last_annotations,
                    &fixture.sort_vars,
                );
            },
            .term => |term_stmt| {
                try fixture.env.addStmt(stmt);
                try Metadata.processTermMetadata(
                    &fixture.env,
                    &fixture.registry,
                    term_stmt,
                    fixture.parser.last_annotations,
                );
            },
            .assertion => |assertion| {
                if (!found_theorem and
                    std.mem.eql(u8, assertion.name, theorem_name))
                {
                    fixture.assertion = assertion;
                    fixture.available_rule_count =
                        fixture.env.rules.items.len;
                    found_theorem = true;
                    if (!include_trailing_rules) return fixture;
                    continue;
                }
                try fixture.env.addStmt(stmt);
                try Metadata.processAssertionMetadata(
                    allocator,
                    &fixture.parser,
                    &fixture.env,
                    &fixture.registry,
                    &fixture.fresh_bindings,
                    &fixture.freshen_bindings,
                    &fixture.views,
                    assertion,
                    fixture.parser.last_annotations,
                );
            },
        }
    }
    if (found_theorem) return fixture;
    return error.MissingTheorem;
}

fn sourceTargetAnchorName(
    allocator: std.mem.Allocator,
    proof_src: []const u8,
    target_block: ProofScript.ProofBlock,
) !?[]const u8 {
    if (target_block.kind == .theorem) return target_block.name;

    // Lenient to match `findSearchLine`'s parse: `spanEql` below compares
    // this walk's block spans against the target block it produced.
    var parser = ProofParser.initLenient(allocator, proof_src);
    var found_target = false;
    while (try parser.nextItem()) |item| {
        switch (item) {
            .block => |block| {
                if (spanEql(block.span, target_block.span)) {
                    found_target = true;
                    continue;
                }
                if (!found_target) continue;
                if (block.kind == .theorem) return block.name;
            },
            .def => |def| {
                if (!found_target) continue;
                if (def.header_tail == null) return def.name;
            },
        }
    }
    return null;
}

fn publicHeaderNameEql(header: anytype, name: []const u8) bool {
    const header_name = header.name orelse return false;
    return std.mem.eql(u8, header_name, name);
}

fn drainLocalItemsBeforeSearchTarget(
    compiler: *CompilerContext,
    allocator: std.mem.Allocator,
    fixture: *Fixture,
    proof_stream: *?PipelineCommon.ProofItemStream,
    target_span: Span,
) !ProofScript.ProofBlock {
    const proofs = if (proof_stream.*) |*value| value else {
        return error.MissingProofBlock;
    };
    var locals = std.ArrayListUnmanaged(ProofScript.TopLevelItem){};
    defer locals.deinit(allocator);

    while (true) {
        const item = (try proofs.next()) orelse return error.MissingProofBlock;
        switch (item) {
            .block => |block| {
                if (spanEql(block.span, target_span)) {
                    try processSearchLocalItems(
                        compiler,
                        allocator,
                        fixture,
                        locals.items,
                    );
                    return block;
                }
                if (PipelineCommon.isLocalProofItem(item)) {
                    try locals.append(allocator, item);
                    continue;
                }
                proofs.putBack(item);
                putBackProofItems(proofs, locals.items);
                return error.MissingProofBlock;
            },
            .def => {
                if (PipelineCommon.isLocalProofItem(item)) {
                    try locals.append(allocator, item);
                    continue;
                }
                proofs.putBack(item);
                putBackProofItems(proofs, locals.items);
                return error.MissingProofBlock;
            },
        }
    }
}

fn processSearchLocalItems(
    compiler: *CompilerContext,
    allocator: std.mem.Allocator,
    fixture: *Fixture,
    items: []const ProofScript.TopLevelItem,
) !void {
    for (items) |item| {
        try PipelineCommon.processLocalProofItem(
            compiler,
            allocator,
            &fixture.parser,
            &fixture.env,
            &fixture.registry,
            &fixture.rule_catalog,
            &fixture.fresh_bindings,
            &fixture.freshen_bindings,
            &fixture.views,
            &fixture.sort_vars,
            item,
            null,
        );
    }
}

fn putBackProofItems(
    proofs: *PipelineCommon.ProofItemStream,
    items: []const ProofScript.TopLevelItem,
) void {
    var idx = items.len;
    while (idx > 0) {
        idx -= 1;
        proofs.putBack(items[idx]);
    }
}

fn processSearchSortStmt(
    fixture: *Fixture,
    stmt: MM0Stmt,
    sort_stmt: SortStmt,
) !void {
    try fixture.env.addStmt(stmt);
    try Metadata.processSortMetadata(
        &fixture.parser,
        sort_stmt,
        fixture.parser.last_annotations,
        &fixture.sort_vars,
    );
}

fn processSearchTermStmt(
    compiler: *CompilerContext,
    allocator: std.mem.Allocator,
    fixture: *Fixture,
    proof_stream: *?PipelineCommon.ProofItemStream,
    term_stmt: TermStmt,
) !void {
    var filled_term_stmt = term_stmt;
    var filled_body_span: ?Span = null;
    if (term_stmt.is_def and term_stmt.body == null) {
        const filled = try PipelineCommon.fillPublicDefBody(
            compiler,
            allocator,
            &fixture.parser,
            proof_stream,
            term_stmt,
        );
        filled_term_stmt = filled.stmt;
        filled_body_span = filled.body_span;
    }

    try PipelineCommon.validateDefinitionBody(
        compiler,
        allocator,
        &fixture.parser,
        &fixture.env,
        filled_term_stmt,
        if (filled_body_span != null) .proof else .mm0,
        filled_body_span,
    );
    try fixture.env.addStmt(.{ .term = filled_term_stmt });
    try Metadata.processTermMetadata(
        &fixture.env,
        &fixture.registry,
        filled_term_stmt,
        fixture.parser.last_annotations,
    );
}

fn processSearchAssertionStmt(
    fixture: *Fixture,
    proof_stream: *?PipelineCommon.ProofItemStream,
    assertion: AssertionStmt,
) !void {
    try fixture.env.addStmt(.{ .assertion = assertion });
    try Metadata.processAssertionMetadata(
        fixture.env.allocator,
        &fixture.parser,
        &fixture.env,
        &fixture.registry,
        &fixture.fresh_bindings,
        &fixture.freshen_bindings,
        &fixture.views,
        assertion,
        fixture.parser.last_annotations,
    );
    consumeMatchingPublicProofBlock(proof_stream, assertion) catch {};
}

fn consumeMatchingPublicProofBlock(
    proof_stream: *?PipelineCommon.ProofItemStream,
    assertion: AssertionStmt,
) !void {
    if (assertion.kind != .theorem) return;
    const proofs = if (proof_stream.*) |*value| value else return;
    const item = (try proofs.next()) orelse return;
    switch (item) {
        .block => |block| {
            if (block.kind == .theorem and
                std.mem.eql(u8, block.name, assertion.name))
            {
                return;
            }
            proofs.putBack(item);
        },
        .def => proofs.putBack(item),
    }
}

fn spanEql(lhs: Span, rhs: Span) bool {
    return lhs.start == rhs.start and lhs.end == rhs.end;
}

pub fn readProofCase(
    allocator: std.mem.Allocator,
    stem: []const u8,
    ext: []const u8,
) ![]u8 {
    const path = try std.fmt.allocPrint(
        allocator,
        "tests/proof_cases/{s}.{s}",
        .{ stem, ext },
    );
    defer allocator.free(path);
    return try std.fs.cwd().readFileAlloc(
        allocator,
        path,
        std.math.maxInt(usize),
    );
}

pub fn parseGoal(
    fixture: *Fixture,
    theorem: *TheoremContext,
    theorem_vars: *NameExprMap,
    text: []const u8,
) !Goal {
    const parsed = try Holes.parseAssertion(
        &fixture.parser,
        theorem,
        theorem_vars,
        &fixture.sort_vars,
        text,
    );
    return switch (parsed) {
        .concrete => |expr| .{ .concrete = expr },
        .holey => |expr| .{ .holey = expr },
    };
}

pub fn runSearchLine(
    allocator: std.mem.Allocator,
    compiler: *CompilerContext,
    fixture: *Fixture,
    labels: *LabelIndexMap,
    checked: *std.ArrayListUnmanaged(CheckedLine),
    theorem: *TheoremContext,
    theorem_vars: *NameExprMap,
    diag_scratch: *CompilerDiag.Scratch,
    rule_unify_cache: *Inference.RuleUnifyCache,
    line: ProofScript.ProofLine,
    commit: bool,
) !AttemptResult {
    const context = Context{
        .allocator = allocator,
        .parser = &fixture.parser,
        .env = &fixture.env,
        .registry = &fixture.registry,
        .rule_catalog = &fixture.rule_catalog,
        .fresh_bindings = &fixture.fresh_bindings,
        .freshen_bindings = &fixture.freshen_bindings,
        .views = &fixture.views,
        .sort_vars = &fixture.sort_vars,
        .assertion = fixture.assertion,
        .labels = labels,
        .checked = checked,
        .diag_scratch = diag_scratch,
        .rule_unify_cache = rule_unify_cache,
        .available_rule_count = fixture.available_rule_count,
    };
    return tryCandidate(
        compiler,
        &context,
        line.application,
        try parseGoal(fixture, theorem, theorem_vars, line.assertion.text),
        theorem,
        theorem_vars,
        .{
            .commit = commit,
            .line_label = line.label,
            .assertion_span = line.assertion.span,
            .diagnostic_span = line.span,
        },
    );
}
