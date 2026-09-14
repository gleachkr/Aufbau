const std = @import("std");
const GlobalEnv = @import("../../env.zig").GlobalEnv;
const TheoremContext = @import("../../expr.zig").TheoremContext;
const MmbWriter = @import("../mmb_writer.zig");
const TermRecord = MmbWriter.TermRecord;
const TheoremRecord = MmbWriter.TheoremRecord;
const Statement = MmbWriter.Statement;
const Metadata = @import("../metadata.zig");
const Sort = @import("../../../trusted/sorts.zig").Sort;
const Expr = @import("../../../trusted/expressions.zig").Expr;
const ArgInfo = @import("../../parse_recovery.zig").ArgInfo;
const boundArgDepsToBinderDeps =
    @import("../../parse_recovery.zig").boundArgDepsToBinderDeps;
const AssertionStmt = @import("../../parse_recovery.zig").AssertionStmt;
const SortStmt = @import("../../parse_recovery.zig").SortStmt;
const TermStmt = @import("../../parse_recovery.zig").TermStmt;
const MM0Parser = @import("../../parse_recovery.zig").MM0Parser;
const MM0Stmt = @import("../../parse_recovery.zig").MM0Stmt;
const MathSpan = @import("../../parse_recovery.zig").MathSpan;
const PublicStmtHeader = @import("../../parse_recovery.zig").PublicStmtHeader;
const ProofScript = @import("../../proof_script.zig");
const ProofScriptParser = ProofScript.Parser;
const TheoremBlock = ProofScript.TheoremBlock;
const DefItem = ProofScript.DefItem;
const NotationItem = ProofScript.NotationItem;
const TopLevelItem = ProofScript.TopLevelItem;
const Span = ProofScript.Span;
const RewriteRegistry = @import("../../rewrite_registry.zig").RewriteRegistry;
const BindingValidation = @import("../../binding_validation.zig");
const CompilerEmit = @import("../emit.zig");
const Check = @import("../check.zig");
const RuleCatalog = @import("../rule_catalog.zig");
const CompilerVars = @import("../vars.zig");
const CompilerDiag = @import("../../diag.zig");
const CompilerContext = @import("../context.zig").CompilerContext;
const CompilerLints = @import("../lints.zig");
const Diagnostic = CompilerDiag.Diagnostic;
const DiagnosticSource = CompilerDiag.DiagnosticSource;

const ViewDecl = Metadata.ViewDecl;
const FreshDecl = Metadata.FreshDecl;
const FreshenDecl = Metadata.FreshenDecl;
const SortVarRegistry = CompilerVars.SortVarRegistry;

pub const Output = struct {
    sort_names: std.ArrayListUnmanaged([]const u8) = .{},
    sorts: std.ArrayListUnmanaged(Sort) = .{},
    terms: std.ArrayListUnmanaged(TermRecord) = .{},
    theorems: std.ArrayListUnmanaged(TheoremRecord) = .{},
    statements: std.ArrayListUnmanaged(Statement) = .{},
};

pub const ProofItemStream = struct {
    allocator: std.mem.Allocator,
    parser: ProofScriptParser,
    pending: std.ArrayListUnmanaged(TopLevelItem) = .{},

    pub fn init(allocator: std.mem.Allocator, source: []const u8) ProofItemStream {
        return .{
            .allocator = allocator,
            .parser = ProofScriptParser.init(allocator, source),
        };
    }

    /// Editor-facing variant: broken proof lines become
    /// `ProofLine.incomplete` entries instead of ending the stream. The
    /// compile path must keep using `init` — an incomplete line is an error
    /// there.
    pub fn initLenient(
        allocator: std.mem.Allocator,
        source: []const u8,
    ) ProofItemStream {
        return .{
            .allocator = allocator,
            .parser = ProofScriptParser.initLenient(allocator, source),
        };
    }

    pub fn next(self: *ProofItemStream) !?TopLevelItem {
        if (self.pending.items.len > 0) {
            return self.pending.pop().?;
        }
        return try self.parser.nextItem();
    }

    pub fn putBack(self: *ProofItemStream, item: TopLevelItem) void {
        self.pending.append(self.allocator, item) catch unreachable;
    }
};

// ---------------------------------------------------------------------------
// The `.mm0` statement walk.
//
// Three loops stream the `.mm0` file in lockstep with the `.auf` proofs: the
// compile path (`run.zig`, strict), the editor analysis (`analyze.zig`,
// recovers per statement), and the search fixture (`search/fixture.zig`,
// stops at a target theorem). They differ in what they do when a step fails
// and in whether they check proofs; they must NOT differ in what a step is.
// Every per-gap and per-declaration obligation therefore lives in the
// helpers below, and a loop only composes them under its own error policy.
// ---------------------------------------------------------------------------

/// Scan to the upcoming public statement, consuming the notation and
/// coercion declarations before it and collecting its annotations. Only a
/// loop that must look at the upcoming header before parsing the statement
/// (to drain the proof-local items anchored to it) calls this separately;
/// `nextPublicStatement` prepares on its own otherwise. On failure the
/// diagnostic is set on `ctx` and the parser is left for
/// `recoverToStatementBoundary`.
pub fn prepareNextPublicStatement(
    ctx: ?*CompilerContext,
    parser: *MM0Parser,
    env: *const GlobalEnv,
) !void {
    parser.prepareNextPublicStatement() catch |err| {
        if (ctx) |c| {
            c.setDiagnostic(mm0ParserDiagnosticWithLocalNotes(parser, env, err));
        }
        return err;
    };
}

/// Parse the next public statement (`null` at end of stream) and discharge
/// what the gap before it owes: mirror the coercions the parser consumed
/// into `env`, warn about annotations that attached to nothing, and reject
/// `.mm0` notation or coercions on a proof-local term. On a parse failure
/// the diagnostic is set on `ctx` and the parser is left for
/// `recoverToStatementBoundary`; `error.LocalTermInMm0` also comes with its
/// diagnostic set, and the statement (if any) is consumed.
pub fn nextPublicStatement(
    ctx: ?*CompilerContext,
    parser: *MM0Parser,
    env: *GlobalEnv,
) !?MM0Stmt {
    const maybe_stmt = parser.next() catch |err| {
        if (ctx) |c| {
            c.setDiagnostic(mm0ParserDiagnosticWithLocalNotes(parser, env, err));
        }
        return err;
    };
    // The parser consumes coercion statements silently while scanning to
    // the next public statement; keep the env's mirror in lockstep.
    try env.syncCoercionsFromParser(parser);
    // Dropped-annotation warnings belong to the gap, not to the statement
    // that follows, so they are issued before any per-statement snapshot a
    // recovering loop takes.
    Metadata.warnDroppedAnnotations(ctx, parser);
    try rejectLocalTermNotation(ctx, parser, env, maybe_stmt);
    return maybe_stmt;
}

/// Where a declaration's annotations come from. This also fixes the
/// diagnostic source and the span its lint and annotation diagnostics
/// anchor on.
pub const DeclarationSite = union(enum) {
    /// A public `.mm0` statement: the parser holds its annotations.
    mm0,
    /// A proof-side item (a local def or lemma): the item carries them.
    proof: struct {
        annotations: []const []const u8,
        name_span: Span,
    },
};

/// Register a public sort: its annotations (`@vars`, hole tokens), then the
/// env entry. Annotations go first so a rejected sort never enters `env`
/// (a recovering loop restores `sort_vars` itself).
pub fn registerSort(
    ctx: ?*CompilerContext,
    parser: *MM0Parser,
    env: *GlobalEnv,
    sort_stmt: SortStmt,
    sort_vars: *SortVarRegistry,
) !void {
    try Metadata.processSortMetadata(
        ctx,
        parser,
        sort_stmt,
        parser.last_annotations,
        parser.last_annotation_spans,
        sort_vars,
    );
    try env.addStmt(.{ .sort = sort_stmt });
}

/// Register a term or def whose body is already filled and validated: the
/// env entry, the unused-parameter lint, then its annotations (`@acui`,
/// `@conversion`), which look the term up by name and so run last. A
/// proof-site term is a proof-local def and is marked so.
///
/// On failure the entry may already be in `env`. The parser holds the
/// term's id, so a recovering caller invalidates it in place
/// (`TermRecoverySnapshot.discardTerm`); it is never removed.
pub fn registerTerm(
    ctx: ?*CompilerContext,
    allocator: std.mem.Allocator,
    parser: *const MM0Parser,
    env: *GlobalEnv,
    registry: *RewriteRegistry,
    term_stmt: TermStmt,
    site: DeclarationSite,
) !void {
    try env.addStmt(.{ .term = term_stmt });
    const term_id = env.term_names.get(term_stmt.name) orelse {
        return error.UnknownTerm;
    };
    if (site == .proof) try env.markTermLocal(term_id);
    const source: DiagnosticSource = switch (site) {
        .mm0 => .mm0,
        .proof => .proof,
    };
    const name_span: Span = switch (site) {
        .mm0 => CompilerDiag.mathSpanToSpan(term_stmt.name_span),
        .proof => |item| item.name_span,
    };
    if (ctx) |c| {
        try CompilerLints.lintUnusedDefinitionParameters(
            c,
            allocator,
            &env.terms.items[term_id],
            name_span,
            source,
        );
    }
    switch (site) {
        .mm0 => try Metadata.processTermMetadata(
            ctx,
            env,
            registry,
            term_stmt,
            parser.last_annotations,
            parser.last_annotation_spans,
        ),
        .proof => |item| try Metadata.processTermMetadataAt(
            ctx,
            env,
            registry,
            term_stmt,
            item.annotations,
            &.{},
            .proof,
            item.name_span,
        ),
    }
}

/// Register an axiom, theorem, or lemma whose proof (if any) is already
/// checked: the env entry, the unused-parameter lint, then its annotations
/// (`@auto`, `@view`/`@recover`, `@fresh`, ...). Registration is atomic:
/// when the annotations are rejected the rule is removed again, so a
/// failed declaration leaves no rule behind for later proofs to cite.
pub fn registerAssertion(
    ctx: ?*CompilerContext,
    allocator: std.mem.Allocator,
    parser: *MM0Parser,
    env: *GlobalEnv,
    registry: *RewriteRegistry,
    fresh_bindings: *std.AutoHashMap(u32, []const FreshDecl),
    freshen_bindings: *std.AutoHashMap(u32, []const FreshenDecl),
    views: *std.AutoHashMap(u32, ViewDecl),
    assertion: AssertionStmt,
    site: DeclarationSite,
) !void {
    const source: DiagnosticSource = switch (site) {
        .mm0 => .mm0,
        .proof => .proof,
    };
    const name_span: Span = switch (site) {
        .mm0 => CompilerDiag.mathSpanToSpan(assertion.name_span),
        .proof => |item| item.name_span,
    };
    try addAssertionToEnv(ctx, env, assertion, assertion.name, name_span, source);
    const rule_id = env.getRuleId(assertion.name) orelse {
        return error.MissingRule;
    };
    if (ctx) |c| {
        try CompilerLints.lintUnusedTheoremParameters(
            c,
            allocator,
            &env.rules.items[rule_id],
            name_span,
            source,
        );
    }
    const annotations: []const []const u8 = switch (site) {
        .mm0 => parser.last_annotations,
        .proof => |item| item.annotations,
    };
    const annotation_spans: []const MathSpan = switch (site) {
        .mm0 => parser.last_annotation_spans,
        .proof => &.{},
    };
    Metadata.processAssertionMetadata(
        allocator,
        ctx,
        parser,
        env,
        registry,
        fresh_bindings,
        freshen_bindings,
        views,
        assertion,
        annotations,
        annotation_spans,
        source,
        if (site == .proof) name_span else null,
    ) catch |err| {
        env.removeLastRule(assertion.name);
        return err;
    };
}

/// Whether every sort and term a declaration names is available in `env`.
/// Only a recovering loop can see `false`: a strict walk fails at the parser
/// before an unknown name reaches the compiler, while recovery leaves
/// unavailable placeholders behind for the declarations it rejected. A
/// blocked declaration is skipped silently, since its cause was reported.
pub fn termDependenciesAvailable(
    env: *const GlobalEnv,
    stmt: TermStmt,
) bool {
    if (!argSortsAvailable(env, stmt.args)) return false;
    if (!argSortsAvailable(env, stmt.dummy_args)) return false;
    if (!env.sort_names.contains(stmt.ret_sort_name)) return false;
    const body = stmt.body orelse return true;
    return exprTermsAvailable(env, body);
}

pub fn assertionDependenciesAvailable(
    env: *const GlobalEnv,
    stmt: AssertionStmt,
) bool {
    if (!argSortsAvailable(env, stmt.args)) return false;
    for (stmt.hyps) |hyp| {
        if (!exprTermsAvailable(env, hyp)) return false;
    }
    return exprTermsAvailable(env, stmt.concl);
}

fn argSortsAvailable(env: *const GlobalEnv, args: []const ArgInfo) bool {
    for (args) |arg| {
        if (!env.sort_names.contains(arg.sort_name)) return false;
    }
    return true;
}

fn exprTermsAvailable(env: *const GlobalEnv, expr: *const Expr) bool {
    switch (expr.*) {
        .variable => return true,
        .term => |term| {
            // Parsed expressions carry parser term ids, not frontend name
            // lookups. In recovery mode a rejected term may still occupy
            // that id as an unavailable placeholder, so the id is checked
            // here instead of assuming every in-range slot is valid.
            if (!env.hasAvailableTerm(term.id)) return false;
            for (term.args) |arg| {
                if (!exprTermsAvailable(env, arg)) return false;
            }
            return true;
        },
        .hole => return false,
    }
}

pub fn validateDefinitionBody(
    self: *CompilerContext,
    allocator: std.mem.Allocator,
    parser: *const MM0Parser,
    env: *const GlobalEnv,
    term_stmt: TermStmt,
    diag_source: DiagnosticSource,
    diag_span: ?Span,
) !void {
    if (!term_stmt.is_def) return;

    var theorem = TheoremContext.init(allocator);
    defer theorem.deinit();
    try theorem.seedTerm(parser, term_stmt);

    const body = term_stmt.body orelse return error.ExpectedDefinitionBody;
    const body_expr_id = try theorem.internParsedExpr(body);
    const body_info = try BindingValidation.currentDefExprInfo(
        env,
        &theorem,
        body_expr_id,
    );

    if (!std.mem.eql(u8, body_info.sort_name, term_stmt.ret_sort_name)) {
        var diag = Diagnostic{
            .kind = .invalid_definition_body,
            .err = error.SortMismatch,
            .name = term_stmt.name,
            .source = diag_source,
            .span = diag_span orelse
                CompilerDiag.mathSpanToSpan(term_stmt.name_span),
            .detail = .{ .definition_body = .{
                .declared_sort_name = term_stmt.ret_sort_name,
                .actual_sort_name = body_info.sort_name,
                .body_deps = body_info.deps,
                .hidden_binder_count = term_stmt.dummy_args.len,
            } },
        };
        CompilerDiag.addNote(&diag, .def_body_result_sort, .mm0, null);
        self.setDiagnostic(diag);
        return error.SortMismatch;
    }

    // The declared result deps index the bound args in order; body deps are
    // in binder-declaration order (dummies included), so widen the declared
    // mask to that space before comparing. Free variables the result type
    // does not declare are the violation (superset declarations are fine),
    // matching the verifier's checkExprAgainstArg.
    const declared_deps = boundArgDepsToBinderDeps(
        term_stmt.args,
        term_stmt.ret_deps,
    );

    const uncovered_deps = body_info.deps & ~declared_deps;
    if (uncovered_deps != 0) {
        var diag = Diagnostic{
            .kind = .invalid_definition_body,
            .err = error.DepViolation,
            .name = term_stmt.name,
            .source = diag_source,
            .span = diag_span orelse
                CompilerDiag.mathSpanToSpan(term_stmt.name_span),
            .detail = .{ .definition_body = .{
                .declared_sort_name = term_stmt.ret_sort_name,
                .actual_sort_name = body_info.sort_name,
                .body_deps = uncovered_deps,
                .hidden_binder_count = term_stmt.dummy_args.len,
            } },
        };
        CompilerDiag.addNote(&diag, .def_body_checked_before_unify, .mm0, null);
        CompilerDiag.addNote(&diag, .def_body_free_var_deps, .mm0, null);
        self.setDiagnostic(diag);
        return error.DepViolation;
    }
}

pub const FilledPublicDef = struct {
    stmt: TermStmt,
    body_span: Span,
};

pub fn fillPublicDefBody(
    self: *CompilerContext,
    _: std.mem.Allocator,
    parser: *MM0Parser,
    proof_stream: *?ProofItemStream,
    term_stmt: TermStmt,
) !FilledPublicDef {
    const actual_proofs = if (proof_stream.*) |*proofs|
        proofs
    else {
        self.setDiagnostic(CompilerDiag.missingPublicDefBodyDiagnostic(
            term_stmt.name,
            CompilerDiag.mathSpanToSpan(term_stmt.name_span),
        ));
        return error.MissingPublicDefBody;
    };

    const item = actual_proofs.next() catch |err| {
        self.setDiagnostic(CompilerDiag.proofParserDiagnostic(
            &actual_proofs.parser,
            term_stmt.name,
            err,
        ));
        return err;
    } orelse {
        self.setDiagnostic(CompilerDiag.missingPublicDefBodyDiagnostic(
            term_stmt.name,
            CompilerDiag.mathSpanToSpan(term_stmt.name_span),
        ));
        return error.MissingPublicDefBody;
    };

    switch (item) {
        .def => |def| return fillFromFillerDefItem(self, parser, term_stmt, def),
        .block, .notation => {
            actual_proofs.putBack(item);
            self.setDiagnostic(CompilerDiag.missingPublicDefBodyDiagnostic(
                term_stmt.name,
                CompilerDiag.mathSpanToSpan(term_stmt.name_span),
            ));
            return error.MissingPublicDefBody;
        },
    }
}

/// Fill `term_stmt` (a bodyless public def) from its .auf filler item. The
/// filler may carry a dummy-only binder tail declaring extra hidden dummies
/// (`def name (.d: obj) = $ ... $`); a tail with a full signature — a
/// local-def shape — is rejected.
pub fn fillFromFillerDefItem(
    self: *CompilerContext,
    parser: *MM0Parser,
    term_stmt: TermStmt,
    def: DefItem,
) !FilledPublicDef {
    try rejectDefAnnotations(self, def);
    if (!std.mem.eql(u8, def.name, term_stmt.name)) {
        self.setDiagnostic(
            CompilerDiag.publicDefBodyNameMismatchDiagnostic(
                term_stmt.name,
                def.name,
                def.name_span,
            ),
        );
        return error.PublicDefBodyNameMismatch;
    }
    var base = term_stmt;
    if (def.header_tail) |tail| {
        if (def.isLocalDef()) {
            self.setDiagnostic(
                CompilerDiag.publicDefBodyHeaderDiagnostic(
                    def.name,
                    def.header_tail_span orelse def.name_span,
                ),
            );
            return error.PublicDefBodyMustBeHeaderless;
        }
        const tail_span = def.header_tail_span orelse def.name_span;
        base = parser.extendStmtWithFillerDummies(
            term_stmt,
            tail,
            tail_span.start,
        ) catch |err| {
            self.setDiagnostic(fillerDummyDiagnostic(parser, def, err));
            return err;
        };
    }
    const body_span = proofMathTextSpan(def.body.span);
    var filled = base;
    filled.body = parser.parsePublicDefBodyText(
        base,
        def.body.text,
        body_span,
    ) catch |err| {
        self.setDiagnostic(publicDefBodyParseDiagnostic(
            parser,
            def,
            err,
        ));
        return err;
    };
    return .{ .stmt = filled, .body_span = def.body.span };
}

pub fn fillerDummyDiagnostic(
    parser: *const MM0Parser,
    def: DefItem,
    err: CompilerDiag.DiagnosticError,
) Diagnostic {
    return .{
        .kind = .generic,
        .err = err,
        .source = .proof,
        .name = def.name,
        .span = CompilerDiag.mathSpanToSpanOpt(parser.diagnosticSpan()) orelse
            (def.header_tail_span orelse def.name_span),
    };
}

pub fn proofMathTextSpan(span: Span) MathSpan {
    return .{
        .start = @min(span.start + 1, span.end),
        .end = if (span.end > span.start) span.end - 1 else span.end,
    };
}

pub fn publicDefBodyParseDiagnostic(
    parser: *const MM0Parser,
    def: DefItem,
    err: CompilerDiag.DiagnosticError,
) Diagnostic {
    var diag = Diagnostic{
        .kind = .generic,
        .err = err,
        .source = .proof,
        .name = def.name,
        .span = CompilerDiag.mathSpanToSpanOpt(parser.diagnosticSpan()) orelse
            def.body.span,
    };
    if (err == error.UnknownMathToken) {
        if (parser.mathError()) |math_err| {
            switch (math_err) {
                .unknown_token => |token| {
                    diag.detail = .{ .unknown_math_token = .{
                        .token = token.text,
                    } };
                },
                else => {},
            }
        }
    }
    return diag;
}

pub fn setExtraProofItemDiagnostic(self: *CompilerContext, item: TopLevelItem) anyerror {
    switch (item) {
        .block => |block| {
            self.setDiagnostic(
                CompilerDiag.extraProofBlockDiagnostic(block.name, block.name_span),
            );
            return error.ExtraProofBlock;
        },
        .def => |def| {
            self.setDiagnostic(
                CompilerDiag.extraProofDefDiagnostic(def.name, def.name_span),
            );
            return error.ExtraProofItem;
        },
        .notation => |notation| {
            self.setDiagnostic(CompilerDiag.extraProofDefDiagnostic(
                notation.name,
                notation.name_span,
            ));
            return error.ExtraProofItem;
        },
    }
}

/// The proof-local items (lemmas, local defs, notation) that precede the
/// next public proof item, when that item anchors to the upcoming `.mm0`
/// statement (the parser must be prepared, see `prepareNextPublicStatement`).
/// The anchor is put back; the items come out in source order for the
/// caller to process under its own error policy. Anything not anchored is
/// put back too and the slice is empty.
pub fn collectAnchoredLocalProofItems(
    ctx: ?*CompilerContext,
    allocator: std.mem.Allocator,
    parser: *const MM0Parser,
    proof_stream: *?ProofItemStream,
) ![]const TopLevelItem {
    const proofs = if (proof_stream.*) |*actual| actual else return &.{};
    const header = parser.peekNextPublicStmtHeader() orelse return &.{};

    var locals = std.ArrayListUnmanaged(TopLevelItem){};
    defer locals.deinit(allocator);

    while (true) {
        const item = proofs.next() catch |err| {
            if (ctx) |c| {
                c.setDiagnostic(CompilerDiag.proofParserDiagnostic(
                    &proofs.parser,
                    header.name,
                    err,
                ));
            }
            return err;
        } orelse {
            putBackItems(proofs, locals.items);
            return &.{};
        };

        if (isLocalProofItem(item)) {
            try locals.append(allocator, item);
            continue;
        }

        proofs.putBack(item);
        if (locals.items.len == 0 or !anchorMatches(header, item)) {
            putBackItems(proofs, locals.items);
            return &.{};
        }
        return try locals.toOwnedSlice(allocator);
    }
}

/// Strict form: process every anchored local item, failing on the first
/// broken one.
pub fn drainAnchoredLocalProofItems(
    self: *CompilerContext,
    allocator: std.mem.Allocator,
    parser: *MM0Parser,
    env: *GlobalEnv,
    registry: *RewriteRegistry,
    rule_catalog: *const RuleCatalog.Catalog,
    fresh_bindings: *std.AutoHashMap(u32, []const FreshDecl),
    freshen_bindings: *std.AutoHashMap(u32, []const FreshenDecl),
    views: *std.AutoHashMap(u32, ViewDecl),
    sort_vars: *const SortVarRegistry,
    proof_stream: *?ProofItemStream,
    emit: ?*Output,
) !void {
    const locals = try collectAnchoredLocalProofItems(
        self,
        allocator,
        parser,
        proof_stream,
    );
    defer allocator.free(locals);
    for (locals) |local| {
        try processLocalProofItem(
            self,
            allocator,
            parser,
            env,
            registry,
            rule_catalog,
            fresh_bindings,
            freshen_bindings,
            views,
            sort_vars,
            local,
            emit,
        );
    }
}

fn putBackItems(proofs: *ProofItemStream, items: []const TopLevelItem) void {
    var idx = items.len;
    while (idx > 0) {
        idx -= 1;
        proofs.putBack(items[idx]);
    }
}

/// Process any proof items remaining after the MM0 stream is exhausted.
/// Local items (lemma blocks, local defs) have no MM0 counterpart to anchor
/// to at end of stream, but they are self-contained emissions and everything
/// they can reference is already in scope, so we simply process them in order.
/// A trailing *public* block or def, by contrast, is a genuine orphan (a proof
/// block with no matching theorem/def) and is still reported as an error.
pub fn drainTrailingLocalProofItems(
    self: *CompilerContext,
    allocator: std.mem.Allocator,
    parser: *MM0Parser,
    env: *GlobalEnv,
    registry: *RewriteRegistry,
    rule_catalog: *const RuleCatalog.Catalog,
    fresh_bindings: *std.AutoHashMap(u32, []const FreshDecl),
    freshen_bindings: *std.AutoHashMap(u32, []const FreshenDecl),
    views: *std.AutoHashMap(u32, ViewDecl),
    sort_vars: *const SortVarRegistry,
    proofs: *ProofItemStream,
    emit: ?*Output,
) !void {
    while (true) {
        const item = proofs.next() catch |err| {
            self.setDiagnostic(CompilerDiag.proofParserDiagnostic(
                &proofs.parser,
                null,
                err,
            ));
            return err;
        } orelse return;

        if (!isLocalProofItem(item)) {
            return setExtraProofItemDiagnostic(self, item);
        }

        try processLocalProofItem(
            self,
            allocator,
            parser,
            env,
            registry,
            rule_catalog,
            fresh_bindings,
            freshen_bindings,
            views,
            sort_vars,
            item,
            emit,
        );
    }
}

pub fn isLocalProofItem(item: TopLevelItem) bool {
    return switch (item) {
        .block => |block| block.kind == .lemma,
        .def => |def| def.isLocalDef(),
        .notation => true,
    };
}

pub fn anchorMatches(header: PublicStmtHeader, item: TopLevelItem) bool {
    switch (item) {
        .block => |block| {
            if (block.kind != .theorem) return false;
            if (header.kind != .theorem) return false;
            const name = header.name orelse return false;
            return std.mem.eql(u8, name, block.name);
        },
        .def => |def| {
            if (def.isLocalDef()) return false;
            if (header.kind != .def) return false;
            const name = header.name orelse return false;
            return std.mem.eql(u8, name, def.name);
        },
        .notation => return false,
    }
}

pub fn processLocalProofItem(
    self: *CompilerContext,
    allocator: std.mem.Allocator,
    parser: *MM0Parser,
    env: *GlobalEnv,
    registry: *RewriteRegistry,
    rule_catalog: *const RuleCatalog.Catalog,
    fresh_bindings: *std.AutoHashMap(u32, []const FreshDecl),
    freshen_bindings: *std.AutoHashMap(u32, []const FreshenDecl),
    views: *std.AutoHashMap(u32, ViewDecl),
    sort_vars: *const SortVarRegistry,
    item: TopLevelItem,
    emit: ?*Output,
) !void {
    switch (item) {
        .block => |block| try processLocalProofBlock(
            self,
            allocator,
            parser,
            env,
            registry,
            rule_catalog,
            fresh_bindings,
            freshen_bindings,
            views,
            sort_vars,
            block,
            emit,
        ),
        .def => |def| try processLocalDefItem(
            self,
            allocator,
            parser,
            env,
            registry,
            def,
            emit,
        ),
        .notation => |notation| try processLocalNotationItem(
            self,
            parser,
            env,
            notation,
        ),
    }
}

/// A proof-local definition has no `.mm0` declaration, so the `.mm0` stream
/// must never name it: the file has to stand on its own for any MM0 reader.
/// The shared parser cannot tell the two streams apart, so the reference is
/// rejected after the statement parses, anchored on that statement. A public
/// def's filler body may still use local defs; it never appears in the `.mm0`.
pub fn rejectLocalTermReferences(
    self: *CompilerContext,
    env: *const GlobalEnv,
    stmt: MM0Stmt,
) error{LocalTermInMm0}!void {
    const found: ?u32 = switch (stmt) {
        .sort => null,
        .term => |term| if (term.body) |body|
            firstLocalTerm(env, body)
        else
            null,
        .assertion => |assertion| blk: {
            for (assertion.hyps) |hyp| {
                if (firstLocalTerm(env, hyp)) |id| break :blk id;
            }
            break :blk firstLocalTerm(env, assertion.concl);
        },
    };
    const term_id = found orelse return;
    self.setDiagnostic(CompilerDiag.localTermInMm0Diagnostic(
        stmt,
        env.terms.items[term_id].name,
    ));
    return error.LocalTermInMm0;
}

fn firstLocalTerm(env: *const GlobalEnv, expr: *const Expr) ?u32 {
    switch (expr.*) {
        .variable, .hole => return null,
        .term => |app| {
            if (env.isLocalTerm(app.id)) return app.id;
            for (app.args) |arg| {
                if (firstLocalTerm(env, arg)) |id| return id;
            }
            return null;
        },
    }
}

/// Notation and coercion declarations are consumed silently while the parser
/// scans to the next public statement, so a local term that carries a
/// coercion, or notation the proof file did not declare, was named by one of
/// them. Each declaration is reported once, anchored on the statement that
/// follows it.
pub fn rejectLocalTermNotation(
    ctx: ?*CompilerContext,
    parser: *const MM0Parser,
    env: *GlobalEnv,
    next_stmt: ?MM0Stmt,
) !void {
    if (env.local_term_ids.items.len == 0) return;
    // The proof file cannot declare coercions, so any on a local term is
    // the `.mm0`'s.
    for (env.coercions.items) |*coercion| {
        if (coercion.local_reported) continue;
        if (!env.isLocalTerm(coercion.term_id)) continue;
        coercion.local_reported = true;
        return failLocalTermInMm0(ctx, env, coercion.term_id, next_stmt);
    }
    var it = parser.notationIterator();
    while (it.next()) |entry| {
        if (!env.isLocalTerm(entry.term_id)) continue;
        if (env.hasLocalNotation(entry.term_id, entry.token)) continue;
        // Recorded as seen so the analyze path reports it once.
        try env.addLocalNotation(entry.term_id, entry.token);
        return failLocalTermInMm0(ctx, env, entry.term_id, next_stmt);
    }
}

fn failLocalTermInMm0(
    ctx: ?*CompilerContext,
    env: *const GlobalEnv,
    term_id: u32,
    next_stmt: ?MM0Stmt,
) error{LocalTermInMm0} {
    if (ctx) |c| c.setDiagnostic(CompilerDiag.localTermInMm0Diagnostic(
        next_stmt,
        env.terms.items[term_id].name,
    ));
    return error.LocalTermInMm0;
}

/// `mm0ParserDiagnostic`, plus a note when proof-side notation may be the
/// real culprit. The token, precedence, and associativity tables are shared,
/// so a local notation registered earlier in lockstep order makes a later,
/// standalone-valid `.mm0` declaration (or binder name) fail at the `.mm0`
/// statement.
pub fn mm0ParserDiagnosticWithLocalNotes(
    parser: *const MM0Parser,
    env: *const GlobalEnv,
    err: CompilerDiag.DiagnosticError,
) Diagnostic {
    var diag = CompilerDiag.mm0ParserDiagnostic(parser, err);
    if (env.local_notations.items.len == 0) return diag;
    switch (err) {
        error.PrecedenceMismatch,
        error.PrecedenceAssocMismatch,
        error.NotationFirstTokenConflict,
        error.DuplicateInfixToken,
        error.BinderTokenCollision,
        => {},
        else => return diag,
    }
    const candidates = [_]?[]const u8{
        parser.mathSpanText(),
        parser.diagnosticSpanText(),
    };
    for (candidates) |maybe_text| {
        const text = std.mem.trim(u8, maybe_text orelse continue, " \t\r\n");
        const term_id = env.localNotationTerm(text) orelse continue;
        CompilerDiag.addNote(&diag, .{ .local_notation_token = .{
            .term_name = env.terms.items[term_id].name,
            .token = text,
        } }, .proof, null);
        return diag;
    }
    CompilerDiag.addNote(&diag, .local_notation_tables_shared, .proof, null);
    return diag;
}

/// A proof-side notation declaration. It may only name a proof-local def:
/// on a public term it would let later `.mm0` math use a token a standalone
/// reader lacks, with nothing in the parsed expression to catch it. On a
/// local def the token parses to the local term, so `rejectLocalTermReferences`
/// already covers any `.mm0` use. The token this item registers is recorded
/// on the env, which is how `rejectLocalTermNotation` tells it from `.mm0`
/// ones; an `.mm0` notation on the same def consumed earlier stays
/// unrecorded, so it is still rejected.
pub fn processLocalNotationItem(
    self: *CompilerContext,
    parser: *MM0Parser,
    env: *GlobalEnv,
    item: NotationItem,
) !void {
    Metadata.warnDroppedProofAnnotations(self, item.annotations, item.name_span);
    const term_id = env.term_names.get(item.name) orelse {
        self.setDiagnostic(.{
            .kind = .generic,
            .err = error.UnknownTerm,
            .source = .proof,
            .name = item.name,
            .span = item.name_span,
        });
        return error.UnknownTerm;
    };
    if (!env.isLocalTerm(term_id)) {
        self.setDiagnostic(CompilerDiag.localNotationOnPublicTermDiagnostic(
            item.name,
            item.name_span,
        ));
        return error.LocalNotationOnPublicTerm;
    }
    const entry = parser.parseLocalNotationText(
        item.text,
        item.span.start,
        term_id,
    ) catch |err| {
        self.setDiagnostic(localNotationParseDiagnostic(parser, item, err));
        return err;
    };
    try env.addLocalNotation(entry.term_id, entry.token);
}

fn localNotationParseDiagnostic(
    parser: *const MM0Parser,
    item: NotationItem,
    err: CompilerDiag.DiagnosticError,
) Diagnostic {
    return .{
        .kind = .generic,
        .err = err,
        .source = .proof,
        .name = item.name,
        .span = CompilerDiag.mathSpanToSpanOpt(parser.diagnosticSpan()) orelse
            item.name_span,
    };
}

pub fn processLocalDefItem(
    self: *CompilerContext,
    allocator: std.mem.Allocator,
    parser: *MM0Parser,
    env: *GlobalEnv,
    registry: *RewriteRegistry,
    def: DefItem,
    emit: ?*Output,
) !void {
    // Covers both a missing tail and a dummy-only filler tail: neither
    // declares the signature a local def needs.
    if (!def.isLocalDef()) {
        self.setDiagnostic(CompilerDiag.unexpectedProofDefDiagnostic(
            def.name,
            def.name_span,
        ));
        return error.UnexpectedProofDefItem;
    }
    const header_tail = def.header_tail.?;
    const term_stmt = parser.parseLocalDefText(
        def.name,
        .{ .start = def.name_span.start, .end = def.name_span.end },
        header_tail,
        def.body.text,
        proofMathTextSpan(def.body.span),
    ) catch |err| {
        self.setDiagnostic(localDefParseDiagnostic(parser, def, err));
        return err;
    };

    validateDefinitionBody(
        self,
        allocator,
        parser,
        env,
        term_stmt,
        .proof,
        def.body.span,
    ) catch |err| return err;

    if (emit) |out| {
        const term_record = CompilerEmit.compileTermRecord(
            allocator,
            parser,
            term_stmt,
        ) catch |err| {
            self.setDiagnostic(localDefParseDiagnostic(parser, def, err));
            return err;
        };
        try out.terms.append(allocator, term_record);
        const body = CompilerEmit.buildDefProofBody(
            allocator,
            parser,
            term_stmt,
        ) catch |err| {
            self.setDiagnostic(localDefParseDiagnostic(parser, def, err));
            return err;
        };
        try out.statements.append(allocator, .{
            .cmd = .LocalDef,
            .body = body,
        });
    }

    // Same directives as an .mm0 term (@acui, @conversion), attached to the
    // def item.
    registerTerm(
        self,
        allocator,
        parser,
        env,
        registry,
        term_stmt,
        .{ .proof = .{
            .annotations = def.annotations,
            .name_span = def.name_span,
        } },
    ) catch |err| {
        self.setIfMissing(.{
            .kind = .generic,
            .err = CompilerDiag.narrowDiagnosticError(err),
            .source = .proof,
            .name = def.name,
            .span = def.name_span,
        });
        return err;
    };
}

/// A public def's body filler takes no `@directive` metadata: the directives
/// belong on the `.mm0` declaration, which already carries them. Plain `--|`
/// prose is a doc comment and is fine anywhere.
pub fn rejectDefAnnotations(self: *CompilerContext, def: DefItem) !void {
    for (def.annotations) |ann| {
        if (!std.mem.startsWith(u8, ann, "@")) continue;
        self.setDiagnostic(CompilerDiag.unsupportedProofDefAnnotationDiagnostic(
            def.name,
            def.name_span,
        ));
        return error.UnsupportedProofDefAnnotation;
    }
}

pub fn localDefParseDiagnostic(
    parser: *const MM0Parser,
    def: DefItem,
    err: CompilerDiag.DiagnosticError,
) Diagnostic {
    var diag = Diagnostic{
        .kind = .generic,
        .err = err,
        .source = .proof,
        .name = def.name,
        .span = CompilerDiag.mathSpanToSpanOpt(parser.diagnosticSpan()) orelse
            def.name_span,
    };
    if (err == error.UnknownMathToken) {
        if (parser.mathError()) |math_err| {
            switch (math_err) {
                .unknown_token => |token| {
                    diag.detail = .{ .unknown_math_token = .{
                        .token = token.text,
                    } };
                },
                else => {},
            }
        }
    }
    return diag;
}

pub fn processAssertion(
    self: *CompilerContext,
    allocator: std.mem.Allocator,
    parser: *MM0Parser,
    env: *GlobalEnv,
    registry: *RewriteRegistry,
    rule_catalog: *const RuleCatalog.Catalog,
    fresh_bindings: *std.AutoHashMap(u32, []const FreshDecl),
    freshen_bindings: *std.AutoHashMap(u32, []const FreshenDecl),
    views: *std.AutoHashMap(u32, ViewDecl),
    sort_vars: *SortVarRegistry,
    proof_parser: *?ProofItemStream,
    assertion: AssertionStmt,
    emit: ?*Output,
) !void {
    if (assertion.kind != .theorem) {
        return try processNonTheoremAssertion(
            self,
            allocator,
            parser,
            env,
            registry,
            rule_catalog,
            fresh_bindings,
            freshen_bindings,
            views,
            assertion,
            emit,
        );
    }

    if (proof_parser.*) |*proofs| {
        var theorem = TheoremContext.init(allocator);
        defer theorem.deinit();

        try theorem.seedAssertion(assertion);
        const theorem_concl = try theorem.internParsedExpr(assertion.concl);
        const block = try nextTheoremBlock(
            self,
            allocator,
            parser,
            env,
            registry,
            rule_catalog,
            fresh_bindings,
            freshen_bindings,
            views,
            sort_vars,
            proofs,
            assertion.name,
            CompilerDiag.mathSpanToSpan(assertion.name_span),
            emit,
        );
        const checked = Check.checkTheoremBlock(
            self,
            allocator,
            parser,
            env,
            registry,
            rule_catalog,
            fresh_bindings,
            freshen_bindings,
            views,
            sort_vars,
            assertion,
            block,
            &theorem,
            theorem_concl,
        ) catch |err| {
            self.setIfMissing(
                CompilerDiag.theoremDiagnostic(
                    assertion.name,
                    block.name_span,
                    .proof,
                    CompilerDiag.narrowDiagnosticError(err),
                ),
            );
            return err;
        };
        if (emit) |out| {
            const unify = try CompilerEmit.buildAssertionUnifyStream(
                allocator,
                &theorem,
                theorem_concl,
            );
            const args = try CompilerEmit.buildArgArray(parser, assertion.args);
            const hyp_names = try CompilerEmit.buildHypNames(
                allocator,
                assertion.hyps.len,
            );
            const body = CompilerEmit.buildTheoremProofBody(
                allocator,
                &theorem,
                env,
                checked,
            ) catch |err| {
                self.setIfMissing(
                    CompilerDiag.theoremDiagnostic(
                        assertion.name,
                        block.name_span,
                        .proof,
                        CompilerDiag.narrowDiagnosticError(err),
                    ),
                );
                return err;
            };
            try out.theorems.append(allocator, .{
                .args = args,
                .unify = unify,
                .name = assertion.name,
                .var_names = try CompilerEmit.buildTheoremVarNames(
                    allocator,
                    assertion.arg_names,
                    theorem.theorem_dummies.items.len,
                ),
                .hyp_names = hyp_names,
            });
            try out.statements.append(allocator, .{
                .cmd = .Thm,
                .body = body,
            });
        }
    }

    try registerAssertion(
        self,
        allocator,
        parser,
        env,
        registry,
        fresh_bindings,
        freshen_bindings,
        views,
        assertion,
        .mm0,
    );
}

pub fn processNonTheoremAssertion(
    self: *CompilerContext,
    allocator: std.mem.Allocator,
    parser: *MM0Parser,
    env: *GlobalEnv,
    registry: *RewriteRegistry,
    _: *const RuleCatalog.Catalog,
    fresh_bindings: *std.AutoHashMap(u32, []const FreshDecl),
    freshen_bindings: *std.AutoHashMap(u32, []const FreshenDecl),
    views: *std.AutoHashMap(u32, ViewDecl),
    assertion: AssertionStmt,
    emit: ?*Output,
) !void {
    if (emit) |out| {
        var theorem = TheoremContext.init(allocator);
        defer theorem.deinit();
        try theorem.seedAssertion(assertion);
        const theorem_concl = try theorem.internParsedExpr(assertion.concl);
        const unify = try CompilerEmit.buildAssertionUnifyStream(
            allocator,
            &theorem,
            theorem_concl,
        );
        const args = try CompilerEmit.buildArgArray(parser, assertion.args);
        const hyp_names = try CompilerEmit.buildHypNames(
            allocator,
            assertion.hyps.len,
        );
        const body = try CompilerEmit.buildAxiomProofBody(
            allocator,
            &theorem,
            theorem_concl,
        );
        try out.theorems.append(allocator, .{
            .args = args,
            .unify = unify,
            .name = assertion.name,
            .var_names = try CompilerEmit.buildTheoremVarNames(
                allocator,
                assertion.arg_names,
                theorem.theorem_dummies.items.len,
            ),
            .hyp_names = hyp_names,
        });
        try out.statements.append(allocator, .{
            .cmd = .Axiom,
            .body = body,
        });
    }

    try registerAssertion(
        self,
        allocator,
        parser,
        env,
        registry,
        fresh_bindings,
        freshen_bindings,
        views,
        assertion,
        .mm0,
    );
}

pub fn nextTheoremBlock(
    self: *CompilerContext,
    allocator: std.mem.Allocator,
    parser: *MM0Parser,
    env: *GlobalEnv,
    registry: *RewriteRegistry,
    rule_catalog: *const RuleCatalog.Catalog,
    fresh_bindings: *std.AutoHashMap(u32, []const FreshDecl),
    freshen_bindings: *std.AutoHashMap(u32, []const FreshenDecl),
    views: *std.AutoHashMap(u32, ViewDecl),
    sort_vars: *const SortVarRegistry,
    proofs: *ProofItemStream,
    theorem_name: []const u8,
    theorem_name_span: Span,
    emit: ?*Output,
) !TheoremBlock {
    while (true) {
        const item = proofs.next() catch |err| {
            self.setDiagnostic(CompilerDiag.proofParserDiagnostic(
                &proofs.parser,
                theorem_name,
                err,
            ));
            return err;
        } orelse {
            self.setDiagnostic(CompilerDiag.missingProofBlockDiagnostic(
                theorem_name,
                theorem_name_span,
            ));
            return error.MissingProofBlock;
        };
        switch (item) {
            .block => |block| {
                if (block.kind == .lemma) {
                    try processLocalProofBlock(
                        self,
                        allocator,
                        parser,
                        env,
                        registry,
                        rule_catalog,
                        fresh_bindings,
                        freshen_bindings,
                        views,
                        sort_vars,
                        block,
                        emit,
                    );
                    continue;
                }
                if (!std.mem.eql(u8, block.name, theorem_name)) {
                    self.setDiagnostic(
                        CompilerDiag.theoremNameMismatchDiagnostic(
                            theorem_name,
                            block.name,
                            block.name_span,
                        ),
                    );
                    return error.TheoremNameMismatch;
                }
                return block;
            },
            .def => |def| {
                self.setDiagnostic(CompilerDiag.unexpectedProofDefDiagnostic(
                    def.name,
                    def.name_span,
                ));
                return error.UnexpectedProofDefItem;
            },
            .notation => |notation| {
                self.setDiagnostic(CompilerDiag.unexpectedProofDefDiagnostic(
                    notation.name,
                    notation.name_span,
                ));
                return error.UnexpectedProofDefItem;
            },
        }
    }
}

pub fn parseLemmaAssertion(
    self: *CompilerContext,
    allocator: std.mem.Allocator,
    parser: *MM0Parser,
    block: TheoremBlock,
) !AssertionStmt {
    const src = try std.fmt.allocPrint(
        allocator,
        "theorem {s}{s};",
        .{ block.name, block.header_tail },
    );
    return parser.parseAssertionText(src, .theorem, true) catch |err| {
        var diag = CompilerDiag.lemmaHeaderDiagnostic(
            block.name,
            block.header_span,
            err,
        );
        CompilerDiag.narrowLemmaHeaderDiagnostic(
            &diag,
            parser,
            "theorem ".len + block.name.len,
            block.header_tail_span,
        );
        self.setDiagnostic(diag);
        return err;
    };
}

pub fn processLocalProofBlock(
    self: *CompilerContext,
    allocator: std.mem.Allocator,
    parser: *MM0Parser,
    env: *GlobalEnv,
    registry: *RewriteRegistry,
    rule_catalog: *const RuleCatalog.Catalog,
    fresh_bindings: *std.AutoHashMap(u32, []const FreshDecl),
    freshen_bindings: *std.AutoHashMap(u32, []const FreshenDecl),
    views: *std.AutoHashMap(u32, ViewDecl),
    sort_vars: *const SortVarRegistry,
    block: TheoremBlock,
    emit: ?*Output,
) !void {
    const assertion = try parseLemmaAssertion(self, allocator, parser, block);

    var theorem = TheoremContext.init(allocator);
    defer theorem.deinit();
    try theorem.seedAssertion(assertion);
    const theorem_concl = try theorem.internParsedExpr(assertion.concl);

    const checked = Check.checkTheoremBlock(
        self,
        allocator,
        parser,
        env,
        registry,
        rule_catalog,
        fresh_bindings,
        freshen_bindings,
        views,
        sort_vars,
        assertion,
        block,
        &theorem,
        theorem_concl,
    ) catch |err| {
        self.setIfMissing(
            CompilerDiag.theoremDiagnostic(
                assertion.name,
                block.header_span,
                .proof,
                CompilerDiag.narrowDiagnosticError(err),
            ),
        );
        return err;
    };

    if (emit) |out| {
        const unify = try CompilerEmit.buildAssertionUnifyStream(
            allocator,
            &theorem,
            theorem_concl,
        );
        const args = try CompilerEmit.buildArgArray(parser, assertion.args);
        const hyp_names = try CompilerEmit.buildHypNames(
            allocator,
            assertion.hyps.len,
        );
        const body = CompilerEmit.buildTheoremProofBody(
            allocator,
            &theorem,
            env,
            checked,
        ) catch |err| {
            self.setIfMissing(
                CompilerDiag.theoremDiagnostic(
                    assertion.name,
                    block.header_span,
                    .proof,
                    CompilerDiag.narrowDiagnosticError(err),
                ),
            );
            return err;
        };
        try out.theorems.append(allocator, .{
            .args = args,
            .unify = unify,
            .name = assertion.name,
            .var_names = try CompilerEmit.buildTheoremVarNames(
                allocator,
                assertion.arg_names,
                theorem.theorem_dummies.items.len,
            ),
            .hyp_names = hyp_names,
        });
        try out.statements.append(allocator, .{
            .cmd = .LocalThm,
            .body = body,
        });
    }

    registerAssertion(
        self,
        allocator,
        parser,
        env,
        registry,
        fresh_bindings,
        freshen_bindings,
        views,
        assertion,
        .{ .proof = .{
            .annotations = block.annotations,
            .name_span = block.name_span,
        } },
    ) catch |err| {
        self.setIfMissing(
            CompilerDiag.proofBlockDiagnostic(
                block.name,
                block.header_span,
                CompilerDiag.narrowDiagnosticError(err),
            ),
        );
        return err;
    };
}

pub fn addAssertionToEnv(
    ctx: ?*CompilerContext,
    env: *GlobalEnv,
    assertion: AssertionStmt,
    diag_name: []const u8,
    span: ?Span,
    source: DiagnosticSource,
) !void {
    env.addStmt(.{ .assertion = assertion }) catch |err| {
        if (err == error.DuplicateRuleName) {
            if (ctx) |c| c.setDiagnostic(CompilerDiag.duplicateRuleNameDiagnostic(
                diag_name,
                span,
                source,
            ));
        }
        return err;
    };
}
