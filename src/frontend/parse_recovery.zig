const std = @import("std");
const core = @import("../trusted/parse.zig");
const Expr = @import("../trusted/expressions.zig").Expr;

pub const ArgInfo = core.ArgInfo;
pub const binderDepsToBoundArgDeps = core.binderDepsToBoundArgDeps;
pub const boundArgDepsToBinderDeps = core.boundArgDepsToBinderDeps;
pub const AssertionKind = core.AssertionKind;
pub const AssertionStmt = core.AssertionStmt;
pub const MathParseError = core.MathParseError;
pub const MathSpan = core.MathSpan;
pub const MM0Stmt = core.MM0Stmt;
pub const PublicStmtHeader = core.PublicStmtHeader;
pub const PublicStmtHeaderKind = core.PublicStmtHeaderKind;
pub const SortStmt = core.SortStmt;
pub const TermStmt = core.TermStmt;
pub const Notation = core.Notation;

/// Every error the MM0 parser boundary can raise: the trusted core's
/// declared contract (`core.ParseError`) plus the wrapper's own filler and
/// local-def errors. Downstream, the compiler's diagnostic catalog
/// (`DiagnosticError`) is checked to cover this set at compile time, so a
/// new kernel parse error is a compile error until it has a summary.
pub const ParseError = core.ParseError || error{
    DuplicateTermName,
    DuplicateFillerBinderName,
    FillerBinderMustBeDummy,
    PublicDefBodyMustBeHeaderless,
};

pub const MM0Parser = struct {
    core: core.MM0Parser,
    pending_annotations: std.ArrayListUnmanaged([]const u8) = .{},
    pending_annotation_spans: std.ArrayListUnmanaged(MathSpan) = .{},
    last_annotations: []const []const u8 = &.{},
    last_annotation_spans: []const MathSpan = &.{},
    // Annotations discarded because a statement the parser consumes silently
    // (a notation declaration, typically) intervened before the next public
    // statement. Accumulated so the compiler can warn instead of losing them
    // without a trace; consumers clear via clearDroppedAnnotations.
    dropped_annotations: std.ArrayListUnmanaged([]const u8) = .{},
    dropped_annotation_spans: std.ArrayListUnmanaged(MathSpan) = .{},
    diagnostic_name_override: ?[]const u8 = null,
    diagnostic_span_override: ?MathSpan = null,
    math_span_override: ?MathSpan = null,

    pub fn init(src: []const u8, allocator: std.mem.Allocator) MM0Parser {
        return .{ .core = core.MM0Parser.init(src, allocator) };
    }

    pub fn deinit(self: *MM0Parser) void {
        self.pending_annotations.deinit(self.core.allocator);
        self.pending_annotation_spans.deinit(self.core.allocator);
        self.dropped_annotations.deinit(self.core.allocator);
        self.dropped_annotation_spans.deinit(self.core.allocator);
        self.freeLastAnnotations();
    }

    pub fn prepareNextPublicStatement(self: *MM0Parser) ParseError!void {
        self.clearDiagnosticOverrides();
        const start = self.core.pos;
        try self.core.prepareNextPublicStatement();
        try self.collectAnnotationsBetween(start, self.core.pos, true);
    }

    pub fn next(self: *MM0Parser) ParseError!?MM0Stmt {
        try self.prepareNextPublicStatement();
        if (self.core.pos >= self.core.src.len) return null;
        try self.flushAnnotations();
        const start = self.core.pos;
        const stmt = try self.core.next();
        try self.collectAnnotationsBetween(start, self.core.pos, true);
        return stmt;
    }

    pub fn peekNextPublicStmtHeader(self: *const MM0Parser) ?PublicStmtHeader {
        return self.core.peekNextPublicStmtHeader();
    }

    /// Preferred (last-declared) notation for `term_id`, for pretty-printing.
    pub fn notationForTerm(self: *const MM0Parser, term_id: u32) ?Notation {
        return self.core.notationForTerm(term_id);
    }

    /// Whether `term_id` is a declared coercion (printed transparently).
    pub fn isCoercionTerm(self: *const MM0Parser, term_id: u32) bool {
        return self.core.isCoercionTerm(term_id);
    }

    /// The set of declared coercion term ids, for mirroring into the
    /// compiler's `GlobalEnv` (the parser consumes `coercion` statements
    /// without emitting them).
    pub fn coercionTermIds(
        self: *const MM0Parser,
    ) *const std.AutoHashMap(u32, void) {
        return &self.core.coercion_terms;
    }

    /// Register a proof-side notation declaration (`prefix`, `infixl`,
    /// `infixr`, or general `notation`), written exactly as in an `.mm0`
    /// file. The core consumes notation statements silently on its way to
    /// the next public statement, so the text is fed to `next()` in place of
    /// the `.mm0` source. The call is transactional: the core registers a
    /// token's precedence and class before it finishes validating the
    /// statement, so on any failure the grammar tables are rolled back, and
    /// the text must register exactly one notation, on `term_id`. Returns
    /// that entry. `text_offset` is the statement's offset in the proof
    /// source: error spans are shifted to it, so `diagnosticSpan()` and
    /// `mathSpan()` read as proof-source offsets.
    pub fn parseLocalNotationText(
        self: *MM0Parser,
        text: []const u8,
        text_offset: usize,
        term_id: u32,
    ) ParseError!NotationEntry {
        self.clearDiagnosticOverrides();
        var snapshot = try GrammarSnapshot.take(&self.core);
        var committed = false;
        defer if (committed) snapshot.discard() else snapshot.restore(&self.core);

        const saved_src = self.core.src;
        const saved_pos = self.core.pos;
        defer {
            self.core.src = saved_src;
            self.core.pos = saved_pos;
        }
        self.core.src = text;
        self.core.pos = 0;
        const stmt = self.core.next() catch |err| {
            self.shiftDiagnosticSpans(text_offset);
            return err;
        };
        if (stmt != null) return error.UnexpectedKeyword;
        const entry = snapshot.newEntry(&self.core) orelse
            return error.UnexpectedKeyword;
        if (entry.term_id != term_id) return error.UnexpectedKeyword;
        committed = true;
        return entry;
    }

    /// The core's term id for `name`, if declared.
    pub fn lookupTermId(self: *const MM0Parser, name: []const u8) ?u32 {
        return self.core.term_names.get(name);
    }

    pub const NotationEntry = struct {
        term_id: u32,
        /// The token the declaration keys on: the leading token of a prefix
        /// or general notation, the operator of an infix one.
        token: []const u8,
    };

    /// The tables a notation statement mutates, cloned so a rejected
    /// proof-side declaration leaves no trace (`parseLocalNotationText`).
    const grammar_fields = [_][]const u8{
        "prefix_notations",
        "infix_notations",
        "term_notations",
        "token_precs",
        "infix_assoc",
        "leading_tokens",
        "infixy_tokens",
    };

    const GrammarSnapshot = struct {
        prefix_notations: @FieldType(core.MM0Parser, "prefix_notations"),
        infix_notations: @FieldType(core.MM0Parser, "infix_notations"),
        term_notations: @FieldType(core.MM0Parser, "term_notations"),
        token_precs: @FieldType(core.MM0Parser, "token_precs"),
        infix_assoc: @FieldType(core.MM0Parser, "infix_assoc"),
        leading_tokens: @FieldType(core.MM0Parser, "leading_tokens"),
        infixy_tokens: @FieldType(core.MM0Parser, "infixy_tokens"),

        fn take(
            parser: *const core.MM0Parser,
        ) std.mem.Allocator.Error!GrammarSnapshot {
            var snapshot: GrammarSnapshot = undefined;
            var taken: usize = 0;
            errdefer snapshot.discardFirst(taken);
            inline for (grammar_fields, 0..) |name, i| {
                @field(snapshot, name) = try @field(parser.*, name).clone();
                taken = i + 1;
            }
            return snapshot;
        }

        fn discardFirst(self: *GrammarSnapshot, count: usize) void {
            inline for (grammar_fields, 0..) |name, i| {
                if (i < count) @field(self, name).deinit();
            }
        }

        fn discard(self: *GrammarSnapshot) void {
            self.discardFirst(grammar_fields.len);
        }

        /// Put the cloned tables back in place of the live ones.
        fn restore(self: *GrammarSnapshot, parser: *core.MM0Parser) void {
            inline for (grammar_fields) |name| {
                @field(parser.*, name).deinit();
                @field(parser.*, name) = @field(self, name);
            }
        }

        /// The one notation registered since the snapshot; null when none
        /// or more than one was (the text held something other than a
        /// single notation statement).
        fn newEntry(
            self: *const GrammarSnapshot,
            parser: *const core.MM0Parser,
        ) ?NotationEntry {
            var found: ?NotationEntry = null;
            var prefix_it = parser.prefix_notations.iterator();
            while (prefix_it.next()) |entry| {
                if (self.prefix_notations.contains(entry.key_ptr.*)) continue;
                if (found != null) return null;
                found = .{
                    .term_id = entry.value_ptr.term_id,
                    .token = entry.key_ptr.*,
                };
            }
            var infix_it = parser.infix_notations.iterator();
            while (infix_it.next()) |entry| {
                if (self.infix_notations.contains(entry.key_ptr.*)) continue;
                if (found != null) return null;
                found = .{
                    .term_id = entry.value_ptr.term_id,
                    .token = entry.key_ptr.*,
                };
            }
            return found;
        }
    };

    /// Every notation the core has registered, whichever stream declared it.
    /// Tokens are unique across both tables (the core rejects reuse), so an
    /// entry identifies one declaration.
    pub const NotationIterator = struct {
        prefix: @FieldType(core.MM0Parser, "prefix_notations").Iterator,
        infix: @FieldType(core.MM0Parser, "infix_notations").Iterator,

        pub fn next(self: *NotationIterator) ?NotationEntry {
            if (self.prefix.next()) |entry| {
                return .{
                    .term_id = entry.value_ptr.term_id,
                    .token = entry.key_ptr.*,
                };
            }
            if (self.infix.next()) |entry| {
                return .{
                    .term_id = entry.value_ptr.term_id,
                    .token = entry.key_ptr.*,
                };
            }
            return null;
        }
    };

    pub fn notationIterator(self: *const MM0Parser) NotationIterator {
        return .{
            .prefix = self.core.prefix_notations.iterator(),
            .infix = self.core.infix_notations.iterator(),
        };
    }

    /// The `.mm0` source text a failed parse's diagnostic span covers, when
    /// the span lies in the `.mm0` source (not in swapped-in proof text).
    pub fn diagnosticSpanText(self: *const MM0Parser) ?[]const u8 {
        const span = self.diagnosticSpan() orelse return null;
        const src = self.core.src;
        if (span.start >= span.end or span.end > src.len) return null;
        return src[span.start..span.end];
    }

    /// The source text under the last math span, when it lies in the
    /// current source (the `.mm0` file, outside a swapped-in parse).
    pub fn mathSpanText(self: *const MM0Parser) ?[]const u8 {
        const span = self.mathSpan() orelse return null;
        const src = self.core.src;
        if (span.start >= span.end or span.end > src.len) return null;
        return src[span.start..span.end];
    }

    fn shiftDiagnosticSpans(self: *MM0Parser, offset: usize) void {
        if (self.core.diagnosticSpan()) |span| {
            self.diagnostic_span_override = shiftSpan(span, offset);
        }
        if (self.core.last_math_span) |span| {
            self.math_span_override = shiftSpan(span, offset);
        }
    }

    pub fn recoverToStatementBoundary(self: *MM0Parser) ParseError!void {
        self.clearDiagnosticOverrides();
        const start = self.core.pos;
        try self.core.skipToSemicolon();
        // No drop recording: this region is a malformed statement's tail, and
        // its diagnostic already covers everything written there.
        try self.collectAnnotationsBetween(start, self.core.pos, false);
    }

    pub fn discardPendingAnnotations(self: *MM0Parser) void {
        self.clearAnnotations();
    }

    pub fn diagnosticName(self: *const MM0Parser) ?[]const u8 {
        return self.diagnostic_name_override orelse self.core.diagnosticName();
    }

    pub fn diagnosticSpan(self: *const MM0Parser) ?MathSpan {
        return self.diagnostic_span_override orelse self.core.diagnosticSpan();
    }

    pub fn mathError(self: *const MM0Parser) ?MathParseError {
        return self.core.last_math_error;
    }

    pub fn mathSpan(self: *const MM0Parser) ?MathSpan {
        return self.math_span_override orelse self.core.last_math_span;
    }

    pub fn expectedChar(self: *const MM0Parser) ?u8 {
        return self.core.expected_char;
    }

    pub fn parseAssertionText(
        self: *MM0Parser,
        src: []const u8,
        kind: AssertionKind,
        is_local: bool,
    ) ParseError!AssertionStmt {
        self.clearDiagnosticOverrides();
        return try self.core.parseAssertionText(src, kind, is_local);
    }

    pub fn parsePublicDefBodyText(
        self: *MM0Parser,
        stmt: TermStmt,
        math: []const u8,
        math_span: ?MathSpan,
    ) ParseError!*const Expr {
        self.clearDiagnosticOverrides();
        return try self.core.parsePublicDefBodyText(stmt, math, math_span);
    }

    pub fn parseLocalDefText(
        self: *MM0Parser,
        name: []const u8,
        name_span: MathSpan,
        header_tail: []const u8,
        body: []const u8,
        body_span: ?MathSpan,
    ) ParseError!TermStmt {
        self.clearDiagnosticOverrides();
        if (self.core.term_names.contains(name)) {
            self.diagnostic_name_override = name;
            self.diagnostic_span_override = name_span;
            return error.DuplicateTermName;
        }

        const synthetic_body_start = "def ".len + name.len +
            " ".len + header_tail.len + " = $".len;
        const synthetic_body_span = MathSpan{
            .start = synthetic_body_start,
            .end = synthetic_body_start + body.len,
        };
        const src = try std.fmt.allocPrint(
            self.core.allocator,
            "def {s} {s} = ${s}$;",
            .{ name, header_tail, body },
        );

        var term = self.core.parseTermText(src, true) catch |err| {
            if (body_span) |real_body_span| {
                self.remapSyntheticBodyDiagnostic(
                    synthetic_body_span,
                    real_body_span,
                );
            }
            return err;
        };
        term.name = name;
        term.name_span = name_span;
        return term;
    }

    /// Extend a bodyless public def's parsed .mm0 statement with the extra
    /// hidden dummies declared on its .auf filler:
    /// `def name (.d: obj) = $ ... $`. The visible signature stays with the
    /// .mm0 declaration, so every binder group in the tail must contain only
    /// `.name` dummy binders. New dummies are appended after the
    /// .mm0-declared ones, with bound-dep bits positioned after all existing
    /// bound variables (mirroring how the core parser numbers binders).
    /// `tail_start` is the tail's absolute offset in the proof source; error
    /// spans are reported relative to it via `diagnosticSpan()`.
    pub fn extendStmtWithFillerDummies(
        self: *MM0Parser,
        stmt: TermStmt,
        tail: []const u8,
        tail_start: usize,
    ) ParseError!TermStmt {
        self.clearDiagnosticOverrides();
        self.diagnostic_name_override = stmt.name;

        var scanned = std.ArrayListUnmanaged(ScannedFillerDummy){};
        defer scanned.deinit(self.core.allocator);
        try self.scanFillerDummyTail(tail, tail_start, &scanned);

        var bound_count: usize = stmt.dummy_args.len;
        for (stmt.args) |arg| {
            if (arg.bound) bound_count += 1;
        }

        const allocator = self.core.allocator;
        const old_len = stmt.dummy_args.len;
        const new_infos = try allocator.alloc(
            ArgInfo,
            old_len + scanned.items.len,
        );
        const new_names = try allocator.alloc(
            ?[]const u8,
            old_len + scanned.items.len,
        );
        const new_exprs = try allocator.alloc(
            *const Expr,
            old_len + scanned.items.len,
        );
        @memcpy(new_infos[0..old_len], stmt.dummy_args);
        @memcpy(new_names[0..old_len], stmt.dummy_names);
        @memcpy(new_exprs[0..old_len], stmt.dummy_exprs);

        for (scanned.items, old_len..) |dummy, idx| {
            if (dummy.name) |name| {
                if (bindsName(stmt, new_names[0..idx], name)) {
                    return self.fillerError(
                        error.DuplicateFillerBinderName,
                        tail_start,
                        dummy.name_span,
                    );
                }
                if (self.core.isRegisteredHoleToken(name)) {
                    return self.fillerError(
                        error.HoleTokenNameCollision,
                        tail_start,
                        dummy.name_span,
                    );
                }
                if (self.core.token_precs.contains(name)) {
                    return self.fillerError(
                        error.BinderTokenCollision,
                        tail_start,
                        dummy.name_span,
                    );
                }
            }
            const sort_id = self.core.sort_names.get(dummy.sort_name) orelse {
                return self.fillerError(
                    error.UnknownSort,
                    tail_start,
                    dummy.sort_span,
                );
            };
            if (bound_count >= core.max_bound_vars) {
                return self.fillerError(
                    error.TooManyBoundVars,
                    tail_start,
                    dummy.name_span,
                );
            }
            const expr = try allocator.create(Expr);
            expr.* = .{ .variable = .{
                .sort = @intCast(sort_id),
                .bound = true,
                .deps = @as(u55, 1) << @intCast(bound_count),
            } };
            bound_count += 1;
            new_infos[idx] = .{
                .sort_name = dummy.sort_name,
                .bound = true,
                .deps = expr.variable.deps,
            };
            new_names[idx] = dummy.name;
            new_exprs[idx] = expr;
        }

        var extended = stmt;
        extended.dummy_args = new_infos;
        extended.dummy_names = new_names;
        extended.dummy_exprs = new_exprs;
        return extended;
    }

    /// Scan the filler tail as binder groups of dummies. Structural
    /// violations (not a binder group, missing sort, unclosed group) fall
    /// back to the headerless-filler error; a well-formed binder that just
    /// isn't a dummy gets the specific error.
    fn scanFillerDummyTail(
        self: *MM0Parser,
        tail: []const u8,
        tail_start: usize,
        out: *std.ArrayListUnmanaged(ScannedFillerDummy),
    ) ParseError!void {
        var pos: usize = 0;
        while (true) {
            skipFillerSpace(tail, &pos);
            if (pos >= tail.len) return;
            const open = tail[pos];
            if (open != '(' and open != '{') {
                return self.fillerError(
                    error.PublicDefBodyMustBeHeaderless,
                    tail_start,
                    .{ .start = pos, .end = tail.len },
                );
            }
            const close: u8 = if (open == '(') ')' else '}';
            pos += 1;

            const group_start = out.items.len;
            while (true) {
                skipFillerSpace(tail, &pos);
                if (pos >= tail.len) {
                    return self.fillerError(
                        error.PublicDefBodyMustBeHeaderless,
                        tail_start,
                        .{ .start = pos, .end = tail.len },
                    );
                }
                if (tail[pos] == ':') break;
                if (tail[pos] != '.') {
                    const span = fillerIdentSpan(tail, pos);
                    return self.fillerError(
                        error.FillerBinderMustBeDummy,
                        tail_start,
                        span,
                    );
                }
                pos += 1;
                const name_span = fillerIdentSpan(tail, pos);
                if (name_span.end == name_span.start) {
                    return self.fillerError(
                        error.PublicDefBodyMustBeHeaderless,
                        tail_start,
                        .{ .start = pos, .end = tail.len },
                    );
                }
                const name = tail[name_span.start..name_span.end];
                pos = name_span.end;
                try out.append(self.core.allocator, .{
                    .name = if (std.mem.eql(u8, name, "_")) null else name,
                    .name_span = name_span,
                    .sort_name = undefined,
                    .sort_span = undefined,
                });
            }
            if (out.items.len == group_start) {
                return self.fillerError(
                    error.PublicDefBodyMustBeHeaderless,
                    tail_start,
                    .{ .start = pos, .end = tail.len },
                );
            }
            pos += 1;
            skipFillerSpace(tail, &pos);
            const sort_span = fillerIdentSpan(tail, pos);
            if (sort_span.end == sort_span.start) {
                return self.fillerError(
                    error.PublicDefBodyMustBeHeaderless,
                    tail_start,
                    .{ .start = pos, .end = tail.len },
                );
            }
            const sort_name = tail[sort_span.start..sort_span.end];
            pos = sort_span.end;
            skipFillerSpace(tail, &pos);
            if (pos >= tail.len or tail[pos] != close) {
                return self.fillerError(
                    error.PublicDefBodyMustBeHeaderless,
                    tail_start,
                    .{ .start = pos, .end = tail.len },
                );
            }
            pos += 1;
            for (out.items[group_start..]) |*dummy| {
                dummy.sort_name = sort_name;
                dummy.sort_span = sort_span;
            }
        }
    }

    fn fillerError(
        self: *MM0Parser,
        err: ParseError,
        tail_start: usize,
        rel_span: MathSpan,
    ) ParseError {
        self.diagnostic_span_override = .{
            .start = tail_start + rel_span.start,
            .end = tail_start + rel_span.end,
        };
        return err;
    }

    pub fn parseFormulaText(
        self: *MM0Parser,
        math: []const u8,
        vars: *const std.StringHashMap(*const Expr),
    ) ParseError!*const Expr {
        self.clearDiagnosticOverrides();
        return try self.core.parseFormulaText(math, vars);
    }

    pub fn parseHoleyFormulaText(
        self: *MM0Parser,
        math: []const u8,
        vars: *const std.StringHashMap(*const Expr),
    ) ParseError!*const Expr {
        self.clearDiagnosticOverrides();
        return try self.core.parseFormulaTextAllowHoles(math, vars);
    }

    pub fn parseArgText(
        self: *MM0Parser,
        math: []const u8,
        vars: *const std.StringHashMap(*const Expr),
        arg: ArgInfo,
    ) ParseError!*const Expr {
        self.clearDiagnosticOverrides();
        return try self.core.parseArgText(math, vars, arg);
    }

    pub fn parseMathText(
        self: *MM0Parser,
        math: []const u8,
        vars: *const std.StringHashMap(*const Expr),
    ) ParseError!*const Expr {
        self.clearDiagnosticOverrides();
        return try self.core.parseMathText(math, vars);
    }

    pub fn isRegisteredHoleToken(self: *const MM0Parser, token: []const u8) bool {
        return self.core.isRegisteredHoleToken(token);
    }

    pub fn registerHoleTokenForSort(
        self: *MM0Parser,
        sort_name: []const u8,
        token: []const u8,
    ) !void {
        return self.core.registerHoleTokenForSort(sort_name, token);
    }

    fn clearDiagnosticOverrides(self: *MM0Parser) void {
        self.diagnostic_name_override = null;
        self.diagnostic_span_override = null;
        self.math_span_override = null;
    }

    fn flushAnnotations(self: *MM0Parser) !void {
        self.freeLastAnnotations();
        if (self.pending_annotations.items.len > 0) {
            self.last_annotations = try self.pending_annotations.toOwnedSlice(
                self.core.allocator,
            );
            self.last_annotation_spans =
                try self.pending_annotation_spans.toOwnedSlice(
                    self.core.allocator,
                );
        }
    }

    fn clearAnnotations(self: *MM0Parser) void {
        self.pending_annotations.clearRetainingCapacity();
        self.pending_annotation_spans.clearRetainingCapacity();
        self.freeLastAnnotations();
    }

    fn freeLastAnnotations(self: *MM0Parser) void {
        if (self.last_annotations.len > 0) {
            self.core.allocator.free(self.last_annotations);
            self.last_annotations = &.{};
        }
        if (self.last_annotation_spans.len > 0) {
            self.core.allocator.free(self.last_annotation_spans);
            self.last_annotation_spans = &.{};
        }
    }

    pub fn clearDroppedAnnotations(self: *MM0Parser) void {
        self.dropped_annotations.clearRetainingCapacity();
        self.dropped_annotation_spans.clearRetainingCapacity();
    }

    fn collectAnnotationsBetween(
        self: *MM0Parser,
        start: usize,
        end: usize,
        record_drops: bool,
    ) !void {
        var pos = start;
        while (pos < end) {
            const ch = self.core.src[pos];
            if (ch == '$') {
                pos += 1;
                while (pos < end and self.core.src[pos] != '$') pos += 1;
                if (pos < end) pos += 1;
            } else if (ch == '"') {
                pos += 1;
                while (pos < end and self.core.src[pos] != '"') pos += 1;
                if (pos < end) pos += 1;
            } else if (ch == '-' and pos + 1 < end and
                self.core.src[pos + 1] == '-')
            {
                pos += 2;
                if (pos < end and self.core.src[pos] == '|') {
                    pos += 1;
                    while (pos < end and
                        (self.core.src[pos] == ' ' or
                            self.core.src[pos] == '\t'))
                    {
                        pos += 1;
                    }
                    const ann_start = pos;
                    while (pos < end and self.core.src[pos] != '\n') pos += 1;
                    var ann_end = pos;
                    while (ann_end > ann_start and
                        (self.core.src[ann_end - 1] == ' ' or
                            self.core.src[ann_end - 1] == '\t' or
                            self.core.src[ann_end - 1] == '\r'))
                    {
                        ann_end -= 1;
                    }
                    // A blank `--|` line is kept: prose annotations are
                    // doc comments, and an empty one is a paragraph break
                    // (the mm0-rs convention). Directive consumers see an
                    // empty string and skip it.
                    try self.pending_annotations.append(
                        self.core.allocator,
                        self.core.src[ann_start..ann_end],
                    );
                    try self.pending_annotation_spans.append(
                        self.core.allocator,
                        .{ .start = ann_start, .end = ann_end },
                    );
                } else {
                    while (pos < end and self.core.src[pos] != '\n') pos += 1;
                }
            } else if (ch == ';') {
                if (record_drops) {
                    try self.dropped_annotations.appendSlice(
                        self.core.allocator,
                        self.pending_annotations.items,
                    );
                    try self.dropped_annotation_spans.appendSlice(
                        self.core.allocator,
                        self.pending_annotation_spans.items,
                    );
                }
                self.pending_annotations.clearRetainingCapacity();
                self.pending_annotation_spans.clearRetainingCapacity();
                pos += 1;
            } else {
                pos += 1;
            }
        }
    }

    fn shiftSpan(span: MathSpan, offset: usize) MathSpan {
        return .{ .start = span.start + offset, .end = span.end + offset };
    }

    fn remapSyntheticBodyDiagnostic(
        self: *MM0Parser,
        synthetic_body_span: MathSpan,
        real_body_span: MathSpan,
    ) void {
        const span = self.core.last_math_span orelse return;
        if (!spanTouches(span, synthetic_body_span)) return;
        self.math_span_override = remapSyntheticSpan(
            span,
            synthetic_body_span,
            real_body_span,
        );
        if (self.core.diagnosticSpan()) |error_span| {
            self.diagnostic_span_override = remapSyntheticSpan(
                error_span,
                synthetic_body_span,
                real_body_span,
            );
        } else {
            self.diagnostic_span_override = real_body_span;
        }
    }
};

const ScannedFillerDummy = struct {
    name: ?[]const u8,
    name_span: MathSpan,
    sort_name: []const u8,
    sort_span: MathSpan,
};

fn skipFillerSpace(tail: []const u8, pos: *usize) void {
    while (pos.* < tail.len) : (pos.* += 1) {
        switch (tail[pos.*]) {
            ' ', '\t', '\r', '\n' => {},
            else => return,
        }
    }
}

/// Span of the identifier at `pos` (empty span if none), using the core
/// parser's identifier character classes.
fn fillerIdentSpan(tail: []const u8, pos: usize) MathSpan {
    var end = pos;
    if (end < tail.len and
        (std.ascii.isAlphabetic(tail[end]) or tail[end] == '_'))
    {
        end += 1;
        while (end < tail.len and
            (std.ascii.isAlphanumeric(tail[end]) or tail[end] == '_'))
        {
            end += 1;
        }
    }
    return .{ .start = pos, .end = end };
}

fn bindsName(
    stmt: TermStmt,
    extra_dummy_names: []const ?[]const u8,
    name: []const u8,
) bool {
    for (stmt.arg_names) |maybe_name| {
        if (maybe_name) |existing| {
            if (std.mem.eql(u8, existing, name)) return true;
        }
    }
    for (extra_dummy_names) |maybe_name| {
        if (maybe_name) |existing| {
            if (std.mem.eql(u8, existing, name)) return true;
        }
    }
    return false;
}

fn spanTouches(span: MathSpan, target: MathSpan) bool {
    return span.start <= target.end and span.end >= target.start;
}

fn remapSyntheticSpan(
    span: MathSpan,
    synthetic_body_span: MathSpan,
    real_body_span: MathSpan,
) MathSpan {
    const start = std.math.clamp(
        span.start,
        synthetic_body_span.start,
        synthetic_body_span.end,
    );
    const end = std.math.clamp(
        span.end,
        synthetic_body_span.start,
        synthetic_body_span.end,
    );
    return .{
        .start = real_body_span.start + start - synthetic_body_span.start,
        .end = real_body_span.start + end - synthetic_body_span.start,
    };
}
