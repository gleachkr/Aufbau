const std = @import("std");
const GlobalEnv = @import("../env.zig").GlobalEnv;
const RewriteRegistry = @import("../rewrite_registry.zig").RewriteRegistry;
const CompilerDiag = @import("../diag.zig");
const FreshSelect = @import("./fresh_select.zig");
const CompilerHoles = @import("./holes.zig");
const CompilerViews = @import("../views.zig");
const CompilerVars = @import("./vars.zig");
const CompilerContext = @import("./context.zig").CompilerContext;
const AssertionStmt = @import("../parse_recovery.zig").AssertionStmt;
const MathSpan = @import("../parse_recovery.zig").MathSpan;
const MM0Parser = @import("../parse_recovery.zig").MM0Parser;
const SortStmt = @import("../parse_recovery.zig").SortStmt;
const TermStmt = @import("../parse_recovery.zig").TermStmt;

pub const ViewDecl = CompilerViews.ViewDecl;
pub const FreshDecl = FreshSelect.FreshDecl;
pub const FreshenDecl = FreshSelect.FreshenDecl;
pub const SortVarDecl = CompilerVars.SortVarDecl;
pub const SortVarRegistry = CompilerVars.SortVarRegistry;

const DiagnosticSource = CompilerDiag.DiagnosticSource;
const Span = @import("../proof_script.zig").Span;

// Everything a doc-comment annotation may legally say at each attachment
// site. @syntax lines carry grammar metadata for external front ends
// (aufbau-syntax); the compiler accepts them everywhere without reading
// them. Anything else off-list is downgraded to a warning as a typo
// safeguard — the annotation is ignored either way.
const known_sort_directives = [_][]const u8{ "@vars", "@hole", "@syntax" };
const known_term_directives = [_][]const u8{
    "@acui",
    "@conversion",
    "@syntax",
};
const known_assertion_directives = [_][]const u8{
    "@relation", "@rewrite",  "@alpha", "@conversion", "@compute",
    "@congr",    "@fallback", "@auto",  "@acui",       "@fresh",
    "@freshen",  "@dummy",    "@view",  "@recover",    "@abstract",
    "@syntax",
};

pub fn processSortMetadata(
    ctx: ?*CompilerContext,
    parser: *MM0Parser,
    sort_stmt: SortStmt,
    annotations: []const []const u8,
    annotation_spans: []const MathSpan,
    sort_vars: *SortVarRegistry,
) !void {
    try CompilerVars.processSortVarAnnotations(
        parser,
        sort_stmt.name,
        sort_stmt.modifiers,
        annotations,
        sort_vars,
    );
    try CompilerHoles.processSortHoleAnnotations(
        parser,
        sort_stmt.name,
        annotations,
        sort_vars,
    );
    warnUnknownAnnotations(
        ctx,
        &known_sort_directives,
        .mm0,
        sort_stmt.name,
        annotations,
        annotation_spans,
        null,
    );
}

pub fn processTermMetadata(
    ctx: ?*CompilerContext,
    env: *GlobalEnv,
    registry: *RewriteRegistry,
    term_stmt: TermStmt,
    annotations: []const []const u8,
    annotation_spans: []const MathSpan,
) !void {
    for (annotations, 0..) |ann, idx| {
        const directive = annotationDirective(ann) orelse continue;
        if (std.mem.eql(u8, directive, "@acui") or
            std.mem.eql(u8, directive, "@conversion"))
        {
            try registry.processAnnotations(
                env,
                term_stmt.name,
                annotations[idx .. idx + 1],
            );
        }
    }
    warnUnknownAnnotations(
        ctx,
        &known_term_directives,
        .mm0,
        term_stmt.name,
        annotations,
        annotation_spans,
        null,
    );
}

pub fn processAssertionMetadata(
    allocator: std.mem.Allocator,
    ctx: ?*CompilerContext,
    parser: *MM0Parser,
    env: *GlobalEnv,
    registry: *RewriteRegistry,
    fresh_bindings: *std.AutoHashMap(u32, []const FreshDecl),
    freshen_bindings: *std.AutoHashMap(u32, []const FreshenDecl),
    views: *std.AutoHashMap(u32, ViewDecl),
    assertion: AssertionStmt,
    annotations: []const []const u8,
    annotation_spans: []const MathSpan,
    source: DiagnosticSource,
    fallback_span: ?Span,
) !void {
    try registry.processAnnotations(env, assertion.name, annotations);
    try FreshSelect.processFreshAnnotations(
        allocator,
        parser,
        env,
        assertion,
        fresh_bindings,
        freshen_bindings,
        annotations,
    );
    try CompilerViews.processViewAnnotations(
        allocator,
        parser,
        env,
        assertion,
        annotations,
        views,
    );
    warnUnknownAnnotations(
        ctx,
        &known_assertion_directives,
        source,
        assertion.name,
        annotations,
        annotation_spans,
        fallback_span,
    );
}

/// Warn about annotations the parser had to throw away because a statement
/// that never surfaces to the compiler (a notation declaration, typically)
/// intervened before the next sort/term/assertion. @syntax legitimately
/// attaches to notation declarations, so it stays silent; anything else in
/// the dropped set had no effect and the author should know.
pub fn warnDroppedAnnotations(
    ctx: ?*CompilerContext,
    parser: *MM0Parser,
) void {
    defer parser.clearDroppedAnnotations();
    const compiler = ctx orelse return;
    const spans = parser.dropped_annotation_spans.items;
    for (parser.dropped_annotations.items, 0..) |ann, idx| {
        const directive = annotationDirective(ann) orelse continue;
        if (std.mem.eql(u8, directive, "@syntax")) continue;
        compiler.addWarning(.{
            .kind = .generic,
            .err = error.UnattachedAnnotation,
            .source = .mm0,
            .span = if (idx < spans.len)
                CompilerDiag.mathSpanToSpan(spans[idx])
            else
                null,
        });
    }
}

fn warnUnknownAnnotations(
    ctx: ?*CompilerContext,
    known: []const []const u8,
    source: DiagnosticSource,
    stmt_name: []const u8,
    annotations: []const []const u8,
    annotation_spans: []const MathSpan,
    fallback_span: ?Span,
) void {
    const compiler = ctx orelse return;
    outer: for (annotations, 0..) |ann, idx| {
        const directive = annotationDirective(ann) orelse continue;
        for (known) |known_directive| {
            if (std.mem.eql(u8, directive, known_directive)) continue :outer;
        }
        compiler.addWarning(.{
            .kind = .generic,
            .err = error.UnknownAnnotation,
            .source = source,
            .name = stmt_name,
            .span = if (idx < annotation_spans.len)
                CompilerDiag.mathSpanToSpan(annotation_spans[idx])
            else
                fallback_span,
        });
    }
}

fn annotationDirective(ann: []const u8) ?[]const u8 {
    if (ann.len == 0 or ann[0] != '@') return null;

    var iter = std.mem.tokenizeAny(u8, ann, " \t\r\n");
    return iter.next();
}
