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

pub fn processSortMetadata(
    parser: *MM0Parser,
    sort_stmt: SortStmt,
    annotations: []const []const u8,
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
            continue;
        }
        // @syntax lines carry grammar metadata for external front ends
        // (aufbau-syntax); the compiler accepts them without reading them.
        if (std.mem.eql(u8, directive, "@syntax")) continue;
        const compiler = ctx orelse continue;
        compiler.addWarning(.{
            .kind = .generic,
            .err = error.UnknownTermAnnotation,
            .source = .mm0,
            .name = term_stmt.name,
            .span = if (idx < annotation_spans.len)
                CompilerDiag.mathSpanToSpan(annotation_spans[idx])
            else
                null,
        });
    }
}

fn annotationDirective(ann: []const u8) ?[]const u8 {
    if (ann.len == 0 or ann[0] != '@') return null;

    var iter = std.mem.tokenizeAny(u8, ann, " \t\r\n");
    return iter.next();
}

pub fn processAssertionMetadata(
    allocator: std.mem.Allocator,
    parser: *MM0Parser,
    env: *GlobalEnv,
    registry: *RewriteRegistry,
    fresh_bindings: *std.AutoHashMap(u32, []const FreshDecl),
    freshen_bindings: *std.AutoHashMap(u32, []const FreshenDecl),
    views: *std.AutoHashMap(u32, ViewDecl),
    assertion: AssertionStmt,
    annotations: []const []const u8,
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
}
