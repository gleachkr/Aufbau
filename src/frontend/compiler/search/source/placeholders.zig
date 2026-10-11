//! Finding search placeholders in a proof source: every `auto?`/`exact?`/
//! `apply?`/`conversion?` marker (for the LSP status diagnostics and the
//! search CLI), and the one at a source offset, with the path to it inside a
//! nested application.

const std = @import("std");
const ArenaAllocator = @import("../../../arena_allocator.zig").ArenaAllocator;
const tunables = @import("../tunables.zig");
const ProofScript = @import("../../../proof_script.zig");
const RuleApplication = ProofScript.RuleApplication;
const Span = ProofScript.Span;
const CompilerDiag = @import("../../../diag.zig");
const ProofParser = ProofScript.Parser;
const fixture_mod = @import("../fixture.zig");
const SourceTarget = fixture_mod.SourceTarget;

/// One search placeholder occurrence in a proof source, as enumerated by
/// `searchPlaceholders`. Spans index into the proof source; nothing borrows
/// the parse.
pub const SearchPlaceholder = struct {
    pub const Kind = enum {
        exact,
        apply,
        auto,
        conversion,

        pub fn keyword(self: Kind) []const u8 {
            return switch (self) {
                .exact => "exact?",
                .apply => "apply?",
                .auto => "auto?",
                .conversion => "conversion?",
            };
        }

        /// The parameter set this placeholder accepts (per-keyword
        /// validation in `tunables.validateSearchParams`).
        pub fn paramContext(self: Kind) tunables.ParamContext {
            return switch (self) {
                .exact => .exact,
                .apply => .apply,
                .auto => .auto,
                .conversion => .conversion,
            };
        }
    };

    kind: Kind,
    /// The placeholder application's span (keyword through refs) — the
    /// natural diagnostic underline. Falls inside the catchment `target_span`
    /// a search at this placeholder reports (the whole line for a top-level
    /// placeholder, this same span for a nested one).
    span: Span,
    /// The placeholder's `name: INTEGER` parameters, verbatim from the parse
    /// (name strings are slices of the proof source, not the parse arena).
    /// The LSP validates these per placeholder (`tunables.validateSearchParams`)
    /// to diagnose typos without running a search.
    params: []const ProofScript.SearchParam = &.{},
    /// The proof block and the line the placeholder sits in (slices of the
    /// proof source).
    theorem: []const u8 = "",
    label: []const u8 = "",
};

/// Enumerate every search placeholder (`exact?`/`apply?`/`auto?`) in
/// `proof_src`, top-level and nested, in source order. Used by the LSP to
/// publish a status diagnostic per placeholder. The parse is lenient, so a
/// broken proof line costs only itself; a parse error elsewhere (a broken
/// header) still ends the scan early (the compiler's own diagnostics cover
/// malformed source), returning whatever was collected before it. The result
/// is allocated on `allocator` (including each placeholder's non-empty
/// `params` array); parser transients are torn down before returning.
pub fn searchPlaceholders(
    allocator: std.mem.Allocator,
    proof_src: []const u8,
) ![]SearchPlaceholder {
    var parse_arena = ArenaAllocator.init(allocator);
    defer parse_arena.deinit();
    var out = std.ArrayListUnmanaged(SearchPlaceholder).empty;
    errdefer out.deinit(allocator);
    var parser = ProofParser.initLenient(parse_arena.allocator(), proof_src);
    while (parser.nextBlockSkippingLocalItems() catch null) |block| {
        for (block.lines) |line| {
            try collectSearchPlaceholders(
                allocator,
                &out,
                block.name,
                line.label,
                line.application,
            );
        }
    }
    return try out.toOwnedSlice(allocator);
}

/// What every host reports for a search placeholder before a search has
/// run at it: a warning on the placeholder, then an error on each of its
/// parameters `tunables.validateSearchParams` rejects (an invalid entry is
/// skipped, never fatal, so the valid ones still apply).
pub const PlaceholderNotice = struct {
    kind: enum { placeholder, parameter },
    /// The placeholder the notice is about.
    placeholder: SearchPlaceholder,
    /// The placeholder's span, or the rejected parameter's.
    span: Span,
    /// In the active diagnostic locale.
    message: []const u8,
};

/// The notices for every placeholder in `proof_src`, in source order (see
/// `searchPlaceholders`). Everything is allocated on `allocator`; use an
/// arena.
pub fn placeholderNotices(
    allocator: std.mem.Allocator,
    proof_src: []const u8,
) ![]PlaceholderNotice {
    var out = std.ArrayListUnmanaged(PlaceholderNotice).empty;
    for (try searchPlaceholders(allocator, proof_src)) |placeholder| {
        try out.append(allocator, .{
            .kind = .placeholder,
            .placeholder = placeholder,
            .span = placeholder.span,
            .message = try CompilerDiag.allocMessage(
                allocator,
                "search_placeholder",
                .{placeholder.kind.keyword()},
            ),
        });
        const issues = try tunables.validateSearchParams(
            allocator,
            placeholder.kind.paramContext(),
            placeholder.params,
        );
        for (issues) |issue| {
            try out.append(allocator, .{
                .kind = .parameter,
                .placeholder = placeholder,
                .span = issue.span,
                .message = issue.message,
            });
        }
    }
    return try out.toOwnedSlice(allocator);
}

fn collectSearchPlaceholders(
    allocator: std.mem.Allocator,
    out: *std.ArrayListUnmanaged(SearchPlaceholder),
    theorem: []const u8,
    label: []const u8,
    application: RuleApplication,
) !void {
    // Gate on the canonical predicate so this can't drift from what the
    // checker/search treat as a placeholder; the kind mapping below only
    // discriminates names that already passed it.
    if (ProofScript.isSearchPlaceholderRuleName(application.rule_name)) {
        const kind: SearchPlaceholder.Kind =
            if (std.mem.eql(u8, application.rule_name, "exact?"))
                .exact
            else if (std.mem.eql(u8, application.rule_name, "apply?"))
                .apply
            else if (std.mem.eql(u8, application.rule_name, "conversion?"))
                .conversion
            else
                .auto;
        // The param structs hold only source slices and values, but the
        // ARRAY lives on the parse arena — copy it onto the caller's
        // allocator alongside the placeholder itself (empty stays a literal
        // so param-free placeholders allocate nothing extra).
        const params: []const ProofScript.SearchParam =
            if (application.search_params.len == 0)
                &.{}
            else
                try allocator.dupe(
                    ProofScript.SearchParam,
                    application.search_params,
                );
        try out.append(allocator, .{
            .kind = kind,
            .span = application.span,
            .params = params,
            .theorem = theorem,
            .label = label,
        });
    }
    for (application.refs) |ref| switch (ref) {
        .application => |child| try collectSearchPlaceholders(
            allocator,
            out,
            theorem,
            label,
            child,
        ),
        .hyp, .line => {},
    };
}

pub fn findSearchLine(
    allocator: std.mem.Allocator,
    proof_src: []const u8,
    offset: usize,
    apply_at_offset: bool,
) !?SourceTarget {
    // Lenient, like every editor-facing parse of the proof source: a broken
    // sibling line must not cost the block its search targets. Incomplete
    // lines themselves have no rule application to target.
    var parser = ProofParser.initLenient(allocator, proof_src);
    while (try parser.nextBlockSkippingLocalItems()) |block| {
        for (block.lines, 0..) |line, line_index| {
            if (line.incomplete) continue;
            if (apply_at_offset and spanContains(
                line.application.rule_span,
                offset,
            )) {
                return .{
                    .block = block,
                    .line_index = line_index,
                    .path = &.{},
                };
            }
            if (ProofScript.isSearchPlaceholderRuleName(
                line.application.rule_name,
            )) {
                const span = line.application.ruleApplicationSpan();
                if (offset >= span.start and offset <= span.end) {
                    return .{
                        .block = block,
                        .line_index = line_index,
                        .path = &.{},
                    };
                }
                if (offset >= line.span.start and offset <= line.span.end) {
                    return .{
                        .block = block,
                        .line_index = line_index,
                        .path = &.{},
                    };
                }
            }
            if (try findNestedSearchPath(
                allocator,
                line.application,
                offset,
                apply_at_offset,
            )) |path| {
                return .{
                    .block = block,
                    .line_index = line_index,
                    .path = path,
                };
            }
        }
    }
    return null;
}

fn findNestedSearchPath(
    allocator: std.mem.Allocator,
    application: RuleApplication,
    offset: usize,
    apply_at_offset: bool,
) !?[]const usize {
    for (application.refs, 0..) |ref, idx| {
        const child = switch (ref) {
            .application => |app| app,
            .hyp, .line => continue,
        };
        if (!spanContains(child.span, offset)) continue;
        if ((apply_at_offset and spanContains(child.rule_span, offset)) or
            (!apply_at_offset and
                ProofScript.isSearchPlaceholderRuleName(child.rule_name)))
        {
            const path = try allocator.alloc(usize, 1);
            path[0] = idx;
            return path;
        }
        if (try findNestedSearchPath(
            allocator,
            child,
            offset,
            apply_at_offset,
        )) |suffix| {
            const path = try allocator.alloc(usize, suffix.len + 1);
            path[0] = idx;
            @memcpy(path[1..], suffix);
            return path;
        }
    }
    return null;
}

fn spanContains(span: Span, offset: usize) bool {
    return offset >= span.start and offset <= span.end;
}

pub fn applicationAtPath(
    root: RuleApplication,
    path: []const usize,
) ?RuleApplication {
    var current = root;
    for (path) |idx| {
        if (idx >= current.refs.len) return null;
        current = switch (current.refs[idx]) {
            .application => |app| app,
            .hyp, .line => return null,
        };
    }
    return current;
}
