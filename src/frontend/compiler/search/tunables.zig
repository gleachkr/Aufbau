//! Per-call search tunables: the `name: INTEGER` parameters a proof author
//! can put on an `auto?` placeholder (`auto? (depth: 8, fuel: 8192)`) to
//! widen ONE search without touching the engine defaults. The defaults stay
//! the bench-anchored global operating point (raising them globally is a
//! measured regression: max_depth=10 ~10x's doomed-search wall-clock across
//! a corpus for zero found-ness gain); a per-call override scopes the extra
//! cost to the one goal the author is actively working on.
//!
//! The parser accepts the parameter form only on search placeholders
//! (`proof_script.zig:parsePlaceholderBindings`), so nothing here is
//! reachable from a real rule application. Unknown names and out-of-range
//! values are skipped by `applySearchParams` and reported as editor
//! diagnostics via `validateSearchParams` — a typo'd parameter never
//! silently changes the search, and never blocks it either.

const std = @import("std");
const types = @import("./types.zig");
const ProofScript = @import("../../proof_script.zig");
const ConversionOptions = @import("./conversion.zig").Options;

pub const SearchParam = ProofScript.SearchParam;
pub const Span = ProofScript.Span;
pub const GenerateOptions = types.GenerateOptions;

/// Which placeholder keyword a parameter list is attached to; each keyword
/// accepts its own parameter set (`auto?` tunes the generator, `conversion?`
/// tunes the egraph, `exact?`/`apply?` accept none).
pub const ParamContext = enum { exact, apply, auto, conversion };

/// The `budget` parameter is written in billions of weighted work ticks —
/// per the `GlobalBudget` calibration, one unit ≈ 1 second of search work.
pub const ticks_per_budget_unit: u64 = 1_000_000_000;

const ParamKind = enum { depth, nodes, fuel, budget, iters };

const ParamSpec = struct {
    name: []const u8,
    kind: ParamKind,
    /// Inclusive value range. The lower bounds exclude values that can only
    /// make the search a guaranteed no-op (`depth: 0` finds nothing by
    /// construction); the upper bounds exclude values so large they are
    /// almost certainly a typo (and would make the editor unresponsive for
    /// hours). `budget: 0` is deliberately allowed: it disables the per-call
    /// work cap entirely, mirroring the bench's `--global-budget=0`.
    min: u64,
    max: u64,
};

/// Public so the failure report can clamp its "try '<param>: N'" suggestions
/// to values validation will accept.
pub const max_depth_value: u64 = 64;
pub const max_nodes_value: u64 = 1_000_000;
pub const max_fuel_value: u64 = 100_000_000;
pub const max_budget_value: u64 = 100_000;
pub const max_iters_value: u64 = 10_000;

const auto_specs = [_]ParamSpec{
    .{ .name = "depth", .kind = .depth, .min = 1, .max = max_depth_value },
    .{ .name = "nodes", .kind = .nodes, .min = 1, .max = max_nodes_value },
    .{ .name = "fuel", .kind = .fuel, .min = 1, .max = max_fuel_value },
    .{ .name = "budget", .kind = .budget, .min = 0, .max = max_budget_value },
};

const conversion_specs = [_]ParamSpec{
    .{ .name = "iters", .kind = .iters, .min = 1, .max = max_iters_value },
    .{ .name = "nodes", .kind = .nodes, .min = 1, .max = max_nodes_value },
};

/// For diagnostics: the accepted parameter names, comma-separated.
pub const known_param_names = "depth, nodes, fuel, budget";
pub const known_conversion_param_names = "iters, nodes";

fn specsFor(context: ParamContext) []const ParamSpec {
    return switch (context) {
        .auto => &auto_specs,
        .conversion => &conversion_specs,
        .exact, .apply => &.{},
    };
}

fn specForNameIn(
    table: []const ParamSpec,
    name: []const u8,
) ?ParamSpec {
    for (table) |spec| {
        if (std.mem.eql(u8, spec.name, name)) return spec;
    }
    return null;
}

fn specForName(name: []const u8) ?ParamSpec {
    return specForNameIn(&auto_specs, name);
}

/// Overlay the valid parameters onto `options`. Unknown names and
/// out-of-range values are skipped (never applied, never fatal) — they are
/// surfaced to the author separately by `validateSearchParams`. Later
/// duplicates win, matching the reading order of the source list.
pub fn applySearchParams(
    options: *GenerateOptions,
    params: []const SearchParam,
) void {
    for (params) |param| {
        const spec = specForName(param.name) orelse continue;
        if (param.value < spec.min or param.value > spec.max) continue;
        switch (spec.kind) {
            .depth => options.max_depth = @intCast(param.value),
            .nodes => options.max_nodes = @intCast(param.value),
            .fuel => options.fuel = @intCast(param.value),
            .budget => options.global_budget = if (param.value == 0)
                null
            else
                param.value * ticks_per_budget_unit,
            // `iters` is a conversion?-only parameter; it never appears in
            // `auto_specs`.
            .iters => {},
        }
    }
}

/// One rejected search parameter, with the source span to underline and an
/// allocator-owned message.
pub const ParamIssue = struct {
    span: Span,
    message: []const u8,
};

/// Overlay the valid `conversion?` parameters (`iters`, `nodes`) onto the
/// egraph options; same skip semantics as `applySearchParams`.
pub fn applyConversionParams(
    options: *ConversionOptions,
    params: []const SearchParam,
) void {
    for (params) |param| {
        const spec = specForNameIn(&conversion_specs, param.name) orelse {
            continue;
        };
        if (param.value < spec.min or param.value > spec.max) continue;
        switch (spec.kind) {
            .iters => options.max_iterations = @intCast(param.value),
            .nodes => options.max_nodes = @intCast(param.value),
            else => {},
        }
    }
}

/// Check a placeholder's parameter list and return an issue per rejected
/// entry (unknown name, out-of-range value, or any parameter on a
/// placeholder that accepts none). Messages are allocated on `allocator`;
/// the returned slice is owned by the caller.
pub fn validateSearchParams(
    allocator: std.mem.Allocator,
    context: ParamContext,
    params: []const SearchParam,
) ![]ParamIssue {
    var issues = std.ArrayListUnmanaged(ParamIssue){};
    errdefer {
        for (issues.items) |issue| allocator.free(issue.message);
        issues.deinit(allocator);
    }
    const table = specsFor(context);
    for (params) |param| {
        if (table.len == 0) {
            try appendIssue(
                allocator,
                &issues,
                param.span,
                "search parameters only apply to auto? and conversion? " ++
                    "(exact? and apply? are single-shot searches with " ++
                    "nothing to tune)",
                .{},
            );
            continue;
        }
        const spec = specForNameIn(table, param.name) orelse {
            switch (context) {
                .auto => try appendIssue(
                    allocator,
                    &issues,
                    param.name_span,
                    "unknown auto? parameter '{s}' (expected one of: " ++
                        known_param_names ++ ")",
                    .{param.name},
                ),
                .conversion => try appendIssue(
                    allocator,
                    &issues,
                    param.name_span,
                    "unknown conversion? parameter '{s}' (expected one " ++
                        "of: " ++ known_conversion_param_names ++ ")",
                    .{param.name},
                ),
                .exact, .apply => unreachable,
            }
            continue;
        };
        if (param.value < spec.min or param.value > spec.max) {
            try appendIssue(
                allocator,
                &issues,
                param.value_span,
                "'{s}' must be between {d} and {d}",
                .{ spec.name, spec.min, spec.max },
            );
        }
    }
    return try issues.toOwnedSlice(allocator);
}

fn appendIssue(
    allocator: std.mem.Allocator,
    issues: *std.ArrayListUnmanaged(ParamIssue),
    span: Span,
    comptime fmt: []const u8,
    args: anytype,
) !void {
    const message = try std.fmt.allocPrint(allocator, fmt, args);
    errdefer allocator.free(message);
    try issues.append(allocator, .{ .span = span, .message = message });
}
