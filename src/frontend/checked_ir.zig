const std = @import("std");
const ExprId = @import("./expr.zig").ExprId;
const PlaceholderId = @import("./expr.zig").PlaceholderId;
const TheoremContext = @import("./expr.zig").TheoremContext;
const GlobalEnv = @import("./env.zig").GlobalEnv;
const BindingValidation = @import("./binding_validation.zig");
const ArgInfo = @import("./parse_recovery.zig").ArgInfo;
const CompilerDiag = @import("./diag.zig");

pub const CheckedRef = union(enum) {
    hyp: usize,
    line: usize,
};

pub const CheckedLine = struct {
    expr: ExprId,
    data: union(enum) {
        rule: RuleLine,
        transport: TransportLine,
        /// `by sorry!`: the goal is admitted without a rule. Emission puts a
        /// `Sorry` opcode at this line, so the verifier still checks every
        /// other step and reports the statement as sorry'd.
        sorry,
    },

    pub const RuleLine = struct {
        rule_id: u32,
        bindings: []const ExprId,
        refs: []const CheckedRef,
    };

    pub const TransportLine = struct {
        source: CheckedRef,
        source_expr: ExprId,
    };
};

pub const DepViolation = struct {
    line_idx: usize,
    rule_id: u32,
    detail: CompilerDiag.DepViolationDiagnosticDetail,
};

/// Kind-aware leakage error set. Both variants fire at the same chokepoints
/// and both mean "an unresolved frontend leaf reached checked IR / emission";
/// the split is purely for debuggability (META.md Stage 2): a genuine
/// placeholder leak and an unsolved search metavariable have different causes
/// and different fixes.
pub const LeakageError = error{ PlaceholderLeakage, UnsolvedMetaLeakage };

/// The single classification point used by every leakage guard arm (here and
/// in `emit.zig`).
pub fn leakageError(
    theorem: *const TheoremContext,
    placeholder_id: PlaceholderId,
) LeakageError {
    return switch (theorem.placeholderClass(placeholder_id)) {
        .standard => error.PlaceholderLeakage,
        .meta => error.UnsolvedMetaLeakage,
    };
}

pub fn validateNoPlaceholderExpr(
    theorem: *const TheoremContext,
    expr: ExprId,
) LeakageError!void {
    var first: ?PlaceholderId = null;
    if (theorem.exprAny(expr, &first, firstPlaceholderPred)) {
        return leakageError(theorem, first.?);
    }
}

fn firstPlaceholderPred(
    first: *?PlaceholderId,
    theorem: *const TheoremContext,
    expr: ExprId,
) bool {
    switch (theorem.interner.node(expr).*) {
        .placeholder => |id| {
            first.* = id;
            return true;
        },
        .variable, .app => return false,
    }
}

pub fn validateNoPlaceholderSlice(
    theorem: *const TheoremContext,
    exprs: []const ExprId,
) LeakageError!void {
    for (exprs) |expr| {
        try validateNoPlaceholderExpr(theorem, expr);
    }
}

/// Memoized twin of `validateNoPlaceholderExpr` for the hot per-candidate
/// validation path. The plain walker re-walks hash-consed shared subtrees
/// once per occurrence — and `validateLine` visits every rule binding twice
/// by construction (each binding is a subtree of the line expr). The memo
/// (`TheoremContext.placeholder_scan_cache`) stores the first placeholder id
/// found under a node in pre-order, so the error raised (and its
/// standard/meta classification) is identical to the plain walk's.
pub fn validateNoPlaceholderExprCached(
    theorem: *TheoremContext,
    expr: ExprId,
) LeakageError!void {
    if (theorem.firstPlaceholder(expr)) |id| {
        return leakageError(theorem, id);
    }
}

pub fn validateLine(
    theorem: *const TheoremContext,
    line: CheckedLine,
) LeakageError!void {
    try validateNoPlaceholderExpr(theorem, line.expr);
    switch (line.data) {
        .rule => |rule| try validateNoPlaceholderSlice(
            theorem,
            rule.bindings,
        ),
        .transport => |transport| try validateNoPlaceholderExpr(
            theorem,
            transport.source_expr,
        ),
        .sorry => {},
    }
}

pub fn validateLines(
    theorem: *const TheoremContext,
    lines: []const CheckedLine,
) LeakageError!void {
    for (lines) |line| {
        try validateLine(theorem, line);
    }
}

/// Memoized twin of `validateLines` (see `validateNoPlaceholderExprCached`).
pub fn validateLinesCached(
    theorem: *TheoremContext,
    lines: []const CheckedLine,
) LeakageError!void {
    for (lines) |line| {
        try validateNoPlaceholderExprCached(theorem, line.expr);
        switch (line.data) {
            .rule => |rule| for (rule.bindings) |binding| {
                try validateNoPlaceholderExprCached(theorem, binding);
            },
            .transport => |transport| try validateNoPlaceholderExprCached(
                theorem,
                transport.source_expr,
            ),
            .sorry => {},
        }
    }
}

/// Deps come from `BindingValidation.currentExprInfoCached`, which memoizes
/// per app node on `theorem`, hence the mutable pointer.
pub fn firstDepViolation(
    env: *const GlobalEnv,
    theorem: *TheoremContext,
    lines: []const CheckedLine,
) !?DepViolation {
    var scratch = BindingValidation.infoScratch(theorem.allocator);
    const allocator = scratch.get();
    for (lines, 0..) |line, line_idx| {
        const rule = switch (line.data) {
            .rule => |rule| rule,
            .transport, .sorry => continue,
        };
        if (rule.rule_id >= env.rules.items.len) return error.UnknownRule;

        const rule_decl = &env.rules.items[rule.rule_id];
        const infos = try allocator.alloc(
            BindingValidation.ExprInfo,
            rule.bindings.len,
        );
        defer allocator.free(infos);
        for (rule.bindings, infos) |binding, *info| {
            info.* = try BindingValidation.exprInfo(
                env,
                theorem,
                binding,
            );
        }
        const violation = BindingValidation.firstDepViolation(
            rule_decl.args,
            infos,
        ) orelse continue;
        return .{
            .line_idx = line_idx,
            .rule_id = rule.rule_id,
            .detail = depViolationDetail(
                rule_decl.args,
                rule_decl.arg_names,
                violation.first_idx,
                infos[violation.first_idx],
                violation.second_idx,
                infos[violation.second_idx],
            ),
        };
    }
    return null;
}

fn depViolationDetail(
    rule_args: []const ArgInfo,
    rule_arg_names: []const ?[]const u8,
    first_idx: usize,
    first_info: BindingValidation.ExprInfo,
    second_idx: usize,
    second_info: BindingValidation.ExprInfo,
) CompilerDiag.DepViolationDiagnosticDetail {
    return .{
        .first_arg_idx = first_idx,
        .second_arg_idx = second_idx,
        .first_arg_name = if (first_idx < rule_arg_names.len)
            rule_arg_names[first_idx]
        else
            null,
        .second_arg_name = if (second_idx < rule_arg_names.len)
            rule_arg_names[second_idx]
        else
            null,
        .first_deps = first_info.deps,
        .second_deps = second_info.deps,
        .first_bound = first_info.bound,
        .second_bound = second_info.bound,
        .first_rule_bound = first_idx < rule_args.len and
            rule_args[first_idx].bound,
        .second_rule_bound = second_idx < rule_args.len and
            rule_args[second_idx].bound,
    };
}

pub fn appendRuleLine(
    lines: *std.ArrayListUnmanaged(CheckedLine),
    allocator: std.mem.Allocator,
    expr: ExprId,
    rule_id: u32,
    bindings: []const ExprId,
    refs: []const CheckedRef,
) !usize {
    const idx = lines.items.len;
    try lines.append(allocator, .{
        .expr = expr,
        .data = .{ .rule = .{
            .rule_id = rule_id,
            .bindings = bindings,
            .refs = refs,
        } },
    });
    return idx;
}

pub fn appendTransportLine(
    lines: *std.ArrayListUnmanaged(CheckedLine),
    allocator: std.mem.Allocator,
    expr: ExprId,
    source_expr: ExprId,
    source: CheckedRef,
) !usize {
    const idx = lines.items.len;
    try lines.append(allocator, .{
        .expr = expr,
        .data = .{ .transport = .{
            .source = source,
            .source_expr = source_expr,
        } },
    });
    return idx;
}

pub fn appendSorryLine(
    lines: *std.ArrayListUnmanaged(CheckedLine),
    allocator: std.mem.Allocator,
    expr: ExprId,
) !usize {
    const idx = lines.items.len;
    try lines.append(allocator, .{ .expr = expr, .data = .sorry });
    return idx;
}

pub fn deinitLine(
    allocator: std.mem.Allocator,
    line: CheckedLine,
) void {
    switch (line.data) {
        .rule => |rule| {
            allocator.free(rule.bindings);
            allocator.free(rule.refs);
        },
        .transport, .sorry => {},
    }
}

pub fn deinitLines(
    allocator: std.mem.Allocator,
    lines: []const CheckedLine,
) void {
    for (lines) |line| {
        deinitLine(allocator, line);
    }
}

pub fn rollbackToMark(
    allocator: std.mem.Allocator,
    lines: *std.ArrayListUnmanaged(CheckedLine),
    mark: usize,
) void {
    deinitLines(allocator, lines.items[mark..]);
    lines.shrinkRetainingCapacity(mark);
}

test "validateLines rejects placeholder bindings" {
    var theorem = TheoremContext.init(std.testing.allocator);
    defer theorem.deinit();
    try theorem.seedBinderCount(1);

    const placeholder = try theorem.addPlaceholderResolved("obj");
    const bindings = [_]ExprId{placeholder};
    const lines = [_]CheckedLine{.{
        .expr = theorem.theorem_vars.items[0],
        .data = .{ .rule = .{
            .rule_id = 0,
            .bindings = &bindings,
            .refs = &.{},
        } },
    }};

    try std.testing.expectError(
        error.PlaceholderLeakage,
        validateLines(&theorem, &lines),
    );
}

test "leakage guard distinguishes unsolved metas from placeholders" {
    var theorem = TheoremContext.init(std.testing.allocator);
    defer theorem.deinit();

    const standard = try theorem.addPlaceholderResolved("obj");
    const meta = try theorem.addMetaPlaceholderResolved("obj");

    try std.testing.expectError(
        error.PlaceholderLeakage,
        validateNoPlaceholderExpr(&theorem, standard),
    );
    try std.testing.expectError(
        error.UnsolvedMetaLeakage,
        validateNoPlaceholderExpr(&theorem, meta),
    );
}

test "validateLines rejects unsolved meta bindings" {
    var theorem = TheoremContext.init(std.testing.allocator);
    defer theorem.deinit();
    try theorem.seedBinderCount(1);

    const meta = try theorem.addMetaPlaceholderResolved("obj");
    const bindings = [_]ExprId{meta};
    const lines = [_]CheckedLine{.{
        .expr = theorem.theorem_vars.items[0],
        .data = .{ .rule = .{
            .rule_id = 0,
            .bindings = &bindings,
            .refs = &.{},
        } },
    }};

    try std.testing.expectError(
        error.UnsolvedMetaLeakage,
        validateLines(&theorem, &lines),
    );
}

test "validateLine rejects placeholder transports" {
    var theorem = TheoremContext.init(std.testing.allocator);
    defer theorem.deinit();
    try theorem.seedBinderCount(1);

    const placeholder = try theorem.addPlaceholderResolved("obj");
    const line: CheckedLine = .{
        .expr = theorem.theorem_vars.items[0],
        .data = .{ .transport = .{
            .source = .{ .hyp = 0 },
            .source_expr = placeholder,
        } },
    };

    try std.testing.expectError(
        error.PlaceholderLeakage,
        validateLine(&theorem, line),
    );
}
