const std = @import("std");
const ExprId = @import("../../expr.zig").ExprId;
const TheoremContext = @import("../../expr.zig").TheoremContext;
const GlobalEnv = @import("../../env.zig").GlobalEnv;
const RuleDecl = @import("../../env.zig").RuleDecl;
const ParseRecovery = @import("../../parse_recovery.zig");
const ArgInfo = ParseRecovery.ArgInfo;
const AssertionStmt = ParseRecovery.AssertionStmt;
const BindingValidation = @import("../../binding_validation.zig");
const ViewTrace = @import("../../view_trace.zig");
const text_util = @import("../../text_util.zig");
const CompilerDiag = @import("../diag.zig");
const CompilerContext = @import("../context.zig").CompilerContext;
const DebugConfig = @import("../../debug.zig").DebugConfig;
const DebugTrace = @import("../../debug.zig");

const ExprInfo = BindingValidation.ExprInfo;
pub const DepViolationDetail = CompilerDiag.DepViolationDiagnosticDetail;

pub fn validateResolvedBindingsWithDebug(
    self: *CompilerContext,
    debug: DebugConfig,
    env: *const GlobalEnv,
    theorem: *const TheoremContext,
    parser: ?*const ParseRecovery.MM0Parser,
    theorem_vars: ?*const NameExprMap,
    assertion: AssertionStmt,
    line: anytype,
    rule: *const RuleDecl,
    bindings: []const ExprId,
) !void {
    for (bindings, 0..) |binding, idx| {
        validateBindingExpr(
            env,
            theorem,
            assertion.args,
            rule.args[idx],
            binding,
        ) catch |err| {
            var diag = CompilerDiag.withPhase(.{
                .kind = .generic,
                .err = err,
                .theorem_name = assertion.name,
                .line_label = line.label,
                .rule_name = line.application.rule_name,
                .name = rule.arg_names[idx],
                .span = CompilerDiag.proofBindingDiagnosticSpan(line, rule.arg_names[idx]),
            }, .inference);
            var note_bufs: BindingValidationNoteBufs = .{};
            attachBindingValidationNotes(
                &diag,
                &note_bufs,
                env,
                theorem,
                parser,
                theorem_vars,
                assertion.args,
                rule.args[idx],
                binding,
                err,
            );
            self.setProof(diag);
            return err;
        };
    }
    if (try firstDepViolation(
        env,
        theorem,
        assertion.args,
        rule.args,
        rule.arg_names,
        bindings,
    )) |found_detail| {
        var detail = found_detail;
        var text_bufs: DepViolationTextBufs = .{};
        attachDepViolationBindingTexts(
            &text_bufs,
            env,
            theorem,
            parser,
            theorem_vars,
            &detail,
            bindings[detail.first_arg_idx],
            bindings[detail.second_arg_idx],
        );
        DebugTrace.traceDependency(
            debug,
            "rule {s} on line {s} violates dependency constraints",
            .{ rule.name, line.label },
        );
        if (detail.first_arg_name) |first_name| {
            DebugTrace.traceDependency(
                debug,
                "  conflicting binders: {s} and {s}",
                .{
                    first_name,
                    detail.second_arg_name orelse "_",
                },
            );
        }
        DebugTrace.traceDependency(
            debug,
            "  deps: first=0x{x} second=0x{x}",
            .{ detail.first_deps, detail.second_deps },
        );
        self.setProof(CompilerDiag.withPhase(.{
            .kind = .generic,
            .err = error.DepViolation,
            .theorem_name = assertion.name,
            .line_label = line.label,
            .rule_name = line.application.rule_name,
            .span = line.ruleApplicationSpan(),
            .detail = .{ .dep_violation = detail },
        }, .theorem_application));
        return error.DepViolation;
    }
}

pub fn validateResolvedBindings(
    self: *CompilerContext,
    env: *const GlobalEnv,
    theorem: *const TheoremContext,
    parser: ?*const ParseRecovery.MM0Parser,
    theorem_vars: ?*const NameExprMap,
    assertion: AssertionStmt,
    line: anytype,
    rule: *const RuleDecl,
    bindings: []const ExprId,
) !void {
    return validateResolvedBindingsWithDebug(
        self,
        .none,
        env,
        theorem,
        parser,
        theorem_vars,
        assertion,
        line,
        rule,
        bindings,
    );
}

pub fn bindingsRespectRuleDeps(
    env: *const GlobalEnv,
    theorem: *const TheoremContext,
    theorem_args: []const ArgInfo,
    rule_args: []const ArgInfo,
    rule_arg_names: []const ?[]const u8,
    bindings: []const ExprId,
) !bool {
    return (try firstDepViolation(
        env,
        theorem,
        theorem_args,
        rule_args,
        rule_arg_names,
        bindings,
    )) == null;
}

pub fn firstDepViolation(
    env: *const GlobalEnv,
    theorem: *const TheoremContext,
    theorem_args: []const ArgInfo,
    rule_args: []const ArgInfo,
    rule_arg_names: []const ?[]const u8,
    bindings: []const ExprId,
) !?DepViolationDetail {
    var infos: [56]ExprInfo = undefined;
    std.debug.assert(bindings.len <= infos.len);
    for (bindings, 0..) |binding, idx| {
        infos[idx] = try exprInfo(env, theorem, theorem_args, binding);
    }

    const violation = BindingValidation.firstDepViolation(
        rule_args,
        infos[0..bindings.len],
    ) orelse return null;
    return depViolationDetail(
        rule_args,
        rule_arg_names,
        violation.first_idx,
        infos[violation.first_idx],
        violation.second_idx,
        infos[violation.second_idx],
    );
}

pub fn firstPartialDepViolation(
    env: *const GlobalEnv,
    theorem: *const TheoremContext,
    theorem_args: []const ArgInfo,
    rule_args: []const ArgInfo,
    rule_arg_names: []const ?[]const u8,
    bindings: []const ?ExprId,
) !?DepViolationDetail {
    var bound_deps: [56]u55 = undefined;
    var bound_arg_indices: [56]usize = undefined;
    var bound_len: usize = 0;
    var prev_deps: [56]u55 = undefined;
    var prev_arg_indices: [56]usize = undefined;
    var prev_len: usize = 0;

    for (rule_args, bindings, 0..) |expected, binding, idx| {
        const info = if (binding) |expr_id|
            try exprInfo(env, theorem, theorem_args, expr_id)
        else
            null;

        if (expected.bound) {
            if (info) |actual| {
                for (prev_deps[0..prev_len], prev_arg_indices[0..prev_len]) |
                    prev_dep,
                    prev_idx,
                | {
                    if (prev_dep & actual.deps != 0) {
                        return depViolationDetail(
                            rule_args,
                            rule_arg_names,
                            prev_idx,
                            try exprInfo(
                                env,
                                theorem,
                                theorem_args,
                                bindings[prev_idx].?,
                            ),
                            idx,
                            actual,
                        );
                    }
                }
                bound_deps[bound_len] = actual.deps;
            } else {
                bound_deps[bound_len] = 0;
            }
            bound_arg_indices[bound_len] = idx;
            bound_len += 1;
        } else if (info) |actual| {
            for (bound_deps[0..bound_len], bound_arg_indices[0..bound_len], 0..) |
                bound_dep,
                bound_idx,
                k,
            | {
                if ((@as(u64, expected.deps) >> @intCast(k)) & 1 != 0) {
                    continue;
                }
                if (bound_dep & actual.deps != 0) {
                    return depViolationDetail(
                        rule_args,
                        rule_arg_names,
                        bound_idx,
                        try exprInfo(
                            env,
                            theorem,
                            theorem_args,
                            bindings[bound_idx].?,
                        ),
                        idx,
                        actual,
                    );
                }
            }
        }

        if (info) |actual| {
            prev_deps[prev_len] = actual.deps;
            prev_arg_indices[prev_len] = idx;
            prev_len += 1;
        }
    }
    return null;
}

fn depViolationDetail(
    rule_args: []const ArgInfo,
    rule_arg_names: []const ?[]const u8,
    first_idx: usize,
    first_info: ExprInfo,
    second_idx: usize,
    second_info: ExprInfo,
) DepViolationDetail {
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

pub const NameExprMap = std.StringHashMap(
    *const @import("../../../trusted/expressions.zig").Expr,
);

pub const dep_violation_text_buf_len = 512;

/// Stack scratch for `attachDepViolationBindingTexts`. The caller keeps
/// these alive through `setProof`; the sink stable-copies the slices at
/// set time, so the buffers may die with the caller's frame afterwards.
pub const DepViolationTextBufs = struct {
    first: [dep_violation_text_buf_len]u8 = undefined,
    second: [dep_violation_text_buf_len]u8 = undefined,
};

/// Fill the detail's notation-rendered assignment texts from the two
/// violating binding expressions. Best-effort: rendering failure (or an
/// expression too large for the scratch buffer) leaves the field null,
/// which renderers treat as "omit the assignment line". `parser` +
/// `theorem_vars` enable real binder names and declared notation; without
/// them the render falls back to internal coordinates, so callers should
/// pass both whenever they are in scope.
pub fn attachDepViolationBindingTexts(
    bufs: *DepViolationTextBufs,
    env: *const GlobalEnv,
    theorem: *const TheoremContext,
    parser: ?*const ParseRecovery.MM0Parser,
    theorem_vars: ?*const NameExprMap,
    detail: *DepViolationDetail,
    first_expr: ?ExprId,
    second_expr: ?ExprId,
) void {
    var names = ViewTrace.OptionalDiagNames.build(
        theorem.allocator,
        theorem,
        parser,
        theorem_vars,
    );
    defer names.deinit(theorem.allocator);
    const names_ptr = names.ptr();

    if (first_expr) |expr_id| {
        detail.first_binding_text =
            renderBoundedExpr(&bufs.first, env, theorem, names_ptr, expr_id);
    }
    if (second_expr) |expr_id| {
        detail.second_binding_text =
            renderBoundedExpr(&bufs.second, env, theorem, names_ptr, expr_id);
    }
}

fn renderBoundedExpr(
    buf: []u8,
    env: *const GlobalEnv,
    theorem: *const TheoremContext,
    names_ptr: ?*const ViewTrace.DiagNames,
    expr_id: ExprId,
) ?[]const u8 {
    var fba = std.heap.FixedBufferAllocator.init(buf);
    const text = if (names_ptr) |names|
        ViewTrace.formatExprNamed(
            fba.allocator(),
            theorem,
            env,
            names,
            expr_id,
        ) catch return null
    else
        ViewTrace.formatExpr(
            fba.allocator(),
            theorem,
            env,
            expr_id,
        ) catch return null;
    return text_util.truncateUtf8(text, 64);
}

pub const binding_note_buf_len = 192;

/// Stack scratch for `attachBindingValidationNotes`; same lifetime contract
/// as `DepViolationTextBufs` (alive through setProof, sink copies at set
/// time).
pub const BindingValidationNoteBufs = struct {
    resolved: [binding_note_buf_len]u8 = undefined,
    sorts: [binding_note_buf_len]u8 = undefined,
};

/// Notes for an inferred binding that failed sort/boundness validation:
/// what the binder was resolved to, and which sorts disagree. Both facts
/// are in hand at the failure point; without them the summary alone gives
/// the author nothing to act on. Best-effort — a failed render or an
/// oversized message just omits that note.
pub fn attachBindingValidationNotes(
    diag: *CompilerDiag.Diagnostic,
    bufs: *BindingValidationNoteBufs,
    env: *const GlobalEnv,
    theorem: *const TheoremContext,
    parser: ?*const ParseRecovery.MM0Parser,
    theorem_vars: ?*const NameExprMap,
    theorem_args: []const ArgInfo,
    expected: ArgInfo,
    expr_id: ExprId,
    err: anyerror,
) void {
    var names = ViewTrace.OptionalDiagNames.build(
        theorem.allocator,
        theorem,
        parser,
        theorem_vars,
    );
    defer names.deinit(theorem.allocator);
    const names_ptr = names.ptr();

    var scratch: [dep_violation_text_buf_len]u8 = undefined;
    if (renderBoundedExpr(&scratch, env, theorem, names_ptr, expr_id)) |text| {
        if (std.fmt.bufPrint(
            &bufs.resolved,
            "this binder was resolved to: {s}",
            .{text},
        )) |message| {
            CompilerDiag.addNote(diag, message, .proof, null);
        } else |_| {}
    }

    const info = exprInfo(env, theorem, theorem_args, expr_id) catch return;
    const message: []const u8 = switch (err) {
        error.SortMismatch => std.fmt.bufPrint(
            &bufs.sorts,
            "it has sort '{s}', but the rule expects sort '{s}' here",
            .{ info.sort_name, expected.sort_name },
        ) catch return,
        error.BoundnessMismatch => "the rule requires a single bound " ++
            "variable here",
        else => return,
    };
    CompilerDiag.addNote(diag, message, .proof, null);
}

// Inference only solves equalities. We still need the same sort, boundness,
// and dependency checks that explicit parser-side argument parsing performs.
pub fn validateBindingExpr(
    env: *const GlobalEnv,
    theorem: *const TheoremContext,
    theorem_args: []const ArgInfo,
    expected: ArgInfo,
    expr_id: ExprId,
) !void {
    const info = try exprInfo(env, theorem, theorem_args, expr_id);
    if (!std.mem.eql(u8, info.sort_name, expected.sort_name)) {
        return error.SortMismatch;
    }
    // Match verifier semantics: bound params require bound exprs,
    // but regular params accept any expression (including bound vars).
    if (expected.bound and !info.bound) return error.BoundnessMismatch;
    // Note: dep checking is deferred to the verifier which checks deps
    // relative to the theorem's own bound variables.
}

pub fn exprInfo(
    env: *const GlobalEnv,
    theorem: *const TheoremContext,
    theorem_args: []const ArgInfo,
    expr_id: ExprId,
) !ExprInfo {
    return try BindingValidation.exprInfo(
        env,
        theorem,
        theorem_args,
        expr_id,
    );
}
