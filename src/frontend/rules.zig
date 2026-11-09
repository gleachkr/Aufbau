const std = @import("std");
const Expr = @import("../trusted/expressions.zig").Expr;
const ExprId = @import("./expr.zig").ExprId;
const ArgInfo = @import("../trusted/parse.zig").ArgInfo;

pub const TemplateExpr = union(enum) {
    binder: usize,
    app: App,

    pub const App = struct {
        term_id: u32,
        args: []const TemplateExpr,
    };

    pub fn fromExpr(
        allocator: std.mem.Allocator,
        expr: *const Expr,
        binders: []const *const Expr,
    ) !TemplateExpr {
        return switch (expr.*) {
            .variable => blk: {
                const idx = binderIndex(binders, expr) orelse {
                    return error.UnknownTemplateVariable;
                };
                break :blk .{ .binder = idx };
            },
            .term => |term| blk: {
                const args = try allocator.alloc(TemplateExpr, term.args.len);
                for (term.args, 0..) |arg, idx| {
                    args[idx] = try fromExpr(allocator, arg, binders);
                }
                break :blk .{ .app = .{
                    .term_id = term.id,
                    .args = args,
                } };
            },
            .hole => return error.HoleNotAllowedInTemplate,
        };
    }

    pub fn eql(a: TemplateExpr, b: TemplateExpr) bool {
        return switch (a) {
            .binder => |lhs| switch (b) {
                .binder => |rhs| lhs == rhs,
                else => false,
            },
            .app => |lhs| switch (b) {
                .app => |rhs| blk: {
                    if (lhs.term_id != rhs.term_id) break :blk false;
                    if (lhs.args.len != rhs.args.len) break :blk false;
                    for (lhs.args, rhs.args) |l_arg, r_arg| {
                        if (!l_arg.eql(r_arg)) break :blk false;
                    }
                    break :blk true;
                },
                else => false,
            },
        };
    }

    pub fn deinit(
        self: *const TemplateExpr,
        allocator: std.mem.Allocator,
    ) void {
        switch (self.*) {
            .binder => {},
            .app => |app| {
                for (app.args) |*arg| arg.deinit(allocator);
                allocator.free(app.args);
            },
        }
    }
};

/// Bitset of binder indices a template references, plus an overflow flag for
/// any index >= 64. Used by the `@auto eager` annotation validation
/// (`rewrite_registry.zig`).
pub const TemplateBinderMask = struct { mask: u64 = 0, overflow: bool = false };

pub fn templateBinderMask(template: TemplateExpr) TemplateBinderMask {
    var result = TemplateBinderMask{};
    collectTemplateBinderMask(template, &result);
    return result;
}

fn collectTemplateBinderMask(
    template: TemplateExpr,
    out: *TemplateBinderMask,
) void {
    switch (template) {
        .binder => |idx| {
            if (idx >= 64) {
                out.overflow = true;
            } else {
                out.mask |= @as(u64, 1) << @intCast(idx);
            }
        },
        .app => |app| {
            for (app.args) |arg| collectTemplateBinderMask(arg, out);
        },
    }
}

/// True when `template` references binder `idx` (no index cap, unlike
/// `templateBinderMask`).
pub fn templateMentionsBinder(template: TemplateExpr, idx: usize) bool {
    return switch (template) {
        .binder => |b| b == idx,
        .app => |app| {
            for (app.args) |arg| {
                if (templateMentionsBinder(arg, idx)) return true;
            }
            return false;
        },
    };
}

/// True when `template` references a binder that `bindings` leaves unbound.
/// Indices past `bindings` count as bound.
pub fn templateHasUnboundBinder(
    template: TemplateExpr,
    bindings: []const ?ExprId,
) bool {
    return switch (template) {
        .binder => |idx| idx < bindings.len and bindings[idx] == null,
        .app => |app| {
            for (app.args) |arg| {
                if (templateHasUnboundBinder(arg, bindings)) return true;
            }
            return false;
        },
    };
}

/// True when some hypothesis references a binder the conclusion does not.
/// This is a purely SYNTACTIC fact about the rule. The name is neutral on
/// purpose: `ex_intro`'s witness is a premise-only binder, but so are
/// `ax_mp`'s cut formula and `or_elim`'s eliminated disjunction. Used by
/// `@auto eager` validation (`rewrite_registry.zig`, rejects such rules).
/// Overflowed masks (>= 64 binders) conservatively report false (the
/// conclusion-determined side).
///
/// A premise-only eigenvariable (`isEigenvariable`) does not count: the
/// application opens it as a variable meta rather than committing to a value,
/// and the instance stays derivable from the conclusion for every legal one.
pub fn hasPremiseOnlyBinder(
    args: []const ArgInfo,
    concl: TemplateExpr,
    hyps: []const TemplateExpr,
) bool {
    const concl_mask = templateBinderMask(concl);
    if (concl_mask.overflow) return false;
    var hyps_mask: u64 = 0;
    for (hyps) |hyp| {
        const m = templateBinderMask(hyp);
        if (m.overflow) return false;
        hyps_mask |= m.mask;
    }
    return !allEigenvariables(args, hyps_mask & ~concl_mask.mask);
}

/// True when every binder in `mask` is an eigenvariable of the rule.
pub fn allEigenvariables(args: []const ArgInfo, mask: u64) bool {
    var rest = mask;
    while (rest != 0) {
        const idx: u6 = @intCast(@ctz(rest));
        rest &= rest - 1;
        if (idx >= args.len or !isEigenvariable(args, idx)) return false;
    }
    return true;
}

/// True when binder `idx` is a bound variable no non-bound binder is declared
/// to depend on. MM0's dependency condition then keeps every value of it out
/// of every other argument (bound occurrences included), so it is fresh for
/// the whole instance.
pub fn isEigenvariable(args: []const ArgInfo, idx: usize) bool {
    if (!args[idx].bound) return false;
    const bit = args[idx].deps;
    for (args, 0..) |arg, other| {
        if (other == idx or arg.bound) continue;
        if (arg.deps & bit != 0) return false;
    }
    return true;
}

fn binderIndex(
    binders: []const *const Expr,
    needle: *const Expr,
) ?usize {
    for (binders, 0..) |binder, idx| {
        if (binder == needle) return idx;
    }
    return null;
}
