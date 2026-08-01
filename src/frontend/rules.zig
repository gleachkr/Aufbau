const std = @import("std");
const Expr = @import("../trusted/expressions.zig").Expr;

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
/// any index >= 64. Shared by the search slot-ordering (`backward/plan.zig`) and
/// the `@auto eager` annotation validation (`rewrite_registry.zig`).
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

/// True when some hypothesis references a binder the conclusion does not.
/// This is a purely SYNTACTIC fact about the rule; whether the search may
/// existentially defer such a binder is a separate policy question
/// (`@auto backward` enrollment / `OpenMode.witness`). The name is neutral
/// on purpose: `ex_intro`'s witness is a premise-only binder, but so are
/// `ax_mp`'s cut formula and `or_elim`'s eliminated disjunction — calling
/// them all "witnesses" invites treating cut formulas as inventable, which
/// is exactly the search explosion the enrollment policy exists to prevent.
/// Shared by `@auto eager` validation (`rewrite_registry.zig`, rejects such
/// rules), the witness-class scheduler (`search/backward/backtrack.zig`,
/// demotes them to class 2), and the witness-pool gate, so they can never
/// drift. Overflowed masks (>= 64 binders) conservatively report false (the
/// conclusion-determined / class-1 side).
pub fn hasPremiseOnlyBinder(
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
    return (hyps_mask & ~concl_mask.mask) != 0;
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
