//! Lockstep descent: which argument pairs a structural walk of a rule
//! template against an expression (or of two expressions) may compare, pin,
//! or descend into. The prunes, seeds and extractors descend through here, so
//! they agree on the rule: the two sides must be applications of the same head
//! at the same arity, and only the arguments that head determines are paired
//! (`semantic.argDetermined`). A pair of any other argument need not be equal
//! even when the applications are (an erasing def, a `@rewrite` head, an ACUI
//! combiner), so reading a binding or a mismatch off it would be a guess.
//! Walks outside this file either descend only rigid heads, which determine
//! every argument (`abstract_prune`'s `matchTemplateStructural` and
//! `abstractDefiniteMismatch`), or build a solution the validator re-checks
//! (`forward.solveCorrespondence*`, `witness.zig`'s read-back and anchor
//! walks, `trigger.matchTriggerPattern`, `split.findSplitSite`), so a guess
//! there is harmless.

const types = @import("../types.zig");
const semantic = @import("./semantic.zig");
const ExprId = @import("../../../expr.zig").ExprId;
const TheoremContext = @import("../../../expr.zig").TheoremContext;
const TemplateExpr = @import("../../../rules.zig").TemplateExpr;
const Context = types.Context;

pub const TemplatePair = struct { template: TemplateExpr, expr: ExprId };
pub const ExprPair = struct { a: ExprId, b: ExprId };

/// The determined argument pairs of `app` against `expr`, or null when `expr`
/// is not an application of the same head at the same arity.
pub fn templateArgs(
    context: *const Context,
    theorem: *const TheoremContext,
    app: TemplateExpr.App,
    expr: ExprId,
) ?Args(TemplateExpr, TemplatePair) {
    const concrete = switch (theorem.interner.node(expr).*) {
        .app => |concrete| concrete,
        else => return null,
    };
    if (concrete.term_id != app.term_id or concrete.args.len != app.args.len) return null;
    return .init(context, app.term_id, app.args, concrete.args);
}

/// The determined argument pairs of two expressions, or null unless both are
/// applications of the same head at the same arity.
pub fn exprArgs(
    context: *const Context,
    theorem: *const TheoremContext,
    a: ExprId,
    b: ExprId,
) ?Args(ExprId, ExprPair) {
    const a_app = switch (theorem.interner.node(a).*) {
        .app => |app| app,
        else => return null,
    };
    const b_app = switch (theorem.interner.node(b).*) {
        .app => |app| app,
        else => return null,
    };
    if (a_app.term_id != b_app.term_id or a_app.args.len != b_app.args.len) return null;
    return .init(context, a_app.term_id, a_app.args, b_app.args);
}

/// Iterator over the determined argument pairs. The expression argument
/// slices are separate heap allocations of the interner, so interning during
/// the walk does not invalidate them.
pub fn Args(comptime Left: type, comptime Pair: type) type {
    return struct {
        context: *const Context,
        head: u32,
        left: []const Left,
        right: []const ExprId,
        index: usize = 0,
        /// A rigid head determines every arg; only a def asks per arg.
        per_arg: bool,

        fn init(
            context: *const Context,
            head: u32,
            left: []const Left,
            right: []const ExprId,
        ) @This() {
            const class = semantic.headClass(context, head);
            return .{
                .context = context,
                .head = head,
                // An ACUI, `@rewrite`, or unavailable head determines no arg.
                .left = if (class == .rigid or class == .def) left else &.{},
                .right = right,
                .per_arg = class == .def,
            };
        }

        pub fn next(self: *@This()) ?Pair {
            while (self.index < self.left.len) {
                const i = self.index;
                self.index += 1;
                if (self.per_arg and !semantic.argDetermined(self.context, self.head, i)) continue;
                return if (Pair == TemplatePair)
                    .{ .template = self.left[i], .expr = self.right[i] }
                else
                    .{ .a = self.left[i], .b = self.right[i] };
            }
            return null;
        }
    };
}

/// How a `walk` ended.
pub const WalkEnd = enum {
    /// The visitor ended the walk.
    stopped,
    /// Every node was reached.
    done,
    /// A head or arity mismatch, which a def could bridge, cut part of the
    /// template off; the rest was still walked.
    partial,
};

/// Walk `template` against `expr` through the arguments each head determines,
/// handing each binder to `visitor.binder(idx, expr)` and each combiner node to
/// `visitor.combiner(app, expr)`, whose members a positional walk cannot pair.
/// Either returns true to end the walk.
pub fn walk(
    context: *const Context,
    theorem: *const TheoremContext,
    template: TemplateExpr,
    expr: ExprId,
    visitor: anytype,
) WalkEnd {
    var partial = false;
    if (walkNode(context, theorem, template, expr, visitor, &partial)) return .stopped;
    return if (partial) .partial else .done;
}

fn walkNode(
    context: *const Context,
    theorem: *const TheoremContext,
    template: TemplateExpr,
    expr: ExprId,
    visitor: anytype,
    partial: *bool,
) bool {
    switch (template) {
        .binder => |idx| return visitor.binder(idx, expr),
        .app => |app| {
            if (context.registry.hasStructuralCombiner(app.term_id)) return visitor.combiner(app, expr);
            var args = templateArgs(context, theorem, app, expr) orelse {
                partial.* = true;
                return false;
            };
            while (args.next()) |pair| {
                if (walkNode(context, theorem, pair.template, pair.expr, visitor, partial)) return true;
            }
            return false;
        },
    }
}
