//! How matching treats a term head: whether it can change under conversion,
//! and which of its arguments equality of two applications forces. Shared by
//! the search prunes (which may only pin or compare forced arguments) and the
//! transparent comparator (which retries a same-head def mismatch by unfolding
//! only when the mismatching argument is not forced). `Screen` lifts this to
//! interned terms: which two can never meet, and how many members of an
//! `@acui` bag a term stands for.

const std = @import("std");
const GlobalEnv = @import("./env.zig").GlobalEnv;
const RewriteRegistry = @import("./rewrite_registry.zig").RewriteRegistry;
const TemplateExpr = @import("./rules.zig").TemplateExpr;
const ExprId = @import("./expr.zig").ExprId;
const ExprNode = @import("./expr.zig").ExprNode;
const TheoremContext = @import("./expr.zig").TheoremContext;
const AcuiBag = @import("./acui_bag.zig");

pub const HeadClass = enum {
    /// A primitive term, or a def without a body (nothing can unfold it):
    /// no conversion changes it, so two applications are equal only when
    /// their arguments are.
    rigid,
    /// A transparent def: it unfolds to its body.
    def,
    /// An `@acui` combiner: rearrangement can reorder, regroup, or (through
    /// the unit and idempotence) drop its arguments.
    acui,
    /// A `@rewrite` head (e.g. a substitution `sb_ty`): it can reduce to a
    /// different head, even when it is also a def or an ACUI combiner.
    rewrite,
    /// A term recovery discarded, or an id outside the environment.
    unavailable,
};

/// The class of `head`. Without a registry no head is ACUI or `@rewrite`.
pub fn classify(
    env: *const GlobalEnv,
    registry: ?*const RewriteRegistry,
    head: u32,
) HeadClass {
    if (!env.hasAvailableTerm(head)) return .unavailable;
    if (registry) |reg| {
        if (reg.rewrites_by_head.contains(head)) return .rewrite;
        if (reg.acui_by_head.contains(head)) return .acui;
    }
    const term = env.terms.items[head];
    return if (term.is_def and term.body != null) .def else .rigid;
}

/// Bound on nested def unfolding; def bodies only reference earlier terms, so
/// this is a defensive cap, not a semantic limit.
const max_depth = 64;

/// The head an application of `head` shows once def heads are unfolded, when
/// that head is rigid. No conversion changes a rigid head, so two terms whose
/// rigid heads differ are never equal. Null when unfolding reaches a binder,
/// or a head that conversion can change.
pub fn rigidHead(
    env: *const GlobalEnv,
    registry: ?*const RewriteRegistry,
    head: u32,
) ?u32 {
    var current = head;
    for (0..max_depth) |_| {
        switch (classify(env, registry, current)) {
            .rigid => return current,
            .def => switch (env.terms.items[current].body.?) {
                .binder => return null,
                .app => |app| current = app.term_id,
            },
            .acui, .rewrite, .unavailable => return null,
        }
    }
    return null;
}

/// Whether applications of `lhs` and `rhs` show different rigid heads,
/// which no conversion reconciles. False when either has none.
pub fn rigidHeadsDiffer(
    env: *const GlobalEnv,
    registry: ?*const RewriteRegistry,
    lhs: u32,
    rhs: u32,
) bool {
    const lhs_head = rigidHead(env, registry, lhs) orelse return false;
    const rhs_head = rigidHead(env, registry, rhs) orelse return false;
    return lhs_head != rhs_head;
}

/// Does `h(a) ≡ h(b)` force `a[arg_idx] ≡ b[arg_idx]`? True for a rigid head,
/// and for a transparent def whose body places that parameter at a path of
/// such heads (possibly through nested defs, each checked the same way).
/// False for ACUI / `@rewrite` / unavailable heads, and for a def arg the body
/// drops or only places under a non-determining head (the `const` trap:
/// `const(X, Y) := X` has `const(X, t) ≡ const(X, t')` with `t ≠ t'`).
/// Binder-introducing defs are fine here: their dummies are fresh on both
/// sides and cannot occur in a real argument.
pub fn argDetermined(
    env: *const GlobalEnv,
    registry: ?*const RewriteRegistry,
    head: u32,
    arg_idx: usize,
) bool {
    return argDeterminedAt(env, registry, head, arg_idx, 0);
}

fn argDeterminedAt(
    env: *const GlobalEnv,
    registry: ?*const RewriteRegistry,
    head: u32,
    arg_idx: usize,
    depth: usize,
) bool {
    if (depth >= max_depth) return false;
    switch (classify(env, registry, head)) {
        .acui, .rewrite, .unavailable => return false,
        .rigid => return true,
        .def => {
            const term = env.terms.items[head];
            if (arg_idx >= term.args.len) return false;
            return paramAtDeterminedPath(env, registry, term.body.?, arg_idx, depth + 1);
        },
    }
}

fn paramAtDeterminedPath(
    env: *const GlobalEnv,
    registry: ?*const RewriteRegistry,
    template: TemplateExpr,
    param: usize,
    depth: usize,
) bool {
    switch (template) {
        .binder => |idx| return idx == param,
        .app => |app| {
            for (app.args, 0..) |arg, i| {
                if (paramAtDeterminedPath(env, registry, arg, param, depth) and
                    argDeterminedAt(env, registry, app.term_id, i, depth)) return true;
            }
            return false;
        },
    }
}

/// One query of the expression-level screen over interned terms: whether two
/// terms can never be made equal (`neverMeet`), and how many members of an
/// `@acui` bag a term stands for under every conversion. Def unfolding, ACUI
/// rearrangement and `@rewrite` reduction never change a rigid head, and an
/// `@acui` application keeps its combiner head while it holds two members it
/// cannot lose. The answers for each term are memoized for the query, so a
/// term shared down a chain (`dbl a := a + a`, nested lattice joins) costs
/// once.
pub const Screen = struct {
    env: *const GlobalEnv,
    registry: *const RewriteRegistry,
    theorem: *const TheoremContext,
    /// A `@recover` hole in the second term of `neverMeet`: what sits there
    /// is still to be filled in, so it meets anything, and as a bag member it
    /// may stand for none or for several.
    hole: ?ExprId = null,
    allocator: std.mem.Allocator,
    /// `stableHead` (keyed with `no_combiner`) and `minMembers` answers. An
    /// allocation failure only skips a memo entry.
    memo: std.AutoHashMapUnmanaged(MemoKey, u64) = .empty,
    depth: usize = 0,

    const MemoKey = struct { expr: ExprId, combiner: u32 };
    const no_combiner = std.math.maxInt(u32);
    const no_head = std.math.maxInt(u64);

    pub fn init(
        env: *const GlobalEnv,
        registry: *const RewriteRegistry,
        theorem: *const TheoremContext,
        allocator: std.mem.Allocator,
    ) Screen {
        return .{ .env = env, .registry = registry, .theorem = theorem, .allocator = allocator };
    }

    pub fn deinit(self: *Screen) void {
        self.memo.deinit(self.allocator);
    }

    /// Whether `a` and `b` can never be made equal: two distinct variables, a
    /// variable against an application with a stable head, applications with
    /// distinct stable heads, or a mismatch in an argument their shared head
    /// determines. A placeholder, a `@rewrite` head, and the hole or a
    /// coercion chain around it hold no opinion.
    pub fn neverMeet(self: *Screen, a: ExprId, b: ExprId) bool {
        if (a == b) return false;
        if (self.hole) |hole| {
            if (b == hole or self.coercedHole(b, hole)) return false;
        }
        const na = self.theorem.interner.node(a);
        const nb = self.theorem.interner.node(b);
        for ([_]*const ExprNode{ na, nb }) |n| switch (n.*) {
            .app => |app| if (self.classOf(app.term_id) == .rewrite) return false,
            else => {},
        };
        switch (na.*) {
            .placeholder => return false,
            // Distinct interned variables are distinct: a theorem variable's
            // id is stable, and a dummy's comes from a monotonic counter.
            .variable => return switch (nb.*) {
                .variable => true,
                .app => self.stableHead(b) != null,
                .placeholder => false,
            },
            .app => |a_app| switch (nb.*) {
                .placeholder => return false,
                .variable => return self.stableHead(a) != null,
                .app => |b_app| {
                    if (a_app.term_id == b_app.term_id and a_app.args.len == b_app.args.len) {
                        for (a_app.args, b_app.args, 0..) |x, y, i| {
                            if (!argDetermined(self.env, self.registry, a_app.term_id, i)) continue;
                            if (self.neverMeet(x, y)) return true;
                        }
                        return false;
                    }
                    const a_head = self.stableHead(a) orelse return false;
                    const b_head = self.stableHead(b) orelse return false;
                    return a_head != b_head;
                },
            },
        }
    }

    /// The head every conversion leaves on the application `expr`: its rigid
    /// head, or an `@acui` combiner that keeps two members it cannot lose,
    /// directly or through a def whose body is such an application.
    pub fn stableHead(self: *Screen, expr: ExprId) ?u32 {
        const app = switch (self.theorem.interner.node(expr).*) {
            .app => |app| app,
            else => return null,
        };
        if (rigidHead(self.env, self.registry, app.term_id)) |head| return head;
        const key = MemoKey{ .expr = expr, .combiner = no_combiner };
        if (self.memo.get(key)) |head| return if (head == no_head) null else @intCast(head);
        if (self.depth >= max_depth) return null;
        self.depth += 1;
        const head = self.keptCombinerHead(expr, app.term_id);
        self.depth -= 1;
        self.memo.put(self.allocator, key, head orelse no_head) catch {};
        return head;
    }

    fn keptCombinerHead(self: *Screen, expr: ExprId, term_id: u32) ?u32 {
        // A rigid head has already answered.
        const head = switch (self.classOf(term_id)) {
            .acui => term_id,
            .def => switch (self.env.terms.items[term_id].body.?) {
                .app => |body| body.term_id,
                .binder => return null,
            },
            else => return null,
        };
        const combiner = self.keepingCombiner(head) orelse return null;
        if (!combiner.law.isIdempotent()) {
            return if (self.minMembers(combiner, expr) >= 2) head else null;
        }
        // Idempotence merges equal members, so look for two that definitely
        // differ, any pair of them, so the answer does not depend on member
        // order. A def is not unfolded here.
        if (head != term_id) return null;
        const members = combiner.flatten(self.theorem, expr) orelse return null;
        var fixed: AcuiBag.ExprBag = .{};
        for (members.slice()) |member| {
            if (!self.exactlyOneMember(combiner, member)) continue;
            for (fixed.slice()) |kept| {
                if (self.neverMeet(kept, member)) return head;
            }
            _ = fixed.append(member);
        }
        return null;
    }

    /// The combiner `head`, when its applications keep that head while they
    /// hold two members: an `@acui` combiner whose unit, if any, is rigid (a
    /// def unit may unfold to a member).
    fn keepingCombiner(self: *const Screen, head: u32) ?AcuiBag.Combiner {
        if (self.classOf(head) != .acui) return null;
        const combiner = AcuiBag.Combiner.of(self.registry, self.env, head) orelse return null;
        if (combiner.unit) |unit| if (self.classOf(unit) != .rigid) return null;
        return combiner;
    }

    /// Whether `expr` stays exactly one member of a `combiner` bag under every
    /// conversion: a variable other than the hole, or an application whose
    /// stable head is neither the combiner nor its unit.
    pub fn exactlyOneMember(self: *Screen, combiner: AcuiBag.Combiner, expr: ExprId) bool {
        if (self.hole == expr) return false;
        return switch (self.theorem.interner.node(expr).*) {
            .variable => true,
            .placeholder => false,
            .app => if (self.stableHead(expr)) |head|
                head != combiner.head and head != combiner.unit
            else
                false,
        };
    }

    /// The fewest members of a `combiner` bag that `expr` stands for under
    /// every conversion.
    pub fn minMembers(self: *Screen, combiner: AcuiBag.Combiner, expr: ExprId) u64 {
        if (self.hole == expr) return 0;
        const app = switch (self.theorem.interner.node(expr).*) {
            .variable => return 1,
            .placeholder => return 0,
            .app => |app| app,
        };
        const key = MemoKey{ .expr = expr, .combiner = combiner.head };
        if (self.memo.get(key)) |count| return count;
        if (self.depth >= max_depth) return 0;
        self.depth += 1;
        const count = self.countMembers(combiner, expr, app.term_id, app.args);
        self.depth -= 1;
        self.memo.put(self.allocator, key, count) catch {};
        return count;
    }

    fn countMembers(
        self: *Screen,
        combiner: AcuiBag.Combiner,
        expr: ExprId,
        term_id: u32,
        args: []const ExprId,
    ) u64 {
        if (term_id == combiner.head) {
            const members = combiner.flatten(self.theorem, expr) orelse return 0;
            var count: u64 = 0;
            for (members.slice()) |member| count +|= self.minMembers(combiner, member);
            return count;
        }
        // A def whose body is a `combiner` application stands for the body's
        // members; the body's binders past `args` are its dummies, each a
        // variable.
        if (self.classOf(term_id) == .def) {
            const body = self.env.terms.items[term_id].body.?;
            if (body == .app and body.app.term_id == combiner.head) {
                const members = combiner.flattenTemplate(body) orelse return 0;
                var count: u64 = 0;
                for (members.slice()) |member| switch (member) {
                    .binder => |idx| count +|= if (idx < args.len)
                        self.minMembers(combiner, args[idx])
                    else
                        1,
                    .app => |member_app| if (rigidHead(self.env, self.registry, member_app.term_id)) |head| {
                        if (head != combiner.unit) count +|= 1;
                    },
                };
                return count;
            }
        }
        return @intFromBool(self.exactlyOneMember(combiner, expr));
    }

    // Whether `expr` is `hole` wrapped in nothing but declared coercions.
    fn coercedHole(self: *const Screen, expr: ExprId, hole: ExprId) bool {
        var current = expr;
        while (current != hole) {
            const app = switch (self.theorem.interner.node(current).*) {
                .app => |app| app,
                else => return false,
            };
            if (app.args.len != 1 or !self.env.isCoercionTerm(app.term_id)) return false;
            current = app.args[0];
        }
        return true;
    }

    fn classOf(self: *const Screen, head: u32) HeadClass {
        return classify(self.env, self.registry, head);
    }
};
