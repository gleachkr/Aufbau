//! The one reading of an `@acui` combiner application as a bag of members.
//!
//! `Spine` reads the binary spine of a combiner head as its leaves, left to
//! right, with their duplicates, unbounded. The normalizer, the checker's
//! conversions and inference use it directly. `Combiner.flatten` is the
//! bounded reading the checker's hints and the search use: a bag holds at
//! most `capacity` members, and on overflow `flatten` returns null, so callers
//! abstain rather than read a truncated bag.
//!
//! What the members *mean* depends on the declared laws (`Law`). Callers that
//! compare members as a set dedup explicitly; nothing here dedups on the
//! combiner's behalf.
//!
//! A unit is always *this* combiner's unit. Two combiners on one sort (ring
//! `+` with `0`, `*` with `1`) do not share units: `x + 1` keeps its `1`.
//! Whether the unit is a member is the reader's choice, one of three:
//! - `Combiner.flatten` drops it: a bag's meaning does not include its unit.
//! - `Spine.provable` drops it only when both unit laws can remove it from
//!   either end, so a proof can follow the reading.
//! - `Spine.raw` keeps it, for proof steps that move members but never remove
//!   the unit.

const std = @import("std");
const ExprId = @import("./expr.zig").ExprId;
const TheoremContext = @import("./expr.zig").TheoremContext;
const TemplateExpr = @import("./rules.zig").TemplateExpr;
const GlobalEnv = @import("./env.zig").GlobalEnv;
const RewriteRegistry = @import("./rewrite_registry.zig").RewriteRegistry;
const ResolvedStructuralCombiner =
    @import("./rewrite_registry.zig").ResolvedStructuralCombiner;

/// The binary spine of `head`, read as its leaves left to right. A node that
/// is not a binary `head` application is one leaf, or no leaf when it is
/// `skip_unit`.
pub const Spine = struct {
    head: u32,
    /// The unit leaf to skip, or null to keep every leaf.
    skip_unit: ?u32 = null,

    /// Every leaf, the unit included.
    pub fn raw(head: u32) Spine {
        return .{ .head = head };
    }

    /// The leaves a proof can reach: the unit is dropped only when both unit
    /// laws are available.
    pub fn provable(acui: ResolvedStructuralCombiner) Spine {
        return .{
            .head = acui.head_term_id,
            .skip_unit = if (acui.supportsLeftUnit() and acui.supportsRightUnit())
                acui.unit_term_id
            else
                null,
        };
    }

    /// The two operands of `expr` when it is a `head` application.
    pub fn split(self: Spine, theorem: *const TheoremContext, expr: ExprId) ?[2]ExprId {
        return switch (theorem.interner.node(expr).*) {
            .app => |app| if (app.term_id == self.head and app.args.len == 2)
                .{ app.args[0], app.args[1] }
            else
                null,
            .variable, .placeholder => null,
        };
    }

    pub fn isBag(self: Spine, theorem: *const TheoremContext, expr: ExprId) bool {
        return self.split(theorem, expr) != null;
    }

    /// Whether `expr` is the leaf this reading skips.
    pub fn skips(self: Spine, theorem: *const TheoremContext, expr: ExprId) bool {
        const unit = self.skip_unit orelse return false;
        return switch (theorem.interner.node(expr).*) {
            .app => |app| app.term_id == unit and app.args.len == 0,
            .variable, .placeholder => false,
        };
    }

    /// Calls `visitor.leaf(leaf)` for each leaf of `expr`, left to right.
    pub fn visit(
        self: Spine,
        theorem: *const TheoremContext,
        expr: ExprId,
        visitor: anytype,
    ) void {
        if (self.split(theorem, expr)) |parts| {
            self.visit(theorem, parts[0], visitor);
            self.visit(theorem, parts[1], visitor);
            return;
        }
        if (self.skips(theorem, expr)) return;
        visitor.leaf(expr);
    }

    pub fn count(self: Spine, theorem: *const TheoremContext, expr: ExprId) usize {
        var counter: struct {
            count: usize = 0,
            pub fn leaf(c: *@This(), _: ExprId) void {
                c.count += 1;
            }
        } = .{};
        self.visit(theorem, expr, &counter);
        return counter.count;
    }

    /// Appends the leaves of `expr` to `out`, growing it once.
    pub fn collect(
        self: Spine,
        allocator: std.mem.Allocator,
        theorem: *const TheoremContext,
        expr: ExprId,
        out: *std.ArrayListUnmanaged(ExprId),
    ) !void {
        // Precise: arena callers keep every buffer a growing list leaves.
        try out.ensureTotalCapacityPrecise(allocator, out.items.len + self.count(theorem, expr));
        const Appender = struct {
            out: *std.ArrayListUnmanaged(ExprId),
            pub fn leaf(a: @This(), leaf_id: ExprId) void {
                a.out.appendAssumeCapacity(leaf_id);
            }
        };
        self.visit(theorem, expr, Appender{ .out = out });
    }

    /// Whether `member` is `bag` or a node of its spine.
    pub fn holds(
        self: Spine,
        theorem: *const TheoremContext,
        bag: ExprId,
        member: ExprId,
    ) bool {
        if (bag == member) return true;
        const parts = self.split(theorem, bag) orelse return false;
        return self.holds(theorem, parts[0], member) or
            self.holds(theorem, parts[1], member);
    }

    /// `split` for a rule template.
    pub fn splitTemplate(self: Spine, template: TemplateExpr) ?[2]TemplateExpr {
        return switch (template) {
            .app => |app| if (app.term_id == self.head and app.args.len == 2)
                .{ app.args[0], app.args[1] }
            else
                null,
            .binder => null,
        };
    }

    /// `skips` for a rule template.
    pub fn skipsTemplate(self: Spine, template: TemplateExpr) bool {
        const unit = self.skip_unit orelse return false;
        return switch (template) {
            .app => |app| app.term_id == unit and app.args.len == 0,
            .binder => false,
        };
    }

    /// `visit` for a rule template. Binders are leaves.
    pub fn visitTemplate(self: Spine, template: TemplateExpr, visitor: anytype) void {
        if (self.splitTemplate(template)) |parts| {
            self.visitTemplate(parts[0], visitor);
            self.visitTemplate(parts[1], visitor);
            return;
        }
        if (self.skipsTemplate(template)) return;
        visitor.leaf(template);
    }

    /// `collect` for a rule template.
    pub fn collectTemplate(
        self: Spine,
        allocator: std.mem.Allocator,
        template: TemplateExpr,
        out: *std.ArrayListUnmanaged(TemplateExpr),
    ) !void {
        var counter: struct {
            count: usize = 0,
            pub fn leaf(c: *@This(), _: TemplateExpr) void {
                c.count += 1;
            }
        } = .{};
        self.visitTemplate(template, &counter);
        try out.ensureTotalCapacityPrecise(allocator, out.items.len + counter.count);
        const Appender = struct {
            out: *std.ArrayListUnmanaged(TemplateExpr),
            pub fn leaf(a: @This(), item: TemplateExpr) void {
                a.out.appendAssumeCapacity(item);
            }
        };
        self.visitTemplate(template, Appender{ .out = out });
    }
};

/// Drops adjacent repeats from sorted `members`: the members of an
/// idempotent bag. Returns the kept prefix.
pub fn mergeRepeats(members: []ExprId) []ExprId {
    var len: usize = 0;
    for (members) |member| {
        if (len != 0 and members[len - 1] == member) continue;
        members[len] = member;
        len += 1;
    }
    return members[0..len];
}

pub const capacity = 64;

/// The member semantics a combiner's declared laws give. Associativity and
/// the unit are mandatory in `@acui`; commutativity and idempotence are not.
pub const Law = enum {
    /// Commutative and idempotent: only which members occur counts.
    set,
    /// Commutative, not idempotent: how often each member occurs counts.
    multiset,
    /// Neither: the order and the multiplicity of the members count.
    sequence,
    /// Idempotent, not commutative: order counts, but a member may repeat.
    idempotent_sequence,

    pub fn of(commutative: bool, idempotent: bool) Law {
        if (commutative) return if (idempotent) .set else .multiset;
        return if (idempotent) .idempotent_sequence else .sequence;
    }

    pub fn isCommutative(self: Law) bool {
        return self == .set or self == .multiset;
    }

    pub fn isIdempotent(self: Law) bool {
        return self == .set or self == .idempotent_sequence;
    }
};

/// The law of the `@acui` combiner headed by `head`, or null when `head` is
/// not one.
pub fn lawOf(registry: *const RewriteRegistry, head: u32) ?Law {
    const combiner = registry.acui_by_head.get(head) orelse return null;
    return Law.of(combiner.comm_name != null, combiner.idem_name != null);
}

/// Whether any `@acui` combiner of `registry` has a law satisfying `pred`.
pub fn anyLaw(registry: *const RewriteRegistry, comptime pred: fn (Law) bool) bool {
    var it = registry.acui_by_head.valueIterator();
    while (it.next()) |combiner| {
        if (pred(Law.of(combiner.comm_name != null, combiner.idem_name != null))) return true;
    }
    return false;
}

pub const Combiner = struct {
    head: u32,
    /// Null when the declared unit term does not resolve.
    unit: ?u32,
    law: Law,

    /// The `@acui` combiner headed by `head`, or null when `head` is not one.
    pub fn of(
        registry: *const RewriteRegistry,
        env: *const GlobalEnv,
        head: u32,
    ) ?Combiner {
        const combiner = registry.acui_by_head.get(head) orelse return null;
        return .{
            .head = head,
            .unit = env.term_names.get(combiner.unit_term_name),
            .law = Law.of(combiner.comm_name != null, combiner.idem_name != null),
        };
    }

    pub fn fromResolved(acui: ResolvedStructuralCombiner) Combiner {
        return .{
            .head = acui.head_term_id,
            .unit = acui.unit_term_id,
            .law = Law.of(acui.comm_id != null, acui.idem_id != null),
        };
    }

    /// Whether `expr` is this combiner's unit.
    pub fn isUnit(self: Combiner, theorem: *const TheoremContext, expr: ExprId) bool {
        return self.spine().skips(theorem, expr);
    }

    /// This combiner's spine, without its unit.
    pub fn spine(self: Combiner) Spine {
        return .{ .head = self.head, .skip_unit = self.unit };
    }

    /// The members of `expr`, or null on overflow. An `expr` not headed by
    /// this combiner is a one-member bag, or empty if it is the unit.
    pub fn flatten(
        self: Combiner,
        theorem: *const TheoremContext,
        expr: ExprId,
    ) ?ExprBag {
        var fill: Fill(ExprId) = .{};
        self.spine().visit(theorem, expr, &fill);
        return if (fill.overflow) null else fill.bag;
    }

    /// `flatten` for a rule template. Binders are members.
    pub fn flattenTemplate(self: Combiner, template: TemplateExpr) ?TemplateBag {
        var fill: Fill(TemplateExpr) = .{};
        self.spine().visitTemplate(template, &fill);
        return if (fill.overflow) null else fill.bag;
    }

    fn Fill(comptime T: type) type {
        return struct {
            bag: Members(T) = .{},
            overflow: bool = false,

            pub fn leaf(self: *@This(), item: T) void {
                if (!self.bag.append(item)) self.overflow = true;
            }
        };
    }

    /// Rebuild `members` as one expression: the unit when empty (null if the
    /// unit does not resolve), the member itself when single, else a right
    /// fold.
    pub fn build(
        self: Combiner,
        theorem: *TheoremContext,
        members: []const ExprId,
    ) error{ OutOfMemory, TooManyTheoremExprs }!?ExprId {
        if (members.len == 0) {
            const unit = self.unit orelse return null;
            return try theorem.interner.internApp(unit, &.{});
        }
        return try rightFold(theorem, self.head, members);
    }
};

pub fn Members(comptime T: type) type {
    return struct {
        items: [capacity]T = undefined,
        len: usize = 0,

        pub fn slice(self: *const @This()) []const T {
            return self.items[0..self.len];
        }

        /// False when the bag is full.
        pub fn append(self: *@This(), item: T) bool {
            if (self.len == capacity) return false;
            self.items[self.len] = item;
            self.len += 1;
            return true;
        }

        /// `append` unless `item` is already a member, for a set reading.
        pub fn appendDistinct(self: *@This(), item: T) bool {
            if (std.mem.indexOfScalar(T, self.slice(), item) != null) return true;
            return self.append(item);
        }
    };
}

pub const ExprBag = Members(ExprId);
pub const TemplateBag = Members(TemplateExpr);

/// Right-fold `members` back into binary `head` applications, preserving
/// left-to-right order: `[a, b, c]` → `head(a, head(b, c))`. A single member
/// is returned as itself. The empty bag is the unit, which `Combiner.build`
/// handles.
pub fn rightFold(
    theorem: *TheoremContext,
    head: u32,
    members: []const ExprId,
) error{ OutOfMemory, TooManyTheoremExprs }!ExprId {
    std.debug.assert(members.len > 0);
    var result = members[members.len - 1];
    var i = members.len - 1;
    while (i > 0) {
        i -= 1;
        result = try theorem.interner.internApp(head, &.{ members[i], result });
    }
    return result;
}
