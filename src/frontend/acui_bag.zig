//! One reading of an `@acui` combiner application as a bag of members, shared
//! by the checker and the search.
//!
//! `Combiner.flatten` splices nested applications of the combiner head and
//! drops the combiner's own unit, keeping every other member in left-to-right
//! order with its duplicates. What the members *mean* depends on the declared
//! laws (`Law`). Callers that compare members as a set dedup explicitly;
//! nothing here dedups on the combiner's behalf.
//!
//! A unit is always *this* combiner's unit. Two combiners on one sort (ring
//! `+` with `0`, `*` with `1`) do not share units: `x + 1` keeps its `1`.
//!
//! A bag holds at most `capacity` members. On overflow `flatten` returns null,
//! and callers abstain rather than read a truncated bag.

const std = @import("std");
const ExprId = @import("./expr.zig").ExprId;
const TheoremContext = @import("./expr.zig").TheoremContext;
const TemplateExpr = @import("./rules.zig").TemplateExpr;
const GlobalEnv = @import("./env.zig").GlobalEnv;
const RewriteRegistry = @import("./rewrite_registry.zig").RewriteRegistry;
const ResolvedStructuralCombiner =
    @import("./rewrite_registry.zig").ResolvedStructuralCombiner;

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
        const unit = self.unit orelse return false;
        return switch (theorem.interner.node(expr).*) {
            .app => |app| app.term_id == unit and app.args.len == 0,
            else => false,
        };
    }

    /// The members of `expr`, or null on overflow. An `expr` not headed by
    /// this combiner is a one-member bag, or empty if it is the unit.
    pub fn flatten(
        self: Combiner,
        theorem: *const TheoremContext,
        expr: ExprId,
    ) ?ExprBag {
        var out = ExprBag{};
        if (!self.flattenInto(theorem, expr, &out)) return null;
        return out;
    }

    fn flattenInto(
        self: Combiner,
        theorem: *const TheoremContext,
        expr: ExprId,
        out: *ExprBag,
    ) bool {
        switch (theorem.interner.node(expr).*) {
            .app => |app| {
                if (app.term_id == self.head) {
                    for (app.args) |arg| {
                        if (!self.flattenInto(theorem, arg, out)) return false;
                    }
                    return true;
                }
                if (app.args.len == 0 and app.term_id == self.unit) return true;
            },
            else => {},
        }
        return out.append(expr);
    }

    /// `flatten` for a rule template. Binders are members.
    pub fn flattenTemplate(self: Combiner, template: TemplateExpr) ?TemplateBag {
        var out = TemplateBag{};
        if (!self.flattenTemplateInto(template, &out)) return null;
        return out;
    }

    fn flattenTemplateInto(self: Combiner, template: TemplateExpr, out: *TemplateBag) bool {
        switch (template) {
            .app => |app| {
                if (app.term_id == self.head) {
                    for (app.args) |arg| {
                        if (!self.flattenTemplateInto(arg, out)) return false;
                    }
                    return true;
                }
                if (app.args.len == 0 and app.term_id == self.unit) return true;
            },
            .binder => {},
        }
        return out.append(template);
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
