//! One reading of an `@acui` combiner application as a bag of members.
//!
//! `flatten` splices nested applications of the combiner head and drops the
//! combiner's own unit, keeping every other member in left-to-right order with
//! its duplicates. What the members *mean* depends on the declared laws, which
//! `lawOf` reports: a set (commutative and idempotent), a multiset (commutative
//! only) or a sequence (not commutative). Callers that compare members as a set
//! dedup explicitly; nothing here dedups on the combiner's behalf.
//!
//! A bag holds at most `capacity` members. On overflow `flatten` returns null,
//! and callers abstain rather than read a truncated bag.

const std = @import("std");
const types = @import("../types.zig");
const ExprId = @import("../../../expr.zig").ExprId;
const TheoremContext = @import("../../../expr.zig").TheoremContext;
const TemplateExpr = @import("../../../rules.zig").TemplateExpr;
const Context = types.Context;

pub const capacity = 64;

pub const Law = enum {
    /// Commutative and idempotent: only which members occur counts.
    set,
    /// Commutative, not idempotent: how often each member occurs counts.
    multiset,
    /// Not commutative: the order of the members counts.
    sequence,
};

/// The member semantics of combiner `head_id`, or null when it is not an
/// `@acui` head.
pub fn lawOf(context: *const Context, head_id: u32) ?Law {
    const combiner = context.registry.acui_by_head.get(head_id) orelse return null;
    if (combiner.comm_name == null) return .sequence;
    return if (combiner.idem_name != null) .set else .multiset;
}

/// The unit term of combiner `head_id`, or null when it is not an `@acui` head
/// or its unit does not resolve.
pub fn unitOf(context: *const Context, head_id: u32) ?u32 {
    const combiner = context.registry.acui_by_head.get(head_id) orelse return null;
    return context.env.term_names.get(combiner.unit_term_name);
}

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

/// The members of `expr` under combiner `head_id`, or null on overflow. An
/// `expr` not headed by `head_id` is a one-member bag, or empty if it is the
/// unit.
pub fn flatten(
    context: *const Context,
    theorem: *const TheoremContext,
    head_id: u32,
    expr: ExprId,
) ?ExprBag {
    var out = ExprBag{};
    const unit = unitOf(context, head_id);
    if (!flattenInto(theorem, head_id, unit, expr, &out)) return null;
    return out;
}

fn flattenInto(
    theorem: *const TheoremContext,
    head_id: u32,
    unit: ?u32,
    expr: ExprId,
    out: *ExprBag,
) bool {
    switch (theorem.interner.node(expr).*) {
        .app => |app| {
            if (app.term_id == head_id) {
                for (app.args) |arg| {
                    if (!flattenInto(theorem, head_id, unit, arg, out)) return false;
                }
                return true;
            }
            if (app.args.len == 0 and unit != null and app.term_id == unit.?) return true;
        },
        else => {},
    }
    return out.append(expr);
}

/// `flatten` for a rule template. Binders are members.
pub fn flattenTemplate(
    context: *const Context,
    head_id: u32,
    template: TemplateExpr,
) ?TemplateBag {
    var out = TemplateBag{};
    const unit = unitOf(context, head_id);
    if (!flattenTemplateInto(head_id, unit, template, &out)) return null;
    return out;
}

fn flattenTemplateInto(
    head_id: u32,
    unit: ?u32,
    template: TemplateExpr,
    out: *TemplateBag,
) bool {
    switch (template) {
        .app => |app| {
            if (app.term_id == head_id) {
                for (app.args) |arg| {
                    if (!flattenTemplateInto(head_id, unit, arg, out)) return false;
                }
                return true;
            }
            if (app.args.len == 0 and unit != null and app.term_id == unit.?) return true;
        },
        .binder => {},
    }
    return out.append(template);
}

/// Rebuild `members` as one expression: the combiner's unit when empty (null if
/// the unit does not resolve), the member itself when single, else a right fold.
pub fn build(
    context: *const Context,
    theorem: *TheoremContext,
    head_id: u32,
    members: []const ExprId,
) error{ OutOfMemory, TooManyTheoremExprs }!?ExprId {
    if (members.len == 0) {
        const unit = unitOf(context, head_id) orelse return null;
        return try theorem.interner.internApp(unit, &.{});
    }
    return try rightFold(theorem, head_id, members);
}

/// Right-fold `members` back into binary `head_id` combiner applications,
/// preserving left-to-right order: `[a, b, c]` → `head(a, head(b, c))`. A
/// single member is returned as itself. The empty region is the combiner's
/// unit, whose resolution can fail — callers handle that case themselves (or
/// use `build`).
pub fn rightFold(
    theorem: *TheoremContext,
    head_id: u32,
    members: []const ExprId,
) error{ OutOfMemory, TooManyTheoremExprs }!ExprId {
    std.debug.assert(members.len > 0);
    var result = members[members.len - 1];
    var i = members.len - 1;
    while (i > 0) {
        i -= 1;
        result = try theorem.interner.internApp(head_id, &.{ members[i], result });
    }
    return result;
}
