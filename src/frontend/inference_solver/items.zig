const std = @import("std");
const ExprId = @import("../expr.zig").ExprId;
const TemplateExpr = @import("../rules.zig").TemplateExpr;
const templateHasUnboundBinder =
    @import("../rules.zig").templateHasUnboundBinder;
const ExprModule = @import("../expr.zig");
const AcuiBag = @import("../acui_bag.zig");
const compareExprIds = @import("../acui_support.zig").compareExprIds;
const SemanticCompare = @import("./semantic_compare.zig");
const types = @import("./types.zig");
const BinderSpace = types.BinderSpace;
const StructuralProfile = types.StructuralProfile;
const StructuralRemainder = types.StructuralRemainder;
const StructuralTemplateItem = types.StructuralTemplateItem;

pub fn structuralProfileFor(
    self: anytype,
    head_term_id: u32,
    unit_term_id: u32,
) anyerror!StructuralProfile {
    const profile = try resolveStructuralProfile(self, head_term_id) orelse {
        return error.UnifyMismatch;
    };
    if (profile.unitTermId() != unit_term_id) {
        return error.UnifyMismatch;
    }
    return profile;
}

pub fn collectTemplateStructuralItems(
    self: anytype,
    template: TemplateExpr,
    space: BinderSpace,
    profile: StructuralProfile,
    out: *std.ArrayListUnmanaged(StructuralTemplateItem),
    remainders: *std.ArrayListUnmanaged(StructuralRemainder),
    bindings: []const ?ExprId,
    pre_required: *std.ArrayListUnmanaged(ExprId),
) anyerror!void {
    switch (template) {
        .binder => |idx| {
            if (isStructuralRemainderBinder(self, space, idx, profile)) {
                if (idx < bindings.len) {
                    if (bindings[idx]) |bound_value| {
                        var items = std.ArrayListUnmanaged(ExprId).empty;
                        defer items.deinit(self.allocator);
                        try collectCanonicalStructuralItems(
                            self,
                            bound_value,
                            profile,
                            &items,
                        );
                        if (profile.isCommutative()) {
                            try pre_required.appendSlice(
                                self.allocator,
                                items.items,
                            );
                        } else {
                            for (items.items) |item| {
                                try appendTemplateStructuralItem(
                                    self,
                                    profile,
                                    out,
                                    .{ .exact = item },
                                );
                            }
                        }
                        return;
                    }
                }
                try remainders.append(self.allocator, .{
                    .binder_idx = idx,
                    .item_pos = out.items.len,
                });
                return;
            }
            try appendTemplateStructuralItem(
                self,
                profile,
                out,
                .{ .template = template },
            );
        },
        .app => {
            const spine = AcuiBag.Spine.provable(profile.combiner);
            if (spine.splitTemplate(template)) |parts| {
                for (parts) |part| try collectTemplateStructuralItems(
                    self,
                    part,
                    space,
                    profile,
                    out,
                    remainders,
                    bindings,
                    pre_required,
                );
                return;
            }
            if (spine.skipsTemplate(template)) return;
            try appendTemplateStructuralItem(
                self,
                profile,
                out,
                .{ .template = template },
            );
        },
    }
}

pub fn collectCanonicalStructuralItems(
    self: anytype,
    expr_id: ExprId,
    profile: StructuralProfile,
    out: *std.ArrayListUnmanaged(ExprId),
) anyerror!void {
    try collectConcreteStructuralItems(
        self,
        try self.canonicalizer.canonicalize(expr_id),
        profile,
        out,
    );
}

pub fn collectConcreteStructuralItems(
    self: anytype,
    expr_id: ExprId,
    profile: StructuralProfile,
    out: *std.ArrayListUnmanaged(ExprId),
) anyerror!void {
    var appender = try ItemAppender.init(self, profile.law, out);
    defer appender.deinit(self.allocator);
    try appendConcreteStructuralItems(self, expr_id, profile, &appender);
}

fn appendConcreteStructuralItems(
    self: anytype,
    expr_id: ExprId,
    profile: StructuralProfile,
    appender: *ItemAppender,
) anyerror!void {
    var raw = std.ArrayListUnmanaged(ExprId).empty;
    defer raw.deinit(self.allocator);

    try AcuiBag.Spine.raw(profile.headTermId()).collect(self.allocator, self.theorem, expr_id, &raw);
    // A walk ticks once per node, and a spine of n leaves has 2n - 1 nodes.
    ExprModule.work_ticks_walk +%= 2 * raw.items.len - 1;
    const provable = AcuiBag.Spine.provable(profile.combiner);
    for (raw.items) |item| {
        if (provable.skips(self.theorem, item)) continue;
        if (try openDefMember(self, item)) |body| {
            try appendConcreteStructuralItems(
                self,
                try self.canonicalizer.canonicalize(body),
                profile,
                appender,
            );
            continue;
        }
        try appender.append(self, item);
    }
}

/// The body of `item` when it is a def application the solve opens
/// (`Solver.open_def_members`); null otherwise, noting a def it reads
/// whole.
fn openDefMember(self: anytype, item: ExprId) anyerror!?ExprId {
    const node = self.theorem.interner.node(item);
    const app = switch (node.*) {
        .app => |value| value,
        else => return null,
    };
    if (self.env.openableDef(app.term_id) == null) return null;
    if (!self.open_def_members) {
        self.saw_def_member = true;
        return null;
    }
    return try self.defOpsContext().unfoldConcreteDef(item);
}

/// Appends items to `out` in a law's item order: sorted when the
/// combiner commutes, and without an item `bindingCompatible` with one
/// already kept when it is idempotent.
///
/// For a commutative idempotent bag, a new item is compared only with the
/// kept items it could match. Items with one canonical form always match,
/// and items with different canonical forms match only when one of them
/// `meetsOtherForms`. So an item that does not is compared only with the
/// kept items that do.
pub const ItemAppender = struct {
    law: AcuiBag.Law,
    out: *std.ArrayListUnmanaged(ExprId),
    /// Canonical forms of the kept items (`.set` only).
    canonical: std.AutoHashMapUnmanaged(ExprId, void) = .empty,
    /// Kept items whose canonical form `meetsOtherForms` (`.set` only),
    /// in `out` order.
    meeting: std.ArrayListUnmanaged(ExprId) = .empty,

    /// `out` may already hold items in the law's order.
    pub fn init(
        self: anytype,
        law: AcuiBag.Law,
        out: *std.ArrayListUnmanaged(ExprId),
    ) anyerror!ItemAppender {
        var appender: ItemAppender = .{ .law = law, .out = out };
        errdefer appender.deinit(self.allocator);
        if (law == .set) {
            for (out.items) |item| {
                const form = try FormOf.get(self, item);
                try appender.keep(self, item, form);
            }
        }
        return appender;
    }

    pub fn deinit(appender: *ItemAppender, allocator: std.mem.Allocator) void {
        appender.canonical.deinit(allocator);
        appender.meeting.deinit(allocator);
    }

    pub fn append(appender: *ItemAppender, self: anytype, expr_id: ExprId) anyerror!void {
        const out = appender.out;
        switch (appender.law) {
            .sequence => try out.append(self.allocator, expr_id),
            .multiset => try insertSorted(self, out, expr_id),
            .idempotent_sequence => {
                if (out.items.len != 0 and try SemanticCompare.bindingCompatible(
                    self,
                    out.items[out.items.len - 1],
                    expr_id,
                )) {
                    return;
                }
                try out.append(self.allocator, expr_id);
            },
            .set => {
                const form = try FormOf.get(self, expr_id);
                if (appender.canonical.contains(form.canonical)) return;
                const candidates = if (form.meets_others)
                    out.items
                else
                    appender.meeting.items;
                for (candidates) |existing| {
                    if (try SemanticCompare.bindingCompatible(self, existing, expr_id)) return;
                }
                try insertSorted(self, out, expr_id);
                try appender.keep(self, expr_id, form);
            },
        }
    }

    fn keep(appender: *ItemAppender, self: anytype, expr_id: ExprId, form: FormOf) anyerror!void {
        try appender.canonical.put(self.allocator, form.canonical, {});
        if (form.meets_others) try appender.meeting.append(self.allocator, expr_id);
    }
};

const FormOf = struct {
    canonical: ExprId,
    meets_others: bool,

    fn get(self: anytype, expr_id: ExprId) anyerror!FormOf {
        const canonical = try self.canonicalizer.canonicalize(expr_id);
        return .{
            .canonical = canonical,
            .meets_others = try SemanticCompare.meetsOtherForms(self, canonical),
        };
    }
};

/// Inserts after the last item not greater than `expr_id`; equal items
/// are the same expression, so their order does not matter.
fn insertSorted(
    self: anytype,
    out: *std.ArrayListUnmanaged(ExprId),
    expr_id: ExprId,
) anyerror!void {
    var insert_at = out.items.len;
    while (insert_at > 0 and compareExprIds(
        self.theorem,
        out.items[insert_at - 1],
        expr_id,
    ) == .gt) insert_at -= 1;
    try out.insert(self.allocator, insert_at, expr_id);
}

pub fn appendTemplateStructuralItem(
    self: anytype,
    profile: StructuralProfile,
    out: *std.ArrayListUnmanaged(StructuralTemplateItem),
    item: StructuralTemplateItem,
) anyerror!void {
    if (profile.isIdempotent() and out.items.len != 0 and
        sameStructuralTemplateItem(out.items[out.items.len - 1], item))
    {
        return;
    }
    try out.append(self.allocator, item);
}

/// The bag holding `items`, in the law's item order. A commutative bag
/// lists them in source order instead (`MemberOrder`).
pub fn rebuildStructuralExpr(
    self: anytype,
    items: []const ExprId,
    profile: StructuralProfile,
) anyerror!ExprId {
    if (!profile.isCommutative() or items.len < 2) {
        return try nestStructuralExpr(self, items, profile);
    }
    return try nestInSourceOrder(self, items, items, profile);
}

/// The bag holding `items`, ordered by the ranks of `keys`, their
/// canonical forms (`MemberOrder.permutation`).
fn nestInSourceOrder(
    self: anytype,
    items: []const ExprId,
    keys: []const ExprId,
    profile: StructuralProfile,
) anyerror!ExprId {
    const order = try self.member_order.permutation(self.allocator, keys);
    defer self.allocator.free(order);
    const ordered = try self.allocator.alloc(ExprId, items.len);
    defer self.allocator.free(ordered);
    for (order, ordered) |idx, *item| item.* = items[idx];
    return try nestStructuralExpr(self, ordered, profile);
}

/// The bag holding `items` in the order given, nested the way the
/// matched sources nest (`MemberOrder.right_nested`).
pub fn nestStructuralExpr(
    self: anytype,
    items: []const ExprId,
    profile: StructuralProfile,
) anyerror!ExprId {
    const interner = @constCast(&self.theorem.interner);
    if (items.len == 0) return try interner.internApp(profile.unitTermId(), &.{});
    const head = profile.headTermId();
    if (self.member_order.right_nested orelse true) {
        var current = items[items.len - 1];
        var idx = items.len - 1;
        while (idx > 0) {
            idx -= 1;
            current = try interner.internApp(head, &.{ items[idx], current });
        }
        return current;
    }
    var current = items[0];
    for (items[1..]) |item| {
        current = try interner.internApp(head, &.{ current, item });
    }
    return current;
}

/// Where each bag member first appeared in a matched source, so that a
/// bag rebuilt from canonical items (a remainder binder's value) lists its
/// members in the source's order and nests the way the source does. The
/// rearrangement certificate between a source and its rebuilt bag then
/// moves only the members a rule takes out, where a sorted rebuild would
/// re-sort the whole bag: quadratic in how far the source is from sorted.
///
/// A member keeps the position of the source it was first seen in, so
/// when two sources list members in different orders the first matched
/// one wins: a rule's premises before its conclusion, and a `@view`'s
/// concrete conclusion before its premises (`Solver.solveOnce`).
/// Each copy of a repeated member has a position of its own: the nth copy
/// in a rebuilt bag goes where the nth copy first appeared, not next to
/// the first. Members no source holds go last, in item order.
pub const MemberOrder = struct {
    /// Each copy of a canonical member -> position of its first appearance.
    ranks: std.AutoHashMapUnmanaged(Copy, u32) = .empty,
    /// Sources already registered: a branch fan-out matches one source
    /// once per branch.
    sources: std.AutoHashMapUnmanaged(ExprId, void) = .empty,
    /// Whether the first source with one nested side nests it on the
    /// right. Null until such a source is seen; a rebuild then nests to
    /// the right.
    right_nested: ?bool = null,

    pub fn deinit(order: *MemberOrder, allocator: std.mem.Allocator) void {
        order.ranks.deinit(allocator);
        order.sources.deinit(allocator);
    }

    pub fn clear(order: *MemberOrder) void {
        order.ranks.clearRetainingCapacity();
        order.sources.clearRetainingCapacity();
        order.right_nested = null;
    }

    /// Records the members of `source`, a bag under `profile`'s combiner,
    /// in source order. The map lives on `self.real_allocator`: it outlives
    /// the per-solve arena's generations.
    pub fn register(
        order: *MemberOrder,
        self: anytype,
        profile: StructuralProfile,
        source: ExprId,
    ) anyerror!void {
        if ((try order.sources.getOrPut(self.real_allocator, source)).found_existing) return;
        var copies: CopyCounts = .empty;
        defer copies.deinit(self.allocator);
        try order.registerMembers(self, profile, source, &copies);
    }

    /// Ranks the members of `source`, counting copies in `copies`, which a
    /// def member's body shares with the bag it stands in.
    fn registerMembers(
        order: *MemberOrder,
        self: anytype,
        profile: StructuralProfile,
        source: ExprId,
        copies: *CopyCounts,
    ) anyerror!void {
        const spine = AcuiBag.Spine.raw(profile.headTermId());
        if (order.right_nested == null) {
            if (spine.split(self.theorem, source)) |parts| {
                const left = spine.isBag(self.theorem, parts[0]);
                const right = spine.isBag(self.theorem, parts[1]);
                if (left != right) order.right_nested = right;
            }
        }
        var raw = std.ArrayListUnmanaged(ExprId).empty;
        defer raw.deinit(self.allocator);
        try spine.collect(self.allocator, self.theorem, source, &raw);
        for (raw.items) |member| {
            if (try openDefMember(self, member)) |body| {
                try order.registerMembers(self, profile, body, copies);
                continue;
            }
            const canonical = try self.canonicalizer.canonicalize(member);
            const copy: Copy = .{
                .member = canonical,
                .nth = try nextCopy(self.allocator, copies, canonical),
            };
            const gop = try order.ranks.getOrPut(self.real_allocator, copy);
            if (!gop.found_existing) gop.value_ptr.* = order.ranks.count() - 1;
        }
    }

    /// The indices of `items` by rank, unranked items last in item
    /// order; the caller frees them. Each item is looked up once, and the
    /// sort runs on (rank, index) keys, which are distinct.
    pub fn permutation(
        order: *const MemberOrder,
        allocator: std.mem.Allocator,
        items: []const ExprId,
    ) ![]u32 {
        const keys = try allocator.alloc(u64, items.len);
        defer allocator.free(keys);
        var copies: CopyCounts = .empty;
        defer copies.deinit(allocator);
        for (items, keys, 0..) |item, *key, idx| {
            const copy: Copy = .{
                .member = item,
                .nth = try nextCopy(allocator, &copies, item),
            };
            const rank: u64 = order.ranks.get(copy) orelse std.math.maxInt(u32);
            key.* = rank << 32 | idx;
        }
        std.sort.pdq(u64, keys, {}, std.sort.asc(u64));
        const out = try allocator.alloc(u32, items.len);
        for (keys, out) |key, *idx| idx.* = @truncate(key);
        return out;
    }

    /// The nth copy of a member, counting from 0.
    const Copy = struct { member: ExprId, nth: u32 };
    /// Member -> how many copies of it have been seen.
    const CopyCounts = std.AutoHashMapUnmanaged(ExprId, u32);

    fn nextCopy(
        allocator: std.mem.Allocator,
        copies: *CopyCounts,
        member: ExprId,
    ) !u32 {
        const seen = try copies.getOrPut(allocator, member);
        if (!seen.found_existing) seen.value_ptr.* = 0;
        defer seen.value_ptr.* += 1;
        return seen.value_ptr.*;
    }
};

/// `bag` with its members in the order `sources` list them, nested as they
/// nest: how a structural solve lays out a remainder (`MemberOrder`), for a
/// bag another reading produced, such as one read off a sorted normal form.
/// `bag` itself when it is not a bag of `profile`'s combiner, or when the
/// combiner does not commute. Resets `self.member_order` to the ranks of
/// `sources`, so it is for a solver that is done solving.
pub fn layoutInSourceOrder(
    self: anytype,
    bag: ExprId,
    profile: StructuralProfile,
    sources: []const ExprId,
) anyerror!ExprId {
    const spine = AcuiBag.Spine.raw(profile.headTermId());
    if (!profile.isCommutative() or !spine.isBag(self.theorem, bag)) return bag;
    self.member_order.clear();
    var visited = std.AutoHashMapUnmanaged(ExprId, void).empty;
    defer visited.deinit(self.allocator);
    for (sources) |source| try registerSourceBags(self, profile, source, &visited);

    var items = std.ArrayListUnmanaged(ExprId).empty;
    defer items.deinit(self.allocator);
    try spine.collect(self.allocator, self.theorem, bag, &items);
    const canonical = try self.allocator.alloc(ExprId, items.items.len);
    defer self.allocator.free(canonical);
    for (items.items, canonical) |item, *out| {
        out.* = try self.canonicalizer.canonicalize(item);
    }
    return try nestInSourceOrder(self, items.items, canonical, profile);
}

/// Registers each bag of `profile`'s combiner in `expr` that no larger one
/// holds.
fn registerSourceBags(
    self: anytype,
    profile: StructuralProfile,
    expr: ExprId,
    visited: *std.AutoHashMapUnmanaged(ExprId, void),
) anyerror!void {
    if ((try visited.getOrPut(self.allocator, expr)).found_existing) return;
    if (AcuiBag.Spine.raw(profile.headTermId()).isBag(self.theorem, expr)) {
        return try self.member_order.register(self, profile, expr);
    }
    switch (self.theorem.interner.node(expr).*) {
        .app => |app| for (app.args) |arg| {
            try registerSourceBags(self, profile, arg, visited);
        },
        else => {},
    }
}

/// How many members of a structural template still hold an unbound binder,
/// not counting remainder binders; null when `template` is not structural.
pub fn openTemplateMemberCount(
    self: anytype,
    template: TemplateExpr,
    space: BinderSpace,
    bindings: []const ?ExprId,
) anyerror!?usize {
    const app = switch (template) {
        .app => |value| value,
        .binder => return null,
    };
    const profile = try resolveStructuralProfile(self, app.term_id) orelse
        return null;
    var counter: struct {
        solver: @TypeOf(self),
        space: BinderSpace,
        profile: StructuralProfile,
        bindings: []const ?ExprId,
        count: usize = 0,
        pub fn leaf(c: *@This(), item: TemplateExpr) void {
            if (item == .binder and isStructuralRemainderBinder(
                c.solver,
                c.space,
                item.binder,
                c.profile,
            )) return;
            if (templateHasUnboundBinder(item, c.bindings)) c.count += 1;
        }
    } = .{
        .solver = self,
        .space = space,
        .profile = profile,
        .bindings = bindings,
    };
    AcuiBag.Spine.provable(profile.combiner).visitTemplate(template, &counter);
    return counter.count;
}

pub fn isStructuralRemainderBinder(
    self: anytype,
    space: BinderSpace,
    idx: usize,
    profile: StructuralProfile,
) bool {
    const sort_name = getBinderSort(self, space, idx) orelse return false;
    const term_decl = if (profile.headTermId() < self.env.terms.items.len)
        &self.env.terms.items[profile.headTermId()]
    else
        return false;
    return std.mem.eql(u8, sort_name, term_decl.ret_sort_name);
}

pub fn resolveStructuralProfile(
    self: anytype,
    head_term_id: u32,
) anyerror!?StructuralProfile {
    const combiner = try self.registry.resolveStructuralCombiner(
        self.env,
        head_term_id,
    ) orelse return null;
    return StructuralProfile.init(combiner);
}

pub fn getBinderSort(
    self: anytype,
    space: BinderSpace,
    idx: usize,
) ?[]const u8 {
    return switch (space) {
        .rule => if (idx < self.rule.args.len)
            self.rule.args[idx].sort_name
        else
            null,
        .view => if (self.view) |view|
            if (idx < view.arg_infos.len)
                view.arg_infos[idx].sort_name
            else
                null
        else
            null,
    };
}

fn sameStructuralTemplateItem(
    lhs: StructuralTemplateItem,
    rhs: StructuralTemplateItem,
) bool {
    return switch (lhs) {
        .exact => |lhs_expr| switch (rhs) {
            .exact => |rhs_expr| lhs_expr == rhs_expr,
            .template => false,
        },
        .template => |lhs_tmpl| switch (rhs) {
            .exact => false,
            .template => |rhs_tmpl| sameTemplateExpr(lhs_tmpl, rhs_tmpl),
        },
    };
}

fn sameTemplateExpr(lhs: TemplateExpr, rhs: TemplateExpr) bool {
    return switch (lhs) {
        .binder => |lhs_idx| switch (rhs) {
            .binder => |rhs_idx| lhs_idx == rhs_idx,
            .app => false,
        },
        .app => |lhs_app| switch (rhs) {
            .binder => false,
            .app => |rhs_app| blk: {
                if (lhs_app.term_id != rhs_app.term_id or
                    lhs_app.args.len != rhs_app.args.len)
                {
                    break :blk false;
                }
                for (lhs_app.args, rhs_app.args) |lhs_arg, rhs_arg| {
                    if (!sameTemplateExpr(lhs_arg, rhs_arg)) {
                        break :blk false;
                    }
                }
                break :blk true;
            },
        },
    };
}
