const std = @import("std");
const ExprId = @import("../expr.zig").ExprId;
const TemplateExpr = @import("../rules.zig").TemplateExpr;
const compareExprIds = @import("../acui_support.zig").compareExprIds;
const SemanticCompare = @import("./semantic_compare.zig");
const StructuralCongruence = @import("./congruence.zig");
const types = @import("./types.zig");
const BinderSpace = types.BinderSpace;
const StructuralFragment = types.StructuralFragment;
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
        .app => |app| {
            if (app.term_id == profile.headTermId() and app.args.len == 2) {
                try collectTemplateStructuralItems(
                    self,
                    app.args[0],
                    space,
                    profile,
                    out,
                    remainders,
                    bindings,
                    pre_required,
                );
                try collectTemplateStructuralItems(
                    self,
                    app.args[1],
                    space,
                    profile,
                    out,
                    remainders,
                    bindings,
                    pre_required,
                );
                return;
            }
            if (app.term_id == profile.unitTermId() and app.args.len == 0 and
                profile.combiner.supportsLeftUnit() and
                profile.combiner.supportsRightUnit())
            {
                return;
            }
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
    var raw = std.ArrayListUnmanaged(ExprId).empty;
    defer raw.deinit(self.allocator);

    try StructuralCongruence.collectItems(self, expr_id, profile, &raw);
    var appender = try ItemAppender.init(self, profile.fragment, out);
    defer appender.deinit(self.allocator);
    for (raw.items) |item| {
        try appender.append(self, item);
    }
}

/// Appends items to `out` in a fragment's item order: sorted when the
/// combiner commutes, and without an item `bindingCompatible` with one
/// already kept when it is idempotent.
///
/// For a commutative idempotent bag, a new item is compared only with the
/// kept items it could match. Items with one canonical form always match,
/// and items with different canonical forms match only when one of them
/// `meetsOtherForms`. So an item that does not is compared only with the
/// kept items that do.
pub const ItemAppender = struct {
    fragment: StructuralFragment,
    out: *std.ArrayListUnmanaged(ExprId),
    /// Canonical forms of the kept items (`.acui` only).
    canonical: std.AutoHashMapUnmanaged(ExprId, void) = .empty,
    /// Kept items whose canonical form `meetsOtherForms` (`.acui` only),
    /// in `out` order.
    meeting: std.ArrayListUnmanaged(ExprId) = .empty,

    /// `out` may already hold items in the fragment's order.
    pub fn init(
        self: anytype,
        fragment: StructuralFragment,
        out: *std.ArrayListUnmanaged(ExprId),
    ) anyerror!ItemAppender {
        var appender: ItemAppender = .{ .fragment = fragment, .out = out };
        errdefer appender.deinit(self.allocator);
        if (fragment == .acui) {
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
        switch (appender.fragment) {
            .au => try out.append(self.allocator, expr_id),
            .acu => try insertSorted(self, out, expr_id),
            .aui => {
                if (out.items.len != 0 and try SemanticCompare.bindingCompatible(
                    self,
                    out.items[out.items.len - 1],
                    expr_id,
                )) {
                    return;
                }
                try out.append(self.allocator, expr_id);
            },
            .acui => {
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

pub fn rebuildStructuralExpr(
    self: anytype,
    items: []const ExprId,
    head_term_id: u32,
    unit_term_id: u32,
) anyerror!ExprId {
    if (items.len == 0) {
        return try @constCast(&self.theorem.interner).internApp(
            unit_term_id,
            &.{},
        );
    }
    if (items.len == 1) return items[0];

    var current = items[items.len - 1];
    var idx = items.len - 1;
    while (idx > 0) {
        idx -= 1;
        current = try @constCast(&self.theorem.interner).internApp(
            head_term_id,
            &[_]ExprId{ items[idx], current },
        );
    }
    return current;
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
