const std = @import("std");
const ExprId = @import("../expr.zig").ExprId;
const BranchStateOps = @import("./branch_state.zig");
const StructuralIntervals = @import("./intervals.zig");
const StructuralItems = @import("./items.zig");
const StructuralStateUpdates =
    @import("./state_updates.zig");
const types = @import("./types.zig");
const BinderSpace = types.BinderSpace;
const BranchState = types.BranchState;
const StructuralJointObligation = types.StructuralJointObligation;
const StructuralProfile = types.StructuralProfile;

pub fn solveStructuralObligation(
    self: anytype,
    state: BranchState,
    space: BinderSpace,
    obligation: StructuralJointObligation,
) anyerror![]BranchState {
    const profile = try StructuralItems.resolveStructuralProfile(
        self,
        obligation.head_term_id,
    ) orelse return error.UnifyMismatch;
    if (profile.unitTermId() != obligation.unit_term_id) {
        return error.UnifyMismatch;
    }
    return switch (profile.fragment) {
        .au, .aui => try solveOrderedStructuralObligation(
            self,
            state,
            space,
            obligation,
            profile,
        ),
        .acu => try solveAcuStructuralObligation(
            self,
            state,
            space,
            obligation,
            profile,
        ),
        .acui => try solveAcuiStructuralObligation(
            self,
            state,
            space,
            obligation,
            profile,
        ),
    };
}

fn solveOrderedStructuralObligation(
    self: anytype,
    state: BranchState,
    space: BinderSpace,
    obligation: StructuralJointObligation,
    profile: StructuralProfile,
) anyerror![]BranchState {
    var target_items = std.ArrayListUnmanaged(ExprId){};
    defer target_items.deinit(self.allocator);
    try StructuralItems.collectCanonicalStructuralItems(
        self,
        obligation.lower_expr,
        profile,
        &target_items,
    );

    const binder_exprs = try self.allocator.alloc(
        ExprId,
        obligation.binder_idxs.len,
    );
    defer self.allocator.free(binder_exprs);

    var out = std.ArrayListUnmanaged(BranchState){};
    try searchOrderedStructuralObligationAssignments(
        self,
        state,
        space,
        obligation,
        profile,
        target_items.items,
        binder_exprs,
        0,
        0,
        &out,
    );
    return try out.toOwnedSlice(self.allocator);
}

fn searchOrderedStructuralObligationAssignments(
    self: anytype,
    state: BranchState,
    space: BinderSpace,
    obligation: StructuralJointObligation,
    profile: StructuralProfile,
    target_items: []const ExprId,
    binder_exprs: []ExprId,
    binder_pos: usize,
    item_start: usize,
    out: *std.ArrayListUnmanaged(BranchState),
) anyerror!void {
    if (binder_pos >= obligation.binder_idxs.len) {
        if (item_start != target_items.len) return;
        try StructuralStateUpdates.appendStructuralCandidateState(
            self,
            state,
            space,
            obligation.binder_idxs,
            binder_exprs,
            1,
            out,
        );
        return;
    }

    var item_end = item_start;
    while (item_end <= target_items.len) : (item_end += 1) {
        const expr_id = try StructuralItems.rebuildStructuralExpr(
            self,
            target_items[item_start..item_end],
            profile.headTermId(),
            profile.unitTermId(),
        );
        if (!try StructuralStateUpdates.candidateBindingCompatible(
            self,
            &state,
            space,
            obligation.binder_idxs[binder_pos],
            expr_id,
        )) {
            continue;
        }
        binder_exprs[binder_pos] = expr_id;
        try searchOrderedStructuralObligationAssignments(
            self,
            state,
            space,
            obligation,
            profile,
            target_items,
            binder_exprs,
            binder_pos + 1,
            item_end,
            out,
        );
    }
}

fn solveAcuStructuralObligation(
    self: anytype,
    state: BranchState,
    space: BinderSpace,
    obligation: StructuralJointObligation,
    profile: StructuralProfile,
) anyerror![]BranchState {
    var target_items = std.ArrayListUnmanaged(ExprId){};
    defer target_items.deinit(self.allocator);
    try StructuralItems.collectCanonicalStructuralItems(
        self,
        obligation.lower_expr,
        profile,
        &target_items,
    );

    const binder_item_lists = try initExprItemLists(
        self,
        obligation.binder_idxs.len,
    );
    defer deinitExprItemLists(self, binder_item_lists);

    var out = std.ArrayListUnmanaged(BranchState){};
    try searchAcuStructuralObligationAssignments(
        self,
        state,
        space,
        obligation,
        profile,
        target_items.items,
        binder_item_lists,
        0,
        &out,
    );
    return try out.toOwnedSlice(self.allocator);
}

fn searchAcuStructuralObligationAssignments(
    self: anytype,
    state: BranchState,
    space: BinderSpace,
    obligation: StructuralJointObligation,
    profile: StructuralProfile,
    binder_target_items: []const ExprId,
    binder_item_lists: []std.ArrayListUnmanaged(ExprId),
    item_pos: usize,
    out: *std.ArrayListUnmanaged(BranchState),
) anyerror!void {
    if (item_pos >= binder_target_items.len) {
        const binder_exprs = try rebuildBindingExprs(
            self,
            binder_item_lists,
            profile,
        );
        defer self.allocator.free(binder_exprs);
        try StructuralStateUpdates.appendStructuralCandidateState(
            self,
            state,
            space,
            obligation.binder_idxs,
            binder_exprs,
            1,
            out,
        );
        return;
    }

    for (binder_item_lists) |*items| {
        try items.append(self.allocator, binder_target_items[item_pos]);
        try searchAcuStructuralObligationAssignments(
            self,
            state,
            space,
            obligation,
            profile,
            binder_target_items,
            binder_item_lists,
            item_pos + 1,
            out,
        );
        _ = items.pop();
    }
}

/// One member's admissible binder subsets (bit `i` stands for the
/// obligation's `binder_idxs[i]`), in the order the cover enumeration
/// visits them: the required binders plus every optional one first, then
/// the optional part descending.
const MemberChoices = struct {
    item: ExprId,
    subsets: []const usize,
};

/// ACUI: every member of the actual bag goes to some subset of the
/// obligation's binders. A member's admissible subsets depend only on the
/// member and the per-binder bounds — never on where earlier members went —
/// so the obligation's covers are exactly the Cartesian product of the
/// per-member choice lists. When nothing outside those bounds can tell two
/// covers apart (`obligationCoupled`), the product is resolved in closed
/// form; otherwise the covers are enumerated for the later constraints to
/// filter.
fn solveAcuiStructuralObligation(
    self: anytype,
    state: BranchState,
    space: BinderSpace,
    obligation: StructuralJointObligation,
    profile: StructuralProfile,
) anyerror![]BranchState {
    var lower_items = std.ArrayListUnmanaged(ExprId){};
    defer lower_items.deinit(self.allocator);
    var upper_items = std.ArrayListUnmanaged(ExprId){};
    defer upper_items.deinit(self.allocator);
    try StructuralItems.collectCanonicalStructuralItems(
        self,
        obligation.lower_expr,
        profile,
        &lower_items,
    );
    try StructuralItems.collectCanonicalStructuralItems(
        self,
        obligation.upper_expr,
        profile,
        &upper_items,
    );

    const binder_lowers = try initExprItemLists(
        self,
        obligation.binder_idxs.len,
    );
    defer deinitExprItemLists(self, binder_lowers);
    const binder_uppers = try initExprItemLists(
        self,
        obligation.binder_idxs.len,
    );
    defer deinitExprItemLists(self, binder_uppers);

    for (
        binder_lowers,
        binder_uppers,
        obligation.binder_idxs,
    ) |*lower, *upper, binder_idx| {
        try collectAcuiBinderBounds(
            self,
            &state,
            space,
            binder_idx,
            profile,
            upper_items.items,
            lower,
            upper,
        );
    }

    const choices = try self.allocator.alloc(
        MemberChoices,
        upper_items.items.len,
    );
    for (choices) |*member| member.* = .{ .item = 0, .subsets = &.{} };
    defer {
        for (choices) |member| self.allocator.free(member.subsets);
        self.allocator.free(choices);
    }
    var out = std.ArrayListUnmanaged(BranchState){};
    for (upper_items.items, 0..) |item, idx| {
        choices[idx] = try admissibleSubsets(
            self,
            item,
            lower_items.items,
            binder_lowers,
            binder_uppers,
        );
        if (choices[idx].subsets.len == 0) {
            return try out.toOwnedSlice(self.allocator);
        }
    }

    if (!obligationCoupled(self, &state, space, obligation)) {
        if (try resolveCoverProduct(
            self,
            state,
            space,
            obligation,
            profile,
            choices,
            &out,
        )) {
            return try out.toOwnedSlice(self.allocator);
        }
        out.clearRetainingCapacity();
    }

    const binder_items = try initExprItemLists(
        self,
        obligation.binder_idxs.len,
    );
    defer deinitExprItemLists(self, binder_items);
    try enumerateCovers(
        self,
        state,
        space,
        obligation,
        profile,
        choices,
        binder_items,
        0,
        &out,
    );
    return try out.toOwnedSlice(self.allocator);
}

fn admissibleSubsets(
    self: anytype,
    item: ExprId,
    lower_items: []const ExprId,
    binder_lowers: []const std.ArrayListUnmanaged(ExprId),
    binder_uppers: []const std.ArrayListUnmanaged(ExprId),
) anyerror!MemberChoices {
    const global_required =
        try StructuralIntervals.structuralItemsContainCompatible(
            self,
            lower_items,
            item,
        );
    var required_mask: usize = 0;
    var allowed_mask: usize = 0;
    for (binder_lowers, binder_uppers, 0..) |lower, upper, idx| {
        if (try StructuralIntervals.structuralItemsContainCompatible(
            self,
            upper.items,
            item,
        )) {
            allowed_mask |= (@as(usize, 1) << @intCast(idx));
        }
        if (try StructuralIntervals.structuralItemsContainCompatible(
            self,
            lower.items,
            item,
        )) {
            required_mask |= (@as(usize, 1) << @intCast(idx));
        }
    }

    var subsets = std.ArrayListUnmanaged(usize){};
    errdefer subsets.deinit(self.allocator);
    if ((required_mask & ~allowed_mask) == 0) {
        const optional_mask = allowed_mask & ~required_mask;
        var choice = optional_mask;
        while (true) {
            const subset = required_mask | choice;
            if (!global_required or subset != 0) {
                try subsets.append(self.allocator, subset);
            }
            if (choice == 0) break;
            choice = (choice - 1) & optional_mask;
        }
    }
    return .{
        .item = item,
        .subsets = try subsets.toOwnedSlice(self.allocator),
    };
}

/// Whether any constraint outside `obligation`'s own binder bounds can tell
/// two of its covers apart: another joint obligation over one of its
/// binders, or, in the view space, a binder that `propagateViewBindings`
/// maps onto the rule space, where the rule's own obligations still wait.
/// Bounds from intervals and existing bindings are already folded into the
/// per-member masks, so an uncoupled obligation's covers pass every later
/// check unchanged.
fn obligationCoupled(
    self: anytype,
    state: *const BranchState,
    space: BinderSpace,
    obligation: StructuralJointObligation,
) bool {
    const obligations = BranchStateOps.getStructuralObligations(
        @constCast(state),
        space,
    );
    for (obligations) |other| {
        if (other.binder_idxs.ptr == obligation.binder_idxs.ptr) continue;
        for (other.binder_idxs) |other_idx| {
            for (obligation.binder_idxs) |idx| {
                if (idx == other_idx) return true;
            }
        }
    }
    if (space == .view) {
        const view = self.view orelse return true;
        for (obligation.binder_idxs) |idx| {
            if (idx < view.binder_map.len and view.binder_map[idx] != null) {
                return true;
            }
        }
    }
    return false;
}

/// Closed form of the cover enumeration for an uncoupled obligation. The
/// only consumer of the cover set is `pickUniqueSolution`, which takes the
/// first cover of minimal rank — rank sums the members per binder, so the
/// minimum puts every member in its first smallest admissible subset — and,
/// for the ambiguity report, the number of covers and the first one
/// enumerated. Emits the first cover as the representative of every cover
/// but the chosen one, then the chosen cover, in enumeration order. Returns
/// false if a representative was rejected, in which case the caller falls
/// back to enumerating.
fn resolveCoverProduct(
    self: anytype,
    state: BranchState,
    space: BinderSpace,
    obligation: StructuralJointObligation,
    profile: StructuralProfile,
    choices: []const MemberChoices,
    out: *std.ArrayListUnmanaged(BranchState),
) anyerror!bool {
    var count: usize = 1;
    for (choices) |member| count *|= member.subsets.len;
    if (count > 1) {
        const before = out.items.len;
        try appendCover(
            self,
            state,
            space,
            obligation,
            profile,
            choices,
            .first,
            count - 1,
            out,
        );
        if (out.items.len == before) return false;
    }
    const before = out.items.len;
    try appendCover(
        self,
        state,
        space,
        obligation,
        profile,
        choices,
        .minimal,
        1,
        out,
    );
    return out.items.len != before;
}

const CoverPick = enum { first, minimal };

fn appendCover(
    self: anytype,
    state: BranchState,
    space: BinderSpace,
    obligation: StructuralJointObligation,
    profile: StructuralProfile,
    choices: []const MemberChoices,
    pick: CoverPick,
    multiplicity: usize,
    out: *std.ArrayListUnmanaged(BranchState),
) anyerror!void {
    const binder_items = try initExprItemLists(
        self,
        obligation.binder_idxs.len,
    );
    defer deinitExprItemLists(self, binder_items);
    for (choices) |member| {
        const subset = switch (pick) {
            .first => member.subsets[0],
            .minimal => minimalSubset(member.subsets),
        };
        try placeMember(self, binder_items, member.item, subset);
    }
    const binder_exprs = try rebuildBindingExprs(
        self,
        binder_items,
        profile,
    );
    defer self.allocator.free(binder_exprs);
    try StructuralStateUpdates.appendStructuralCandidateState(
        self,
        state,
        space,
        obligation.binder_idxs,
        binder_exprs,
        multiplicity,
        out,
    );
}

/// The first subset of minimal size, in enumeration order.
fn minimalSubset(subsets: []const usize) usize {
    var best = subsets[0];
    for (subsets[1..]) |subset| {
        if (@popCount(subset) < @popCount(best)) best = subset;
    }
    return best;
}

fn enumerateCovers(
    self: anytype,
    state: BranchState,
    space: BinderSpace,
    obligation: StructuralJointObligation,
    profile: StructuralProfile,
    choices: []const MemberChoices,
    binder_items: []std.ArrayListUnmanaged(ExprId),
    member_pos: usize,
    out: *std.ArrayListUnmanaged(BranchState),
) anyerror!void {
    if (member_pos >= choices.len) {
        const binder_exprs = try rebuildBindingExprs(
            self,
            binder_items,
            profile,
        );
        defer self.allocator.free(binder_exprs);
        try StructuralStateUpdates.appendStructuralCandidateState(
            self,
            state,
            space,
            obligation.binder_idxs,
            binder_exprs,
            1,
            out,
        );
        return;
    }

    const member = choices[member_pos];
    for (member.subsets) |subset| {
        try placeMember(self, binder_items, member.item, subset);
        try enumerateCovers(
            self,
            state,
            space,
            obligation,
            profile,
            choices,
            binder_items,
            member_pos + 1,
            out,
        );
        unplaceMember(binder_items, subset);
    }
}

fn placeMember(
    self: anytype,
    binder_items: []std.ArrayListUnmanaged(ExprId),
    item: ExprId,
    subset: usize,
) !void {
    for (binder_items, 0..) |*items, idx| {
        if ((subset & (@as(usize, 1) << @intCast(idx))) != 0) {
            try items.append(self.allocator, item);
        }
    }
}

fn unplaceMember(
    binder_items: []std.ArrayListUnmanaged(ExprId),
    subset: usize,
) void {
    for (binder_items, 0..) |*items, idx| {
        if ((subset & (@as(usize, 1) << @intCast(idx))) != 0) {
            _ = items.pop();
        }
    }
}

fn collectAcuiBinderBounds(
    self: anytype,
    state: *const BranchState,
    space: BinderSpace,
    binder_idx: usize,
    profile: StructuralProfile,
    default_upper_items: []const ExprId,
    lower_out: *std.ArrayListUnmanaged(ExprId),
    upper_out: *std.ArrayListUnmanaged(ExprId),
) anyerror!void {
    const bindings = BranchStateOps.getBindings(@constCast(state), space);
    const intervals = BranchStateOps.getStructuralIntervals(
        @constCast(state),
        space,
    );
    if (binder_idx < bindings.len) {
        if (bindings[binder_idx]) |binding| {
            try StructuralItems.collectCanonicalStructuralItems(
                self,
                binding,
                profile,
                lower_out,
            );
            try upper_out.appendSlice(self.allocator, lower_out.items);
            return;
        }
    }
    if (binder_idx < intervals.len) {
        if (intervals[binder_idx]) |interval| {
            try StructuralItems.collectCanonicalStructuralItems(
                self,
                interval.lower_expr,
                profile,
                lower_out,
            );
            try StructuralItems.collectCanonicalStructuralItems(
                self,
                interval.upper_expr,
                profile,
                upper_out,
            );
            return;
        }
    }
    try upper_out.appendSlice(self.allocator, default_upper_items);
}

fn initExprItemLists(
    self: anytype,
    len: usize,
) ![]std.ArrayListUnmanaged(ExprId) {
    const lists = try self.allocator.alloc(std.ArrayListUnmanaged(ExprId), len);
    for (lists) |*items| items.* = .{};
    return lists;
}

fn deinitExprItemLists(
    self: anytype,
    lists: []std.ArrayListUnmanaged(ExprId),
) void {
    for (lists) |*items| items.deinit(self.allocator);
    self.allocator.free(lists);
}

fn rebuildBindingExprs(
    self: anytype,
    binder_item_lists: []const std.ArrayListUnmanaged(ExprId),
    profile: StructuralProfile,
) ![]ExprId {
    const binder_exprs = try self.allocator.alloc(ExprId, binder_item_lists.len);
    errdefer self.allocator.free(binder_exprs);

    for (binder_item_lists, 0..) |items, idx| {
        binder_exprs[idx] = try StructuralItems.rebuildStructuralExpr(
            self,
            items.items,
            profile.headTermId(),
            profile.unitTermId(),
        );
    }
    return binder_exprs;
}
