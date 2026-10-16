const std = @import("std");
const ExprId = @import("../expr.zig").ExprId;
const BranchStateOps = @import("./branch_state.zig");
const SemanticCompare = @import("./semantic_compare.zig");
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
    return switch (profile.law) {
        .sequence, .idempotent_sequence => try solveOrderedStructuralObligation(
            self,
            state,
            space,
            obligation,
            profile,
        ),
        .multiset, .set => try solveBagStructuralObligation(
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
    var target_items = std.ArrayListUnmanaged(ExprId).empty;
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

    var out = std.ArrayListUnmanaged(BranchState).empty;
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

/// One distinct member's admissible placements, in the order the cover
/// enumeration visits them. A placement is the number of copies of `item`
/// each of the obligation's binders takes (entry `i` for `binder_idxs[i]`);
/// `counts` holds the placements back to back.
const MemberChoices = struct {
    item: ExprId,
    binder_count: usize,
    counts: []const u32,

    fn len(self: MemberChoices) usize {
        return self.counts.len / self.binder_count;
    }

    fn placement(self: MemberChoices, idx: usize) []const u32 {
        return self.counts[idx * self.binder_count ..][0..self.binder_count];
    }
};

/// ACU and ACUI: the copies of each member of the actual bag go to the
/// obligation's binders, under ACU each copy to exactly one binder, under
/// ACUI the member to a nonempty subset of them. A member's admissible
/// placements depend only on the member and the per-binder bounds — never
/// on where other members went — so the obligation's covers are exactly the
/// Cartesian product of the per-member choice lists. When the bounds are
/// exact and nothing outside them can tell two covers apart
/// (`obligationCoupled`), the product is resolved in closed form; otherwise
/// the covers are enumerated for the later constraints to filter.
fn solveBagStructuralObligation(
    self: anytype,
    state: BranchState,
    space: BinderSpace,
    obligation: StructuralJointObligation,
    profile: StructuralProfile,
) anyerror![]BranchState {
    var lower_items = std.ArrayListUnmanaged(ExprId).empty;
    defer lower_items.deinit(self.allocator);
    var upper_items = std.ArrayListUnmanaged(ExprId).empty;
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
        try collectBinderBounds(
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
    // A set keeps no two compatible members, so ACUI's bounds hold as read;
    // ACU's count copies exactly only when compatibility is identity.
    const exact = profile.law == .set or
        !try boundsMeetOtherForms(self, upper_items.items, binder_lowers);

    var choices = std.ArrayListUnmanaged(MemberChoices).empty;
    defer {
        for (choices.items) |member| self.allocator.free(member.counts);
        choices.deinit(self.allocator);
    }
    var out = std.ArrayListUnmanaged(BranchState).empty;
    var item_pos: usize = 0;
    while (item_pos < upper_items.items.len) {
        const item = upper_items.items[item_pos];
        // Copies of one member sit next to each other in the sorted items.
        var copies: u32 = 1;
        while (item_pos + copies < upper_items.items.len and
            upper_items.items[item_pos + copies] == item) copies += 1;
        item_pos += copies;

        const member = switch (profile.law) {
            .set => try admissibleSubsets(
                self,
                item,
                lower_items.items,
                binder_lowers,
                binder_uppers,
            ),
            .multiset => try admissibleDistributions(
                self,
                item,
                copies,
                binder_lowers,
                binder_uppers,
                exact,
            ),
            .sequence, .idempotent_sequence => unreachable,
        };
        try choices.append(self.allocator, member);
        if (member.len() == 0) {
            return try out.toOwnedSlice(self.allocator);
        }
    }

    if (exact and !obligationCoupled(self, &state, space, obligation)) {
        if (try resolveCoverProduct(
            self,
            state,
            space,
            obligation,
            profile,
            choices.items,
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
        choices.items,
        binder_items,
        0,
        &out,
    );
    return try out.toOwnedSlice(self.allocator);
}

/// ACUI: the binder subsets a member may go to, the required binders plus
/// every optional one first, then the optional part descending.
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

    var counts = std.ArrayListUnmanaged(u32).empty;
    errdefer counts.deinit(self.allocator);
    if ((required_mask & ~allowed_mask) == 0) {
        const optional_mask = allowed_mask & ~required_mask;
        var choice = optional_mask;
        while (true) {
            const subset = required_mask | choice;
            if (!global_required or subset != 0) {
                for (0..binder_lowers.len) |idx| {
                    try counts.append(
                        self.allocator,
                        @intCast((subset >> @intCast(idx)) & 1),
                    );
                }
            }
            if (choice == 0) break;
            choice = (choice - 1) & optional_mask;
        }
    }
    return .{
        .item = item,
        .binder_count = binder_lowers.len,
        .counts = try counts.toOwnedSlice(self.allocator),
    };
}

/// ACU: the ways to share a member's `copies` among the binders, each
/// binder taking at least the copies its lower bound holds and at most
/// those its upper bound allows. Ordered as handing out the copies one at
/// a time, each to the binder of the copy before it or a later one, first
/// reaches them: most copies to the first binder first, then to the
/// second, and so on. When the bounds are not `exact`, another member may
/// meet a lower bound, so it requires nothing.
fn admissibleDistributions(
    self: anytype,
    item: ExprId,
    copies: u32,
    binder_lowers: []const std.ArrayListUnmanaged(ExprId),
    binder_uppers: []const std.ArrayListUnmanaged(ExprId),
    exact: bool,
) anyerror!MemberChoices {
    const binder_count = binder_lowers.len;
    const bounds = try self.allocator.alloc(u32, 3 * binder_count);
    defer self.allocator.free(bounds);
    const mins = bounds[0..binder_count];
    const maxes = bounds[binder_count .. 2 * binder_count];
    const current = bounds[2 * binder_count ..];
    for (binder_lowers, binder_uppers, mins, maxes) |lower, upper, *min, *max| {
        min.* = if (exact) try countCompatible(self, lower.items, item) else 0;
        max.* = @min(copies, try countCompatible(self, upper.items, item));
    }

    var counts = std.ArrayListUnmanaged(u32).empty;
    errdefer counts.deinit(self.allocator);
    try appendDistributions(self, &counts, mins, maxes, current, 0, copies);
    return .{
        .item = item,
        .binder_count = binder_count,
        .counts = try counts.toOwnedSlice(self.allocator),
    };
}

fn appendDistributions(
    self: anytype,
    out: *std.ArrayListUnmanaged(u32),
    mins: []const u32,
    maxes: []const u32,
    current: []u32,
    pos: usize,
    remaining: u32,
) !void {
    if (pos + 1 == current.len) {
        if (remaining < mins[pos] or remaining > maxes[pos]) return;
        current[pos] = remaining;
        try out.appendSlice(self.allocator, current);
        return;
    }
    var count = @min(maxes[pos], remaining) + 1;
    while (count > mins[pos]) {
        count -= 1;
        current[pos] = count;
        try appendDistributions(
            self,
            out,
            mins,
            maxes,
            current,
            pos + 1,
            remaining - count,
        );
    }
}

fn countCompatible(
    self: anytype,
    items: []const ExprId,
    item: ExprId,
) anyerror!u32 {
    var count: u32 = 0;
    for (items) |candidate| {
        if (try SemanticCompare.bindingCompatible(self, candidate, item)) {
            count += 1;
        }
    }
    return count;
}

/// Whether a member of the actual bag or of a binder's lower bound can be
/// `bindingCompatible` with a different member. Otherwise compatibility is
/// identity, so the multiset bounds count copies exactly. (A binder's upper
/// bound is its lower bound or the actual bag.)
fn boundsMeetOtherForms(
    self: anytype,
    items: []const ExprId,
    binder_lowers: []const std.ArrayListUnmanaged(ExprId),
) anyerror!bool {
    for (items) |item| {
        if (try meetsOtherForms(self, item)) return true;
    }
    for (binder_lowers) |lower| {
        for (lower.items) |item| {
            if (try meetsOtherForms(self, item)) return true;
        }
    }
    return false;
}

fn meetsOtherForms(self: anytype, item: ExprId) anyerror!bool {
    return try SemanticCompare.meetsOtherForms(
        self,
        try self.canonicalizer.canonicalize(item),
    );
}

/// Whether any constraint outside `obligation`'s own binder bounds can tell
/// two of its covers apart: another joint obligation over one of its
/// binders, or, in the view space, a binder that `propagateViewBindings`
/// maps onto the rule space, where the rule's own obligations still wait.
/// Bounds from intervals and existing bindings are already folded into the
/// per-member choices, so an uncoupled obligation's covers pass every later
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
/// minimum puts every member in its first smallest admissible placement —
/// and, for the ambiguity report, the number of covers and the first one
/// enumerated. Emits the first cover as the representative of every cover
/// but the chosen one, then the chosen cover, in enumeration order. When the
/// first cover is the chosen one (always under ACU, where every placement of
/// a member places all its copies), emits it, then the next cover as the
/// representative of the rest. Returns false if a representative was
/// rejected, in which case the caller falls back to enumerating.
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
    var first_is_minimal = true;
    for (choices) |member| {
        count *|= member.len();
        if (minimalPlacement(member) != 0) first_is_minimal = false;
    }
    if (first_is_minimal) {
        const before = out.items.len;
        try appendCover(
            self,
            state,
            space,
            obligation,
            profile,
            choices,
            .first,
            1,
            out,
        );
        if (out.items.len == before) return false;
        if (count == 1) return true;
        try appendCover(
            self,
            state,
            space,
            obligation,
            profile,
            choices,
            .next,
            count - 1,
            out,
        );
        return out.items.len != before + 1;
    }
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

/// `next` is the cover enumerated after the first: the last member with a
/// choice takes its second placement.
const CoverPick = enum { first, next, minimal };

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
    var last_choice: usize = 0;
    if (pick == .next) {
        for (choices, 0..) |member, pos| {
            if (member.len() > 1) last_choice = pos;
        }
    }
    for (choices, 0..) |member, pos| {
        const counts = member.placement(switch (pick) {
            .first => 0,
            .next => @intFromBool(pos == last_choice),
            .minimal => minimalPlacement(member),
        });
        try placeMember(self, binder_items, member.item, counts);
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

/// The index of the first placement placing the fewest copies, in
/// enumeration order.
fn minimalPlacement(member: MemberChoices) usize {
    var best: usize = 0;
    var best_size = placementSize(member.placement(0));
    for (1..member.len()) |idx| {
        const size = placementSize(member.placement(idx));
        if (size < best_size) {
            best = idx;
            best_size = size;
        }
    }
    return best;
}

fn placementSize(counts: []const u32) usize {
    var size: usize = 0;
    for (counts) |count| size += count;
    return size;
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
    for (0..member.len()) |idx| {
        const counts = member.placement(idx);
        try placeMember(self, binder_items, member.item, counts);
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
        unplaceMember(binder_items, counts);
    }
}

fn placeMember(
    self: anytype,
    binder_items: []std.ArrayListUnmanaged(ExprId),
    item: ExprId,
    counts: []const u32,
) !void {
    for (binder_items, counts) |*items, count| {
        try items.appendNTimes(self.allocator, item, count);
    }
}

fn unplaceMember(
    binder_items: []std.ArrayListUnmanaged(ExprId),
    counts: []const u32,
) void {
    for (binder_items, counts) |*items, count| {
        items.shrinkRetainingCapacity(items.items.len - count);
    }
}

fn collectBinderBounds(
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
    for (lists) |*items| items.* = .empty;
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
