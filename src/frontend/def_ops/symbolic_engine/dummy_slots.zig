const std = @import("std");
const ExprId = @import("../../expr.zig").ExprId;
const Types = @import("../types.zig");
const MatchState = @import("../match_state.zig");
const Root = @import("witness_state.zig");

const SymbolicDummyInfo = Types.SymbolicDummyInfo;
const MatchSession = MatchState.MatchSession;

const invalidateRepresentativeCaches = Root.invalidateRepresentativeCaches;
const currentWitnessExpr = Root.currentWitnessExpr;

pub fn slotForWitness(
    self: anytype,
    witness: ExprId,
    info: SymbolicDummyInfo,
    state: *MatchSession,
    witness_slots: *std.AutoHashMapUnmanaged(ExprId, usize),
) anyerror!usize {
    if (witness_slots.get(witness)) |slot| return slot;
    if (state.materialized_witness_slots.get(witness)) |slot| {
        try witness_slots.put(self.shared.allocator, witness, slot);
        return slot;
    }

    const slot = try state.addDummyInfo(self.shared.allocator, info);
    try witness_slots.put(self.shared.allocator, witness, slot);
    try state.putWitness(self.shared.allocator, slot, witness);
    try state.putProvisionalWitnessInfo(
        self.shared.allocator,
        witness,
        info,
    );
    invalidateRepresentativeCaches(state);
    return slot;
}

pub fn resolveDummySlot(
    slot: usize,
    state: *const MatchSession,
) anyerror!usize {
    if (slot >= state.symbolic_dummy_infos.items.len) {
        return error.UnknownDummyVar;
    }
    var current = slot;
    var steps: usize = 0;
    while (state.dummy_aliases.get(current)) |next| {
        if (next >= state.symbolic_dummy_infos.items.len) {
            return error.UnknownDummyVar;
        }
        current = next;
        steps += 1;
        if (steps > state.symbolic_dummy_infos.items.len) {
            return error.CyclicSymbolicDummyAlias;
        }
    }
    return current;
}

pub fn putWitnessForDummySlot(
    self: anytype,
    slot: usize,
    actual: ExprId,
    state: *MatchSession,
) anyerror!void {
    const root = try resolveDummySlot(slot, state);
    try state.putWitness(self.shared.allocator, root, actual);
    invalidateRepresentativeCaches(state);
}

pub fn alignDummySlots(
    self: anytype,
    lhs_slot: usize,
    rhs_slot: usize,
    state: *MatchSession,
) anyerror!bool {
    const lhs_root = try resolveDummySlot(lhs_slot, state);
    const rhs_root = try resolveDummySlot(rhs_slot, state);
    if (lhs_root == rhs_root) return true;

    const lhs_info = state.symbolic_dummy_infos.items[lhs_root];
    const rhs_info = state.symbolic_dummy_infos.items[rhs_root];
    if (!std.mem.eql(u8, lhs_info.sort_name, rhs_info.sort_name)) {
        return false;
    }
    if (lhs_info.bound != rhs_info.bound) {
        return false;
    }

    // After the cheap filters: this one scans every slot twice.
    if (try rootsMustStayDistinct(lhs_root, rhs_root, state)) return false;

    const lhs_witness = currentWitnessExpr(lhs_root, state);
    const rhs_witness = currentWitnessExpr(rhs_root, state);
    if (lhs_witness != null and rhs_witness != null and
        lhs_witness.? != rhs_witness.?)
    {
        return false;
    }

    // The merged slot must forbid the union of both expansions' argument
    // deps; a witness already in place has only been checked against its own
    // side's mask, so re-check it against the union before aliasing.
    const merged_forbidden =
        lhs_info.forbidden_deps | rhs_info.forbidden_deps;
    for ([2]?ExprId{ lhs_witness, rhs_witness }) |maybe_witness| {
        const witness = maybe_witness orelse continue;
        const deps = try Root.exprDeps(self, witness);
        if (deps & merged_forbidden != 0) return false;
        if (!try witnessRespectsDistinctness(lhs_root, witness, state) or
            !try witnessRespectsDistinctness(rhs_root, witness, state))
        {
            return false;
        }
    }

    const winner = if (lhs_witness != null)
        lhs_root
    else if (rhs_witness != null)
        rhs_root
    else if (lhs_root <= rhs_root)
        lhs_root
    else
        rhs_root;
    const loser = if (winner == lhs_root) rhs_root else lhs_root;

    if (state.witnesses.get(loser)) |existing| {
        if (state.witnesses.get(winner)) |winner_existing| {
            if (winner_existing != existing) return false;
        } else {
            try state.putWitness(self.shared.allocator, winner, existing);
        }
        try state.removeWitness(self.shared.allocator, loser);
    }
    if (state.materialized_witnesses.get(loser)) |existing| {
        if (state.materialized_witnesses.get(winner)) |winner_existing| {
            if (winner_existing != existing) return false;
        } else {
            try state.putMaterializedWitness(
                self.shared.allocator,
                winner,
                existing,
            );
            try state.putMaterializedWitnessSlot(
                self.shared.allocator,
                existing,
                winner,
            );
        }
        try state.removeMaterializedWitness(self.shared.allocator, loser);
    }

    try state.widenDummyForbiddenDeps(
        self.shared.allocator,
        winner,
        merged_forbidden,
    );
    try state.putDummyAlias(self.shared.allocator, loser, winner);
    invalidateRepresentativeCaches(state);
    return true;
}

/// Inspect the original slots, not just the union-find roots: a root can
/// stand for dummies from several expansions after valid cross-expansion
/// alignment. Merging it must not identify siblings indirectly.
fn rootsMustStayDistinct(
    lhs_root: usize,
    rhs_root: usize,
    state: *const MatchSession,
) anyerror!bool {
    for (state.symbolic_dummy_infos.items, 0..) |lhs_info, lhs_slot| {
        const group = lhs_info.distinct_group orelse continue;
        if (try resolveDummySlot(lhs_slot, state) != lhs_root) continue;
        for (state.symbolic_dummy_infos.items, 0..) |rhs_info, rhs_slot| {
            if (rhs_info.distinct_group != group) continue;
            if (try resolveDummySlot(rhs_slot, state) == rhs_root) {
                return true;
            }
        }
    }
    return false;
}

/// Reject `actual` as a witness for `root` when some other root already
/// holds it and the two must stay distinct. Driving the scan off the witness
/// maps (usually a handful of entries) rather than off every slot keeps the
/// common case cheap; `rootsMustStayDistinct` still scans all slots per
/// candidate conflict.
pub fn witnessRespectsDistinctness(
    root: usize,
    actual: ExprId,
    state: *const MatchSession,
) anyerror!bool {
    for ([_]Types.WitnessMap{
        state.witnesses,
        state.materialized_witnesses,
    }) |witnesses| {
        var it = witnesses.iterator();
        while (it.next()) |entry| {
            if (entry.value_ptr.* != actual) continue;
            const other = try resolveDummySlot(entry.key_ptr.*, state);
            if (other == root) continue;
            if (try rootsMustStayDistinct(root, other, state)) return false;
        }
    }
    return true;
}
