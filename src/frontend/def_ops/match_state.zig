const std = @import("std");
const Types = @import("./types.zig");
const ExprId = @import("../expr.zig").ExprId;

/// One undone-able mutation of a `MatchSession`. Each entry stores the
/// *previous* value for a key (or binding slot); `old == null` means the
/// key was absent, so undo removes it.
pub const TrailEntry = union(enum) {
    binding: struct { idx: usize, old: ?Types.BoundValue },
    witness: struct { key: usize, old: ?ExprId },
    materialized_witness: struct { key: usize, old: ?ExprId },
    materialized_witness_slot: struct { key: ExprId, old: ?usize },
    dummy_alias: struct { key: usize, old: ?usize },
    provisional_witness_info: struct { key: ExprId, old: ?Types.SymbolicDummyInfo },
    materialized_witness_info: struct { key: ExprId, old: ?Types.SymbolicDummyInfo },
    dummy_forbidden: struct { slot: usize, old: u55 },
};

pub const MatchSession = struct {
    /// Never write a slot directly: use `setBinding` (trailed) once matching
    /// has begun, or `seedBinding` while seeding a fresh session. Direct
    /// writes are invisible to snapshot rollback and to anything keyed on
    /// session state.
    bindings: []?Types.BoundValue,
    witnesses: Types.WitnessMap = .{},
    materialized_witnesses: Types.WitnessMap = .{},
    materialized_witness_slots: Types.WitnessSlotMap = .empty,
    dummy_aliases: Types.DummyAliasMap = .empty,
    provisional_witness_infos: Types.ProvisionalWitnessInfoMap = .empty,
    materialized_witness_infos: Types.MaterializedWitnessInfoMap = .empty,
    transparent_representatives: Types.RepresentativeCache = .empty,
    normalized_representatives: Types.RepresentativeCache = .empty,
    symbolic_dummy_infos: std.ArrayListUnmanaged(Types.SymbolicDummyInfo) = .{},
    /// Negative memo for `matchSymbolicToSymbolicState`: combined hash of
    /// (lhs, rhs, session state) for pairs already proven NOT to match under
    /// the current state. Mirrors the semantic-search `visited` dedup but for
    /// the inner unbudgeted bidirectional unfold matcher, which otherwise
    /// re-explores structurally-identical pairs exponentially. Rollback-safe:
    /// the key includes the state hash, so a restored state re-derives the
    /// same key and the cached "fails" verdict remains valid.
    sym_match_neg: std.AutoHashMapUnmanaged(u64, void) = .empty,
    /// Undo log enabling O(1) snapshots. Every mutation that can happen
    /// while a `MatchSnapshot` is live MUST go through the trailed helpers
    /// below; only the initial seeding of a fresh session (before any
    /// snapshot exists) may bypass the trail, and only via `seedBinding`,
    /// which asserts that.
    trail: std.ArrayListUnmanaged(TrailEntry) = .{},
    /// Set by `saveMatchSnapshot` on the first snapshot and never cleared.
    /// Once true, untrailed mutation (`seedBinding`) is illegal: a rollback
    /// could not undo it.
    snapshotted: bool = false,
    /// Bumped by `invalidateRepresentativeCaches`. Snapshots record it so
    /// restore knows whether the representative caches were invalidated
    /// (and thus hold post-save entries that the rollback makes stale).
    cache_generation: u64 = 0,

    pub fn init(
        allocator: std.mem.Allocator,
        binding_len: usize,
    ) !MatchSession {
        const bindings = try allocator.alloc(?Types.BoundValue, binding_len);
        @memset(bindings, null);
        return .{
            .bindings = bindings,
        };
    }

    pub fn deinit(
        self: *MatchSession,
        allocator: std.mem.Allocator,
    ) void {
        allocator.free(self.bindings);
        self.witnesses.deinit(allocator);
        self.materialized_witnesses.deinit(allocator);
        self.materialized_witness_slots.deinit(allocator);
        self.dummy_aliases.deinit(allocator);
        self.provisional_witness_infos.deinit(allocator);
        self.materialized_witness_infos.deinit(allocator);
        self.transparent_representatives.deinit(allocator);
        self.normalized_representatives.deinit(allocator);
        self.symbolic_dummy_infos.deinit(allocator);
        self.sym_match_neg.deinit(allocator);
        self.trail.deinit(allocator);
    }

    pub fn setBinding(
        self: *MatchSession,
        allocator: std.mem.Allocator,
        idx: usize,
        value: ?Types.BoundValue,
    ) !void {
        try self.trail.append(allocator, .{ .binding = .{
            .idx = idx,
            .old = self.bindings[idx],
        } });
        self.bindings[idx] = value;
    }

    /// Untrailed binding write, for seeding a session before matching
    /// begins. Legal only while no `MatchSnapshot` has been taken: a
    /// snapshot taken after seeding can never unwind past these writes, so
    /// they need no trail entry. (Seeding itself may trail witness and
    /// dummy-info entries through `rebuildBoundValue` — the invariant is on
    /// snapshots, not on the trail being empty.) After the first snapshot,
    /// all binding mutation must go through `setBinding`.
    ///
    /// Anything keyed on session state (hashes, version counters) must
    /// treat seeding as part of session identity; this helper and
    /// `setBinding` are the only two binding-write funnels.
    pub fn seedBinding(
        self: *MatchSession,
        idx: usize,
        value: ?Types.BoundValue,
    ) void {
        std.debug.assert(!self.snapshotted);
        self.bindings[idx] = value;
    }

    /// Append a dummy-info record and return its slot. The list is
    /// append-only; snapshots roll it back by length
    /// (`MatchSnapshot.dummy_info_len`), so no trail entry is needed.
    pub fn addDummyInfo(
        self: *MatchSession,
        allocator: std.mem.Allocator,
        info: Types.SymbolicDummyInfo,
    ) !usize {
        const slot = self.symbolic_dummy_infos.items.len;
        try self.symbolic_dummy_infos.append(allocator, info);
        return slot;
    }

    pub fn putWitness(
        self: *MatchSession,
        allocator: std.mem.Allocator,
        key: usize,
        value: ExprId,
    ) !void {
        try self.trail.ensureUnusedCapacity(allocator, 1);
        const old = try self.witnesses.fetchPut(allocator, key, value);
        self.trail.appendAssumeCapacity(.{ .witness = .{
            .key = key,
            .old = if (old) |kv| kv.value else null,
        } });
    }

    pub fn removeWitness(
        self: *MatchSession,
        allocator: std.mem.Allocator,
        key: usize,
    ) !void {
        if (!self.witnesses.contains(key)) return;
        try self.trail.ensureUnusedCapacity(allocator, 1);
        const old = self.witnesses.fetchRemove(key).?;
        self.trail.appendAssumeCapacity(.{ .witness = .{
            .key = key,
            .old = old.value,
        } });
    }

    pub fn putMaterializedWitness(
        self: *MatchSession,
        allocator: std.mem.Allocator,
        key: usize,
        value: ExprId,
    ) !void {
        try self.trail.ensureUnusedCapacity(allocator, 1);
        const old = try self.materialized_witnesses.fetchPut(allocator, key, value);
        self.trail.appendAssumeCapacity(.{ .materialized_witness = .{
            .key = key,
            .old = if (old) |kv| kv.value else null,
        } });
    }

    pub fn removeMaterializedWitness(
        self: *MatchSession,
        allocator: std.mem.Allocator,
        key: usize,
    ) !void {
        if (!self.materialized_witnesses.contains(key)) return;
        try self.trail.ensureUnusedCapacity(allocator, 1);
        const old = self.materialized_witnesses.fetchRemove(key).?;
        self.trail.appendAssumeCapacity(.{ .materialized_witness = .{
            .key = key,
            .old = old.value,
        } });
    }

    pub fn putMaterializedWitnessSlot(
        self: *MatchSession,
        allocator: std.mem.Allocator,
        key: ExprId,
        value: usize,
    ) !void {
        try self.trail.ensureUnusedCapacity(allocator, 1);
        const old = try self.materialized_witness_slots.fetchPut(allocator, key, value);
        self.trail.appendAssumeCapacity(.{ .materialized_witness_slot = .{
            .key = key,
            .old = if (old) |kv| kv.value else null,
        } });
    }

    pub fn putDummyAlias(
        self: *MatchSession,
        allocator: std.mem.Allocator,
        key: usize,
        value: usize,
    ) !void {
        try self.trail.ensureUnusedCapacity(allocator, 1);
        const old = try self.dummy_aliases.fetchPut(allocator, key, value);
        self.trail.appendAssumeCapacity(.{ .dummy_alias = .{
            .key = key,
            .old = if (old) |kv| kv.value else null,
        } });
    }

    pub fn putProvisionalWitnessInfo(
        self: *MatchSession,
        allocator: std.mem.Allocator,
        key: ExprId,
        value: Types.SymbolicDummyInfo,
    ) !void {
        try self.trail.ensureUnusedCapacity(allocator, 1);
        const old = try self.provisional_witness_infos.fetchPut(allocator, key, value);
        self.trail.appendAssumeCapacity(.{ .provisional_witness_info = .{
            .key = key,
            .old = if (old) |kv| kv.value else null,
        } });
    }

    pub fn putMaterializedWitnessInfo(
        self: *MatchSession,
        allocator: std.mem.Allocator,
        key: ExprId,
        value: Types.SymbolicDummyInfo,
    ) !void {
        try self.trail.ensureUnusedCapacity(allocator, 1);
        const old = try self.materialized_witness_infos.fetchPut(allocator, key, value);
        self.trail.appendAssumeCapacity(.{ .materialized_witness_info = .{
            .key = key,
            .old = if (old) |kv| kv.value else null,
        } });
    }

    /// Widen a dummy slot's capture mask in place, trailed. Used when two
    /// dummy slots are aliased (`alignDummySlots`): the surviving root must
    /// forbid the union of both expansions' argument deps. In-place mutation
    /// of a surviving entry is otherwise illegal (snapshots roll the list
    /// back by length only), hence the trail entry.
    pub fn widenDummyForbiddenDeps(
        self: *MatchSession,
        allocator: std.mem.Allocator,
        slot: usize,
        merged: u55,
    ) !void {
        const info = &self.symbolic_dummy_infos.items[slot];
        if (info.forbidden_deps == merged) return;
        try self.trail.append(allocator, .{ .dummy_forbidden = .{
            .slot = slot,
            .old = info.forbidden_deps,
        } });
        info.forbidden_deps = merged;
    }

    /// Undo all mutations past `trail_len`, most recent first.
    ///
    /// Map restoration is intentionally infallible. The trail is unwound in
    /// strict LIFO order, and none of these maps shrink during matching. When
    /// undo re-inserts an old value, the matching remove or insert has already
    /// freed the required slot, so `putAssumeCapacity` is the checked form of
    /// that invariant.
    pub fn unwindTrail(
        self: *MatchSession,
        trail_len: usize,
    ) void {
        std.debug.assert(self.trail.items.len >= trail_len);
        while (self.trail.items.len > trail_len) {
            const entry = self.trail.pop().?;
            switch (entry) {
                .binding => |e| self.bindings[e.idx] = e.old,
                .witness => |e| if (e.old) |old| {
                    self.witnesses.putAssumeCapacity(e.key, old);
                } else {
                    _ = self.witnesses.remove(e.key);
                },
                .materialized_witness => |e| if (e.old) |old| {
                    self.materialized_witnesses.putAssumeCapacity(e.key, old);
                } else {
                    _ = self.materialized_witnesses.remove(e.key);
                },
                .materialized_witness_slot => |e| if (e.old) |old| {
                    self.materialized_witness_slots.putAssumeCapacity(e.key, old);
                } else {
                    _ = self.materialized_witness_slots.remove(e.key);
                },
                .dummy_alias => |e| if (e.old) |old| {
                    self.dummy_aliases.putAssumeCapacity(e.key, old);
                } else {
                    _ = self.dummy_aliases.remove(e.key);
                },
                .provisional_witness_info => |e| if (e.old) |old| {
                    self.provisional_witness_infos.putAssumeCapacity(e.key, old);
                } else {
                    _ = self.provisional_witness_infos.remove(e.key);
                },
                .materialized_witness_info => |e| if (e.old) |old| {
                    self.materialized_witness_infos.putAssumeCapacity(e.key, old);
                } else {
                    _ = self.materialized_witness_infos.remove(e.key);
                },
                // The slot is still in bounds here: snapshot restore unwinds
                // the trail before truncating `symbolic_dummy_infos`.
                .dummy_forbidden => |e| {
                    self.symbolic_dummy_infos.items[e.slot].forbidden_deps =
                        e.old;
                },
            }
        }
    }
};

/// O(1) savepoint: positions in the session's undo structures plus the
/// cache generation at save time. Restoring replays the trail backwards;
/// it does NOT deep-copy any session state.
pub const MatchSnapshot = struct {
    trail_len: usize,
    dummy_info_len: usize,
    cache_generation: u64,
};
