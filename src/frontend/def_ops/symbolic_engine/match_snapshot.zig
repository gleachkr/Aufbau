const MatchState = @import("../match_state.zig");
const Containers = @import("../../containers.zig");

const cloneMap = Containers.cloneMap;

const MatchSession = MatchState.MatchSession;
const MatchSnapshot = MatchState.MatchSnapshot;

pub fn saveMatchSnapshot(
    self: anytype,
    state: *MatchSession,
) anyerror!MatchSnapshot {
    _ = self;
    // Seals the session against untrailed writes: from here on, rollback
    // must be able to undo every mutation, so `seedBinding` becomes illegal.
    state.snapshotted = true;
    return .{
        .trail_len = state.trail.items.len,
        .dummy_info_len = state.symbolic_dummy_infos.items.len,
        .cache_generation = state.cache_generation,
    };
}

pub fn restoreMatchSnapshot(
    self: anytype,
    snapshot: *const MatchSnapshot,
    state: *MatchSession,
) anyerror!void {
    _ = self;
    state.unwindTrail(snapshot.trail_len);
    state.symbolic_dummy_infos.shrinkRetainingCapacity(
        snapshot.dummy_info_len,
    );
    // The representative caches are memoization keyed on binding/witness
    // state. They are cleared (and the generation bumped) on every such
    // mutation, so a moved generation means the current cache contents
    // were computed under state this rollback just discarded.
    if (state.cache_generation != snapshot.cache_generation) {
        state.transparent_representatives.clearRetainingCapacity();
        state.normalized_representatives.clearRetainingCapacity();
    }
}

pub fn deinitMatchSnapshot(
    self: anytype,
    snapshot: *MatchSnapshot,
) void {
    _ = self;
    _ = snapshot;
}

pub fn cloneRepresentativeState(
    self: anytype,
    source: *const MatchSession,
    binding_len: usize,
) anyerror!MatchSession {
    var clone = try MatchSession.init(self.shared.allocator, binding_len);
    errdefer clone.deinit(self.shared.allocator);

    clone.witnesses = try cloneMap(self.shared.allocator, source.witnesses);
    clone.materialized_witnesses =
        try cloneMap(self.shared.allocator, source.materialized_witnesses);
    clone.materialized_witness_slots =
        try cloneMap(self.shared.allocator, source.materialized_witness_slots);
    clone.dummy_aliases = try cloneMap(self.shared.allocator, source.dummy_aliases);
    clone.provisional_witness_infos =
        try cloneMap(
            self.shared.allocator,
            source.provisional_witness_infos,
        );
    clone.materialized_witness_infos =
        try cloneMap(
            self.shared.allocator,
            source.materialized_witness_infos,
        );
    try clone.symbolic_dummy_infos.appendSlice(
        self.shared.allocator,
        source.symbolic_dummy_infos.items,
    );
    return clone;
}
