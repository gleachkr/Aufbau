const MatchState = @import("../match_state.zig");

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
        .deferred_len = state.deferred.items.len,
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
    state.deferred.shrinkRetainingCapacity(snapshot.deferred_len);
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
