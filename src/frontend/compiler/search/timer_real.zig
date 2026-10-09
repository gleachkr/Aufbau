const std = @import("std");

pub fn timestampIf(enabled: bool) i128 {
    if (!enabled) return 0;
    return nanoTimestamp();
}

pub fn elapsedSince(start: i128) u64 {
    const elapsed = nanoTimestamp() - start;
    if (elapsed <= 0) return 0;
    return @intCast(elapsed);
}

/// Profiling counters only, so this reads the clock through the debug `Io`
/// rather than threading the host's through every search entry point.
pub fn nanoTimestamp() i128 {
    return std.Io.Clock.awake.now(std.Options.debug_io).nanoseconds;
}
