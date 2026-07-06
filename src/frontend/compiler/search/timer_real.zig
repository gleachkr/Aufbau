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

pub fn nanoTimestamp() i128 {
    return std.time.nanoTimestamp();
}
