const build_options = @import("build_options");

const impl = if (build_options.enable_search_timers)
    @import("./timer_real.zig")
else
    @import("./timer_disabled.zig");

pub const timestampIf = impl.timestampIf;
pub const elapsedSince = impl.elapsedSince;
pub const nanoTimestamp = impl.nanoTimestamp;
