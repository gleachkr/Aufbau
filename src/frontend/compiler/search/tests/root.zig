//! Aggregator for the search test suite, split by subsystem (task #230).
//! Shared fixtures live in helpers.zig; each topic file is self-contained
//! beyond that.

comptime {
    _ = @import("./source_tests.zig");
    _ = @import("./auto_tests.zig");
    _ = @import("./apply_tests.zig");
    _ = @import("./prune_tests.zig");
    _ = @import("./forward_tests.zig");
    _ = @import("./tunables_tests.zig");
    _ = @import("./conversion_tests.zig");
    _ = @import("./compute_tests.zig");
    _ = @import("./conversion_defs_tests.zig");
    _ = @import("./alpha_tests.zig");
}
