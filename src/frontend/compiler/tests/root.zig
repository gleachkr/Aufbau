//! Aggregator for the compiler test suite, split by subsystem (task #230).
//! Shared fixtures live in helpers.zig; each topic file is self-contained
//! beyond that.

comptime {
    _ = @import("./annotation_tests.zig");
    _ = @import("./statement_tests.zig");
    _ = @import("./proof_tests.zig");
    _ = @import("./diagnostic_tests.zig");
    _ = @import("./inference_tests.zig");
    _ = @import("./normalization_tests.zig");
    _ = @import("./analyze_tests.zig");
}
