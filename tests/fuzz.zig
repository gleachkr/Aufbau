//! Fuzz test root. `zig build test` runs each target once on a fixed input
//! as a smoke check; `zig build fuzz --fuzz` fuzzes them. See
//! docs/fuzzing.md.
test {
    _ = @import("fuzz/harness.zig");
    _ = @import("fuzz/mutate.zig");
    _ = @import("fuzz/compile.zig");
    _ = @import("fuzz/kernel.zig");
    _ = @import("fuzz/lsp.zig");
    _ = @import("fuzz/search.zig");
    _ = @import("fuzz/shapes.zig");
    _ = @import("fuzz/theory.zig");
    _ = @import("fuzz/mmb_mutate.zig");
}
