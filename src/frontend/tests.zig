const mm0 = @import("mm0");

comptime {
    _ = @import("./tests/root.zig");
    _ = @import("./tests/unpack.zig");
    _ = mm0.DefOpsTests;
}
