comptime {
    _ = @import("./tests/root.zig");
    _ = @import("./tests/fresh.zig");
    _ = @import("./frontend/pretty_print.zig");
    _ = @import("./frontend/text_util.zig");
    // Must be a same-module comptime import: the test runner only collects
    // test decls reachable from the root module, so the previous routing
    // through the mm0 module (`mm0.DefOpsTests` in frontend/tests.zig)
    // silently ran zero of the def_ops tests from the April 2026 test split
    // onward.
    _ = @import("./frontend/def_ops/tests/root.zig");
}
