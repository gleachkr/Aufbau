comptime {
    _ = @import("./tests/root.zig");
    _ = @import("./tests/fresh.zig");
    _ = @import("./frontend/pretty_print.zig");
    _ = @import("./frontend/text_util.zig");
    // Must be same-module comptime imports: the test runner only collects
    // test decls reachable from the root module, so the previous routing
    // through the mm0 module (`mm0.DefOpsTests` in frontend/tests.zig)
    // silently ran zero of the def_ops tests from the April 2026 test split
    // onward. Only the files below are wired in; the rest of
    // frontend/def_ops/tests/ (root.zig's imports) accumulated ~29 failures
    // while dark and awaits repair before it can be re-enabled.
    _ = @import("./frontend/def_ops/tests/directed_normalize.zig");
    _ = @import("./frontend/def_ops/tests/rewrite_application.zig");
}
