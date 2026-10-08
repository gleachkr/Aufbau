comptime {
    _ = @import("./tests/root.zig");
    _ = @import("./tests/fresh.zig");
    _ = @import("./frontend/pretty_print.zig");
    _ = @import("./frontend/text_util.zig");
    _ = @import("./frontend/view_trace.zig");
    _ = @import("./frontend/compiler/check_memo.zig");
    // Files whose inline tests would otherwise run only because something
    // here happens to reference them (scripts/check-test-wiring.mjs).
    _ = @import("./frontend/acui_support.zig");
    _ = @import("./frontend/binding_validation.zig");
    _ = @import("./frontend/canonicalizer.zig");
    _ = @import("./frontend/checked_ir.zig");
    _ = @import("./frontend/debug.zig");
    _ = @import("./frontend/imports.zig");
    _ = @import("./frontend/compiler/emit.zig");
    _ = @import("./frontend/compiler/holes.zig");
    _ = @import("./frontend/compiler/check/checked_range.zig");
    _ = @import("./frontend/compiler/check/inline_hints.zig");
    _ = @import("./frontend/compiler/inference/meta_store.zig");
    _ = @import("./frontend/compiler/inference/open_terms.zig");
    _ = @import("./frontend/def_ops/mirror_support.zig");
    _ = @import("./frontend/normalizer/proof_emit.zig");
    // Must be a same-module comptime import: the test runner only collects
    // test decls reachable from the root module, so the previous routing
    // through the mm0 module (`mm0.DefOpsTests` in frontend/tests.zig)
    // silently ran zero of the def_ops tests from the April 2026 test split
    // onward.
    _ = @import("./frontend/def_ops/tests/root.zig");
}
