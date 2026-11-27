comptime {
    _ = @import("./lsp_protocol_tests.zig");
    _ = @import("./lsp_actions_tests.zig");
    _ = @import("./lsp_holes_tests.zig");
    _ = @import("./lsp_navigation_tests.zig");
    _ = @import("./lsp_units_tests.zig");
    _ = @import("./lsp_stdio_tests.zig");
    _ = @import("./lsp_offsets_tests.zig");
    _ = @import("../diag_json.zig");
}
