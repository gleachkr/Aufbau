const std = @import("std");
const mm0 = @import("mm0");
const scenarios = @import("search_scenarios");

const Search = mm0.CompilerSupport.Search;

test "search scenarios return their expected suggestions" {
    const allocator = std.testing.allocator;
    var report: std.Io.Writer.Allocating = .init(allocator);
    defer report.deinit();
    var failed: usize = 0;
    for (&scenarios.scenarios) |*scenario| {
        var counters = Search.SearchCounters{};
        var suggestions = scenarios.run(allocator, std.testing.io, scenario, &counters) catch |err| {
            try report.writer.print("{s}: {s}\n", .{ scenario.name, @errorName(err) });
            failed += 1;
            continue;
        };
        defer suggestions.deinit();
        if (!try scenarios.check(scenario, suggestions.items, &counters, &report.writer)) failed += 1;
    }
    if (failed != 0) {
        std.debug.print("{d} of {d} search scenarios failed:\n{s}", .{
            failed,
            scenarios.scenarios.len,
            report.written(),
        });
        return error.SearchScenarioFailed;
    }
}
