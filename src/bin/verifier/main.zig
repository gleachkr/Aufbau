const std = @import("std");

pub fn main(init: std.process.Init.Minimal) !void {
    return @import("./cli.zig").main(init);
}
