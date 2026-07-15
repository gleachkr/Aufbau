const std = @import("std");
const build_options = @import("build_options");
const mm0 = @import("mm0");

const CliError = error{
    InvalidUsage,
    Reported,
};

const usage_text =
    "Usage: mm0-zig [OPTIONS] FILE.mmb < FILE.mm0\n" ++
    "\nOptions:\n" ++
    "  -h, --help     Show this help and exit\n" ++
    "  -V, --version  Show the version and exit\n";

const version_text = "mm0-zig " ++ build_options.version ++ "\n";

const Command = union(enum) {
    verify: []const u8,
    help,
    version,
};

fn writeToFile(file: std.fs.File, text: []const u8) !void {
    var buf: [512]u8 = undefined;
    var w = file.writer(&buf);
    try w.interface.writeAll(text);
    try w.interface.flush();
}

pub fn usage() !void {
    try writeToFile(std.fs.File.stdout(), usage_text);
}

fn usageError() !void {
    try writeToFile(std.fs.File.stderr(), usage_text);
}

fn version() !void {
    try writeToFile(std.fs.File.stdout(), version_text);
}

fn parseArgs(argv: []const []const u8) !Command {
    if (argv.len != 1) return CliError.InvalidUsage;

    const arg = argv[0];
    if (std.mem.eql(u8, arg, "-h") or
        std.mem.eql(u8, arg, "--help"))
    {
        return .help;
    }
    if (std.mem.eql(u8, arg, "-V") or
        std.mem.eql(u8, arg, "--version"))
    {
        return .version;
    }
    if (std.mem.startsWith(u8, arg, "-")) {
        return CliError.InvalidUsage;
    }
    return .{ .verify = arg };
}

fn reportFileError(action: []const u8, path: []const u8, err: anyerror) void {
    std.debug.print("mm0-zig: unable to {s} '{s}': {s}\n", .{
        action,
        path,
        @errorName(err),
    });
}

fn runVerify(allocator: std.mem.Allocator, mmb_path: []const u8) !void {
    const cwd = std.fs.cwd();

    const mmb_bytes = cwd.readFileAllocOptions(
        allocator,
        mmb_path,
        std.math.maxInt(usize),
        null,
        std.mem.Alignment.of(mm0.Arg),
        null,
    ) catch |err| {
        reportFileError("read", mmb_path, err);
        return CliError.Reported;
    };
    defer allocator.free(mmb_bytes);

    const mm0_src = std.fs.File.readToEndAlloc(
        std.fs.File.stdin(),
        allocator,
        std.math.maxInt(usize),
    ) catch |err| {
        std.debug.print("mm0-zig: unable to read standard input: {s}\n", .{
            @errorName(err),
        });
        return CliError.Reported;
    };
    defer allocator.free(mm0_src);

    const parsed = mm0.Mmb.parse(allocator, mmb_bytes) catch |err| {
        std.debug.print("mm0-zig: failed to parse '{s}': {s}\n", .{
            mmb_path,
            @errorName(err),
        });
        return CliError.Reported;
    };

    var session = mm0.VerificationSession.initParsed(
        allocator,
        mm0_src,
        parsed,
    ) catch |err| {
        std.debug.print("mm0-zig: failed to prepare verification: {s}\n", .{
            @errorName(err),
        });
        return CliError.Reported;
    };
    defer session.deinit();

    session.verify() catch |err| {
        session.verifier.reportError(err);
        return CliError.Reported;
    };

    try writeToFile(
        std.fs.File.stdout(),
        "Verification successful!\n",
    );
}

pub fn run(
    allocator: std.mem.Allocator,
    argv: []const []const u8,
) !void {
    switch (try parseArgs(argv)) {
        .verify => |mmb_path| try runVerify(allocator, mmb_path),
        .help => try usage(),
        .version => try version(),
    }
}

pub fn main() !void {
    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    defer _ = gpa.deinit();
    const allocator = gpa.allocator();

    const args = try std.process.argsAlloc(allocator);
    defer std.process.argsFree(allocator, args);

    run(allocator, args[1..]) catch |err| switch (err) {
        CliError.InvalidUsage => {
            usageError() catch {};
            std.process.exit(1);
        },
        CliError.Reported => std.process.exit(1),
        else => {
            std.debug.print("mm0-zig: {s}\n", .{@errorName(err)});
            std.process.exit(1);
        },
    };
}

test "parse help and version commands" {
    const help_args = [_][]const u8{ "-h", "--help" };
    for (help_args) |arg| {
        try std.testing.expectEqual(.help, try parseArgs(&.{arg}));
    }
    const version_args = [_][]const u8{ "-V", "--version" };
    for (version_args) |arg| {
        try std.testing.expectEqual(.version, try parseArgs(&.{arg}));
    }
}

test "parse verifier input and reject unknown options" {
    const command = try parseArgs(&.{"proof.mmb"});
    switch (command) {
        .verify => |path| try std.testing.expectEqualStrings(
            "proof.mmb",
            path,
        ),
        else => return error.TestUnexpectedCommand,
    }
    try std.testing.expectError(
        CliError.InvalidUsage,
        parseArgs(&.{"--wat"}),
    );
}

test "help and version text identify the verifier" {
    try std.testing.expect(std.mem.startsWith(u8, usage_text, "Usage:"));
    try std.testing.expectEqualStrings(
        "mm0-zig " ++ build_options.version ++ "\n",
        version_text,
    );
}
