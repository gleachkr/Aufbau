const std = @import("std");
const build_options = @import("build_options");
const mm0 = @import("mm0");
const compiler_lsp = @import("./lsp.zig");
const DebugConfig = mm0.DebugConfig;

const CliError = error{
    InvalidUsage,
    Reported,
};

const usage_text =
    "Usage:\n" ++
    "  abc compile INPUT.mm0 INPUT.auf OUTPUT.mmb " ++
    "[--debug SYSTEMS] [-Werror] [--lang LANG]\n" ++
    "  abc lsp [--lang LANG]\n" ++
    "  abc [--help | --version]\n" ++
    "\nOptions:\n" ++
    "  -h, --help       Show this help and exit\n" ++
    "  -V, --version    Show the version and exit\n" ++
    "  --debug SYSTEMS  Enable debug output (comma-separated:\n" ++
    "                   " ++
    mm0.advertised_channel_list ++
    ")\n" ++
    "  -Werror          Treat compiler warnings as errors\n" ++
    "  --lang LANG      Diagnostic language (en, de); also read from\n" ++
    "                   the ABC_LANG environment variable\n";

const version_text = "abc " ++ build_options.version ++ "\n";

const CompilePaths = struct {
    input: []const u8,
    proof: []const u8,
    output: []const u8,
};

const CompileCommand = struct {
    paths: CompilePaths,
    debug: DebugConfig,
    warnings_as_errors: bool,
};

const Command = union(enum) {
    compile: CompileCommand,
    lsp,
    help,
    version,
};

fn writeToFile(file: std.fs.File, text: []const u8) !void {
    var buf: [1024]u8 = undefined;
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

fn appendPositionalArg(
    positional: *std.ArrayListUnmanaged([]const u8),
    arg: []const u8,
) !void {
    if (positional.items.len >= positional.capacity) {
        return CliError.InvalidUsage;
    }
    positional.appendAssumeCapacity(arg);
}

fn parseCompileArgs(argv: []const []const u8) !Command {
    var debug = DebugConfig.none;
    var warnings_as_errors = false;
    var positional = std.ArrayListUnmanaged([]const u8){};
    var buf: [64][]const u8 = undefined;
    positional.items = buf[0..0];
    positional.capacity = buf.len;

    var i: usize = 0;
    while (i < argv.len) : (i += 1) {
        if (std.mem.eql(u8, argv[i], "--debug")) {
            i += 1;
            if (i >= argv.len) return CliError.InvalidUsage;
            debug = DebugConfig.parse(argv[i]) catch {
                return CliError.InvalidUsage;
            };
        } else if (std.mem.eql(u8, argv[i], "-Werror")) {
            warnings_as_errors = true;
        } else {
            try appendPositionalArg(&positional, argv[i]);
        }
    }

    const pos = positional.items;
    if (pos.len != 4 or !std.mem.eql(u8, pos[0], "compile")) {
        return CliError.InvalidUsage;
    }

    return .{ .compile = .{
        .paths = .{
            .input = pos[1],
            .proof = pos[2],
            .output = pos[3],
        },
        .debug = debug,
        .warnings_as_errors = warnings_as_errors,
    } };
}

fn parseArgs(argv: []const []const u8) !Command {
    if (argv.len == 1) {
        const arg = argv[0];
        if (std.mem.eql(u8, arg, "lsp")) return .lsp;
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
    }
    return parseCompileArgs(argv);
}

fn reportFileError(action: []const u8, path: []const u8, err: anyerror) void {
    std.debug.print("abc: unable to {s} '{s}': {s}\n", .{
        action,
        path,
        @errorName(err),
    });
}

fn loadSource(
    allocator: std.mem.Allocator,
    path: []const u8,
) ![]u8 {
    return std.fs.cwd().readFileAlloc(
        allocator,
        path,
        std.math.maxInt(usize),
    ) catch |err| {
        reportFileError("read", path, err);
        return CliError.Reported;
    };
}

fn runCompile(
    allocator: std.mem.Allocator,
    cmd: CompileCommand,
) !void {
    const source = try loadSource(allocator, cmd.paths.input);
    defer allocator.free(source);

    const proof = try loadSource(allocator, cmd.paths.proof);
    defer allocator.free(proof);

    var compiler = mm0.Compiler.initWithProof(
        allocator,
        source,
        proof,
    );
    compiler.debug = cmd.debug;
    compiler.diagnostics.warnings_as_errors = cmd.warnings_as_errors;
    const mmb = compiler.compileMmb(allocator) catch |err| {
        const failed_path = if (compiler.diagnostics.last_diagnostic) |diag|
            switch (diag.source) {
                .proof => cmd.paths.proof,
                .mm0 => cmd.paths.input,
            }
        else
            cmd.paths.input;
        std.debug.print("abc: failed to compile '{s}'\n", .{failed_path});
        compiler.reportError(err);
        return CliError.Reported;
    };
    defer allocator.free(mmb);

    compiler.reportWarnings();

    std.fs.cwd().writeFile(.{
        .sub_path = cmd.paths.output,
        .data = mmb,
    }) catch |err| {
        reportFileError("write", cmd.paths.output, err);
        return CliError.Reported;
    };
}

const LangSplit = struct {
    rest: []const []const u8,
    lang: ?mm0.CompilerLang,
};

/// Strip `--lang XX` (valid before any command) out of the argument list
/// so the command parsers stay locale-agnostic.
fn splitLangArgs(
    argv: []const []const u8,
    buf: [][]const u8,
) !LangSplit {
    var lang: ?mm0.CompilerLang = null;
    var len: usize = 0;
    var i: usize = 0;
    while (i < argv.len) : (i += 1) {
        if (std.mem.eql(u8, argv[i], "--lang")) {
            i += 1;
            if (i >= argv.len) return CliError.InvalidUsage;
            lang = mm0.parseCompilerLang(argv[i]) orelse
                return CliError.InvalidUsage;
        } else {
            if (len >= buf.len) return CliError.InvalidUsage;
            buf[len] = argv[i];
            len += 1;
        }
    }
    return .{ .rest = buf[0..len], .lang = lang };
}

fn applyEnvLang(allocator: std.mem.Allocator) void {
    const value = std.process.getEnvVarOwned(allocator, "ABC_LANG") catch
        return;
    defer allocator.free(value);
    if (mm0.parseCompilerLang(value)) |lang| mm0.setCompilerLang(lang);
}

pub fn run(
    allocator: std.mem.Allocator,
    argv: []const []const u8,
) !void {
    var lang_buf: [64][]const u8 = undefined;
    const split = try splitLangArgs(argv, &lang_buf);
    if (split.lang) |lang| {
        mm0.setCompilerLang(lang);
    } else {
        applyEnvLang(allocator);
    }
    const cmd = try parseArgs(split.rest);
    switch (cmd) {
        .compile => |compile| try runCompile(allocator, compile),
        .lsp => try compiler_lsp.run(allocator),
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
            std.debug.print("abc: {s}\n", .{@errorName(err)});
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

test "help and version text identify the compiler" {
    try std.testing.expect(std.mem.startsWith(u8, usage_text, "Usage:\n"));
    try std.testing.expectEqualStrings(
        "abc " ++ build_options.version ++ "\n",
        version_text,
    );
}

test "parse compile command accepts maintained debug channels" {
    const cmd = try parseArgs(&.{
        "compile",
        "input.mm0",
        "proof.auf",
        "output.mmb",
        "--debug",
        "views,dependency",
    });
    switch (cmd) {
        .compile => |compile| {
            try std.testing.expectEqualStrings(
                "input.mm0",
                compile.paths.input,
            );
            try std.testing.expect(compile.debug.views);
            try std.testing.expect(compile.debug.dependency);
            try std.testing.expect(!compile.warnings_as_errors);
        },
        else => return error.TestUnexpectedCommand,
    }
}

test "parse compile command accepts aliases and Werror in any order" {
    const cmd = try parseArgs(&.{
        "--debug",
        "check,emission",
        "compile",
        "input.mm0",
        "proof.auf",
        "output.mmb",
        "-Werror",
    });
    switch (cmd) {
        .compile => |compile| {
            try std.testing.expect(compile.debug.boundary);
            try std.testing.expect(compile.debug.normalization);
            try std.testing.expect(compile.warnings_as_errors);
        },
        else => return error.TestUnexpectedCommand,
    }
}

test "split --lang out of the argument list" {
    var buf: [8][]const u8 = undefined;
    const split = try splitLangArgs(
        &.{ "compile", "--lang", "de", "a.mm0", "a.auf", "a.mmb" },
        &buf,
    );
    try std.testing.expectEqual(mm0.CompilerLang.de, split.lang.?);
    try std.testing.expectEqual(@as(usize, 4), split.rest.len);
    try std.testing.expectEqualStrings("a.mm0", split.rest[1]);

    const without = try splitLangArgs(&.{"lsp"}, &buf);
    try std.testing.expectEqual(@as(?mm0.CompilerLang, null), without.lang);

    try std.testing.expectError(
        CliError.InvalidUsage,
        splitLangArgs(&.{ "lsp", "--lang", "xx" }, &buf),
    );
    try std.testing.expectError(
        CliError.InvalidUsage,
        splitLangArgs(&.{ "lsp", "--lang" }, &buf),
    );
}

test "parse compile command rejects invalid debug flags" {
    try std.testing.expectError(
        CliError.InvalidUsage,
        parseArgs(&.{
            "compile",
            "input.mm0",
            "proof.auf",
            "output.mmb",
            "--debug",
            "wat",
        }),
    );
}
