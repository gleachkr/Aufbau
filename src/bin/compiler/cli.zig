const std = @import("std");
const build_options = @import("build_options");
const mm0 = @import("mm0");
const compiler_lsp = @import("./lsp.zig");
const writeFields = @import("./diag_json.zig").writeFields;
const DebugConfig = mm0.DebugConfig;
const SearchDriver = mm0.CompilerSupport.SearchDriver;
const SearchParam = mm0.CompilerSupport.Search.tunables.SearchParam;

const CliError = error{
    InvalidUsage,
    Reported,
    /// The output was written, but a proof line is admitted with
    /// `sorry!`; the build is not verified (exit status 3, as mm0-c).
    Sorry,
    /// `search` left a marker without a proof (exit status 4).
    Missed,
};

const usage_text =
    "Usage:\n" ++
    "  abc compile INPUT.mm0 INPUT.auf OUTPUT.mmb " ++
    "[--debug SYSTEMS] [-Werror] [--lang LANG]\n" ++
    "  abc search INPUT.mm0 INPUT.auf [--fill] [--json] [-v | -vv]\n" ++
    "             [--only THEOREM[:LABEL]] [--retry N] [--depth N] " ++
    "[--budget N]\n" ++
    "             [--lang LANG]\n" ++
    "  abc join INPUT.mm0 [OUTPUT.mm0]\n" ++
    "  abc lsp [--lang LANG]\n" ++
    "  abc [--help | --version]\n" ++
    "\nAn INPUT.auf of - reads standard input; an OUTPUT.mmb of - writes\n" ++
    "standard output.\n" ++
    "\nOptions:\n" ++
    "  -h, --help       Show this help and exit\n" ++
    "  -V, --version    Show the version and exit\n" ++
    "  --debug SYSTEMS  Enable debug output (comma-separated:\n" ++
    "                   " ++
    mm0.advertised_channel_list ++
    ")\n" ++
    "  -Werror          Treat compiler warnings as errors\n" ++
    "  --fill           Write INPUT.auf to standard output with every proof\n" ++
    "                   found put in place; the report goes to standard error\n" ++
    "  --json           Report each search marker as one line of JSON\n" ++
    "  -v, -vv          Report what each search cost; -vv adds why it\n" ++
    "                   missed and the rules it tried most\n" ++
    "  --only THEOREM[:LABEL]\n" ++
    "                   Search only the markers of THEOREM, or of its line\n" ++
    "                   LABEL\n" ++
    "  --retry N        Search a missed auto? again with the larger limits\n" ++
    "                   its report advises, up to N times\n" ++
    "  --depth N        Depth limit for each auto? that does not set its own\n" ++
    "  --budget N       Work budget for each search that does not set its own\n" ++
    "  --lang LANG      Diagnostic language (en, de); also read from\n" ++
    "                   the ABC_LANG environment variable\n" ++
    "\nExit status:\n" ++
    "  0  compiled, or found a proof for every search marker\n" ++
    "  1  failed\n" ++
    "  3  compiled, but a proof line is admitted with sorry!\n" ++
    "  4  searched, but a search marker has no proof\n";

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

const SearchCommand = struct {
    input: []const u8,
    proof: []const u8,
    fill: bool = false,
    json: bool = false,
    /// 0, or 1 for `-v` and 2 for `-vv`.
    verbosity: u2 = 0,
    only: ?SearchDriver.Only = null,
    retries: usize = 0,
    depth: ?u64 = null,
    budget: ?u64 = null,
};

const JoinCommand = struct {
    input: []const u8,
    /// Standard output when null.
    output: ?[]const u8,
};

const Command = union(enum) {
    compile: CompileCommand,
    search: SearchCommand,
    join: JoinCommand,
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

/// The value after the flag at `i.*`, which `i.*` then indexes.
fn flagValue(argv: []const []const u8, i: *usize) ![]const u8 {
    i.* += 1;
    if (i.* >= argv.len) return CliError.InvalidUsage;
    return argv[i.*];
}

fn flagNumber(argv: []const []const u8, i: *usize) !u64 {
    return std.fmt.parseInt(u64, try flagValue(argv, i), 10) catch
        CliError.InvalidUsage;
}

/// `THEOREM` or `THEOREM:LABEL`.
fn parseOnly(arg: []const u8) !SearchDriver.Only {
    var parts = std.mem.splitScalar(u8, arg, ':');
    const theorem = parts.first();
    const label = parts.next();
    if (theorem.len == 0 or parts.next() != null) return CliError.InvalidUsage;
    if (label) |name| if (name.len == 0) return CliError.InvalidUsage;
    return .{ .theorem = theorem, .label = label };
}

/// Read the `search` flag at `i.*` into `search`; false when `argv[i.*]`
/// is not one.
fn parseSearchFlag(
    argv: []const []const u8,
    i: *usize,
    search: *SearchCommand,
) !bool {
    const arg = argv[i.*];
    if (std.mem.eql(u8, arg, "--fill")) {
        search.fill = true;
    } else if (std.mem.eql(u8, arg, "--json")) {
        search.json = true;
    } else if (std.mem.eql(u8, arg, "-v")) {
        search.verbosity = @max(search.verbosity, 1);
    } else if (std.mem.eql(u8, arg, "-vv")) {
        search.verbosity = 2;
    } else if (std.mem.eql(u8, arg, "--only")) {
        search.only = try parseOnly(try flagValue(argv, i));
    } else if (std.mem.eql(u8, arg, "--retry")) {
        search.retries = try flagNumber(argv, i);
    } else if (std.mem.eql(u8, arg, "--depth")) {
        search.depth = try flagNumber(argv, i);
    } else if (std.mem.eql(u8, arg, "--budget")) {
        search.budget = try flagNumber(argv, i);
    } else return false;
    return true;
}

fn parseCompileArgs(argv: []const []const u8) !Command {
    var debug = DebugConfig.none;
    var warnings_as_errors = false;
    var search_flags = false;
    var search: SearchCommand = .{ .input = "", .proof = "" };
    var positional = std.ArrayListUnmanaged([]const u8){};
    var buf: [64][]const u8 = undefined;
    positional.items = buf[0..0];
    positional.capacity = buf.len;

    var i: usize = 0;
    while (i < argv.len) : (i += 1) {
        const arg = argv[i];
        if (std.mem.eql(u8, arg, "--debug")) {
            debug = DebugConfig.parse(try flagValue(argv, &i)) catch {
                return CliError.InvalidUsage;
            };
        } else if (std.mem.eql(u8, arg, "-Werror")) {
            warnings_as_errors = true;
        } else if (try parseSearchFlag(argv, &i, &search)) {
            search_flags = true;
        } else {
            try appendPositionalArg(&positional, arg);
        }
    }

    const pos = positional.items;
    if (pos.len >= 2 and std.mem.eql(u8, pos[0], "join")) {
        if (pos.len > 3 or warnings_as_errors or debug.any() or search_flags) {
            return CliError.InvalidUsage;
        }
        return .{ .join = .{
            .input = pos[1],
            .output = if (pos.len == 3) pos[2] else null,
        } };
    }
    if (pos.len >= 1 and std.mem.eql(u8, pos[0], "search")) {
        if (pos.len != 3 or warnings_as_errors or debug.any()) {
            return CliError.InvalidUsage;
        }
        search.input = pos[1];
        search.proof = pos[2];
        return .{ .search = search };
    }
    if (search_flags) return CliError.InvalidUsage;
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

fn reportLoadFailure(
    allocator: std.mem.Allocator,
    failure: ?mm0.Imports.LoadFailure,
    err: anyerror,
) void {
    const info = failure orelse {
        std.debug.print("abc: {s}\n", .{@errorName(err)});
        return;
    };
    const message = info.message(allocator) catch return;
    defer allocator.free(message);
    std.debug.print("abc: {s}\n", .{message});
    const join = switch (info) {
        .join => |join| join,
        .read => return,
    };
    const cwd = std.process.getCwdAlloc(allocator) catch "";
    defer if (cwd.len != 0) allocator.free(cwd);
    const pos = lineCol(join.file_text, join.span.start);
    std.debug.print("  --> {s}:{d}:{d}\n", .{
        mm0.Imports.displayPath(cwd, join.file_key),
        pos.line,
        pos.column,
    });
}

const LineCol = struct { line: usize, column: usize };

fn lineCol(text: []const u8, offset: usize) LineCol {
    var line: usize = 1;
    var column: usize = 1;
    for (text[0..@min(offset, text.len)]) |ch| {
        if (ch == '\n') {
            line += 1;
            column = 1;
        } else column += 1;
    }
    return .{ .line = line, .column = column };
}

fn runJoin(allocator: std.mem.Allocator, cmd: JoinCommand) !void {
    var arena = std.heap.ArenaAllocator.init(allocator);
    defer arena.deinit();

    var failure: ?mm0.Imports.LoadFailure = null;
    const pair = mm0.Imports.loadPair(
        arena.allocator(),
        cmd.input,
        null,
        &failure,
    ) catch |err| {
        reportLoadFailure(allocator, failure, err);
        return CliError.Reported;
    };

    if (cmd.output) |output| {
        std.fs.cwd().writeFile(.{
            .sub_path = output,
            .data = pair.mm0.text,
        }) catch |err| {
            reportFileError("write", output, err);
            return CliError.Reported;
        };
    } else {
        writeToFile(std.fs.File.stdout(), pair.mm0.text) catch |err| {
            reportFileError("write", "standard output", err);
            return CliError.Reported;
        };
    }
}

fn runCompile(
    allocator: std.mem.Allocator,
    cmd: CompileCommand,
) !void {
    var arena = std.heap.ArenaAllocator.init(allocator);
    defer arena.deinit();

    var failure: ?mm0.Imports.LoadFailure = null;
    const pair = mm0.Imports.loadPair(
        arena.allocator(),
        cmd.paths.input,
        cmd.paths.proof,
        &failure,
    ) catch |err| {
        reportLoadFailure(allocator, failure, err);
        return CliError.Reported;
    };

    var compiler = mm0.Compiler.initWithProof(
        allocator,
        pair.mm0.text,
        pair.proof.?.text,
    );
    compiler.debug = cmd.debug;
    compiler.diagnostics.warnings_as_errors = cmd.warnings_as_errors;
    compiler.diagnostics.setMapping(.mm0, pair.mm0_mapping);
    compiler.diagnostics.setMapping(.proof, pair.proof_mapping);
    const mmb = compiler.compileMmb(allocator) catch |err| {
        const failed_path = if (compiler.diagnostics.last_diagnostic) |diag|
            compiler.diagnostics.diagnosticFileLabel(diag) orelse
                switch (diag.source) {
                    .proof => cmd.paths.proof,
                    .mm0 => cmd.paths.input,
                }
        else
            cmd.paths.input;
        std.debug.print("abc: failed to compile '{s}'\n", .{
            if (std.mem.eql(u8, failed_path, mm0.Imports.stdin_path))
                mm0.Imports.stdin_label
            else
                failed_path,
        });
        compiler.reportError(err);
        return CliError.Reported;
    };
    defer allocator.free(mmb);

    compiler.reportWarnings();

    if (std.mem.eql(u8, cmd.paths.output, "-")) {
        writeToFile(std.fs.File.stdout(), mmb) catch |err| {
            reportFileError("write", "standard output", err);
            return CliError.Reported;
        };
    } else std.fs.cwd().writeFile(.{
        .sub_path = cmd.paths.output,
        .data = mmb,
    }) catch |err| {
        reportFileError("write", cmd.paths.output, err);
        return CliError.Reported;
    };

    for (compiler.warningDiagnostics()) |diag| {
        if (diag.err == error.SorryLine) return CliError.Sorry;
    }
}

fn runSearch(
    allocator: std.mem.Allocator,
    cmd: SearchCommand,
) !void {
    var arena = std.heap.ArenaAllocator.init(allocator);
    defer arena.deinit();

    const params = try searchParams(arena.allocator(), cmd);

    var failure: ?mm0.Imports.LoadFailure = null;
    const pair = mm0.Imports.loadPair(
        arena.allocator(),
        cmd.input,
        cmd.proof,
        &failure,
    ) catch |err| {
        reportLoadFailure(allocator, failure, err);
        return CliError.Reported;
    };
    const proof = pair.proof.?;
    const proof_mapping = pair.proof_mapping.?;

    // Errors elsewhere in the unit fail the run, but the markers are still
    // searched: the analysis around each one admits what it cannot check.
    var compiler = mm0.Compiler.initWithProof(
        allocator,
        pair.mm0.text,
        proof.text,
    );
    compiler.allow_search_placeholders = true;
    compiler.diagnostics.setMapping(.mm0, pair.mm0_mapping);
    compiler.diagnostics.setMapping(.proof, proof_mapping);
    compiler.analyze() catch |err| {
        if (err == error.OutOfMemory) return err;
        compiler.reportError(err);
        return CliError.Reported;
    };
    const errors = compiler.primaryDiagnostics();
    for (errors) |diag| compiler.diagnostics.reportDiagnostic(diag);
    for ([_]mm0.CompilerDiagnosticSource{ .mm0, .proof }) |source| {
        if (compiler.omittedPrimaryDiagnostic(source)) |omitted| {
            compiler.diagnostics.reportDiagnostic(omitted);
        }
    }

    var result = try SearchDriver.run(
        allocator,
        pair.mm0.text,
        proof.text,
        .{ .only = cmd.only, .retries = cmd.retries, .params = params },
    );
    defer result.deinit();
    if (cmd.only) |only| if (result.markers.len == 0) {
        std.debug.print("abc: no search marker matches --only {s}{s}{s}\n", .{
            only.theorem,
            if (only.label == null) "" else ":",
            only.label orelse "",
        });
        return CliError.Reported;
    };

    var buf: [4096]u8 = undefined;
    // With `--fill` the filled file takes standard output.
    var report = if (cmd.fill)
        std.fs.File.stderr().writer(&buf)
    else
        std.fs.File.stdout().writer(&buf);
    const failed = if (cmd.json)
        try writeSearchJson(&report.interface, proof_mapping, result.markers)
    else
        try writeSearchReport(
            &report.interface,
            proof_mapping,
            result.markers,
            cmd.verbosity,
        );
    try report.interface.flush();
    if (cmd.fill) try writeFilled(allocator, proof_mapping, result.markers);
    if (failed or errors.len != 0) return CliError.Reported;
    for (result.markers) |marker| {
        if (marker.outcome != .found) return CliError.Missed;
    }
}

const SearchMarker = SearchDriver.Marker;

/// `--depth` and `--budget` as `auto?` parameters. An out-of-range value
/// gets the message it would get in a proof file.
fn searchParams(arena: std.mem.Allocator, cmd: SearchCommand) ![]const SearchParam {
    const Search = mm0.CompilerSupport.Search;
    var params = std.ArrayListUnmanaged(SearchParam){};
    const flags = [_]struct { name: []const u8, value: ?u64 }{
        .{ .name = "depth", .value = cmd.depth },
        .{ .name = "budget", .value = cmd.budget },
    };
    for (flags) |flag| {
        const value = flag.value orelse continue;
        const nowhere: Search.Span = .{ .start = 0, .end = 0 };
        try params.append(arena, .{
            .name = flag.name,
            .name_span = nowhere,
            .value = value,
            .value_span = nowhere,
            .span = nowhere,
        });
    }
    const issues = try Search.tunables.validateSearchParams(arena, .auto, params.items);
    for (issues) |issue| std.debug.print("abc: {s}\n", .{issue.message});
    if (issues.len != 0) return CliError.Reported;
    return params.items;
}

/// Write the root proof file to standard output with each proof found in
/// it put in place. A proof found in another file is not written; a
/// warning names it.
fn writeFilled(
    allocator: std.mem.Allocator,
    mapping: mm0.Imports.Mapping,
    markers: []const SearchMarker,
) !void {
    // The root proof file is joined last.
    const root = mapping.files.len - 1;
    const root_text = mapping.files[root].text;
    const Edit = SearchDriver.Edit;
    var edits = std.ArrayListUnmanaged(Edit){};
    defer edits.deinit(allocator);
    for (markers) |marker| {
        const edit = marker.edit orelse continue;
        const hit = mapping.map.locateSpan(.{
            .start = edit.span.start,
            .end = edit.span.end,
        }) orelse continue;
        if (hit.file_index != root) {
            const pos = lineCol(mapping.files[hit.file_index].text, hit.span.start);
            std.debug.print(
                "abc: warning: {s}:{d}: a proof was found for {s} {s}, " ++
                    "but --fill writes only {s}\n",
                .{
                    mapping.labels[hit.file_index],
                    pos.line,
                    marker.theorem,
                    marker.label,
                    mapping.labels[root],
                },
            );
            continue;
        }
        try edits.append(allocator, .{
            .span = .{ .start = hit.span.start, .end = hit.span.end },
            .text = edit.text,
        });
        if (marker.filled_assertion) |filled| {
            const assertion = mapping.map.locateSpan(.{
                .start = filled.span.start,
                .end = filled.span.end,
            }) orelse continue;
            try edits.append(allocator, .{
                .span = .{ .start = assertion.span.start, .end = assertion.span.end },
                .text = filled.text,
            });
        }
    }
    var buf: [4096]u8 = undefined;
    var stdout = std.fs.File.stdout().writer(&buf);
    try SearchDriver.writeEdits(&stdout.interface, root_text, edits.items);
    try stdout.interface.flush();
}

/// Where a marker sits, for the report: its file's label and line.
const MarkerPlace = struct {
    label: []const u8,
    line: usize,
};

fn markerPlace(mapping: mm0.Imports.Mapping, marker: SearchMarker) ?MarkerPlace {
    const hit = mapping.locateSpan(.{
        .start = marker.span.start,
        .end = marker.span.end,
    }) orelse return null;
    return .{ .label = hit.label, .line = lineCol(hit.text, hit.span.start).line };
}

/// One record per marker, then a count; returns whether a search failed.
fn writeSearchReport(
    w: *std.Io.Writer,
    mapping: mm0.Imports.Mapping,
    markers: []const SearchMarker,
    verbosity: u2,
) !bool {
    var found: usize = 0;
    var missed: usize = 0;
    var candidates: usize = 0;
    var not_searched: usize = 0;
    var failed = false;
    for (markers) |marker| {
        if (markerPlace(mapping, marker)) |place| {
            try w.print("{s}:{d}", .{ place.label, place.line });
        } else try w.writeAll("?");
        try w.print("  {s} {s}  {s}  ", .{
            marker.theorem,
            marker.label,
            marker.kind.keyword(),
        });
        switch (marker.outcome) {
            .found => {
                found += 1;
                try w.writeAll("found");
            },
            .candidates => {
                candidates += 1;
                try w.writeAll("candidates");
            },
            .missed => {
                missed += 1;
                try w.writeAll("missed");
            },
            .cut_short => {
                missed += 1;
                try w.writeAll("missed (search cut short)");
            },
            .not_searched => {
                not_searched += 1;
                if (marker.blocked_by) |label| {
                    try w.print("not searched: {s} does not check", .{label});
                } else try w.writeAll("not searched");
            },
            .failed => {
                failed = true;
                try w.print("failed: {s}", .{@errorName(marker.failure.?)});
            },
        }
        switch (marker.rounds.len) {
            0 => try w.writeAll("\n"),
            1 => try w.writeAll(" after 1 retry\n"),
            else => |n| try w.print(" after {d} retries\n", .{n}),
        }
        for (marker.suggestions) |suggestion| {
            try writeIndented(w, suggestion);
        }
        for (marker.holes) |hole| {
            try w.print("  {s} := {s}\n", .{ hole.name, hole.value });
        }
        if (marker.retry) |retry| try w.print("  retry: {s}\n", .{retry});
        if (verbosity >= 1) {
            // Each round in turn: what it cost, and what it retried with.
            for (marker.rounds) |round| {
                try writeCost(w, round.cost);
                try w.print("  retried: {s}\n", .{round.retry});
            }
            switch (marker.outcome) {
                .not_searched, .failed => {},
                else => try writeCost(w, marker.cost),
            }
        }
        if (verbosity >= 2) try writeDetail(w, marker);
    }
    if (markers.len == 0) {
        try w.writeAll("no search markers\n");
    } else {
        try w.print("{d} found, {d} missed", .{ found, missed });
        if (candidates != 0) try w.print(", {d} with candidates", .{candidates});
        if (not_searched != 0) try w.print(", {d} not searched", .{not_searched});
        try w.writeAll("\n");
    }
    return failed;
}

/// `-v`: what a search cost, work ticks first, since they repeat from run
/// to run.
fn writeCost(w: *std.Io.Writer, cost: SearchDriver.Cost) !void {
    try w.writeAll("  cost: ");
    if (cost.phase != 0) try w.print("{d} ticks, ", .{cost.ticks});
    try w.print("{d} candidates, {f} ms wall", .{
        cost.candidates,
        Milliseconds{ .ns = cost.wall_ns },
    });
    if (cost.phase != 0) {
        try w.print(", depth {d} in {s}", .{
            cost.depth,
            mm0.CompilerSupport.Search.phaseName(cost.phase),
        });
    }
    try w.writeAll("\n");
}

/// A duration, in milliseconds to the microsecond: "12.345".
const Milliseconds = struct {
    ns: u64,

    pub fn format(self: Milliseconds, w: *std.Io.Writer) !void {
        try w.print("{d}.{d:0>3}", .{
            self.ns / std.time.ns_per_ms,
            (self.ns / std.time.ns_per_us) % 1000,
        });
    }

    pub fn jsonStringify(self: Milliseconds, jw: *std.json.Stringify) !void {
        try jw.print("{f}", .{self});
    }
};

/// `-vv`: why a search missed, and the rules it tried most.
fn writeDetail(w: *std.Io.Writer, marker: SearchMarker) !void {
    if (marker.detail) |detail| try w.print("  why: {s}\n", .{detail});
    if (marker.cost.rules.len == 0) return;
    try w.writeAll("  rules tried most:\n");
    for (marker.cost.rules) |rule| {
        try w.print("    {s}: {d} tried, {d} accepted, {d} rejected\n", .{
            rule.name,
            rule.attempts,
            rule.accepted,
            rule.rejected,
        });
    }
}

/// `--json`: one object per marker and line, with every field at every
/// verbosity; returns whether a search failed.
fn writeSearchJson(
    w: *std.Io.Writer,
    mapping: mm0.Imports.Mapping,
    markers: []const SearchMarker,
) !bool {
    var failed = false;
    for (markers) |marker| {
        if (marker.outcome == .failed) failed = true;
        const place = markerPlace(mapping, marker);
        var jw: std.json.Stringify = .{ .writer = w };
        try jw.beginObject();
        try writeFields(&jw, .{
            .file = if (place) |p| p.label else null,
            .line = if (place) |p| p.line else null,
            .theorem = marker.theorem,
            .label = marker.label,
            .kind = marker.kind.keyword(),
            .status = marker.outcome,
            .suggestions = marker.suggestions,
            .holes = marker.holes,
            .retry = marker.retry,
            .blocked_by = marker.blocked_by,
            .failure = marker.failure,
            .detail = marker.detail,
        });
        try writeCostFields(&jw, marker.cost);
        try jw.objectField("rounds");
        try jw.beginArray();
        for (marker.rounds) |round| {
            try jw.beginObject();
            try writeFields(&jw, .{ .status = round.outcome, .retry = round.retry });
            try writeCostFields(&jw, round.cost);
            try jw.endObject();
        }
        try jw.endArray();
        try jw.endObject();
        try w.writeByte('\n');
    }
    return failed;
}

fn writeCostFields(jw: *std.json.Stringify, cost: SearchDriver.Cost) !void {
    const ran = cost.phase != 0;
    try writeFields(jw, .{
        .ticks = cost.ticks,
        .candidates = cost.candidates,
        .wall_ms = Milliseconds{ .ns = cost.wall_ns },
        .depth = if (ran) cost.depth else null,
        .phase = if (ran) cost.phase else null,
        .phase_name = if (ran) mm0.CompilerSupport.Search.phaseName(cost.phase) else null,
        .rules = cost.rules,
    });
}

fn writeIndented(w: *std.Io.Writer, text: []const u8) !void {
    var lines = std.mem.splitScalar(u8, std.mem.trimRight(u8, text, "\n"), '\n');
    while (lines.next()) |line| try w.print("  {s}\n", .{line});
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
        .search => |search| try runSearch(allocator, search),
        .join => |join| try runJoin(allocator, join),
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
        CliError.Sorry => std.process.exit(3),
        CliError.Missed => std.process.exit(4),
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

test "parse join command" {
    const cmd = try parseArgs(&.{ "join", "a.mm0" });
    switch (cmd) {
        .join => |join| {
            try std.testing.expectEqualStrings("a.mm0", join.input);
            try std.testing.expect(join.output == null);
        },
        else => return error.TestUnexpectedCommand,
    }
    const with_output = try parseArgs(&.{ "join", "a.mm0", "out.mm0" });
    switch (with_output) {
        .join => |join| try std.testing.expectEqualStrings("out.mm0", join.output.?),
        else => return error.TestUnexpectedCommand,
    }
    try std.testing.expectError(CliError.InvalidUsage, parseArgs(&.{"join"}));
    try std.testing.expectError(
        CliError.InvalidUsage,
        parseArgs(&.{ "join", "a.mm0", "b.mm0", "c.mm0" }),
    );
    try std.testing.expectError(
        CliError.InvalidUsage,
        parseArgs(&.{ "join", "a.mm0", "-Werror" }),
    );
}

test "parse search command" {
    const cmd = try parseArgs(&.{ "search", "a.mm0", "a.auf" });
    switch (cmd) {
        .search => |search| {
            try std.testing.expectEqualStrings("a.mm0", search.input);
            try std.testing.expectEqualStrings("a.auf", search.proof);
        },
        else => return error.TestUnexpectedCommand,
    }
    try std.testing.expectError(
        CliError.InvalidUsage,
        parseArgs(&.{ "search", "a.mm0" }),
    );
    try std.testing.expectError(
        CliError.InvalidUsage,
        parseArgs(&.{ "search", "a.mm0", "a.auf", "-Werror" }),
    );
    const flagged = try parseArgs(&.{ "search", "-vv", "a.mm0", "--fill", "a.auf", "--json", "-v" });
    switch (flagged) {
        .search => |search| {
            try std.testing.expect(search.fill);
            try std.testing.expect(search.json);
            try std.testing.expectEqual(@as(u2, 2), search.verbosity);
        },
        else => return error.TestUnexpectedCommand,
    }
    try std.testing.expectError(
        CliError.InvalidUsage,
        parseArgs(&.{ "compile", "a.mm0", "a.auf", "a.mmb", "--fill" }),
    );
    try std.testing.expectError(
        CliError.InvalidUsage,
        parseArgs(&.{ "join", "a.mm0", "-v" }),
    );
}

test "parse search limits and --only" {
    const cmd = try parseArgs(&.{
        "search",  "a.mm0", "a.auf",   "--only", "thm:l2",
        "--retry", "3",     "--depth", "8",      "--budget",
        "0",
    });
    switch (cmd) {
        .search => |search| {
            try std.testing.expectEqualStrings("thm", search.only.?.theorem);
            try std.testing.expectEqualStrings("l2", search.only.?.label.?);
            try std.testing.expectEqual(@as(usize, 3), search.retries);
            try std.testing.expectEqual(@as(?u64, 8), search.depth);
            try std.testing.expectEqual(@as(?u64, 0), search.budget);
        },
        else => return error.TestUnexpectedCommand,
    }
    const theorem = try parseArgs(&.{ "search", "--only", "thm", "a.mm0", "a.auf" });
    try std.testing.expect(theorem.search.only.?.label == null);
    const bad = [_][]const []const u8{
        &.{ "search", "a.mm0", "a.auf", "--retry" },
        &.{ "search", "a.mm0", "a.auf", "--retry", "-1" },
        &.{ "search", "a.mm0", "a.auf", "--depth", "x" },
        &.{ "search", "a.mm0", "a.auf", "--only", ":l1" },
        &.{ "search", "a.mm0", "a.auf", "--only", "thm:" },
        &.{ "search", "a.mm0", "a.auf", "--only", "a:b:c" },
        &.{ "compile", "a.mm0", "a.auf", "a.mmb", "--retry", "1" },
    };
    for (bad) |args| {
        try std.testing.expectError(CliError.InvalidUsage, parseArgs(args));
    }
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
