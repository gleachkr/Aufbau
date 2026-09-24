const std = @import("std");

const WebPackageInstall = struct {
    source_dir: []const u8,
    package_name: []const u8,
};

const WEB_PACKAGE_INSTALLS = [_]WebPackageInstall{
    .{ .source_dir = "web/packages/compiler", .package_name = "compiler" },
    .{ .source_dir = "web/packages/verifier", .package_name = "verifier" },
    .{ .source_dir = "web/packages/lsp", .package_name = "lsp" },
    .{ .source_dir = "web/packages/editor", .package_name = "editor" },
};

const WebWasmInstall = struct {
    artifact: *std.Build.Step.Compile,
    package_name: []const u8,
    file_name: []const u8,
};

fn readProjectVersion(b: *std.Build) []const u8 {
    const contents = b.build_root.handle.readFileAlloc(
        b.allocator,
        "VERSION",
        64,
    ) catch |err| {
        std.debug.panic("unable to read VERSION: {s}", .{@errorName(err)});
    };
    const version = std.mem.trim(u8, contents, " \t\r\n");
    _ = std.SemanticVersion.parse(version) catch |err| {
        std.debug.panic("invalid VERSION: {s}", .{@errorName(err)});
    };
    return version;
}

/// The one roster of web-demo examples.  Each entry ships
/// `tests/proof_cases/{name}.{mm0,auf}` and is listed in the generated
/// `fixtures/manifest.json`, which is what the demo page builds its example
/// picker from — so adding an example is a single edit here.
const WebDemoFixture = struct {
    name: []const u8,
    /// Display name in the picker; defaults to `name`.
    label: ?[]const u8 = null,
};

const WEB_DEMO_FIXTURES = [_]WebDemoFixture{
    .{ .name = "hilbert" },
    .{ .name = "russell" },
    .{ .name = "tseitin" },
    .{ .name = "robinson" },
    .{ .name = "aristotle" },
    .{ .name = "peirce" },
    .{ .name = "gentzen" },
    .{ .name = "prawitz" },
    .{ .name = "barcan" },
    .{ .name = "prior" },
    .{ .name = "pnueli" },
    .{ .name = "barwise" },
    .{ .name = "loeb" },
    .{ .name = "church" },
    .{ .name = "leibniz" },
    .{ .name = "mac_lane", .label = "mac lane" },
    .{ .name = "martin_lof", .label = "martin-löf" },
    .{ .name = "peano" },
    .{ .name = "euclid" },
    .{ .name = "smullyan" },
    .{ .name = "zermelo" },
    .{ .name = "tait" },
    .{ .name = "pratt" },
    .{ .name = "hoare" },
    .{ .name = "diaconescu" },
    .{ .name = "herbrand" },
    .{ .name = "girard" },
    .{ .name = "reynolds" },
    .{ .name = "cardano" },
};

fn installWebPackageSet(
    b: *std.Build,
    step: *std.Build.Step,
    install_root: []const u8,
    compiler_wasm: *std.Build.Step.Compile,
    verifier_wasm: *std.Build.Step.Compile,
    lsp_server_wasm: *std.Build.Step.Compile,
) void {
    for (WEB_PACKAGE_INSTALLS) |pkg| {
        const install_pkg = b.addInstallDirectory(.{
            .source_dir = b.path(pkg.source_dir),
            .install_dir = .prefix,
            .install_subdir = b.fmt(
                "{s}/@aufbau/{s}",
                .{ install_root, pkg.package_name },
            ),
        });
        step.dependOn(&install_pkg.step);

        const install_license = b.addInstallFile(
            b.path("LICENSE"),
            b.fmt(
                "{s}/@aufbau/{s}/LICENSE",
                .{ install_root, pkg.package_name },
            ),
        );
        step.dependOn(&install_license.step);
    }

    const wasm_installs = [_]WebWasmInstall{
        .{
            .artifact = compiler_wasm,
            .package_name = "compiler",
            .file_name = "compiler.wasm",
        },
        .{
            .artifact = verifier_wasm,
            .package_name = "verifier",
            .file_name = "verifier.wasm",
        },
        .{
            .artifact = lsp_server_wasm,
            .package_name = "lsp",
            .file_name = "lsp.wasm",
        },
    };

    for (wasm_installs) |wasm| {
        const install_wasm = b.addInstallArtifact(wasm.artifact, .{
            .dest_dir = .{ .override = .prefix },
            .dest_sub_path = b.fmt(
                "{s}/@aufbau/{s}/{s}",
                .{ install_root, wasm.package_name, wasm.file_name },
            ),
        });
        step.dependOn(&install_wasm.step);

        // The wasm-hosting glue (instantiation, input/result buffers) is one
        // source shared by the three wasm packages, copied into each as a
        // private module so the packages stay independently installable.
        const install_host = b.addInstallFile(
            b.path("web/packages/shared/host.js"),
            b.fmt(
                "{s}/@aufbau/{s}/host.js",
                .{ install_root, wasm.package_name },
            ),
        );
        step.dependOn(&install_host.step);
    }
}

fn installWebDemoFixtures(b: *std.Build, step: *std.Build.Step) void {
    const install_web_assets = b.addInstallDirectory(.{
        .source_dir = b.path("web"),
        .install_dir = .prefix,
        .install_subdir = "web-demo",
    });
    step.dependOn(&install_web_assets.step);

    const install_web_fonts = b.addInstallDirectory(.{
        .source_dir = b.path("web/fonts"),
        .install_dir = .prefix,
        .install_subdir = "web-demo/fonts",
    });
    step.dependOn(&install_web_fonts.step);

    var manifest: std.ArrayList(u8) = .empty;
    manifest.append(b.allocator, '[') catch @panic("OOM");

    for (WEB_DEMO_FIXTURES, 0..) |fixture, index| {
        const install_mm0 = b.addInstallFile(
            b.path(b.fmt("tests/proof_cases/{s}.mm0", .{fixture.name})),
            b.fmt("web-demo/fixtures/{s}.mm0", .{fixture.name}),
        );
        step.dependOn(&install_mm0.step);

        const install_proof = b.addInstallFile(
            b.path(b.fmt("tests/proof_cases/{s}.auf", .{fixture.name})),
            b.fmt("web-demo/fixtures/{s}.auf", .{fixture.name}),
        );
        step.dependOn(&install_proof.step);

        // Names and labels are hand-written identifiers, so a plain quoted
        // form is enough — no JSON escaping is needed.
        manifest.print(b.allocator, "{s}{{\"name\":\"{s}\",\"label\":\"{s}\"}}", .{
            if (index == 0) "" else ",",
            fixture.name,
            fixture.label orelse fixture.name,
        }) catch @panic("OOM");
    }

    manifest.appendSlice(b.allocator, "]\n") catch @panic("OOM");

    const write_manifest = b.addWriteFiles();
    const manifest_file = write_manifest.add("manifest.json", manifest.items);
    const install_manifest = b.addInstallFile(
        manifest_file,
        "web-demo/fixtures/manifest.json",
    );
    step.dependOn(&install_manifest.step);
}

fn addSearchBuildOptions(
    b: *std.Build,
    module: *std.Build.Module,
    enable_search_timers: bool,
) void {
    const options = b.addOptions();
    options.addOption(bool, "enable_search_timers", enable_search_timers);
    module.addOptions("build_options", options);
}

pub fn build(b: *std.Build) void {
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});
    const project_version = readProjectVersion(b);
    const version_options = b.addOptions();
    version_options.addOption([]const u8, "version", project_version);
    const search_timers = b.option(
        bool,
        "search-timers",
        "Enable proof-search timing counters",
    ) orelse true;
    const lsp_dep = b.dependency("lsp_kit", .{
        .target = target,
        .optimize = optimize,
    });
    const lsp_module = lsp_dep.module("lsp");
    const lsp_types_module = lsp_dep.module("lsp-types");

    const mm0_lib = b.createModule(.{
        .root_source_file = b.path("src/lib.zig"),
        .target = target,
        .optimize = optimize,
    });
    addSearchBuildOptions(b, mm0_lib, search_timers);

    const lsp_diagnostics_module = b.createModule(.{
        .root_source_file = b.path("src/frontend/lsp/diagnostics.zig"),
        .target = target,
        .optimize = optimize,
    });
    lsp_diagnostics_module.addImport("mm0", mm0_lib);
    lsp_diagnostics_module.addImport("lsp", lsp_module);

    const wasm_target = b.resolveTargetQuery(.{
        .cpu_arch = .wasm32,
        .os_tag = .freestanding,
    });
    const lsp_offsets_wasm_module = b.createModule(.{
        .root_source_file = lsp_dep.path("src/offsets.zig"),
        .target = wasm_target,
        .optimize = optimize,
    });
    lsp_offsets_wasm_module.addImport("types", lsp_types_module);
    const lsp_wasm_module = b.createModule(.{
        .root_source_file = b.path("src/bin/compiler/lsp_wasm_compat.zig"),
        .target = wasm_target,
        .optimize = optimize,
    });
    lsp_wasm_module.addImport("types", lsp_types_module);
    lsp_wasm_module.addImport("offsets", lsp_offsets_wasm_module);
    const mm0_wasm_lib = b.createModule(.{
        .root_source_file = b.path("src/lib.zig"),
        .target = wasm_target,
        .optimize = optimize,
    });
    addSearchBuildOptions(b, mm0_wasm_lib, false);

    const lsp_diagnostics_wasm_module = b.createModule(.{
        .root_source_file = b.path("src/frontend/lsp/diagnostics.zig"),
        .target = wasm_target,
        .optimize = optimize,
    });
    lsp_diagnostics_wasm_module.addImport("mm0", mm0_wasm_lib);
    lsp_diagnostics_wasm_module.addImport("lsp", lsp_wasm_module);

    const verifier_module = b.createModule(.{
        .root_source_file = b.path("src/bin/verifier/main.zig"),
        .target = target,
        .optimize = optimize,
    });
    verifier_module.addImport("mm0", mm0_lib);
    verifier_module.addOptions("build_options", version_options);

    const verifier_exe = b.addExecutable(.{
        .name = "mm0-zig",
        .root_module = verifier_module,
    });
    b.installArtifact(verifier_exe);

    const compiler_module = b.createModule(.{
        .root_source_file = b.path("src/bin/compiler/main.zig"),
        .target = target,
        .optimize = optimize,
    });
    compiler_module.addImport("mm0", mm0_lib);
    compiler_module.addImport("lsp", lsp_module);
    compiler_module.addImport("lsp_diagnostics", lsp_diagnostics_module);
    compiler_module.addOptions("build_options", version_options);

    const compiler_exe = b.addExecutable(.{
        .name = "abc",
        .root_module = compiler_module,
    });
    b.installArtifact(compiler_exe);

    const compiler_wasm_module = b.createModule(.{
        .root_source_file = b.path("src/bin/compiler/wasm.zig"),
        .target = wasm_target,
        .optimize = optimize,
    });
    compiler_wasm_module.addImport("mm0", mm0_wasm_lib);

    const compiler_wasm = b.addExecutable(.{
        .name = "abc-web",
        .root_module = compiler_wasm_module,
    });
    compiler_wasm.entry = .disabled;
    compiler_wasm.rdynamic = true;
    compiler_wasm.export_memory = true;
    // The default wasm shadow stack is far smaller than a native thread
    // stack; the search's recursive descent overflows it into unrelated
    // linear memory (no guard page in wasm). Match a native 8 MiB stack.
    compiler_wasm.stack_size = 8 * 1024 * 1024;

    const verifier_wasm_module = b.createModule(.{
        .root_source_file = b.path("src/bin/verifier/wasm.zig"),
        .target = wasm_target,
        .optimize = optimize,
    });
    verifier_wasm_module.addImport("mm0", mm0_wasm_lib);

    const verifier_wasm = b.addExecutable(.{
        .name = "mm0-zig-web",
        .root_module = verifier_wasm_module,
    });
    verifier_wasm.entry = .disabled;
    verifier_wasm.rdynamic = true;
    verifier_wasm.export_memory = true;
    verifier_wasm.stack_size = 8 * 1024 * 1024;

    const lsp_server_wasm_module = b.createModule(.{
        .root_source_file = b.path("src/bin/compiler/lsp_wasm.zig"),
        .target = wasm_target,
        .optimize = optimize,
    });
    lsp_server_wasm_module.addImport("mm0", mm0_wasm_lib);
    lsp_server_wasm_module.addImport("lsp", lsp_wasm_module);
    lsp_server_wasm_module.addImport(
        "lsp_diagnostics",
        lsp_diagnostics_wasm_module,
    );
    lsp_server_wasm_module.addOptions("build_options", version_options);

    const lsp_server_wasm = b.addExecutable(.{
        .name = "abc-lsp-web",
        .root_module = lsp_server_wasm_module,
    });
    lsp_server_wasm.entry = .disabled;
    lsp_server_wasm.rdynamic = true;
    lsp_server_wasm.export_memory = true;
    lsp_server_wasm.stack_size = 8 * 1024 * 1024;

    const web_demo_step = b.step("web-demo", "Build the browser demo");
    const web_packages_step = b.step(
        "web-packages",
        "Build the redistributable JS/wasm packages",
    );

    installWebPackageSet(
        b,
        web_demo_step,
        "web-demo",
        compiler_wasm,
        verifier_wasm,
        lsp_server_wasm,
    );
    installWebPackageSet(
        b,
        web_packages_step,
        "npm",
        compiler_wasm,
        verifier_wasm,
        lsp_server_wasm,
    );
    installWebDemoFixtures(b, web_demo_step);

    const node_wasm_test_cmd = b.addSystemCommand(&.{"node"});
    node_wasm_test_cmd.addFileArg(b.path("tests/node_wasm_loading.mjs"));
    node_wasm_test_cmd.addArg(
        b.getInstallPath(.prefix, "npm/@aufbau"),
    );
    node_wasm_test_cmd.step.dependOn(web_packages_step);
    const node_wasm_test_step = b.step(
        "test-node-wasm",
        "Test packed npm WASM packages under Node",
    );
    node_wasm_test_step.dependOn(&node_wasm_test_cmd.step);

    const wasm_host_test_cmd = b.addSystemCommand(&.{"node"});
    wasm_host_test_cmd.addFileArg(b.path("tests/wasm_host_mock.mjs"));
    wasm_host_test_cmd.addArg(b.getInstallPath(.prefix, "npm/@aufbau"));
    wasm_host_test_cmd.step.dependOn(web_packages_step);
    const wasm_host_test_step = b.step(
        "test-wasm-host",
        "Test the packages' wasm hosting against mock instances",
    );
    wasm_host_test_step.dependOn(&wasm_host_test_cmd.step);

    const editor_browser_test_cmd = b.addSystemCommand(&.{"node"});
    editor_browser_test_cmd.addFileArg(
        b.path("tests/editor_browser_smoke.mjs"),
    );
    editor_browser_test_cmd.addArg(
        b.getInstallPath(.prefix, "npm/@aufbau"),
    );
    editor_browser_test_cmd.step.dependOn(web_packages_step);
    const editor_browser_test_step = b.step(
        "test-editor-browser",
        "Test the packed editor package in Chromium",
    );
    editor_browser_test_step.dependOn(&editor_browser_test_cmd.step);

    const lsp_cross_origin_test_cmd = b.addSystemCommand(&.{"node"});
    lsp_cross_origin_test_cmd.addFileArg(
        b.path("tests/lsp_cross_origin_worker.mjs"),
    );
    lsp_cross_origin_test_cmd.addArg(
        b.getInstallPath(.prefix, "npm/@aufbau"),
    );
    lsp_cross_origin_test_cmd.step.dependOn(web_packages_step);
    const lsp_cross_origin_test_step = b.step(
        "test-lsp-cross-origin",
        "Test the LSP worker transport across origins in Chromium",
    );
    lsp_cross_origin_test_step.dependOn(&lsp_cross_origin_test_cmd.step);

    const run_step = b.step("run", "Run the mm0-zig verifier");
    const run_cmd = b.addRunArtifact(verifier_exe);
    run_step.dependOn(&run_cmd.step);
    run_cmd.step.dependOn(b.getInstallStep());

    const run_compiler_step = b.step(
        "run-compiler",
        "Run the abc compiler",
    );
    const run_compiler_cmd = b.addRunArtifact(compiler_exe);
    run_compiler_step.dependOn(&run_compiler_cmd.step);
    run_compiler_cmd.step.dependOn(b.getInstallStep());

    if (b.args) |args| {
        run_cmd.addArgs(args);
        run_compiler_cmd.addArgs(args);
    }

    const trusted_test_module = b.createModule(.{
        .root_source_file = b.path("src/trusted/tests.zig"),
        .target = target,
        .optimize = optimize,
    });
    trusted_test_module.addImport("mm0", mm0_lib);

    const trusted_tests = b.addTest(.{
        .root_module = trusted_test_module,
    });
    const run_trusted_tests = b.addRunArtifact(trusted_tests);

    const root_test_module = b.createModule(.{
        .root_source_file = b.path("src/tests.zig"),
        .target = target,
        .optimize = optimize,
    });
    root_test_module.addImport("mm0", mm0_lib);

    const root_tests = b.addTest(.{
        .root_module = root_test_module,
    });
    const run_root_tests = b.addRunArtifact(root_tests);

    const frontend_test_module = b.createModule(.{
        .root_source_file = b.path("src/frontend/tests.zig"),
        .target = target,
        .optimize = optimize,
    });
    frontend_test_module.addImport("mm0", mm0_lib);

    const frontend_tests = b.addTest(.{
        .root_module = frontend_test_module,
    });
    const run_frontend_tests = b.addRunArtifact(frontend_tests);

    const lsp_index_test_module = b.createModule(.{
        .root_source_file = b.path("src/lsp_index_tests.zig"),
        .target = target,
        .optimize = optimize,
    });

    const lsp_index_tests = b.addTest(.{
        .root_module = lsp_index_test_module,
    });
    const run_lsp_index_tests = b.addRunArtifact(lsp_index_tests);

    const compiler_test_module = b.createModule(.{
        .root_source_file = b.path("src/frontend/compiler/tests.zig"),
        .target = target,
        .optimize = optimize,
    });
    compiler_test_module.addImport("mm0", mm0_lib);

    const compiler_tests = b.addTest(.{
        .root_module = compiler_test_module,
    });
    const run_compiler_tests = b.addRunArtifact(compiler_tests);

    const compiler_search_test_module = b.createModule(.{
        .root_source_file = b.path("src/search_tests.zig"),
        .target = target,
        .optimize = optimize,
    });
    addSearchBuildOptions(b, compiler_search_test_module, search_timers);

    const compiler_search_tests = b.addTest(.{
        .root_module = compiler_search_test_module,
    });
    const run_compiler_search_tests = b.addRunArtifact(
        compiler_search_tests,
    );

    const search_bench_module = b.createModule(.{
        .root_source_file = b.path("src/search_bench.zig"),
        .target = target,
        .optimize = optimize,
    });
    search_bench_module.addImport("mm0", mm0_lib);
    const search_bench_exe = b.addExecutable(.{
        .name = "search-bench",
        .root_module = search_bench_module,
    });
    const run_search_bench = b.addRunArtifact(search_bench_exe);
    if (b.args) |args| {
        run_search_bench.addArgs(args);
    }

    // Frontier regression guards (test-frontier-smoke); the table and its
    // rationale live in tests/frontier_guards.zig.
    const frontier_guards = @import("tests/frontier_guards.zig");
    const frontier_smoke_step = b.step(
        "test-frontier-smoke",
        "Regression guard: targeted breadth frontier lines must stay found",
    );
    for (frontier_guards.guards) |guard| {
        const run = b.addRunArtifact(search_bench_exe);
        run.addArgs(&.{
            b.fmt("--frontier={s}", .{guard.mode}),
            b.fmt("--files={s}", .{guard.files}),
            "--require-no-miss",
        });
        if (guard.filter) |needle| run.addArg(b.fmt("--filter={s}", .{needle}));
        if (guard.max_depth) |d| run.addArg(b.fmt("--max-depth={d}", .{d}));
        if (guard.gen_nodes) |n| run.addArg(b.fmt("--gen-nodes={d}", .{n}));
        if (guard.gen_fuel) |f| run.addArg(b.fmt("--gen-fuel={d}", .{f}));
        if (guard.global_budget) |g| run.addArg(b.fmt("--global-budget={d}", .{g}));
        if (guard.fwd_facts) |n| run.addArg(b.fmt("--fwd-facts={d}", .{n}));
        if (guard.fwd_attempts) |n| run.addArg(b.fmt("--fwd-attempts={d}", .{n}));
        if (guard.fwd_layers) |n| run.addArg(b.fmt("--fwd-layers={d}", .{n}));
        frontier_smoke_step.dependOn(&run.step);
    }

    const compiler_bin_test_module = b.createModule(.{
        .root_source_file = b.path("src/bin/compiler/tests.zig"),
        .target = target,
        .optimize = optimize,
    });
    compiler_bin_test_module.addImport("mm0", mm0_lib);
    compiler_bin_test_module.addImport("lsp", lsp_module);
    compiler_bin_test_module.addImport(
        "lsp_diagnostics",
        lsp_diagnostics_module,
    );
    compiler_bin_test_module.addOptions("build_options", version_options);

    const compiler_bin_tests = b.addTest(.{
        .root_module = compiler_bin_test_module,
    });
    const run_compiler_bin_tests = b.addRunArtifact(compiler_bin_tests);

    const verifier_bin_test_module = b.createModule(.{
        .root_source_file = b.path("src/bin/verifier/tests.zig"),
        .target = target,
        .optimize = optimize,
    });
    verifier_bin_test_module.addImport("mm0", mm0_lib);
    verifier_bin_test_module.addOptions("build_options", version_options);

    const verifier_bin_tests = b.addTest(.{
        .root_module = verifier_bin_test_module,
    });
    const run_verifier_bin_tests = b.addRunArtifact(verifier_bin_tests);

    const integration_test_module = b.createModule(.{
        .root_source_file = b.path("tests/integration_examples.zig"),
        .target = target,
        .optimize = optimize,
    });
    integration_test_module.addImport("mm0", mm0_lib);

    const integration_tests = b.addTest(.{
        .root_module = integration_test_module,
    });
    const run_integration_tests = b.addRunArtifact(integration_tests);

    const unit_step = b.step("test-unit", "Run unit tests");
    unit_step.dependOn(&run_trusted_tests.step);
    unit_step.dependOn(&run_root_tests.step);
    unit_step.dependOn(&run_frontend_tests.step);
    unit_step.dependOn(&run_lsp_index_tests.step);
    unit_step.dependOn(&run_compiler_tests.step);
    unit_step.dependOn(&run_compiler_search_tests.step);
    unit_step.dependOn(&run_compiler_bin_tests.step);
    unit_step.dependOn(&run_verifier_bin_tests.step);

    const cli_smoke_step = b.step(
        "test-cli",
        "Smoke-test native CLI help, version, and I/O errors",
    );

    const abc_usage_text =
        "Usage:\n" ++
        "  abc compile INPUT.mm0 INPUT.auf OUTPUT.mmb " ++
        "[--debug SYSTEMS] [-Werror] [--lang LANG]\n" ++
        "  abc join INPUT.mm0 [OUTPUT.mm0]\n" ++
        "  abc lsp [--lang LANG]\n" ++
        "  abc [--help | --version]\n" ++
        "\nOptions:\n" ++
        "  -h, --help       Show this help and exit\n" ++
        "  -V, --version    Show the version and exit\n" ++
        "  --debug SYSTEMS  Enable debug output (comma-separated:\n" ++
        "                   inference,views,dependency,freshen," ++
        "normalization,boundary,all)\n" ++
        "  -Werror          Treat compiler warnings as errors\n" ++
        "  --lang LANG      Diagnostic language (en, de); also read from\n" ++
        "                   the ABC_LANG environment variable\n" ++
        "\nExit status:\n" ++
        "  0  compiled\n" ++
        "  1  failed\n" ++
        "  3  compiled, but a proof line is admitted with sorry!\n";

    const abc_help = b.addRunArtifact(compiler_exe);
    abc_help.addArg("--help");
    abc_help.expectStdOutEqual(abc_usage_text);
    cli_smoke_step.dependOn(&abc_help.step);

    const abc_invalid = b.addRunArtifact(compiler_exe);
    abc_invalid.expectExitCode(1);
    abc_invalid.expectStdErrEqual(abc_usage_text);
    cli_smoke_step.dependOn(&abc_invalid.step);

    const abc_version = b.addRunArtifact(compiler_exe);
    abc_version.addArg("--version");
    abc_version.expectStdOutEqual(b.fmt("abc {s}\n", .{project_version}));
    cli_smoke_step.dependOn(&abc_version.step);

    const abc_missing = b.addRunArtifact(compiler_exe);
    abc_missing.addArgs(&.{
        "compile",
        "does-not-exist.mm0",
        "does-not-exist.auf",
        "unused.mmb",
    });
    abc_missing.expectExitCode(1);
    abc_missing.expectStdErrEqual(
        "abc: unable to read 'does-not-exist.mm0': FileNotFound\n",
    );
    cli_smoke_step.dependOn(&abc_missing.step);

    const verifier_usage_text =
        "Usage: mm0-zig [OPTIONS] FILE.mmb < FILE.mm0\n" ++
        "\nOptions:\n" ++
        "  -h, --help     Show this help and exit\n" ++
        "  -V, --version  Show the version and exit\n";

    const verifier_help = b.addRunArtifact(verifier_exe);
    verifier_help.addArg("--help");
    verifier_help.expectStdOutEqual(verifier_usage_text);
    cli_smoke_step.dependOn(&verifier_help.step);

    const verifier_invalid = b.addRunArtifact(verifier_exe);
    verifier_invalid.expectExitCode(1);
    verifier_invalid.expectStdErrEqual(verifier_usage_text);
    cli_smoke_step.dependOn(&verifier_invalid.step);

    const verifier_version = b.addRunArtifact(verifier_exe);
    verifier_version.addArg("--version");
    verifier_version.expectStdOutEqual(b.fmt(
        "mm0-zig {s}\n",
        .{project_version},
    ));
    cli_smoke_step.dependOn(&verifier_version.step);

    const verifier_missing = b.addRunArtifact(verifier_exe);
    verifier_missing.addArg("does-not-exist.mmb");
    verifier_missing.expectExitCode(1);
    verifier_missing.expectStdErrEqual(
        "mm0-zig: unable to read 'does-not-exist.mmb': FileNotFound\n",
    );
    cli_smoke_step.dependOn(&verifier_missing.step);

    unit_step.dependOn(cli_smoke_step);

    const integration_step = b.step(
        "test-integration",
        "Run integration tests against mm0 examples",
    );
    integration_step.dependOn(&run_integration_tests.step);

    const search_bench_step = b.step(
        "bench-search",
        "Run proof-search benchmark scenarios",
    );
    search_bench_step.dependOn(&run_search_bench.step);

    // Scenario regression guard wired into `zig build test`. The scenario bench
    // asserts each `expected_replacement` / `expected_suggestion_count` before
    // printing, so a stale expectation (e.g. a notation-rendering or capability
    // change that moves a suggestion) exits nonzero. Run in `--compact` mode so
    // the gate stays quiet; the full per-scenario counter dump is still
    // available via `zig build bench-search`. This guard exists because the
    // scenario expectations silently rotted across several committed changes
    // while only `bench-search` (a manual step) exercised them.
    const run_search_scenarios = b.addRunArtifact(search_bench_exe);
    run_search_scenarios.addArg("--compact");
    const search_scenarios_step = b.step(
        "test-search-scenarios",
        "Regression guard: proof-search scenario suggestions must stay current",
    );
    search_scenarios_step.dependOn(&run_search_scenarios.step);

    const test_step = b.step("test", "Run all tests");
    test_step.dependOn(unit_step);
    test_step.dependOn(integration_step);
    test_step.dependOn(frontier_smoke_step);
    test_step.dependOn(search_scenarios_step);
    test_step.dependOn(node_wasm_test_step);
    test_step.dependOn(wasm_host_test_step);
}
