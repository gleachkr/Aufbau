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

const WEB_DEMO_FIXTURES = [_][]const u8{
    "hilbert",
    "russell",
    "tseitin",
    "robinson",
    "aristotle",
    "peirce",
    "gentzen",
    "prawitz",
    "barcan",
    "prior",
    "pnueli",
    "barwise",
    "loeb",
    "church",
    "leibniz",
    "mac_lane",
    "martin_lof",
    "peano",
    "euclid",
    "smullyan",
    "zermelo",
    "tait",
    "pratt",
    "hoare",
    "diaconescu",
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

    for (WEB_DEMO_FIXTURES) |fixture| {
        const install_mm0 = b.addInstallFile(
            b.path(b.fmt("tests/proof_cases/{s}.mm0", .{fixture})),
            b.fmt("web-demo/fixtures/{s}.mm0", .{fixture}),
        );
        step.dependOn(&install_mm0.step);

        const install_proof = b.addInstallFile(
            b.path(b.fmt("tests/proof_cases/{s}.auf", .{fixture})),
            b.fmt("web-demo/fixtures/{s}.auf", .{fixture}),
        );
        step.dependOn(&install_proof.step);
    }
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

    // Targeted breadth-frontier regression guards wired into `zig build test`.
    // The `matchOneHypViaView` ACUI-split fix and the `shape.zig` index
    // pre-filter have no unit coverage; their only automated check is that
    // these `ex_elim` lines stay recoverable by `auto?`. `--require-no-miss`
    // exits nonzero on any MISS/ERR (or an empty selection), failing the build.
    const FrontierGuard = struct {
        // null filter = run the WHOLE fixture (every theorem block). Used by the
        // fixture-total guards below, which lock in the FULL count across an
        // entire bespoke-stress fixture, not just one hand-picked line.
        filter: ?[]const u8 = null,
        files: []const u8,
        mode: []const u8 = "breadth",
        // Per-guard budget overrides (null = use the bench default). A guard for
        // a genuinely deep proof can raise these without affecting the global
        // search defaults (which must stay low — raising the global `max_depth`
        // destroys corpus wall-clock on doomed searches for no found-ness gain).
        max_depth: ?usize = null,
        gen_nodes: ?usize = null,
        gen_fuel: ?usize = null,
        global_budget: ?u64 = null,
        // Per-guard forward-saturation budget overrides (null = bench default).
        // Same rationale as the generation budgets: a guard for a genuinely deep
        // forward chain can raise these without touching the conservative global
        // forward defaults (which bound the no-result `forward_stress` case).
        fwd_facts: ?usize = null,
        fwd_attempts: ?usize = null,
        fwd_layers: ?usize = null,
    };
    const frontier_guards = [_]FrontierGuard{
        .{
            .filter = "exists_prime_factor",
            .files = "tests/proof_cases/euclid.mm0:tests/proof_cases/euclid.auf",
        },
        .{
            .filter = "cb_branch_fg_injective_mixed",
            .files = "tests/proof_cases/zermelo.mm0:tests/proof_cases/zermelo.auf",
        },
        // Additive two-sided sequent calculus: guards the ACUI bound-binder
        // slot-count fix (`imp_trans l6`, `de_morgan l5` were the breadth misses
        // it repaired) and the forced-member conclusion seed.
        .{
            .filter = "imp_trans",
            .files = "tests/search_bench_cases/additive_fol.mm0:tests/search_bench_cases/additive_fol.auf",
        },
        .{
            .filter = "de_morgan",
            .files = "tests/search_bench_cases/additive_fol.mm0:tests/search_bench_cases/additive_fol.auf",
        },
        // Depth guard: `de_morgan` must regenerate its WHOLE proof from the bare
        // goal (frontier FULL), which is the only automated check for
        // `tryPrincipalEnumerate` — the breadth guard above finds `de_morgan`
        // through the pool ref and never exercises principal enumeration.
        .{
            .filter = "de_morgan",
            .files = "tests/search_bench_cases/additive_fol.mm0:tests/search_bench_cases/additive_fol.auf",
            .mode = "depth",
        },
        // Depth guard for principal-formula fan-out
        // (`exact_acui.findAmbiguousPrincipal`): `shared_subgoal` must regenerate
        // its WHOLE proof from the bare goal at the default budget. Without
        // fan-out the loose two-premise `lim` search burns its fuel on doomed
        // tuples and stalls at frontier 4/9 — this is the only end-to-end guard
        // that the multi-premise principal selection stays effective.
        .{
            .filter = "shared_subgoal",
            .files = "tests/search_bench_cases/additive_fol.mm0:tests/search_bench_cases/additive_fol.auf",
            .mode = "depth",
        },
        // Depth guard for the idempotent principal-retention pass (phase 4,
        // `GenerationHook.allow_retain_principal` / `exact_split.buildEnumerator`).
        // This goal is provable ONLY by keeping the conjunction `A∧B` in `lan`'s
        // premise (a non-minimal ACUI complement `g , g = g`); minimal-complement
        // pinning dead-ends. The only automated check that generation explores the
        // non-minimal complement — breadth finds it through the pool ref and never
        // exercises the split enumerator's retention path.
        .{
            .filter = "idem_complement_probe",
            .files = "tests/search_bench_cases/idem_complement_probe.mm0:" ++
                "tests/search_bench_cases/idem_complement_probe.auf",
            .mode = "depth",
        },
        // Depth guards for the success transposition memo (`generate.zig`
        // `Driver.concrete_ok`). `branch_converge` and `fan_in` are the convergent
        // (DAG-shaped) additive proofs whose shared subgoals the memo collapses;
        // without it they need ~40× the node/fuel budget. The memo keys subgoals
        // by an ACUI-canonical form, so commuted-context subgoals share a slot too.
        // They are genuinely deep (proof depth ≥ 9), so the global default
        // (`max_depth = 6`) cannot reach them — and must not be raised globally
        // (doing so 10×'s corpus wall-clock on doomed searches for zero gain).
        // These guards raise the budget *only* for these two lines, pinning them
        // FULL as the memo's regression check (breadth finds them through the pool
        // and never exercises deep generation). The budgets are pinned just above
        // each theorem's measured floor (2026-06-24) so a budget regression trips
        // the guard: `branch_converge` is fuel-bound (FULL ≥ f=2048, n≤64);
        // `fan_in` is node-bound (FULL ≥ n=124, f≥512). These are far below the
        // pre-tightening 384/10000 — the witness-unification/eigenvariable-ordering
        // work since the memo landed dropped the floors substantially.
        .{
            .filter = "branch_converge",
            .files = "tests/search_bench_cases/additive_fol.mm0:" ++
                "tests/search_bench_cases/additive_fol.auf",
            .mode = "depth",
            .max_depth = 10,
            .gen_nodes = 128,
            .gen_fuel = 3072,
        },
        .{
            .filter = "fan_in",
            .files = "tests/search_bench_cases/additive_fol.mm0:" ++
                "tests/search_bench_cases/additive_fol.auf",
            .mode = "depth",
            .max_depth = 10,
            .gen_nodes = 192,
            .gen_fuel = 1024,
        },
        // Backward hyp-ordering depth guard (branchfactor + relation-transport
        // screen, `exact.zig` `hypSlotCost` / `isRelationTransport`). `eq_euclid`
        // is a multi-line Hilbert-style modus-ponens chain that regenerates its
        // WHOLE proof from the bare goal ONLY when the generate-only slot is
        // costed (so a well-constrained ref premise leads) — it is unfound at
        // frontier 4 without the cost. The additive total guard above is the dual
        // check (it traps the transport screen: without it, the same cost reorders
        // `mpbi`'s premises and additive collapses). Default budget: the gain is
        // not budget-bound. See `project_premise_ordering_shared_pin`.
        .{
            .filter = "eq_euclid",
            .files = "tests/search_bench_cases/peano_frontier.mm0:" ++
                "tests/search_bench_cases/peano_frontier.auf",
            .mode = "depth",
        },
        // Forward-saturation depth guards (Horn-clause / transitive closure,
        // META_STRESS.md "Bespoke theory #2"). These are the only end-to-end
        // checks that `auto?` FORWARD-SATURATES a real multi-layer Horn
        // derivation: each goal `path v0 vN` must regenerate its WHOLE proof
        // from the edge hypotheses alone (frontier FULL), which exercises the
        // Stage 7/8 forward layer + derived-from-derived recipes (backward
        // search alone can't — the middle vertex is an open subgoal).
        //
        // `reach16` (a length-16 closure, 136 sub-paths) regenerates FULL at the
        // DEFAULT forward bounds — the forward-saturation capability floor; if a
        // change regresses forward derivation or its dedupe, it drops below FULL.
        // `skip_ladder` guards the dedupe path specifically (Fibonacci-many
        // shared-subpath routes). `reach24` regenerates FULL only with the
        // forward budget raised (attempts 1024→16384, facts 64→128, layers
        // untouched) — the completeness-at-budget check pinning the bound order
        // attempts→facts (raising facts alone does nothing). The global forward
        // defaults stay conservative (they bound the no-result `forward_stress`
        // case); the budget is scoped here, exactly as the additive guards above
        // scope generation budget.
        .{
            .filter = "reach16",
            .files = "tests/search_bench_cases/transitive_closure.mm0:" ++
                "tests/search_bench_cases/transitive_closure.auf",
            .mode = "depth",
        },
        .{
            .filter = "skip_ladder",
            .files = "tests/search_bench_cases/transitive_closure.mm0:" ++
                "tests/search_bench_cases/transitive_closure.auf",
            .mode = "depth",
        },
        .{
            .filter = "reach24",
            .files = "tests/search_bench_cases/transitive_closure.mm0:" ++
                "tests/search_bench_cases/transitive_closure.auf",
            .mode = "depth",
            .fwd_attempts = 16384,
            .fwd_facts = 128,
        },
        // `@auto trigger` seeding depth guards (phase 6; see
        // docs/design_notes/trigger_seeding.md). The minimal ND theory is the
        // pure repro of the elimination-major left-rule gap: both theorems
        // must regenerate their WHOLE proof from the bare goal and an EMPTY
        // ref pool, which is possible ONLY through the seeding retry —
        // `nd_mp_inner` (`p → q , p ⊢ q`) was a clean MISS at any budget
        // before it (imp_elim's `p` is premise-only; no ref pins it). These
        // pin the whole chain: annotation parsing → subterm harvest → seed
        // minting → seeded derived pool → the seed-aware slot cost
        // (`HypPlan.seeded_len`, which lets the seed-determined elimination
        // major lead its open minors). FULL at the default budget.
        .{
            .filter = "nd_mp_inner",
            .files = "tests/search_bench_cases/nd_minimal.mm0:" ++
                "tests/search_bench_cases/nd_minimal.auf",
            .mode = "depth",
        },
        .{
            .filter = "nd_or_comm_min",
            .files = "tests/search_bench_cases/nd_minimal.mm0:" ++
                "tests/search_bench_cases/nd_minimal.auf",
            .mode = "depth",
        },
        // The real-theory seeding win: zermelo_frontier's `ax` carries the
        // same triggers, and `nd_exists_elim_const` (4/6 before, capped at
        // the k where a truncated `ax` line had to be re-invented) is FULL
        // with them — the only zermelo per-theorem change from the
        // annotation. (`nd_or_comm` stays 2/6: its k=3 miss is the separate
        // phase-5 distractor-flood budget death, not the left-rule gap.)
        .{
            .filter = "nd_exists_elim_const",
            .files = "tests/search_bench_cases/zermelo_frontier.mm0:" ++
                "tests/search_bench_cases/zermelo_frontier.auf",
            .mode = "depth",
        },
        // Forward-enrollment depth guard for church (task #120,
        // docs/design_notes/church_forward_enrollment.md). church_frontier
        // carries `@auto forward` on MP + eqTR1/eqTR2 — the measured
        // zero-loss set. `OR_DEF` goes 3/14 -> FULL with it (the flagship
        // per-theorem change; DISJ_CASES 1->2 and IMP_TRANS 2->3 aren't
        // FULL-able so can't be pinned by a depth guard). FULL at the
        // default budget; trips if forward join enrollment, the eqTR typing
        // extraction, or the annotation parsing regresses.
        .{
            .filter = "OR_DEF",
            .files = "tests/search_bench_cases/church_frontier.mm0:" ++
                "tests/search_bench_cases/church_frontier.auf",
            .mode = "depth",
        },
        // Forward-JOIN depth guards (∀∃ quantifier alternation, META_STRESS.md
        // "Bespoke theory #3"). These pin the forward-join meta grounding: a
        // universal family fact (`P ?t → Q ?t`, from `all_elim`) joined with a
        // concrete fact (`P c`) by `mp @auto forward` must derive the concrete
        // fact (`Q c`), grounding `?t := c` at the join and baking it as a recipe
        // pin (`DerivedRef.pinned_metas`); the backward `ex_intro` then closes
        // the existential. Both regenerate their WHOLE proof from the bare goal
        // at the DEFAULT budget — the forward-join capability floor.
        //
        // `chain_ex` is the strongest end-to-end check: a TWO-LAYER join
        // (`Pc → Qc → Sc`) whose `S c` recipe nests `Q c`'s recipe, exercising
        // pin propagation across nested layers. `all_imp_ex_compound` pins the
        // COMPOUND-witness join (consequent `Q (f c)`, witness `f c`). If a
        // change regresses the join overlay, the pin baking, or the
        // required⊆shape gate, these drop below FULL. (The genuinely-free
        // witness-invention cells `free_instance_ex` / `compound_free_ex` ride
        // the pre-existing backward path and are covered by the bench corpus and
        // the negative unit test, not guarded here.)
        .{
            .filter = "chain_ex",
            .files = "tests/search_bench_cases/quantifier_alternation.mm0:" ++
                "tests/search_bench_cases/quantifier_alternation.auf",
            .mode = "depth",
        },
        .{
            .filter = "all_imp_ex_compound",
            .files = "tests/search_bench_cases/quantifier_alternation.mm0:" ++
                "tests/search_bench_cases/quantifier_alternation.auf",
            .mode = "depth",
        },
        // Sophisticated forward-join probes that must stay FULL: `diag_ex` grounds
        // the universal meta in TWO family positions (`R ?t ?t`) consistently from
        // one anchor; `nested_rel_ex` peels a nested `∀x∀y`, grounding the outer
        // meta at the join while the inner stays universal into the existential;
        // `ambiguous_anchor_ex` has two valid anchors and must pick one without
        // double-counting.
        .{
            .filter = "diag_ex",
            .files = "tests/search_bench_cases/quantifier_alternation.mm0:" ++
                "tests/search_bench_cases/quantifier_alternation.auf",
            .mode = "depth",
        },
        .{
            .filter = "nested_rel_ex",
            .files = "tests/search_bench_cases/quantifier_alternation.mm0:" ++
                "tests/search_bench_cases/quantifier_alternation.auf",
            .mode = "depth",
        },
        .{
            .filter = "ambiguous_anchor_ex",
            .files = "tests/search_bench_cases/quantifier_alternation.mm0:" ++
                "tests/search_bench_cases/quantifier_alternation.auf",
            .mode = "depth",
        },
        // Nested `ex_intro` composition: the inner introduction resolves a carried
        // ancestor witness from its concrete hyp (`solveCarriedViewMetas`) and
        // renders it explicitly so the outer reads the witness back.
        // `nested_concrete_ex` threads `R c d` two `∃` layers up;
        // `double_all_ex` invents both witnesses through a doubly-universal hyp.
        .{
            .filter = "nested_concrete_ex",
            .files = "tests/search_bench_cases/quantifier_alternation.mm0:" ++
                "tests/search_bench_cases/quantifier_alternation.auf",
            .mode = "depth",
        },
        .{
            .filter = "double_all_ex",
            .files = "tests/search_bench_cases/quantifier_alternation.mm0:" ++
                "tests/search_bench_cases/quantifier_alternation.auf",
            .mode = "depth",
        },
        // Two-layer same-predicate forward chain under a buried witness:
        // `∀x(Px→P(f x)), Pc ⊢ ∃y P(f(f y))`. The whole-proof regen from hyps
        // reuses the SAME family fact `P ?x→P(f ?x)` twice with DIFFERENT witnesses
        // (`?x=c` then `?x=f c`); guards the per-occurrence recipe materialization
        // (`forward.resolveRecipeValues` scoped pins + cursor render) that lets one
        // family fact carry distinct per-use witnesses.
        .{
            .filter = "deep_compound_ex",
            .files = "tests/search_bench_cases/quantifier_alternation.mm0:" ++
                "tests/search_bench_cases/quantifier_alternation.auf",
            .mode = "depth",
        },
        // Carried-witness COMPOUND guard (witness-unification migration): the
        // carried (outer) witness of a nested `ex_intro` must accept a COMPOUND
        // value end-to-end — `solveCarriedViewMetas` resolves `W := f c`, and
        // the `UnifyMismatch` holey-retry in `validateSelectedRefs` hands the
        // checker the value the inference solver's placeholder model cannot
        // absorb (wildcard-for-subtree). Matches all three `nested_compound_*`
        // variants (outer / inner / both); bare-witness `nested_concrete_ex`
        // above cannot catch this regression (wildcard-for-leaf survives
        // inference). FULL at the default budget.
        .{
            .filter = "nested_compound",
            .files = "tests/search_bench_cases/quantifier_alternation.mm0:" ++
                "tests/search_bench_cases/quantifier_alternation.auf",
            .mode = "depth",
        },
        // Deeper stress probes layered on the fixes above. `triple_compound_ex`
        // adds a THIRD same-family forward layer (witness under three `f`s):
        // capability is present but the third saturation layer needs
        // `fwd_layers=4` (default is 3 — enough for `deep_compound_ex`'s two
        // layers, not three). `diag_compound_ex` is `diag_ex` with a COMPOUND
        // diagonal witness (`f c` read consistently off both `R y y` slots).
        // `forward_nested_ex` feeds a FORWARD-derived relational fact (`R c d`,
        // no such hypothesis) into the nested-`ex_intro` carried-witness path,
        // combining forward join with carried-meta nested introduction.
        .{
            .filter = "triple_compound_ex",
            .files = "tests/search_bench_cases/quantifier_alternation.mm0:" ++
                "tests/search_bench_cases/quantifier_alternation.auf",
            .mode = "depth",
            .fwd_layers = 4,
        },
        .{
            .filter = "diag_compound_ex",
            .files = "tests/search_bench_cases/quantifier_alternation.mm0:" ++
                "tests/search_bench_cases/quantifier_alternation.auf",
            .mode = "depth",
        },
        .{
            .filter = "forward_nested_ex",
            .files = "tests/search_bench_cases/quantifier_alternation.mm0:" ++
                "tests/search_bench_cases/quantifier_alternation.auf",
            .mode = "depth",
        },
        // ── Fixture-TOTAL FULL guards (META_STRESS.md §3 bespoke theories #1–#3).
        // The per-line guards above pin specific theorems just above their budget
        // floor (catching *budget* regressions on those lines). These three pin
        // the FULL *total* of an ENTIRE fixture: with `--filter` omitted every
        // theorem block is selected, and depth + `--require-no-miss` fails unless
        // EVERY line regenerates its whole proof (`full == theorems`). This is the
        // completeness backstop — it catches a regression on any unguarded line
        // and forces any newly-added theorem to reach FULL (or be given coverage),
        // so the "100% FULL" claim for these fixtures can't silently rot.
        //
        // Each fixture uses the union of its own per-line budget overrides (the
        // max across its theorems), so the total guard is no looser than the
        // line guards it subsumes. Verified 2026-07-02: additive_fol 84/84,
        // transitive_closure 7/7, quantifier_alternation 23/23 FULL (18 + the
        // five compound-witness probes); each total trips (exit 1) if its
        // budget union is reduced below floor.
        .{
            // #1 additive sequent calculus (backward generation): branch_converge
            // is fuel-bound (3072), fan_in node-bound (192); both need depth 10.
            .files = "tests/search_bench_cases/additive_fol.mm0:" ++
                "tests/search_bench_cases/additive_fol.auf",
            .mode = "depth",
            .max_depth = 10,
            .gen_nodes = 192,
            .gen_fuel = 3072,
        },
        .{
            // #2 transitive closure (forward saturation): reach24/reach32 need the
            // forward budget raised (attempts 16384, facts 128); reach32 is NOT
            // individually guarded, so this total is its only FULL check.
            .files = "tests/search_bench_cases/transitive_closure.mm0:" ++
                "tests/search_bench_cases/transitive_closure.auf",
            .mode = "depth",
            .fwd_attempts = 16384,
            .fwd_facts = 128,
        },
        .{
            // #3 quantifier alternation (forward join): triple_compound_ex needs a
            // 4th saturation layer; everything else is FULL at the default budget.
            .files = "tests/search_bench_cases/quantifier_alternation.mm0:" ++
                "tests/search_bench_cases/quantifier_alternation.auf",
            .mode = "depth",
            .fwd_layers = 4,
        },
        // ── Tait one-sided (Schütte) sequent calculus: backward search over a
        // single ACUI succedent `⊢ Δ` (see tait.mm0's header). A classical FOL
        // stress fixture — every connective has a positive intro rule (ror / rand
        // / rim / rbi / rall / rex) plus an EXPLICIT De Morgan rule for its
        // negation (rdm_*), because binder inference (exact unify replay) runs
        // BEFORE @rewrite normalization and so cannot match a De-Morgan-normalized
        // ref line; the rdm_* rules keep the leaves structural.
        //
        // KEY depth finding (2026-07-04): the search depth a proof needs equals
        // its proof-TREE HEIGHT (longest leaf→root rule chain), NOT its line
        // count. iff_comm (15 lines) is FULL at the default md=6 because it is a
        // BALANCED tree of height 6, while all_swap (8 lines) needs md=7 because
        // it is a linear chain of height 7. md=6 misses the height-7/8 proofs.
        // drinker's md≥8 FLOOD (its usable window used to be md∈[5,7]) is FIXED
        // by the depth-major phase-ladder core (generate.zig runPhaseLadder,
        // 2026-07-05); with forall_mono's node floor removed by the member-side
        // capture check (below) the fixture is 20/20 FULL at every md≥8 with
        // NO overrides.
        //
        // Gap-closure history (2026-07-04 dissection; ex_swap closed later
        // the same day, forall_mono on 2026-07-05):
        //   * resolution — was a doomed-reject flood: loose 1-premise candidates
        //     (`ror`/`rdm_*`, principal binders unbound inside the ACUI
        //     succedent) swept the whole pool through full `tryCandidate`. The
        //     hyp-vs-ref member-consistency prune (`hypRefMembersPlausible`)
        //     kills the sweep; the internal-child enumeration cutoff dropped
        //     the honest budget floor 5.51G → 3.75G ticks (was >10G before
        //     the prune); and removing the redundant pre-clone COW chain
        //     level under every `tryCandidate` probe (`tryCandidateProbe` in
        //     candidate.zig, 2026-07-05) dropped it again, 3.75G → 3.09G —
        //     UNDER the 3.35G default cap. CLOSED: FULL 13/13 at pure
        //     defaults, guarded below with no overrides (deterministic
        //     margin 1.08×: any change pushing the k=6 floor +8% trips it).
        //   * forall_mono — was NODE-bound, not fuel-bound (floor ∈ (384,
        //     512]). CLOSED by the member-side witness capture check (see the
        //     forall_mono guard comment below): the node budget had been going
        //     to scope-escaping member-witness fills, not to the honest carry
        //     recursion. FULL at pure defaults. (The corpus-wide nodes=2048
        //     sweep staying REFUTED is unaffected — 21 depth-FULL losses.)
        //   * ex_swap — was the last capability gap (rex ACCEPTED-witness
        //     over-generation: `rex` KEEPS its principal, so every open node
        //     re-offered a fresh carry-metavar rex whose premise is itself a
        //     new ∃ member — a self-feeding cascade of VALID one-step
        //     rederivations, ~one accepted full validation per chain node).
        //     CLOSED by the internal-child enumeration cutoff
        //     (`ExactOptions.internal_open_child`) plus the witness-class
        //     candidate order (`witnessClass` in exact.zig): FULL 7/7 at
        //     DEFAULT budget/nodes (worst row 1.68G, was 9.5G + n=4096 floors).
        //     Guarded below at md=12 with no overrides.
        // ex_all_to_all_ex — formerly the hardest of the set (its single `ax`
        // leaf must co-solve TWO open rex witnesses in one complementary pair,
        // no rigid anchor) — is CLOSED by the complementary coupled sweep
        // (`collectComplementShapes` / `unifyMembersThroughShape` in
        // exact_witness.zig).
        //
        // ── `@auto eager` era (2026-07-05). The fixture now declares its
        // invertible discipline: the non-branching decomposition ladder
        // (ror/rim/rdm_*) is `@auto eager`, the branching rules (rand/rbi)
        // `@auto eager 2`, rex stays plain `@auto backward`. Eager rules are
        // tried first, committed to once applied (set-commit cut), and exempt
        // from the depth budget — so counted depth ≈ genuine choice points and
        // EVERY theorem is FULL at the DEFAULT md=6 (most at md=1): the old
        // per-theorem md floors (imp_trans/all_swap/all_an_dist_fwd/
        // ex_all_to_all_ex md=7, forall_mono/ex_swap md=12, drinker's md≥8
        // flood) all collapsed into the default-md whole-fixture net below.
        // The nested-inline binder-extraction residual (task #93) is CLOSED:
        // accepted `@auto eager` candidates inside internal generation child
        // solves now carry their resolved bindings rendered on the spliced
        // application (`internal_child` in exact_validate.zig), so the parent
        // re-check never re-infers them from an ACUI-reassociated hint. The
        // old resolution churn (k>=6 rows at ~3.4G ticks, over the 3.35G
        // default cap) collapsed to ~58M; the whole fixture's worst theorem
        // is now ~0.31G (exists_mono), so the depth nets below run at the
        // pure DEFAULT budget with >10x margin.
        .{
            // Completeness backstop: every one of the 385 proof lines must stay
            // breadth-found (and any newly-added line must be found) — at pure
            // defaults, with the eager cut live. This is also the teeth that
            // the eager annotations stay genuinely invertible: a wrong
            // annotation would make some hand-proof line unreachable through
            // the cut-honoring phases.
            .files = "tests/search_bench_cases/tait.mm0:" ++
                "tests/search_bench_cases/tait.auf",
            .mode = "breadth",
        },
        // Depth-completeness net at the DEFAULT md: every theorem (all 52,
        // core + extended battery) regenerates FULL from the bare goal at
        // md=6 — the headline property of the eager discipline. Pure
        // defaults, including the tick budget (see note above).
        .{
            .files = "tests/search_bench_cases/tait.mm0:" ++
                "tests/search_bench_cases/tait.auf",
            .mode = "depth",
        },
        // Monotonicity net at md=12: everything found at md=6 must stay found
        // when the depth budget is deep — the depth-major phase-ladder teeth
        // (drinker's old md≥8 flood: phase-major nesting put doomed deep
        // phase-1/2 passes in front of its shallow phase-3 witness proof).
        .{
            .files = "tests/search_bench_cases/tait.mm0:" ++
                "tests/search_bench_cases/tait.auf",
            .mode = "depth",
            .max_depth = 12,
        },
    };
    const frontier_smoke_step = b.step(
        "test-frontier-smoke",
        "Regression guard: targeted breadth frontier lines must stay found",
    );
    for (frontier_guards) |guard| {
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
        "[--debug SYSTEMS] [-Werror]\n" ++
        "  abc lsp\n" ++
        "  abc [--help | --version]\n" ++
        "\nOptions:\n" ++
        "  -h, --help       Show this help and exit\n" ++
        "  -V, --version    Show the version and exit\n" ++
        "  --debug SYSTEMS  Enable debug output (comma-separated:\n" ++
        "                   inference,views,dependency,freshen," ++
        "normalization,boundary,all)\n" ++
        "  -Werror          Treat compiler warnings as errors\n";

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
}
