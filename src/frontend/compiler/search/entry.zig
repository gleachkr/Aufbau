//! The `auto?` and `exact?` entries: set up the search core's run on a
//! clone of the theorem (the `@vars` pool, `@auto trigger` seeds, forward
//! saturation), run it, and copy the proof it finds out of the transient
//! state (see `search/ARCHITECTURE.md`).

const std = @import("std");
const ArenaAllocator = @import("../../arena_allocator.zig").ArenaAllocator;
const types = @import("./types.zig");
const forward = @import("./forward.zig");
const trigger = @import("./trigger.zig");
const core = @import("./core/root.zig");
const session_mod = @import("./session.zig");
const expr_mod = @import("../../expr.zig");
const TheoremContext = @import("../../expr.zig").TheoremContext;
const ProofScript = @import("../../proof_script.zig");
const RuleApplication = ProofScript.RuleApplication;
const Ref = ProofScript.Ref;
const CompilerContext = @import("../context.zig").CompilerContext;
const Check = @import("../check.zig");
const Goal = types.Goal;
const Context = types.Context;
const NameExprMap = types.NameExprMap;
const GenerateOptions = types.GenerateOptions;

/// Generated full proof trees for a goal. The trees are owned by `arena`; they
/// stay valid until `deinit`, which the caller invokes after rendering.
pub const GeneratedResults = struct {
    arena: ArenaAllocator,
    applications: []const RuleApplication,

    pub fn deinit(self: *GeneratedResults) void {
        self.arena.deinit();
        self.* = undefined;
    }
};

/// Top-level entry for `auto?`: a proof of `goal` by the search core. A
/// holey goal is searched with a meta in place of each hole, so the proof
/// found fills the holes too (`auto?` on `g ⊢ t : _` infers a type). An
/// implicit whole-conclusion goal gets no search.
pub fn generateTopLevel(
    compiler: *CompilerContext,
    session: *session_mod.SearchSession,
    goal: Goal,
    theorem: *const TheoremContext,
    theorem_vars: *const NameExprMap,
    options: GenerateOptions,
    budget_ptr: ?*types.GlobalBudget,
) !GeneratedResults {
    var arena = ArenaAllocator.init(session.allocator);
    errdefer arena.deinit();

    // The search call's cost budget (`budget_ptr`, from
    // `options.global_budget`) spans forward saturation and the core. The
    // caller installs it as `compiler.work_budget` for the whole call.
    const ticks_start = expr_mod.work_ticks;
    const sym_ticks_start = expr_mod.work_ticks_sym;
    const core_ticks_start = expr_mod.work_ticks_core;
    const walk_ticks_start = expr_mod.work_ticks_walk;
    // Candidate checks run deep in the descent; the checker's stack guard
    // measures from here so it counts the descent's frames too.
    const saved_stack_base = compiler.stack_base;
    if (saved_stack_base == null) compiler.stack_base = @frameAddress();
    defer compiler.stack_base = saved_stack_base;

    switch (goal) {
        .concrete, .holey => {},
        .implicit_whole_conclusion => return .{ .arena = arena, .applications = &.{} },
    }
    if (options.max_depth == 0) {
        return .{ .arena = arena, .applications = &.{} };
    }

    var work_theorem = try theorem.clone();
    defer work_theorem.deinit();

    // The `@vars` pool tokens, named as dummies of the work theorem, from
    // which the core's close-out names leftover eigenvariables and
    // witnesses.
    var vars_clone = try poolVarsClone(session, &work_theorem, theorem_vars);
    defer if (vars_clone) |*clone| clone.deinit();

    // `@auto trigger` seeds: ground instances of the theory's hypothesis-free
    // trigger rules harvested from the goal's subterms (the analytic leaf
    // set; see `trigger.zig`), less any restating a pool fact. They reach
    // the core as the depth-0 sources of forward saturation. A holey goal's
    // holes are metas, not subterms to seed from.
    var harvested: []types.DerivedRef = &.{};
    defer session.allocator.free(harvested);
    var seeds: []const types.DerivedRef = &.{};
    if (goal == .concrete and session.context.registry.triggerRuleCount() > 0) {
        harvested = try trigger.harvestSeeds(
            session.context,
            &work_theorem,
            goal.concrete,
            session.allocator,
        );
        seeds = try trigger.dropRestatedSeeds(
            session.context,
            &work_theorem,
            try session.getReferencePool(theorem, session.effectiveCounters(null)),
            &.{},
            harvested,
            session.allocator,
        );
    }

    // Bounded multi-layer forward saturation over the ref pool, with the
    // seeds as depth-0 sources, before the core runs. Skipped entirely
    // (no cost) when the theory declares no `@auto forward` rules — the
    // pool then holds the seeds alone, if any.
    var derived_pool: ?types.DerivedPool = null;
    defer if (derived_pool) |*dpool| dpool.deinit();
    if (session.context.registry.autoForwardRuleCount() > 0) {
        derived_pool = try saturateForward(session, theorem, &work_theorem, options, seeds);
    } else if (seeds.len > 0) {
        derived_pool = try trigger.seedOnlyPool(session.context, seeds);
    }

    const counters = session.effectiveCounters(null);
    if (counters) |c| c.trigger_seed_count += seeds.len;
    var applications = std.ArrayListUnmanaged(RuleApplication).empty;
    try runCore(.{
        .compiler = compiler,
        .context = session.context,
        .theorem = &work_theorem,
        .theorem_vars = if (vars_clone) |*clone| clone else theorem_vars,
        .pool_theorem = theorem,
        .pool = try session.getReferencePool(theorem, counters),
        .derived = if (derived_pool) |*dpool| dpool else null,
        .goal = goal,
        .max_depth = options.coreDepth(),
        .stack_guard_bytes = options.stack_guard_bytes,
        .budget = budget_ptr,
        .counters = counters,
        .out = arena.allocator(),
        .scratch = session.allocator,
    }, &applications);

    if (counters) |c| {
        // Mirror the forward layer's meta-store activity into the bench
        // counters.
        if (derived_pool) |*dpool| {
            c.universal_metas_created += dpool.store.stats.universal_created;
            c.meta_assignments += dpool.store.stats.assignments;
            c.meta_rollbacks += dpool.store.stats.rollbacks;
        }
        // Per-call cost observability: ticks consumed by this whole call.
        c.gen_work_ticks = expr_mod.work_ticks -% ticks_start;
        c.gen_sym_ticks = expr_mod.work_ticks_sym -% sym_ticks_start;
        c.gen_core_ticks = expr_mod.work_ticks_core -% core_ticks_start;
        c.gen_walk_ticks = expr_mod.work_ticks_walk -% walk_ticks_start;
    }

    return .{ .arena = arena, .applications = applications.items };
}

/// `exact?`: a proof of `goal` in one step by the search core, a rule
/// whose premises pool refs and rules with no premises close
/// (`core.Request.one_step`). A holey
/// goal's holes and an inline slot's unknowns are the core's to fill.
pub fn exactTopLevel(
    compiler: *CompilerContext,
    session: *session_mod.SearchSession,
    goal: Goal,
    theorem: *const TheoremContext,
    theorem_vars: *const NameExprMap,
    stack_guard_bytes: usize,
    budget: ?*types.GlobalBudget,
) !GeneratedResults {
    var arena = ArenaAllocator.init(session.allocator);
    errdefer arena.deinit();
    const saved_stack_base = compiler.stack_base;
    if (saved_stack_base == null) compiler.stack_base = @frameAddress();
    defer compiler.stack_base = saved_stack_base;
    var work_theorem = try theorem.clone();
    defer work_theorem.deinit();
    var vars_clone = try poolVarsClone(session, &work_theorem, theorem_vars);
    defer if (vars_clone) |*clone| clone.deinit();
    const counters = session.effectiveCounters(null);
    var found = std.ArrayListUnmanaged(RuleApplication).empty;
    _ = core.run(.{
        .compiler = compiler,
        .context = session.context,
        .theorem = &work_theorem,
        .theorem_vars = if (vars_clone) |*clone| clone else theorem_vars,
        .pool_theorem = theorem,
        .pool = try session.getReferencePool(theorem, counters),
        .goal = goal,
        .max_depth = 1,
        .one_step = true,
        .collect = &found,
        .stack_guard_bytes = stack_guard_bytes,
        .budget = budget,
        .counters = counters,
        .out = arena.allocator(),
        .scratch = session.allocator,
    }) catch |err| switch (err) {
        // Out of budget or stack: what the search found so far.
        error.SearchBudgetExhausted, error.SearchStackExhausted => {},
        else => |e| return e,
    };
    // Those citing only references first, then as the rules are declared,
    // then by fewer premises.
    std.mem.sort(RuleApplication, found.items, session.context, struct {
        fn lessThan(context: *const Context, lhs: RuleApplication, rhs: RuleApplication) bool {
            const l_nested = nestedSteps(lhs);
            const r_nested = nestedSteps(rhs);
            if (l_nested != r_nested) return l_nested < r_nested;
            const l = context.env.getRuleId(lhs.rule_name).?;
            const r = context.env.getRuleId(rhs.rule_name).?;
            if (l != r) return l < r;
            return lhs.refs.len < rhs.refs.len;
        }

        fn nestedSteps(app: RuleApplication) usize {
            var count: usize = 0;
            for (app.refs) |ref| if (ref == .application) {
                count += 1;
            };
            return count;
        }
    }.lessThan);
    return .{ .arena = arena, .applications = found.items };
}

/// A clone of `theorem_vars` naming each `@vars` pool token as a dummy of
/// `work_theorem`, in sorted order so the dummy ids are deterministic; null
/// when the theory declares no pools. A token that finds no dependency slot
/// is left out: branches needing it fail cleanly.
fn poolVarsClone(
    session: *session_mod.SearchSession,
    work_theorem: *TheoremContext,
    theorem_vars: *const NameExprMap,
) !?NameExprMap {
    if (session.context.sort_vars.count() == 0) return null;
    var vars = try Check.cloneNameExprMap(session.allocator, theorem_vars);
    errdefer vars.deinit();
    var tokens = std.ArrayListUnmanaged([]const u8).empty;
    defer tokens.deinit(session.allocator);
    var token_iter = session.context.sort_vars.tokens.keyIterator();
    while (token_iter.next()) |token| {
        try tokens.append(session.allocator, token.*);
    }
    std.mem.sort([]const u8, tokens.items, {}, stringLessThan);
    for (tokens.items) |token| {
        const decl = session.context.sort_vars.getTokenDecl(token) orelse
            continue;
        work_theorem.ensureNamedDummyParserVar(
            session.context.parser.core.allocator,
            &vars,
            token,
            decl.sort_name,
            decl.sort_id,
        ) catch |err| switch (err) {
            error.OutOfMemory => return error.OutOfMemory,
            else => {},
        };
    }
    return vars;
}

/// The search core's run on `request.goal`, recording in the counters how
/// it ended. A proof it finds is appended to `applications`.
fn runCore(
    request: core.Request,
    applications: *std.ArrayListUnmanaged(RuleApplication),
) !void {
    const result = core.run(request) catch |err| switch (err) {
        error.SearchBudgetExhausted => return endCore(request.counters, .budget),
        error.SearchStackExhausted => return endCore(request.counters, .stack),
        else => |e| return e,
    };
    switch (result) {
        .abstained => {},
        .missed => |missed| endCore(request.counters, if (missed.exhausted) .exhausted else .depth_limit),
        .found => |found| {
            if (request.counters) |c| {
                c.gen_last_depth = found.depth;
                c.core_ran = true;
            }
            // A derived fact's recipe lives in the derived pool, freed
            // with the call.
            try applications.append(request.out, try cloneApplication(request.out, found.application));
        },
    }
}

/// Record how the core's run ended without a proof, for the miss report.
fn endCore(counters: ?*types.SearchCounters, end: types.CoreEnd) void {
    const c = counters orelse return;
    c.core_ran = true;
    c.core_end = end;
}

/// Bounded forward saturation over the theorem's ref pool, with `seeds` as
/// extra depth-0 sources.
fn saturateForward(
    session: *session_mod.SearchSession,
    theorem: *const TheoremContext,
    work_theorem: *TheoremContext,
    options: GenerateOptions,
    seeds: []const types.DerivedRef,
) !types.DerivedPool {
    const ref_pool = try session.getReferencePool(
        theorem,
        session.effectiveCounters(null),
    );
    const ref_index = try session.getRefIndex(
        theorem,
        session.effectiveCounters(null),
    );
    return forward.saturate(
        session.context,
        work_theorem,
        ref_pool,
        ref_index,
        options.forward,
        session.effectiveCounters(null),
        seeds,
    );
}

fn stringLessThan(_: void, lhs: []const u8, rhs: []const u8) bool {
    return std.mem.lessThan(u8, lhs, rhs);
}

/// Deep-copy a `RuleApplication` (recursively, through inline refs) into `arena`
/// so it outlives the core's transient state. Leaf data
/// (rule/label name slices) point into the stable env/source and are aliased;
/// explicit-binding strings (derived recipes render these into the
/// transient derived pool's arena) are duplicated.
fn cloneApplication(
    arena: std.mem.Allocator,
    app: RuleApplication,
) anyerror!RuleApplication {
    const refs = try arena.alloc(Ref, app.refs.len);
    for (app.refs, 0..) |ref, idx| {
        refs[idx] = switch (ref) {
            .hyp, .line => ref,
            .application => |child| .{
                .application = try cloneApplication(arena, child),
            },
        };
    }
    const zero_span = ProofScript.Span{ .start = 0, .end = 0 };
    const arg_bindings = try arena.alloc(
        ProofScript.ArgBinding,
        app.arg_bindings.len,
    );
    for (app.arg_bindings, 0..) |binding, idx| {
        arg_bindings[idx] = .{
            .name = try arena.dupe(u8, binding.name),
            .name_span = zero_span,
            .formula = .{
                .text = try arena.dupe(u8, binding.formula.text),
                .span = zero_span,
            },
            .span = zero_span,
        };
    }
    var copy = app;
    copy.refs = refs;
    copy.arg_bindings = arg_bindings;
    copy.binding_list_span = null;
    copy.rule_span = zero_span;
    copy.refs_span = if (refs.len == 0) null else zero_span;
    copy.span = zero_span;
    return copy;
}
