const std = @import("std");
const GlobalEnv = @import("./env.zig").GlobalEnv;
const RuleDecl = @import("./env.zig").RuleDecl;
const Expr = @import("../trusted/expressions.zig").Expr;
const SurfaceExpr = @import("./surface_expr.zig");
const TemplateExpr = @import("./rules.zig").TemplateExpr;
const ExprId = @import("./expr.zig").ExprId;
const TheoremContext = @import("./expr.zig").TheoremContext;
const RewriteRegistry = @import("./rewrite_registry.zig").RewriteRegistry;
const CompilerDiag = @import("./diag.zig");
const ViewDecl = @import("./views.zig").ViewDecl;
const DerivedBinding = @import("./views.zig").DerivedBinding;
const Canonicalizer = @import("./canonicalizer.zig").Canonicalizer;
const AcuiSupport = @import("./acui_support.zig");
const DerivedBindings = @import("./derived_bindings.zig");
const DefOps = @import("./def_ops.zig");
const DebugConfig = @import("./debug.zig").DebugConfig;
const BranchStateOps = @import("./inference_solver/branch_state.zig");
const SemanticCompare = @import("./inference_solver/semantic_compare.zig");
const StructuralIntervals =
    @import("./inference_solver/intervals.zig");
const StructuralMatcher = @import("./inference_solver/matcher.zig");
const ViewState = @import("./inference_solver/view_state.zig");
const StructuralObligationSolver =
    @import("./inference_solver/obligation_solver.zig");
const StructuralStateUpdates =
    @import("./inference_solver/state_updates.zig");
const Ambiguity = @import("./inference_solver/ambiguity_report.zig");
const types = @import("./inference_solver/types.zig");
const BinderSpace = types.BinderSpace;
const MatchConstraint = types.MatchConstraint;
const StructuralJointObligation = types.StructuralJointObligation;
const BranchState = types.BranchState;

const SolutionPreference = Ambiguity.SolutionPreference;
pub const AmbiguityReport = Ambiguity.AmbiguityReport;

const ConclusionConstraint = union(enum) {
    concrete: ExprId,
    surface: *const Expr,
};

/// Which rule-application region a constraint filters against. Hypothesis
/// constraints are indexed in source order (premise i vs rule hypothesis i).
const ConstraintRegion = enum {
    hypothesis,
    conclusion,
};

/// Recorded when a constraint stage empties the branch-state set: no
/// completion of the rule's variables makes that part of the application
/// match. Finalization-stage failures (structural obligations, derived
/// bindings) leave this null — they have no single clashing region.
pub const SolveFailure = struct {
    region: Region,
    /// The concrete expression the failing constraint matched against
    /// (the cited premise's conclusion, or the statement itself).
    actual: ?ExprId,

    pub const Region = union(enum) {
        conclusion,
        hypothesis: usize,
    };
};

pub const Solver = struct {
    // During `solveWithConclusion`, `allocator` is repointed at `state_arena`
    // so the throwaway BranchState generations (each solve fans out into many
    // short-lived generations that were never individually freed) are reclaimed
    // in one shot when the Solver is torn down. `real_allocator` is the caller's
    // allocator — which is also the theorem interner's allocator — and is used
    // for everything that must outlive the arena churn: the returned bindings,
    // the ambiguity report, and every def_ops context (whose `internAppOwned`
    // frees interned args with the interner allocator, so its `SharedContext`
    // allocator MUST equal the interner allocator).
    allocator: std.mem.Allocator,
    real_allocator: std.mem.Allocator,
    state_arena: std.heap.ArenaAllocator,
    env: *const GlobalEnv,
    theorem: *TheoremContext,
    registry: *RewriteRegistry,
    rule_id: u32,
    rule: *const RuleDecl,
    view: ?*const ViewDecl,
    canonicalizer: Canonicalizer,
    scratch: ?*CompilerDiag.Scratch,
    debug: DebugConfig,
    ambiguity_warning: bool = false,
    ambiguity_report: AmbiguityReport = .{},
    failure: ?SolveFailure = null,
    // Reusable def_ops contexts, created lazily and torn down in `deinit`.
    // One solve fans out into many short-lived match attempts that each used
    // to build a fresh context — discarding the symbolic hash-cons table and
    // the whole-template expansion memo between attempts. Sharing one context
    // per solve is sound because theorem/env/registry are fixed for the
    // Solver's lifetime and the context-level caches key only structure that
    // is stable under theorem-interner growth (see `SharedContext`). Both use
    // `real_allocator` (the interner allocator) like the per-call contexts did.
    def_ops_ctx: ?DefOps.Context = null,
    def_ops_ctx_plain: ?DefOps.Context = null,
    /// Solve-lifetime ACUI structural-support context for the semantic-compare
    /// paths (`bindingCompatible` / `commonStructuralTarget`), which used to
    /// build a fresh context — and therefore a cold def_ops context — per
    /// comparison. Same soundness argument as the def_ops contexts above.
    acui_support_ctx: ?AcuiSupport.Context = null,

    pub fn init(
        allocator: std.mem.Allocator,
        env: *const GlobalEnv,
        theorem: *TheoremContext,
        registry: *RewriteRegistry,
        rule_id: u32,
        rule: *const RuleDecl,
        view: ?*const ViewDecl,
        scratch: ?*CompilerDiag.Scratch,
        debug: DebugConfig,
    ) Solver {
        return .{
            .allocator = allocator,
            .real_allocator = allocator,
            .state_arena = std.heap.ArenaAllocator.init(allocator),
            .env = env,
            .theorem = theorem,
            .registry = registry,
            .rule_id = rule_id,
            .rule = rule,
            .view = view,
            .canonicalizer = Canonicalizer.init(
                allocator,
                @constCast(theorem),
                registry,
                env,
            ),
            .scratch = scratch,
            .debug = debug,
        };
    }

    pub fn canUseNormalizedStructuralItemMatch(self: *const Solver) bool {
        // Final validation can now produce normalized transport. Structural
        // search may use normalized item matching as a branch-local inference aid
        // whenever diagnostic scratch is available. The expensive path is
        // still gated by structural competition and by exact/transparent
        // item matching failing first.
        return self.scratch != null;
    }

    pub fn deinit(self: *Solver) void {
        // The ambiguity summaries are built by `pickUniqueSolution` after
        // `allocator` has been restored to `real_allocator`, so free them there
        // regardless of what `allocator` currently points at.
        if (self.ambiguity_report.chosen_bindings) |summary| {
            self.real_allocator.free(summary);
        }
        if (self.ambiguity_report.alternative_bindings) |summary| {
            self.real_allocator.free(summary);
        }
        self.canonicalizer.cache.deinit();
        if (self.def_ops_ctx) |*ctx| ctx.deinit();
        if (self.def_ops_ctx_plain) |*ctx| ctx.deinit();
        if (self.acui_support_ctx) |*ctx| ctx.deinit();
        self.state_arena.deinit();
    }

    /// The solve-lifetime def_ops context (with registry). Lazily created on
    /// first use via a stable `*Solver`, so the by-value construction copies
    /// inside `DefOps.Context.init*` settle before any self-referential state
    /// (arena, caches) exists.
    pub fn defOpsContext(self: *Solver) *DefOps.Context {
        if (self.def_ops_ctx == null) {
            self.def_ops_ctx = DefOps.Context.initWithRegistry(
                self.real_allocator,
                self.theorem,
                self.env,
                self.registry,
            );
        }
        return &self.def_ops_ctx.?;
    }

    /// Registry-free variant (transparent-only matching sites).
    pub fn defOpsContextPlain(self: *Solver) *DefOps.Context {
        if (self.def_ops_ctx_plain == null) {
            self.def_ops_ctx_plain = DefOps.Context.init(
                self.real_allocator,
                self.theorem,
                self.env,
            );
        }
        return &self.def_ops_ctx_plain.?;
    }

    pub fn hadAmbiguityWarning(self: *const Solver) bool {
        return self.ambiguity_warning;
    }

    pub fn getAmbiguityReport(self: *const Solver) ?AmbiguityReport {
        if (!self.ambiguity_warning) return null;
        return self.ambiguity_report;
    }

    pub fn getFailure(self: *const Solver) ?SolveFailure {
        return self.failure;
    }

    pub fn structuralSupport(self: *Solver) AcuiSupport.Context {
        // AcuiSupport builds def_ops contexts internally, whose `internAppOwned`
        // frees interned args with the theorem interner allocator, so it must run
        // on the real allocator, not the per-solve arena.
        return AcuiSupport.Context.init(
            self.real_allocator,
            self.theorem,
            self.env,
            self.registry,
        );
    }

    /// Solve-lifetime shared variant of `structuralSupport`. Callers must not
    /// deinit (or copy) the result; the Solver owns it. Lazily created via a
    /// stable `*Solver`, so the by-value construction copy settles while the
    /// context's lazy def_ops field is still null (the documented-safe window).
    pub fn structuralSupportShared(self: *Solver) *AcuiSupport.Context {
        if (self.acui_support_ctx == null) {
            self.acui_support_ctx = self.structuralSupport();
        }
        return &self.acui_support_ctx.?;
    }

    // This entry point is supposed to infer omitted structural binders for
    // every fragment we advertise through `@acui`: AU, ACU, AUI, and ACUI.
    // That means preserving the fragment's order / multiplicity semantics
    // while still handling structural matches that leave several remainder
    // binders unresolved until later constraints or finalization.
    pub fn solve(
        self: *Solver,
        partial_bindings: []const ?ExprId,
        ref_exprs: []const ExprId,
        line_expr: ExprId,
    ) anyerror![]const ExprId {
        return try self.solveWithConclusion(
            partial_bindings,
            ref_exprs,
            .{ .concrete = line_expr },
        );
    }

    pub fn solveHoleyConclusion(
        self: *Solver,
        partial_bindings: []const ?ExprId,
        ref_exprs: []const ExprId,
        holey_concl: *const Expr,
    ) anyerror![]const ExprId {
        return try self.solveWithConclusion(
            partial_bindings,
            ref_exprs,
            .{ .surface = holey_concl },
        );
    }

    fn solveWithConclusion(
        self: *Solver,
        partial_bindings: []const ?ExprId,
        ref_exprs: []const ExprId,
        conclusion: ConclusionConstraint,
    ) anyerror![]const ExprId {
        // Route the throwaway BranchState generations through the per-solve
        // arena; def_ops contexts are pinned to `real_allocator` separately so
        // the interner contract still holds. Restore before we build the result.
        // Reset first so a Solver reused across solves (e.g. the holey→plain
        // fallback) reclaims the previous solve's generations rather than
        // accumulating them until teardown. Nothing outside the arena references
        // it between solves (the result and ambiguity report are on real).
        _ = self.state_arena.reset(.retain_capacity);
        self.allocator = self.state_arena.allocator();
        errdefer self.allocator = self.real_allocator;
        self.failure = null;

        var states = try self.initialStates(partial_bindings);

        if (self.view) |view| {
            states = try self.applyHypConstraints(
                states.items,
                view.hyps,
                ref_exprs,
                .view,
            );
            states = try self.applyConclusionConstraint(
                states.items,
                view.concl,
                conclusion,
                .view,
            );
            states = try self.finalizeViewAndRuleStates(states.items, view);
        } else {
            states = try self.applyHypConstraints(
                states.items,
                self.rule.hyps,
                ref_exprs,
                .rule,
            );
            states = try self.applyConclusionConstraint(
                states.items,
                self.rule.concl,
                conclusion,
                .rule,
            );
            states = try self.finalizeStructuralStates(states.items, .rule);
        }

        // The result and ambiguity report must outlive the arena, so build them
        // on the real allocator. The arena-backed `states` stay valid (the arena
        // is not reclaimed until the Solver is torn down).
        self.allocator = self.real_allocator;
        return try Ambiguity.pickUniqueSolution(
            self,
            states.items,
            .minimal_structural,
        );
    }

    fn initialStates(
        self: *Solver,
        partial_bindings: []const ?ExprId,
    ) !std.ArrayListUnmanaged(BranchState) {
        var states = std.ArrayListUnmanaged(BranchState){};
        try states.append(
            self.allocator,
            try BranchStateOps.initState(self, partial_bindings),
        );
        return states;
    }

    fn finalizeViewAndRuleStates(
        self: *Solver,
        states: []const BranchState,
        view: *const ViewDecl,
    ) anyerror!std.ArrayListUnmanaged(BranchState) {
        var next = try self.finalizeStructuralStates(states, .view);
        next = try self.materializeViewMatchStates(next.items);
        next = try self.applyDerivedBindings(next.items, view.derived_bindings);
        next = try self.finalizeStructuralStates(next.items, .view);
        next = try self.materializeViewMatchStates(next.items);
        try self.propagateViewBindings(next.items, view);
        next = try self.finalizeStructuralStates(next.items, .rule);
        return next;
    }

    fn applyHypConstraints(
        self: *Solver,
        states: []const BranchState,
        hyps: []const TemplateExpr,
        ref_exprs: []const ExprId,
        space: BinderSpace,
    ) anyerror!std.ArrayListUnmanaged(BranchState) {
        var constraints = std.ArrayListUnmanaged(MatchConstraint){};
        defer constraints.deinit(self.allocator);
        for (hyps, ref_exprs) |hyp, actual| {
            try constraints.append(self.allocator, .{
                .template = hyp,
                .actual = actual,
            });
        }
        return try self.applyConstraints(
            states,
            constraints.items,
            space,
            .hypothesis,
        );
    }

    fn applyConclusionConstraint(
        self: *Solver,
        states: []const BranchState,
        template: TemplateExpr,
        conclusion: ConclusionConstraint,
        space: BinderSpace,
    ) anyerror!std.ArrayListUnmanaged(BranchState) {
        return switch (conclusion) {
            .concrete => |actual| blk: {
                const constraints = [_]MatchConstraint{.{
                    .template = template,
                    .actual = actual,
                }};
                break :blk try self.applyConstraints(
                    states,
                    constraints[0..],
                    space,
                    .conclusion,
                );
            },
            .surface => |actual| try self.applySurfaceConstraint(
                states,
                template,
                actual,
                space,
            ),
        };
    }

    fn applyConstraints(
        self: *Solver,
        states: []const BranchState,
        constraints: []const MatchConstraint,
        space: BinderSpace,
        region: ConstraintRegion,
    ) anyerror!std.ArrayListUnmanaged(BranchState) {
        var current = std.ArrayListUnmanaged(BranchState){};
        try current.appendSlice(self.allocator, states);

        for (constraints, 0..) |constraint, constraint_idx| {
            var next = std.ArrayListUnmanaged(BranchState){};
            for (current.items) |state| {
                const matches = try StructuralMatcher.matchExpr(
                    self,
                    constraint.template,
                    constraint.actual,
                    space,
                    state,
                );
                try next.appendSlice(self.allocator, matches);
                const may_need_symbolic_view = space == .view and
                    !try self.templateContainsStructuralCombiner(
                        constraint.template,
                    );
                if ((matches.len == 0 or may_need_symbolic_view) and
                    space == .view)
                {
                    if (try self.matchViewConstraintSymbolically(
                        state,
                        constraint,
                    )) |new_state| {
                        try next.append(self.allocator, new_state);
                    }
                }
            }
            if (next.items.len == 0) {
                self.failure = .{
                    .region = switch (region) {
                        .hypothesis => .{ .hypothesis = constraint_idx },
                        .conclusion => .conclusion,
                    },
                    .actual = constraint.actual,
                };
                return error.UnifyMismatch;
            }
            current = next;
        }
        return current;
    }

    fn applySurfaceConstraint(
        self: *Solver,
        states: []const BranchState,
        template: TemplateExpr,
        actual: *const Expr,
        space: BinderSpace,
    ) anyerror!std.ArrayListUnmanaged(BranchState) {
        var next = std.ArrayListUnmanaged(BranchState){};
        for (states) |state| {
            const matches = try self.matchSurfaceExpr(
                template,
                actual,
                space,
                state,
            );
            try next.appendSlice(self.allocator, matches);
        }
        if (next.items.len == 0) {
            self.failure = .{ .region = .conclusion, .actual = null };
            return error.UnifyMismatch;
        }
        return next;
    }

    fn matchSurfaceExpr(
        self: *Solver,
        template: TemplateExpr,
        actual: *const Expr,
        space: BinderSpace,
        state: BranchState,
    ) anyerror![]BranchState {
        if (actual.* == .hole) {
            const out = try self.allocator.alloc(BranchState, 1);
            out[0] = try BranchStateOps.cloneState(self, state);
            return out;
        }

        if (!SurfaceExpr.containsHole(actual)) {
            const actual_id = try self.theorem.internParsedExpr(actual);
            return try StructuralMatcher.matchExpr(
                self,
                template,
                actual_id,
                space,
                state,
            );
        }

        return switch (template) {
            .binder => blk: {
                const out = try self.allocator.alloc(BranchState, 1);
                out[0] = try BranchStateOps.cloneState(self, state);
                break :blk out;
            },
            .app => |app| blk: {
                const actual_term = switch (actual.*) {
                    .term => |term| term,
                    .variable, .hole => break :blk &.{},
                };
                if (actual_term.id != app.term_id or
                    actual_term.args.len != app.args.len)
                {
                    break :blk &.{};
                }

                var states = std.ArrayListUnmanaged(BranchState){};
                try states.append(
                    self.allocator,
                    try BranchStateOps.cloneState(self, state),
                );
                for (app.args, actual_term.args) |tmpl_arg, actual_arg| {
                    var next = std.ArrayListUnmanaged(BranchState){};
                    for (states.items) |current| {
                        const matches = try self.matchSurfaceExpr(
                            tmpl_arg,
                            actual_arg,
                            space,
                            current,
                        );
                        try next.appendSlice(self.allocator, matches);
                    }
                    if (next.items.len == 0) break :blk &.{};
                    states = next;
                }
                break :blk try states.toOwnedSlice(self.allocator);
            },
        };
    }

    fn templateContainsStructuralCombiner(
        self: *Solver,
        template: TemplateExpr,
    ) anyerror!bool {
        return switch (template) {
            .binder => false,
            .app => |app| blk: {
                if ((try self.registry.resolveStructuralCombiner(
                    self.env,
                    app.term_id,
                )) != null) {
                    break :blk true;
                }
                for (app.args) |arg| {
                    if (try self.templateContainsStructuralCombiner(arg)) {
                        break :blk true;
                    }
                }
                break :blk false;
            },
        };
    }

    fn matchViewConstraintSymbolically(
        self: *Solver,
        state: BranchState,
        constraint: MatchConstraint,
    ) anyerror!?BranchState {
        const seed_state = state.view_match_state orelse return null;
        const view = self.view orelse return null;

        const def_ops = self.defOpsContext();

        var session = try def_ops.beginRuleMatchFromSeedState(
            view.arg_infos,
            &seed_state,
        );
        defer session.deinit();

        if (!try session.matchTransparentOrSemantic(
            constraint.template,
            constraint.actual,
        )) {
            return null;
        }

        var new_state = try BranchStateOps.cloneState(self, state);
        try ViewState.syncFromSession(self.allocator, &new_state, &session);
        return new_state;
    }

    fn materializeViewMatchStates(
        self: *Solver,
        states: []const BranchState,
    ) anyerror!std.ArrayListUnmanaged(BranchState) {
        var next = std.ArrayListUnmanaged(BranchState){};
        for (states) |state| {
            var new_state = try BranchStateOps.cloneState(self, state);
            ViewState.syncConcreteBindingsIntoSeedState(
                self.allocator,
                &new_state,
            );
            try self.materializeViewMatchState(&new_state);
            try next.append(self.allocator, new_state);
        }
        return next;
    }

    fn materializeViewMatchState(
        self: *Solver,
        state: *BranchState,
    ) anyerror!void {
        const seed_state = state.view_match_state orelse return;
        const view = self.view orelse return;

        const def_ops = self.defOpsContext();

        var session = try def_ops.beginRuleMatchFromSeedState(
            view.arg_infos,
            &seed_state,
        );
        defer session.deinit();

        try ViewState.syncFromSession(self.allocator, state, &session);
    }

    fn applyDerivedBindings(
        self: *Solver,
        states: []const BranchState,
        derived_bindings: []const DerivedBinding,
    ) anyerror!std.ArrayListUnmanaged(BranchState) {
        var next = std.ArrayListUnmanaged(BranchState){};
        var first_err: ?anyerror = null;
        for (states) |state| {
            var new_state = try BranchStateOps.cloneState(self, state);
            if (new_state.view_bindings == null) {
                try next.append(self.allocator, new_state);
                continue;
            }
            {
                var snapshot = try self.derivedBindingSnapshot(&new_state);
                // `dummy_witnesses` was materialized on the def_ops session's
                // real allocator, so it must be freed there, not on the arena.
                defer snapshot.deinit(self.real_allocator);

                DerivedBindings.applyDerivedBindings(
                    self.theorem,
                    self.env,
                    self.registry,
                    snapshot.value,
                    derived_bindings,
                    self.view.?.arg_names,
                    false,
                ) catch |err| {
                    if (first_err == null) first_err = err;
                    continue;
                };
            }
            ViewState.syncConcreteBindingsIntoSeedState(
                self.allocator,
                &new_state,
            );
            try next.append(self.allocator, new_state);
        }
        if (next.items.len == 0) return first_err orelse error.UnifyMismatch;
        return next;
    }

    const DerivedBindingSnapshot = struct {
        value: DerivedBindings.MatchSnapshot,

        pub fn deinit(
            self: *DerivedBindingSnapshot,
            allocator: std.mem.Allocator,
        ) void {
            if (self.value.dummy_witnesses) |witnesses| {
                allocator.free(witnesses);
            }
        }
    };

    fn derivedBindingSnapshot(
        self: *Solver,
        state: *BranchState,
    ) anyerror!DerivedBindingSnapshot {
        const view_bindings = state.view_bindings.?;
        const seed_state = if (state.view_match_state) |*match_state|
            match_state
        else
            return .{ .value = .{ .view_bindings = view_bindings } };
        const view = self.view orelse {
            return .{ .value = .{ .view_bindings = view_bindings } };
        };

        const def_ops = self.defOpsContext();

        var session = try def_ops.beginRuleMatchFromSeedState(
            view.arg_infos,
            seed_state,
        );
        defer session.deinit();

        const dummy_witnesses = try session.materializeDummyWitnesses();
        errdefer self.real_allocator.free(dummy_witnesses);

        return .{ .value = .{
            .view_bindings = view_bindings,
            .view_seeds = seed_state.bindings,
            .dummy_witnesses = dummy_witnesses,
        } };
    }

    fn finalizeStructuralStates(
        self: *Solver,
        states: []const BranchState,
        space: BinderSpace,
    ) anyerror!std.ArrayListUnmanaged(BranchState) {
        var next = std.ArrayListUnmanaged(BranchState){};
        var first_err: ?anyerror = null;
        for (states) |state| {
            const finalized = self.finalizeStructuralBindings(
                state,
                space,
            ) catch |err| {
                if (first_err == null) first_err = err;
                continue;
            };
            try next.appendSlice(self.allocator, finalized);
        }
        if (next.items.len == 0) return first_err orelse error.UnifyMismatch;
        return next;
    }

    fn finalizeStructuralBindings(
        self: *Solver,
        state: BranchState,
        space: BinderSpace,
    ) anyerror![]BranchState {
        var out = std.ArrayListUnmanaged(BranchState){};
        try self.searchStructuralFinalizations(state, space, &out);
        if (out.items.len == 0) return error.UnifyMismatch;
        return try out.toOwnedSlice(self.allocator);
    }

    fn searchStructuralFinalizations(
        self: *Solver,
        state: BranchState,
        space: BinderSpace,
        out: *std.ArrayListUnmanaged(BranchState),
    ) anyerror!void {
        var current = try BranchStateOps.cloneState(self, state);
        if (!try self.partialStructuralStateCompatible(&current, space)) {
            return;
        }

        if (nextUnresolvedStructuralObligation(&current, space)) |idx| {
            const obligations = BranchStateOps.getStructuralObligations(&current, space);
            const branches = try StructuralObligationSolver.solveStructuralObligation(
                self,
                current,
                space,
                obligations[idx],
            );
            for (branches) |branch| {
                try self.searchStructuralFinalizations(branch, space, out);
            }
            return;
        }

        try self.fillDeterministicStructuralBindings(&current, space);
        if (!try self.allStructuralObligationsSatisfied(&current, space)) {
            return;
        }
        try StructuralStateUpdates.appendUniqueStateForSpace(
            self,
            out,
            current,
            space,
        );
    }

    pub fn partialStructuralStateCompatible(
        self: *Solver,
        state: *BranchState,
        space: BinderSpace,
    ) anyerror!bool {
        const bindings = BranchStateOps.getBindings(state, space);
        const intervals = BranchStateOps.getStructuralIntervals(state, space);
        for (intervals, 0..) |maybe_interval, idx| {
            const interval = maybe_interval orelse continue;
            const binding = bindings[idx] orelse continue;
            if (!try StructuralIntervals.exprWithinInterval(self, binding, interval)) {
                return false;
            }
        }
        const obligations = BranchStateOps.getStructuralObligations(state, space);
        for (obligations) |obligation| {
            if (!try StructuralIntervals.obligationCompatibleWithState(
                self,
                state,
                space,
                obligation,
            )) {
                return false;
            }
        }
        return true;
    }

    fn nextUnresolvedStructuralObligation(
        state: *BranchState,
        space: BinderSpace,
    ) ?usize {
        const bindings = BranchStateOps.getBindings(state, space);
        const obligations = BranchStateOps.getStructuralObligations(state, space);
        var best_idx: ?usize = null;
        var best_unbound: usize = std.math.maxInt(usize);
        for (obligations, 0..) |obligation, idx| {
            var unbound: usize = 0;
            for (obligation.binder_idxs) |binder_idx| {
                if (binder_idx >= bindings.len or
                    bindings[binder_idx] == null)
                {
                    unbound += 1;
                }
            }
            if (unbound != 0 and unbound < best_unbound) {
                best_unbound = unbound;
                best_idx = idx;
            }
        }
        return best_idx;
    }

    fn fillDeterministicStructuralBindings(
        self: *Solver,
        state: *BranchState,
        space: BinderSpace,
    ) anyerror!void {
        const bindings = BranchStateOps.getBindings(state, space);
        const intervals = BranchStateOps.getStructuralIntervals(state, space);
        for (intervals, 0..) |maybe_interval, idx| {
            const interval = maybe_interval orelse continue;
            if (bindings[idx]) |existing| {
                if (!try StructuralIntervals.exprWithinInterval(self, existing, interval)) {
                    return error.UnifyMismatch;
                }
                continue;
            }
            bindings[idx] = interval.lower_expr;
        }
    }

    fn allStructuralObligationsSatisfied(
        self: *Solver,
        state: *BranchState,
        space: BinderSpace,
    ) anyerror!bool {
        const bindings = BranchStateOps.getBindings(state, space);
        const obligations = BranchStateOps.getStructuralObligations(state, space);
        for (obligations) |obligation| {
            for (obligation.binder_idxs) |binder_idx| {
                if (binder_idx >= bindings.len or
                    bindings[binder_idx] == null)
                {
                    return false;
                }
            }
            if (!try StructuralIntervals.obligationSatisfied(self, bindings, obligation)) {
                return false;
            }
        }
        return true;
    }

    fn propagateViewBindings(
        self: *Solver,
        states: []BranchState,
        view: *const ViewDecl,
    ) anyerror!void {
        for (states) |*state| {
            const view_bindings = state.view_bindings orelse continue;
            for (view.binder_map, 0..) |mapping, vi| {
                const rule_idx = mapping orelse continue;
                const binding = view_bindings[vi] orelse continue;
                if (state.rule_bindings[rule_idx]) |existing| {
                    if (!try SemanticCompare.bindingCompatible(self, existing, binding)) {
                        return error.ViewBindingConflict;
                    }
                } else {
                    if (!try StructuralIntervals.bindingSatisfiesStructural(
                        self,
                        state,
                        .rule,
                        rule_idx,
                        binding,
                    )) {
                        return error.ViewBindingConflict;
                    }
                    state.rule_bindings[rule_idx] = binding;
                }
            }
        }
    }
};
