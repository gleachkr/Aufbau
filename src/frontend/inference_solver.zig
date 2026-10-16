const std = @import("std");
const ArenaAllocator = @import("./arena_allocator.zig").ArenaAllocator;
const GlobalEnv = @import("./env.zig").GlobalEnv;
const RuleDecl = @import("./env.zig").RuleDecl;
const Expr = @import("../trusted/expressions.zig").Expr;
const Rules = @import("./rules.zig");
const TemplateExpr = Rules.TemplateExpr;
const ExprModule = @import("./expr.zig");
const ExprId = @import("./expr.zig").ExprId;
const TheoremContext = @import("./expr.zig").TheoremContext;
const RewriteRegistry = @import("./rewrite_registry.zig").RewriteRegistry;
const CompilerDiag = @import("./diag.zig");
const ArgInfo = @import("./parse_recovery.zig").ArgInfo;
const ViewDecl = @import("./views.zig").ViewDecl;
const DerivedBinding = @import("./views.zig").DerivedBinding;
const Canonicalizer = @import("./normalizer.zig").Canonicalizer;
const DerivedBindings = @import("./derived_bindings.zig");
const DefOps = @import("./def_ops.zig");
const DebugTrace = @import("./debug.zig");
const DebugConfig = DebugTrace.DebugConfig;
const BranchStateOps = @import("./inference_solver/branch_state.zig");
const SemanticCompare = @import("./inference_solver/semantic_compare.zig");
const StructuralIntervals =
    @import("./inference_solver/intervals.zig");
const StructuralMatcher = @import("./inference_solver/matcher.zig");
const SessionSync = @import("./inference_solver/session_sync.zig");
const StructuralObligationSolver =
    @import("./inference_solver/obligation_solver.zig");
const StructuralStateUpdates =
    @import("./inference_solver/state_updates.zig");
const Ambiguity = @import("./inference_solver/ambiguity_report.zig");
const StructuralItems = @import("./inference_solver/items.zig");
const types = @import("./inference_solver/types.zig");
const BinderSpace = types.BinderSpace;
const MatchConstraint = types.MatchConstraint;
const StructuralJointObligation = types.StructuralJointObligation;
const BranchState = types.BranchState;

const SolutionPreference = Ambiguity.SolutionPreference;
pub const AmbiguityReport = Ambiguity.AmbiguityReport;

const ConclusionConstraint = union(enum) {
    concrete: ExprId,
    /// An interned conclusion whose placeholders are holes: a holey line
    /// (`Holes.internWithLineHoles`) or an inline minor's hint from a holey
    /// goal.
    holey: ExprId,
    /// A whole-line hole: the conclusion constrains nothing.
    unconstrained,
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
    state_arena: ArenaAllocator,
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
    /// Largest branch population any single constraint left behind during
    /// this solve. Observability only: an `InferenceStatsSink` reads it so a
    /// test can pin that a premise extends the population instead of
    /// multiplying it.
    peak_branches: usize = 0,
    /// The derived-binding failure `derivedBindingsFeasible` last pruned a
    /// branch with, while matching the current constraint. A constraint
    /// that leaves no branch fails with it when set, rather than as a
    /// mismatch: some reading did match, and a `@recover` ruled it out.
    pruned_by: ?anyerror = null,
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
    /// Search work ceiling, set by the caller when the solve runs under a
    /// budgeted search (`CompilerContext.work_budget`). Polled by every
    /// branch clone and semantic compare (`checkBudget`), the two operations
    /// a branch fan-out multiplies, so a solve whose population blows up
    /// aborts at the budget instead of running to completion. Null on the
    /// compile path.
    budget: ?ExprModule.WorkBudget = null,
    /// Fresh variables for a `@recover` whose hole the pattern lacks
    /// (`DerivedBindings.FreshVar`). Null leaves such a target unsolved.
    fresh_var: ?DerivedBindings.FreshVar = null,
    /// Source order of the bag members this solve matched, so remainder
    /// binders are rebuilt in it (`StructuralItems.MemberOrder`).
    member_order: StructuralItems.MemberOrder = .{},

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
            .state_arena = ArenaAllocator.init(allocator),
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
                {},
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
        self.member_order.deinit(self.real_allocator);
        self.canonicalizer.deinit();
        if (self.def_ops_ctx) |*ctx| ctx.deinit();
        if (self.def_ops_ctx_plain) |*ctx| ctx.deinit();
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

    /// Abort the solve if the installed search budget is spent.
    pub fn checkBudget(self: *const Solver) error{SearchBudgetExhausted}!void {
        if (self.budget) |budget| try budget.check();
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

    /// Solve against a conclusion whose placeholders are holes: a holey line
    /// or a holey hint. Null is a whole-line hole.
    pub fn solveHoley(
        self: *Solver,
        partial_bindings: []const ?ExprId,
        ref_exprs: []const ExprId,
        holey: ?ExprId,
    ) anyerror![]const ExprId {
        return try self.solveWithConclusion(
            partial_bindings,
            ref_exprs,
            if (holey) |expr| .{ .holey = expr } else .unconstrained,
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
        self.member_order.clear();

        var states = try self.initialStates(partial_bindings);

        if (self.view) |view| {
            // A concrete statement goes first: it binds the view's context
            // and its `@recover` patterns, so matching a premise's bag
            // member by member can drop a member no `@recover` reads
            // (`derivedBindingsFeasible`) instead of carrying every choice
            // of member to the end. A holey statement binds too little to
            // go first.
            if (conclusion == .concrete) {
                states = try self.applyConclusionConstraint(
                    states.items,
                    view.concl,
                    conclusion,
                    .view,
                );
            }
            states = try self.applyHypConstraints(
                states.items,
                view.hyps,
                ref_exprs,
                .view,
            );
            if (conclusion != .concrete) {
                states = try self.applyConclusionConstraint(
                    states.items,
                    view.concl,
                    conclusion,
                    .view,
                );
            }
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
            states = try self.materializeMatchStates(states.items, .rule);
            states = try self.finalizeStructuralStates(states.items, .rule);
        }
        if (conclusion == .holey) {
            states = try self.keepStatesFittingHint(states.items, conclusion.holey);
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
        var states = std.ArrayListUnmanaged(BranchState).empty;
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
        next = try self.materializeMatchStates(next.items, .view);
        next = try self.applyDerivedBindings(next.items, view.derived_bindings);
        next = try self.finalizeStructuralStates(next.items, .view);
        next = try self.materializeMatchStates(next.items, .view);
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
        var constraints = std.ArrayListUnmanaged(MatchConstraint).empty;
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
            .holey => |actual| try self.applyHoleyConstraint(
                states,
                template,
                actual,
                space,
            ),
            .unconstrained => blk: {
                var next = std.ArrayListUnmanaged(BranchState).empty;
                try next.appendSlice(self.allocator, states);
                break :blk next;
            },
        };
    }

    fn applyConstraints(
        self: *Solver,
        states: []const BranchState,
        constraints: []const MatchConstraint,
        space: BinderSpace,
        region: ConstraintRegion,
    ) anyerror!std.ArrayListUnmanaged(BranchState) {
        var current = std.ArrayListUnmanaged(BranchState).empty;
        try current.appendSlice(self.allocator, states);

        for (constraints, 0..) |constraint, constraint_idx| {
            self.pruned_by = null;
            var next = std.ArrayListUnmanaged(BranchState).empty;
            for (current.items) |state| {
                const matches = try StructuralMatcher.matchExpr(
                    self,
                    constraint.template,
                    constraint.actual,
                    space,
                    state,
                );
                try next.appendSlice(self.allocator, matches);
                // When structural matching finds nothing, a branch carrying
                // session state tries the whole constraint symbolically.
                // A structural success is not re-derived here: for a bare
                // binder it already ran the same session match, and a
                // second copy per premise doubles the branch population.
                if (matches.len == 0 and
                    BranchStateOps.matchState(&state, space) != null)
                {
                    if (try self.matchConstraintSymbolically(
                        state,
                        constraint,
                        space,
                    )) |new_state| {
                        try next.append(self.allocator, new_state);
                    }
                }
            }
            self.peak_branches = @max(self.peak_branches, next.items.len);
            if (next.items.len == 0) {
                if (self.pruned_by) |err| return err;
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

    fn applyHoleyConstraint(
        self: *Solver,
        states: []const BranchState,
        template: TemplateExpr,
        actual: ExprId,
        space: BinderSpace,
    ) anyerror!std.ArrayListUnmanaged(BranchState) {
        var next = std.ArrayListUnmanaged(BranchState).empty;
        for (states) |state| {
            const matches = try self.matchHoleyExpr(template, actual, space, state);
            try next.appendSlice(self.allocator, matches);
        }
        if (next.items.len == 0) {
            self.failure = .{ .region = .conclusion, .actual = null };
            return error.UnifyMismatch;
        }
        return next;
    }

    /// Match against an interned expression whose placeholders are holes: a
    /// placeholder matches anything, a binder facing a subterm with
    /// one fixes nothing, and a placeholder-free subterm matches structurally.
    fn matchHoleyExpr(
        self: *Solver,
        template: TemplateExpr,
        actual: ExprId,
        space: BinderSpace,
        state: BranchState,
    ) anyerror![]BranchState {
        if (!self.theorem.containsPlaceholder(actual)) {
            return try StructuralMatcher.matchExpr(self, template, actual, space, state);
        }
        const node = self.theorem.interner.node(actual);
        if (node.* == .placeholder or template == .binder) {
            const out = try self.allocator.alloc(BranchState, 1);
            out[0] = try BranchStateOps.cloneState(self, state);
            return out;
        }
        const app = template.app;
        if (node.* != .app or node.app.term_id != app.term_id or
            node.app.args.len != app.args.len) return &.{};

        var states = std.ArrayListUnmanaged(BranchState).empty;
        try states.append(self.allocator, try BranchStateOps.cloneState(self, state));
        for (app.args, node.app.args) |tmpl_arg, actual_arg| {
            var next = std.ArrayListUnmanaged(BranchState).empty;
            for (states.items) |current| {
                const matches = try self.matchHoleyExpr(tmpl_arg, actual_arg, space, current);
                try next.appendSlice(self.allocator, matches);
            }
            if (next.items.len == 0) return &.{};
            states = next;
        }
        return try states.toOwnedSlice(self.allocator);
    }

    /// Drop each complete branch whose conclusion contradicts the visible
    /// structure of the holey `hint`. `matchHoleyExpr` lets a binder facing
    /// a holey subterm take nothing from it, so against `p , p → q ⊢ ‹hole› → q`
    /// a branch can split `ax`'s `g , a ⊢ a` as `a := p`, which the visible
    /// `→ q` rules out.
    fn keepStatesFittingHint(
        self: *Solver,
        states: []const BranchState,
        hint: ExprId,
    ) anyerror!std.ArrayListUnmanaged(BranchState) {
        const bindings = try self.allocator.alloc(ExprId, self.rule.args.len);
        var next = std.ArrayListUnmanaged(BranchState).empty;
        for (states) |state| {
            const complete = for (state.rule_bindings, bindings) |binding, *slot| {
                slot.* = binding orelse break false;
            } else true;
            if (complete) {
                const concl = try self.theorem.instantiateTemplate(self.rule.concl, bindings);
                if (!try self.fitsHoleySkeleton(concl, hint)) continue;
            }
            try next.append(self.allocator, state);
        }
        if (next.items.len == 0) {
            self.failure = .{ .region = .conclusion, .actual = null };
            return error.UnifyMismatch;
        }
        return next;
    }

    /// True unless `expr` and `hint` differ where the hint shows something:
    /// a hole matches anything, and a hole-free part must agree. That part
    /// was not necessarily matched already: a rule variable facing a holey
    /// subterm took nothing from it. Under an ACUI combiner members line up
    /// only modulo order, so it is not checked.
    fn fitsHoleySkeleton(self: *Solver, expr: ExprId, hint: ExprId) anyerror!bool {
        if (expr == hint) return true;
        if (!self.theorem.containsPlaceholder(hint)) {
            return try SemanticCompare.bindingCompatible(self, expr, hint);
        }
        const hint_node = self.theorem.interner.node(hint);
        if (hint_node.* != .app) return true;
        const node = self.theorem.interner.node(expr);
        if (node.* != .app or node.app.term_id != hint_node.app.term_id or
            node.app.args.len != hint_node.app.args.len) return false;
        if (self.registry.hasStructuralCombiner(hint_node.app.term_id)) return true;
        for (node.app.args, hint_node.app.args) |arg, hint_arg| {
            if (!try self.fitsHoleySkeleton(arg, hint_arg)) return false;
        }
        return true;
    }

    pub fn argInfosForSpace(
        self: *const Solver,
        space: BinderSpace,
    ) []const ArgInfo {
        return switch (space) {
            .rule => self.rule.args,
            .view => self.view.?.arg_infos,
        };
    }

    fn matchConstraintSymbolically(
        self: *Solver,
        state: BranchState,
        constraint: MatchConstraint,
        space: BinderSpace,
    ) anyerror!?BranchState {
        const seed_state = BranchStateOps.matchState(&state, space) orelse {
            return null;
        };

        const def_ops = self.defOpsContext();

        var session = try def_ops.beginRuleMatchFromSeedState(
            self.argInfosForSpace(space),
            seed_state,
        );
        defer session.deinit();

        if (!try session.matchTransparentOrSemantic(
            constraint.template,
            constraint.actual,
        )) {
            return null;
        }

        var new_state = try BranchStateOps.cloneState(self, state);
        try SessionSync.syncFromSession(
            self.allocator,
            &new_state,
            space,
            &session,
        );
        return new_state;
    }

    /// Push each branch's concrete bindings into its session state (if it
    /// has one) and read back whatever that state now resolves.
    fn materializeMatchStates(
        self: *Solver,
        states: []const BranchState,
        space: BinderSpace,
    ) anyerror!std.ArrayListUnmanaged(BranchState) {
        var next = std.ArrayListUnmanaged(BranchState).empty;
        for (states) |state| {
            if (BranchStateOps.matchState(&state, space) == null) {
                try next.append(self.allocator, state);
                continue;
            }
            var new_state = try BranchStateOps.cloneState(self, state);
            SessionSync.syncConcreteBindingsIntoSeedState(
                self.allocator,
                &new_state,
                space,
            );
            try self.materializeMatchState(&new_state, space);
            try next.append(self.allocator, new_state);
        }
        return next;
    }

    fn materializeMatchState(
        self: *Solver,
        state: *BranchState,
        space: BinderSpace,
    ) anyerror!void {
        const seed_state = BranchStateOps.matchState(state, space) orelse return;

        const def_ops = self.defOpsContext();

        var session = try def_ops.beginRuleMatchFromSeedState(
            self.argInfosForSpace(space),
            seed_state,
        );
        defer session.deinit();

        try SessionSync.syncFromSession(self.allocator, state, space, &session);
    }

    fn applyDerivedBindings(
        self: *Solver,
        states: []const BranchState,
        derived_bindings: []const DerivedBinding,
    ) anyerror!std.ArrayListUnmanaged(BranchState) {
        var next = std.ArrayListUnmanaged(BranchState).empty;
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
            SessionSync.syncConcreteBindingsIntoSeedState(
                self.allocator,
                &new_state,
                .view,
            );
            try next.append(self.allocator, new_state);
        }
        if (next.items.len == 0) return first_err orelse error.UnifyMismatch;
        return next;
    }

    /// False when a `@recover` of the view already fails on this branch:
    /// its source, pattern and hole are all bound and no instance of the
    /// pattern is the source. Only a `@recover` that alone decides its
    /// target is tried (`recoverDecidesTarget`): later constraints then
    /// only bind more, so every completion of the branch fails there too.
    pub fn derivedBindingsFeasible(
        self: *Solver,
        state: BranchState,
        space: BinderSpace,
    ) anyerror!bool {
        if (space != .view) return true;
        const view = self.view orelse return true;
        const bindings = state.view_bindings orelse return true;
        for (view.derived_bindings, 0..) |binding, binding_idx| {
            const recover = switch (binding) {
                .recover => |value| value,
                .abstract => continue,
            };
            if (bindings[recover.target_view_idx] != null or
                bindings[recover.source_view_idx] == null or
                bindings[recover.pattern_view_idx] == null or
                bindings[recover.hole_view_idx] == null) continue;
            if (!recoverDecidesTarget(
                view,
                binding_idx,
                recover.target_view_idx,
            )) continue;
            var probe = state;
            probe.view_bindings = try self.allocator.dupe(?ExprId, bindings);
            defer self.allocator.free(probe.view_bindings.?);
            var snapshot = try self.derivedBindingSnapshot(&probe);
            defer snapshot.deinit(self.real_allocator);
            // A probe takes no fresh variable: one would stay declared in
            // the theorem for a branch that may be dropped, and a pattern
            // without the hole never rules a branch out anyway.
            snapshot.value.fresh_var = null;
            DerivedBindings.applyDerivedBindings(
                self.theorem,
                self.env,
                self.registry,
                snapshot.value,
                &.{binding},
                view.arg_names,
                false,
            ) catch |err| {
                if (!DerivedBindings.isDerivedBindingFailure(err)) return err;
                self.pruned_by = err;
                return false;
            };
        }
        return true;
    }

    /// Whether nothing but the `@recover` at `binding_idx` may bind its
    /// `target`: no view premise or statement mentions it, and no other
    /// derived binding solves it. A `@recover` skips a target that is
    /// already bound, so otherwise its failure now need not stand.
    fn recoverDecidesTarget(
        view: *const ViewDecl,
        binding_idx: usize,
        target: usize,
    ) bool {
        if (Rules.templateMentionsBinder(view.concl, target)) return false;
        for (view.hyps) |hyp| {
            if (Rules.templateMentionsBinder(hyp, target)) return false;
        }
        for (view.derived_bindings, 0..) |other, other_idx| {
            if (other_idx != binding_idx and
                DerivedBindings.solvesBinder(other, target)) return false;
        }
        return true;
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
            return .{ .value = .{
                .view_bindings = view_bindings,
                .fresh_var = self.fresh_var,
            } };
        const view = self.view orelse {
            return .{ .value = .{
                .view_bindings = view_bindings,
                .fresh_var = self.fresh_var,
            } };
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
            .fresh_var = self.fresh_var,
        } };
    }

    fn finalizeStructuralStates(
        self: *Solver,
        states: []const BranchState,
        space: BinderSpace,
    ) anyerror!std.ArrayListUnmanaged(BranchState) {
        var next = std.ArrayListUnmanaged(BranchState).empty;
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
        var out = std.ArrayListUnmanaged(BranchState).empty;
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
