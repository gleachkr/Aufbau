//! The search core: a backward prover over the theory's own rules, in the
//! shape of blast (`docs/design_notes/shared_witness.md`, revision 2).
//!
//! It searches ground goals with the rules whose conclusion fixes every
//! binder but the quantifier witnesses and cuts (`catalog.zig`), over
//! `@acui` bags matched member by member, commutative ones in any order
//! and sequences in theirs (`terms.zig`),
//! unfolding a definition in a goal or fact where its head does not match,
//! and trying a goal in its `@rewrite` normal form. Its facts are the pool
//! refs and the ground facts forward saturation derived from them, each
//! standing for its recipe. A γ witness or cut is a witness variable closed
//! by unification, a δ one (or a definition's dummy) an eigenvariable whose
//! name waits until the proof needs one (`wvars.zig`). It runs before the
//! generation ladder (`GenerateOptions.core`, on by default), which still
//! runs when the core abstains or misses.
//!
//! The run works in a clone of the call's theorem, discarded at the end.
//! The proof record is rendered as one `RuleApplication` tree with every
//! binding explicit, a witness variable or eigenvariable left unbound
//! named from its sort's `@vars` pool, and the checker validates it once
//! (D5): the checker stays the only authority on what the core returns.

const std = @import("std");
const ArenaAllocator = @import("../../../arena_allocator.zig").ArenaAllocator;
const ExprId = @import("../../../expr.zig").ExprId;
const TheoremContext = @import("../../../expr.zig").TheoremContext;
const ProofScript = @import("../../../proof_script.zig");
const RuleApplication = ProofScript.RuleApplication;
const CompilerContext = @import("../../context.zig").CompilerContext;
const types = @import("../types.zig");
const Context = types.Context;
const NameExprMap = types.NameExprMap;
const SearchCounters = types.SearchCounters;
const refs_mod = @import("../refs.zig");
const forward = @import("../forward.zig");
const candidate_mod = @import("../candidate.zig");
const catalog_mod = @import("./catalog.zig");
const Terms = @import("./terms.zig").Terms;
const WVars = @import("./wvars.zig").WVars;
const Keys = @import("./keys.zig").Keys;
const prover_mod = @import("./prover.zig");
const Prover = prover_mod.Prover;
const Node = prover_mod.Node;

pub const Request = struct {
    compiler: *CompilerContext,
    context: *const Context,
    /// The call's working theorem. The core works in a clone of it.
    theorem: *const TheoremContext,
    theorem_vars: *const NameExprMap,
    /// The theorem the pool refs are stated in.
    pool_theorem: *const TheoremContext,
    pool: []const refs_mod.RefPoolEntry,
    /// Facts forward saturation derived from the pool; those forward rules
    /// derived that hold no universal meta join the pool facts.
    derived: ?*types.DerivedPool = null,
    goal: ExprId,
    max_depth: usize,
    stack_guard_bytes: usize,
    budget: ?*types.GlobalBudget,
    counters: ?*SearchCounters,
    /// Owns the returned application.
    out: std.mem.Allocator,
    scratch: std.mem.Allocator,
};

pub const Result = union(enum) {
    /// The goal is outside what the core searches.
    abstained,
    /// No proof within `max_depth`.
    missed,
    found: struct { application: RuleApplication, depth: usize },
};

pub fn run(request: Request) !Result {
    var arena = ArenaAllocator.init(request.scratch);
    defer arena.deinit();
    var theorem = try request.theorem.clone();
    defer theorem.deinit();
    var wvars = WVars{
        .allocator = request.scratch,
        .arena = arena.allocator(),
        .context = request.context,
        .theorem = &theorem,
    };
    defer wvars.deinit();
    var terms = try Terms.init(request.scratch, request.context, &theorem, &wvars);
    defer terms.deinit();
    if (!try terms.supported(request.goal)) return .abstained;
    const goal = terms.canonical(request.goal) catch |err| switch (err) {
        error.Unsupported => return .abstained,
        else => |e| return e,
    };

    var catalog = try catalog_mod.build(request.scratch, request.context);
    defer catalog.deinit();
    const facts = try poolFacts(request, &theorem, &terms, arena.allocator());
    var keys = Keys{
        .allocator = request.scratch,
        .arena = arena.allocator(),
        .terms = &terms,
        .wvars = &wvars,
        .fact_vars = &.{},
    };
    defer keys.deinit();
    keys.fact_vars = try factVariables(&keys, facts, arena.allocator());

    var close_out = CloseOut{ .request = request, .theorem = &theorem, .wvars = &wvars };
    var prover = Prover{
        .allocator = request.scratch,
        .arena = arena.allocator(),
        .context = request.context,
        .terms = &terms,
        .wvars = &wvars,
        .keys = &keys,
        .theorem_vars = request.theorem_vars,
        .catalog = &catalog,
        .facts = facts,
        .budget = request.budget,
        .close_out = .{ .ctx = &close_out, .tryFn = CloseOut.tryRoot },
        .stack_base = @frameAddress(),
        .stack_guard_bytes = request.stack_guard_bytes,
    };
    defer prover.deinit();
    close_out.prover = &prover;
    defer if (request.counters) |c| {
        c.core_nodes += prover.stats.nodes;
        c.core_rejects += prover.stats.rejects;
    };

    for (1..request.max_depth + 1) |depth| {
        if (try prover.solve(goal, depth)) {
            return .{ .found = .{ .application = close_out.found.?, .depth = depth } };
        }
    }
    return .missed;
}

/// The pool facts the core can close a goal with, canonical, then the
/// ground facts forward rules derived, each standing for its recipe.
fn poolFacts(request: Request, theorem: *TheoremContext, terms: *Terms, arena: std.mem.Allocator) ![]const prover_mod.Fact {
    var facts = std.ArrayListUnmanaged(prover_mod.Fact).empty;
    for (request.pool) |entry| {
        const expr = refs_mod.sourceRefExpr(request.context, request.pool_theorem, entry.ref) catch continue;
        if (!try terms.supported(expr)) continue;
        const canonical = terms.canonical(expr) catch |err| switch (err) {
            error.Unsupported => continue,
            else => |e| return e,
        };
        try facts.append(arena, .{ .expr = canonical, .ref = entry.ref });
    }
    if (request.derived) |dpool| for (dpool.refs) |*dref| {
        // A trigger seed has no sources: an axiom instance the closers
        // already give.
        if (dref.sources.len == 0 or dref.has_universal_meta) continue;
        if (!try terms.supported(dref.shape)) continue;
        const canonical = terms.canonical(dref.shape) catch |err| switch (err) {
            error.Unsupported => continue,
            else => |e| return e,
        };
        const application = (try forward.materializeApplication(
            dpool,
            request.context,
            theorem,
            request.theorem_vars,
            null,
            dref,
            null,
        )) orelse continue;
        try facts.append(arena, .{ .expr = canonical, .ref = .{ .application = application } });
    };
    return facts.items;
}

/// The variables `facts` mention, sorted.
fn factVariables(keys: *Keys, facts: []const prover_mod.Fact, arena: std.mem.Allocator) ![]const ExprId {
    var out = std.ArrayListUnmanaged(ExprId).empty;
    for (facts) |fact| {
        for (try keys.variables(fact.expr)) |variable| {
            if (std.mem.indexOfScalar(ExprId, out.items, variable) == null) try out.append(arena, variable);
        }
    }
    std.mem.sort(ExprId, out.items, {}, std.sort.asc(ExprId));
    return out.items;
}

/// Renders a finished proof record and checks it against the goal.
const CloseOut = struct {
    request: Request,
    theorem: *TheoremContext,
    wvars: *WVars,
    /// Set once the prover exists; names come from its `@vars` pools.
    prover: *Prover = undefined,
    /// Names of the wvars left unbound, by wvar index, during one render.
    names: std.AutoHashMapUnmanaged(u32, ExprId) = .empty,
    found: ?RuleApplication = null,

    fn tryRoot(ctx: *anyopaque, root: *const Node) prover_mod.Error!bool {
        const self: *CloseOut = @ptrCast(@alignCast(ctx));
        // A goal a pool fact states is direct `exact?`'s to report; one a
        // derived fact states is proved by the fact's recipe.
        switch (root.step) {
            .rule => {},
            .ref => |ref| if (ref != .application) return false,
        }
        const request = self.request;
        var namer = forward.Namer.init(request.scratch);
        defer namer.deinit();
        try namer.collectTheoremVars(self.theorem, request.theorem_vars);
        defer self.names.clearAndFree(request.scratch);
        const mark = self.wvars.mark();
        defer self.wvars.rollback(mark);
        if (!try self.nameEigens(root)) return false;
        const application = switch (root.step) {
            .rule => (try self.render(&namer, root)) orelse return false,
            .ref => |ref| ref.application,
        };
        if (request.counters) |c| c.full_try_candidate_calls += 1;
        if (request.budget) |budget| try budget.spendCandidate();
        var attempt = candidate_mod.probe(
            request.compiler,
            request.context,
            application,
            .{ .concrete = request.goal },
            self.theorem,
            request.theorem_vars,
            .{ .counters = request.counters, .final_attempt = true },
        ) catch |err| switch (err) {
            error.OutOfMemory => return error.OutOfMemory,
            else => return false,
        };
        attempt.deinit();
        self.found = application;
        return true;
    }

    /// `node` as an application with every binding explicit, or null when
    /// a value has no source text (an unnamed binder or variable) or a
    /// wvar has no admissible name.
    fn render(self: *CloseOut, namer: *forward.Namer, node: *const Node) prover_mod.Error!?RuleApplication {
        const request = self.request;
        const step = node.step.rule;
        const rule = &request.context.env.rules.items[step.rule_id];
        const zero_span = ProofScript.Span{ .start = 0, .end = 0 };
        const bindings = try request.out.alloc(ProofScript.ArgBinding, step.bindings.len);
        for (bindings, step.bindings, 0..) |*binding, value, idx| {
            const name = rule.arg_names[idx] orelse return null;
            if (!try self.nameLeftovers(value)) return null;
            const resolved = try self.wvars.deref(value, &self.names);
            const text = (try namer.render(request.out, request.context, self.theorem, resolved)) orelse return null;
            binding.* = .{
                .name = name,
                .name_span = zero_span,
                .formula = .{ .text = text, .span = zero_span },
                .span = zero_span,
            };
        }
        const refs = try request.out.alloc(ProofScript.Ref, node.children.len);
        for (refs, node.children) |*ref, child| {
            ref.* = switch (child.?.step) {
                .ref => |fact| fact,
                .rule => .{ .application = (try self.render(namer, child.?)) orelse return null },
            };
        }
        return RuleApplication{
            .rule_name = rule.name,
            .rule_span = zero_span,
            .arg_bindings = bindings,
            .refs_span = if (refs.len == 0) null else zero_span,
            .refs = refs,
            .span = zero_span,
        };
    }

    /// Name every eigenvariable the proof leaves unbound, oldest first, with
    /// the first variable of its sort's `@vars` pool that its introduction
    /// goal, as named so far, does not mention. Two eigenvariables may
    /// share a name when neither goal mentions the other. False when one
    /// has no name.
    fn nameEigens(self: *CloseOut, root: *const Node) prover_mod.Error!bool {
        const scratch = self.request.scratch;
        var leftovers = std.ArrayListUnmanaged(u32).empty;
        defer leftovers.deinit(scratch);
        try self.collectLeftovers(root, &leftovers);
        const wvars = self.wvars;
        var eigens = std.ArrayListUnmanaged(u32).empty;
        defer eigens.deinit(scratch);
        for (leftovers.items) |idx| {
            if (wvars.isEigen(idx)) try eigens.append(scratch, idx);
        }
        // Indices grow with levels.
        std.mem.sort(u32, eigens.items, {}, std.sort.asc(u32));
        var shared = std.AutoHashMapUnmanaged(ExprId, void).empty;
        defer shared.deinit(scratch);
        for (eigens.items) |idx| {
            const wvar = wvars.vars.items[idx];
            const goal = try wvars.deref(wvar.introduced_at.?, &self.names);
            const name = for (try self.prover.pool(wvar.sort_name)) |variable| {
                if (!wvars.isBound(variable)) continue;
                if (wvars.eigens.contains(variable) and !shared.contains(variable)) continue;
                if (std.mem.indexOfScalar(ExprId, wvar.capture, variable) != null) continue;
                if (!wvars.mentions(goal, variable)) break variable;
            } else return false;
            try self.names.put(scratch, idx, name);
            try shared.put(scratch, name, {});
            try wvars.nameEigen(idx, name);
        }
        return true;
    }

    fn collectLeftovers(self: *CloseOut, node: *const Node, out: *std.ArrayListUnmanaged(u32)) prover_mod.Error!void {
        switch (node.step) {
            .ref => {},
            .rule => |step| for (step.bindings) |value| {
                try self.wvars.collectUnbound(self.request.scratch, value, out);
            },
        }
        for (node.children) |child| try self.collectLeftovers(child.?, out);
    }

    /// Name each wvar `value` leaves unbound with the first variable of its
    /// sort's `@vars` pool it admits (`WVars.admits`), unless an earlier
    /// binding already named it. False when one admits none.
    fn nameLeftovers(self: *CloseOut, value: ExprId) prover_mod.Error!bool {
        const scratch = self.request.scratch;
        var leftovers = std.ArrayListUnmanaged(u32).empty;
        defer leftovers.deinit(scratch);
        try self.wvars.collectUnbound(scratch, value, &leftovers);
        for (leftovers.items) |idx| {
            if (self.names.contains(idx)) continue;
            const sort_name = self.wvars.vars.items[idx].sort_name;
            const name = for (try self.prover.pool(sort_name)) |variable| {
                if (self.wvars.admits(idx, variable)) break variable;
            } else return false;
            try self.names.put(scratch, idx, name);
        }
        return true;
    }
};
