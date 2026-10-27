//! The search core: a backward prover over the theory's own rules, in the
//! shape of blast (`docs/design_notes/shared_witness.md`, revision 2).
//!
//! Stage C0 is the skeleton for goals every rule application fixes
//! completely: ground goals, rules whose conclusion fixes every binder
//! (`catalog.zig`), and commutative `@acui` bags matched member by member
//! (`terms.zig`). It runs behind `GenerateOptions.core` and falls back to
//! the generation ladder on a miss.
//!
//! The proof record is rendered as one `RuleApplication` tree with every
//! binding explicit, and the checker validates it once (D5): the checker
//! stays the only authority on what the core returns.

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
const prover_mod = @import("./prover.zig");
const Prover = prover_mod.Prover;
const Node = prover_mod.Node;

pub const Request = struct {
    compiler: *CompilerContext,
    context: *const Context,
    /// The call's working theorem. The core interns into it; the proof is
    /// checked against it.
    theorem: *TheoremContext,
    theorem_vars: *const NameExprMap,
    /// The theorem the pool refs are stated in.
    pool_theorem: *const TheoremContext,
    pool: []const refs_mod.RefPoolEntry,
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
    var terms = try Terms.init(request.scratch, request.context, request.theorem);
    defer terms.deinit();
    if (!try terms.supported(request.goal)) return .abstained;
    const goal = terms.canonical(request.goal) catch |err| switch (err) {
        error.Unsupported => return .abstained,
        else => |e| return e,
    };

    var catalog = try catalog_mod.build(request.scratch, request.context);
    defer catalog.deinit();
    const facts = try poolFacts(request, &terms, arena.allocator());

    var close_out = CloseOut{ .request = request };
    var prover = Prover{
        .allocator = request.scratch,
        .arena = arena.allocator(),
        .context = request.context,
        .terms = &terms,
        .catalog = &catalog,
        .facts = facts,
        .budget = request.budget,
        .close_out = .{ .ctx = &close_out, .tryFn = CloseOut.tryRoot },
        .stack_base = @frameAddress(),
        .stack_guard_bytes = request.stack_guard_bytes,
    };
    defer prover.deinit();
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

/// The pool facts the core can close a goal with, canonical.
fn poolFacts(request: Request, terms: *Terms, arena: std.mem.Allocator) ![]const prover_mod.Fact {
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
    return facts.items;
}

/// Renders a finished proof record and checks it against the goal.
const CloseOut = struct {
    request: Request,
    found: ?RuleApplication = null,

    fn tryRoot(ctx: *anyopaque, root: *const Node) prover_mod.Error!bool {
        const self: *CloseOut = @ptrCast(@alignCast(ctx));
        // A goal a pool fact states is direct `exact?`'s to report.
        if (root.step != .rule) return false;
        const request = self.request;
        var namer = forward.Namer.init(request.scratch);
        defer namer.deinit();
        try namer.collectTheoremVars(request.theorem, request.theorem_vars);
        const application = (try self.render(&namer, root)) orelse return false;
        if (request.counters) |c| c.full_try_candidate_calls += 1;
        if (request.budget) |budget| try budget.spendCandidate();
        var attempt = candidate_mod.probe(
            request.compiler,
            request.context,
            application,
            .{ .concrete = request.goal },
            request.theorem,
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
    /// a value has no source text (an unnamed binder or variable).
    fn render(self: *CloseOut, namer: *forward.Namer, node: *const Node) !?RuleApplication {
        const request = self.request;
        const step = node.step.rule;
        const rule = &request.context.env.rules.items[step.rule_id];
        const zero_span = ProofScript.Span{ .start = 0, .end = 0 };
        const bindings = try request.out.alloc(ProofScript.ArgBinding, step.bindings.len);
        for (bindings, step.bindings, 0..) |*binding, value, idx| {
            const name = rule.arg_names[idx] orelse return null;
            const text = (try namer.render(request.out, request.context, request.theorem, value)) orelse return null;
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
        return .{
            .rule_name = rule.name,
            .rule_span = zero_span,
            .arg_bindings = bindings,
            .refs_span = if (refs.len == 0) null else zero_span,
            .refs = refs,
            .span = zero_span,
        };
    }
};
