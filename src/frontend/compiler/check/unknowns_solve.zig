//! The named-unknown pre-pass: before the line walk, solve the named
//! unknowns (`?a`) of one proof block from all its lines at once, so a line
//! can use a value that only a later line fixes.
//!
//! Every rule application gives equations: its conclusion is its line's
//! statement (or, inline, its parent's premise), each premise is what its
//! reference states, and each explicit binding is its value. The unknowns
//! are the names, a fresh variable per anonymous hole, and a fresh variable
//! per rule binder of each application. The pass solves the equations by
//! first-order unification and commits only what is forced. An equation
//! under a `@rewrite` head is solved by the normal forms of its sides once
//! both have a head that decides them; until then it waits, as does an
//! `@acui` bag the bag step cannot decide yet. Waiting only leaves more
//! solutions, never a wrong one. One that still waits at the end, against
//! a term whose head decides it, holds only if the rewrite head rewrites
//! at the top, so its rewrite rules are tried as a chain's rules are. An equation under a definition unfolds
//! the later definition and equates its body with the other side. A clash
//! anywhere solves nothing; the walk then reports it where it meets it,
//! and the pass names the first line by which the lines clash and, when
//! two terms could not be equal, which.
//!
//! A `@view`, `@recover`, `@abstract` or `@fresh` rule is checked through
//! its view, but the proof applies the rule itself, so its literal
//! statement gives the equations. A `@freshen` rule renames bound variables
//! before it matches and contributes nothing; the walk fills names there.
//! A line citing a `@fallback` chain checks by one of the
//! chain's rules: each rule is tried on a trail, and when only one can
//! check, its equations are committed; otherwise only the values every
//! rule that can check agrees on are.

const std = @import("std");
const ExprModule = @import("../../../trusted/expressions.zig");
const Expr = ExprModule.Expr;
const ExprId = @import("../../expr.zig").ExprId;
const TheoremContext = @import("../../expr.zig").TheoremContext;
const GlobalEnv = @import("../../env.zig").GlobalEnv;
const RuleDecl = @import("../../env.zig").RuleDecl;
const MM0Parser = @import("../../parse_recovery.zig").MM0Parser;
const RewriteRegistry = @import("../../rewrite_registry.zig").RewriteRegistry;
const RewriteRule = @import("../../rewrite_registry.zig").RewriteRule;
const TemplateExpr = @import("../../rules.zig").TemplateExpr;
const SurfaceExpr = @import("../../surface_expr.zig");
const ProofScript = @import("../../proof_script.zig");
const ProofLine = ProofScript.ProofLine;
const RuleApplication = ProofScript.RuleApplication;
const TheoryState = @import("../theory_state.zig").TheoryState;
const Holes = @import("../holes.zig");
const NameExprMap = @import("./types.zig").NameExprMap;
const Unknowns = @import("./unknowns.zig");
const CompilerVars = @import("../vars.zig");
const AcuiBag = @import("../../acui_bag.zig");
const HeadClass = @import("../../head_class.zig");
const Canonicalizer = @import("../../normalizer.zig").Canonicalizer;

pub const Inputs = struct {
    allocator: std.mem.Allocator,
    theory: *TheoryState,
    theorem: *TheoremContext,
    theorem_vars: *NameExprMap,
    lines: []const ProofLine,
    /// The theorem's conclusion, which the last line proves.
    conclusion: ?ExprId,
};

/// Solve the block's named unknowns and bind the solved ones in `out`.
pub fn solve(inputs: Inputs, out: *Unknowns.Unknowns) !void {
    if (!mayHoldHoles(&inputs.theory.parser, inputs.lines)) return;
    var solver = Solver{ .inputs = inputs, .read = &out.statements };
    defer solver.deinit();
    // A clash, or anything else the pass cannot read, solves nothing.
    solver.run() catch |err| switch (err) {
        error.OutOfMemory => return err,
        // Only names are told of a clash: a line with a hole of its own
        // reports its own error.
        error.Clash => return if (mayNameUnknowns(&inputs.theory.parser, inputs.lines))
            reportClash(inputs, out),
        else => return,
    };
    var places = solver.places.iterator();
    while (places.next()) |entry| {
        const value = try solver.resolveFully(entry.value_ptr.*);
        if (solver.isVariable(value)) continue;
        const shown = if (solver.mentionsVariable(value)) try solver.visibleShape(value) else value;
        if (!solver.isVariable(shown)) try out.placed.put(inputs.allocator, entry.key_ptr.*, shown);
    }
    var it = solver.names.iterator();
    while (it.next()) |entry| {
        const name = entry.key_ptr.*;
        const value = try solver.resolveFully(entry.value_ptr.*);
        if (solver.isVariable(value)) {
            // Open: it stands for the first name it is the value of, inside
            // other names' shapes; a later name equated to it has that
            // name as its shape.
            switch (inputs.theorem.interner.node(value).*) {
                .placeholder => |pid| {
                    const open = try out.open.getOrPut(inputs.allocator, pid);
                    if (!open.found_existing) {
                        open.value_ptr.* = name;
                    } else {
                        try out.partial.put(inputs.allocator, name, value);
                    }
                },
                else => {},
            }
        } else if (solver.mentionsVariable(value)) {
            const shown = try solver.visibleShape(value);
            if (!solver.isVariable(shown)) try out.partial.put(inputs.allocator, name, shown);
        } else {
            try out.bound.put(inputs.allocator, name, value);
        }
    }
}

/// The lines clash: find the first line by which they do and tell the
/// walk. The pass solves the lines in no fixed order, and how far it gets
/// before an equation must wait depends on that order, so each prefix of
/// the lines is solved afresh as a whole; the whole block clashed, so one
/// does. No name is solved.
fn reportClash(inputs: Inputs, out: *Unknowns.Unknowns) !void {
    for (1..inputs.lines.len + 1) |len| {
        var prefix = inputs;
        prefix.lines = inputs.lines[0..len];
        if (len < inputs.lines.len) prefix.conclusion = null;
        var solver = Solver{ .inputs = prefix, .read = &out.statements };
        defer solver.deinit();
        solver.run() catch |err| switch (err) {
            error.OutOfMemory => return err,
            error.Clash => return solver.recordClash(prefix.lines[len - 1].label, out),
            else => {},
        };
    }
}

/// The app nodes a walk of a shared term has entered. The first
/// `plain_steps` go unrecorded, so a small term costs nothing.
const Seen = struct {
    const plain_steps = 64;

    steps: usize = 0,
    set: std.AutoHashMapUnmanaged(ExprId, void) = .empty,

    fn begin(self: *Seen) void {
        self.steps = 0;
        if (self.set.count() != 0) self.set.clearRetainingCapacity();
    }

    /// False when `id` was entered before.
    fn enter(self: *Seen, allocator: std.mem.Allocator, id: ExprId) bool {
        self.steps += 1;
        if (self.steps <= plain_steps) return true;
        const slot = self.set.getOrPut(allocator, id) catch return true;
        return !slot.found_existing;
    }
};

const Solver = struct {
    inputs: Inputs,
    /// The statements read, by the address of their text, for the walk.
    read: *std.AutoHashMapUnmanaged(usize, Holes.ParsedAssertion),
    /// Each name's variable.
    names: std.StringArrayHashMapUnmanaged(ExprId) = .empty,
    /// Each anonymous hole's variable, by where the hole is written.
    places: std.AutoArrayHashMapUnmanaged(usize, ExprId) = .empty,
    /// The app nodes the walk of a value under way has entered, and the
    /// resolved form of those `resolveFully` has left: a value is a shared
    /// term, and each of its nodes is visited once.
    seen: Seen = .{},
    resolved: std.AutoHashMapUnmanaged(ExprId, ExprId) = .empty,
    /// The pass's own variables, and what each is bound to.
    variables: std.AutoHashMapUnmanaged(ExprId, Slot) = .empty,
    /// Counts the waiting equations made outside a trial (`Slot.touched`).
    epoch: u32 = 0,
    /// Set while the variables a rewrite step looks at are noted.
    reads: ?*Reads = null,
    /// Counts the note-taking spans (`Slot.read`).
    read_spans: u32 = 0,
    /// The rewrite steps that forced nothing, by waiting equation.
    idle_steps: std.AutoHashMapUnmanaged([2]ExprId, IdleStep) = .empty,
    /// Each line's statement, by label.
    statements: std.StringHashMapUnmanaged(ExprId) = .empty,
    work: std.ArrayListUnmanaged([2]ExprId) = .empty,
    /// Bag equations not decided yet: retried while bindings are made.
    postponed: std.ArrayListUnmanaged(Waiting) = .empty,
    /// The waiting equations as they were before the trial under way.
    postponed_saved: std.ArrayListUnmanaged(Waiting) = .empty,
    /// Scratch of `postpone`.
    mentioned: std.ArrayListUnmanaged(ExprId) = .empty,
    mentioned_seen: std.AutoHashMapUnmanaged(ExprId, void) = .empty,
    /// Owns the `Waiting.vars` lists.
    waiting_arena: ?std.heap.ArenaAllocator = null,
    /// Bindings made so far, to tell whether deciding the chains and the
    /// rewrite steps made progress.
    progress: usize = 0,
    /// The variables a trial bound, in order, so it can undo them.
    trail: std.ArrayListUnmanaged(ExprId) = .empty,
    /// Lines citing a `@fallback` chain, decided after the other lines.
    choices: std.ArrayListUnmanaged(Choice) = .empty,
    /// Inside a trial of one rule of a chain, where a nested chain
    /// contributes nothing.
    in_trial: bool = false,
    /// Normal forms of the equations under a `@rewrite` head; made on
    /// first use.
    canonicalizer: ?Canonicalizer = null,
    /// The two terms of the clash, when it was between two terms that
    /// cannot be equal.
    clash_terms: ?[2]ExprId = null,
    /// Equations a rewrite step was committed for, so it is not again.
    steps_done: std.ArrayListUnmanaged([2]ExprId) = .empty,

    const Slot = struct {
        binding: ?ExprId = null,
        /// `epoch` when a waiting equation that mentions the variable was
        /// last made outside a trial.
        touched: u32 = 0,
        /// The note-taking span that last saw the variable unbound.
        read: u32 = 0,
    };

    /// The unbound variables looked at since note-taking began.
    const Reads = struct {
        allocator: std.mem.Allocator,
        span: u32,
        vars: std.ArrayListUnmanaged(ExprId) = .empty,
        /// A variable could not be noted, so the notes are no use.
        lost: bool = false,
    };

    /// A rewrite step that was tried and forced nothing. What it found
    /// depends only on the unbound variables it looked at and the waiting
    /// equations on them, so it stands until one of the variables is bound
    /// or a waiting equation that mentions one is made. (Trying every
    /// waiting equation's rules again whenever anything was bound made the
    /// pass quadratic in the lines of a long proof.)
    const IdleStep = struct {
        epoch: u32,
        vars: []const ExprId,
    };

    /// An equation that waits for more bindings.
    const Waiting = struct {
        pair: [2]ExprId,
        /// The unbound variables the two sides mentioned when the
        /// equation was last tried. Nothing else can change what it says,
        /// so it is tried again only once one of them is bound. (Trying
        /// every waiting equation again on any binding ran without end on
        /// one that unfolds a definition, whose hidden variables are
        /// minted and bound anew each time, and cost a pass over all of
        /// them per binding.)
        vars: []const ExprId,
    };

    const Choice = struct {
        app: RuleApplication,
        goal: ExprId,
        /// The chain, in the order the walk tries it.
        rules: []const u32,
        decided: bool = false,
    };

    fn deinit(self: *Solver) void {
        const allocator = self.inputs.allocator;
        self.names.deinit(allocator);
        self.places.deinit(allocator);
        self.variables.deinit(allocator);
        self.seen.set.deinit(allocator);
        self.resolved.deinit(allocator);
        self.idle_steps.deinit(allocator);
        self.statements.deinit(allocator);
        self.work.deinit(allocator);
        self.postponed.deinit(allocator);
        self.postponed_saved.deinit(allocator);
        self.mentioned.deinit(allocator);
        self.mentioned_seen.deinit(allocator);
        if (self.waiting_arena) |*arena| arena.deinit();
        self.trail.deinit(allocator);
        for (self.choices.items) |choice| allocator.free(choice.rules);
        self.choices.deinit(allocator);
        self.steps_done.deinit(allocator);
        if (self.canonicalizer) |*canonicalizer| canonicalizer.deinit();
    }

    fn run(self: *Solver) !void {
        const allocator = self.inputs.allocator;
        const parser = &self.inputs.theory.parser;
        // The walk stops at an incomplete line; so does the pass.
        const lines = for (self.inputs.lines, 0..) |line, idx| {
            if (line.incomplete) break self.inputs.lines[0..idx];
        } else self.inputs.lines;

        // Statements first, in line order: a reference may name any
        // earlier line.
        var holey: std.StringHashMapUnmanaged(void) = .empty;
        defer holey.deinit(allocator);
        var any = false;
        for (lines) |line| {
            if (try self.readStatement(line)) {
                try holey.put(allocator, line.label, {});
                any = true;
            }
            if (applicationMayHold(parser, line.application)) any = true;
        }
        if (!any) return;

        // Only a line with a hole, one that cites such a line, or one with
        // a hole in a binding says anything about a hole: any other line's
        // equations are between its own rule's binders and statements
        // without holes.
        for (lines) |line| {
            if (!holey.contains(line.label) and !citesAny(line.application, &holey) and
                !applicationMayHold(parser, line.application)) continue;
            const statement = self.statements.get(line.label) orelse continue;
            try self.application(line.application, statement);
        }
        // The last line meets the conclusion only when the block is whole.
        if (lines.len != 0 and lines.len == self.inputs.lines.len and holey.contains(lines[lines.len - 1].label)) {
            if (self.statements.get(lines[lines.len - 1].label)) |statement| {
                if (self.inputs.conclusion) |conclusion| try self.equate(statement, conclusion);
            }
        }
        try self.settle();
        try self.decideChoices();
    }

    /// Read `line`'s statement, and keep it for the walk: whether it holds
    /// a hole. A statement that cannot be read is left out.
    fn readStatement(self: *Solver, line: ProofLine) !bool {
        const theory = self.inputs.theory;
        const parsed = Holes.parseAssertion(
            &theory.parser,
            self.inputs.theorem,
            self.inputs.theorem_vars,
            &theory.sort_vars,
            line.assertion.text,
        ) catch |err| switch (err) {
            error.OutOfMemory => return err,
            else => return false,
        };
        try self.read.put(self.inputs.allocator, @intFromPtr(line.assertion.text.ptr), parsed);
        switch (parsed) {
            .concrete => |expr| {
                try self.statements.put(self.inputs.allocator, line.label, expr);
                return false;
            },
            .holey => |surface| {
                const expr = (try self.internSurface(surface)) orelse return false;
                try self.statements.put(self.inputs.allocator, line.label, expr);
                return true;
            },
        }
    }

    /// Tell the walk that the lines up to `line` clash, as this solver
    /// found; no name is solved.
    fn recordClash(self: *Solver, line: []const u8, out: *Unknowns.Unknowns) !void {
        const allocator = self.inputs.allocator;
        var terms: ?[2]ExprId = null;
        if (self.clash_terms) |pair| {
            terms = .{ try self.resolveFully(pair[0]), try self.resolveFully(pair[1]) };
        }
        out.clash = .{ .line = line, .terms = terms };
        // A name still open inside the terms is written as itself.
        var it = self.names.iterator();
        while (it.next()) |entry| {
            const value = try self.resolveFully(entry.value_ptr.*);
            switch (self.inputs.theorem.interner.node(value).*) {
                .placeholder => |pid| {
                    const open = try out.open.getOrPut(allocator, pid);
                    if (!open.found_existing) open.value_ptr.* = entry.key_ptr.*;
                },
                else => {},
            }
        }
    }

    /// Solve the pending equations, retrying each postponed one once a
    /// variable it waits on is bound.
    fn settle(self: *Solver) !void {
        try self.drain();
        while (true) {
            var kept: usize = 0;
            for (self.postponed.items) |waiting| {
                if (self.woken(waiting)) {
                    try self.work.append(self.inputs.allocator, waiting.pair);
                } else {
                    self.postponed.items[kept] = waiting;
                    kept += 1;
                }
            }
            if (kept == self.postponed.items.len) break;
            self.postponed.shrinkRetainingCapacity(kept);
            try self.drain();
        }
    }

    /// Whether a variable `waiting` waits on has been bound.
    fn woken(self: *const Solver, waiting: Waiting) bool {
        for (waiting.vars) |variable| {
            if (self.variables.get(variable).?.binding != null) return true;
        }
        return false;
    }

    /// Make `lhs = rhs` wait for one of its unbound variables.
    fn postpone(self: *Solver, lhs: ExprId, rhs: ExprId) !void {
        const allocator = self.inputs.allocator;
        const vars = &self.mentioned;
        vars.clearRetainingCapacity();
        self.mentioned_seen.clearRetainingCapacity();
        try self.collectVariables(lhs, vars, &self.mentioned_seen);
        try self.collectVariables(rhs, vars, &self.mentioned_seen);
        if (!self.in_trial) {
            self.epoch += 1;
            for (vars.items) |variable| self.variables.getPtr(variable).?.touched = self.epoch;
        }
        if (self.waiting_arena == null) self.waiting_arena = std.heap.ArenaAllocator.init(allocator);
        try self.postponed.append(allocator, .{
            .pair = .{ lhs, rhs },
            .vars = try self.waiting_arena.?.allocator().dupe(ExprId, vars.items),
        });
    }

    fn collectVariables(
        self: *Solver,
        expr: ExprId,
        vars: *std.ArrayListUnmanaged(ExprId),
        seen: *std.AutoHashMapUnmanaged(ExprId, void),
    ) !void {
        const resolved = self.resolve(expr);
        const slot = try seen.getOrPut(self.inputs.allocator, resolved);
        if (slot.found_existing) return;
        if (self.isVariable(resolved)) return vars.append(self.inputs.allocator, resolved);
        switch (self.inputs.theorem.interner.node(resolved).*) {
            .app => |app| for (app.args) |arg| try self.collectVariables(arg, vars, seen),
            else => {},
        }
    }

    /// The equations of `app`, whose conclusion is `goal`.
    fn application(self: *Solver, app: RuleApplication, goal: ExprId) anyerror!void {
        const theory = self.inputs.theory;
        if (!isOrdinaryRuleName(app.rule_name)) return;
        const rule_id = theory.env.rule_names.get(app.rule_name) orelse return;
        if (theory.registry.getFallbackRule(rule_id) == null) {
            if (!self.literalRule(rule_id)) return;
            const rule: *const RuleDecl = &theory.env.rules.items[rule_id];
            if (app.refs.len != rule.hyps.len) return;
            return self.ruleApplication(app, rule_id, goal);
        }
        if (self.in_trial) return;
        const allocator = self.inputs.allocator;
        var rules: std.ArrayListUnmanaged(u32) = .empty;
        defer rules.deinit(allocator);
        var next: ?u32 = rule_id;
        while (next) |candidate| : (next = theory.registry.getFallbackRule(candidate)) {
            // A cycle is the walk's error to report.
            if (std.mem.indexOfScalar(u32, rules.items, candidate) != null) return;
            // A rule the pass cannot read could always be the one that
            // checks, so the chain forces nothing.
            if (!self.literalRule(candidate)) return;
            try rules.append(allocator, candidate);
        }
        const owned = try rules.toOwnedSlice(allocator);
        errdefer allocator.free(owned);
        try self.choices.append(allocator, .{ .app = app, .goal = goal, .rules = owned });
    }

    /// The equations of `app` read with the rule `rule_id`, whose premise
    /// count matches.
    fn ruleApplication(self: *Solver, app: RuleApplication, rule_id: u32, goal: ExprId) anyerror!void {
        const theory = self.inputs.theory;
        const theorem = self.inputs.theorem;
        const rule: *const RuleDecl = &theory.env.rules.items[rule_id];

        const allocator = self.inputs.allocator;
        const binders = try allocator.alloc(ExprId, rule.args.len);
        defer allocator.free(binders);
        for (rule.args, binders) |arg, *binder| {
            binder.* = try self.mint(arg.sort_name);
        }
        for (app.arg_bindings) |binding| {
            const idx = for (rule.arg_names, 0..) |name, i| {
                if (name != null and std.mem.eql(u8, name.?, binding.name)) break i;
            } else continue;
            // As the walk does: an `@vars` token the text names becomes
            // its theorem-local dummy.
            const value = blk: {
                try CompilerVars.ensureMathTextVars(
                    &theory.parser,
                    self.inputs.theorem,
                    self.inputs.theorem_vars,
                    &theory.sort_vars,
                    binding.formula.text,
                );
                break :blk theory.parser.parseHoleyArgText(
                    binding.formula.text,
                    self.inputs.theorem_vars,
                    rule.args[idx],
                );
            } catch |err| switch (err) {
                error.OutOfMemory => return err,
                else => continue,
            };
            try self.equate(binders[idx], (try self.internSurface(value)) orelse continue);
        }

        try self.equate(try theorem.instantiateTemplate(rule.concl, binders), goal);
        for (app.refs, rule.hyps) |ref, hyp| {
            const premise = try theorem.instantiateTemplate(hyp, binders);
            switch (ref) {
                .hyp => |hyp_ref| {
                    const resolved = ProofScript.resolveHypRef(
                        theorem.theorem_hyp_names,
                        theorem.theorem_hyps.items.len,
                        hyp_ref,
                    );
                    switch (resolved) {
                        .index => |idx| try self.equate(premise, theorem.theorem_hyps.items[idx]),
                        .unknown, .ambiguous => {},
                    }
                },
                .line => |label| if (self.statements.get(label.label)) |stated| {
                    try self.equate(premise, stated);
                },
                .application => |child| try self.application(child, premise),
            }
        }
    }

    /// Whether `rule_id`'s literal conclusion and premises hold of every
    /// line that applies it. A `@view`, `@recover`, `@abstract` or `@fresh`
    /// rule is checked through its view, but the proof still applies the
    /// rule itself, so its literal statement is forced; a substitution in
    /// it is a rewrite head and waits like any other. A `@freshen` rule
    /// renames bound variables before it matches, so its literal statement
    /// would clash with a line that is only alpha-equivalent to it.
    fn literalRule(self: *const Solver, rule_id: u32) bool {
        return !self.inputs.theory.freshen_bindings.contains(rule_id);
    }

    // ---------------------------------------------------------------
    // Choices: the walk checks a `@fallback` line by the first rule of
    // its chain that checks. Each rule is tried on a trail against
    // everything else solved so far. A rule that clashes cannot check.
    // When one rule is left, its equations are committed; when several
    // are, a name every one of them gives the same value takes it. Either
    // is forced: every successful check agrees with it. Committing one
    // choice may decide another, so the choices are retried while
    // bindings are made.

    fn decideChoices(self: *Solver) !void {
        while (true) {
            const before = self.progress;
            // Committing a rule may add the choices of its inline
            // sub-proofs, so the list may grow while it is walked.
            var i: usize = 0;
            while (i < self.choices.items.len) : (i += 1) {
                if (!self.choices.items[i].decided) try self.decide(i);
            }
            if (self.progress != before) continue;
            // Rewrite steps wait until the chains decide nothing more.
            try self.decideSteps();
            if (self.progress == before) return;
        }
    }

    fn decide(self: *Solver, index: usize) !void {
        const allocator = self.inputs.allocator;
        const choice = self.choices.items[index];
        const attempts = try allocator.alloc(Attempt, choice.rules.len);
        defer allocator.free(attempts);
        for (choice.rules, attempts) |rule_id, *attempt| {
            attempt.* = .{ .chain = .{ .choice = choice, .rule_id = rule_id } };
        }
        switch (try self.weigh(attempts)) {
            .one => |i| {
                self.choices.items[index].decided = true;
                try self.apply(attempts[i]);
                try self.settle();
            },
            .agreed => |agreed| try self.commitAgreed(agreed),
        }
    }

    /// What trying each of `attempts` forces: the index of the only one
    /// that can check, or else the bindings every one that can check
    /// makes; a clash when none can.
    const Verdict = union(enum) { one: usize, agreed: []Binding };

    /// A variable a trial bound, and its value.
    const Binding = struct { variable: ExprId, value: ExprId };

    fn weigh(self: *Solver, attempts: []const Attempt) !Verdict {
        const allocator = self.inputs.allocator;
        var agreed: std.ArrayListUnmanaged(Binding) = .empty;
        errdefer agreed.deinit(allocator);
        var survivor: usize = 0;
        var survivors: usize = 0;
        for (attempts, 0..) |attempt, i| {
            const bindings = (try self.trial(attempt)) orelse continue;
            defer allocator.free(bindings);
            survivors += 1;
            survivor = i;
            if (survivors == 1) {
                try agreed.appendSlice(allocator, bindings);
                continue;
            }
            var kept: usize = 0;
            for (agreed.items) |binding| {
                const same = for (bindings) |theirs| {
                    if (theirs.variable == binding.variable) break theirs.value == binding.value;
                } else false;
                if (!same) continue;
                agreed.items[kept] = binding;
                kept += 1;
            }
            agreed.shrinkRetainingCapacity(kept);
            // Two can check and agree on nothing: no later one changes that.
            if (kept == 0) break;
        }
        if (survivors == 0) return error.Clash;
        if (survivors == 1) {
            agreed.deinit(allocator);
            return .{ .one = survivor };
        }
        return .{ .agreed = try agreed.toOwnedSlice(allocator) };
    }

    /// Make the bindings every surviving attempt agreed on, and free
    /// `agreed`.
    fn commitAgreed(self: *Solver, agreed: []Binding) !void {
        defer self.inputs.allocator.free(agreed);
        for (agreed) |binding| try self.equate(binding.variable, binding.value);
        try self.settle();
    }

    /// Try `attempt` and undo it: when it can check, the bindings it made
    /// of the variables there were before it; null when it clashes. A
    /// value that mentions a variable of the trial's own is left out, as
    /// no other attempt can agree with it. Caller frees.
    fn trial(self: *Solver, attempt: Attempt) !?[]Binding {
        const allocator = self.inputs.allocator;
        std.debug.assert(self.work.items.len == 0 and !self.in_trial);
        switch (attempt) {
            .chain => |chain| {
                const rule: *const RuleDecl = &self.inputs.theory.env.rules.items[chain.rule_id];
                if (chain.choice.app.refs.len != rule.hyps.len) return null;
            },
            .step => {},
        }
        const first_new: ExprId = @intCast(self.inputs.theorem.interner.count());
        const trail_mark = self.trail.items.len;
        const progress_mark = self.progress;
        // Trials do not nest, so one saved copy serves them all.
        self.postponed_saved.clearRetainingCapacity();
        try self.postponed_saved.appendSlice(allocator, self.postponed.items);
        defer {
            for (self.trail.items[trail_mark..]) |variable| {
                self.variables.getPtr(variable).?.binding = null;
            }
            self.trail.shrinkRetainingCapacity(trail_mark);
            self.work.clearRetainingCapacity();
            self.postponed.clearRetainingCapacity();
            // Restores what was copied out; capacity is already there.
            self.postponed.appendSliceAssumeCapacity(self.postponed_saved.items);
            self.progress = progress_mark;
            self.in_trial = false;
        }
        self.in_trial = true;
        const checks = blk: {
            self.apply(attempt) catch |err| switch (err) {
                error.Clash => break :blk false,
                else => return err,
            };
            self.settle() catch |err| switch (err) {
                error.Clash => break :blk false,
                else => return err,
            };
            break :blk true;
        };
        if (!checks) return null;
        var bindings: std.ArrayListUnmanaged(Binding) = .empty;
        errdefer bindings.deinit(allocator);
        for (self.trail.items[trail_mark..]) |variable| {
            if (variable >= first_new) continue;
            const value = try self.resolveFully(variable);
            if (self.mentionsFrom(value, first_new)) continue;
            try bindings.append(allocator, .{ .variable = variable, .value = value });
        }
        return try bindings.toOwnedSlice(allocator);
    }

    /// Whether `expr` mentions a pass variable made at `first` or later.
    /// A term over one was itself made later.
    fn mentionsFrom(self: *Solver, expr: ExprId, first: ExprId) bool {
        self.seen.begin();
        return self.mentionsFromIn(expr, first);
    }

    fn mentionsFromIn(self: *Solver, expr: ExprId, first: ExprId) bool {
        if (expr < first) return false;
        if (self.isVariable(expr)) return true;
        return switch (self.inputs.theorem.interner.node(expr).*) {
            .app => |app| self.seen.enter(self.inputs.allocator, expr) and for (app.args) |arg| {
                if (self.mentionsFromIn(arg, first)) break true;
            } else false,
            else => false,
        };
    }

    /// One way a line or an equation may check, tried on a trail.
    const Attempt = union(enum) {
        /// The rule `rule_id` of a `@fallback` chain.
        chain: struct { choice: Choice, rule_id: u32 },
        /// `stuck = other` by the rewrite `rule` at the top of `stuck`.
        step: struct { stuck: ExprId, other: ExprId, rule: *const RewriteRule },
    };

    fn apply(self: *Solver, attempt: Attempt) !void {
        switch (attempt) {
            .chain => |chain| try self.ruleApplication(chain.choice.app, chain.rule_id, chain.choice.goal),
            .step => |step| try self.rewriteStep(step.stuck, step.other, step.rule),
        }
    }

    // ---------------------------------------------------------------
    // Rewrite steps: an equation still waiting when nothing else decides
    // anything, between a term under a `@rewrite` head and a term whose
    // head decides it, holds only if the first rewrites at the top: its
    // normal form must lose its head. Every rewrite rule of that head is
    // tried like a rule of a chain. A rule's bound binders must take
    // distinct bound variables, and its other binders must avoid the bound
    // variables they may not depend on; a pass variable there is narrowed
    // to one that avoids them (`restrict`), which lets the rewrite fire.

    fn decideSteps(self: *Solver) !void {
        const allocator = self.inputs.allocator;
        const pending = try allocator.dupe(Waiting, self.postponed.items);
        defer allocator.free(pending);
        for (pending) |waiting| {
            if (self.idleStepStands(waiting.pair)) continue;
            const first_new: ExprId = @intCast(self.inputs.theorem.interner.count());
            self.read_spans += 1;
            var reads = Reads{ .allocator = allocator, .span = self.read_spans };
            defer reads.vars.deinit(allocator);
            self.reads = &reads;
            defer self.reads = null;
            if (try self.stepPair(waiting.pair)) continue;
            self.reads = null;
            if (!reads.lost) try self.rememberIdleStep(waiting.pair, reads.vars.items, first_new);
        }
    }

    /// Step the waiting equation `pair` if one side is stuck against a
    /// rigid other; whether that forced anything.
    fn stepPair(self: *Solver, pair: [2]ExprId) !bool {
        const lhs = try self.normalForm(pair[0]);
        const rhs = try self.normalForm(pair[1]);
        if (self.stuckHead(lhs) != null and self.rigid(rhs, lhs)) return self.decideStep(lhs, rhs);
        if (self.stuckHead(rhs) != null and self.rigid(lhs, rhs)) return self.decideStep(rhs, lhs);
        return false;
    }

    fn idleStepStands(self: *const Solver, pair: [2]ExprId) bool {
        const idle = self.idle_steps.get(pair) orelse return false;
        for (idle.vars) |variable| {
            const slot = self.variables.get(variable).?;
            if (slot.binding != null or slot.touched > idle.epoch) return false;
        }
        return true;
    }

    /// Stepping `pair` forced nothing, having looked at `vars`; the ones
    /// made at `first_new` or later were its trials' own.
    fn rememberIdleStep(self: *Solver, pair: [2]ExprId, vars: []const ExprId, first_new: ExprId) !void {
        const allocator = self.inputs.allocator;
        if (self.waiting_arena == null) self.waiting_arena = std.heap.ArenaAllocator.init(allocator);
        const kept = try self.waiting_arena.?.allocator().alloc(ExprId, vars.len);
        var count: usize = 0;
        for (vars) |variable| {
            if (variable >= first_new) continue;
            kept[count] = variable;
            count += 1;
        }
        try self.idle_steps.put(allocator, pair, .{ .epoch = self.epoch, .vars = kept[0..count] });
    }

    /// The `@rewrite` head of `expr`, when only its rewrites can change
    /// it: not a definition, which unfolds, nor an `@acui` combiner, whose
    /// laws rearrange it.
    fn stuckHead(self: *const Solver, expr: ExprId) ?u32 {
        return switch (self.inputs.theorem.interner.node(self.resolve(expr)).*) {
            .app => |app| if (self.rewriteOnly(app.term_id)) app.term_id else null,
            else => null,
        };
    }

    fn rewriteOnly(self: *const Solver, term_id: u32) bool {
        const theory = self.inputs.theory;
        return theory.env.openableDef(term_id) == null and
            AcuiBag.Combiner.of(&theory.registry, &theory.env, term_id) == null and
            theory.registry.getRewriteRules(term_id).len != 0;
    }

    /// Whether `expr` can equal only terms with its head, and that head
    /// is not `stuck`'s.
    fn rigid(self: *const Solver, expr: ExprId, stuck: ExprId) bool {
        const resolved = self.resolve(expr);
        if (self.isVariable(resolved)) return false;
        return switch (self.inputs.theorem.interner.node(resolved).*) {
            .app => |app| !self.flexibleHead(app.term_id) and app.term_id != self.stuckHead(stuck).?,
            .variable => true,
            .placeholder => false,
        };
    }

    /// Whether trying the rewrite rules of `stuck`'s head forced anything.
    fn decideStep(self: *Solver, stuck: ExprId, other: ExprId) !bool {
        const allocator = self.inputs.allocator;
        for (self.steps_done.items) |done| {
            if (done[0] == stuck and done[1] == other) return false;
        }
        const rules = self.inputs.theory.registry.getRewriteRules(self.stuckHead(stuck).?);
        const attempts = try allocator.alloc(Attempt, rules.len);
        defer allocator.free(attempts);
        for (rules, attempts) |*rule, *attempt| {
            attempt.* = .{ .step = .{ .stuck = stuck, .other = other, .rule = rule } };
        }
        const verdict = self.weigh(attempts) catch |err| switch (err) {
            error.Clash => return self.clash(stuck, other),
            // A rule the pass cannot read could be the one that fires, so
            // the equation forces nothing.
            error.Unreadable => return false,
            else => return err,
        };
        switch (verdict) {
            .one => |i| {
                // A right side under a rewrite head again would wait as a
                // new equation, and could be stepped without end.
                switch (rules[i].rhs) {
                    .app => |app| if (self.rewriteOnly(app.term_id)) return false,
                    .binder => {},
                }
                try self.steps_done.append(allocator, .{ stuck, other });
                try self.apply(attempts[i]);
                try self.settle();
                return true;
            },
            .agreed => |agreed| {
                const any = agreed.len != 0;
                try self.commitAgreed(agreed);
                return any;
            },
        }
    }

    /// The equations of `stuck = other` when `rule` rewrites `stuck` at the
    /// top: its left side is `stuck` argument by argument (each modulo
    /// conversion, as the normalizer rewrites inside first), and its right
    /// side is `other`. Then the rule's binders must satisfy its
    /// dependencies.
    fn rewriteStep(self: *Solver, stuck: ExprId, other: ExprId, rule: *const RewriteRule) !void {
        const allocator = self.inputs.allocator;
        const theorem = self.inputs.theorem;
        const decl: *const RuleDecl = &self.inputs.theory.env.rules.items[rule.rule_id];
        if (decl.args.len != rule.num_binders) return error.Unreadable;
        const binders = try allocator.alloc(ExprId, decl.args.len);
        defer allocator.free(binders);
        for (decl.args, binders) |arg, *binder| binder.* = try self.mint(arg.sort_name);
        const lhs = try theorem.instantiateTemplate(rule.lhs, binders);
        const lhs_app = switch (theorem.interner.node(lhs).*) {
            .app => |app| app,
            else => return error.Unreadable,
        };
        const stuck_app = theorem.interner.node(self.resolve(stuck)).app;
        if (lhs_app.term_id != stuck_app.term_id or lhs_app.args.len != stuck_app.args.len) {
            return error.Clash;
        }
        for (lhs_app.args, stuck_app.args) |l, r| try self.equate(l, r);
        try self.equate(try theorem.instantiateTemplate(rule.rhs, binders), other);
        try self.settle();
        // The bound binders' variables, which the other binders' values
        // must avoid where the rule says so.
        const bits = try allocator.alloc(u55, decl.args.len);
        defer allocator.free(bits);
        for (decl.args, binders, bits, 0..) |arg, binder, *bit, i| {
            bit.* = 0;
            if (!arg.bound) continue;
            const value = self.resolve(binder);
            switch (theorem.interner.node(value).*) {
                .variable => {},
                // Which variable it is decides what may fire.
                else => return error.Unreadable,
            }
            const leaf = (try theorem.currentLeafInfo(value)) orelse return error.Unreadable;
            if (!leaf.bound) return error.Clash;
            for (decl.args[0..i], binders[0..i]) |earlier, earlier_binder| {
                if (earlier.bound and self.resolve(earlier_binder) == value) return error.Clash;
            }
            bit.* = leaf.deps;
        }
        for (decl.args, binders) |arg, binder| {
            if (arg.bound) continue;
            var avoid: u55 = 0;
            for (decl.args, bits) |bound, bit| {
                if (bound.bound and arg.deps & bound.deps == 0) avoid |= bit;
            }
            if (avoid != 0) try self.restrict(binder, ~avoid);
        }
    }

    /// Narrow `expr` to mention only the variables `allowed` keeps: a pass
    /// variable that may mention others is bound to a fresh one that may
    /// not, and a theorem variable outside `allowed` is a clash. A term
    /// under a definition or `@rewrite` head may still lose a variable as
    /// more is bound, so it is left as it is.
    fn restrict(self: *Solver, expr: ExprId, allowed: u55) !void {
        self.seen.begin();
        return self.restrictIn(expr, allowed);
    }

    fn restrictIn(self: *Solver, expr: ExprId, allowed: u55) !void {
        const theorem = self.inputs.theorem;
        const resolved = self.resolve(expr);
        if (self.isVariable(resolved)) {
            const deps = try theorem.exprDeps(resolved, .{});
            if (deps & ~allowed == 0) return;
            const sort_name = try SurfaceExpr.exprIdSortName(theorem, &self.inputs.theory.env, resolved);
            const narrowed = try theorem.addRestrictedLineHolePlaceholder(sort_name, deps & allowed);
            try self.variables.put(self.inputs.allocator, narrowed, .{});
            if (self.in_trial) try self.trail.append(self.inputs.allocator, resolved);
            self.variables.getPtr(resolved).?.binding = narrowed;
            self.progress += 1;
            return;
        }
        switch (theorem.interner.node(resolved).*) {
            .app => |app| if (!self.undecided(app.term_id) and
                self.seen.enter(self.inputs.allocator, resolved))
            {
                for (app.args) |arg| try self.restrictIn(arg, allowed);
            },
            .variable => if (try theorem.exprDeps(resolved, .{}) & ~allowed != 0) return error.Clash,
            .placeholder => {},
        }
    }

    fn internSurface(self: *Solver, expr: *const Expr) !?ExprId {
        const theorem = self.inputs.theorem;
        switch (expr.*) {
            .variable => return try theorem.internParsedExpr(expr),
            .hole => |hole| {
                const sort_name = SurfaceExpr.sortNameById(&self.inputs.theory.env, hole.sort) orelse
                    return null;
                const name = hole.name orelse {
                    const variable = try self.mint(sort_name);
                    if (Unknowns.placeOf(hole)) |place| {
                        try self.places.put(self.inputs.allocator, place, variable);
                    }
                    return variable;
                };
                const entry = try self.names.getOrPut(self.inputs.allocator, name);
                if (!entry.found_existing) entry.value_ptr.* = try self.mint(sort_name);
                return entry.value_ptr.*;
            },
            .term => |term| {
                const args = try theorem.allocator.alloc(ExprId, term.args.len);
                defer theorem.allocator.free(args);
                for (term.args, args) |arg, *out| {
                    out.* = (try self.internSurface(arg)) orelse return null;
                }
                return try theorem.interner.internApp(term.id, args);
            },
        }
    }

    /// A variable of the pass. It may come to stand for anything, so it
    /// claims to mention every variable: normalizing through it fires no
    /// rewrite whose binding must avoid one (`{x / t} ?p` keeps its
    /// substitution, as `?p` may mention `x`). The walk only prints the
    /// variables a shape keeps; a line gets the shape as surface syntax,
    /// its open parts as ordinary holes (`Unknowns.substitute`).
    fn mint(self: *Solver, sort_name: []const u8) !ExprId {
        const variable = try self.inputs.theorem.addUnrestrictedLineHolePlaceholder(sort_name);
        try self.variables.put(self.inputs.allocator, variable, .{});
        return variable;
    }

    fn isVariable(self: *const Solver, id: ExprId) bool {
        return self.variables.contains(id);
    }

    fn resolve(self: *const Solver, id: ExprId) ExprId {
        var current = id;
        while (self.variables.getPtr(current)) |slot| {
            current = slot.binding orelse {
                if (self.reads) |reads| if (slot.read != reads.span) {
                    slot.read = reads.span;
                    reads.vars.append(reads.allocator, current) catch {
                        reads.lost = true;
                    };
                };
                return current;
            };
        }
        return current;
    }

    fn equate(self: *Solver, lhs: ExprId, rhs: ExprId) !void {
        try self.work.append(self.inputs.allocator, .{ lhs, rhs });
    }

    fn drain(self: *Solver) !void {
        const theorem = self.inputs.theorem;
        while (self.work.pop()) |pair| {
            const lhs = self.resolve(pair[0]);
            const rhs = self.resolve(pair[1]);
            if (lhs == rhs) continue;
            if (self.isVariable(lhs)) {
                try self.bind(lhs, rhs);
                continue;
            }
            if (self.isVariable(rhs)) {
                try self.bind(rhs, lhs);
                continue;
            }
            // Before the bag step: a definition may stand for a bag.
            if (self.definitionHead(lhs) != null or self.definitionHead(rhs) != null) {
                try self.definitionPair(lhs, rhs);
                continue;
            }
            if (self.combinerOf(lhs) orelse self.combinerOf(rhs)) |combiner| {
                try self.bagStep(combiner, lhs, rhs);
                continue;
            }
            const lhs_node = theorem.interner.node(lhs).*;
            const rhs_node = theorem.interner.node(rhs).*;
            const lhs_app = switch (lhs_node) {
                .app => |app| app,
                .variable => switch (rhs_node) {
                    .app => |app| if (self.undecided(app.term_id)) {
                        try self.rewritePair(lhs, rhs);
                        continue;
                    } else return self.clash(lhs, rhs),
                    // Distinct theorem variables.
                    .variable => return self.clash(lhs, rhs),
                    .placeholder => continue,
                },
                .placeholder => continue,
            };
            const rhs_app = switch (rhs_node) {
                .app => |app| app,
                .variable => if (self.undecided(lhs_app.term_id)) {
                    try self.rewritePair(lhs, rhs);
                    continue;
                } else return self.clash(lhs, rhs),
                .placeholder => continue,
            };
            if (self.undecided(lhs_app.term_id) or self.undecided(rhs_app.term_id)) {
                try self.rewritePair(lhs, rhs);
                continue;
            }
            if (lhs_app.term_id == rhs_app.term_id and lhs_app.args.len == rhs_app.args.len) {
                for (lhs_app.args, rhs_app.args) |l, r| try self.equate(l, r);
                continue;
            }
            return self.clash(lhs, rhs);
        }
    }

    /// `lhs` and `rhs`, decided and different, cannot be equal. A trial's
    /// clash only rules out its rule, so it is not the one to report.
    fn clash(self: *Solver, lhs: ExprId, rhs: ExprId) error{Clash} {
        if (!self.in_trial) self.clash_terms = .{ lhs, rhs };
        return error.Clash;
    }

    /// `lhs = rhs`, where a side is headed by a `@rewrite` head. Each
    /// side's normal form equals it under any binding of the pass's
    /// variables, since no rewrite that needs a binding to avoid a variable
    /// fires through one (`mint`). A normal form headed by a definition
    /// unfolds (`definitionPair`). When both normal forms are decided by
    /// their heads they are equated; otherwise the equation waits for more
    /// bindings.
    fn rewritePair(self: *Solver, lhs: ExprId, rhs: ExprId) !void {
        const lhs_normal = try self.normalForm(lhs);
        const rhs_normal = try self.normalForm(rhs);
        if (lhs_normal == rhs_normal) return;
        if (self.definitionHead(lhs_normal) != null or self.definitionHead(rhs_normal) != null) {
            return self.definitionPair(lhs_normal, rhs_normal);
        }
        if (self.decided(lhs_normal) and self.decided(rhs_normal)) {
            return self.equate(lhs_normal, rhs_normal);
        }
        try self.postpone(lhs, rhs);
    }

    /// `lhs = rhs` with a side headed by a definition. Two applications of
    /// one definition that every argument determines (`argDetermined`) are
    /// equal just when their arguments are, so those are equated; unfolding
    /// both instead would walk the two bodies to the bottom, once per use
    /// of each nested definition. Otherwise the later
    /// definition unfolds (a definition mentions only earlier ones, so
    /// this ends), and its body is equated with the other side. A
    /// definition application equals only what its body equals, so this
    /// forces nothing a solution lacks. The body's hidden variables must
    /// stay out of the arguments, which the pass does not check: a value
    /// that breaks that leaves no solution at all, and the walk reports it.
    fn definitionPair(self: *Solver, lhs: ExprId, rhs: ExprId) !void {
        const lhs_def = self.definitionHead(lhs);
        const rhs_def = self.definitionHead(rhs);
        if (lhs_def != null and rhs_def != null and lhs_def.? == rhs_def.?) {
            const theorem = self.inputs.theorem;
            const theory = self.inputs.theory;
            const lhs_app = theorem.interner.node(self.resolve(lhs)).app;
            const rhs_app = theorem.interner.node(self.resolve(rhs)).app;
            const determined = for (0..lhs_app.args.len) |i| {
                if (!HeadClass.argDetermined(&theory.env, &theory.registry, lhs_app.term_id, i)) break false;
            } else lhs_app.args.len == rhs_app.args.len;
            if (determined) {
                for (lhs_app.args, rhs_app.args) |l, r| try self.equate(l, r);
                return;
            }
        }
        const unfold_lhs = lhs_def != null and (rhs_def == null or lhs_def.? >= rhs_def.?);
        if (unfold_lhs) {
            try self.equate(try self.unfoldDefinition(lhs), rhs);
        } else {
            try self.equate(lhs, try self.unfoldDefinition(rhs));
        }
    }

    /// The definition heading `expr`, if any.
    fn definitionHead(self: *const Solver, expr: ExprId) ?u32 {
        return switch (self.inputs.theorem.interner.node(self.resolve(expr)).*) {
            .app => |app| if (self.inputs.theory.env.openableDef(app.term_id) != null) app.term_id else null,
            else => null,
        };
    }

    /// The body of a definition application, with a fresh variable for
    /// each of the definition's hidden variables, which binds to the
    /// variable the other side puts there.
    fn unfoldDefinition(self: *Solver, expr: ExprId) !ExprId {
        const theorem = self.inputs.theorem;
        const allocator = self.inputs.allocator;
        const app = theorem.interner.node(self.resolve(expr)).app;
        const term = self.inputs.theory.env.openableDef(app.term_id).?;
        const binders = try allocator.alloc(ExprId, app.args.len + term.dummy_args.len);
        defer allocator.free(binders);
        @memcpy(binders[0..app.args.len], app.args);
        for (term.dummy_args, binders[app.args.len..]) |dummy, *binder| {
            binder.* = try self.mint(dummy.sort_name);
        }
        return theorem.instantiateTemplate(term.body.?, binders);
    }

    /// The normal form of `expr` with the bindings made so far written in;
    /// `expr` itself when it cannot be normalized.
    fn normalForm(self: *Solver, expr: ExprId) !ExprId {
        const resolved = try self.resolveFully(expr);
        const theory = self.inputs.theory;
        if (self.canonicalizer == null) self.canonicalizer = Canonicalizer.init(
            self.inputs.allocator,
            self.inputs.theorem,
            &theory.registry,
            &theory.env,
            {},
        );
        return self.canonicalizer.?.canonicalizeWithFreshBudget(resolved) catch |err| switch (err) {
            error.OutOfMemory => return err,
            else => resolved,
        };
    }

    /// Whether `expr` can be compared by its head: anything but an
    /// application of a definition or a `@rewrite` head.
    fn decided(self: *const Solver, expr: ExprId) bool {
        return switch (self.inputs.theorem.interner.node(self.resolve(expr)).*) {
            .app => |app| !self.undecided(app.term_id),
            else => true,
        };
    }

    /// Heads whose applications may equal a different head: a definition
    /// (it unfolds) or a `@rewrite` head (it rewrites).
    fn undecided(self: *const Solver, term_id: u32) bool {
        const theory = self.inputs.theory;
        return theory.env.openableDef(term_id) != null or
            theory.registry.getRewriteRules(term_id).len != 0;
    }

    /// The `@acui` combiner `expr` is an application of, if any.
    fn combinerOf(self: *const Solver, expr: ExprId) ?AcuiBag.Combiner {
        const theory = self.inputs.theory;
        const app = switch (self.inputs.theorem.interner.node(expr).*) {
            .app => |app| app,
            else => return null,
        };
        if (app.args.len != 2) return null;
        // Read as a proof can follow it: the unit is a member like any
        // other unless unit laws remove it from both sides.
        return AcuiBag.Combiner.provable(&theory.registry, &theory.env, app.term_id);
    }

    // ---------------------------------------------------------------
    // The bag step: two bags of one combiner, equal modulo its laws.
    // Leaves are members, except the pass's own variables of the bag's
    // sort, which are rests (they stand for any part of the bag). A
    // theorem variable is a rigid member. Only forced conclusions are
    // drawn; anything else waits for more bindings (`postponed`).

    fn bagStep(self: *Solver, combiner: AcuiBag.Combiner, lhs: ExprId, rhs: ExprId) !void {
        const allocator = self.inputs.allocator;
        var left: std.ArrayListUnmanaged(ExprId) = .empty;
        defer left.deinit(allocator);
        var right: std.ArrayListUnmanaged(ExprId) = .empty;
        defer right.deinit(allocator);
        var units: [2]usize = .{ 0, 0 };
        try self.flattenBag(combiner, lhs, &left, &units[0]);
        try self.flattenBag(combiner, rhs, &right, &units[1]);
        // A leaf under a definition or `@rewrite` head may stand for any
        // number of members, and a combiner with rewrites of its own may
        // equal other bags: neither is decided by member counting.
        if (self.undecided(combiner.head) or self.anyUndecidedLeaf(left.items) or
            self.anyUndecidedLeaf(right.items))
        {
            try self.postpone(lhs, rhs);
            return;
        }
        const done = switch (combiner.law) {
            .multiset => try self.bagMultiset(combiner, &left, &right, units),
            .set => try self.bagSet(combiner, &left, &right, units),
            // A dropped unit shifts the positions the pairing reads.
            .sequence => units[0] == 0 and units[1] == 0 and
                try self.bagSequence(combiner, left.items, right.items),
            .idempotent_sequence => false,
        };
        if (!done) try self.postpone(lhs, rhs);
    }

    /// The leaves of `expr` under `combiner`, in order, resolved, without
    /// the unit when unit laws remove it; `units` counts the units dropped.
    fn flattenBag(
        self: *Solver,
        combiner: AcuiBag.Combiner,
        expr: ExprId,
        out: *std.ArrayListUnmanaged(ExprId),
        units: *usize,
    ) !void {
        const resolved = self.resolve(expr);
        if (!self.isVariable(resolved)) switch (self.inputs.theorem.interner.node(resolved).*) {
            .app => |app| {
                if (app.term_id == combiner.head and app.args.len == 2) {
                    try self.flattenBag(combiner, app.args[0], out, units);
                    try self.flattenBag(combiner, app.args[1], out, units);
                    return;
                }
                if (combiner.unit) |unit| if (app.term_id == unit and app.args.len == 0) {
                    units.* += 1;
                    return;
                };
            },
            else => {},
        };
        try out.append(self.inputs.allocator, resolved);
    }

    /// Split `leaves` into members and rests.
    fn partition(
        self: *Solver,
        leaves: []const ExprId,
        members: *std.ArrayListUnmanaged(ExprId),
        rests: *std.ArrayListUnmanaged(ExprId),
    ) !void {
        for (leaves) |leaf| {
            if (self.isVariable(leaf))
                try rests.append(self.inputs.allocator, leaf)
            else
                try members.append(self.inputs.allocator, leaf);
        }
    }

    /// Multiset law: cancel identical members; then, when one side has no
    /// rest, each member of the other side is a distinct member of it, and
    /// a single rest takes what is left. True when the equation is done.
    fn bagMultiset(
        self: *Solver,
        combiner: AcuiBag.Combiner,
        left: *std.ArrayListUnmanaged(ExprId),
        right: *std.ArrayListUnmanaged(ExprId),
        units: [2]usize,
    ) !bool {
        cancelIdentical(left, right);
        const allocator = self.inputs.allocator;
        var lm: std.ArrayListUnmanaged(ExprId) = .empty;
        defer lm.deinit(allocator);
        var lr: std.ArrayListUnmanaged(ExprId) = .empty;
        defer lr.deinit(allocator);
        var rm: std.ArrayListUnmanaged(ExprId) = .empty;
        defer rm.deinit(allocator);
        var rr: std.ArrayListUnmanaged(ExprId) = .empty;
        defer rr.deinit(allocator);
        try self.partition(left.items, &lm, &lr);
        try self.partition(right.items, &rm, &rr);
        if (lr.items.len != 0 and rr.items.len != 0) return false;
        const open_m, const open_r, const closed_m, const closed_units = if (lr.items.len != 0)
            .{ lm.items, lr.items, rm.items, units[1] }
        else
            .{ rm.items, rr.items, lm.items, units[0] };
        if (open_m.len > closed_m.len) return error.Clash;
        if (open_r.len == 0 and open_m.len != closed_m.len) return error.Clash;
        const assignment = (try self.uniqueMatching(open_m, closed_m)) orelse return false;
        defer allocator.free(assignment);
        const used = try allocator.alloc(bool, closed_m.len);
        defer allocator.free(used);
        @memset(used, false);
        for (open_m, assignment) |member, target| {
            used[target] = true;
            try self.equate(member, closed_m[target]);
        }
        if (open_r.len != 1) return open_r.len == 0;
        var leftover: std.ArrayListUnmanaged(ExprId) = .empty;
        defer leftover.deinit(allocator);
        for (closed_m, used) |member, taken| if (!taken) try leftover.append(allocator, member);
        try self.appendUnits(combiner, closed_units, &leftover);
        const value = (try combiner.build(self.inputs.theorem, leftover.items)) orelse return false;
        try self.equate(open_r[0], value);
        return true;
    }

    /// Set law: when one side has no rest, each member of the other side is
    /// one of its members; commit those with a single candidate. A side
    /// that is a single rest takes the other, when that has no rest.
    fn bagSet(
        self: *Solver,
        combiner: AcuiBag.Combiner,
        left: *std.ArrayListUnmanaged(ExprId),
        right: *std.ArrayListUnmanaged(ExprId),
        units: [2]usize,
    ) !bool {
        const allocator = self.inputs.allocator;
        dedupe(left);
        dedupe(right);
        var lm: std.ArrayListUnmanaged(ExprId) = .empty;
        defer lm.deinit(allocator);
        var lr: std.ArrayListUnmanaged(ExprId) = .empty;
        defer lr.deinit(allocator);
        var rm: std.ArrayListUnmanaged(ExprId) = .empty;
        defer rm.deinit(allocator);
        var rr: std.ArrayListUnmanaged(ExprId) = .empty;
        defer rr.deinit(allocator);
        try self.partition(left.items, &lm, &lr);
        try self.partition(right.items, &rm, &rr);
        if (rr.items.len == 0) try self.commitUniqueCandidates(lm.items, rm.items);
        if (lr.items.len == 0) try self.commitUniqueCandidates(rm.items, lm.items);
        if (lm.items.len == 0 and lr.items.len == 1 and rr.items.len == 0) {
            try self.appendUnits(combiner, @min(units[1], 1), &rm);
            try self.equate(lr.items[0], (try combiner.build(self.inputs.theorem, rm.items)) orelse return false);
            return true;
        }
        if (rm.items.len == 0 and rr.items.len == 1 and lr.items.len == 0) {
            try self.appendUnits(combiner, @min(units[0], 1), &lm);
            try self.equate(rr.items[0], (try combiner.build(self.inputs.theorem, lm.items)) orelse return false);
            return true;
        }
        return lr.items.len == 0 and rr.items.len == 0;
    }

    /// Append `count` units to `members`: a rest's value keeps the units
    /// the closed side writes, so it is spelled as the source spells it.
    fn appendUnits(
        self: *Solver,
        combiner: AcuiBag.Combiner,
        count: usize,
        members: *std.ArrayListUnmanaged(ExprId),
    ) !void {
        const unit = combiner.unit orelse return;
        const unit_expr = try self.inputs.theorem.interner.internApp(unit, &.{});
        for (0..count) |_| try members.append(self.inputs.allocator, unit_expr);
    }

    /// Each of `members` equals one of `candidates`: commit those that can
    /// equal only one; a member that can equal none is a clash.
    fn commitUniqueCandidates(self: *Solver, members: []const ExprId, candidates: []const ExprId) !void {
        for (members) |member| {
            var only: ?ExprId = null;
            var count: usize = 0;
            for (candidates) |candidate| {
                if (!try self.compatible(member, candidate)) continue;
                count += 1;
                only = candidate;
            }
            if (count == 0) return error.Clash;
            if (count == 1) try self.equate(member, only.?);
        }
    }

    /// Sequence law: cancel the common ends; then pair positionally when
    /// neither side has a rest, or around a single rest on one side.
    fn bagSequence(
        self: *Solver,
        combiner: AcuiBag.Combiner,
        left_all: []const ExprId,
        right_all: []const ExprId,
    ) !bool {
        var left = left_all;
        var right = right_all;
        while (left.len != 0 and right.len != 0 and left[0] == right[0]) {
            left = left[1..];
            right = right[1..];
        }
        while (left.len != 0 and right.len != 0 and left[left.len - 1] == right[right.len - 1]) {
            left = left[0 .. left.len - 1];
            right = right[0 .. right.len - 1];
        }
        const left_rests = self.countRests(left);
        const right_rests = self.countRests(right);
        if (left_rests == 0 and right_rests == 0) {
            if (left.len != right.len) return error.Clash;
            for (left, right) |l, r| try self.equate(l, r);
            return true;
        }
        if (left_rests != 0 and right_rests != 0) return false;
        const open, const closed = if (left_rests != 0) .{ left, right } else .{ right, left };
        if (self.countRests(open) != 1) return false;
        const at = for (open, 0..) |leaf, i| {
            if (self.isVariable(leaf)) break i;
        } else unreachable;
        const before = open[0..at];
        const after = open[at + 1 ..];
        if (before.len + after.len > closed.len) return error.Clash;
        for (before, closed[0..before.len]) |l, r| try self.equate(l, r);
        for (after, closed[closed.len - after.len ..]) |l, r| try self.equate(l, r);
        const middle = closed[before.len .. closed.len - after.len];
        try self.equate(open[at], (try combiner.build(self.inputs.theorem, middle)) orelse return false);
        return true;
    }

    fn anyUndecidedLeaf(self: *const Solver, leaves: []const ExprId) bool {
        for (leaves) |leaf| switch (self.inputs.theorem.interner.node(leaf).*) {
            .app => |app| if (self.undecided(app.term_id)) return true,
            else => {},
        };
        return false;
    }

    fn countRests(self: *const Solver, leaves: []const ExprId) usize {
        var count: usize = 0;
        for (leaves) |leaf| {
            if (self.isVariable(leaf)) count += 1;
        }
        return count;
    }

    /// The only injective assignment of `members` into `targets` that pairs
    /// only compatible terms, or null when there are several; a clash when
    /// there is none. Caller frees.
    fn uniqueMatching(self: *Solver, members: []const ExprId, targets: []const ExprId) !?[]usize {
        const allocator = self.inputs.allocator;
        const compat = try allocator.alloc(bool, members.len * targets.len);
        defer allocator.free(compat);
        for (members, 0..) |member, i| for (targets, 0..) |target, j| {
            compat[i * targets.len + j] = try self.compatible(member, target);
        };
        var matcher = try AcuiBag.Matching.init(allocator, compat, members.len, targets.len);
        defer matcher.deinit(allocator);
        if (!matcher.run(null)) return error.Clash;
        const assignment = try allocator.alloc(usize, members.len);
        errdefer allocator.free(assignment);
        for (matcher.owner, 0..) |owner, j| if (owner) |i| {
            assignment[i] = j;
        };
        // Another matching differs from this one in some member's pair:
        // forbid each pair in turn and look for one.
        for (assignment, 0..) |target, member| {
            if (matcher.run(.{ member, target })) {
                allocator.free(assignment);
                return null;
            }
        }
        return assignment;
    }

    /// Whether `lhs` and `rhs` could be equal: false only when no binding
    /// of the pass's variables makes them so. A side under a `@rewrite` or
    /// definition head is read by its normal form (`decidedForm`), so a
    /// substitution its bindings let fire is told apart by the head it
    /// rewrites to.
    fn compatible(self: *Solver, lhs_id: ExprId, rhs_id: ExprId) !bool {
        const lhs = try self.decidedForm(lhs_id);
        const rhs = try self.decidedForm(rhs_id);
        if (lhs == rhs or self.isVariable(lhs) or self.isVariable(rhs)) return true;
        const theorem = self.inputs.theorem;
        const lhs_node = theorem.interner.node(lhs).*;
        const rhs_node = theorem.interner.node(rhs).*;
        switch (lhs_node) {
            .placeholder => return true,
            .variable => return switch (rhs_node) {
                .app => |app| self.flexibleHead(app.term_id),
                .variable => false,
                .placeholder => true,
            },
            .app => |lhs_app| switch (rhs_node) {
                .placeholder => return true,
                .variable => return self.flexibleHead(lhs_app.term_id),
                .app => |rhs_app| {
                    if (lhs_app.term_id != rhs_app.term_id or lhs_app.args.len != rhs_app.args.len) {
                        return self.flexibleHead(lhs_app.term_id) or self.flexibleHead(rhs_app.term_id);
                    }
                    if (self.flexibleHead(lhs_app.term_id)) return true;
                    for (lhs_app.args, rhs_app.args) |l, r| {
                        if (!try self.compatible(l, r)) return false;
                    }
                    return true;
                },
            },
        }
    }

    /// `id` resolved, or its normal form when it sits under a `@rewrite`
    /// or definition head. The normal form equals it under any binding of
    /// the pass's variables (`mint`), so comparing it forces nothing more.
    fn decidedForm(self: *Solver, id: ExprId) !ExprId {
        const resolved = self.resolve(id);
        if (self.decided(resolved)) return resolved;
        return self.normalForm(resolved);
    }

    /// Heads whose applications may equal a term with another head.
    fn flexibleHead(self: *const Solver, term_id: u32) bool {
        const theory = self.inputs.theory;
        return self.undecided(term_id) or
            AcuiBag.Combiner.of(&theory.registry, &theory.env, term_id) != null;
    }

    fn bind(self: *Solver, variable: ExprId, value: ExprId) !void {
        if (self.occurs(variable, value)) return error.Clash;
        const env = &self.inputs.theory.env;
        const theorem = self.inputs.theorem;
        const want = try SurfaceExpr.exprIdSortName(theorem, env, variable);
        const have = try SurfaceExpr.exprIdSortName(theorem, env, value);
        if (!std.mem.eql(u8, want, have)) return error.Clash;
        const allowed = try theorem.exprDeps(variable, .{});
        // Bind the wider of two pass variables to the narrower.
        if (self.isVariable(value)) {
            const other = try theorem.exprDeps(value, .{});
            if (other != allowed and allowed & ~other == 0) return self.bind(value, variable);
        }
        if (allowed != std.math.maxInt(u55)) try self.restrict(value, allowed);
        if (self.in_trial) try self.trail.append(self.inputs.allocator, variable);
        self.variables.getPtr(variable).?.binding = value;
        self.progress += 1;
    }

    fn occurs(self: *Solver, variable: ExprId, expr: ExprId) bool {
        self.seen.begin();
        return self.occursIn(variable, expr);
    }

    fn occursIn(self: *Solver, variable: ExprId, expr: ExprId) bool {
        const resolved = self.resolve(expr);
        if (resolved == variable) return true;
        return switch (self.inputs.theorem.interner.node(resolved).*) {
            .app => |app| self.seen.enter(self.inputs.allocator, resolved) and for (app.args) |arg| {
                if (self.occursIn(variable, arg)) break true;
            } else false,
            else => false,
        };
    }

    fn resolveFully(self: *Solver, expr: ExprId) !ExprId {
        if (self.resolved.count() != 0) self.resolved.clearRetainingCapacity();
        return self.resolveFullyIn(expr);
    }

    fn resolveFullyIn(self: *Solver, expr: ExprId) !ExprId {
        const theorem = self.inputs.theorem;
        const resolved = self.resolve(expr);
        const app = switch (theorem.interner.node(resolved).*) {
            .app => |app| app,
            else => return resolved,
        };
        if (self.resolved.get(resolved)) |known| return known;
        const args = try theorem.allocator.alloc(ExprId, app.args.len);
        defer theorem.allocator.free(args);
        var changed = false;
        for (app.args, args) |arg, *out| {
            out.* = try self.resolveFullyIn(arg);
            if (out.* != arg) changed = true;
        }
        const value = if (changed) try theorem.interner.internApp(app.term_id, args) else resolved;
        try self.resolved.put(self.inputs.allocator, resolved, value);
        return value;
    }

    fn mentionsVariable(self: *Solver, expr: ExprId) bool {
        self.seen.begin();
        return self.mentionsFromIn(expr, 0);
    }

    /// What a resolved `value` that mentions a variable shows of itself.
    /// A part under a `@rewrite` head that mentions one shows nothing: what
    /// it rewrites to waits on the variable, so it is a variable of its own.
    fn visibleShape(self: *Solver, value: ExprId) !ExprId {
        var shown: std.AutoHashMapUnmanaged(ExprId, ExprId) = .empty;
        defer shown.deinit(self.inputs.allocator);
        return self.visibleShapeIn(value, &shown);
    }

    fn visibleShapeIn(
        self: *Solver,
        value: ExprId,
        shown: *std.AutoHashMapUnmanaged(ExprId, ExprId),
    ) !ExprId {
        const theorem = self.inputs.theorem;
        const app = switch (theorem.interner.node(value).*) {
            .app => |app| app,
            else => return value,
        };
        if (shown.get(value)) |known| return known;
        const result = if (!self.mentionsVariable(value))
            value
        else if (self.rewriteOnly(app.term_id))
            try self.mint(try SurfaceExpr.exprIdSortName(theorem, &self.inputs.theory.env, value))
        else blk: {
            const args = try theorem.allocator.alloc(ExprId, app.args.len);
            defer theorem.allocator.free(args);
            for (app.args, args) |arg, *out| out.* = try self.visibleShapeIn(arg, shown);
            break :blk try theorem.interner.internApp(app.term_id, args);
        };
        try shown.put(self.inputs.allocator, value, result);
        return result;
    }
};

/// Remove members the two sides share, one copy at a time.
fn cancelIdentical(left: *std.ArrayListUnmanaged(ExprId), right: *std.ArrayListUnmanaged(ExprId)) void {
    var i: usize = 0;
    outer: while (i < left.items.len) {
        for (right.items, 0..) |item, j| {
            if (item != left.items[i]) continue;
            _ = left.orderedRemove(i);
            _ = right.orderedRemove(j);
            continue :outer;
        }
        i += 1;
    }
}

/// Drop repeated leaves (set law).
fn dedupe(list: *std.ArrayListUnmanaged(ExprId)) void {
    var len: usize = 0;
    for (list.items) |item| {
        if (std.mem.indexOfScalar(ExprId, list.items[0..len], item) != null) continue;
        list.items[len] = item;
        len += 1;
    }
    list.shrinkRetainingCapacity(len);
}

/// Whether a line could name an unknown: the walk then holds what it
/// reports of a line to the end of the block, as a later line may bind a
/// name it shows (a cheap test before parsing).
pub fn mayNameUnknowns(parser: *const MM0Parser, lines: []const ProofLine) bool {
    return anyText(parser, lines, textMayName);
}

/// Whether a line could hold a hole, named or not, in its statement or in
/// an explicit binding.
fn mayHoldHoles(parser: *const MM0Parser, lines: []const ProofLine) bool {
    return anyText(parser, lines, textMayHold);
}

const TextTest = fn (*const MM0Parser, []const u8) bool;

fn anyText(parser: *const MM0Parser, lines: []const ProofLine, comptime may: TextTest) bool {
    for (lines) |line| {
        if (may(parser, line.assertion.text) or applicationAnyText(parser, line.application, may)) return true;
    }
    return false;
}

/// Whether `app` or one of its inline sub-proofs cites a line in `labels`.
fn citesAny(app: RuleApplication, labels: *const std.StringHashMapUnmanaged(void)) bool {
    for (app.refs) |ref| switch (ref) {
        .hyp => {},
        .line => |label| if (labels.contains(label.label)) return true,
        .application => |child| if (citesAny(child, labels)) return true,
    };
    return false;
}

/// Whether an explicit binding of `app` or of its inline sub-proofs may
/// hold a hole.
fn applicationMayHold(parser: *const MM0Parser, app: RuleApplication) bool {
    return applicationAnyText(parser, app, textMayHold);
}

fn applicationAnyText(parser: *const MM0Parser, app: RuleApplication, comptime may: TextTest) bool {
    for (app.arg_bindings) |binding| {
        if (may(parser, binding.formula.text)) return true;
    }
    for (app.refs) |ref| switch (ref) {
        .application => |child| if (applicationAnyText(parser, child, may)) return true,
        else => {},
    };
    return false;
}

/// Whether `text` holds an `@unknown` prefix.
fn textMayName(parser: *const MM0Parser, text: []const u8) bool {
    var it = parser.core.unknown_prefixes.keyIterator();
    while (it.next()) |prefix| {
        if (std.mem.indexOf(u8, text, prefix.*) != null) return true;
    }
    return false;
}

/// Whether `text` holds an `@hole` token or an `@unknown` prefix.
fn textMayHold(parser: *const MM0Parser, text: []const u8) bool {
    var it = parser.core.hole_tokens.keyIterator();
    while (it.next()) |token| {
        if (std.mem.indexOf(u8, text, token.*) != null) return true;
    }
    return textMayName(parser, text);
}

fn isOrdinaryRuleName(name: []const u8) bool {
    return !ProofScript.isOpenGoalRuleName(name) and
        !ProofScript.isSorryRuleName(name) and
        !ProofScript.isSearchPlaceholderRuleName(name);
}
