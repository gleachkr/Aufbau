//! Terms for the search core: canonical bags, matching a rule conclusion
//! against a goal, and building a rule's premises.
//!
//! Every expression the core works on is canonical: each commutative
//! `@acui` bag lists its members once per occurrence its law counts, in
//! `ExprId` order, and a sequence (associative with a unit, nothing more)
//! lists its members in their own order, so two ground goals equal modulo
//! ACUI are the same `ExprId`. The order is only stable within one
//! theorem's interner, which is all one core run uses. A goal holding
//! witness variables (`wvars.zig`) is canonical as written, with each wvar
//! a leaf; once a binding changes it, `resolveGoal` makes it canonical
//! again.
//!
//! Matching enumerates every way a conclusion template fits a goal, and
//! unifies through the witness variables: a binder met twice must agree
//! with its first value, and an unbound wvar on either side takes the other
//! side's term. Each unifier is an alternative, run in place by the sink
//! while its bindings hold. A bag member of the template takes a distinct
//! goal member; each choice is an alternative. The bag's rest binder takes
//! what is left over, which is the minimal complement: a set law would
//! also allow the rest to keep a member the template already claims, which
//! the core does not try yet. A bag with several rest binders (shares,
//! under a set law) leaves them unbound and reports the split (`split`) for
//! the prover to settle. Two bags holding wvars unify member by member
//! (`pairBags`); an unbound wvar of the bag's own sort, such as a share,
//! stands for a part of the bag and takes the other bag's members nothing
//! else pairs with. A sequence matches in order instead: a template member
//! takes the next goal member and a rest binder a run of them, and two
//! sequences unify member by member, where one unbound wvar of the
//! sequence's sort takes the run its neighbours leave. An unbound goal
//! wvar facing template structure takes it by narrowing: the node waits
//! for the end of the match, and once the rest of the conclusion has bound
//! the node's binders it is instantiated and unified with the wvar. A
//! binder left unbound fails the match, so a wvar takes only structure the
//! goal fixes elsewhere, never a guess: a goal that is a bare wvar meets no
//! conclusion with binders. A sink with `mayInvent` may instead give such
//! binders cut wvars of their own (`Matcher.invent`), for premises to fix
//! from facts, and bound ones bound names (`wvars.zig`), while the node
//! holds a binder the match bound.
//!
//! Matching and unification are modulo definitions: where heads differ,
//! an application of the later-declared definition unfolds one step
//! (`unfold`, or `unfoldTemplate` for one in a rule's template) and the
//! match goes on, since a definition's body only uses terms declared
//! before it. Equal heads compare argument by argument. A template's
//! definition with dummies does not unfold: its dummies would need binders
//! the rule does not have. The checker makes the same conversion when it
//! validates the proof.
//!
//! A goal holding a term some `@rewrite` rule rewrites also has a normal
//! form (`normalForm`), which the prover tries beside it: the conversion to
//! it is the checker's normalization. A part of it holding a γ witness
//! variable has none yet, since what the variable becomes decides a
//! rewrite's dependency conditions (`sb_t x t a` drops the substitution
//! only when `a` does not depend on `x`); an eigenvariable normalizes as a
//! fresh bound variable, which is what it becomes. `openNormalForm` takes
//! one with every wvar as a fresh bound variable: each step it makes holds
//! for any value that, like the stand-in, holds no bound variable of the
//! expression.
//!
//! A rule's conclusion may hold such a term too (`nat_ind_elim`'s type
//! `[k/n] C`). Against a goal node with its head it matches argument by
//! argument; against any other it is postponed until the rest of the match
//! has bound its binders, then instantiated and unified with the goal node
//! in normal form. One whose binders the match leaves unbound (cuts,
//! `catalog.zig`) is reported (`postponed`) for the prover to check once
//! the premises bind them.

const std = @import("std");
const ExprId = @import("../../../expr.zig").ExprId;
const TheoremContext = @import("../../../expr.zig").TheoremContext;
const Rules = @import("../../../rules.zig");
const TemplateExpr = Rules.TemplateExpr;
const RuleDecl = @import("../../../env.zig").RuleDecl;
const AcuiBag = @import("../../../acui_bag.zig");
const Context = @import("../types.zig").Context;
const catalog = @import("./catalog.zig");
const WVars = @import("./wvars.zig").WVars;
const ExprFlags = @import("./wvars.zig").ExprFlags;
const ExprMap = @import("./wvars.zig").ExprMap;
const Canonicalizer = @import("../../../normalizer.zig").Canonicalizer;

pub const Error = error{
    OutOfMemory,
    TooManyTheoremExprs,
    /// The term is outside what the core reads: a bag past
    /// `AcuiBag.capacity`, or an application wider than `catalog.max_args`.
    Unsupported,
};

const TemplateKey = struct { args: usize, term_id: u32 };

/// One unfolding of an expression (`Terms.unfold`): its result, with the
/// wvars from `dummies` on, `count` of them, as its dummies, and the
/// expression's older unfoldings.
const Unfolded = struct { result: ExprId, dummies: u32, count: u32, next: ?*const Unfolded };

pub const Terms = struct {
    allocator: std.mem.Allocator,
    context: *const Context,
    theorem: *TheoremContext,
    wvars: *WVars,
    /// The bag the shares of the conclusion match in progress split, while
    /// the sink runs.
    split: ?SplitBag = null,
    /// The conclusion nodes the match in progress left to check once the
    /// premises bind their binders, while the sink runs.
    postponed: ?*const Postponed = null,
    /// The cut wvars the match in progress minted for binders a narrowing
    /// left unbound, while the sink runs.
    invented: ?*const Invented = null,
    /// The bag combiner each combiner head and each unit term reads as, by
    /// term id.
    bags: []?AcuiBag.Combiner = &.{},
    /// Whether some `@rewrite` rule rewrites each term, by term id.
    rewritten: []bool = &.{},
    /// Whether each term is a definition `unfold` opens, by term id.
    opens: []bool = &.{},
    canonical_memo: ExprMap = .{},
    /// One-step unfoldings of definition applications, newest first; an
    /// expression's only one is itself when its body is past what the core
    /// reads. They live in `template_arena`.
    unfold_memo: std.AutoHashMapUnmanaged(ExprId, *const Unfolded) = .empty,
    /// Whether an expression holds an application of a definition the core
    /// can unfold.
    defs: ExprFlags = .{},
    /// Whether an expression holds an application of a term some
    /// `@rewrite` rule rewrites.
    redexes: ExprFlags = .{},
    /// Normal forms; an expression maps to itself when it is its own, or
    /// the rewrites fail on it.
    normal_memo: ExprMap = .{},
    /// Created on the first normal form; its cache lasts the run.
    canonicalizer: ?Canonicalizer = null,
    /// Template unfoldings (`unfoldTemplate`), null for a definition that
    /// does not unfold; their argument lists live in `template_arena`.
    template_unfolds: std.AutoHashMapUnmanaged(TemplateKey, ?TemplateExpr) = .empty,
    template_arena: std.heap.ArenaAllocator,
    /// Bound variables that stand in for eigenvariables while a goal is
    /// normalized (`standInNormal`), each with its sort.
    stand_ins: std.ArrayListUnmanaged(struct { sort_name: []const u8, expr: ExprId }) = .empty,

    pub fn init(
        allocator: std.mem.Allocator,
        context: *const Context,
        theorem: *TheoremContext,
        wvars: *WVars,
    ) Error!Terms {
        var self = Terms{
            .allocator = allocator,
            .context = context,
            .theorem = theorem,
            .wvars = wvars,
            .template_arena = std.heap.ArenaAllocator.init(allocator),
        };
        errdefer self.deinit();
        const term_count = context.env.terms.items.len;
        self.bags = try allocator.alloc(?AcuiBag.Combiner, term_count);
        @memset(self.bags, null);
        self.rewritten = try allocator.alloc(bool, term_count);
        for (self.rewritten, 0..) |*rewritten, term_id| {
            rewritten.* = context.registry.getRewriteRules(@intCast(term_id)).len != 0;
        }
        self.opens = try allocator.alloc(bool, term_count);
        for (self.opens, 0..) |*opens, term_id| opens.* = context.env.openableDef(@intCast(term_id)) != null;
        var it = context.registry.acui_by_head.keyIterator();
        while (it.next()) |head| {
            const combiner = AcuiBag.Combiner.of(context.registry, context.env, head.*) orelse continue;
            if (!catalog.readsLaw(combiner.law)) continue;
            self.bags[combiner.head] = combiner;
            if (combiner.unit) |unit| self.bags[unit] = combiner;
        }
        return self;
    }

    pub fn deinit(self: *Terms) void {
        self.allocator.free(self.bags);
        self.allocator.free(self.rewritten);
        self.allocator.free(self.opens);
        self.canonical_memo.deinit(self.allocator);
        self.unfold_memo.deinit(self.allocator);
        self.defs.deinit(self.allocator);
        self.redexes.deinit(self.allocator);
        self.normal_memo.deinit(self.allocator);
        if (self.canonicalizer) |*canonicalizer| canonicalizer.deinit();
        self.stand_ins.deinit(self.allocator);
        self.template_unfolds.deinit(self.allocator);
        self.template_arena.deinit();
        self.* = undefined;
    }

    /// The bag combiner that reads `term_id`: the combiner itself or its
    /// unit. A combiner the core does not read (`catalog.readsLaw`) reads
    /// as an ordinary term; `supported` keeps such goals out.
    pub fn bagFor(self: *const Terms, term_id: u32) ?AcuiBag.Combiner {
        return if (term_id < self.bags.len) self.bags[term_id] else null;
    }

    /// Whether the core can search `expr`: no placeholders or combiners
    /// it does not read. A definition is an ordinary term here, never
    /// unfolded. O(size of `expr`) over shared nodes.
    pub fn supported(self: *Terms, expr: ExprId) Error!bool {
        var seen = std.AutoHashMapUnmanaged(ExprId, void).empty;
        defer seen.deinit(self.allocator);
        return self.supportedWalk(expr, &seen);
    }

    fn supportedWalk(
        self: *Terms,
        expr: ExprId,
        seen: *std.AutoHashMapUnmanaged(ExprId, void),
    ) Error!bool {
        if ((try seen.getOrPut(self.allocator, expr)).found_existing) return true;
        switch (self.theorem.interner.node(expr).*) {
            .variable => return true,
            .placeholder => return false,
            .app => |app| {
                if (app.term_id >= self.context.env.terms.items.len) return false;
                if (AcuiBag.Combiner.of(self.context.registry, self.context.env, app.term_id)) |combiner| {
                    if (!catalog.readsLaw(combiner.law)) return false;
                }
                for (app.args) |arg| {
                    if (!try self.supportedWalk(arg, seen)) return false;
                }
                return true;
            },
        }
    }

    /// `expr`, an application of a definition with a body, unfolded one
    /// step: the body with the arguments in place and each dummy a fresh
    /// eigenvariable introduced at the unfolding. Such a dummy may become
    /// only a variable the unfolding does not otherwise mention, which is
    /// MM0's condition on an unfolding: disjoint from the arguments, and
    /// distinct from its siblings. An expression unfolds with the same
    /// dummies wherever it appears while no step has used them; once one
    /// has, it unfolds again with fresh ones, since each use of a
    /// definition picks its dummies apart. Null when `expr` applies no such
    /// definition or its body is past what the core reads.
    pub fn unfold(self: *Terms, expr: ExprId) Error!?ExprId {
        const app = switch (self.theorem.interner.node(expr).*) {
            .app => |app| app,
            .variable, .placeholder => return null,
        };
        const def = self.context.env.openableDef(app.term_id) orelse return null;
        const known = self.unfold_memo.get(expr);
        if (known) |newest| {
            if (newest.result == expr) return null;
            var at: ?*const Unfolded = newest;
            while (at) |cell| : (at = cell.next) {
                if (self.untouched(cell)) return cell.result;
            }
        }
        const values = try self.allocator.alloc(ExprId, app.args.len + def.dummy_args.len);
        defer self.allocator.free(values);
        @memcpy(values[0..app.args.len], app.args);
        const first = self.wvars.count();
        for (def.dummy_args, values[app.args.len..]) |dummy, *value| {
            value.* = try self.wvars.introduce(dummy.sort_name, expr, null);
        }
        const result = self.instantiate(def.body.?, values) catch |err| switch (err) {
            error.Unsupported => {
                const cell = try self.template_arena.allocator().create(Unfolded);
                cell.* = .{ .result = expr, .dummies = first, .count = 0, .next = null };
                try self.unfold_memo.put(self.allocator, expr, cell);
                return null;
            },
            else => |e| return e,
        };
        for (first..self.wvars.count()) |idx| self.wvars.vars.items[idx].introduced_at = result;
        const cell = try self.template_arena.allocator().create(Unfolded);
        cell.* = .{ .result = result, .dummies = first, .count = self.wvars.count() - first, .next = known };
        try self.unfold_memo.put(self.allocator, expr, cell);
        return result;
    }

    /// Whether no step has bound, barred or narrowed a dummy of `cell`.
    fn untouched(self: *const Terms, cell: *const Unfolded) bool {
        for (cell.dummies..cell.dummies + cell.count) |idx| {
            const wvar = self.wvars.vars.items[idx];
            if (wvar.value != null or wvar.fresh_in != null or wvar.capture.len != 0) return false;
        }
        return true;
    }

    /// The template application `app` of a definition unfolded one step:
    /// its body with `app`'s arguments for its binders. Null when the
    /// definition does not unfold or has dummies.
    pub fn unfoldTemplate(self: *Terms, app: TemplateExpr.App) Error!?TemplateExpr {
        const def = self.context.env.openableDef(app.term_id) orelse return null;
        if (def.dummy_args.len != 0) return null;
        const key = TemplateKey{ .args = @intFromPtr(app.args.ptr), .term_id = app.term_id };
        if (self.template_unfolds.get(key)) |known| return known;
        const result = try self.substTemplate(def.body.?, app.args);
        try self.template_unfolds.put(self.allocator, key, result);
        return result;
    }

    fn substTemplate(self: *Terms, body: TemplateExpr, args: []const TemplateExpr) Error!TemplateExpr {
        return switch (body) {
            .binder => |idx| args[idx],
            .app => |app| blk: {
                const out = try self.template_arena.allocator().alloc(TemplateExpr, app.args.len);
                for (out, app.args) |*slot, arg| slot.* = try self.substTemplate(arg, args);
                break :blk .{ .app = .{ .term_id = app.term_id, .args = out } };
            },
        };
    }

    /// The term `expr` applies, or null for a variable or placeholder.
    pub fn headOf(self: *const Terms, expr: ExprId) ?u32 {
        return switch (self.theorem.interner.node(expr).*) {
            .app => |app| app.term_id,
            .variable, .placeholder => null,
        };
    }

    /// Whether `expr` holds an application of a definition `unfold` opens.
    pub fn holdsDef(self: *Terms, expr: ExprId) Error!bool {
        return self.holdsHead(&self.defs, expr, opensDef);
    }

    /// Whether `term_id` is a definition `unfold` opens.
    pub fn opensDef(self: *const Terms, term_id: u32) bool {
        return term_id < self.opens.len and self.opens[term_id];
    }

    /// Whether a conclusion node applying `term_id` meets only goal nodes
    /// applying it too: nothing rewrites it, it does not unfold and it
    /// reads as no bag (`Matcher.term`). A goal node applying a definition
    /// may still unfold toward it.
    pub fn isRigid(self: *const Terms, term_id: u32) bool {
        return !self.isRewritten(term_id) and !self.opensDef(term_id) and self.bagFor(term_id) == null;
    }

    pub fn isRewritten(self: *const Terms, term_id: u32) bool {
        return term_id < self.rewritten.len and self.rewritten[term_id];
    }

    /// Whether `expr` holds an application of a term `pred` accepts,
    /// memoized in `memo`.
    fn holdsHead(
        self: *Terms,
        memo: *ExprFlags,
        expr: ExprId,
        comptime pred: fn (*const Terms, u32) bool,
    ) Error!bool {
        if (memo.get(expr)) |known| return known;
        const result = switch (self.theorem.interner.node(expr).*) {
            .variable, .placeholder => false,
            .app => |app| blk: {
                if (pred(self, app.term_id)) break :blk true;
                for (app.args) |arg| {
                    if (try self.holdsHead(memo, arg, pred)) break :blk true;
                }
                break :blk false;
            },
        };
        try memo.put(self.allocator, expr, result);
        return result;
    }

    /// The canonical normal form of `expr` under the theory's `@rewrite`
    /// rules, or null when `expr` is its own normal form or the normalizer
    /// fails on it (a rewrite cycle, or past the step limit). Where a γ
    /// wvar decides a rewrite, the arguments around it are normalized
    /// alone.
    pub fn normalForm(self: *Terms, expr: ExprId) Error!?ExprId {
        if (!try self.holdsHead(&self.redexes, expr, isRewritten)) return null;
        const result = try self.normalPart(expr);
        return if (result == expr) null else result;
    }

    fn normalPart(self: *Terms, expr: ExprId) Error!ExprId {
        if (!try self.holdsHead(&self.redexes, expr, isRewritten)) return expr;
        if (!try self.wvars.holdsWVar(expr)) return self.groundNormal(expr);
        // Eigenvariables normalize as fresh bound variables: each is one,
        // which nothing else in the goal depends on. A γ wvar's value
        // decides a rewrite's dependency conditions.
        if (try self.standInNormal(expr, true)) |normal| return normal;
        const app = switch (self.theorem.interner.node(expr).*) {
            .app => |app| app,
            .variable, .placeholder => return expr,
        };
        if (app.args.len > catalog.max_args) return expr;
        var args: [catalog.max_args]ExprId = undefined;
        var changed = false;
        for (app.args, 0..) |arg, idx| {
            args[idx] = try self.normalPart(arg);
            if (args[idx] != arg) changed = true;
        }
        if (!changed) return expr;
        return self.canonical(try self.theorem.interner.internApp(app.term_id, args[0..app.args.len])) catch |err| switch (err) {
            error.Unsupported => expr,
            else => |e| return e,
        };
    }

    /// The normal form of `expr` with every unbound wvar, γ ones too, as a
    /// stand-in bound variable; null when nothing rewrites. It holds for
    /// the values the γ wvars take that, like the stand-ins, hold no bound
    /// variable of `expr` (`WVars.narrowCapture`).
    pub fn openNormalForm(self: *Terms, expr: ExprId) Error!?ExprId {
        if (!try self.holdsHead(&self.redexes, expr, isRewritten)) return null;
        const normal = (try self.standInNormal(expr, false)) orelse return null;
        return if (normal == expr) null else normal;
    }

    /// The normal form of `expr` with each unbound wvar as a stand-in bound
    /// variable, or `expr` itself; null when `only_eigens` and it holds a γ
    /// wvar, or a sort has no stand-in left.
    fn standInNormal(self: *Terms, expr: ExprId, only_eigens: bool) Error!?ExprId {
        var held = std.ArrayListUnmanaged(u32).empty;
        defer held.deinit(self.allocator);
        try self.wvars.collectUnbound(self.allocator, expr, &held);
        var wexprs: [catalog.max_args]ExprId = undefined;
        var stand_ins: [catalog.max_args]ExprId = undefined;
        if (held.items.len > wexprs.len) return null;
        for (held.items, 0..) |idx, at| {
            if (only_eigens and !self.wvars.isEigen(idx)) return null;
            const sort_name = self.wvars.vars.items[idx].sort_name;
            var nth: usize = 0;
            for (held.items[0..at]) |other| {
                if (std.mem.eql(u8, self.wvars.vars.items[other].sort_name, sort_name)) nth += 1;
            }
            wexprs[at] = self.wvars.vars.items[idx].expr;
            stand_ins[at] = (try self.standIn(sort_name, nth)) orelse return null;
        }
        const n = held.items.len;
        const ground = try self.replace(expr, wexprs[0..n], stand_ins[0..n]);
        const normal = try self.groundNormal(ground);
        if (normal == ground) return expr;
        return self.canonical(try self.replace(normal, stand_ins[0..n], wexprs[0..n])) catch |err| switch (err) {
            error.Unsupported => expr,
            else => |e| return e,
        };
    }

    /// The `nth` bound variable of `sort_name` that stands in for an
    /// eigenvariable, minted on first use; null when the theorem has no
    /// dependency slot left for it.
    fn standIn(self: *Terms, sort_name: []const u8, nth: usize) Error!?ExprId {
        var seen: usize = 0;
        for (self.stand_ins.items) |stand_in| {
            if (!std.mem.eql(u8, stand_in.sort_name, sort_name)) continue;
            if (seen == nth) return stand_in.expr;
            seen += 1;
        }
        const sort_id = self.context.parser.core.sort_names.get(sort_name) orelse return null;
        const expr = self.theorem.addDummyVarResolved(sort_name, sort_id) catch |err| switch (err) {
            error.OutOfMemory => return error.OutOfMemory,
            else => return null,
        };
        try self.stand_ins.append(self.allocator, .{ .sort_name = sort_name, .expr = expr });
        return expr;
    }

    /// `expr` with each leaf in `from` replaced by its counterpart in `to`.
    fn replace(self: *Terms, expr: ExprId, from: []const ExprId, to: []const ExprId) Error!ExprId {
        if (std.mem.indexOfScalar(ExprId, from, expr)) |at| return to[at];
        const app = switch (self.theorem.interner.node(expr).*) {
            .app => |app| app,
            .variable, .placeholder => return expr,
        };
        if (app.args.len > catalog.max_args) return error.Unsupported;
        var args: [catalog.max_args]ExprId = undefined;
        var changed = false;
        for (app.args, 0..) |arg, idx| {
            args[idx] = try self.replace(arg, from, to);
            if (args[idx] != arg) changed = true;
        }
        if (!changed) return expr;
        return self.theorem.interner.internApp(app.term_id, args[0..app.args.len]);
    }

    /// The normal form of the wvar-free `expr`, or `expr` itself.
    fn groundNormal(self: *Terms, expr: ExprId) Error!ExprId {
        if (self.normal_memo.get(expr)) |done| return done;
        if (self.canonicalizer == null) {
            self.canonicalizer = Canonicalizer.init(self.allocator, self.theorem, self.context.registry, self.context.env, {});
        }
        const canonicalizer = &self.canonicalizer.?;
        const normal = canonicalizer.canonicalizeWithFreshBudget(expr) catch |err| switch (err) {
            error.OutOfMemory => return error.OutOfMemory,
            error.TooManyTheoremExprs => return error.TooManyTheoremExprs,
            else => expr,
        };
        const result = if (normal == expr) expr else self.canonical(normal) catch |err| switch (err) {
            error.Unsupported => expr,
            else => |e| return e,
        };
        try self.normal_memo.put(self.allocator, expr, result);
        return result;
    }

    /// `expr` with every bag in canonical form.
    pub fn canonical(self: *Terms, expr: ExprId) Error!ExprId {
        if (self.canonical_memo.get(expr)) |done| return done;
        const result: ExprId = switch (self.theorem.interner.node(expr).*) {
            .variable, .placeholder => expr,
            .app => |app| blk: {
                if (self.bagFor(app.term_id)) |combiner| {
                    const members = combiner.flatten(self.theorem, expr) orelse return error.Unsupported;
                    var out: AcuiBag.ExprBag = .{};
                    for (members.slice()) |member| {
                        if (!out.append(try self.canonical(member))) return error.Unsupported;
                    }
                    break :blk try self.buildBag(combiner, &out);
                }
                if (app.args.len > catalog.max_args) return error.Unsupported;
                var args: [catalog.max_args]ExprId = undefined;
                for (app.args, 0..) |arg, idx| args[idx] = try self.canonical(arg);
                break :blk try self.theorem.interner.internApp(app.term_id, args[0..app.args.len]);
            },
        };
        try self.canonical_memo.put(self.allocator, expr, result);
        return result;
    }

    /// The canonical bag of `members`, each already canonical: a
    /// commutative bag sorted, and deduplicated under a set law; a
    /// sequence as it stands.
    fn buildBag(self: *Terms, combiner: AcuiBag.Combiner, members: *AcuiBag.ExprBag) Error!ExprId {
        const items = members.items[0..members.len];
        if (!combiner.law.isCommutative()) {
            return (try combiner.build(self.theorem, items)) orelse error.Unsupported;
        }
        std.mem.sort(ExprId, items, {}, std.sort.asc(ExprId));
        const kept = if (combiner.law.isIdempotent()) AcuiBag.mergeRepeats(items) else items;
        return (try combiner.build(self.theorem, kept)) orelse error.Unsupported;
    }

    /// `expr` with the current bindings applied, canonical.
    pub fn resolveGoal(self: *Terms, expr: ExprId) Error!ExprId {
        if (!try self.wvars.holdsWVar(expr)) return expr;
        return self.canonical(try self.wvars.deref(expr, null));
    }

    /// Whether `a` and `b` are equal under the current bindings.
    fn same(self: *Terms, a: ExprId, b: ExprId) Error!bool {
        if (a == b) return true;
        return try self.resolveGoal(a) == try self.resolveGoal(b);
    }

    /// `pattern` with each free occurrence of the variable `hole` replaced
    /// by `value`, canonical: the instance a quantifier rule's view states.
    /// An occurrence under a binder of `hole` belongs to that binder and
    /// stays.
    pub fn swap(self: *Terms, pattern: ExprId, hole: ExprId, value: ExprId) Error!ExprId {
        return self.canonical(try self.swapWalk(pattern, hole, value));
    }

    fn swapWalk(self: *Terms, expr: ExprId, hole: ExprId, value: ExprId) Error!ExprId {
        if (expr == hole) return value;
        const app = switch (self.theorem.interner.node(expr).*) {
            .app => |app| app,
            .variable, .placeholder => return expr,
        };
        if (app.args.len > catalog.max_args) return error.Unsupported;
        const decl = &self.context.env.terms.items[app.term_id];
        for (app.args, 0..) |arg, idx| {
            if (idx < decl.args.len and decl.args[idx].bound and arg == hole) return expr;
        }
        var args: [catalog.max_args]ExprId = undefined;
        var changed = false;
        for (app.args, 0..) |arg, idx| {
            args[idx] = try self.swapWalk(arg, hole, value);
            if (args[idx] != arg) changed = true;
        }
        if (!changed) return expr;
        return self.theorem.interner.internApp(app.term_id, args[0..app.args.len]);
    }

    /// Append the variables `expr` binds (those in a bound argument of some
    /// application) to `out`.
    pub fn boundVariables(
        self: *Terms,
        arena: std.mem.Allocator,
        expr: ExprId,
        out: *std.ArrayListUnmanaged(ExprId),
    ) Error!void {
        const app = switch (self.theorem.interner.node(expr).*) {
            .app => |app| app,
            .variable, .placeholder => return,
        };
        const decl = &self.context.env.terms.items[app.term_id];
        for (app.args, 0..) |arg, idx| {
            if (idx < decl.args.len and decl.args[idx].bound) {
                if (std.mem.indexOfScalar(ExprId, out.items, arg) == null) try out.append(arena, arg);
            } else {
                try self.boundVariables(arena, arg, out);
            }
        }
    }

    /// `template` with `bindings` substituted, canonical when every binding
    /// is.
    pub fn instantiate(
        self: *Terms,
        template: TemplateExpr,
        bindings: []const ExprId,
    ) Error!ExprId {
        switch (template) {
            .binder => |idx| return bindings[idx],
            .app => |app| {
                if (self.bagFor(app.term_id)) |combiner| {
                    const parts = combiner.flattenTemplate(template) orelse return error.Unsupported;
                    var out: AcuiBag.ExprBag = .{};
                    for (parts.slice()) |part| {
                        const value = try self.instantiate(part, bindings);
                        const members = combiner.flatten(self.theorem, value) orelse return error.Unsupported;
                        for (members.slice()) |member| {
                            if (!out.append(member)) return error.Unsupported;
                        }
                    }
                    return self.buildBag(combiner, &out);
                }
                if (app.args.len > catalog.max_args) return error.Unsupported;
                var args: [catalog.max_args]ExprId = undefined;
                for (app.args, 0..) |arg, idx| args[idx] = try self.instantiate(arg, bindings);
                return self.theorem.interner.internApp(app.term_id, args[0..app.args.len]);
            },
        }
    }

    /// Whether `template`, with the rule binders `bindings` fixes, might
    /// be an instance of `expr`: a cheap structural check where an unfixed
    /// binder, an unbound wvar and a bag stand for anything.
    pub fn mightFit(self: *Terms, template: TemplateExpr, bindings: []const ?ExprId, expr: ExprId) Error!bool {
        switch (template) {
            .binder => |idx| return if (bindings[idx]) |value| self.mightEqual(value, expr, .strict) else true,
            .app => |app| {
                if (self.bagFor(app.term_id) != null) return true;
                const target = switch (self.theorem.interner.node(self.wvars.resolve(expr)).*) {
                    .app => |target| target,
                    else => return false,
                };
                if (target.term_id != app.term_id or target.args.len != app.args.len) return false;
                for (app.args, target.args) |arg, value| {
                    if (!try self.mightFit(arg, bindings, value)) return false;
                }
                return true;
            },
        }
    }

    /// Whether `a` and `b` might unify: a cheap structural check where an
    /// unbound wvar and a bag stand for anything, and with `.unfolding`,
    /// where heads differ, an application of a definition declared after
    /// the other head is compared unfolded.
    pub fn mightEqual(self: *Terms, a: ExprId, b: ExprId, how: enum { strict, unfolding }) Error!bool {
        const lhs = self.wvars.resolve(a);
        const rhs = self.wvars.resolve(b);
        if (lhs == rhs) return true;
        const interner = &self.theorem.interner;
        const lhs_app = switch (interner.node(lhs).*) {
            .app => |app| app,
            .placeholder => return true,
            .variable => return interner.node(rhs).* == .placeholder,
        };
        const rhs_app = switch (interner.node(rhs).*) {
            .app => |app| app,
            .placeholder => return true,
            .variable => return false,
        };
        if (lhs_app.term_id != rhs_app.term_id) {
            if (how == .strict) return false;
            const later, const other = if (lhs_app.term_id > rhs_app.term_id) .{ lhs, rhs } else .{ rhs, lhs };
            const unfolded = (try self.unfold(later)) orelse return false;
            return self.mightEqual(unfolded, other, how);
        }
        if (lhs_app.args.len != rhs_app.args.len) return false;
        if (self.bagFor(lhs_app.term_id) != null) return true;
        for (lhs_app.args, rhs_app.args) |x, y| {
            if (!try self.mightEqual(x, y, how)) return false;
        }
        return true;
    }

    /// Call `sink.match(bindings)` for every way `rule`'s conclusion fits
    /// the canonical `goal`, until it returns true. `bindings` has one
    /// entry per rule binder, null for those the conclusion does not fix;
    /// wvar bindings the match made hold during the call. Returns whether
    /// the sink stopped the enumeration.
    pub fn matchConclusion(
        self: *Terms,
        rule: *const RuleDecl,
        goal: ExprId,
        comptime Sink: type,
        sink: *Sink,
    ) (Error || Sink.Error)!bool {
        if (try self.conclusionClash(rule.concl, goal)) return false;
        // On the heap: the match stays on the stack for the rest of the
        // proof.
        const bindings = try self.allocator.alloc(?ExprId, rule.args.len);
        defer self.allocator.free(bindings);
        @memset(bindings, null);
        var matcher = Matcher(Sink){ .terms = self, .rule = rule, .bindings = bindings, .sink = sink };
        try matcher.term(rule.concl, goal, null);
        return matcher.stop;
    }

    /// Call `sink.match(&.{})` for every unifier of `a` and `b`, until it
    /// returns true. Returns whether the sink stopped the enumeration.
    pub fn unify(
        self: *Terms,
        a: ExprId,
        b: ExprId,
        comptime Sink: type,
        sink: *Sink,
    ) (Error || Sink.Error)!bool {
        if (try self.clash(a, b)) return false;
        var matcher = Matcher(Sink){ .terms = self, .rule = null, .bindings = &.{}, .sink = sink };
        try matcher.unify(a, b, null);
        return matcher.stop;
    }

    /// Whether no bindings let `a` and `b` unify: they differ where neither
    /// is an unbound wvar, no definition the matcher would unfold applies
    /// and no bag is read. It interns nothing, and further bindings leave
    /// it true, so `unify` may skip the pair.
    fn clash(self: *Terms, a: ExprId, b: ExprId) Error!bool {
        const lhs = self.wvars.resolve(a);
        const rhs = self.wvars.resolve(b);
        if (lhs == rhs) return false;
        if (self.wvars.of(lhs) != null or self.wvars.of(rhs) != null) return false;
        if (!try self.wvars.holdsWVar(lhs) and !try self.wvars.holdsWVar(rhs) and
            !try self.holdsDef(lhs) and !try self.holdsDef(rhs)) return true;
        const lhs_head = self.headOf(lhs);
        const rhs_head = self.headOf(rhs);
        for ([_]?u32{ lhs_head, rhs_head }) |head| {
            if (self.bagFor(head orelse continue) != null) return false;
        }
        if (lhs_head != rhs_head) {
            // `Matcher.unify` unfolds only the later-declared head.
            const lhs_later = rhs_head == null or (lhs_head != null and lhs_head.? > rhs_head.?);
            const later = (if (lhs_later) lhs_head else rhs_head) orelse return true;
            return !self.opensDef(later);
        }
        if (lhs_head == null) return true;
        const interner = &self.theorem.interner;
        const lhs_args = interner.node(lhs).app.args;
        const rhs_args = interner.node(rhs).app.args;
        if (lhs_args.len != rhs_args.len) return true;
        for (lhs_args, rhs_args) |x, y| {
            if (try self.clash(x, y)) return true;
        }
        return false;
    }

    /// What `clash` reads of the top of `expr`.
    pub fn shape(self: *Terms, expr: ExprId) Error!Shape {
        const head = self.headOf(expr);
        return .{
            .head = head,
            .wild = if (head) |id| self.bagFor(id) != null or self.opensDef(id) else false,
            .plain = !try self.wvars.holdsWVar(expr) and !try self.holdsDef(expr),
        };
    }

    /// `goal` resolved once, to try many facts against (`excludes`).
    pub fn screen(self: *Terms, goal: ExprId) Error!Screen {
        const target = self.wvars.resolve(goal);
        return .{ .target = target, .open = self.wvars.of(target) != null, .shape = try self.shape(target) };
    }

    /// Whether `fact`, of shape `fact_shape`, clashes with the screened
    /// goal (`clash`), reading the goal's top from `screen`.
    pub fn excludes(self: *Terms, goal: Screen, fact: ExprId, fact_shape: Shape) Error!bool {
        if (goal.open or fact == goal.target) return false;
        if (!fact_shape.plain) return self.clash(fact, goal.target);
        if (goal.shape.plain) return true;
        if (fact_shape.head != goal.shape.head and !fact_shape.wild and !goal.shape.wild) return true;
        return self.clash(fact, goal.target);
    }

    /// Whether no bindings let the conclusion `template` fit `expr`, as
    /// `clash` for `unify`: they differ where `expr` holds no unbound wvar
    /// and the matcher neither postpones, unfolds nor reads a bag.
    fn conclusionClash(self: *Terms, template: TemplateExpr, expr: ExprId) Error!bool {
        const app = switch (template) {
            .binder => return false,
            .app => |app| app,
        };
        const target = self.wvars.resolve(expr);
        if (self.wvars.of(target) != null) return false;
        const head = self.headOf(target);
        if (self.isRewritten(app.term_id) and head != app.term_id) return false;
        if (head) |own| {
            if (own > app.term_id and self.opensDef(own)) return false;
            if (own < app.term_id and self.opensDef(app.term_id)) return false;
        }
        if (self.bagFor(app.term_id) != null) return false;
        if (head != app.term_id) return true;
        const args = self.theorem.interner.node(target).app.args;
        if (args.len != app.args.len) return true;
        for (app.args, args) |arg, value| {
            if (try self.conclusionClash(arg, value)) return true;
        }
        return false;
    }
};

/// The top of an expression as `clash` reads it: its head, whether that
/// head reads as a bag or is a definition `unify` may unfold, and whether
/// the expression holds no wvar and no definition.
pub const Shape = struct {
    head: ?u32,
    wild: bool,
    plain: bool,
};

/// A goal resolved for `Terms.excludes`; `open` when it is an unbound wvar,
/// which any fact may close.
pub const Screen = struct {
    target: ExprId,
    open: bool,
    shape: Shape,
};

/// A conclusion bag whose rest binders are shares (`catalog.Rule.shares`):
/// the goal bag's members and those the template's own members took.
pub const SplitBag = struct {
    combiner: AcuiBag.Combiner,
    members: []const ExprId,
    taken: u64,
};

/// A conclusion node matched against the goal node `goal` once its binders
/// are known: one under a head some `@rewrite` rule rewrites, or, when
/// `narrow`, one facing an unbound wvar.
pub const Postponed = struct {
    template: TemplateExpr,
    goal: ExprId,
    next: ?*const Postponed,
    /// The node gives the wvar its structure, so the match fails when it
    /// leaves one of the node's binders unbound: the wvar takes only
    /// structure the rest of the conclusion fixes.
    narrow: bool = false,
};

/// A cut wvar a narrowing minted for a binder the match left unbound
/// (`Matcher.invent`), as a list.
pub const Invented = struct { wvar: u32, next: ?*const Invented };

/// What is left to match after the current step, as a stack-allocated
/// list: the arguments of an application from position `at` on (template
/// against goal, or two terms unified), and the next member of a bag in
/// progress. One cell stands for all of an application's remaining
/// arguments, since a match stays on the stack until the proof is done.
const Pending = struct {
    step: union(enum) {
        /// Positions count over the rigid arguments, then the bags.
        args: struct { template: []const TemplateExpr, goal: []const ExprId, at: usize },
        unify: struct { a: []const ExprId, b: []const ExprId, at: usize },
        bag: *const BagState,
        pairing: *const BagPairing,
        seq: *const SeqState,
        /// The postponed nodes in `list` to check, those already left for
        /// the prover in `left`.
        check: struct { list: ?*const Postponed, left: ?*const Postponed },
    },
    next: ?*const Pending,
};

/// A sequence being matched part by part, in order: the template's parts,
/// the goal's members, the next part and the first member it may take.
const SeqState = struct {
    combiner: AcuiBag.Combiner,
    template: []const TemplateExpr,
    goal: []const ExprId,
    part: usize = 0,
    at: usize = 0,
};

/// Two sequences to unify member by member, `a`'s against `b`'s at the
/// same position. A `part` is an unbound wvar taken out of `a`, which
/// first takes `run`: the members of `b` its neighbours in `a` leave
/// between them.
const SeqPairing = struct {
    a: []const ExprId,
    b: []const ExprId,
    part: ?ExprId = null,
    run: ExprId = undefined,
};

/// A bag being matched member by member: template members in match order,
/// the goal's members, which of those are taken, and the rest binder, or
/// whether several rest binders share the leftover.
const BagState = struct {
    combiner: AcuiBag.Combiner,
    template: []const TemplateExpr,
    goal: []const ExprId,
    used: u64 = 0,
    index: usize = 0,
    rest: ?usize = null,
    shared: bool = false,
};

/// Two bags being unified member by member: each of `a`'s members against
/// one of `b`'s, distinct ones unless the law is idempotent, and then each
/// of `b`'s members none was paired with: into `absorb`, an unbound wvar of
/// the bag's sort taken out of `a`, or under an idempotent law against one
/// of `a`'s. `index` counts over `a`, then over `b`.
const BagPairing = struct {
    combiner: AcuiBag.Combiner,
    a: []const ExprId,
    b: []const ExprId,
    absorb: ?ExprId = null,
    paired: u64 = 0,
    absorbed: u64 = 0,
    index: usize = 0,
};

fn Matcher(comptime Sink: type) type {
    return struct {
        terms: *Terms,
        /// The rule whose conclusion is matched; null when only unifying.
        rule: ?*const RuleDecl,
        bindings: []?ExprId,
        sink: *Sink,
        stop: bool = false,
        /// The conclusion nodes postponed so far (`postpone`).
        postponed: ?*const Postponed = null,
        /// The cut wvars minted so far (`invent`).
        invented: ?*const Invented = null,

        const Self = @This();
        const MatchError = Error || Sink.Error;

        fn run(self: *Self, pending: ?*const Pending) MatchError!void {
            const node = pending orelse {
                const list = self.postponed orelse return self.report(null);
                self.postponed = null;
                defer self.postponed = list;
                return self.check(list, null);
            };
            switch (node.step) {
                .args => |args| {
                    // Bags go last, so the rigid arguments bind what they
                    // can before a bag enumerates its members.
                    const len = args.template.len;
                    var at = args.at;
                    while (at < 2 * len) : (at += 1) {
                        if ((at >= len) == self.isBagTemplate(args.template[at % len])) break;
                    } else return self.run(node.next);
                    var after = node.*;
                    after.step.args.at = at + 1;
                    try self.term(args.template[at % len], args.goal[at % len], &after);
                },
                .unify => |args| {
                    if (args.at == args.a.len) return self.run(node.next);
                    var after = node.*;
                    after.step.unify.at += 1;
                    try self.unify(args.a[args.at], args.b[args.at], &after);
                },
                .bag => |state| try self.bag(state.*, node.next),
                .pairing => |state| try self.pairBags(state.*, node.next),
                .seq => |state| try self.seq(state.*, node.next),
                .check => |state| try self.check(state.list, state.left),
            }
        }

        /// The match is complete: hand it to the sink, with the postponed
        /// nodes `left` for the prover.
        fn report(self: *Self, left: ?*const Postponed) MatchError!void {
            const outer = self.terms.postponed;
            self.terms.postponed = left;
            defer self.terms.postponed = outer;
            const outer_invented = self.terms.invented;
            self.terms.invented = self.invented;
            defer self.terms.invented = outer_invented;
            if (try self.sink.match(self.bindings)) self.stop = true;
        }

        /// Defer the conclusion node `template` against `expr` to the end
        /// of the match (`Postponed.narrow`).
        fn postpone(self: *Self, template: TemplateExpr, expr: ExprId, narrow: bool, next: ?*const Pending) MatchError!void {
            const outer = self.postponed;
            const cell = Postponed{ .template = template, .goal = expr, .next = outer, .narrow = narrow };
            self.postponed = &cell;
            defer self.postponed = outer;
            try self.run(next);
        }

        /// Unify each postponed node of `list` whose binders the match
        /// bound with its goal node, instantiated and in normal form; the
        /// others join `left` for `report`, except a narrowing one, which
        /// invents its unbound binders or fails the match.
        fn check(self: *Self, list: ?*const Postponed, left: ?*const Postponed) MatchError!void {
            const node = list orelse return self.report(left);
            const instance = (try @call(.never_inline, instantiateBound, .{ self, node.template })) orelse {
                if (node.narrow) return self.invent(node, left);
                const kept = Postponed{ .template = node.template, .goal = node.goal, .next = left };
                return self.check(node.next, &kept);
            };
            const cell = Pending{ .step = .{ .check = .{ .list = node.next, .left = left } }, .next = null };
            try self.unify(instance, node.goal, &cell);
        }

        /// The narrowing `node` holds binders the match left unbound: give
        /// each a cut wvar of its own, reported as `Terms.invented`, and
        /// check `node` again. A premise must then fix them from a fact.
        /// Only a sink with `mayInvent` invents, and only when the node
        /// also holds a binder the rest of the match bound: structure made
        /// of invented binders alone is a guess. A bound binder gets a
        /// bound name instead, which is no guess: any fresh variable will
        /// do, and its steps' bars say which.
        fn invent(self: *Self, node: *const Postponed, left: ?*const Postponed) MatchError!void {
            if (!@hasDecl(Sink, "mayInvent")) return;
            const rule = self.rule orelse return;
            // The catalog admits rules of at most 64 arguments.
            const held = Rules.templateBinderMask(node.template).mask;
            var bound: u64 = 0;
            for (self.bindings, 0..) |binding, idx| {
                if (binding != null) bound |= @as(u64, 1) << @intCast(idx);
            }
            if (held & bound == 0) return;
            const unbound = held & ~bound;
            var names: u64 = 0;
            var rest = unbound;
            while (rest != 0) : (rest &= rest - 1) {
                const idx = @ctz(rest);
                if (rule.args[idx].bound) {
                    names |= @as(u64, 1) << @intCast(idx);
                } else if (!self.sink.mayInvent(idx)) return;
            }
            // On the heap: the match stays on the stack for the rest of
            // the proof.
            const cells = try self.terms.allocator.alloc(Invented, @popCount(unbound & ~names));
            defer self.terms.allocator.free(cells);
            const outer = self.invented;
            defer {
                self.invented = outer;
                rest = unbound;
                while (rest != 0) : (rest &= rest - 1) self.bindings[@ctz(rest)] = null;
            }
            rest = names;
            while (rest != 0) : (rest &= rest - 1) {
                const idx = @ctz(rest);
                self.bindings[idx] = try self.terms.wvars.introduceName(rule.args[idx].sort_name);
            }
            rest = unbound & ~names;
            var at: usize = 0;
            while (rest != 0) : (rest &= rest - 1) {
                const idx = @ctz(rest);
                const wvar = try self.terms.wvars.mint(rule.args[idx].sort_name, &.{}, true);
                self.bindings[idx] = wvar;
                cells[at] = .{ .wvar = self.terms.wvars.of(wvar).?, .next = self.invented };
                self.invented = &cells[at];
                at += 1;
            }
            return self.check(node, left);
        }

        /// `template` instantiated with the match's bindings, resolved and
        /// in normal form; null when it holds an unbound binder.
        fn instantiateBound(self: *Self, template: TemplateExpr) Error!?ExprId {
            if (Rules.templateHasUnboundBinder(template, self.bindings)) return null;
            const values = try self.terms.allocator.alloc(ExprId, self.bindings.len);
            defer self.terms.allocator.free(values);
            for (values, self.bindings) |*value, binding| value.* = binding orelse undefined;
            const instance = try self.terms.resolveGoal(try self.terms.instantiate(template, values));
            return (try self.terms.normalForm(instance)) orelse instance;
        }

        fn term(self: *Self, template: TemplateExpr, expr: ExprId, next: ?*const Pending) MatchError!void {
            switch (template) {
                .binder => |idx| try self.bind(idx, expr, next),
                .app => |app| {
                    const target = self.terms.wvars.resolve(expr);
                    if (self.terms.wvars.of(target) != null) return self.postpone(template, target, true, next);
                    if (self.terms.isRewritten(app.term_id) and self.terms.headOf(target) != app.term_id) {
                        return self.postpone(template, target, false, next);
                    }
                    if (try self.unfoldToward(app.term_id, target)) |unfolded| {
                        return self.term(template, unfolded, next);
                    }
                    if (try self.unfoldTemplateToward(app, target)) |unfolded| {
                        return self.term(unfolded, target, next);
                    }
                    if (self.terms.bagFor(app.term_id)) |combiner| {
                        if (!combiner.law.isCommutative()) return self.startSeq(combiner, template, target, next);
                        return self.startBag(combiner, template, target, next);
                    }
                    const goal_app = switch (self.terms.theorem.interner.node(target).*) {
                        .app => |goal_app| goal_app,
                        else => return,
                    };
                    if (goal_app.term_id != app.term_id or goal_app.args.len != app.args.len) return;
                    const cell = Pending{
                        .step = .{ .args = .{ .template = app.args, .goal = goal_app.args, .at = 0 } },
                        .next = next,
                    };
                    try self.run(&cell);
                },
            }
        }

        /// `expr` unfolded one step when it applies a definition other than
        /// `head` whose unfoldings can reach `head`: a definition's body
        /// only uses terms declared before it.
        fn unfoldToward(self: *Self, head: u32, expr: ExprId) Error!?ExprId {
            const own = self.terms.headOf(expr) orelse return null;
            if (own <= head) return null;
            return self.terms.unfold(expr);
        }

        /// The template application `app` unfolded one step when it applies
        /// a definition declared after `expr`'s head.
        fn unfoldTemplateToward(self: *Self, app: TemplateExpr.App, expr: ExprId) Error!?TemplateExpr {
            const own = self.terms.headOf(expr) orelse return null;
            if (own >= app.term_id) return null;
            return self.terms.unfoldTemplate(app);
        }

        fn isBagTemplate(self: *const Self, template: TemplateExpr) bool {
            return switch (template) {
                .binder => false,
                .app => |app| self.terms.bagFor(app.term_id) != null,
            };
        }

        fn bind(self: *Self, idx: usize, expr: ExprId, next: ?*const Pending) MatchError!void {
            if (self.bindings[idx]) |value| return self.unify(value, expr, next);
            self.bindings[idx] = expr;
            defer self.bindings[idx] = null;
            try self.run(next);
        }

        fn unify(self: *Self, a: ExprId, b: ExprId, next: ?*const Pending) MatchError!void {
            const wvars = self.terms.wvars;
            const lhs = wvars.resolve(a);
            const rhs = wvars.resolve(b);
            if (lhs == rhs) return self.run(next);
            // Ground terms are canonical, so distinct ids differ unless a
            // definition unfolds.
            if (!try wvars.holdsWVar(lhs) and !try wvars.holdsWVar(rhs) and
                !try self.terms.holdsDef(lhs) and !try self.terms.holdsDef(rhs)) return;
            if (try self.bindWVar(lhs, rhs, next)) return;
            if (try self.bindWVar(rhs, lhs, next)) return;
            const lhs_head = self.terms.headOf(lhs);
            const rhs_head = self.terms.headOf(rhs);
            if (lhs_head != rhs_head) {
                // A bag holding a part of itself meets a one-member bag or
                // the unit.
                for ([_]?u32{ lhs_head, rhs_head }) |head| {
                    const combiner = self.terms.bagFor(head orelse continue) orelse continue;
                    if (combiner.head != head.?) continue;
                    if (!combiner.law.isCommutative()) {
                        if (try self.unifySeq(combiner, lhs, rhs, next, true)) return;
                        break;
                    }
                    const pairing = (try @call(.never_inline, preparePairing, .{ self, combiner, lhs, rhs })) orelse break;
                    if (pairing.absorb == null) {
                        self.terms.allocator.free(pairing.a);
                        self.terms.allocator.free(pairing.b);
                        break;
                    }
                    defer self.terms.allocator.free(pairing.a);
                    defer self.terms.allocator.free(pairing.b);
                    return self.pairBags(pairing, next);
                }
                // Only the later-declared definition's unfoldings can reach
                // the other head.
                const lhs_later = rhs_head == null or (lhs_head != null and lhs_head.? > rhs_head.?);
                const later = if (lhs_later) lhs else rhs;
                const unfolded = (try self.terms.unfold(later)) orelse return;
                return self.unify(unfolded, if (lhs_later) rhs else lhs, next);
            }
            if (lhs_head == null) return;
            const interner = &self.terms.theorem.interner;
            const lhs_app = interner.node(lhs).app;
            const rhs_app = interner.node(rhs).app;
            if (lhs_app.args.len != rhs_app.args.len) return;
            if (self.terms.bagFor(lhs_app.term_id)) |combiner| {
                if (try self.terms.same(lhs, rhs)) return self.run(next);
                if (!combiner.law.isCommutative()) {
                    _ = try self.unifySeq(combiner, lhs, rhs, next, false);
                    return;
                }
                const pairing = (try @call(.never_inline, preparePairing, .{ self, combiner, lhs, rhs })) orelse return;
                defer self.terms.allocator.free(pairing.a);
                defer self.terms.allocator.free(pairing.b);
                return self.pairBags(pairing, next);
            }
            const cell = Pending{
                .step = .{ .unify = .{ .a = lhs_app.args, .b = rhs_app.args, .at = 0 } },
                .next = next,
            };
            try self.run(&cell);
        }

        /// The members of bags `lhs` and `rhs`, copied out of the
        /// fixed-capacity bags as `prepareBag` does; null when no pairing
        /// can make them equal. When exactly one bag holds one unbound wvar
        /// of the bag's sort, that bag is `a` and the wvar its `absorb`.
        fn preparePairing(self: *Self, combiner: AcuiBag.Combiner, lhs: ExprId, rhs: ExprId) Error!?BagPairing {
            var a = combiner.flatten(self.terms.theorem, lhs) orelse return error.Unsupported;
            var b = combiner.flatten(self.terms.theorem, rhs) orelse return error.Unsupported;
            const a_part = self.partOf(combiner, a.slice());
            const b_part = self.partOf(combiner, b.slice());
            var absorb: ?ExprId = null;
            if ((a_part == null) != (b_part == null)) {
                if (a_part == null) std.mem.swap(AcuiBag.ExprBag, &a, &b);
                const at = (a_part orelse b_part).?;
                absorb = a.items[at];
                a.items[at] = a.items[a.len - 1];
                a.len -= 1;
                if (a.len > b.len) return null;
            } else if (!combiner.law.isIdempotent() and a.len != b.len) return null;
            const allocator = self.terms.allocator;
            const a_members = try allocator.dupe(ExprId, a.slice());
            errdefer allocator.free(a_members);
            return .{
                .combiner = combiner,
                .a = a_members,
                .b = try allocator.dupe(ExprId, b.slice()),
                .absorb = absorb,
            };
        }

        /// The position of the one member of `members` that is an unbound
        /// wvar of the bag's own sort, standing for a part of the bag; null
        /// when there is none or more than one.
        fn partOf(self: *Self, combiner: AcuiBag.Combiner, members: []const ExprId) ?usize {
            const wvars = self.terms.wvars;
            const bag_sort = self.terms.context.env.terms.items[combiner.head].ret_sort_name;
            var found: ?usize = null;
            for (members, 0..) |member, at| {
                const idx = wvars.of(member) orelse continue;
                if (wvars.vars.items[idx].value != null) continue;
                if (!std.mem.eql(u8, wvars.vars.items[idx].sort_name, bag_sort)) continue;
                if (found != null) return null;
                found = at;
            }
            return found;
        }

        fn pairBags(self: *Self, state: BagPairing, next: ?*const Pending) MatchError!void {
            const idempotent = state.combiner.law.isIdempotent();
            var after = state;
            after.index += 1;
            const cell = Pending{ .step = .{ .pairing = &after }, .next = next };
            if (state.index < state.a.len) {
                const member = state.a[state.index];
                // A member without wvars that the other bag holds pairs with
                // that copy alone: any other partner only adds bindings.
                if (!try self.terms.wvars.holdsWVar(member)) {
                    for (state.b, 0..) |other, at| {
                        const bit = @as(u64, 1) << @intCast(at);
                        if (other != member or (!idempotent and state.paired & bit != 0)) continue;
                        after.paired |= bit;
                        return self.pairBags(after, next);
                    }
                }
                for (state.b, 0..) |other, at| {
                    const bit = @as(u64, 1) << @intCast(at);
                    if (!idempotent and state.paired & bit != 0) continue;
                    after.paired = state.paired | bit;
                    try self.unify(member, other, &cell);
                    if (self.stop) return;
                }
                return;
            }
            const at = state.index - state.a.len;
            if (at == state.b.len) {
                const absorb = state.absorb orelse return self.run(next);
                var part: AcuiBag.ExprBag = .{};
                for (state.b, 0..) |member, idx| {
                    if (state.absorbed & (@as(u64, 1) << @intCast(idx)) != 0) _ = part.append(member);
                }
                // `b`'s members are canonical and in order, so the part is
                // canonical as it stands.
                const value = (try state.combiner.build(self.terms.theorem, part.slice())) orelse return;
                _ = try self.bindWVar(absorb, value, next);
                return;
            }
            const member = state.b[at];
            const bit = @as(u64, 1) << @intCast(at);
            if (state.paired & bit != 0 or (idempotent and !try self.terms.wvars.holdsWVar(member) and
                std.mem.indexOfScalar(ExprId, state.a, member) != null))
            {
                return self.pairBags(after, next);
            }
            if (state.absorb != null) {
                after.absorbed |= bit;
                return self.pairBags(after, next);
            }
            for (state.a) |other| {
                try self.unify(other, member, &cell);
                if (self.stop) return;
            }
        }

        /// When `wvar` is an unbound witness variable, run `next` with it
        /// bound to `value` if its constraints allow, and return true.
        fn bindWVar(self: *Self, wvar: ExprId, value: ExprId, next: ?*const Pending) MatchError!bool {
            const wvars = self.terms.wvars;
            const idx = wvars.of(wvar) orelse return false;
            const start = wvars.mark();
            defer wvars.rollback(start);
            if (try wvars.bind(idx, value)) try self.run(next);
            return true;
        }

        fn isRestBinder(self: *const Self, combiner: AcuiBag.Combiner, template: TemplateExpr) bool {
            const idx = switch (template) {
                .binder => |idx| idx,
                .app => return false,
            };
            const bag_sort = self.terms.context.env.terms.items[combiner.head].ret_sort_name;
            return std.mem.eql(u8, self.rule.?.args[idx].sort_name, bag_sort);
        }

        fn startBag(
            self: *Self,
            combiner: AcuiBag.Combiner,
            template: TemplateExpr,
            expr: ExprId,
            next: ?*const Pending,
        ) MatchError!void {
            const state = try @call(.never_inline, prepareBag, .{ self, combiner, template, expr });
            defer self.terms.allocator.free(state.template);
            defer self.terms.allocator.free(state.goal);
            try self.bag(state, next);
        }

        /// The bag's template members in match order and the goal's
        /// members, copied out of the fixed-capacity bags. The bag match
        /// stays on the stack for the rest of the proof, so it holds only
        /// these slices.
        fn prepareBag(self: *Self, combiner: AcuiBag.Combiner, template: TemplateExpr, expr: ExprId) Error!BagState {
            const parts = combiner.flattenTemplate(template) orelse return error.Unsupported;
            const members = combiner.flatten(self.terms.theorem, expr) orelse return error.Unsupported;
            // Bound rest binders and structured members first, the unbound
            // rest binder last: it takes what the others leave. Several
            // distinct unbound ones share it.
            var rest: ?usize = null;
            var rests: u64 = 0;
            var kept: usize = 0;
            for (parts.slice()) |part| {
                if (self.isRestBinder(combiner, part) and self.bindings[part.binder] == null) {
                    rest = part.binder;
                    rests |= @as(u64, 1) << @intCast(part.binder);
                } else {
                    kept += 1;
                }
            }
            const allocator = self.terms.allocator;
            const ordered = try allocator.alloc(TemplateExpr, kept);
            errdefer allocator.free(ordered);
            var count: usize = 0;
            for (parts.slice()) |part| {
                if (self.isRestBinder(combiner, part) and self.bindings[part.binder] == null) continue;
                ordered[count] = part;
                count += 1;
            }
            return .{
                .combiner = combiner,
                .template = ordered,
                .goal = try allocator.dupe(ExprId, members.slice()),
                .rest = if (@popCount(rests) > 1) null else rest,
                .shared = @popCount(rests) > 1,
            };
        }

        fn bag(self: *Self, state: BagState, next: ?*const Pending) MatchError!void {
            if (state.index == state.template.len) return self.finishBag(state, next);
            const part = state.template[state.index];
            if (self.isRestBinder(state.combiner, part)) {
                // A rest binder an earlier match bound: its members must be
                // among the goal's.
                var after = state;
                after.used = (try @call(.never_inline, takeAll, .{ self, state, self.bindings[part.binder].? })) orelse return;
                after.index += 1;
                return self.bag(after, next);
            }
            for (state.goal, 0..) |member, at| {
                const bit = @as(u64, 1) << @intCast(at);
                if (state.used & bit != 0) continue;
                var after = state;
                after.used |= bit;
                after.index += 1;
                const cell = Pending{ .step = .{ .bag = &after }, .next = next };
                try self.term(part, member, &cell);
                if (self.stop) return;
            }
        }

        /// `state.used` with a goal member taken for each member of
        /// `value`, or null when one has none.
        fn takeAll(self: *Self, state: BagState, value: ExprId) Error!?u64 {
            const members = state.combiner.flatten(self.terms.theorem, value) orelse return error.Unsupported;
            var used = state.used;
            for (members.slice()) |member| {
                used |= (try self.takeMember(state.combiner, state.goal, used, member)) orelse return null;
            }
            return used;
        }

        /// The bit of a goal member equal to `member` that `used` leaves
        /// free, or under an idempotent law one already taken; null when
        /// there is none.
        fn takeMember(self: *Self, combiner: AcuiBag.Combiner, goal: []const ExprId, used: u64, member: ExprId) Error!?u64 {
            var taken: ?u64 = null;
            for (goal, 0..) |candidate, at| {
                if (!try self.terms.same(candidate, member)) continue;
                const bit = @as(u64, 1) << @intCast(at);
                if (used & bit == 0) return bit;
                taken = bit;
            }
            return if (combiner.law.isIdempotent()) taken else null;
        }

        fn finishBag(self: *Self, state: BagState, next: ?*const Pending) MatchError!void {
            if (state.shared) {
                const outer = self.terms.split;
                self.terms.split = .{ .combiner = state.combiner, .members = state.goal, .taken = state.used };
                defer self.terms.split = outer;
                return self.run(next);
            }
            const rest = state.rest orelse {
                if (@popCount(state.used) == state.goal.len) try self.run(next);
                return;
            };
            const value = (try @call(.never_inline, leftover, .{ self, state })) orelse return;
            try self.bind(rest, value, next);
        }

        /// The bag of the goal members `state` leaves untaken.
        fn leftover(self: *Self, state: BagState) Error!?ExprId {
            var left: AcuiBag.ExprBag = .{};
            for (state.goal, 0..) |member, at| {
                if (state.used & (@as(u64, 1) << @intCast(at)) == 0) _ = left.append(member);
            }
            // The goal's members are canonical and in order, so the
            // leftover is canonical as it stands.
            return state.combiner.build(self.terms.theorem, left.slice());
        }

        fn startSeq(
            self: *Self,
            combiner: AcuiBag.Combiner,
            template: TemplateExpr,
            expr: ExprId,
            next: ?*const Pending,
        ) MatchError!void {
            const state = try @call(.never_inline, prepareSeq, .{ self, combiner, template, expr });
            defer self.terms.allocator.free(state.template);
            defer self.terms.allocator.free(state.goal);
            try self.seq(state, next);
        }

        /// The sequence's template parts and the goal's members, copied out
        /// of the fixed-capacity bags as `prepareBag` does.
        fn prepareSeq(self: *Self, combiner: AcuiBag.Combiner, template: TemplateExpr, expr: ExprId) Error!SeqState {
            const parts = combiner.flattenTemplate(template) orelse return error.Unsupported;
            const members = combiner.flatten(self.terms.theorem, try self.terms.resolveGoal(expr)) orelse
                return error.Unsupported;
            const allocator = self.terms.allocator;
            const owned = try allocator.dupe(TemplateExpr, parts.slice());
            errdefer allocator.free(owned);
            return .{ .combiner = combiner, .template = owned, .goal = try allocator.dupe(ExprId, members.slice()) };
        }

        /// Match the sequence's parts in order: a member takes the next goal
        /// member, a rest binder a run of them. When no rest binder follows,
        /// the run is what the members after it leave; otherwise each length
        /// is an alternative.
        fn seq(self: *Self, state: SeqState, next: ?*const Pending) MatchError!void {
            if (state.part == state.template.len) {
                if (state.at == state.goal.len) try self.run(next);
                return;
            }
            const part = state.template[state.part];
            var after = state;
            after.part += 1;
            const cell = Pending{ .step = .{ .seq = &after }, .next = next };
            if (!self.isRestBinder(state.combiner, part)) {
                if (state.at == state.goal.len) return;
                after.at += 1;
                return self.term(part, state.goal[state.at], &cell);
            }
            var members: usize = 0;
            var open = false;
            for (state.template[state.part + 1 ..]) |later| {
                if (self.isRestBinder(state.combiner, later)) open = true else members += 1;
            }
            const left = state.goal.len - state.at;
            if (members > left) return;
            var len = if (open) 0 else left - members;
            while (len <= left - members) : (len += 1) {
                // A run of canonical members in order is canonical.
                const value = (try state.combiner.build(self.terms.theorem, state.goal[state.at..][0..len])) orelse continue;
                after.at = state.at + len;
                try self.term(part, value, &cell);
                if (self.stop) return;
            }
        }

        /// Unify the sequences `lhs` and `rhs` member by member, in order.
        /// When exactly one holds one unbound wvar of the sequence's sort,
        /// that wvar takes the run of the other's members its neighbours
        /// leave. With `need_part`, a pairing without such a wvar is not
        /// run. Returns whether the pairing ran.
        fn unifySeq(
            self: *Self,
            combiner: AcuiBag.Combiner,
            lhs: ExprId,
            rhs: ExprId,
            next: ?*const Pending,
            need_part: bool,
        ) MatchError!bool {
            const pairing = (try @call(.never_inline, prepareSeqPairing, .{ self, combiner, lhs, rhs })) orelse return false;
            defer self.terms.allocator.free(pairing.a);
            defer self.terms.allocator.free(pairing.b);
            const cell = Pending{ .step = .{ .unify = .{ .a = pairing.a, .b = pairing.b, .at = 0 } }, .next = next };
            const part = pairing.part orelse {
                if (need_part) return false;
                try self.run(&cell);
                return true;
            };
            _ = try self.bindWVar(part, pairing.run, &cell);
            return true;
        }

        /// The members `unifySeq` pairs up, copied out of the fixed-capacity
        /// bags; null when no pairing can make the sequences equal.
        fn prepareSeqPairing(self: *Self, combiner: AcuiBag.Combiner, lhs: ExprId, rhs: ExprId) Error!?SeqPairing {
            const theorem = self.terms.theorem;
            var a = combiner.flatten(theorem, try self.terms.resolveGoal(lhs)) orelse return error.Unsupported;
            var b = combiner.flatten(theorem, try self.terms.resolveGoal(rhs)) orelse return error.Unsupported;
            const a_part = self.partOf(combiner, a.slice());
            const b_part = self.partOf(combiner, b.slice());
            const allocator = self.terms.allocator;
            if ((a_part == null) == (b_part == null)) {
                if (a.len != b.len) return null;
                const a_members = try allocator.dupe(ExprId, a.slice());
                errdefer allocator.free(a_members);
                return .{ .a = a_members, .b = try allocator.dupe(ExprId, b.slice()) };
            }
            if (a_part == null) std.mem.swap(AcuiBag.ExprBag, &a, &b);
            const at = (a_part orelse b_part).?;
            if (b.len + 1 < a.len) return null;
            const end = b.len - (a.len - 1 - at);
            const taken = (try combiner.build(theorem, b.items[at..end])) orelse return null;
            const a_members = try allocator.alloc(ExprId, a.len - 1);
            errdefer allocator.free(a_members);
            @memcpy(a_members[0..at], a.items[0..at]);
            @memcpy(a_members[at..], a.items[at + 1 .. a.len]);
            const b_members = try allocator.alloc(ExprId, a.len - 1);
            @memcpy(b_members[0..at], b.items[0..at]);
            @memcpy(b_members[at..], b.items[end..b.len]);
            return .{ .a = a_members, .b = b_members, .part = a.items[at], .run = taken };
        }
    };
}
