//! The rules the search core applies, and the role of each
//! (`docs/design_notes/shared_witness.md` D2). Roles come from the rule's
//! annotations and shape alone:
//!
//! - a **closer** has no premises (`ax`, `contra_left`);
//! - a **safe** rule is `@auto eager`: invertible, so once it applies the
//!   goal is committed to the safe rules;
//! - an **unsafe** rule is any other rule; each application charges one
//!   unit of the depth budget.
//!
//! A binder the conclusion does not fix is one of:
//!
//! - a **witness**: a binder a `@view` reads back with `@recover` from a
//!   premise formula the view states as a substitution instance. One that
//!   is not a bound variable is γ (`all_left`'s `t`): it becomes a fresh
//!   witness variable. A bound one is δ (`all_intro`'s `y`), an
//!   eigenvariable. Such a rule's premises are the view's, so a premise
//!   holds the instance itself, not a substitution redex;
//! - in a rule without a view, a **cut** (`imp_trans`'s `q`, `t_app`'s
//!   `A`): a binder that is not bound becomes a fresh witness variable,
//!   which only a premise's closure binds. A bound one (`subset_intro`'s
//!   `x`) is δ, stated by the premises directly. A binder the conclusion
//!   holds only under a term some `@rewrite` rule rewrites (`sb_tm_eq`'s
//!   `u1` in `⟦ x / u1 ⟧ t`) is a cut too, unless the match binds it: such
//!   a node meets a goal with another head only once its binders are
//!   known, by its normal form (`terms.zig`).
//!
//! A rule whose conclusion is a bare binder (`mp`'s `b`) applies to every
//! goal of that binder's sort; its other binders are cuts.
//!
//! A rule whose view abstracts a binder (`@abstract`, `eq_replace`'s `p`
//! read off `q` and `r`) is searched as its view: the core matches the
//! view's conclusion and proves its premises, whose binders the conclusion
//! does not fix are cuts. Once they are proved, the checker's walk reads
//! the target off the two sides, with a fresh eigenvariable for the hole
//! (`Abstraction`).
//!
//! Rules are admitted over `@acui` bags, commutative ones and sequences
//! (`martin_lof`'s ordered contexts `g , x : A`). A conclusion bag with
//! more than one rest binder (`or_elim`'s `G , H , K`) needs an idempotent
//! law: its rest binders are **shares**, which split the goal's context
//! between the premises (`Prover.Split`). A definition in a rule is an
//! ordinary term constructor: the core unfolds definitions in goals and
//! facts (`terms.zig`), never in a rule's own templates. A relation's transport (`mpbi`) is left out:
//! the core converts by unification, unfolding and normal forms instead.
//! Rules mixing cuts with a view and other rules with fresh variables wait
//! for the later stages, as do bridges, which only link facts already in
//! hand.

const std = @import("std");
const TemplateExpr = @import("../../../rules.zig").TemplateExpr;
const Rules = @import("../../../rules.zig");
const AcuiBag = @import("../../../acui_bag.zig");
const ArgInfo = @import("../../../parse_recovery.zig").ArgInfo;
const ViewDecl = @import("../../../views.zig").ViewDecl;
const AbstractDecl = @import("../../../derived_bindings.zig").AbstractDecl;
const RuleDecl = @import("../../../env.zig").RuleDecl;
const Context = @import("../types.zig").Context;

pub const Role = enum { closer, safe, unsafe };

pub const Rule = struct {
    rule_id: u32,
    role: Role,
    /// `@auto eager` priority (1 = tried first); 0 for other rules.
    priority: u8 = 0,
    /// The premises to prove: the rule's own, or with witnesses the view's,
    /// over the view's binders.
    premises: []const TemplateExpr,
    /// The view the premises are stated in, when the rule has witnesses.
    view: ?*const ViewDecl = null,
    witnesses: []const Witness = &.{},
    /// The binders a rule without a view leaves open, or an abstraction's
    /// view binders.
    cuts: []const Cut = &.{},
    /// For a rule whose view abstracts a binder, the view; the premises,
    /// cuts and shares are over its binders.
    abstraction: ?Abstraction = null,
    /// The rest binders of a conclusion bag that has more than one.
    shares: []const usize = &.{},
    /// The term applications the conclusion fixes outside bags: of two
    /// unsafe rules, the one whose conclusion says more about the goal is
    /// tried first.
    specificity: u8 = 0,

    /// The statement the core matches and proves: an abstraction's view,
    /// else the rule itself.
    pub fn statement(self: *const Rule, context: *const Context) *const RuleDecl {
        if (self.abstraction) |*abstraction| return &abstraction.statement;
        return &context.env.rules.items[self.rule_id];
    }

    /// Whether the rule has a γ cut, a value only a premise's closure picks.
    pub fn hasGammaCut(self: *const Rule) bool {
        for (self.cuts) |cut| {
            if (cut.kind == .gamma) return true;
        }
        return false;
    }

    fn deinit(self: Rule, allocator: std.mem.Allocator) void {
        allocator.free(self.witnesses);
        allocator.free(self.cuts);
        allocator.free(self.shares);
    }
};

/// A binder the conclusion leaves open, and the view binder its premise
/// formula is: `pattern` (a rule binder) with the bound variable `hole` (a
/// rule binder) replaced by the witness.
pub const Witness = struct {
    kind: Kind,
    /// The rule binder the witness fills.
    arg: usize,
    /// The view binder holding the instance.
    source: usize,
    pattern: usize,
    hole: usize,
};

/// A binder of a rule without a view that neither the conclusion fixes nor
/// a view reads back: a fresh witness variable (γ) or an eigenvariable (δ).
pub const Cut = struct {
    kind: Kind,
    /// The rule binder.
    arg: usize,
};

pub const Kind = enum { gamma, delta };

/// A rule whose view abstracts one of its binders with bare plugs: its
/// target and hole stay out of the view's statements, and every rule
/// binder is a view binder.
pub const Abstraction = struct {
    view: *const ViewDecl,
    decl: AbstractDecl,
    /// The view as a statement over its own binders.
    statement: RuleDecl,
    /// The view binders its premises hold.
    premise_binders: u64,
};

/// The most arguments one application may have: terms are rebuilt in
/// fixed-size buffers. A rule with a wider application is left out.
pub const max_args = 16;

/// Whether the core reads an `@acui` combiner with `law` as a bag: a
/// commutative one as a set or multiset, a sequence in order. An
/// idempotent sequence, which no theory uses yet, is left out.
pub fn readsLaw(law: AcuiBag.Law) bool {
    return law != .idempotent_sequence;
}

/// The head the rules with a bare-binder conclusion are listed under.
pub const bare_head = std.math.maxInt(u32);

pub const Catalog = struct {
    allocator: std.mem.Allocator,
    /// Admitted rules by conclusion head (`bare_head` for a bare binder):
    /// closers, then safe rules by priority, then unsafe rules, each in
    /// declaration order.
    by_head: std.AutoHashMapUnmanaged(u32, []const Rule) = .empty,

    pub fn deinit(self: *Catalog) void {
        var it = self.by_head.valueIterator();
        while (it.next()) |rules| {
            for (rules.*) |rule| rule.deinit(self.allocator);
            self.allocator.free(rules.*);
        }
        self.by_head.deinit(self.allocator);
        self.* = undefined;
    }

    /// The rules whose conclusion has head `term_id`.
    pub fn forHead(self: *const Catalog, term_id: u32) []const Rule {
        return self.by_head.get(term_id) orelse &.{};
    }
};

pub fn build(allocator: std.mem.Allocator, context: *const Context) !Catalog {
    var lists = std.AutoHashMapUnmanaged(u32, std.ArrayListUnmanaged(Rule)).empty;
    defer {
        var it = lists.valueIterator();
        while (it.next()) |list| {
            for (list.items) |rule| rule.deinit(allocator);
            list.deinit(allocator);
        }
        lists.deinit(allocator);
    }
    const count = @min(context.available_rule_count, context.env.rules.items.len);
    for (0..count) |idx| {
        const rule_id: u32 = @intCast(idx);
        var entry = (try admit(allocator, context, rule_id)) orelse continue;
        errdefer entry.deinit(allocator);
        const rule = &context.env.rules.items[rule_id];
        const concl = entry.statement(context).concl;
        entry.specificity = @intCast(@min(rigidApps(context, concl), std.math.maxInt(u8)));
        if (rule.hyps.len == 0) {
            entry.role = .closer;
        } else if (context.registry.eagerPriority(rule_id)) |priority| {
            entry.role = .safe;
            entry.priority = priority;
        }
        const head = switch (concl) {
            .app => |app| app.term_id,
            .binder => bare_head,
        };
        const gop = try lists.getOrPut(allocator, head);
        if (!gop.found_existing) gop.value_ptr.* = .empty;
        try gop.value_ptr.append(allocator, entry);
    }

    var catalog = Catalog{ .allocator = allocator };
    errdefer catalog.deinit();
    var it = lists.iterator();
    while (it.next()) |entry| {
        const rules = try allocator.dupe(Rule, entry.value_ptr.items);
        errdefer allocator.free(rules);
        std.mem.sort(Rule, rules, {}, ruleLessThan);
        try catalog.by_head.put(allocator, entry.key_ptr.*, rules);
        // The catalog owns the witness, cut and share lists now.
        entry.value_ptr.clearRetainingCapacity();
    }
    return catalog;
}

fn ruleLessThan(_: void, lhs: Rule, rhs: Rule) bool {
    if (lhs.role != rhs.role) return @backingInt(lhs.role) < @backingInt(rhs.role);
    if (lhs.priority != rhs.priority) return lhs.priority < rhs.priority;
    return lhs.rule_id < rhs.rule_id;
}

/// The catalog entry for `rule_id` (role still unset), or null when the
/// core does not apply it. The caller owns the witness, cut and share
/// lists.
fn admit(allocator: std.mem.Allocator, context: *const Context, rule_id: u32) !?Rule {
    const rule = &context.env.rules.items[rule_id];
    switch (rule.concl) {
        .app => {},
        .binder => |idx| {
            if (rule.args[idx].bound or context.views.contains(rule_id)) return null;
        },
    }
    if (context.registry.isRelationTransport(context.env, rule_id)) return null;
    if (context.registry.isAutoBridgeRule(rule_id)) return null;
    if (context.views.getPtr(rule_id)) |view| for (view.derived_bindings) |derived| {
        if (derived == .abstract) return admitAbstraction(allocator, context, rule_id, view);
    };
    if (context.fresh_bindings.contains(rule_id)) return null;
    if (rule.args.len > 64) return null;
    const concl_mask = Rules.templateBinderMask(rule.concl);
    if (concl_mask.overflow) return null;
    if (!templateSupported(context, rule.args, rule.concl, .conclusion)) return null;
    var shares = std.ArrayListUnmanaged(usize).empty;
    errdefer shares.deinit(allocator);
    try collectShares(allocator, context, rule.args, rule.concl, &shares);
    const all: u64 = if (rule.args.len == 64)
        std.math.maxInt(u64)
    else
        (@as(u64, 1) << @intCast(rule.args.len)) - 1;
    // A rule the conclusion fixes keeps its own premises even with a view,
    // as does one whose view reads back no binder (`ex_elim`'s, which only
    // carries `@freshen`).
    const view = (if (concl_mask.mask == all) null else readsBack(context, rule_id, concl_mask.mask)) orelse {
        for (rule.hyps) |hyp| {
            if (!templateSupported(context, rule.args, hyp, .premise)) return null;
        }
        var cuts = std.ArrayListUnmanaged(Cut).empty;
        errdefer cuts.deinit(allocator);
        const rigid = rigidBinders(context, rule.concl);
        for (rule.args, 0..) |arg, idx| {
            if ((rigid >> @intCast(idx)) & 1 != 0) continue;
            // A bound one is δ even when other binders may depend on it
            // (`ex_elim`'s `x`, with `G H: ctx x`): a fresh variable is
            // a value those binders allow too.
            const kind: Kind = if (arg.bound) .delta else .gamma;
            try cuts.append(allocator, .{ .kind = kind, .arg = idx });
        }
        const owned_cuts = try cuts.toOwnedSlice(allocator);
        errdefer allocator.free(owned_cuts);
        return .{
            .rule_id = rule_id,
            .role = .unsafe,
            .premises = rule.hyps,
            .cuts = owned_cuts,
            .shares = try shares.toOwnedSlice(allocator),
        };
    };
    if (view.num_binders > 64) return null;
    var witnesses = std.ArrayListUnmanaged(Witness).empty;
    errdefer witnesses.deinit(allocator);
    var sources: u64 = 0;
    for (view.derived_bindings) |derived| {
        const recover = switch (derived) {
            .recover => |recover| recover,
            .abstract => return null,
        };
        const arg = view.binder_map[recover.target_view_idx] orelse return null;
        if (concl_mask.mask & (@as(u64, 1) << @intCast(arg)) != 0) continue;
        if (view.binder_map[recover.source_view_idx] != null) return null;
        const pattern = view.binder_map[recover.pattern_view_idx] orelse return null;
        const hole = view.binder_map[recover.hole_view_idx] orelse return null;
        if ((concl_mask.mask >> @intCast(pattern)) & 1 == 0) return null;
        if ((concl_mask.mask >> @intCast(hole)) & 1 == 0) return null;
        if (!rule.args[hole].bound) return null;
        const kind: Kind = if (!rule.args[arg].bound)
            .gamma
        else if (Rules.isEigenvariable(rule.args, arg))
            .delta
        else
            return null;
        try witnesses.append(allocator, .{
            .kind = kind,
            .arg = arg,
            .source = recover.source_view_idx,
            .pattern = pattern,
            .hole = hole,
        });
        sources |= @as(u64, 1) << @intCast(recover.source_view_idx);
    }
    // Every unfixed binder is a witness, and every view binder is a rule
    // binder or a witness's instance.
    var fixed = concl_mask.mask;
    for (witnesses.items) |witness| fixed |= @as(u64, 1) << @intCast(witness.arg);
    if (fixed != all) return null;
    for (view.binder_map, 0..) |mapped, idx| {
        if (mapped == null and (sources >> @intCast(idx)) & 1 == 0) return null;
    }
    for (view.hyps) |hyp| {
        if (!templateSupported(context, view.arg_infos, hyp, .premise)) return null;
    }
    const owned_witnesses = try witnesses.toOwnedSlice(allocator);
    errdefer allocator.free(owned_witnesses);
    return .{
        .rule_id = rule_id,
        .role = .unsafe,
        .premises = view.hyps,
        .view = view,
        .witnesses = owned_witnesses,
        .shares = try shares.toOwnedSlice(allocator),
    };
}

/// The entry for `rule_id`, whose view `view` abstracts a binder, or null
/// when the core does not apply it: the abstraction has a pattern plug, a
/// rule binder is no view binder, the target or hole occurs in the view's
/// statements, or a view binder its conclusion leaves open is bound.
fn admitAbstraction(allocator: std.mem.Allocator, context: *const Context, rule_id: u32, view: *const ViewDecl) !?Rule {
    if (view.derived_bindings.len != 1) return null;
    const decl = view.derived_bindings[0].abstract;
    if (decl.hasPattern()) return null;
    const rule = &context.env.rules.items[rule_id];
    if (rule.args.len > 64 or view.num_binders > 64) return null;
    var mapped: u64 = 0;
    for (view.binder_map) |arg| {
        if (arg) |idx| mapped |= @as(u64, 1) << @intCast(idx);
    }
    if (@popCount(mapped) != rule.args.len) return null;
    if (view.binder_map[decl.target_view_idx] == null) return null;
    if (view.binder_map[decl.hole_view_idx] == null or !view.arg_infos[decl.hole_view_idx].bound) return null;
    const statement = RuleDecl{
        .name = rule.name,
        .args = view.arg_infos,
        .arg_names = view.arg_names,
        .hyps = view.hyps,
        .concl = view.concl,
        .kind = rule.kind,
        .is_local = rule.is_local,
    };
    const derived = (@as(u64, 1) << @intCast(decl.target_view_idx)) | (@as(u64, 1) << @intCast(decl.hole_view_idx));
    const concl_mask = Rules.templateBinderMask(view.concl);
    if (concl_mask.overflow or concl_mask.mask & derived != 0) return null;
    if (!templateSupported(context, view.arg_infos, view.concl, .conclusion)) return null;
    var premise_binders: u64 = 0;
    for (view.hyps) |hyp| {
        const mask = Rules.templateBinderMask(hyp);
        if (mask.overflow or mask.mask & derived != 0) return null;
        premise_binders |= mask.mask;
        if (!templateSupported(context, view.arg_infos, hyp, .premise)) return null;
    }
    var shares = std.ArrayListUnmanaged(usize).empty;
    errdefer shares.deinit(allocator);
    try collectShares(allocator, context, view.arg_infos, view.concl, &shares);
    var cuts = std.ArrayListUnmanaged(Cut).empty;
    errdefer cuts.deinit(allocator);
    const rigid = rigidBinders(context, view.concl) | derived;
    for (view.arg_infos, 0..) |arg, idx| {
        if ((rigid >> @intCast(idx)) & 1 != 0) continue;
        if (arg.bound) return null;
        try cuts.append(allocator, .{ .kind = .gamma, .arg = idx });
    }
    const owned_cuts = try cuts.toOwnedSlice(allocator);
    errdefer allocator.free(owned_cuts);
    return .{
        .rule_id = rule_id,
        .role = .unsafe,
        .premises = view.hyps,
        .cuts = owned_cuts,
        .shares = try shares.toOwnedSlice(allocator),
        .abstraction = .{ .view = view, .decl = decl, .statement = statement, .premise_binders = premise_binders },
    };
}

/// The view of `rule_id` when it reads back a binder the conclusion
/// `concl_mask` does not fix.
fn readsBack(context: *const Context, rule_id: u32, concl_mask: u64) ?*const ViewDecl {
    const view = context.views.getPtr(rule_id) orelse return null;
    for (view.derived_bindings) |derived| {
        const target = switch (derived) {
            .recover => |recover| recover.target_view_idx,
            .abstract => return view,
        };
        const arg = view.binder_map[target] orelse return view;
        if ((concl_mask >> @intCast(arg)) & 1 == 0) return view;
    }
    return null;
}

/// A template the core can match and build: applications of at most
/// `max_args` arguments and only `@acui` combiners the core reads
/// (`readsLaw`). A conclusion bag with more than one rest binder also
/// needs an idempotent law, so its shares can overlap.
fn templateSupported(
    context: *const Context,
    args: []const ArgInfo,
    template: TemplateExpr,
    side: enum { conclusion, premise },
) bool {
    const app = switch (template) {
        .binder => return true,
        .app => |app| app,
    };
    if (app.args.len > max_args) return false;
    if (app.term_id >= context.env.terms.items.len) return false;
    if (AcuiBag.Combiner.of(context.registry, context.env, app.term_id)) |combiner| {
        if (!readsLaw(combiner.law)) return false;
        const members = combiner.flattenTemplate(template) orelse return false;
        // Distinct rest binders: `g , g` has one.
        var rests: u64 = 0;
        for (members.slice()) |member| switch (member) {
            .binder => |idx| {
                if (isRest(context, args, app.term_id, idx)) rests |= @as(u64, 1) << @intCast(idx);
            },
            .app => if (!templateSupported(context, args, member, side)) return false,
        };
        return @popCount(rests) <= 1 or side == .premise or combiner.law.isIdempotent();
    }
    for (app.args) |arg| {
        if (!templateSupported(context, args, arg, side)) return false;
    }
    return true;
}

/// The binders `template` holds outside the applications of terms some
/// `@rewrite` rule rewrites.
fn rigidBinders(context: *const Context, template: TemplateExpr) u64 {
    return switch (template) {
        .binder => |idx| @as(u64, 1) << @intCast(idx),
        .app => |app| blk: {
            if (context.registry.getRewriteRules(app.term_id).len != 0) break :blk 0;
            var mask: u64 = 0;
            for (app.args) |arg| mask |= rigidBinders(context, arg);
            break :blk mask;
        },
    };
}

/// The applications of `template` outside its bags.
fn rigidApps(context: *const Context, template: TemplateExpr) usize {
    const app = switch (template) {
        .binder => return 0,
        .app => |app| app,
    };
    if (AcuiBag.Combiner.of(context.registry, context.env, app.term_id) != null) return 0;
    var count: usize = 1;
    for (app.args) |arg| count += rigidApps(context, arg);
    return count;
}

/// Whether binder `idx` is a rest binder of a bag headed by `head`: a
/// member of the bag's own sort.
fn isRest(context: *const Context, args: []const ArgInfo, head: u32, idx: usize) bool {
    return std.mem.eql(u8, args[idx].sort_name, context.env.terms.items[head].ret_sort_name);
}

/// Append to `out` the rest binders of each bag of the supported
/// conclusion `template` that has more than one.
fn collectShares(
    allocator: std.mem.Allocator,
    context: *const Context,
    args: []const ArgInfo,
    template: TemplateExpr,
    out: *std.ArrayListUnmanaged(usize),
) !void {
    const app = switch (template) {
        .binder => return,
        .app => |app| app,
    };
    const combiner = AcuiBag.Combiner.of(context.registry, context.env, app.term_id) orelse {
        for (app.args) |arg| try collectShares(allocator, context, args, arg, out);
        return;
    };
    var rests: AcuiBag.Members(usize) = .{};
    for (combiner.flattenTemplate(template).?.slice()) |member| switch (member) {
        .binder => |idx| if (isRest(context, args, app.term_id, idx)) {
            _ = rests.appendDistinct(idx);
        },
        .app => try collectShares(allocator, context, args, member, out),
    };
    // A single rest binder takes what is left over itself.
    if (rests.len > 1) try out.appendSlice(allocator, rests.slice());
}
