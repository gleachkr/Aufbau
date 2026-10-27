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
//! The conclusion fixes every binder of a rule except its witnesses: a
//! binder its `@view` reads back with `@recover` from a premise formula the
//! view states as a substitution instance. A witness that is not a bound
//! variable is γ (`all_left`'s `t`): it becomes a fresh witness variable. A
//! bound one is δ (`all_intro`'s `y`), an eigenvariable. Such a rule's
//! premises are the view's, so a premise holds the instance itself, not a
//! substitution redex. Rules are admitted over commutative `@acui` bags
//! with at most one rest binder per bag. A definition is an ordinary term
//! constructor: the core never unfolds it, and a proof that needs the
//! unfolding is the checker's to find or the generation search's. Rules
//! with other unfixed binders (cuts) or fresh variables wait for the later
//! stages, as do bridges, which only link facts already in hand.

const std = @import("std");
const TemplateExpr = @import("../../../rules.zig").TemplateExpr;
const Rules = @import("../../../rules.zig");
const AcuiBag = @import("../../../acui_bag.zig");
const ArgInfo = @import("../../../parse_recovery.zig").ArgInfo;
const ViewDecl = @import("../../../views.zig").ViewDecl;
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
};

/// A binder the conclusion leaves open, and the view binder its premise
/// formula is: `pattern` (a rule binder) with the bound variable `hole` (a
/// rule binder) replaced by the witness.
pub const Witness = struct {
    kind: enum { gamma, delta },
    /// The rule binder the witness fills.
    arg: usize,
    /// The view binder holding the instance.
    source: usize,
    pattern: usize,
    hole: usize,
};

/// The most arguments one application may have: terms are rebuilt in
/// fixed-size buffers. A rule with a wider application is left out.
pub const max_args = 16;

pub const Catalog = struct {
    allocator: std.mem.Allocator,
    /// Admitted rules by conclusion head: closers, then safe rules by
    /// priority, then unsafe rules, each in declaration order.
    by_head: std.AutoHashMapUnmanaged(u32, []const Rule) = .empty,

    pub fn deinit(self: *Catalog) void {
        var it = self.by_head.valueIterator();
        while (it.next()) |rules| {
            for (rules.*) |rule| self.allocator.free(rule.witnesses);
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
            for (list.items) |rule| allocator.free(rule.witnesses);
            list.deinit(allocator);
        }
        lists.deinit(allocator);
    }
    const count = @min(context.available_rule_count, context.env.rules.items.len);
    for (0..count) |idx| {
        const rule_id: u32 = @intCast(idx);
        var entry = (try admit(allocator, context, rule_id)) orelse continue;
        errdefer allocator.free(entry.witnesses);
        const rule = &context.env.rules.items[rule_id];
        if (rule.hyps.len == 0) {
            entry.role = .closer;
        } else if (context.registry.eagerPriority(rule_id)) |priority| {
            entry.role = .safe;
            entry.priority = priority;
        }
        const gop = try lists.getOrPut(allocator, rule.concl.app.term_id);
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
        // The catalog owns the witness lists now.
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
/// core does not apply it. The caller owns the witness list.
fn admit(allocator: std.mem.Allocator, context: *const Context, rule_id: u32) !?Rule {
    const rule = &context.env.rules.items[rule_id];
    // A bare-binder conclusion matches every goal (a relation transport, or
    // a cut); its premises then fix nothing the goal does not.
    if (rule.concl != .app) return null;
    if (context.registry.isAutoBridgeRule(rule_id)) return null;
    if (context.fresh_bindings.contains(rule_id)) return null;
    if (rule.args.len > 64) return null;
    const concl_mask = Rules.templateBinderMask(rule.concl);
    if (concl_mask.overflow) return null;
    if (!templateSupported(context, rule.args, rule.concl)) return null;
    const all: u64 = if (rule.args.len == 64)
        std.math.maxInt(u64)
    else
        (@as(u64, 1) << @intCast(rule.args.len)) - 1;
    if (concl_mask.mask == all) {
        for (rule.hyps) |hyp| {
            if (!templateSupported(context, rule.args, hyp)) return null;
        }
        return .{ .rule_id = rule_id, .role = .unsafe, .premises = rule.hyps };
    }

    const view = context.views.getPtr(rule_id) orelse return null;
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
        const kind: @FieldType(Witness, "kind") = if (!rule.args[arg].bound)
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
        if (!templateSupported(context, view.arg_infos, hyp)) return null;
    }
    return .{
        .rule_id = rule_id,
        .role = .unsafe,
        .premises = view.hyps,
        .view = view,
        .witnesses = try witnesses.toOwnedSlice(allocator),
    };
}

/// A template the core can match and build: applications of at most
/// `max_args` arguments, only commutative `@acui` combiners, each bag with
/// at most one rest binder.
fn templateSupported(
    context: *const Context,
    args: []const ArgInfo,
    template: TemplateExpr,
) bool {
    const app = switch (template) {
        .binder => return true,
        .app => |app| app,
    };
    if (app.args.len > max_args) return false;
    if (app.term_id >= context.env.terms.items.len) return false;
    if (AcuiBag.Combiner.of(context.registry, context.env, app.term_id)) |combiner| {
        if (!combiner.law.isCommutative()) return false;
        const members = combiner.flattenTemplate(template) orelse return false;
        const bag_sort = context.env.terms.items[app.term_id].ret_sort_name;
        var rest: usize = 0;
        for (members.slice()) |member| switch (member) {
            .binder => |idx| {
                if (std.mem.eql(u8, args[idx].sort_name, bag_sort)) rest += 1;
            },
            .app => if (!templateSupported(context, args, member)) return false,
        };
        return rest <= 1;
    }
    for (app.args) |arg| {
        if (!templateSupported(context, args, arg)) return false;
    }
    return true;
}
