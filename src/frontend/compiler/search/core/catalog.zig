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
//! Stage C0 admits only rules whose conclusion fixes every binder, over
//! commutative `@acui` bags with at most one rest binder per bag. Rules
//! with views, fresh variables, bound binders or definitions wait for the
//! later stages, as do bridges, which only link facts already in hand.

const std = @import("std");
const TemplateExpr = @import("../../../rules.zig").TemplateExpr;
const Rules = @import("../../../rules.zig");
const AcuiBag = @import("../../../acui_bag.zig");
const RuleDecl = @import("../../../env.zig").RuleDecl;
const Context = @import("../types.zig").Context;

pub const Role = enum { closer, safe, unsafe };

pub const Rule = struct {
    rule_id: u32,
    role: Role,
    /// `@auto eager` priority (1 = tried first); 0 for other rules.
    priority: u8 = 0,
};

/// The most arguments one template application may have. Templates are
/// matched with stack-allocated continuations; a rule with a wider
/// application is left out.
pub const max_args = 16;

/// The most premises an admitted rule may have.
pub const max_premises = 16;

pub const Catalog = struct {
    allocator: std.mem.Allocator,
    /// Admitted rules by conclusion head: closers, then safe rules by
    /// priority, then unsafe rules, each in declaration order.
    by_head: std.AutoHashMapUnmanaged(u32, []const Rule) = .empty,

    pub fn deinit(self: *Catalog) void {
        var it = self.by_head.valueIterator();
        while (it.next()) |rules| self.allocator.free(rules.*);
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
        while (it.next()) |list| list.deinit(allocator);
        lists.deinit(allocator);
    }
    const count = @min(context.available_rule_count, context.env.rules.items.len);
    for (0..count) |idx| {
        const rule_id: u32 = @intCast(idx);
        if (!admits(context, rule_id)) continue;
        const rule = &context.env.rules.items[rule_id];
        const entry: Rule = if (rule.hyps.len == 0)
            .{ .rule_id = rule_id, .role = .closer }
        else if (context.registry.eagerPriority(rule_id)) |priority|
            .{ .rule_id = rule_id, .role = .safe, .priority = priority }
        else
            .{ .rule_id = rule_id, .role = .unsafe };
        const gop = try lists.getOrPut(allocator, rule.concl.app.term_id);
        if (!gop.found_existing) gop.value_ptr.* = .empty;
        try gop.value_ptr.append(allocator, entry);
    }

    var catalog = Catalog{ .allocator = allocator };
    errdefer catalog.deinit();
    var it = lists.iterator();
    while (it.next()) |entry| {
        const rules = try allocator.dupe(Rule, entry.value_ptr.items);
        std.mem.sort(Rule, rules, {}, ruleLessThan);
        try catalog.by_head.put(allocator, entry.key_ptr.*, rules);
    }
    return catalog;
}

fn ruleLessThan(_: void, lhs: Rule, rhs: Rule) bool {
    if (lhs.role != rhs.role) return @backingInt(lhs.role) < @backingInt(rhs.role);
    if (lhs.priority != rhs.priority) return lhs.priority < rhs.priority;
    return lhs.rule_id < rhs.rule_id;
}

/// Whether stage C0 applies `rule_id`.
fn admits(context: *const Context, rule_id: u32) bool {
    const rule = &context.env.rules.items[rule_id];
    // A bare-binder conclusion matches every goal (a relation transport, or
    // a cut); its premises then fix nothing the goal does not.
    if (rule.concl != .app) return false;
    if (context.registry.isAutoBridgeRule(rule_id)) return false;
    if (context.views.contains(rule_id) or
        context.fresh_bindings.contains(rule_id) or
        context.freshen_bindings.contains(rule_id)) return false;
    if (rule.args.len > 64) return false;
    for (rule.args) |arg| {
        if (arg.bound) return false;
    }
    if (rule.hyps.len > max_premises) return false;
    const concl_mask = Rules.templateBinderMask(rule.concl);
    if (concl_mask.overflow) return false;
    // Every binder is fixed by the conclusion.
    const all: u64 = if (rule.args.len == 64)
        std.math.maxInt(u64)
    else
        (@as(u64, 1) << @intCast(rule.args.len)) - 1;
    if (concl_mask.mask != all) return false;
    if (!templateSupported(context, rule, rule.concl)) return false;
    for (rule.hyps) |hyp| {
        if (!templateSupported(context, rule, hyp)) return false;
    }
    return true;
}

/// A template the core can match and build: no definitions, applications
/// of at most `max_args` arguments, only commutative `@acui` combiners,
/// each bag with at most one rest binder.
fn templateSupported(
    context: *const Context,
    rule: *const RuleDecl,
    template: TemplateExpr,
) bool {
    const app = switch (template) {
        .binder => return true,
        .app => |app| app,
    };
    if (app.args.len > max_args) return false;
    if (app.term_id >= context.env.terms.items.len) return false;
    if (context.env.terms.items[app.term_id].is_def) return false;
    if (AcuiBag.Combiner.of(context.registry, context.env, app.term_id)) |combiner| {
        if (!combiner.law.isCommutative()) return false;
        const members = combiner.flattenTemplate(template) orelse return false;
        const bag_sort = context.env.terms.items[app.term_id].ret_sort_name;
        var rest: usize = 0;
        for (members.slice()) |member| switch (member) {
            .binder => |idx| {
                if (std.mem.eql(u8, rule.args[idx].sort_name, bag_sort)) rest += 1;
            },
            .app => if (!templateSupported(context, rule, member)) return false,
        };
        return rest <= 1;
    }
    for (app.args) |arg| {
        if (!templateSupported(context, rule, arg)) return false;
    }
    return true;
}
