const std = @import("std");

const clipper = @import("./clipper.zig");
const shape_mod = @import("./shape.zig");
const types = @import("./types.zig");
const timer = @import("./timer.zig");
const Env = @import("../../env.zig");
const RewriteRegistry = @import("../../rewrite_registry.zig").RewriteRegistry;
const TheoremContext = @import("../../expr.zig").TheoremContext;

const GlobalEnv = Env.GlobalEnv;
const RuleDecl = Env.RuleDecl;
const Goal = types.Goal;
const SearchCounters = types.SearchCounters;

pub const Source = enum {
    raw,
    view,
};

pub const Entry = struct {
    rule_id: u32,
    declaration_order: usize,
    source_mask: u8 = 0,
    conclusion_sort: clipper.SortId,
    hypothesis_count: usize,
};

const source_raw_bit: u8 = 1 << 0;
const source_view_bit: u8 = 1 << 1;

pub const Index = struct {
    allocator: std.mem.Allocator,
    env: *const GlobalEnv,
    registry: *const RewriteRegistry,
    clipper_index: clipper.Index,
    entries: []Entry,
    options: shape_mod.Options,

    pub fn build(
        allocator: std.mem.Allocator,
        env: *const GlobalEnv,
        registry: *const RewriteRegistry,
        views: *const std.AutoHashMap(u32, types.ViewDecl),
        options: shape_mod.Options,
        counters: ?*SearchCounters,
    ) !Index {
        const build_start = timer.timestampIf(counters != null);
        const entries = try allocator.alloc(Entry, env.rules.items.len);
        errdefer allocator.free(entries);
        var result = Index{
            .allocator = allocator,
            .env = env,
            .registry = registry,
            .clipper_index = try clipper.Index.init(allocator),
            .entries = entries,
            .options = options,
        };
        errdefer result.clipper_index.deinit();

        const builder = shape_mod.Builder.initWithRegistry(
            allocator,
            env,
            registry,
            options,
        );
        for (env.rules.items, 0..) |rule, rule_idx| {
            const item = result.clipper_index.addItem();
            std.debug.assert(item == rule_idx);
            const conclusion_sort = try templateSort(env, rule.concl, rule.args);
            result.entries[rule_idx] = .{
                .rule_id = @intCast(rule_idx),
                .declaration_order = rule_idx,
                .conclusion_sort = conclusion_sort,
                .hypothesis_count = rule.hyps.len,
            };
            try result.insertRuleConclusion(&builder, rule_idx, rule, .raw);
            if (views.get(@intCast(rule_idx))) |view| {
                try result.insertViewConclusion(&builder, rule_idx, &view);
            }
        }
        if (counters) |actual| {
            actual.rule_index_build_ns += timer.elapsedSince(build_start);
        }
        return result;
    }

    pub fn deinit(self: *Index) void {
        self.clipper_index.deinit();
        self.allocator.free(self.entries);
        self.* = undefined;
    }

    pub fn lookupGoal(
        self: *const Index,
        goal: Goal,
        theorem: *const TheoremContext,
        available_rule_count: usize,
        counters: ?*SearchCounters,
    ) ![]u32 {
        const shape_start = timer.timestampIf(counters != null);
        var shape_set = try self.shapeGoal(goal, theorem) orelse {
            if (counters) |actual| {
                actual.shape_emission_ns += timer.elapsedSince(shape_start);
                actual.shape_emissions += 1;
                actual.rule_shape_emissions += 1;
            }
            return try self.allAvailableRules(available_rule_count);
        };
        defer shape_set.deinit();
        if (counters) |actual| {
            actual.shape_emission_ns += timer.elapsedSince(shape_start);
            actual.shape_emissions += 1;
            actual.rule_shape_emissions += 1;
        }

        const lookup_start = timer.timestampIf(counters != null);
        var live = clipper.BitSet{};
        defer live.deinit(self.allocator);
        for (shape_set.variants) |variant| {
            var bits = try self.clipper_index.query(variant);
            defer bits.deinit(self.allocator);
            try live.unionWith(self.allocator, &bits);
        }
        var availability = clipper.BitSet{};
        defer availability.deinit(self.allocator);
        const rule_limit = @min(available_rule_count, self.entries.len);
        var rule_idx: usize = 0;
        while (rule_idx < rule_limit) : (rule_idx += 1) {
            try availability.set(self.allocator, rule_idx);
        }
        live.intersectWith(&availability);
        const items = try self.clipper_index.collect(&live);
        defer self.allocator.free(items);

        const rules = try self.allocator.alloc(u32, items.len);
        errdefer self.allocator.free(rules);
        for (items, 0..) |item, idx| {
            rules[idx] = self.entries[item].rule_id;
        }
        if (counters) |actual| {
            actual.rule_lookup_ns += timer.elapsedSince(lookup_start);
        }
        return rules;
    }

    fn insertRuleConclusion(
        self: *Index,
        builder: *const shape_mod.Builder,
        rule_idx: usize,
        rule: RuleDecl,
        source: Source,
    ) !void {
        var shapes = try builder.fromTemplate(rule.concl, rule.args);
        defer shapes.deinit();
        for (shapes.variants) |variant| {
            try self.clipper_index.insertShape(rule_idx, variant);
        }
        self.entries[rule_idx].source_mask |= switch (source) {
            .raw => source_raw_bit,
            .view => source_view_bit,
        };
    }

    fn insertViewConclusion(
        self: *Index,
        builder: *const shape_mod.Builder,
        rule_idx: usize,
        view: *const types.ViewDecl,
    ) !void {
        var shapes = try builder.fromTemplate(view.concl, view.arg_infos);
        defer shapes.deinit();
        for (shapes.variants) |variant| {
            try self.clipper_index.insertShape(rule_idx, variant);
        }
        self.entries[rule_idx].source_mask |= source_view_bit;
    }

    fn shapeGoal(
        self: *const Index,
        goal: Goal,
        theorem: *const TheoremContext,
    ) !?shape_mod.ShapeSet {
        const builder = shape_mod.Builder.initWithRegistry(
            self.allocator,
            self.env,
            self.registry,
            self.options,
        );
        return switch (goal) {
            .concrete => |expr_id| try builder.fromExprId(theorem, expr_id),
            .holey => |expr| try builder.fromSurfaceExpr(expr),
            .implicit_whole_conclusion => |maybe_hint| if (maybe_hint) |hint|
                try builder.fromExprId(theorem, hint)
            else
                null,
        };
    }

    fn allAvailableRules(
        self: *const Index,
        available_rule_count: usize,
    ) ![]u32 {
        const rule_limit = @min(available_rule_count, self.entries.len);
        const rules = try self.allocator.alloc(u32, rule_limit);
        for (rules, 0..) |*rule_id, idx| {
            rule_id.* = @intCast(idx);
        }
        return rules;
    }
};

fn templateSort(
    env: *const GlobalEnv,
    template: @import("../../rules.zig").TemplateExpr,
    args: []const @import("../../parse_recovery.zig").ArgInfo,
) !clipper.SortId {
    const sort_name = switch (template) {
        .app => |app| blk: {
            if (!env.hasAvailableTerm(app.term_id)) return error.UnknownTerm;
            break :blk env.terms.items[app.term_id].ret_sort_name;
        },
        .binder => |idx| blk: {
            if (idx >= args.len) return error.UnknownTemplateBinder;
            break :blk args[idx].sort_name;
        },
    };
    const sort_id = env.sort_names.get(sort_name) orelse return error.UnknownSort;
    return @intCast(sort_id);
}
