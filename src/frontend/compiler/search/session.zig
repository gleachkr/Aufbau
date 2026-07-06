const std = @import("std");

const refs_mod = @import("./refs.zig");
const ref_index_mod = @import("./ref_index.zig");
const rule_index_mod = @import("./rule_index.zig");
const shape_mod = @import("./shape.zig");
const types = @import("./types.zig");
const TheoremContext = @import("../../expr.zig").TheoremContext;

const Context = types.Context;
const Goal = types.Goal;
const SearchCounters = types.SearchCounters;

pub const Options = struct {
    counters: ?*SearchCounters = null,
    shape_options: shape_mod.Options = .{},
    /// Content-keyed query-shape cache on the ref index (see
    /// `ref_index.ShapeCache`). Off only for bench A/B.
    query_shape_cache: bool = true,
};

pub const SearchSession = struct {
    allocator: std.mem.Allocator,
    context: *const Context,
    counters: ?*SearchCounters = null,
    shape_options: shape_mod.Options = .{},
    query_shape_cache: bool = true,
    rule_index: ?rule_index_mod.Index = null,
    reference_pool: ?[]refs_mod.RefPoolEntry = null,
    ref_index: ?ref_index_mod.Index = null,

    pub fn init(context: *const Context, options: Options) SearchSession {
        return .{
            .allocator = context.allocator,
            .context = context,
            .counters = options.counters,
            .shape_options = options.shape_options,
            .query_shape_cache = options.query_shape_cache,
        };
    }

    pub fn deinit(self: *SearchSession) void {
        if (self.rule_index) |*index| {
            index.deinit();
        }
        if (self.ref_index) |*index| {
            index.deinit();
        }
        if (self.reference_pool) |pool| {
            self.allocator.free(pool);
        }
        self.* = undefined;
    }

    pub fn effectiveCounters(
        self: *const SearchSession,
        override: ?*SearchCounters,
    ) ?*SearchCounters {
        return override orelse self.counters;
    }

    pub fn candidateRuleIds(
        self: *SearchSession,
        goal: Goal,
        theorem: *const TheoremContext,
        use_rule_index: bool,
        counters: ?*SearchCounters,
    ) ![]u32 {
        if (!use_rule_index) {
            return try self.allAvailableRuleIds();
        }
        const index = try self.ensureRuleIndex(counters);
        return try index.lookupGoal(
            goal,
            theorem,
            self.context.available_rule_count,
            counters,
        );
    }

    /// Lazily built from the FIRST theorem passed in and reused for the whole
    /// session, so the first caller must be a top-level search: pool entries
    /// capture that theorem's ExprIds, and a `hookSolveOpen` scope clone's ids
    /// die with the scope (generate.zig asserts the ordering at the scope
    /// site). Later callers' theorems all extend the same base id-space.
    pub fn getReferencePool(
        self: *SearchSession,
        theorem: *const TheoremContext,
        counters: ?*SearchCounters,
    ) ![]const refs_mod.RefPoolEntry {
        if (self.reference_pool == null) {
            self.reference_pool = try refs_mod.buildReferencePool(
                self.allocator,
                self.context,
                theorem,
            );
        }
        const pool = self.reference_pool.?;
        if (counters) |actual| {
            actual.ref_pool_size = pool.len;
        }
        return pool;
    }

    pub fn getRefIndex(
        self: *SearchSession,
        theorem: *const TheoremContext,
        counters: ?*SearchCounters,
    ) !*const ref_index_mod.Index {
        if (self.ref_index == null) {
            const pool = try self.getReferencePool(theorem, counters);
            self.ref_index = try ref_index_mod.Index.build(
                self.allocator,
                self.context,
                theorem,
                pool,
                self.shape_options,
                counters,
            );
        }
        if (self.query_shape_cache and self.ref_index.?.shape_cache == null) {
            try self.ref_index.?.enableShapeCache();
        }
        return &self.ref_index.?;
    }

    fn ensureRuleIndex(
        self: *SearchSession,
        counters: ?*SearchCounters,
    ) !*const rule_index_mod.Index {
        if (self.rule_index == null) {
            self.rule_index = try rule_index_mod.Index.build(
                self.allocator,
                self.context.env,
                self.context.registry,
                self.context.views,
                self.shape_options,
                counters,
            );
        }
        return &self.rule_index.?;
    }

    fn allAvailableRuleIds(self: *SearchSession) ![]u32 {
        const rule_limit = @min(
            self.context.available_rule_count,
            self.context.env.rules.items.len,
        );
        const ids = try self.allocator.alloc(u32, rule_limit);
        for (ids, 0..) |*id, idx| {
            id.* = @intCast(idx);
        }
        return ids;
    }
};
