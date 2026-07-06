const std = @import("std");

const clipper = @import("./clipper.zig");
const refs_mod = @import("./refs.zig");
const shape_mod = @import("./shape.zig");
const types = @import("./types.zig");
const timer = @import("./timer.zig");
const ExprId = @import("../../expr.zig").ExprId;
const TheoremContext = @import("../../expr.zig").TheoremContext;
const TemplateExpr = @import("../../rules.zig").TemplateExpr;
const ArgInfo = @import("../../parse_recovery.zig").ArgInfo;

const Context = types.Context;
const SearchCounters = types.SearchCounters;

pub const SourceKind = enum {
    theorem_hyp,
    checked_line,
};

pub const Entry = struct {
    pool_index: usize,
    /// The pool ref behind this entry. Null for indexes built over bare
    /// expressions (`buildFromExprs`), e.g. the derived-ref pool.
    ref: ?@import("../../proof_script.zig").Ref,
    source_kind: SourceKind,
    expr: ExprId,
    order: usize,
};

pub const LookupResult = struct {
    allocator: std.mem.Allocator,
    indices: []usize,
    broad: bool = false,

    pub fn deinit(self: *LookupResult) void {
        self.allocator.free(self.indices);
        self.* = undefined;
    }
};

// Session-scoped memo of query-side template `ShapeSet`s. The backtracker asks
// the same rule-hyp slot question at every node (~260k shape builds against a
// ~16-ref index on the zermelo found-outliers), so `lookupTemplateDual`
// memoizes the built set. Soundness is by construction, not by corpus: the key
// is a full structural serialization of every theorem-dependent input the
// shape `Builder` reads — resolved node structure, variable leaf kind + index
// + sort, placeholder leaf sort ONLY (identity is never read: `shape.zig`
// `varLeaf` keys variables by numeric index, `.placeholder` renders a pure
// sort-wildcard). Key-equal therefore implies builder-output-equal even across
// sibling COW clones that reuse overlay ExprIds for different exprs (the
// aliasing that made a raw-ExprId key unsound). Everything else the builder
// consults (env decls, rewrite registry, `Options`) is fixed per `Index`.
const ShapeCache = struct {
    map: std.StringHashMapUnmanaged(shape_mod.ShapeSet) = .empty,
    // Reused per-call key build buffer; `map` keys are owned dupes of it.
    scratch: std.ArrayListUnmanaged(u8) = .{},
    // Per-call DAG backref table (ExprId → first-visit ordinal), so shared
    // subterms serialize as O(1) backrefs instead of exponential tree copies.
    // Within one call all ids come from one theorem clone, so id-equal means
    // node-equal; the ordinals are first-visit-deterministic.
    backrefs: std.AutoHashMapUnmanaged(ExprId, u32) = .empty,

    fn deinit(self: *ShapeCache, allocator: std.mem.Allocator) void {
        var it = self.map.iterator();
        while (it.next()) |entry| {
            allocator.free(entry.key_ptr.*);
            entry.value_ptr.deinit();
        }
        self.map.deinit(allocator);
        self.scratch.deinit(allocator);
        self.backrefs.deinit(allocator);
        self.* = undefined;
    }
};

// Key-stream tags. Template positions and bound-binder expr positions are
// disjoint by construction, but the tag spaces stay distinct anyway so a
// malformed serialization can never make two different inputs collide.
const key_backref: u8 = 0;
const key_expr_app: u8 = 1;
const key_theorem_var: u8 = 2;
const key_dummy_var: u8 = 3;
const key_placeholder: u8 = 4;
const key_template_app: u8 = 5;
const key_binder_unbound: u8 = 6;
const key_binder_bound: u8 = 7;

pub const Index = struct {
    allocator: std.mem.Allocator,
    context: *const Context,
    clipper_index: clipper.Index,
    entries: []Entry,
    options: shape_mod.Options,
    // Behind a pointer so `*const Index` lookups can populate it.
    shape_cache: ?*ShapeCache = null,

    pub fn build(
        allocator: std.mem.Allocator,
        context: *const Context,
        theorem: *const TheoremContext,
        pool: []const refs_mod.RefPoolEntry,
        options: shape_mod.Options,
        counters: ?*SearchCounters,
    ) !Index {
        const build_start = timer.timestampIf(counters != null);
        const entries = try allocator.alloc(Entry, pool.len);
        errdefer allocator.free(entries);
        var result = Index{
            .allocator = allocator,
            .context = context,
            .clipper_index = try clipper.Index.init(allocator),
            .entries = entries,
            .options = options,
        };
        errdefer result.clipper_index.deinit();

        const builder = shape_mod.Builder.initWithRegistry(
            allocator,
            context.env,
            context.registry,
            options,
        );
        for (pool, 0..) |pool_entry, pool_index| {
            const item = result.clipper_index.addItem();
            std.debug.assert(item == pool_index);
            const expr = try refs_mod.sourceRefExpr(
                context,
                theorem,
                pool_entry.ref,
            );
            result.entries[pool_index] = .{
                .pool_index = pool_index,
                .ref = pool_entry.ref,
                .source_kind = sourceKind(pool_entry.ref),
                .expr = expr,
                .order = pool_entry.order,
            };
            var shapes = try builder.fromExprId(theorem, expr);
            defer shapes.deinit();
            for (shapes.variants) |variant| {
                try result.clipper_index.insertShape(pool_index, variant);
            }
        }
        if (counters) |actual| {
            actual.ref_index_build_ns += timer.elapsedSince(build_start);
        }
        return result;
    }

    /// Build an index over bare expressions — used for the derived-ref pool,
    /// whose shapes carry universal-meta leaves. The shape
    /// builder maps placeholder leaves to covering wildcards, so a lookup can
    /// only over-approximate the matching derived refs, never miss one.
    /// Entries carry no pool ref; lookups consume `pool_index` (= the
    /// position in `exprs`).
    pub fn buildFromExprs(
        allocator: std.mem.Allocator,
        context: *const Context,
        theorem: *const TheoremContext,
        exprs: []const ExprId,
        options: shape_mod.Options,
        counters: ?*SearchCounters,
    ) !Index {
        const build_start = timer.timestampIf(counters != null);
        const entries = try allocator.alloc(Entry, exprs.len);
        errdefer allocator.free(entries);
        var result = Index{
            .allocator = allocator,
            .context = context,
            .clipper_index = try clipper.Index.init(allocator),
            .entries = entries,
            .options = options,
        };
        errdefer result.clipper_index.deinit();

        const builder = shape_mod.Builder.initWithRegistry(
            allocator,
            context.env,
            context.registry,
            options,
        );
        for (exprs, 0..) |expr, idx| {
            const item = result.clipper_index.addItem();
            std.debug.assert(item == idx);
            result.entries[idx] = .{
                .pool_index = idx,
                .ref = null,
                .source_kind = .checked_line,
                .expr = expr,
                .order = idx,
            };
            var shapes = try builder.fromExprId(theorem, expr);
            defer shapes.deinit();
            for (shapes.variants) |variant| {
                try result.clipper_index.insertShape(idx, variant);
            }
        }
        if (counters) |actual| {
            actual.ref_index_build_ns += timer.elapsedSince(build_start);
        }
        return result;
    }

    pub fn deinit(self: *Index) void {
        if (self.shape_cache) |cache| {
            cache.deinit(self.allocator);
            self.allocator.destroy(cache);
        }
        self.clipper_index.deinit();
        self.allocator.free(self.entries);
        self.* = undefined;
    }

    pub fn enableShapeCache(self: *Index) !void {
        if (self.shape_cache != null) return;
        const cache = try self.allocator.create(ShapeCache);
        cache.* = .{};
        self.shape_cache = cache;
    }

    pub fn lookupExpected(
        self: *const Index,
        theorem: *const TheoremContext,
        expected: ExprId,
        counters: ?*SearchCounters,
    ) !LookupResult {
        const builder = shape_mod.Builder.initWithRegistry(
            self.allocator,
            self.context.env,
            self.context.registry,
            self.options,
        );
        const shape_start = timer.timestampIf(counters != null);
        var shape_set = try builder.fromExprId(theorem, expected);
        defer shape_set.deinit();
        if (counters) |actual| {
            actual.shape_emission_ns += timer.elapsedSince(shape_start);
            actual.shape_emissions += 1;
        }
        return try self.lookupShapeSet(&shape_set, counters);
    }

    pub fn lookupTemplate(
        self: *const Index,
        theorem: *const TheoremContext,
        template: @import("../../rules.zig").TemplateExpr,
        args: []const @import("../../parse_recovery.zig").ArgInfo,
        bindings: []const ?ExprId,
        counters: ?*SearchCounters,
    ) !LookupResult {
        const dual = try self.lookupTemplateDual(
            null,
            theorem,
            template,
            args,
            bindings,
            counters,
        );
        std.debug.assert(dual.secondary == null);
        return dual.primary;
    }

    /// One template lookup against two indexes: the shape set is built once
    /// and queried against `self` and (when present) `secondary`. Used to ask
    /// the pool index and the derived-ref index the same slot question for
    /// the price of one shape emission.
    pub const DualLookup = struct {
        primary: LookupResult,
        secondary: ?LookupResult,

        pub fn deinit(self: *DualLookup) void {
            self.primary.deinit();
            if (self.secondary) |*lookup| lookup.deinit();
            self.* = undefined;
        }
    };

    pub fn lookupTemplateDual(
        self: *const Index,
        secondary: ?*const Index,
        theorem: *const TheoremContext,
        template: @import("../../rules.zig").TemplateExpr,
        args: []const @import("../../parse_recovery.zig").ArgInfo,
        bindings: []const ?ExprId,
        counters: ?*SearchCounters,
    ) !DualLookup {
        const shape_start = timer.timestampIf(counters != null);
        var local_set: ?shape_mod.ShapeSet = null;
        defer if (local_set) |*set| set.deinit();
        const shape_set: *const shape_mod.ShapeSet = blk: {
            if (self.shape_cache) |cache| {
                if (try buildCallKey(
                    self.allocator,
                    cache,
                    theorem,
                    template,
                    args,
                    bindings,
                )) {
                    if (cache.map.getPtr(cache.scratch.items)) |hit| {
                        if (counters) |actual| actual.shape_cache_hits += 1;
                        break :blk hit;
                    }
                    var built = try self.buildTemplateShapes(
                        theorem,
                        template,
                        args,
                        bindings,
                    );
                    errdefer built.deinit();
                    const owned_key = try self.allocator.dupe(
                        u8,
                        cache.scratch.items,
                    );
                    errdefer self.allocator.free(owned_key);
                    try cache.map.putNoClobber(self.allocator, owned_key, built);
                    if (counters) |actual| actual.shape_cache_misses += 1;
                    break :blk cache.map.getPtr(owned_key).?;
                }
            }
            local_set = try self.buildTemplateShapes(
                theorem,
                template,
                args,
                bindings,
            );
            break :blk &local_set.?;
        };
        if (counters) |actual| {
            actual.shape_emission_ns += timer.elapsedSince(shape_start);
            actual.shape_emissions += 1;
        }
        var primary = try self.lookupShapeSet(shape_set, counters);
        errdefer primary.deinit();
        const second: ?LookupResult = if (secondary) |index|
            try index.lookupShapeSet(shape_set, counters)
        else
            null;
        return .{ .primary = primary, .secondary = second };
    }

    fn buildTemplateShapes(
        self: *const Index,
        theorem: *const TheoremContext,
        template: TemplateExpr,
        args: []const ArgInfo,
        bindings: []const ?ExprId,
    ) !shape_mod.ShapeSet {
        const builder = shape_mod.Builder.initWithRegistry(
            self.allocator,
            self.context.env,
            self.context.registry,
            self.options,
        );
        return try builder.fromTemplateWithBindings(
            theorem,
            template,
            args,
            bindings,
        );
    }

    // A `@recover` coupling constraint expressed as an ACUI-member containment
    // query: the context (arg `ctx_arg_index` of the `turnstile_term_id`
    // sequent) of the matched hypothesis must hold a member `wrapper(pattern)`
    // with the recover `hole` widened. See `lookupTemplateInjected`.
    pub const RecoverMemberInjection = struct {
        turnstile_term_id: u32,
        ctx_arg_index: usize,
        wrapper_term_id: u32,
        pattern: ExprId,
        hole: ExprId,
    };

    // Like `lookupTemplate`, but before querying, splice extra ACUI members into
    // the context region of the built sequent shape. This pushes a cross-hyp
    // `@recover` coupling constraint into the index: instead of the permissive
    // view (whose free context binder `q` shapes to a covering wildcard), the
    // query demands a context member matching the recover pattern, so refs that
    // could never satisfy the recover law are filtered cheaply at lookup rather
    // than after full validation. Sound: injecting a member only narrows the
    // accept set, and the pattern's hole is widened so any valid witness still
    // matches.
    pub fn lookupTemplateInjected(
        self: *const Index,
        theorem: *const TheoremContext,
        template: @import("../../rules.zig").TemplateExpr,
        args: []const @import("../../parse_recovery.zig").ArgInfo,
        bindings: []const ?ExprId,
        injections: []const RecoverMemberInjection,
        counters: ?*SearchCounters,
    ) !LookupResult {
        const dual = try self.lookupTemplateInjectedDual(
            null,
            theorem,
            template,
            args,
            bindings,
            injections,
            counters,
        );
        std.debug.assert(dual.secondary == null);
        return dual.primary;
    }

    pub fn lookupTemplateInjectedDual(
        self: *const Index,
        secondary: ?*const Index,
        theorem: *const TheoremContext,
        template: @import("../../rules.zig").TemplateExpr,
        args: []const @import("../../parse_recovery.zig").ArgInfo,
        bindings: []const ?ExprId,
        injections: []const RecoverMemberInjection,
        counters: ?*SearchCounters,
    ) !DualLookup {
        const builder = shape_mod.Builder.initWithRegistry(
            self.allocator,
            self.context.env,
            self.context.registry,
            self.options,
        );
        const shape_start = timer.timestampIf(counters != null);
        var shape_set = try builder.fromTemplateWithBindings(
            theorem,
            template,
            args,
            bindings,
        );
        defer shape_set.deinit();
        for (shape_set.variants) |*variant| {
            for (injections) |inj| {
                try injectMember(self.allocator, &builder, theorem, variant, inj);
            }
        }
        if (counters) |actual| {
            actual.shape_emission_ns += timer.elapsedSince(shape_start);
            actual.shape_emissions += 1;
        }
        var primary = try self.lookupShapeSet(&shape_set, counters);
        errdefer primary.deinit();
        const second: ?LookupResult = if (secondary) |index|
            try index.lookupShapeSet(&shape_set, counters)
        else
            null;
        return .{ .primary = primary, .secondary = second };
    }

    fn lookupShapeSet(
        self: *const Index,
        shape_set: *const shape_mod.ShapeSet,
        counters: ?*SearchCounters,
    ) !LookupResult {
        if (allVariantsBroad(shape_set.variants)) {
            return try self.lookupSort(
                rootSort(shape_set.variants[0]),
                true,
                counters,
            );
        }

        const lookup_start = timer.timestampIf(counters != null);
        var live = clipper.BitSet{};
        defer live.deinit(self.allocator);
        for (shape_set.variants) |variant| {
            var bits = try self.clipper_index.query(variant);
            defer bits.deinit(self.allocator);
            try live.unionWith(self.allocator, &bits);
        }
        const items = try self.clipper_index.collect(&live);
        defer self.allocator.free(items);
        const indices = try self.indicesFromItems(items);
        if (counters) |actual| {
            actual.ref_lookup_ns += timer.elapsedSince(lookup_start);
        }
        return .{
            .allocator = self.allocator,
            .indices = indices,
            .broad = false,
        };
    }

    pub fn lookupSort(
        self: *const Index,
        sort_id: clipper.SortId,
        broad: bool,
        counters: ?*SearchCounters,
    ) !LookupResult {
        const lookup_start = timer.timestampIf(counters != null);
        var bits = try self.clipper_index.query(.{ .hole = sort_id });
        defer bits.deinit(self.allocator);
        const items = try self.clipper_index.collect(&bits);
        defer self.allocator.free(items);
        const indices = try self.indicesFromItems(items);
        if (counters) |actual| {
            actual.ref_lookup_ns += timer.elapsedSince(lookup_start);
        }
        return .{
            .allocator = self.allocator,
            .indices = indices,
            .broad = broad,
        };
    }

    fn indicesFromItems(
        self: *const Index,
        items: []const clipper.ItemId,
    ) ![]usize {
        const indices = try self.allocator.alloc(usize, items.len);
        errdefer self.allocator.free(indices);
        for (items, 0..) |item, idx| {
            indices[idx] = self.entries[item].pool_index;
        }
        return indices;
    }
};

// Splice one recover-coupling member into a sequent variant's context region.
// No-ops (sound) unless the variant is the expected turnstile with an ACUI
// region at `ctx_arg_index` — a wildcard/broad variant or an unexpected shape
// simply keeps its permissive form. The built member is owned by the variant
// tree afterwards (freed by `ShapeSet.deinit`).
fn injectMember(
    allocator: std.mem.Allocator,
    builder: *const shape_mod.Builder,
    theorem: *const TheoremContext,
    variant: *clipper.ShapeNode,
    inj: Index.RecoverMemberInjection,
) !void {
    const cnode = switch (variant.*) {
        .concrete => |*c| c,
        else => return,
    };
    if (cnode.token.term_id != inj.turnstile_term_id) return;
    if (inj.ctx_arg_index >= cnode.children.len) return;
    const children = @constCast(cnode.children);
    const ctx_child = &children[inj.ctx_arg_index];
    const acui = switch (ctx_child.*) {
        .acui => |*a| a,
        else => return,
    };

    const member = try builder.recoverMemberShape(
        theorem,
        inj.wrapper_term_id,
        inj.pattern,
        inj.hole,
    );
    errdefer shape_mod.deinitShape(allocator, member);

    const old = acui.members;
    const new_members = try allocator.alloc(clipper.ShapeNode, old.len + 1);
    @memcpy(new_members[0..old.len], old);
    new_members[old.len] = member;
    allocator.free(@constCast(old));
    acui.members = new_members;
}

fn sourceKind(ref: @import("../../proof_script.zig").Ref) SourceKind {
    return switch (ref) {
        .hyp => .theorem_hyp,
        .line => .checked_line,
        .application => .checked_line,
    };
}

fn allVariantsBroad(variants: []const clipper.ShapeNode) bool {
    for (variants) |variant| {
        if (isConcreteRoot(variant)) return false;
    }
    return true;
}

fn isConcreteRoot(shape: clipper.ShapeNode) bool {
    return switch (shape) {
        // An ACUI region carries discriminating member structure, so it is not
        // a broad root even though its top is the (collapsed) combiner.
        .concrete, .acui => true,
        .wildcard, .hole => false,
    };
}

fn rootSort(shape: clipper.ShapeNode) clipper.SortId {
    return switch (shape) {
        .concrete => |node| node.sort,
        .acui => |node| node.sort,
        .wildcard => |sort_id| sort_id,
        .hole => |sort_id| sort_id,
    };
}

// Serialize the full builder-input key for one `lookupTemplateDual` call into
// `cache.scratch`. Returns false when the call should not be cached (an
// anomalous input the builder itself would reject or widen); the caller then
// builds uncached, preserving behavior exactly.
fn buildCallKey(
    allocator: std.mem.Allocator,
    cache: *ShapeCache,
    theorem: *const TheoremContext,
    template: TemplateExpr,
    args: []const ArgInfo,
    bindings: []const ?ExprId,
) error{OutOfMemory}!bool {
    cache.scratch.clearRetainingCapacity();
    cache.backrefs.clearRetainingCapacity();
    return keyTemplate(allocator, cache, theorem, template, args, bindings);
}

fn keyTemplate(
    allocator: std.mem.Allocator,
    cache: *ShapeCache,
    theorem: *const TheoremContext,
    template: TemplateExpr,
    args: []const ArgInfo,
    bindings: []const ?ExprId,
) error{OutOfMemory}!bool {
    switch (template) {
        .binder => |idx| {
            if (idx >= args.len) return false;
            const bound: ?ExprId = if (idx < bindings.len)
                bindings[idx]
            else
                null;
            if (bound) |expr_id| {
                try keyByte(allocator, cache, key_binder_bound);
                // The builder still reads the arg sort of a bound binder: it
                // is the node-budget fallback wildcard's sort.
                try keyBytes(allocator, cache, args[idx].sort_name);
                return try keyExpr(allocator, cache, theorem, expr_id);
            }
            try keyByte(allocator, cache, key_binder_unbound);
            try keyBytes(allocator, cache, args[idx].sort_name);
            return true;
        },
        .app => |app| {
            try keyByte(allocator, cache, key_template_app);
            try keyU32(allocator, cache, app.term_id);
            try keyU32(allocator, cache, @intCast(app.args.len));
            for (app.args) |arg| {
                const ok = try keyTemplate(
                    allocator,
                    cache,
                    theorem,
                    arg,
                    args,
                    bindings,
                );
                if (!ok) return false;
            }
            return true;
        },
    }
}

fn keyExpr(
    allocator: std.mem.Allocator,
    cache: *ShapeCache,
    theorem: *const TheoremContext,
    expr_id: ExprId,
) error{OutOfMemory}!bool {
    const gop = try cache.backrefs.getOrPut(allocator, expr_id);
    if (gop.found_existing) {
        try keyByte(allocator, cache, key_backref);
        try keyU32(allocator, cache, gop.value_ptr.*);
        return true;
    }
    gop.value_ptr.* = @intCast(cache.backrefs.count() - 1);
    switch (theorem.interner.node(expr_id).*) {
        .app => |app| {
            try keyByte(allocator, cache, key_expr_app);
            try keyU32(allocator, cache, app.term_id);
            try keyU32(allocator, cache, @intCast(app.args.len));
            for (app.args) |arg| {
                if (!try keyExpr(allocator, cache, theorem, arg)) return false;
            }
            return true;
        },
        .variable => |var_id| {
            const info = (theorem.currentLeafInfo(expr_id) catch
                return false) orelse return false;
            switch (var_id) {
                .theorem_var => |idx| {
                    try keyByte(allocator, cache, key_theorem_var);
                    try keyU32(allocator, cache, idx);
                },
                .dummy_var => |idx| {
                    try keyByte(allocator, cache, key_dummy_var);
                    try keyU32(allocator, cache, idx);
                },
            }
            try keyBytes(allocator, cache, info.sort_name);
            return true;
        },
        .placeholder => {
            const info = (theorem.currentLeafInfo(expr_id) catch
                return false) orelse return false;
            try keyByte(allocator, cache, key_placeholder);
            try keyBytes(allocator, cache, info.sort_name);
            return true;
        },
    }
}

fn keyByte(
    allocator: std.mem.Allocator,
    cache: *ShapeCache,
    value: u8,
) error{OutOfMemory}!void {
    try cache.scratch.append(allocator, value);
}

fn keyU32(
    allocator: std.mem.Allocator,
    cache: *ShapeCache,
    value: u32,
) error{OutOfMemory}!void {
    try cache.scratch.appendSlice(allocator, &std.mem.toBytes(value));
}

fn keyBytes(
    allocator: std.mem.Allocator,
    cache: *ShapeCache,
    bytes: []const u8,
) error{OutOfMemory}!void {
    try keyU32(allocator, cache, @intCast(bytes.len));
    try cache.scratch.appendSlice(allocator, bytes);
}

// The load-bearing soundness property of the cache key (the raw-ExprId cache
// this replaces was unsound exactly here): sibling COW clones mint overlapping
// overlay ExprIds for different exprs, so the key must resolve binding CONTENT
// through the querying clone, never reuse ids. See ShapeCache doc.
test "shape cache key resolves binding content, not ExprIds, across sibling clones" {
    const allocator = std.testing.allocator;

    var base = @import("../../expr.zig").TheoremContext.init(allocator);
    defer base.deinit();
    const a_expr = try base.interner.internApp(0, &.{});

    var clone_a = try base.clone();
    defer clone_a.deinit();
    var clone_b = try base.clone();
    defer clone_b.deinit();

    // Same overlay id in both clones, different content: P(a) vs R(a).
    const p_a = try clone_a.interner.internApp(1, &.{a_expr});
    const r_b = try clone_b.interner.internApp(2, &.{a_expr});
    try std.testing.expectEqual(p_a, r_b);

    var cache = ShapeCache{};
    defer cache.deinit(allocator);

    const args = [_]ArgInfo{
        .{ .sort_name = "wff", .bound = false, .deps = 0 },
    };
    const template = TemplateExpr{ .binder = 0 };

    const key_a = blk: {
        const bindings = [_]?ExprId{p_a};
        try std.testing.expect(try buildCallKey(
            allocator,
            &cache,
            &clone_a,
            template,
            &args,
            &bindings,
        ));
        break :blk try allocator.dupe(u8, cache.scratch.items);
    };
    defer allocator.free(key_a);

    // Same id, different content -> different key.
    {
        const bindings = [_]?ExprId{r_b};
        try std.testing.expect(try buildCallKey(
            allocator,
            &cache,
            &clone_b,
            template,
            &args,
            &bindings,
        ));
        try std.testing.expect(
            !std.mem.eql(u8, key_a, cache.scratch.items),
        );
    }

    // Different id, equal content -> equal key (the cross-clone sharing that
    // carries the win).
    {
        const p_b = try clone_b.interner.internApp(1, &.{a_expr});
        const bindings = [_]?ExprId{p_b};
        try std.testing.expect(try buildCallKey(
            allocator,
            &cache,
            &clone_b,
            template,
            &args,
            &bindings,
        ));
        try std.testing.expectEqualSlices(u8, key_a, cache.scratch.items);
    }
}

// Shared subterms serialize as backrefs, so DAG-shaped bindings can't blow up
// exponentially, and the backref ordinals are deterministic in visit order.
test "shape cache key uses backrefs for shared subterms" {
    const allocator = std.testing.allocator;

    var theorem = @import("../../expr.zig").TheoremContext.init(allocator);
    defer theorem.deinit();
    const a_expr = try theorem.interner.internApp(0, &.{});
    // pair(a, a): second occurrence must serialize as a backref.
    const pair = try theorem.interner.internApp(1, &.{ a_expr, a_expr });

    var cache = ShapeCache{};
    defer cache.deinit(allocator);

    const args = [_]ArgInfo{
        .{ .sort_name = "wff", .bound = false, .deps = 0 },
    };
    const template = TemplateExpr{ .binder = 0 };
    const bindings = [_]?ExprId{pair};
    try std.testing.expect(try buildCallKey(
        allocator,
        &cache,
        &theorem,
        template,
        &args,
        &bindings,
    ));
    // Serializing pair(a, b) with distinct leaves must yield a LONGER key
    // than pair(a, a), whose second leaf collapsed to a backref.
    const key_shared_len = cache.scratch.items.len;
    const b_expr = try theorem.interner.internApp(2, &.{});
    const pair_distinct = try theorem.interner.internApp(
        1,
        &.{ a_expr, b_expr },
    );
    const bindings_distinct = [_]?ExprId{pair_distinct};
    try std.testing.expect(try buildCallKey(
        allocator,
        &cache,
        &theorem,
        template,
        &args,
        &bindings_distinct,
    ));
    try std.testing.expect(cache.scratch.items.len > key_shared_len);
}
