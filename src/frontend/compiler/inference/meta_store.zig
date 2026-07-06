//! Branch-local search metavariable store (META.md Stage 2).
//!
//! A search meta is represented in the interner as an ordinary placeholder
//! leaf whose `PlaceholderId` keys this store; the assignment state lives
//! here, never in the interner node. That keeps interning, hashing, and the
//! COW theorem clone working unchanged, and lets the existing emission
//! leakage guard cover unsolved metas (kind-aware via
//! `PlaceholderClass.meta`).
//!
//! Lifetime/rollback discipline (enforced under real search from Stage 4):
//! - the store is branch-local: one store per search branch, marked before a
//!   hypothesis match and rolled back beside `rollbackOneHypMatch`;
//! - metas are fully solved before every `tryCandidate` call, so validation
//!   never sees a live meta;
//! - a meta leaf is always dereferenced through the store before any
//!   structural match (the matching-site invariant).

const std = @import("std");
const ExprModule = @import("../../expr.zig");
const ExprId = ExprModule.ExprId;
const PlaceholderId = ExprModule.PlaceholderId;
const TheoremContext = ExprModule.TheoremContext;
const GlobalEnv = @import("../../env.zig").GlobalEnv;
const BindingValidation = @import("../../binding_validation.zig");

/// The four placeholder-like search leaves (META.md terminology). Only the
/// store may interpret them; everything else sees an opaque placeholder leaf.
pub const MetaKind = enum {
    /// Matches anything and binds nothing. Hints and shape filtering only.
    wildcard,
    /// Backward-search unknown; must be solved before a proof is emitted.
    existential,
    /// Schematic variable in a derived forward ref; solved transiently when
    /// the derived ref is used (Stage 7 use-time discipline).
    universal,
    /// Search unknown that may need a theorem-local dummy from an @vars pool.
    bound_choice,
};

pub const MetaInfo = struct {
    sort_name: []const u8,
    /// Allowed-dependency constraint set: the theorem dep bits an assignment
    /// is permitted to mention. NOT an allocated dep bit — meta leaves are
    /// minted dep-free (`addMetaPlaceholderResolved`).
    allowed_deps: u55,
    kind: MetaKind,
    /// True for a meta minted by an *enclosing* open slot and registered here
    /// across an interner clone boundary (`registerAncestorMeta`). When such a
    /// meta is solved at this leaf, the binder that mentions it is rendered as
    /// an explicit binding so its now-concrete value rides the conclusion back
    /// up to the slot that minted it (carry-to-leaf).
    ancestor: bool = false,
};

/// Counters mirrored into `SearchCounters` by the search driver once stages
/// 4/7 wire the store in; kept local here so the store has no dependency on
/// the search layer.
pub const MetaStats = struct {
    wildcard_created: usize = 0,
    existential_created: usize = 0,
    universal_created: usize = 0,
    bound_choice_created: usize = 0,
    assignments: usize = 0,
    rollbacks: usize = 0,
};

const TrailEntry = union(enum) {
    minted: PlaceholderId,
    assigned: PlaceholderId,
};

pub const MetaStore = struct {
    allocator: std.mem.Allocator,
    env: *const GlobalEnv,
    metas: std.AutoHashMapUnmanaged(PlaceholderId, MetaInfo) = .empty,
    assignments: std.AutoHashMapUnmanaged(PlaceholderId, ExprId) = .empty,
    trail: std.ArrayListUnmanaged(TrailEntry) = .{},
    /// Universal metas are deferred choices: they may only be assigned during
    /// a derived-ref use-time match (Stage 7), opened explicitly by the
    /// driver. Everywhere else an attempted assignment is a phase error.
    universal_use_open: bool = false,
    stats: MetaStats = .{},
    /// Shared global counter for stable cross-interner `meta_id`s. When set,
    /// `mint` stamps each meta leaf with a globally-unique id (see
    /// `PlaceholderInfo.meta_id`) so an ancestor witness threaded into a
    /// descendant open-target search (across an interner clone boundary) is
    /// still recognizable as the *same* logical meta and can be re-registered
    /// and bound at the leaf. Null on the legacy per-slot path (`exact?`/the
    /// forward derived pool), which keeps byte-identical behavior.
    meta_id_counter: ?*u64 = null,

    pub fn init(
        allocator: std.mem.Allocator,
        env: *const GlobalEnv,
    ) MetaStore {
        return .{ .allocator = allocator, .env = env };
    }

    pub fn deinit(self: *MetaStore) void {
        self.metas.deinit(self.allocator);
        self.assignments.deinit(self.allocator);
        self.trail.deinit(self.allocator);
        self.* = undefined;
    }

    /// Mint a fresh meta leaf in `theorem`'s interner and register it.
    pub fn mint(
        self: *MetaStore,
        theorem: *TheoremContext,
        sort_name: []const u8,
        allowed_deps: u55,
        kind: MetaKind,
    ) !ExprId {
        const expr_id = if (self.meta_id_counter) |counter| blk: {
            const meta_id = counter.*;
            counter.* += 1;
            break :blk try theorem.addMetaPlaceholderWithMetaId(sort_name, meta_id);
        } else try theorem.addMetaPlaceholderResolved(sort_name);
        const placeholder_id = switch (theorem.interner.node(expr_id).*) {
            .placeholder => |id| id,
            else => unreachable,
        };
        try self.metas.put(self.allocator, placeholder_id, .{
            .sort_name = sort_name,
            .allowed_deps = allowed_deps,
            .kind = kind,
        });
        try self.trail.append(self.allocator, .{ .minted = placeholder_id });
        switch (kind) {
            .wildcard => self.stats.wildcard_created += 1,
            .existential => self.stats.existential_created += 1,
            .universal => self.stats.universal_created += 1,
            .bound_choice => self.stats.bound_choice_created += 1,
        }
        return expr_id;
    }

    /// Register an *ancestor* meta — a `.meta`-class leaf carrying a stable
    /// `meta_id` that was minted in an enclosing open slot and threaded into
    /// this interner across a clone boundary (so it has a different local
    /// `PlaceholderId` here, but the same logical identity). Registering it by
    /// local pid makes the leaf bindable in this slot's store, so the leaf
    /// unification that forces it (e.g. `ax` unifying two members) can solve
    /// it; the value then flows up via the materialized conclusion. No-op if
    /// already registered or if the leaf carries no `meta_id`. Trailed, so it
    /// rolls back with the branch.
    pub fn registerAncestorMeta(
        self: *MetaStore,
        theorem: *const TheoremContext,
        expr_id: ExprId,
    ) !void {
        const pid = switch (theorem.interner.node(expr_id).*) {
            .placeholder => |id| id,
            else => return,
        };
        if (self.metas.contains(pid)) return;
        const ph_info = theorem.placeholderInfo(pid) orelse return;
        if (ph_info.meta_id == null) return;
        try self.putRegistration(pid, ph_info.sort_name, true);
    }

    /// Shared registration body for `registerAncestorMeta` / `registerLocalMeta`:
    /// record the leaf as a fully-dep-permitted existential meta and trail it for
    /// rollback. Callers apply their own eligibility guard and the
    /// already-registered short-circuit first.
    fn putRegistration(
        self: *MetaStore,
        pid: PlaceholderId,
        sort_name: []const u8,
        ancestor: bool,
    ) !void {
        try self.metas.put(self.allocator, pid, .{
            .sort_name = sort_name,
            .allowed_deps = std.math.maxInt(u55),
            .kind = .existential,
            .ancestor = ancestor,
        });
        try self.trail.append(self.allocator, .{ .minted = pid });
    }

    /// Register an existing `.meta`-class leaf by its local `PlaceholderId` so
    /// this store will unify it. `solveCorrespondence` keys on `info(pid) != null`
    /// to decide whether a placeholder is a bindable meta, so a seed meta minted
    /// at candidate-creation time (before any store exists) is inert until a
    /// store registers it here. Used by the eliminator reconciliation seed: an
    /// ephemeral store registers the bindings' seed metas, solves them against a
    /// matched ref, then derefs the result back into the bindings. Unlike
    /// `registerAncestorMeta` no `meta_id` is required (the leaf is local to this
    /// interner). No-op on a non-placeholder or a standard (non-meta) leaf, or
    /// when already registered. Trailed, so it rolls back with the branch.
    pub fn registerLocalMeta(
        self: *MetaStore,
        theorem: *const TheoremContext,
        expr_id: ExprId,
    ) !void {
        const pid = switch (theorem.interner.node(expr_id).*) {
            .placeholder => |id| id,
            else => return,
        };
        if (self.metas.contains(pid)) return;
        const ph_info = theorem.placeholderInfo(pid) orelse return;
        if (ph_info.class != .meta) return;
        try self.putRegistration(pid, ph_info.sort_name, false);
    }

    /// True if `expr` mentions an ancestor meta (solved or not). Used to find
    /// the binders whose explicit rendering carries a leaf-solved ancestor
    /// witness back to the slot that minted it.
    pub fn exprMentionsAncestor(
        self: *const MetaStore,
        theorem: *const TheoremContext,
        expr: ExprId,
    ) bool {
        return switch (theorem.interner.node(expr).*) {
            .variable => false,
            .placeholder => |pid| if (self.metas.get(pid)) |m| m.ancestor else false,
            .app => |app| blk: {
                for (app.args) |arg| {
                    if (self.exprMentionsAncestor(theorem, arg)) break :blk true;
                }
                break :blk false;
            },
        };
    }

    /// The store's meta id for `expr_id`, or null when the expression is not
    /// a registered meta leaf (including ordinary standard placeholders).
    pub fn metaIdOf(
        self: *const MetaStore,
        theorem: *const TheoremContext,
        expr_id: ExprId,
    ) ?PlaceholderId {
        return switch (theorem.interner.node(expr_id).*) {
            .placeholder => |id| if (self.metas.contains(id)) id else null,
            .variable, .app => null,
        };
    }

    pub fn info(self: *const MetaStore, meta_id: PlaceholderId) ?MetaInfo {
        return self.metas.get(meta_id);
    }

    pub fn lookup(self: *const MetaStore, meta_id: PlaceholderId) ?ExprId {
        return self.assignments.get(meta_id);
    }

    /// Dereference `expr_id` through the current assignments: every solved
    /// meta leaf is replaced (recursively) by its assigned value; unsolved
    /// metas and ordinary leaves pass through. Returns the input id when
    /// nothing changed, so hash-consed identity is preserved on the solved
    /// path.
    pub fn deref(
        self: *const MetaStore,
        theorem: *TheoremContext,
        expr_id: ExprId,
    ) !ExprId {
        ExprModule.work_ticks_walk +%= 1;
        const node = theorem.interner.node(expr_id).*;
        switch (node) {
            .variable => return expr_id,
            .placeholder => |id| {
                const value = self.assignments.get(id) orelse return expr_id;
                return try self.deref(theorem, value);
            },
            .app => |app| {
                var changed = false;
                const args = try theorem.allocator.alloc(ExprId, app.args.len);
                for (app.args, 0..) |arg, idx| {
                    args[idx] = self.deref(theorem, arg) catch |err| {
                        theorem.allocator.free(args);
                        return err;
                    };
                    if (args[idx] != arg) changed = true;
                }
                if (!changed) {
                    theorem.allocator.free(args);
                    return expr_id;
                }
                return try theorem.interner.internAppOwned(app.term_id, args);
            },
        }
    }

    /// Assign `value` to a meta. Validates kind/phase, single assignment,
    /// occurs check, sort, and the allowed-dependency constraint. Sort and
    /// dep checks are skipped when the value's leaf info is unavailable —
    /// search stays a proposer; `tryCandidate` revalidates every accepted
    /// proof.
    pub fn assign(
        self: *MetaStore,
        theorem: *TheoremContext,
        meta_id: PlaceholderId,
        value: ExprId,
    ) !void {
        const meta = self.metas.get(meta_id) orelse return error.UnknownMeta;
        switch (meta.kind) {
            .wildcard => return error.WildcardNeverBinds,
            .universal => if (!self.universal_use_open) {
                return error.UniversalWrongPhase;
            },
            .existential, .bound_choice => {},
        }
        if (self.assignments.contains(meta_id)) {
            return error.MetaAlreadyAssigned;
        }
        const resolved = try self.deref(theorem, value);
        if (self.occursIn(theorem, meta_id, resolved)) {
            return error.OccursCheckFailed;
        }
        if (BindingValidation.currentExprInfo(
            self.env,
            theorem,
            resolved,
        )) |value_info| {
            if (!std.mem.eql(u8, value_info.sort_name, meta.sort_name)) {
                return error.SortMismatch;
            }
            if ((value_info.deps & ~meta.allowed_deps) != 0) {
                return error.DependencyViolation;
            }
        } else |_| {}
        try self.trail.append(self.allocator, .{ .assigned = meta_id });
        errdefer _ = self.trail.pop();
        try self.assignments.put(self.allocator, meta_id, resolved);
        self.stats.assignments += 1;
    }

    /// Whether `meta_id` occurs in `expr_id`. The expression must already be
    /// dereferenced through current assignments.
    fn occursIn(
        self: *const MetaStore,
        theorem: *const TheoremContext,
        meta_id: PlaceholderId,
        expr_id: ExprId,
    ) bool {
        return switch (theorem.interner.node(expr_id).*) {
            .variable => false,
            .placeholder => |id| id == meta_id,
            .app => |app| blk: {
                for (app.args) |arg| {
                    if (self.occursIn(theorem, meta_id, arg)) break :blk true;
                }
                break :blk false;
            },
        };
    }

    /// Trail mark for branch-local rollback. Pair with `rollbackTo` at the
    /// same site as the assembly backtrack (`rollbackOneHypMatch`).
    pub fn mark(self: *const MetaStore) usize {
        return self.trail.items.len;
    }

    /// Undo every mint and assignment recorded after `trail_mark`. A rolled-
    /// back mint leaves a dead leaf in the interner (it is append-only);
    /// nothing may reference that leaf afterwards — the expressions that
    /// mentioned it are abandoned by the same backtrack.
    pub fn rollbackTo(self: *MetaStore, trail_mark: usize) void {
        if (trail_mark >= self.trail.items.len) return;
        var idx = self.trail.items.len;
        while (idx > trail_mark) : (idx -= 1) {
            switch (self.trail.items[idx - 1]) {
                .minted => |id| {
                    _ = self.assignments.remove(id);
                    _ = self.metas.remove(id);
                },
                .assigned => |id| _ = self.assignments.remove(id),
            }
        }
        self.trail.shrinkRetainingCapacity(trail_mark);
        self.stats.rollbacks += 1;
    }

    /// Open/close the derived-ref use-time window in which universal metas
    /// may be assigned (Stage 7's transient-assignment discipline).
    pub fn openUniversalUse(self: *MetaStore) void {
        self.universal_use_open = true;
    }

    pub fn closeUniversalUse(self: *MetaStore) void {
        self.universal_use_open = false;
    }

    /// True when no unsolved meta is reachable from `expr_id` (through
    /// current assignments). Ordinary standard placeholders are not metas
    /// and do not count; the emission leakage guard covers those.
    pub fn isFullySolved(
        self: *const MetaStore,
        theorem: *const TheoremContext,
        expr_id: ExprId,
    ) bool {
        return !self.hasUnsolvedMeta(theorem, expr_id);
    }

    fn hasUnsolvedMeta(
        self: *const MetaStore,
        theorem: *const TheoremContext,
        expr_id: ExprId,
    ) bool {
        ExprModule.work_ticks_walk +%= 1;
        return switch (theorem.interner.node(expr_id).*) {
            .variable => false,
            .placeholder => |id| blk: {
                if (!self.metas.contains(id)) break :blk false;
                if (self.assignments.get(id)) |value| {
                    break :blk self.hasUnsolvedMeta(theorem, value);
                }
                break :blk true;
            },
            .app => |app| blk: {
                for (app.args) |arg| {
                    if (self.hasUnsolvedMeta(theorem, arg)) break :blk true;
                }
                break :blk false;
            },
        };
    }

    /// Fully dereference `expr_id`; error if any unsolved meta remains
    /// (wildcards included — they may never reach a rendered expression).
    pub fn materialize(
        self: *const MetaStore,
        theorem: *TheoremContext,
        expr_id: ExprId,
    ) !ExprId {
        const resolved = try self.deref(theorem, expr_id);
        if (self.hasUnsolvedMeta(theorem, resolved)) {
            return error.UnsolvedMeta;
        }
        return resolved;
    }

    /// Collect the unsolved metas reachable from `expr_id`, each reported
    /// once, for diagnostics before validation or rendering.
    pub fn collectUnsolved(
        self: *const MetaStore,
        theorem: *const TheoremContext,
        expr_id: ExprId,
        out: *std.ArrayListUnmanaged(PlaceholderId),
    ) !void {
        switch (theorem.interner.node(expr_id).*) {
            .variable => {},
            .placeholder => |id| {
                if (!self.metas.contains(id)) return;
                if (self.assignments.get(id)) |value| {
                    try self.collectUnsolved(theorem, value, out);
                    return;
                }
                for (out.items) |seen| {
                    if (seen == id) return;
                }
                try out.append(self.allocator, id);
            },
            .app => |app| {
                for (app.args) |arg| {
                    try self.collectUnsolved(theorem, arg, out);
                }
            },
        }
    }

    /// Debug chokepoint guard: panics in safe builds when a live meta is
    /// reachable from `expr_id`. Wired at the solved-only chokepoints
    /// (`tryCandidate` entry, generation-hook boundary, render entry) in
    /// Stage 4; the kind-aware leakage guard remains the hard backstop.
    pub fn assertNoLiveMeta(
        self: *const MetaStore,
        theorem: *const TheoremContext,
        expr_id: ExprId,
    ) void {
        if (std.debug.runtime_safety) {
            if (self.hasUnsolvedMeta(theorem, expr_id)) {
                @panic("live search meta reached a solved-only chokepoint");
            }
        }
    }
};

/// Store-free debug guard for chokepoints that have no store in scope: no
/// meta-class leaf at all may appear here, solved or not (post-
/// materialization surfaces).
pub fn assertNoMetaLeaf(
    theorem: *const TheoremContext,
    expr_id: ExprId,
) void {
    if (!std.debug.runtime_safety) return;
    switch (theorem.interner.node(expr_id).*) {
        .variable => {},
        .placeholder => |id| switch (theorem.placeholderClass(id)) {
            .standard => {},
            .meta => @panic("meta leaf reached a meta-free chokepoint"),
        },
        .app => |app| {
            for (app.args) |arg| {
                assertNoMetaLeaf(theorem, arg);
            }
        },
    }
}

// --- tests ---------------------------------------------------------------

const TermDecl = @import("../../env.zig").TermDecl;

fn appendTerm(env: *GlobalEnv, name: []const u8, ret_sort: []const u8) !u32 {
    const id: u32 = @intCast(env.terms.items.len);
    try env.terms.append(env.allocator, TermDecl{
        .name = name,
        .args = &.{},
        .arg_names = &.{},
        .dummy_args = &.{},
        .dummy_names = &.{},
        .ret_sort_name = ret_sort,
        .is_def = false,
        .body = null,
    });
    try env.term_names.put(name, id);
    return id;
}

const TestSetup = struct {
    arena: std.heap.ArenaAllocator,
    env: GlobalEnv,
    theorem: TheoremContext,
    store: MetaStore,

    fn init() !*TestSetup {
        const self = try std.testing.allocator.create(TestSetup);
        self.arena = std.heap.ArenaAllocator.init(std.testing.allocator);
        self.env = GlobalEnv.init(self.arena.allocator());
        self.theorem = TheoremContext.init(std.testing.allocator);
        self.store = MetaStore.init(std.testing.allocator, &self.env);
        return self;
    }

    fn deinit(self: *TestSetup) void {
        self.store.deinit();
        self.theorem.deinit();
        self.arena.deinit();
        std.testing.allocator.destroy(self);
    }
};

test "create existential meta consumes no dep bit" {
    var setup = try TestSetup.init();
    defer setup.deinit();
    const theorem = &setup.theorem;

    const dep_watermark = theorem.next_placeholder_dep;
    const meta = try setup.store.mint(theorem, "obj", 0, .existential);

    const meta_id = setup.store.metaIdOf(theorem, meta) orelse
        return error.ExpectedMeta;
    const meta_info = setup.store.info(meta_id) orelse
        return error.ExpectedMetaInfo;
    try std.testing.expectEqual(MetaKind.existential, meta_info.kind);
    try std.testing.expectEqualStrings("obj", meta_info.sort_name);
    // Dep-free minting: the shared u55 dep space is untouched, and the
    // interner-side info is marked as a meta-class placeholder.
    try std.testing.expectEqual(dep_watermark, theorem.next_placeholder_dep);
    try std.testing.expectEqual(
        ExprModule.PlaceholderClass.meta,
        theorem.theorem_placeholders.items[meta_id].class,
    );
    try std.testing.expectEqual(
        @as(usize, 1),
        setup.store.stats.existential_created,
    );
}

test "standard placeholders are not metas" {
    var setup = try TestSetup.init();
    defer setup.deinit();

    const standard = try setup.theorem.addPlaceholderResolved("obj");
    try std.testing.expect(
        setup.store.metaIdOf(&setup.theorem, standard) == null,
    );
    // And the two minting paths share one id space without colliding.
    const meta = try setup.store.mint(&setup.theorem, "obj", 0, .existential);
    try std.testing.expect(standard != meta);
}

test "assign and dereference" {
    var setup = try TestSetup.init();
    defer setup.deinit();
    const theorem = &setup.theorem;

    const f = try appendTerm(&setup.env, "f", "obj");
    const c = try appendTerm(&setup.env, "c", "obj");
    const value = try theorem.interner.internApp(c, &.{});

    const meta = try setup.store.mint(theorem, "obj", 0, .existential);
    const meta_id = setup.store.metaIdOf(theorem, meta).?;
    const wrapped = try theorem.interner.internApp(f, &.{meta});

    try std.testing.expect(!setup.store.isFullySolved(theorem, wrapped));
    try setup.store.assign(theorem, meta_id, value);

    const expected = try theorem.interner.internApp(f, &.{value});
    try std.testing.expectEqual(
        expected,
        try setup.store.deref(theorem, wrapped),
    );
    try std.testing.expect(setup.store.isFullySolved(theorem, wrapped));
    try std.testing.expectEqual(
        expected,
        try setup.store.materialize(theorem, wrapped),
    );
    try std.testing.expectEqual(@as(usize, 1), setup.store.stats.assignments);
}

test "rollback to a mark" {
    var setup = try TestSetup.init();
    defer setup.deinit();
    const theorem = &setup.theorem;

    const c = try appendTerm(&setup.env, "c", "obj");
    const value = try theorem.interner.internApp(c, &.{});

    const first = try setup.store.mint(theorem, "obj", 0, .existential);
    const first_id = setup.store.metaIdOf(theorem, first).?;
    try setup.store.assign(theorem, first_id, value);

    const trail_mark = setup.store.mark();
    const second = try setup.store.mint(theorem, "obj", 0, .existential);
    const second_id = setup.store.metaIdOf(theorem, second).?;
    try setup.store.assign(theorem, second_id, value);

    setup.store.rollbackTo(trail_mark);

    // The second meta's mint and assignment are gone; the first survives.
    try std.testing.expect(setup.store.metaIdOf(theorem, second) == null);
    try std.testing.expect(setup.store.lookup(second_id) == null);
    try std.testing.expectEqual(value, setup.store.lookup(first_id).?);
    try std.testing.expectEqual(@as(usize, 1), setup.store.stats.rollbacks);
}

test "repeated meta occurrences share the same assignment" {
    var setup = try TestSetup.init();
    defer setup.deinit();
    const theorem = &setup.theorem;

    const pair = try appendTerm(&setup.env, "pair", "obj");
    const c = try appendTerm(&setup.env, "c", "obj");
    const value = try theorem.interner.internApp(c, &.{});

    const meta = try setup.store.mint(theorem, "obj", 0, .existential);
    const meta_id = setup.store.metaIdOf(theorem, meta).?;
    // Hash-consing makes both occurrences the same leaf, so one assignment
    // covers both positions.
    const doubled = try theorem.interner.internApp(pair, &.{ meta, meta });

    try setup.store.assign(theorem, meta_id, value);
    const resolved = try setup.store.deref(theorem, doubled);
    const resolved_app = theorem.interner.node(resolved).*.app;
    try std.testing.expectEqual(value, resolved_app.args[0]);
    try std.testing.expectEqual(resolved_app.args[0], resolved_app.args[1]);

    // A second direct assignment is rejected; callers deref instead.
    try std.testing.expectError(
        error.MetaAlreadyAssigned,
        setup.store.assign(theorem, meta_id, value),
    );
}

test "occurs check rejects cyclic assignment" {
    var setup = try TestSetup.init();
    defer setup.deinit();
    const theorem = &setup.theorem;

    const f = try appendTerm(&setup.env, "f", "obj");
    const g = try appendTerm(&setup.env, "g", "obj");

    const meta = try setup.store.mint(theorem, "obj", 0, .existential);
    const meta_id = setup.store.metaIdOf(theorem, meta).?;
    const cyclic = try theorem.interner.internApp(f, &.{meta});
    try std.testing.expectError(
        error.OccursCheckFailed,
        setup.store.assign(theorem, meta_id, cyclic),
    );

    // Indirect cycle through a second meta.
    const other = try setup.store.mint(theorem, "obj", 0, .existential);
    const other_id = setup.store.metaIdOf(theorem, other).?;
    try setup.store.assign(theorem, meta_id, try theorem.interner.internApp(
        f,
        &.{other},
    ));
    try std.testing.expectError(
        error.OccursCheckFailed,
        setup.store.assign(theorem, other_id, try theorem.interner.internApp(
            g,
            &.{meta},
        )),
    );
}

test "sort mismatch rejects assignment" {
    var setup = try TestSetup.init();
    defer setup.deinit();
    const theorem = &setup.theorem;

    const w = try appendTerm(&setup.env, "w", "wff");
    const wff_value = try theorem.interner.internApp(w, &.{});

    const meta = try setup.store.mint(theorem, "obj", 0, .existential);
    const meta_id = setup.store.metaIdOf(theorem, meta).?;
    try std.testing.expectError(
        error.SortMismatch,
        setup.store.assign(theorem, meta_id, wff_value),
    );
}

test "dependency violation rejects assignment" {
    var setup = try TestSetup.init();
    defer setup.deinit();
    const theorem = &setup.theorem;

    // A theorem-local dummy carries dep bit 1<<0.
    const dummy = try theorem.addDummyVarResolved("obj", 0);

    const closed = try setup.store.mint(theorem, "obj", 0, .existential);
    const closed_id = setup.store.metaIdOf(theorem, closed).?;
    try std.testing.expectError(
        error.DependencyViolation,
        setup.store.assign(theorem, closed_id, dummy),
    );

    // The same value is accepted when the constraint set permits the dep.
    const open = try setup.store.mint(theorem, "obj", 1, .existential);
    const open_id = setup.store.metaIdOf(theorem, open).?;
    try setup.store.assign(theorem, open_id, dummy);
}

test "wildcard metas never bind" {
    var setup = try TestSetup.init();
    defer setup.deinit();
    const theorem = &setup.theorem;

    const c = try appendTerm(&setup.env, "c", "obj");
    const value = try theorem.interner.internApp(c, &.{});

    const meta = try setup.store.mint(theorem, "obj", 0, .wildcard);
    const meta_id = setup.store.metaIdOf(theorem, meta).?;
    try std.testing.expectError(
        error.WildcardNeverBinds,
        setup.store.assign(theorem, meta_id, value),
    );
}

test "universal metas cannot be assigned in the wrong phase" {
    var setup = try TestSetup.init();
    defer setup.deinit();
    const theorem = &setup.theorem;

    const c = try appendTerm(&setup.env, "c", "obj");
    const value = try theorem.interner.internApp(c, &.{});

    const meta = try setup.store.mint(theorem, "obj", 0, .universal);
    const meta_id = setup.store.metaIdOf(theorem, meta).?;
    try std.testing.expectError(
        error.UniversalWrongPhase,
        setup.store.assign(theorem, meta_id, value),
    );

    // Inside a derived-ref use window the assignment is permitted, and the
    // use-time discipline rolls it back afterwards.
    setup.store.openUniversalUse();
    const trail_mark = setup.store.mark();
    try setup.store.assign(theorem, meta_id, value);
    try std.testing.expectEqual(value, setup.store.lookup(meta_id).?);
    setup.store.rollbackTo(trail_mark);
    setup.store.closeUniversalUse();
    try std.testing.expect(setup.store.lookup(meta_id) == null);
}

test "unsolved existential leakage is rejected" {
    var setup = try TestSetup.init();
    defer setup.deinit();
    const theorem = &setup.theorem;

    const f = try appendTerm(&setup.env, "f", "obj");
    const meta = try setup.store.mint(theorem, "obj", 0, .existential);
    const wrapped = try theorem.interner.internApp(f, &.{meta});

    try std.testing.expectError(
        error.UnsolvedMeta,
        setup.store.materialize(theorem, wrapped),
    );

    var unsolved: std.ArrayListUnmanaged(PlaceholderId) = .{};
    defer unsolved.deinit(std.testing.allocator);
    try setup.store.collectUnsolved(theorem, wrapped, &unsolved);
    try std.testing.expectEqual(@as(usize, 1), unsolved.items.len);
    try std.testing.expectEqual(
        setup.store.metaIdOf(theorem, meta).?,
        unsolved.items[0],
    );
}
