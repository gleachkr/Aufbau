//! Search metavariables: the substitution (`Sigma`) and the store over it
//! (`MetaStore`), used for forward saturation's universal metas and
//! ephemeral matches.
//!
//! A search meta is represented in the interner as an ordinary placeholder
//! leaf; the store maps its `PlaceholderId` to a key in the substitution, and
//! the assignment state lives there, never in the interner node. That keeps interning, hashing, and the
//! COW theorem clone working unchanged, and lets the existing emission
//! leakage guard cover unsolved metas (kind-aware via
//! `PlaceholderClass.meta`).
//!
//! Lifetime/rollback discipline:
//! - a use marks the store and rolls its assignments back afterwards;
//! - metas are fully solved before every `tryCandidate` call, so validation
//!   never sees a live meta;
//! - a meta leaf is always dereferenced through the store before any
//!   structural match (the matching-site invariant).

const std = @import("std");
const ArenaAllocator = @import("../../arena_allocator.zig").ArenaAllocator;
const ExprModule = @import("../../expr.zig");
const ExprId = ExprModule.ExprId;
const PlaceholderId = ExprModule.PlaceholderId;
const TheoremContext = ExprModule.TheoremContext;
const GlobalEnv = @import("../../env.zig").GlobalEnv;

/// The search leaf kinds; defined with the placeholder factory that mints
/// them.
pub const MetaKind = @import("../inference/open_terms.zig").MetaKind;

pub const MetaInfo = struct {
    sort_name: []const u8,
    /// Allowed-dependency constraint set: the theorem dep bits an assignment
    /// is permitted to mention. NOT an allocated dep bit — meta leaves are
    /// minted dep-free (`addMetaPlaceholderResolved`).
    allowed_deps: u55,
    kind: MetaKind,
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

/// A key into `Sigma`: a meta's stable `meta_id` (`PlaceholderInfo.meta_id`)
/// when the view mints it with one, else an alias from `alias_base` upward
/// that only the view holding it can reach.
pub const MetaKey = u64;
const alias_base: MetaKey = 1 << 63;

/// What `Sigma` records for one meta: its constraints and, once assigned, its
/// value (an `ExprId` in the interner of the view that assigned it).
pub const MetaEntry = struct {
    info: MetaInfo,
    value: ?ExprId = null,
};

/// One trail step: `entered` registered `key` under the view's `pid`,
/// `bound` assigned it. `view` is the view that made the step; only that
/// view may undo it.
pub const Step = struct {
    view: u32,
    key: MetaKey,
    pid: PlaceholderId,
    kind: enum { entered, bound },
};

/// A store's substitution: every meta's constraints and assignment, keyed
/// by `MetaKey`, with one trail, used strictly LIFO.
pub const Sigma = struct {
    allocator: std.mem.Allocator,
    entries: std.AutoHashMapUnmanaged(MetaKey, MetaEntry) = .empty,
    trail: std.ArrayListUnmanaged(Step) = .empty,
    next_alias: MetaKey = alias_base,

    pub fn init(allocator: std.mem.Allocator) Sigma {
        return .{ .allocator = allocator };
    }

    pub fn deinit(self: *Sigma) void {
        self.entries.deinit(self.allocator);
        self.trail.deinit(self.allocator);
        self.* = undefined;
    }

    fn takeAlias(self: *Sigma) MetaKey {
        const key = self.next_alias;
        self.next_alias += 1;
        return key;
    }
};

/// A view over its own `Sigma`: the interner-local map from a meta leaf's
/// `PlaceholderId` to its key, plus counters. Each meta it mints is keyed by
/// an alias.
pub const MetaStore = struct {
    allocator: std.mem.Allocator,
    env: *const GlobalEnv,
    own: Sigma,
    /// This view's id in its `Sigma`, stamped on every step it makes.
    id: u32 = 0,
    /// Trail length when the view was made; `deinit` undoes back to it.
    base: usize = 0,
    keys: std.AutoHashMapUnmanaged(PlaceholderId, MetaKey) = .empty,
    stats: MetaStats = .{},

    /// A store over its own private substitution.
    pub fn init(
        allocator: std.mem.Allocator,
        env: *const GlobalEnv,
    ) MetaStore {
        return .{ .allocator = allocator, .env = env, .own = Sigma.init(allocator) };
    }

    /// Undo this view's steps and free it.
    pub fn deinit(self: *MetaStore) void {
        self.undo(self.base);
        self.keys.deinit(self.allocator);
        self.own.deinit();
        self.* = undefined;
    }

    fn substitution(self: *MetaStore) *Sigma {
        return &self.own;
    }

    fn substitutionConst(self: *const MetaStore) *const Sigma {
        return &self.own;
    }

    fn entry(self: *const MetaStore, pid: PlaceholderId) ?MetaEntry {
        const key = self.keys.get(pid) orelse return null;
        return self.substitutionConst().entries.get(key).?;
    }

    /// The number of metas registered in this view.
    pub fn count(self: *const MetaStore) usize {
        return self.keys.count();
    }

    /// Mint a fresh meta leaf in `theorem`'s interner and register it.
    pub fn mint(
        self: *MetaStore,
        theorem: *TheoremContext,
        sort_name: []const u8,
        allowed_deps: u55,
        kind: MetaKind,
    ) !ExprId {
        std.debug.assert(kind != .bound_choice);
        const expr_id = try theorem.addMetaPlaceholderResolved(sort_name);
        const placeholder_id = switch (theorem.interner.node(expr_id).*) {
            .placeholder => |id| id,
            else => unreachable,
        };
        try self.enter(placeholder_id, self.own.takeAlias(), .{
            .sort_name = sort_name,
            .allowed_deps = allowed_deps,
            .kind = kind,
        });
        switch (kind) {
            .wildcard => self.stats.wildcard_created += 1,
            .existential => self.stats.existential_created += 1,
            .universal => self.stats.universal_created += 1,
            .bound_choice => self.stats.bound_choice_created += 1,
        }
        return expr_id;
    }

    /// Enter a new meta under `key` with the view's handle `pid`, trailed.
    fn enter(self: *MetaStore, pid: PlaceholderId, key: MetaKey, meta: MetaInfo) !void {
        const s = self.substitution();
        try s.trail.append(s.allocator, .{ .view = self.id, .key = key, .pid = pid, .kind = .entered });
        errdefer _ = s.trail.pop();
        try s.entries.put(s.allocator, key, .{ .info = meta });
        errdefer _ = s.entries.remove(key);
        try self.keys.put(self.allocator, pid, key);
    }

    pub fn info(self: *const MetaStore, meta_id: PlaceholderId) ?MetaInfo {
        return if (self.entry(meta_id)) |e| e.info else null;
    }

    pub fn lookup(self: *const MetaStore, meta_id: PlaceholderId) ?ExprId {
        return if (self.entry(meta_id)) |e| e.value else null;
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
                const value = self.lookup(id) orelse return expr_id;
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
                return theorem.interner.internAppOwned(app.term_id, args) catch |err| {
                    theorem.allocator.free(args);
                    return err;
                };
            },
        }
    }

    /// Whether `meta_id` occurs in `expr_id`. The expression must already be
    /// dereferenced through current assignments.
    pub fn occursIn(
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

    /// Trail mark for rollback. Pair with `rollbackTo`.
    pub fn mark(self: *const MetaStore) usize {
        return self.substitutionConst().trail.items.len;
    }

    /// Undo every mint and assignment recorded after `trail_mark`. A rolled-
    /// back mint leaves a dead leaf in the interner (it is append-only);
    /// nothing may reference that leaf afterwards — the expressions that
    /// mentioned it are abandoned by the same backtrack.
    pub fn rollbackTo(self: *MetaStore, trail_mark: usize) void {
        if (trail_mark >= self.mark()) return;
        self.undo(trail_mark);
        self.stats.rollbacks += 1;
    }

    fn undo(self: *MetaStore, trail_mark: usize) void {
        const s = self.substitution();
        while (s.trail.items.len > trail_mark) {
            const step = s.trail.pop().?;
            std.debug.assert(step.view == self.id);
            switch (step.kind) {
                .entered => {
                    _ = s.entries.remove(step.key);
                    _ = self.keys.remove(step.pid);
                },
                .bound => s.entries.getPtr(step.key).?.value = null,
            }
        }
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
                const e = self.entry(id) orelse break :blk false;
                if (e.value) |value| {
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

    /// Collect the unsolved metas reachable from `expr_id`, each reported
    /// once, for diagnostics before validation or rendering. A shared app
    /// node is visited once.
    pub fn collectUnsolved(
        self: *const MetaStore,
        theorem: *const TheoremContext,
        expr_id: ExprId,
        out: *std.ArrayListUnmanaged(PlaceholderId),
    ) !void {
        var visited: TheoremContext.DagMemo(void) = .{};
        defer visited.deinit(self.allocator);
        try self.collectUnsolvedIn(theorem, &visited, expr_id, out);
    }

    fn collectUnsolvedIn(
        self: *const MetaStore,
        theorem: *const TheoremContext,
        visited: *TheoremContext.DagMemo(void),
        expr_id: ExprId,
        out: *std.ArrayListUnmanaged(PlaceholderId),
    ) !void {
        switch (theorem.interner.node(expr_id).*) {
            .variable => {},
            .placeholder => |id| {
                const e = self.entry(id) orelse return;
                if (e.value) |value| {
                    try self.collectUnsolvedIn(theorem, visited, value, out);
                    return;
                }
                for (out.items) |seen| {
                    if (seen == id) return;
                }
                try out.append(self.allocator, id);
            },
            .app => |app| {
                if (visited.get(expr_id) != null) return;
                for (app.args) |arg| {
                    try self.collectUnsolvedIn(theorem, visited, arg, out);
                }
                try visited.put(self.allocator, expr_id, {});
            },
        }
    }
};

// --- tests ---------------------------------------------------------------
