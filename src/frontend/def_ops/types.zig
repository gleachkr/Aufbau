const std = @import("std");
const ExprId = @import("../expr.zig").ExprId;

pub const ConversionPlan = union(enum) {
    refl,
    unfold_lhs: struct {
        witness: ExprId,
        next: *const ConversionPlan,
    },
    unfold_rhs: struct {
        witness: ExprId,
        next: *const ConversionPlan,
    },
    cong: struct {
        children: []const *const ConversionPlan,
    },
};

pub const SymbolicDummyInfo = struct {
    sort_name: []const u8,
    bound: bool,
};

pub const SymbolicExpr = union(enum) {
    binder: usize,
    fixed: ExprId,
    dummy: usize,
    app: App,

    pub const App = struct {
        term_id: u32,
        args: []const *const SymbolicExpr,
        /// Cached structural hash of this whole app subtree (mixes `term_id`,
        /// arity, and each child's structural hash). Populated once at
        /// construction (`allocSymbolic`) so search-memo keys are O(1) hash
        /// reads instead of O(tree-size) walks — the dominant worst-case
        /// `auto?` latency lever on def-unfold-heavy theories (church, etc.).
        hash: u64 = 0,
    };
};

/// Cheap integer hash mix (splitmix64-style finalize). No streaming-hasher
/// init/finalize overhead, which matters because this runs per node and, via
/// the session-state hashers, per memo probe.
pub inline fn mixHash(h: u64, v: u64) u64 {
    var x = (h ^ v) *% 0x9E3779B97F4A7C15;
    x ^= x >> 29;
    return x;
}

/// Cheap content hash of a short byte string via `mixHash`. Used for the sort
/// names embedded in `SymbolicDummyInfo` when hashing session state.
pub fn mixHashBytes(h: u64, bytes: []const u8) u64 {
    var acc = mixHash(h, bytes.len);
    for (bytes) |b| acc = mixHash(acc, b);
    return acc;
}

/// O(1) structural hash of a node: scalars hash inline; an `app` returns its
/// cached `hash`. Requires app caches to be populated (see `allocSymbolic`).
pub fn symbolicHash(node: *const SymbolicExpr) u64 {
    return switch (node.*) {
        .binder => |idx| mixHash(2, idx),
        .fixed => |expr_id| mixHash(3, expr_id),
        .dummy => |slot| mixHash(4, slot),
        .app => |app| app.hash,
    };
}

/// Compute an app node's structural hash from its children's structural hashes
/// (which, for app children, are themselves cached → O(arity) per node).
pub fn computeAppHash(term_id: u32, args: []const *const SymbolicExpr) u64 {
    var h = mixHash(5, term_id);
    h = mixHash(h, args.len);
    for (args) |arg| h = mixHash(h, symbolicHash(arg));
    return h;
}

pub const BindingMode = enum {
    exact,
    transparent,
    normalized,
};

pub const BindingSeed = union(enum) {
    none,
    exact: ExprId,
    semantic: struct {
        expr_id: ExprId,
        mode: BindingMode,
    },
    /// Carry a pre-built BoundValue (possibly symbolic) from one session
    /// into another without collapsing it to a concrete ExprId first.
    bound: BoundValue,

    pub fn fromOptionalBindings(
        allocator: std.mem.Allocator,
        bindings: []const ?ExprId,
    ) ![]BindingSeed {
        const seeds = try allocator.alloc(BindingSeed, bindings.len);
        for (bindings, 0..) |binding, idx| {
            seeds[idx] = if (binding) |expr_id|
                .{ .exact = expr_id }
            else
                .none;
        }
        return seeds;
    }
};

pub const ConcreteBinding = struct {
    raw: ExprId,
    repr: *const SymbolicExpr,
    mode: BindingMode,
};

pub const SymbolicBinding = struct {
    expr: *const SymbolicExpr,
    mode: BindingMode,
};

pub const BoundValue = union(enum) {
    concrete: ConcreteBinding,
    symbolic: SymbolicBinding,
};

pub const UnresolvedDummyRoot = struct {
    root_slot: usize,
    sort_name: []const u8,
    bound: bool,
};

pub const MaterializedDummyAssignment = struct {
    root_slot: usize,
    expr_id: ExprId,
};

/// Caller-owned policy for grounding unresolved hidden dummy roots. The
/// callback may depend on mutable compiler state, so queries using it must not
/// populate the pure def-instantiation caches.
pub const HiddenWitnessProvider = struct {
    context: *anyopaque,
    provideFn: *const fn (
        context: *anyopaque,
        allocator: std.mem.Allocator,
        roots: []const UnresolvedDummyRoot,
        extra_used_deps: u55,
    ) anyerror!?[]MaterializedDummyAssignment,

    pub fn provide(
        self: HiddenWitnessProvider,
        allocator: std.mem.Allocator,
        roots: []const UnresolvedDummyRoot,
        extra_used_deps: u55,
    ) anyerror!?[]MaterializedDummyAssignment {
        return try self.provideFn(
            self.context,
            allocator,
            roots,
            extra_used_deps,
        );
    }
};

pub const WitnessMap = std.AutoHashMapUnmanaged(usize, ExprId);
pub const WitnessSlotMap = std.AutoHashMapUnmanaged(ExprId, usize);
pub const DummyAliasMap = std.AutoHashMapUnmanaged(usize, usize);
pub const ProvisionalWitnessInfoMap = std.AutoHashMapUnmanaged(
    ExprId,
    SymbolicDummyInfo,
);
pub const MaterializedWitnessInfoMap = std.AutoHashMapUnmanaged(
    ExprId,
    SymbolicDummyInfo,
);
pub const RepresentativeCache = std.AutoHashMapUnmanaged(
    ExprId,
    *const SymbolicExpr,
);

pub const MatchSeedState = struct {
    /// Owned: `.bound` seeds hold deep-cloned `SymbolicExpr` trees (see
    /// `exportMatchSeedState`), NOT pointers into a session's scratch arena.
    /// A seed state may outlive the `def_ops.Context` it was exported from,
    /// so it can never alias scratch memory.
    bindings: []BindingSeed,
    symbolic_dummy_infos: []SymbolicDummyInfo,
    witnesses: WitnessMap = .{},
    materialized_witnesses: WitnessMap = .{},
    materialized_witness_slots: WitnessSlotMap = .{},
    dummy_aliases: DummyAliasMap = .{},
    provisional_witness_infos: ProvisionalWitnessInfoMap = .{},
    materialized_witness_infos: MaterializedWitnessInfoMap = .{},

    /// Replace one owned seed, freeing the previous value's cloned trees.
    /// A seed state is dead data, not live session state — no trail applies.
    /// Mutating it affects only sessions built from it afterwards
    /// (`initFromSeedState` / `restoreFromSeedState`); a session already
    /// seeded from it does NOT observe the change.
    pub fn replaceSeed(
        self: *MatchSeedState,
        allocator: std.mem.Allocator,
        idx: usize,
        seed: BindingSeed,
    ) void {
        freeBindingSeedOwned(allocator, self.bindings[idx]);
        self.bindings[idx] = seed;
    }

    pub fn deinit(self: *MatchSeedState, allocator: std.mem.Allocator) void {
        for (self.bindings) |seed| freeBindingSeedOwned(allocator, seed);
        allocator.free(self.bindings);
        allocator.free(self.symbolic_dummy_infos);
        self.witnesses.deinit(allocator);
        self.materialized_witnesses.deinit(allocator);
        self.materialized_witness_slots.deinit(allocator);
        self.dummy_aliases.deinit(allocator);
        self.provisional_witness_infos.deinit(allocator);
        self.materialized_witness_infos.deinit(allocator);
    }
};

/// Deep-clone a `SymbolicExpr` tree with `allocator`. Sessions allocate these
/// trees in a per-context scratch arena that dies with the context; cloning is
/// how a `BoundValue` legitimately crosses a context boundary (export to a
/// `MatchSeedState`) or enters a new session's arena (seed consumption).
pub fn cloneSymbolicExpr(
    allocator: std.mem.Allocator,
    expr: *const SymbolicExpr,
) anyerror!*const SymbolicExpr {
    const node = try allocator.create(SymbolicExpr);
    errdefer allocator.destroy(node);
    switch (expr.*) {
        .binder, .fixed, .dummy => node.* = expr.*,
        .app => |app| {
            const args = try allocator.alloc(
                *const SymbolicExpr,
                app.args.len,
            );
            var cloned: usize = 0;
            errdefer {
                for (args[0..cloned]) |arg| freeSymbolicExpr(allocator, arg);
                allocator.free(args);
            }
            for (app.args, 0..) |arg, idx| {
                args[idx] = try cloneSymbolicExpr(allocator, arg);
                cloned = idx + 1;
            }
            // Structural hash is clone-invariant (same structure → same
            // child hashes), so carry the cached value across the copy.
            node.* = .{ .app = .{
                .term_id = app.term_id,
                .args = args,
                .hash = app.hash,
            } };
        },
    }
    return node;
}

/// Free a tree produced by `cloneSymbolicExpr`. Must never be called on
/// scratch-arena trees (those are reclaimed wholesale at context deinit).
pub fn freeSymbolicExpr(
    allocator: std.mem.Allocator,
    expr: *const SymbolicExpr,
) void {
    switch (expr.*) {
        .app => |app| {
            for (app.args) |arg| freeSymbolicExpr(allocator, arg);
            allocator.free(app.args);
        },
        .binder, .fixed, .dummy => {},
    }
    allocator.destroy(@constCast(expr));
}

pub fn cloneBoundValue(
    allocator: std.mem.Allocator,
    bound: BoundValue,
) anyerror!BoundValue {
    return switch (bound) {
        .concrete => |concrete| .{ .concrete = .{
            .raw = concrete.raw,
            .repr = try cloneSymbolicExpr(allocator, concrete.repr),
            .mode = concrete.mode,
        } },
        .symbolic => |symbolic| .{ .symbolic = .{
            .expr = try cloneSymbolicExpr(allocator, symbolic.expr),
            .mode = symbolic.mode,
        } },
    };
}

pub fn freeBoundValueOwned(
    allocator: std.mem.Allocator,
    bound: BoundValue,
) void {
    switch (bound) {
        .concrete => |concrete| freeSymbolicExpr(allocator, concrete.repr),
        .symbolic => |symbolic| freeSymbolicExpr(allocator, symbolic.expr),
    }
}

pub fn freeBindingSeedOwned(
    allocator: std.mem.Allocator,
    seed: BindingSeed,
) void {
    switch (seed) {
        .bound => |bound| freeBoundValueOwned(allocator, bound),
        .none, .exact, .semantic => {},
    }
}

pub const ConcreteVarInfo = struct {
    sort_name: []const u8,
    bound: bool,
};
