//! Egraph core for `conversion?` search: equality saturation over
//! `@conversion` rules with gated congruence closure.
//!
//! Follows the microegg architecture (arena union-find, canonicalize-on-add
//! hashcons, deferred wholesale rebuild, batched match-then-instantiate;
//! <https://pavpanchekha.com/blog/microegg.html>) with two deviations
//! documented in `docs/design_notes/conversion_egraph.md`:
//!
//! - Congruence unions are *gated*: rebuild merges congruent parents only
//!   when the head term has a `@congr` rule registered (`congr_heads`),
//!   because that rule is exactly the proof step extraction will emit.
//!   Nodes failing the gate stay in separate classes, so every union in the
//!   graph is extractable by construction.
//! - Bound-binder argument positions store the atom directly
//!   (`Child.bound`) and never enter union-find: MM0 bound binders are
//!   rigid atoms (no alpha), and the `@congr` lemmas require them
//!   identical on both sides.
//!
//! Every union records a justification edge (`unions`) for explanation
//! extraction. The whole structure lives for one search call and MUST be
//! allocated from a per-call arena: nothing here frees, and abandoned
//! buffers (canonicalization copies, the per-iteration class index) lean on
//! arena teardown.

const std = @import("std");
const TemplateExpr = @import("../../rules.zig").TemplateExpr;

pub const EClassId = u32;
pub const ENodeId = u32;

/// Opaque ground-atom key supplied by the driver (theorem vars, bound
/// binders, and dummies each map to a distinct leaf).
pub const LeafId = u32;

/// One argument position of an application node. Regular positions hold an
/// e-class; bound-binder positions hold the atom itself and are rigid.
pub const Child = union(enum) {
    class: EClassId,
    bound: LeafId,
};

pub const ENode = union(enum) {
    leaf: LeafId,
    app: App,
    /// An AC-policied operator application, interned as a flattened
    /// multiset: nested same-head applications splice into one node and
    /// members sort by canonical class root, so every reassociation and
    /// permutation of the same members IS one node. The associativity and
    /// commutativity laws contribute zero saturation work; extraction pays
    /// them back as explicit certificate chains (see
    /// `docs/design_notes/ac_representation.md`).
    bag: Bag,

    pub const App = struct {
        term_id: u32,
        children: []const Child,
    };

    pub const Bag = struct {
        term_id: u32,
        /// Multiset of member classes (duplicates preserved — idempotence
        /// and units stay ordinary rules), sorted by canonical root.
        /// Always at least two members.
        members: []const EClassId,
    };
};

/// A dependency restriction on one rule: the theorem's bound binder at
/// `bound_slot` may not occur in the instantiation of the term binder at
/// `term_slot` (its `deps` bit for that bound binder is unset). Slots are
/// rule binder indices.
pub const Restriction = struct {
    bound_slot: u32,
    term_slot: u32,
};

/// One enrolled `@conversion` orientation. `match_side` is e-matched;
/// `target_side` is instantiated over the resulting substitution and
/// unioned with the matched class. The caller guarantees `match_side` is an
/// application whose binders cover the target side (validated at
/// annotation time), and expands a `both` annotation into two rules.
pub const Rule = struct {
    /// Caller tag (the `@conversion` rule id); opaque to the core.
    rule_id: u32,
    /// True when this orientation runs the theorem right-to-left, so the
    /// lowering of a forward traversal needs the relation's `symm`.
    reversed: bool,
    match_side: TemplateExpr,
    target_side: TemplateExpr,
    num_binders: usize,
    /// Rule binder indices that are bound binders (instantiate to atoms).
    /// Both dep-gate halves key off this: distinctness across the slots,
    /// and the avoidance checks in `restrictions`.
    bound_slots: []const u32 = &.{},
    /// Dependency restrictions the verifier will enforce on every emitted
    /// instance of this rule. Shared by both orientations of a theorem.
    restrictions: []const Restriction = &.{},
};

/// Why two classes were unioned. Consumed by explanation extraction. The
/// two endpoint nodes must be members of the two classes passed to `merge`;
/// they anchor the explanation forest.
pub const Justification = union(enum) {
    rule: struct {
        /// Index into the rules slice passed to `saturate`.
        rule_slot: u32,
        /// The node whose class matched the rule's match side.
        from_node: ENodeId,
        /// A node of the instantiated target class (the instance node for
        /// an application target; the class's creating node for a bare
        /// binder target; the wrapped bag for an extension match).
        to_node: ENodeId,
        /// The substitution the match produced (indexed by rule binder).
        subst: []const ?Child,
        /// For an AC bag match that covered only a sub-multiset: the
        /// unmatched member classes rejoined around the rewrite target.
        extension: []const EClassId = &.{},
    },
    congruence: struct {
        left: ENodeId,
        right: ENodeId,
    },
    /// A ground union seeded by the driver: the reference-pool entry at
    /// `pool_index` is itself a proven `rel(lhs, rhs)` fact, so its two
    /// sides are one class. The seeded side terms ride along because the
    /// lowering cites the entry's exact formula — unlike a rule instance,
    /// which may anchor on any class representative.
    pool_equation: struct {
        pool_index: u32,
        lhs: *const Term,
        rhs: *const Term,
    },
};

fn justEndpoints(just: Justification) struct { a: ENodeId, b: ENodeId } {
    return switch (just) {
        .rule => |rule| .{ .a = rule.from_node, .b = rule.to_node },
        .congruence => |congr| .{ .a = congr.left, .b = congr.right },
        .pool_equation => |eq| .{ .a = eq.lhs.node, .b = eq.rhs.node },
    };
}

pub const UnionEdge = struct {
    a: EClassId,
    b: EClassId,
    just: Justification,
};

const ExplEdge = struct {
    to: ENodeId,
    just: Justification,
    /// True when the justification's semantic direction (endpoint a -> b)
    /// runs child -> parent along this link.
    forward: bool,
};

pub const SaturateOutcome = enum { saturated, iteration_capped, node_capped };

pub const SaturateStats = struct {
    outcome: SaturateOutcome,
    iterations: usize = 0,
    unions_applied: usize = 0,
    /// Matches refused by the dep gate this run. A nonzero count on a
    /// saturated miss means dependency constraints (not rule coverage)
    /// blocked at least one candidate union.
    dep_deferred: usize = 0,
    /// AC bag-match enumerations truncated by the per-match budget this
    /// run. A nonzero count on a saturated miss means the miss is NOT a
    /// forced negative — some assignments were never tried.
    ac_match_capped: usize = 0,
    /// Cyclic `bag_in_class` entries dropped by rebuild passes this run.
    /// Dropping keeps member lists finite but forfeits some congruence
    /// merges, so a nonzero count on a saturated miss means the miss is
    /// NOT a forced negative in the AC quotient.
    ac_cyclic_dropped: usize = 0,
};

pub const SaturateOptions = struct {
    max_iterations: usize = 16,
    max_nodes: usize = 10_000,
    /// Assignment-enumeration budget per top-level bag match (a rule
    /// against one bag node). Trips count in `ac_match_capped`.
    ac_match_budget: usize = 10_000,
};

const StoredNode = struct {
    node: ENode,
    class: EClassId,
};

const NodeCtx = struct {
    pub fn hash(_: NodeCtx, node: ENode) u32 {
        var h = std.hash.Wyhash.init(0);
        switch (node) {
            .leaf => |leaf| {
                h.update(&[1]u8{0});
                h.update(std.mem.asBytes(&leaf));
            },
            .app => |app| {
                h.update(&[1]u8{1});
                h.update(std.mem.asBytes(&app.term_id));
                for (app.children) |child| switch (child) {
                    .class => |id| {
                        h.update(&[1]u8{2});
                        h.update(std.mem.asBytes(&id));
                    },
                    .bound => |id| {
                        h.update(&[1]u8{3});
                        h.update(std.mem.asBytes(&id));
                    },
                };
            },
            .bag => |bag| {
                h.update(&[1]u8{4});
                h.update(std.mem.asBytes(&bag.term_id));
                for (bag.members) |member| {
                    h.update(std.mem.asBytes(&member));
                }
            },
        }
        return @truncate(h.final());
    }

    pub fn eql(_: NodeCtx, a: ENode, b: ENode, _: usize) bool {
        return nodeEql(a, b);
    }
};

fn nodeEql(a: ENode, b: ENode) bool {
    switch (a) {
        .leaf => |al| return b == .leaf and b.leaf == al,
        .app => |aa| {
            if (b != .app) return false;
            const ba = b.app;
            if (aa.term_id != ba.term_id) return false;
            if (aa.children.len != ba.children.len) return false;
            for (aa.children, ba.children) |ac, bc| {
                switch (ac) {
                    .class => |id| {
                        if (bc != .class or bc.class != id) return false;
                    },
                    .bound => |id| {
                        if (bc != .bound or bc.bound != id) return false;
                    },
                }
            }
            return true;
        },
        .bag => |ab| {
            if (b != .bag) return false;
            const bb = b.bag;
            if (ab.term_id != bb.term_id) return false;
            return std.mem.eql(EClassId, ab.members, bb.members);
        },
    }
}

const NodeMap = std.ArrayHashMapUnmanaged(ENode, ENodeId, NodeCtx, true);

pub const EGraph = struct {
    /// MUST be a per-call arena; see the module doc.
    allocator: std.mem.Allocator,
    /// Union-find over class ids; `parents[i] == i` marks a root. Classes
    /// are created only in `add` — rebuild reuses ids, never makesets.
    parents: std.ArrayListUnmanaged(EClassId) = .{},
    /// Append-only node store; `ENodeId` indexes stay stable across
    /// rebuilds (justifications reference them). Node contents are
    /// re-canonicalized in place — safe because bound children are rigid
    /// and class children only move within their class.
    nodes: std.ArrayListUnmanaged(StoredNode) = .{},
    /// Canonical node -> first node id with that shape. Maintained
    /// incrementally by `add`, reconstructed wholesale by `rebuild`.
    memo: NodeMap = .{},
    /// Leaf atom -> its class, for resolving a bound-position binding used
    /// in a regular (term) position.
    leaf_classes: std.AutoArrayHashMapUnmanaged(LeafId, EClassId) = .{},
    /// Head terms with a registered `@congr` rule: the congruence gate.
    congr_heads: std.AutoArrayHashMapUnmanaged(u32, void) = .{},
    /// Per-term bitmask of bound argument positions (bit i set = position i
    /// is a bound binder). Terms without an entry have no bound positions.
    bound_masks: std.AutoArrayHashMapUnmanaged(u32, u64) = .{},
    /// Binary heads certified assoc+comm: applications intern as sorted
    /// bags. The driver must only police heads that are congruence-gated
    /// (`congr_heads`) and have no bound positions — extraction lifts
    /// through bag positions with the head's `@congr` rule.
    ac_heads: std.AutoArrayHashMapUnmanaged(u32, void) = .{},
    /// `(term_id << 32 | class root) -> lowest bag node id` for splicing:
    /// a member class with an entry denotes a bag of the same head, so its
    /// members belong in the enclosing bag. Updated on add, refreshed
    /// wholesale each rebuild pass; staleness between passes only defers a
    /// splice to the next canonicalization (never corrupts one).
    bag_in_class: std.AutoArrayHashMapUnmanaged(u64, ENodeId) = .{},
    /// Remaining assignment budget for the current top-level bag match;
    /// reset per (rule, node) match call.
    ac_budget_remaining: usize = 0,
    /// Set when an enumeration actually early-outs on an empty budget —
    /// distinguishes truncation from an enumeration that completed on
    /// exactly its last budget unit. Reset per (rule, node) match call.
    ac_budget_hit: bool = false,
    /// Total bag-match budget trips (monotone; `saturate` reports deltas).
    ac_match_capped_total: usize = 0,
    /// Total cyclic bag-index entries dropped (monotone; `saturate`
    /// reports deltas).
    ac_cyclic_dropped_total: usize = 0,
    /// Proof-forest edges, one per effective union, in union order.
    unions: std.ArrayListUnmanaged(UnionEdge) = .{},
    /// Creating node of each class (parallel to `parents`). Every class is
    /// born in `add` with exactly one node, so this always names a member.
    class_node: std.ArrayListUnmanaged(ENodeId) = .{},
    /// Explanation forest (Nieuwenhuis–Oliveras): per-node parent link
    /// carrying the union justification. Distinct from the fast union-find:
    /// edges connect the *semantic endpoint nodes* of each union and are
    /// never path-compressed, only re-rooted.
    expl_parent: std.ArrayListUnmanaged(?ExplEdge) = .{},
    /// Root class -> member node ids; rebuilt per saturation iteration.
    class_index: std.AutoArrayHashMapUnmanaged(
        EClassId,
        std.ArrayListUnmanaged(ENodeId),
    ) = .{},

    pub fn init(allocator: std.mem.Allocator) EGraph {
        return .{ .allocator = allocator };
    }

    pub fn find(self: *const EGraph, id: EClassId) EClassId {
        var current = id;
        while (self.parents.items[current] != current) {
            current = self.parents.items[current];
        }
        return current;
    }

    /// Add a node (children canonicalized first) and return its class.
    /// Child slices are duplicated into the arena; callers may pass stack
    /// slices.
    pub fn add(self: *EGraph, node: ENode) !EClassId {
        return self.addWith(node, self.allocator);
    }

    /// `add` with canonicalization scratch supplied by the caller: the
    /// canonical shape's slices are duplicated into the egraph arena only
    /// when the node is actually inserted. Memo hits (the overwhelmingly
    /// common case on hot match paths) then cost the scratch arena
    /// nothing durable.
    fn addWith(
        self: *EGraph,
        node: ENode,
        scratch: std.mem.Allocator,
    ) !EClassId {
        const canon = try self.canonicalizeInto(node, null, scratch);
        if (self.memo.get(canon)) |node_id| {
            return self.find(self.nodes.items[node_id].class);
        }
        const owned = try self.ownNode(canon);
        const class: EClassId = @intCast(self.parents.items.len);
        try self.parents.append(self.allocator, class);
        const node_id: ENodeId = @intCast(self.nodes.items.len);
        try self.nodes.append(self.allocator, .{
            .node = owned,
            .class = class,
        });
        try self.class_node.append(self.allocator, node_id);
        try self.expl_parent.append(self.allocator, null);
        try self.memo.put(self.allocator, owned, node_id);
        if (owned == .leaf) {
            try self.leaf_classes.put(self.allocator, owned.leaf, class);
        }
        if (owned == .bag) {
            try self.bag_in_class.put(
                self.allocator,
                bagKey(owned.bag.term_id, class),
                node_id,
            );
        }
        return class;
    }

    /// Duplicate a (possibly scratch-backed) canonical node's slices into
    /// the egraph arena for permanent storage.
    fn ownNode(self: *EGraph, node: ENode) !ENode {
        return switch (node) {
            .leaf => node,
            .app => |app| .{ .app = .{
                .term_id = app.term_id,
                .children = try self.allocator.dupe(Child, app.children),
            } },
            .bag => |bag| .{ .bag = .{
                .term_id = bag.term_id,
                .members = try self.allocator.dupe(EClassId, bag.members),
            } },
        };
    }

    /// The node id of a shape already in the graph (canonicalized first).
    /// Drivers use this to anchor seed expressions for `explain`.
    pub fn lookupNode(self: *EGraph, node: ENode) !?ENodeId {
        const canon = try self.canonicalize(node);
        return self.memo.get(canon);
    }

    pub fn sameClass(self: *const EGraph, a: EClassId, b: EClassId) bool {
        return self.find(a) == self.find(b);
    }

    /// Number of live e-classes (union-find roots).
    pub fn classCount(self: *const EGraph) usize {
        var count: usize = 0;
        for (self.parents.items, 0..) |parent, idx| {
            if (parent == idx) count += 1;
        }
        return count;
    }

    /// Number of distinct canonical e-nodes (valid after a rebuild).
    pub fn eNodeCount(self: *const EGraph) usize {
        return self.memo.count();
    }

    /// Union two classes, recording the justification. Returns false when
    /// they were already one class (no edge recorded).
    pub fn merge(
        self: *EGraph,
        a: EClassId,
        b: EClassId,
        just: Justification,
    ) !bool {
        const root_a = self.find(a);
        const root_b = self.find(b);
        if (root_a == root_b) return false;
        self.parents.items[root_a] = root_b;
        try self.unions.append(self.allocator, .{
            .a = a,
            .b = b,
            .just = just,
        });
        const ends = justEndpoints(just);
        self.reRootExplanation(ends.a);
        self.expl_parent.items[ends.a] = .{
            .to = ends.b,
            .just = just,
            .forward = true,
        };
        return true;
    }

    /// Reverse the explanation-forest parent chain above `node` so it
    /// becomes the root of its tree (justifications flip direction).
    fn reRootExplanation(self: *EGraph, node: ENodeId) void {
        var current = node;
        var carried: ?ExplEdge = null;
        while (true) {
            const outgoing = self.expl_parent.items[current];
            self.expl_parent.items[current] = carried;
            const edge = outgoing orelse break;
            carried = .{
                .to = current,
                .just = edge.just,
                .forward = !edge.forward,
            };
            current = edge.to;
        }
    }

    /// Deferred congruence repair: re-canonicalize every stored node until
    /// fixpoint, unioning nodes that collapse to the same canonical shape
    /// when the congruence gate allows it. Reuses existing class ids
    /// (never makesets). Returns true when any union happened.
    pub fn rebuild(self: *EGraph) !bool {
        var any = false;
        while (true) {
            var changed = false;
            self.memo.clearRetainingCapacity();
            try self.refreshBagIndex();
            for (self.nodes.items, 0..) |*stored, idx| {
                stored.class = self.find(stored.class);
                stored.node = try self.canonicalizeWith(
                    stored.node,
                    stored.class,
                );
                const gop = try self.memo.getOrPut(
                    self.allocator,
                    stored.node,
                );
                if (!gop.found_existing) {
                    gop.value_ptr.* = @intCast(idx);
                    continue;
                }
                const other = self.nodes.items[gop.value_ptr.*];
                const other_class = self.find(other.class);
                if (other_class == stored.class) continue;
                if (!self.congruenceAllowed(stored.node)) continue;
                _ = try self.merge(other_class, stored.class, .{
                    .congruence = .{
                        .left = gop.value_ptr.*,
                        .right = @intCast(idx),
                    },
                });
                changed = true;
                any = true;
            }
            if (!changed) break;
        }
        return any;
    }

    /// Rebuild the splice index from scratch: lowest bag node id per
    /// (head, class root). Run at each rebuild pass start so splicing
    /// sees every union applied so far; between rebuilds the index only
    /// grows through `add`, and staleness merely defers a splice.
    ///
    /// Entries whose expansion re-enters their own class are dropped:
    /// after an absorption- or idempotence-style union a class contains a
    /// bag mentioning the class itself, and splicing through it would
    /// grow member lists without bound (each pass re-expanding the
    /// occurrence it atomicized last pass). A cyclic class is an atomic
    /// member everywhere — bags over it are not fully canonical, which
    /// costs some congruence merges in that corner but keeps every list
    /// finite.
    fn refreshBagIndex(self: *EGraph) !void {
        self.bag_in_class.clearRetainingCapacity();
        for (self.nodes.items, 0..) |stored, idx| {
            const bag = switch (stored.node) {
                .bag => |bag| bag,
                else => continue,
            };
            const key = bagKey(bag.term_id, self.find(stored.class));
            const gop = try self.bag_in_class.getOrPut(self.allocator, key);
            if (!gop.found_existing or gop.value_ptr.* > idx) {
                gop.value_ptr.* = @intCast(idx);
            }
        }
        var cyclic: std.ArrayListUnmanaged(u64) = .{};
        for (self.bag_in_class.keys()) |key| {
            const term_id: u32 = @intCast(key >> 32);
            const root: EClassId = @truncate(key);
            if (try self.bagExpansionReenters(term_id, root)) {
                try cyclic.append(self.allocator, key);
            }
        }
        for (cyclic.items) |key| {
            _ = self.bag_in_class.swapRemove(key);
        }
        self.ac_cyclic_dropped_total += cyclic.items.len;
    }

    /// True when the transitive same-head member expansion of `root`'s
    /// bag reaches `root` again.
    fn bagExpansionReenters(
        self: *const EGraph,
        term_id: u32,
        root: EClassId,
    ) !bool {
        var stack: std.ArrayListUnmanaged(EClassId) = .{};
        var seen: std.ArrayListUnmanaged(EClassId) = .{};
        const bag_node = self.bag_in_class.get(bagKey(term_id, root)).?;
        for (self.nodes.items[bag_node].node.bag.members) |member| {
            try stack.append(self.allocator, self.find(member));
        }
        while (stack.pop()) |class| {
            if (class == root) return true;
            if (std.mem.indexOfScalar(
                EClassId,
                seen.items,
                class,
            ) != null) continue;
            try seen.append(self.allocator, class);
            const node = self.bag_in_class.get(
                bagKey(term_id, class),
            ) orelse continue;
            for (self.nodes.items[node].node.bag.members) |member| {
                try stack.append(self.allocator, self.find(member));
            }
        }
        return false;
    }

    /// Equality saturation: batched match-then-instantiate per iteration,
    /// rebuild after each batch, until a fixpoint (no new node, no
    /// effective union) or a cap. Deterministic: node order, rule order,
    /// and class-member order are all insertion-ordered.
    pub fn saturate(
        self: *EGraph,
        rules: []const Rule,
        opts: SaturateOptions,
    ) !SaturateStats {
        var stats = SaturateStats{ .outcome = .iteration_capped };
        const capped_start = self.ac_match_capped_total;
        const cyclic_start = self.ac_cyclic_dropped_total;
        // Match-phase scratch: pattern pairs, substitution probes, and
        // candidate lists are garbage the moment one (node, rule) match
        // call returns. Left in the egraph arena they accumulate to
        // budget x (nodes x rules) allocations per iteration — gigabytes
        // on dense workloads — so they live in a reusable arena instead.
        // Escaping values (solution substs, extensions, sub-bag member
        // arrays) stay on `self.allocator`.
        var scratch_state = std.heap.ArenaAllocator.init(
            std.heap.page_allocator,
        );
        defer scratch_state.deinit();
        _ = try self.rebuild();
        while (stats.iterations < opts.max_iterations) {
            stats.iterations += 1;
            try self.buildClassIndex();

            var matches: std.ArrayListUnmanaged(Match) = .{};
            const matched_nodes = self.nodes.items.len;
            for (0..matched_nodes) |node_id| {
                switch (self.nodes.items[node_id].node) {
                    .leaf => {},
                    .app => |app| for (rules, 0..) |rule, rule_slot| {
                        const pattern = rule.match_side.app;
                        if (pattern.term_id != app.term_id) continue;
                        if (pattern.args.len != app.children.len) continue;
                        self.ac_budget_remaining = opts.ac_match_budget;
                        self.ac_budget_hit = false;
                        _ = scratch_state.reset(.retain_capacity);
                        try self.matchRule(
                            rule,
                            @intCast(rule_slot),
                            @intCast(node_id),
                            &matches,
                            scratch_state.allocator(),
                        );
                        if (self.ac_budget_hit) {
                            self.ac_match_capped_total += 1;
                        }
                    },
                    .bag => |bag| for (rules, 0..) |rule, rule_slot| {
                        const pattern = rule.match_side.app;
                        if (pattern.term_id != bag.term_id) continue;
                        self.ac_budget_remaining = opts.ac_match_budget;
                        self.ac_budget_hit = false;
                        _ = scratch_state.reset(.retain_capacity);
                        try self.matchRuleBag(
                            rule,
                            @intCast(rule_slot),
                            @intCast(node_id),
                            &matches,
                            scratch_state.allocator(),
                        );
                        if (self.ac_budget_hit) {
                            self.ac_match_capped_total += 1;
                        }
                    },
                }
                // Binder-subset matching materializes sub-bags via add();
                // hold that growth to the same node cap as the apply loop.
                if (self.nodes.items.len > opts.max_nodes) {
                    _ = try self.rebuild();
                    stats.outcome = .node_capped;
                    return self.finishStats(stats, capped_start, cyclic_start);
                }
            }

            var changed = false;
            var avoid_cache: AvoidCache = .{};
            for (matches.items) |m| {
                if (!try self.depGateAllows(
                    rules[m.rule_slot],
                    m.subst,
                    &avoid_cache,
                )) {
                    stats.dep_deferred += 1;
                    continue;
                }
                const target = (try self.instantiate(
                    rules[m.rule_slot].target_side,
                    m.subst,
                )) orelse continue;
                var to_class = target.class;
                var to_node = target.node;
                if (m.extension.len != 0) {
                    // Extension semantics: the rewrite hit a sub-multiset
                    // of the bag; the target rejoins the leftover members
                    // before the union.
                    const bag_term =
                        self.nodes.items[m.root_node].node.bag.term_id;
                    const members = try self.allocator.alloc(
                        EClassId,
                        m.extension.len + 1,
                    );
                    members[0] = target.class;
                    @memcpy(members[1..], m.extension);
                    const shape = ENode{ .bag = .{
                        .term_id = bag_term,
                        .members = members,
                    } };
                    to_class = try self.add(shape);
                    to_node = (try self.lookupNode(shape)).?;
                }
                const from = self.find(self.nodes.items[m.root_node].class);
                const merged = try self.merge(from, to_class, .{
                    .rule = .{
                        .rule_slot = m.rule_slot,
                        .from_node = m.root_node,
                        .to_node = to_node,
                        .subst = m.subst,
                        .extension = m.extension,
                    },
                });
                if (merged) {
                    changed = true;
                    stats.unions_applied += 1;
                }
                if (self.nodes.items.len > opts.max_nodes) {
                    _ = try self.rebuild();
                    stats.outcome = .node_capped;
                    return self.finishStats(stats, capped_start, cyclic_start);
                }
            }

            const grew = self.nodes.items.len != matched_nodes;
            const congr_changed = try self.rebuild();
            if (!changed and !grew and !congr_changed) {
                stats.outcome = .saturated;
                return self.finishStats(stats, capped_start, cyclic_start);
            }
        }
        return self.finishStats(stats, capped_start, cyclic_start);
    }

    fn finishStats(
        self: *const EGraph,
        stats: SaturateStats,
        capped_start: usize,
        cyclic_start: usize,
    ) SaturateStats {
        var out = stats;
        out.ac_match_capped = self.ac_match_capped_total - capped_start;
        out.ac_cyclic_dropped = self.ac_cyclic_dropped_total - cyclic_start;
        return out;
    }

    const AvoidCache = std.AutoArrayHashMapUnmanaged(LeafId, []const bool);

    /// Per-class snapshot of `avoidable(class, atom)`: the class can
    /// denote at least one term in which `atom` does not occur. Monotone
    /// in graph growth (members only accumulate under adds and merges),
    /// so a stale false only defers a match to a later iteration — it
    /// never admits a bad one.
    fn computeAvoidable(self: *EGraph, atom: LeafId) ![]const bool {
        const avoid = try self.allocator.alloc(bool, self.parents.items.len);
        @memset(avoid, false);
        while (true) {
            var changed = false;
            node_loop: for (self.nodes.items) |stored| {
                const root = self.find(stored.class);
                if (avoid[root]) continue;
                switch (stored.node) {
                    .leaf => |leaf| if (leaf == atom) continue :node_loop,
                    .app => |app| for (app.children) |child| switch (child) {
                        .bound => |leaf| if (leaf == atom) {
                            continue :node_loop;
                        },
                        .class => |c| {
                            const child_root = self.find(c);
                            if (child_root >= avoid.len or
                                !avoid[child_root])
                            {
                                continue :node_loop;
                            }
                        },
                    },
                    // A bag is a wide application with regular positions
                    // only: avoidable iff every member is.
                    .bag => |bag| for (bag.members) |member| {
                        const member_root = self.find(member);
                        if (member_root >= avoid.len or
                            !avoid[member_root])
                        {
                            continue :node_loop;
                        }
                    },
                }
                avoid[root] = true;
                changed = true;
            }
            if (!changed) break;
        }
        return avoid;
    }

    /// The dep gate: admit a match only when the instance the lowering
    /// will emit can satisfy the verifier's disjointness conditions —
    /// bound binders map to pairwise-distinct atoms, and each restricted
    /// term binder's class can denote a term avoiding the paired atom
    /// (extraction then picks such a representative). A refusal defers
    /// the match, not the union: matching reruns every iteration and
    /// avoidability only grows, so gating loses no valid union — only
    /// unprovable ones.
    fn depGateAllows(
        self: *EGraph,
        rule: Rule,
        subst: []const ?Child,
        cache: *AvoidCache,
    ) !bool {
        if (rule.bound_slots.len == 0) return true;
        for (rule.bound_slots, 0..) |slot, idx| {
            const binding = subst[slot] orelse continue;
            // A bound binder matched only in term positions binds a
            // class; the instance needs a concrete atom, which
            // extraction cannot conjure. Defer.
            if (binding != .bound) return false;
            for (rule.bound_slots[0..idx]) |prev_slot| {
                const prev = subst[prev_slot] orelse continue;
                if (prev == .bound and prev.bound == binding.bound) {
                    return false;
                }
            }
        }
        for (rule.restrictions) |restriction| {
            const bound_binding = subst[restriction.bound_slot] orelse {
                continue;
            };
            const atom = switch (bound_binding) {
                .bound => |leaf| leaf,
                .class => return false,
            };
            const term_binding = subst[restriction.term_slot] orelse continue;
            switch (term_binding) {
                .bound => |leaf| if (leaf == atom) return false,
                .class => |c| {
                    const gop = try cache.getOrPut(self.allocator, atom);
                    if (!gop.found_existing) {
                        gop.value_ptr.* = try self.computeAvoidable(atom);
                    }
                    const avoid = gop.value_ptr.*;
                    const root = self.find(c);
                    if (root >= avoid.len or !avoid[root]) return false;
                },
            }
        }
        return true;
    }

    fn canonicalize(self: *const EGraph, node: ENode) !ENode {
        return self.canonicalizeInto(node, null, self.allocator);
    }

    fn canonicalizeWith(
        self: *const EGraph,
        node: ENode,
        self_class: ?EClassId,
    ) error{OutOfMemory}!ENode {
        return self.canonicalizeInto(node, self_class, self.allocator);
    }

    /// Canonicalize a node into `alloc`. `self_class` (the node's own
    /// class, when re-canonicalizing a stored node) seeds the splice
    /// cycle guard so a cyclic class stays an atomic member of its own
    /// bag. Callers that only probe the memo pass a scratch allocator;
    /// storage paths pass the egraph arena (or own the result).
    fn canonicalizeInto(
        self: *const EGraph,
        node: ENode,
        self_class: ?EClassId,
        alloc: std.mem.Allocator,
    ) error{OutOfMemory}!ENode {
        switch (node) {
            .leaf => return node,
            .app => |app| {
                // An AC-policied binary application interns as a bag.
                if (app.children.len == 2 and
                    app.children[0] == .class and
                    app.children[1] == .class and
                    self.ac_heads.contains(app.term_id))
                {
                    return try self.canonicalBag(
                        app.term_id,
                        &.{ app.children[0].class, app.children[1].class },
                        self_class,
                        alloc,
                    );
                }
                const children = try alloc.alloc(
                    Child,
                    app.children.len,
                );
                for (app.children, 0..) |child, idx| {
                    children[idx] = switch (child) {
                        .class => |id| .{ .class = self.find(id) },
                        .bound => child,
                    };
                }
                return .{ .app = .{
                    .term_id = app.term_id,
                    .children = children,
                } };
            },
            .bag => |bag| return try self.canonicalBag(
                bag.term_id,
                bag.members,
                self_class,
                alloc,
            ),
        }
    }

    fn bagKey(term_id: u32, root: EClassId) u64 {
        return (@as(u64, term_id) << 32) | root;
    }

    /// Splice, canonicalize, and sort bag members: any member class that
    /// denotes a same-head bag contributes its members instead of itself
    /// (recursively), so every grouping of the same multiset interns to
    /// one shape.
    fn canonicalBag(
        self: *const EGraph,
        term_id: u32,
        members: []const EClassId,
        self_class: ?EClassId,
        alloc: std.mem.Allocator,
    ) error{OutOfMemory}!ENode {
        var out: std.ArrayListUnmanaged(EClassId) = .{};
        var visited: std.ArrayListUnmanaged(EClassId) = .{};
        if (self_class) |class| {
            try visited.append(alloc, self.find(class));
        }
        for (members) |member| {
            try self.spliceInto(
                term_id,
                self.find(member),
                &out,
                &visited,
                alloc,
            );
        }
        std.mem.sort(EClassId, out.items, {}, std.sort.asc(EClassId));
        return .{ .bag = .{ .term_id = term_id, .members = out.items } };
    }

    /// Append `root` to `out`, expanding through its bag node when the
    /// class denotes one. `visited` is the ancestor set of the current
    /// expansion: re-entering a class keeps it atomic, so bags over
    /// cyclic classes (absorption-style unions) stay finite. The cost is
    /// full canonicality in that corner — strictly better than the
    /// unbounded minting the same corner causes in tree representation.
    fn spliceInto(
        self: *const EGraph,
        term_id: u32,
        root: EClassId,
        out: *std.ArrayListUnmanaged(EClassId),
        visited: *std.ArrayListUnmanaged(EClassId),
        alloc: std.mem.Allocator,
    ) error{OutOfMemory}!void {
        const bag_node = self.bag_in_class.get(bagKey(term_id, root)) orelse {
            try out.append(alloc, root);
            return;
        };
        if (std.mem.indexOfScalar(EClassId, visited.items, root) != null) {
            try out.append(alloc, root);
            return;
        }
        try visited.append(alloc, root);
        defer _ = visited.pop();
        const members = self.nodes.items[bag_node].node.bag.members;
        for (members) |member| {
            try self.spliceInto(
                term_id,
                self.find(member),
                out,
                visited,
                alloc,
            );
        }
    }

    fn congruenceAllowed(self: *const EGraph, node: ENode) bool {
        return switch (node) {
            // Distinct leaves never share a canonical shape, and one leaf
            // is deduped at add time; defensive false.
            .leaf => false,
            .app => |app| self.congr_heads.contains(app.term_id),
            .bag => |bag| self.congr_heads.contains(bag.term_id),
        };
    }

    fn buildClassIndex(self: *EGraph) !void {
        // Old member lists are abandoned to the arena.
        self.class_index.clearRetainingCapacity();
        for (self.nodes.items, 0..) |stored, node_id| {
            const root = self.find(stored.class);
            const gop = try self.class_index.getOrPut(self.allocator, root);
            if (!gop.found_existing) gop.value_ptr.* = .{};
            try gop.value_ptr.append(self.allocator, @intCast(node_id));
        }
    }

    const Match = struct {
        rule_slot: u32,
        root_node: ENodeId,
        subst: []const ?Child,
        /// Unmatched bag members (canonical roots at match time) of an AC
        /// match; the apply loop wraps the target with them.
        extension: []const EClassId = &.{},
    };

    fn matchRule(
        self: *EGraph,
        rule: Rule,
        rule_slot: u32,
        root_node: ENodeId,
        matches: *std.ArrayListUnmanaged(Match),
        scratch: std.mem.Allocator,
    ) !void {
        const pattern = rule.match_side.app;
        const node = self.nodes.items[root_node].node.app;
        const pairs = try scratch.alloc(PatternPair, pattern.args.len);
        for (pattern.args, node.children, 0..) |p, c, idx| {
            pairs[idx] = .{ .pattern = p, .child = c };
        }
        const subst = try scratch.alloc(?Child, rule.num_binders);
        @memset(subst, null);

        var solutions: std.ArrayListUnmanaged([]const ?Child) = .{};
        try self.solvePairs(pairs, 0, subst, &solutions, self.allocator, scratch);
        for (solutions.items) |solution| {
            try matches.append(self.allocator, .{
                .rule_slot = rule_slot,
                .root_node = root_node,
                .subst = solution,
            });
        }
    }

    const PatternPair = struct {
        pattern: TemplateExpr,
        child: Child,
    };

    const BagSolution = struct {
        subst: []const ?Child,
        extension: []const EClassId,
    };

    /// Flatten a rule side over an AC head into its member patterns:
    /// nested same-head applications splice (mirroring bag interning);
    /// binders and other-headed applications are members.
    fn flattenPattern(
        self: *EGraph,
        alloc: std.mem.Allocator,
        term_id: u32,
        pattern: TemplateExpr,
        out: *std.ArrayListUnmanaged(TemplateExpr),
    ) error{OutOfMemory}!void {
        if (pattern == .app and pattern.app.term_id == term_id and
            pattern.app.args.len == 2)
        {
            try self.flattenPattern(alloc, term_id, pattern.app.args[0], out);
            try self.flattenPattern(alloc, term_id, pattern.app.args[1], out);
            return;
        }
        try out.append(alloc, pattern);
    }

    /// Structured members sort before binder members: they pin bindings
    /// cheaply before the binders enumerate sub-multisets.
    fn structuredFirst(_: void, a: TemplateExpr, b: TemplateExpr) bool {
        return a == .app and b == .binder;
    }

    /// E-matching modulo AC: match a rule whose match side is headed by
    /// the bag's operator against one bag node. Pattern members assign to
    /// distinct member positions (structured members one each, binder
    /// members any nonempty sub-multiset); leftover members become the
    /// match's extension. Enumeration is bounded by the caller-set
    /// `ac_budget_remaining` (trips reported via `ac_match_capped`).
    fn matchRuleBag(
        self: *EGraph,
        rule: Rule,
        rule_slot: u32,
        root_node: ENodeId,
        matches: *std.ArrayListUnmanaged(Match),
        scratch: std.mem.Allocator,
    ) !void {
        const bag = self.nodes.items[root_node].node.bag;
        var pattern_members: std.ArrayListUnmanaged(TemplateExpr) = .{};
        try self.flattenPattern(
            scratch,
            bag.term_id,
            rule.match_side,
            &pattern_members,
        );
        if (pattern_members.items.len > bag.members.len) return;
        std.mem.sort(
            TemplateExpr,
            pattern_members.items,
            {},
            structuredFirst,
        );

        const subst = try scratch.alloc(?Child, rule.num_binders);
        @memset(subst, null);
        const used = try scratch.alloc(bool, bag.members.len);
        @memset(used, false);
        var solutions: std.ArrayListUnmanaged(BagSolution) = .{};
        try self.assignBagMembers(
            bag,
            pattern_members.items,
            0,
            subst,
            used,
            true,
            &solutions,
            self.allocator,
            scratch,
        );
        for (solutions.items) |solution| {
            try matches.append(self.allocator, .{
                .rule_slot = rule_slot,
                .root_node = root_node,
                .subst = solution.subst,
                .extension = solution.extension,
            });
        }
    }

    /// Recursive assignment of pattern members to bag member positions.
    /// `subst` and `used` thread through with backtracking; solutions
    /// carry copies owned by `dest` (the caller's escape allocator);
    /// every intermediate probe lives in `scratch`.
    fn assignBagMembers(
        self: *EGraph,
        bag: ENode.Bag,
        pattern_members: []const TemplateExpr,
        p_idx: usize,
        subst: []?Child,
        used: []bool,
        allow_extension: bool,
        solutions: *std.ArrayListUnmanaged(BagSolution),
        dest: std.mem.Allocator,
        scratch: std.mem.Allocator,
    ) error{OutOfMemory}!void {
        // Entry charge, completions included: it bounds calls, solutions,
        // and recursion depth alike. The flag distinguishes a genuine
        // early-out from an enumeration that finished exactly on its last
        // budget unit (only the former weakens a forced negative).
        if (self.ac_budget_remaining == 0) {
            self.ac_budget_hit = true;
            return;
        }
        self.ac_budget_remaining -= 1;
        if (p_idx == pattern_members.len) {
            var extension: std.ArrayListUnmanaged(EClassId) = .{};
            for (bag.members, used) |member, is_used| {
                if (!is_used) {
                    try extension.append(scratch, self.find(member));
                }
            }
            if (extension.items.len != 0 and !allow_extension) return;
            try solutions.append(dest, .{
                .subst = try dest.dupe(?Child, subst),
                .extension = try dest.dupe(EClassId, extension.items),
            });
            return;
        }
        switch (pattern_members[p_idx]) {
            .app => {
                for (bag.members, 0..) |member, idx| {
                    if (used[idx]) continue;
                    // Solve the structured pattern against this member
                    // class, then continue assigning under each solution.
                    const pairs = try scratch.alloc(PatternPair, 1);
                    pairs[0] = .{
                        .pattern = pattern_members[p_idx],
                        .child = .{ .class = member },
                    };
                    const probe = try scratch.dupe(?Child, subst);
                    var partial: std.ArrayListUnmanaged(
                        []const ?Child,
                    ) = .{};
                    try self.solvePairs(
                        pairs,
                        0,
                        probe,
                        &partial,
                        scratch,
                        scratch,
                    );
                    used[idx] = true;
                    for (partial.items) |candidate| {
                        const next = try scratch.dupe(
                            ?Child,
                            candidate,
                        );
                        try self.assignBagMembers(
                            bag,
                            pattern_members,
                            p_idx + 1,
                            next,
                            used,
                            allow_extension,
                            solutions,
                            dest,
                            scratch,
                        );
                    }
                    used[idx] = false;
                }
            },
            .binder => |binder_idx| {
                var chosen: std.ArrayListUnmanaged(usize) = .{};
                try self.enumerateBinderSubsets(
                    bag,
                    pattern_members,
                    p_idx,
                    subst,
                    used,
                    allow_extension,
                    solutions,
                    binder_idx,
                    0,
                    &chosen,
                    dest,
                    scratch,
                );
            },
        }
    }

    /// Enumerate nonempty sub-multisets of unused members (in position
    /// order) for one binder member: each subset is tried both as the
    /// binder's binding and as a prefix of a larger subset.
    fn enumerateBinderSubsets(
        self: *EGraph,
        bag: ENode.Bag,
        pattern_members: []const TemplateExpr,
        p_idx: usize,
        subst: []?Child,
        used: []bool,
        allow_extension: bool,
        solutions: *std.ArrayListUnmanaged(BagSolution),
        binder_idx: usize,
        start: usize,
        chosen: *std.ArrayListUnmanaged(usize),
        dest: std.mem.Allocator,
        scratch: std.mem.Allocator,
    ) error{OutOfMemory}!void {
        for (start..bag.members.len) |idx| {
            if (used[idx]) continue;
            if (self.ac_budget_remaining == 0) {
                self.ac_budget_hit = true;
                return;
            }
            self.ac_budget_remaining -= 1;
            try chosen.append(scratch, idx);
            used[idx] = true;
            try self.applyBinderSubset(
                bag,
                pattern_members,
                p_idx,
                subst,
                used,
                allow_extension,
                solutions,
                binder_idx,
                chosen.items,
                dest,
                scratch,
            );
            try self.enumerateBinderSubsets(
                bag,
                pattern_members,
                p_idx,
                subst,
                used,
                allow_extension,
                solutions,
                binder_idx,
                idx + 1,
                chosen,
                dest,
                scratch,
            );
            used[idx] = false;
            _ = chosen.pop();
        }
    }

    /// Bind one binder member to the chosen sub-multiset: the member's
    /// class for a singleton, a lazily-materialized sub-bag class
    /// otherwise. Continues the assignment on success.
    fn applyBinderSubset(
        self: *EGraph,
        bag: ENode.Bag,
        pattern_members: []const TemplateExpr,
        p_idx: usize,
        subst: []?Child,
        used: []bool,
        allow_extension: bool,
        solutions: *std.ArrayListUnmanaged(BagSolution),
        binder_idx: usize,
        chosen: []const usize,
        dest: std.mem.Allocator,
        scratch: std.mem.Allocator,
    ) error{OutOfMemory}!void {
        const binding: Child = if (chosen.len == 1)
            .{ .class = bag.members[chosen[0]] }
        else blk: {
            // Scratch-backed shape: addWith copies the canonical members
            // into the egraph arena only if the sub-bag is actually new.
            const members = try scratch.alloc(EClassId, chosen.len);
            for (chosen, 0..) |member_idx, i| {
                members[i] = bag.members[member_idx];
            }
            const shape = ENode{ .bag = .{
                .term_id = bag.term_id,
                .members = members,
            } };
            break :blk .{ .class = try self.addWith(shape, scratch) };
        };
        if (subst[binder_idx]) |existing| {
            if (!self.bindingsCompatible(existing, binding)) return;
            try self.assignBagMembers(
                bag,
                pattern_members,
                p_idx + 1,
                subst,
                used,
                allow_extension,
                solutions,
                dest,
                scratch,
            );
        } else {
            subst[binder_idx] = self.normalizeBinding(binding);
            defer subst[binder_idx] = null;
            try self.assignBagMembers(
                bag,
                pattern_members,
                p_idx + 1,
                subst,
                used,
                allow_extension,
                solutions,
                dest,
                scratch,
            );
        }
    }

    /// Top-down e-matching with substitution threading (microegg's
    /// starting point). Binders bind classes (canonical) or bound atoms;
    /// an application pattern against a class child branches over the
    /// class's member nodes with a re-stacked worklist.
    fn solvePairs(
        self: *EGraph,
        pairs: []const PatternPair,
        idx: usize,
        subst: []?Child,
        solutions: *std.ArrayListUnmanaged([]const ?Child),
        dest: std.mem.Allocator,
        scratch: std.mem.Allocator,
    ) !void {
        if (idx == pairs.len) {
            const copy = try dest.dupe(?Child, subst);
            try solutions.append(dest, copy);
            return;
        }
        const pair = pairs[idx];
        switch (pair.pattern) {
            .binder => |binder_idx| {
                if (subst[binder_idx]) |existing| {
                    if (!self.bindingsCompatible(existing, pair.child)) {
                        return;
                    }
                    try self.solvePairs(
                        pairs,
                        idx + 1,
                        subst,
                        solutions,
                        dest,
                        scratch,
                    );
                } else {
                    subst[binder_idx] = self.normalizeBinding(pair.child);
                    try self.solvePairs(
                        pairs,
                        idx + 1,
                        subst,
                        solutions,
                        dest,
                        scratch,
                    );
                    subst[binder_idx] = null;
                }
            },
            .app => |pattern_app| switch (pair.child) {
                .bound => return,
                .class => |class| {
                    const root = self.find(class);
                    const members = self.class_index.get(root) orelse return;
                    for (members.items) |member_id| {
                        switch (self.nodes.items[member_id].node) {
                            .leaf => continue,
                            .app => |member| {
                                if (member.term_id != pattern_app.term_id) {
                                    continue;
                                }
                                if (member.children.len !=
                                    pattern_app.args.len)
                                {
                                    continue;
                                }
                                const extended = try scratch.alloc(
                                    PatternPair,
                                    pattern_app.args.len +
                                        (pairs.len - idx - 1),
                                );
                                for (
                                    pattern_app.args,
                                    member.children,
                                    0..,
                                ) |p, c, i| {
                                    extended[i] = .{
                                        .pattern = p,
                                        .child = c,
                                    };
                                }
                                @memcpy(
                                    extended[pattern_app.args.len..],
                                    pairs[idx + 1 ..],
                                );
                                try self.solvePairs(
                                    extended,
                                    0,
                                    subst,
                                    solutions,
                                    dest,
                                    scratch,
                                );
                            },
                            // A same-head sub-pattern against a bag
                            // member: AC match with exact cover (no
                            // extension below the rewrite root), then
                            // chain the rest of the worklist under each
                            // solution.
                            .bag => |member_bag| {
                                if (member_bag.term_id !=
                                    pattern_app.term_id)
                                {
                                    continue;
                                }
                                var flat: std.ArrayListUnmanaged(
                                    TemplateExpr,
                                ) = .{};
                                try self.flattenPattern(
                                    scratch,
                                    member_bag.term_id,
                                    pair.pattern,
                                    &flat,
                                );
                                if (flat.items.len >
                                    member_bag.members.len)
                                {
                                    continue;
                                }
                                std.mem.sort(
                                    TemplateExpr,
                                    flat.items,
                                    {},
                                    structuredFirst,
                                );
                                const probe = try scratch.dupe(
                                    ?Child,
                                    subst,
                                );
                                const used = try scratch.alloc(
                                    bool,
                                    member_bag.members.len,
                                );
                                @memset(used, false);
                                var bag_solutions: std.ArrayListUnmanaged(
                                    BagSolution,
                                ) = .{};
                                try self.assignBagMembers(
                                    member_bag,
                                    flat.items,
                                    0,
                                    probe,
                                    used,
                                    false,
                                    &bag_solutions,
                                    scratch,
                                    scratch,
                                );
                                for (bag_solutions.items) |solution| {
                                    const next = try scratch.dupe(
                                        ?Child,
                                        solution.subst,
                                    );
                                    try self.solvePairs(
                                        pairs[idx + 1 ..],
                                        0,
                                        next,
                                        solutions,
                                        dest,
                                        scratch,
                                    );
                                }
                            },
                        }
                    }
                },
            },
        }
    }

    fn normalizeBinding(self: *const EGraph, child: Child) Child {
        return switch (child) {
            .class => |id| .{ .class = self.find(id) },
            .bound => child,
        };
    }

    fn bindingsCompatible(self: *const EGraph, a: Child, b: Child) bool {
        switch (a) {
            .class => |ac| switch (b) {
                .class => |bc| return self.find(ac) == self.find(bc),
                .bound => |leaf| return self.leafMatchesClass(leaf, ac),
            },
            .bound => |leaf| switch (b) {
                .class => |bc| return self.leafMatchesClass(leaf, bc),
                .bound => |bl| return leaf == bl,
            },
        }
    }

    fn leafMatchesClass(
        self: *const EGraph,
        leaf: LeafId,
        class: EClassId,
    ) bool {
        const leaf_class = self.leaf_classes.get(leaf) orelse return false;
        return self.find(leaf_class) == self.find(class);
    }

    const Instantiated = struct {
        class: EClassId,
        /// A member node anchoring the instance in the explanation forest:
        /// the instance node itself for an application target, the class's
        /// creating node for a bare binder target.
        node: ENodeId,
    };

    /// Instantiate a rule's target side over a substitution, adding the
    /// nodes it denotes. Returns null when the rule instance is ill-formed
    /// here (bound position without an atom binding); the match is skipped.
    fn instantiate(
        self: *EGraph,
        pattern: TemplateExpr,
        subst: []const ?Child,
    ) !?Instantiated {
        switch (pattern) {
            .binder => |binder_idx| {
                const binding = subst[binder_idx] orelse return null;
                const class = switch (binding) {
                    .class => |id| self.find(id),
                    .bound => |leaf| try self.leafClass(leaf),
                };
                const root = self.find(class);
                return .{ .class = root, .node = self.class_node.items[root] };
            },
            .app => |app| {
                const mask = self.bound_masks.get(app.term_id) orelse 0;
                const children = try self.allocator.alloc(
                    Child,
                    app.args.len,
                );
                for (app.args, 0..) |arg, idx| {
                    const is_bound = idx < 64 and
                        (mask >> @intCast(idx)) & 1 == 1;
                    if (is_bound) {
                        const binder_idx = switch (arg) {
                            .binder => |b| b,
                            .app => return null,
                        };
                        const binding = subst[binder_idx] orelse return null;
                        switch (binding) {
                            .bound => |leaf| {
                                children[idx] = .{ .bound = leaf };
                            },
                            .class => return null,
                        }
                    } else {
                        const inst = (try self.instantiate(
                            arg,
                            subst,
                        )) orelse return null;
                        children[idx] = .{ .class = inst.class };
                    }
                }
                const shape = ENode{ .app = .{
                    .term_id = app.term_id,
                    .children = children,
                } };
                const class = try self.add(shape);
                const node = (try self.lookupNode(shape)).?;
                return .{ .class = class, .node = node };
            },
        }
    }

    /// Class of a leaf atom used in a regular (term) position, creating it
    /// on first use.
    fn leafClass(self: *EGraph, leaf: LeafId) !EClassId {
        if (self.leaf_classes.get(leaf)) |class| return self.find(class);
        return try self.add(.{ .leaf = leaf });
    }

    /// Produce the term-level conversion path from `from` to `to` (both
    /// resolved terms over graph nodes, typically the two seed formulas):
    /// a sequence of single-rule rewrite steps at positions whose
    /// sequential application transforms `from` into exactly `to`. Returns
    /// null when the two terms are not in one class or the explanation
    /// exceeds the caps (a clean miss for the caller, never a wrong path).
    /// `rules` must be the slice passed to `saturate`.
    pub fn explain(
        self: *EGraph,
        rules: []const Rule,
        from: *const Term,
        to: *const Term,
        opts: ExplainOptions,
    ) !?[]const Step {
        const from_class = self.nodes.items[from.node].class;
        const to_class = self.nodes.items[to.node].class;
        if (!self.sameClass(from_class, to_class)) return null;
        try self.buildClassIndex();
        var ctx = ExplainCtx{
            .eg = self,
            .rules = rules,
            .opts = opts,
        };
        if (!try ctx.explainTerms(from, to, &.{})) return null;
        return ctx.steps.items;
    }
};

/// A resolved term: a concrete tree of graph nodes, one representative per
/// e-class hole. `children` parallels the node's children; entries are null
/// at bound positions (the atom is part of the node identity). For a bag
/// node, `children` parallels the node's sorted members (all non-null) and
/// the term denotes the right-nested comb over them in that order.
pub const Term = struct {
    node: ENodeId,
    children: []const ?*const Term,
};

/// Structural term equality. Anchor node ids are NOT compared: duplicate
/// stored nodes with one canonical shape (the residue of congruence
/// rebuilds) denote the same term.
pub fn termEql(eg: *const EGraph, a: *const Term, b: *const Term) bool {
    const na = eg.nodes.items[a.node].node;
    const nb = eg.nodes.items[b.node].node;
    switch (na) {
        .leaf => |leaf| return nb == .leaf and nb.leaf == leaf,
        .bag => |ab| {
            if (nb != .bag) return false;
            if (ab.term_id != nb.bag.term_id) return false;
            if (a.children.len != b.children.len) return false;
            for (a.children, b.children) |ca, cb| {
                if (!termEql(eg, ca.?, cb.?)) return false;
            }
            return true;
        },
        .app => |aa| {
            if (nb != .app) return false;
            const ba = nb.app;
            if (aa.term_id != ba.term_id) return false;
            if (aa.children.len != ba.children.len) return false;
            for (aa.children, ba.children, a.children, b.children) |
                ca,
                cb,
                ta,
                tb,
            | {
                switch (ca) {
                    .bound => |leaf| {
                        if (cb != .bound or cb.bound != leaf) return false;
                    },
                    .class => {
                        if (cb != .class) return false;
                        if (!termEql(eg, ta.?, tb.?)) return false;
                    },
                }
            }
            return true;
        },
    }
}

/// Same head, same bound atoms, same child classes: the two nodes denote
/// the same e-node shape (possibly as duplicate stored entries).
fn nodeShapeEql(eg: *const EGraph, n1: ENodeId, n2: ENodeId) bool {
    if (n1 == n2) return true;
    const a = eg.nodes.items[n1].node;
    const b = eg.nodes.items[n2].node;
    switch (a) {
        .leaf => |leaf| return b == .leaf and b.leaf == leaf,
        .bag => |ab| {
            if (b != .bag) return false;
            const bb = b.bag;
            if (ab.term_id != bb.term_id) return false;
            if (ab.members.len != bb.members.len) return false;
            for (ab.members, bb.members) |ma, mb| {
                if (eg.find(ma) != eg.find(mb)) return false;
            }
            return true;
        },
        .app => |aa| {
            if (b != .app) return false;
            const ba = b.app;
            if (aa.term_id != ba.term_id) return false;
            if (aa.children.len != ba.children.len) return false;
            for (aa.children, ba.children) |ca, cb| {
                switch (ca) {
                    .bound => |leaf| {
                        if (cb != .bound or cb.bound != leaf) return false;
                    },
                    .class => |c| {
                        if (cb != .class) return false;
                        if (eg.find(c) != eg.find(cb.class)) return false;
                    },
                }
            }
            return true;
        },
    }
}

/// A rendered rule-binder assignment for one extracted step.
pub const BindingValue = union(enum) {
    term: *const Term,
    bound: LeafId,
};

/// One extracted rewrite at `position`, turning the redex `before` into
/// `after`. A `.rule` step applies the `@conversion` theorem (right-to-left
/// when `needs_symm`) with `bindings`; a `.pool_equation` step is the
/// reference-pool entry's own `rel(lhs, rhs)` fact, cited directly
/// (through `symm` when `needs_symm`).
pub const Step = struct {
    pub const Source = union(enum) {
        /// The `@conversion` theorem's rule id (caller tag, opaque here).
        rule: u32,
        /// Index into the driver's reference pool.
        pool_equation: u32,
    };

    /// Present when an endpoint of a `.rule` step is a bag: the member
    /// indices of that endpoint's children the rule instance covers. The
    /// complement (identical on both sides) is the extension the lowering
    /// re-trees around the instance. Empty for a non-bag endpoint (the
    /// whole term is the instance).
    pub const BagInfo = struct {
        matched_before: []const u32,
        matched_after: []const u32,
    };

    source: Source,
    needs_symm: bool,
    /// Argument-index path from the formula root to the redex (for a bag
    /// term, a component is a member index of the canonical comb).
    position: []const u32,
    before: *const Term,
    after: *const Term,
    /// Indexed by rule binder; entries the rule never bound are null.
    bindings: []const ?BindingValue,
    bag: ?BagInfo = null,
};

pub const ExplainOptions = struct {
    /// Give up (clean miss) beyond this many extracted steps.
    max_steps: usize = 512,
    /// Recursion cap over forest stitching + congruence descent.
    max_depth: usize = 64,
};

const Traversed = struct {
    just: Justification,
    /// True when the traversal runs the justification's semantic direction
    /// (endpoint a -> endpoint b).
    forward: bool,
};

const ExplainCtx = struct {
    eg: *EGraph,
    rules: []const Rule,
    opts: ExplainOptions,
    steps: std.ArrayListUnmanaged(Step) = .{},
    depth: usize = 0,
    /// Interned avoid-masks: sorted atom lists a representative's subtree
    /// must not mention. Index 0 is always the empty mask.
    mask_atoms: std.ArrayListUnmanaged([]const LeafId) = .{},
    /// Masks whose extraction fixpoint has run.
    masks_computed: std.AutoArrayHashMapUnmanaged(u32, void) = .{},
    /// Extraction state: minimal-size representative per (class root,
    /// avoid-mask). Restricted rule binders extract under a nonzero mask
    /// so the cited term satisfies the instance's disjointness
    /// conditions; everything else uses mask 0.
    class_cost: std.AutoArrayHashMapUnmanaged(u64, usize) = .{},
    class_best: std.AutoArrayHashMapUnmanaged(u64, ENodeId) = .{},
    class_term: std.AutoArrayHashMapUnmanaged(u64, *const Term) = .{},

    fn allocator(self: *ExplainCtx) std.mem.Allocator {
        return self.eg.allocator;
    }

    fn maskedKey(root: EClassId, mask_id: u32) u64 {
        return (@as(u64, mask_id) << 32) | root;
    }

    fn maskContains(atoms: []const LeafId, leaf: LeafId) bool {
        return std.mem.indexOfScalar(LeafId, atoms, leaf) != null;
    }

    /// Intern a sorted, deduplicated atom list. Linear scan: distinct
    /// masks per explanation are few (one per restricted atom set).
    fn internMask(self: *ExplainCtx, atoms: []const LeafId) !u32 {
        if (self.mask_atoms.items.len == 0) {
            try self.mask_atoms.append(self.allocator(), &.{});
        }
        for (self.mask_atoms.items, 0..) |existing, idx| {
            if (std.mem.eql(LeafId, existing, atoms)) return @intCast(idx);
        }
        try self.mask_atoms.append(
            self.allocator(),
            try self.allocator().dupe(LeafId, atoms),
        );
        return @intCast(self.mask_atoms.items.len - 1);
    }

    fn maskAtoms(self: *const ExplainCtx, mask_id: u32) []const LeafId {
        if (mask_id == 0) return &.{};
        return self.mask_atoms.items[mask_id];
    }

    /// Fixpoint pass computing, per class root, the minimal-size member
    /// node (ties broken by first node id) whose subtree avoids the
    /// mask's atoms. Well-founded by construction: a best node's children
    /// always have strictly smaller cost. Classes with no avoiding
    /// member simply get no entry (`classTerm` then returns null).
    fn ensureExtraction(self: *ExplainCtx, mask_id: u32) !void {
        const gop = try self.masks_computed.getOrPut(
            self.allocator(),
            mask_id,
        );
        if (gop.found_existing) return;
        const atoms = self.maskAtoms(mask_id);
        while (true) {
            var changed = false;
            node_loop: for (self.eg.nodes.items, 0..) |stored, node_id| {
                var cost: usize = 1;
                switch (stored.node) {
                    .leaf => |leaf| if (maskContains(atoms, leaf)) {
                        continue :node_loop;
                    },
                    .app => |app| for (app.children) |child| {
                        switch (child) {
                            .bound => |leaf| if (maskContains(atoms, leaf)) {
                                continue :node_loop;
                            },
                            .class => |c| {
                                const child_cost = self.class_cost.get(
                                    maskedKey(self.eg.find(c), mask_id),
                                ) orelse continue :node_loop;
                                cost += child_cost;
                            },
                        }
                    },
                    .bag => |bag| for (bag.members) |member| {
                        const child_cost = self.class_cost.get(
                            maskedKey(self.eg.find(member), mask_id),
                        ) orelse continue :node_loop;
                        cost += child_cost;
                    },
                }
                const root = self.eg.find(stored.class);
                const key = maskedKey(root, mask_id);
                const cost_gop = try self.class_cost.getOrPut(
                    self.allocator(),
                    key,
                );
                if (!cost_gop.found_existing or cost < cost_gop.value_ptr.*) {
                    cost_gop.value_ptr.* = cost;
                    try self.class_best.put(
                        self.allocator(),
                        key,
                        @intCast(node_id),
                    );
                    changed = true;
                }
            }
            if (!changed) break;
        }
    }

    /// The extracted representative term of a class under an avoid-mask
    /// (memoized per root and mask). Null when the class has no member
    /// avoiding the masked atoms.
    fn classTerm(
        self: *ExplainCtx,
        class: EClassId,
        mask_id: u32,
    ) error{OutOfMemory}!?*const Term {
        try self.ensureExtraction(mask_id);
        const key = maskedKey(self.eg.find(class), mask_id);
        if (self.class_term.get(key)) |term| return term;
        const best = self.class_best.get(key) orelse return null;
        const term = (try self.termForNode(best, mask_id)) orelse return null;
        try self.class_term.put(self.allocator(), key, term);
        return term;
    }

    /// A resolved term with `node` at the top and extracted representatives
    /// below, all avoiding the mask's atoms.
    fn termForNode(
        self: *ExplainCtx,
        node_id: ENodeId,
        mask_id: u32,
    ) error{OutOfMemory}!?*const Term {
        const node = self.eg.nodes.items[node_id].node;
        const children: []?*const Term = switch (node) {
            .leaf => &.{},
            .bag => |bag| blk: {
                const children = try self.allocator().alloc(
                    ?*const Term,
                    bag.members.len,
                );
                for (bag.members, 0..) |member, idx| {
                    children[idx] = (try self.classTerm(
                        member,
                        mask_id,
                    )) orelse return null;
                }
                break :blk children;
            },
            .app => |app| blk: {
                const children = try self.allocator().alloc(
                    ?*const Term,
                    app.children.len,
                );
                for (app.children, 0..) |child, idx| {
                    children[idx] = switch (child) {
                        .bound => null,
                        .class => |c| (try self.classTerm(c, mask_id)) orelse {
                            return null;
                        },
                    };
                }
                break :blk children;
            },
        };
        const term = try self.allocator().create(Term);
        term.* = .{ .node = node_id, .children = children };
        return term;
    }

    /// Path between two same-class nodes in the explanation forest, as
    /// justifications tagged with traversal direction.
    fn forestPath(
        self: *ExplainCtx,
        n1: ENodeId,
        n2: ENodeId,
    ) !?[]const Traversed {
        const alloc = self.allocator();
        // Ancestor chain of n1 with positions for LCA lookup.
        var chain1_nodes: std.ArrayListUnmanaged(ENodeId) = .{};
        var chain1_edges: std.ArrayListUnmanaged(ExplEdge) = .{};
        var positions: std.AutoArrayHashMapUnmanaged(ENodeId, usize) = .{};
        var current = n1;
        while (true) {
            try positions.put(alloc, current, chain1_nodes.items.len);
            try chain1_nodes.append(alloc, current);
            const edge = self.eg.expl_parent.items[current] orelse break;
            try chain1_edges.append(alloc, edge);
            current = edge.to;
        }
        // Walk up from n2 until the chains meet.
        var chain2_edges: std.ArrayListUnmanaged(ExplEdge) = .{};
        var lca_pos: usize = undefined;
        current = n2;
        while (true) {
            if (positions.get(current)) |pos| {
                lca_pos = pos;
                break;
            }
            const edge = self.eg.expl_parent.items[current] orelse {
                return null;
            };
            try chain2_edges.append(alloc, edge);
            current = edge.to;
        }

        var path: std.ArrayListUnmanaged(Traversed) = .{};
        for (chain1_edges.items[0..lca_pos]) |edge| {
            // Traversed child -> parent: as stored.
            try path.append(alloc, .{
                .just = edge.just,
                .forward = edge.forward,
            });
        }
        var idx = chain2_edges.items.len;
        while (idx > 0) {
            idx -= 1;
            // Traversed parent -> child: reversed.
            const edge = chain2_edges.items[idx];
            try path.append(alloc, .{
                .just = edge.just,
                .forward = !edge.forward,
            });
        }
        return path.items;
    }

    fn pushPos(
        self: *ExplainCtx,
        pos: []const u32,
        idx: u32,
    ) ![]const u32 {
        const extended = try self.allocator().alloc(u32, pos.len + 1);
        @memcpy(extended[0..pos.len], pos);
        extended[pos.len] = idx;
        return extended;
    }

    /// Emit the steps rewriting `from` into exactly `to` at `pos`. Returns
    /// false to give up (caps or an unexplainable gap) — the caller treats
    /// the whole extraction as a miss.
    /// Re-pair a seed-time term's children with its nodes' current member
    /// order. Bag members re-sort in place as unions land, so a Term built
    /// before saturation may no longer parallel its node. Children are
    /// reused verbatim (they pin the written formula's representatives) —
    /// only the bag-level pairing moves. Null when no pairing exists: a
    /// splice changed the member count, or a member's class drifted away
    /// from every child (the caller treats the edge as unexplainable).
    fn refreshSeedTerm(
        self: *ExplainCtx,
        term: *const Term,
    ) error{OutOfMemory}!?*const Term {
        if (self.eg.ac_heads.count() == 0) return term;
        switch (self.eg.nodes.items[term.node].node) {
            .leaf => return term,
            .app => {
                var children: ?[]?*const Term = null;
                for (term.children, 0..) |maybe_child, idx| {
                    const child = maybe_child orelse continue;
                    const fixed = (try self.refreshSeedTerm(child)) orelse {
                        return null;
                    };
                    if (fixed == child) continue;
                    if (children == null) {
                        children = try self.allocator().dupe(
                            ?*const Term,
                            term.children,
                        );
                    }
                    children.?[idx] = fixed;
                }
                const updated = children orelse return term;
                const copy = try self.allocator().create(Term);
                copy.* = .{ .node = term.node, .children = updated };
                return copy;
            },
            .bag => |bag| {
                if (term.children.len != bag.members.len) return null;
                const children = try self.allocator().alloc(
                    ?*const Term,
                    bag.members.len,
                );
                @memset(children, null);
                for (term.children) |maybe_child| {
                    const child = maybe_child orelse return null;
                    const fixed = (try self.refreshSeedTerm(child)) orelse {
                        return null;
                    };
                    const root = self.eg.find(
                        self.eg.nodes.items[fixed.node].class,
                    );
                    var placed = false;
                    for (bag.members, 0..) |member, idx| {
                        if (children[idx] != null) continue;
                        if (self.eg.find(member) != root) continue;
                        children[idx] = fixed;
                        placed = true;
                        break;
                    }
                    if (!placed) return null;
                }
                const copy = try self.allocator().create(Term);
                copy.* = .{ .node = term.node, .children = children };
                return copy;
            },
        }
    }

    fn explainTerms(
        self: *ExplainCtx,
        from: *const Term,
        to: *const Term,
        pos: []const u32,
    ) error{OutOfMemory}!bool {
        if (self.steps.items.len > self.opts.max_steps) return false;
        if (self.depth >= self.opts.max_depth) return false;
        self.depth += 1;
        defer self.depth -= 1;

        if (nodeShapeEql(self.eg, from.node, to.node)) {
            return try self.alignChildren(from, to, pos);
        }

        const path = (try self.forestPath(from.node, to.node)) orelse {
            return false;
        };
        var current = from;
        for (path) |edge| {
            current = (try self.processEdge(current, edge, pos)) orelse {
                return false;
            };
        }
        // A rendered pattern instance can anchor on a different member than
        // the forest vertex; the recursion re-aligns (bounded by max_depth).
        return try self.explainTerms(current, to, pos);
    }

    /// Same top node: recursively align differing child representatives.
    fn alignChildren(
        self: *ExplainCtx,
        from: *const Term,
        to: *const Term,
        pos: []const u32,
    ) error{OutOfMemory}!bool {
        if (from.children.len != to.children.len) return false;
        for (from.children, to.children, 0..) |fc, tc, idx| {
            const from_child = fc orelse continue;
            const to_child = tc.?;
            if (termEql(self.eg, from_child, to_child)) continue;
            const child_pos = try self.pushPos(pos, @intCast(idx));
            if (!try self.explainTerms(from_child, to_child, child_pos)) {
                return false;
            }
        }
        return true;
    }

    fn processEdge(
        self: *ExplainCtx,
        current: *const Term,
        edge: Traversed,
        pos: []const u32,
    ) error{OutOfMemory}!?*const Term {
        switch (edge.just) {
            .congruence => |congr| {
                const u = if (edge.forward) congr.left else congr.right;
                const v = if (edge.forward) congr.right else congr.left;
                var aligned = current;
                if (!nodeShapeEql(self.eg, aligned.node, u)) {
                    const anchor = (try self.termForNode(u, 0)) orelse {
                        return null;
                    };
                    if (!try self.explainTerms(aligned, anchor, pos)) {
                        return null;
                    }
                    aligned = anchor;
                }
                // Congruent nodes share canonical shape (same head, same
                // child classes, same bound atoms), so re-anchoring is
                // free: the term tree is unchanged.
                const reanchored = try self.allocator().create(Term);
                reanchored.* = .{ .node = v, .children = aligned.children };
                return reanchored;
            },
            .rule => |rule_just| {
                const rule = self.rules[rule_just.rule_slot];
                const pattern_in = if (edge.forward)
                    rule.match_side
                else
                    rule.target_side;
                const pattern_out = if (edge.forward)
                    rule.target_side
                else
                    rule.match_side;
                const needs_symm = if (edge.forward)
                    rule.reversed
                else
                    !rule.reversed;
                const before_node = if (edge.forward)
                    rule_just.from_node
                else
                    rule_just.to_node;
                const after_node = if (edge.forward)
                    rule_just.to_node
                else
                    rule_just.from_node;

                const binder_masks = try self.binderMasks(
                    rule,
                    rule_just.subst,
                );
                // Bag endpoints render against the edge's own nodes (the
                // extension members live there); tree endpoints keep the
                // class-anchored pattern rendering.
                var bag_info: ?Step.BagInfo = null;
                var lhs: *const Term = undefined;
                var rhs: *const Term = undefined;
                const before_is_bag =
                    self.eg.nodes.items[before_node].node == .bag;
                const after_is_bag =
                    self.eg.nodes.items[after_node].node == .bag;
                if (before_is_bag or after_is_bag) {
                    var matched_before: []const u32 = &.{};
                    var matched_after: []const u32 = &.{};
                    if (before_is_bag) {
                        const rendered = (try self.renderBag(
                            before_node,
                            pattern_in,
                            rule_just.subst,
                            binder_masks,
                            true,
                        )) orelse return null;
                        lhs = rendered.term;
                        matched_before = rendered.matched;
                    } else {
                        lhs = (try self.renderPattern(
                            self.eg.find(
                                self.eg.nodes.items[before_node].class,
                            ),
                            pattern_in,
                            rule_just.subst,
                            binder_masks,
                        )) orelse return null;
                    }
                    if (after_is_bag) {
                        const rendered = (try self.renderBag(
                            after_node,
                            pattern_out,
                            rule_just.subst,
                            binder_masks,
                            true,
                        )) orelse return null;
                        rhs = rendered.term;
                        matched_after = rendered.matched;
                    } else {
                        rhs = (try self.renderPattern(
                            self.eg.find(
                                self.eg.nodes.items[after_node].class,
                            ),
                            pattern_out,
                            rule_just.subst,
                            binder_masks,
                        )) orelse return null;
                    }
                    bag_info = .{
                        .matched_before = matched_before,
                        .matched_after = matched_after,
                    };
                } else {
                    const class = self.eg.find(
                        self.eg.nodes.items[current.node].class,
                    );
                    lhs = (try self.renderPattern(
                        class,
                        pattern_in,
                        rule_just.subst,
                        binder_masks,
                    )) orelse return null;
                    rhs = (try self.renderPattern(
                        class,
                        pattern_out,
                        rule_just.subst,
                        binder_masks,
                    )) orelse return null;
                }
                if (!try self.explainTerms(current, lhs, pos)) return null;

                const bindings = try self.allocator().alloc(
                    ?BindingValue,
                    rule.num_binders,
                );
                for (rule_just.subst, 0..) |maybe_binding, idx| {
                    const binding = maybe_binding orelse {
                        bindings[idx] = null;
                        continue;
                    };
                    bindings[idx] = switch (binding) {
                        .class => |c| .{
                            .term = (try self.classTerm(
                                c,
                                binder_masks[idx],
                            )) orelse {
                                return null;
                            },
                        },
                        .bound => |leaf| .{ .bound = leaf },
                    };
                }
                try self.steps.append(self.allocator(), .{
                    .source = .{ .rule = rule.rule_id },
                    .needs_symm = needs_symm,
                    .position = pos,
                    .before = lhs,
                    .after = rhs,
                    .bindings = bindings,
                    .bag = bag_info,
                });
                return rhs;
            },
            .pool_equation => |eq| {
                // The seeded side terms are the step endpoints verbatim:
                // the lowering cites the pool entry's exact formula, so no
                // representative substitution is allowed here. Bag members
                // re-sort as unions land, so re-pair the seed-time children
                // with their nodes' current member order first (children
                // are kept verbatim — only the pairing moves).
                const before = (try self.refreshSeedTerm(
                    if (edge.forward) eq.lhs else eq.rhs,
                )) orelse return null;
                const after = (try self.refreshSeedTerm(
                    if (edge.forward) eq.rhs else eq.lhs,
                )) orelse return null;
                if (!try self.explainTerms(current, before, pos)) {
                    return null;
                }
                try self.steps.append(self.allocator(), .{
                    .source = .{ .pool_equation = eq.pool_index },
                    .needs_symm = !edge.forward,
                    .position = pos,
                    .before = before,
                    .after = after,
                    .bindings = &.{},
                });
                return after;
            },
        }
    }

    /// Per-binder avoid-mask ids for one admitted rule edge, derived from
    /// the rule's restrictions and the edge's substitution: a restricted
    /// term binder must render a representative avoiding the atoms its
    /// paired bound binders were instantiated with.
    fn binderMasks(
        self: *ExplainCtx,
        rule: Rule,
        subst: []const ?Child,
    ) ![]const u32 {
        const masks = try self.allocator().alloc(u32, rule.num_binders);
        @memset(masks, 0);
        if (rule.restrictions.len == 0) return masks;
        for (0..rule.num_binders) |slot| {
            var atoms: std.ArrayListUnmanaged(LeafId) = .{};
            for (rule.restrictions) |restriction| {
                if (restriction.term_slot != slot) continue;
                const binding = subst[restriction.bound_slot] orelse continue;
                if (binding != .bound) continue;
                if (maskContains(atoms.items, binding.bound)) continue;
                try atoms.append(self.allocator(), binding.bound);
            }
            if (atoms.items.len == 0) continue;
            std.mem.sort(LeafId, atoms.items, {}, std.sort.asc(LeafId));
            masks[slot] = try self.internMask(atoms.items);
        }
        return masks;
    }

    const RenderedBag = struct {
        term: *const Term,
        /// Sorted member indices the pattern instance covers; the
        /// complement is the extension.
        matched: []const u32,
    };

    /// Render a rule-side instance over a bag node: each flattened
    /// pattern member claims the bag member position(s) its instance
    /// denotes (a binder bound to a sub-bag claims each of that sub-bag's
    /// members individually), and leftover members — the extension —
    /// render as mask-0 representatives. `allow_leftover` is false below
    /// the rewrite root, where a pattern must cover its bag exactly.
    fn renderBag(
        self: *ExplainCtx,
        bag_node: ENodeId,
        pattern: TemplateExpr,
        subst: []const ?Child,
        binder_masks: []const u32,
        allow_leftover: bool,
    ) error{OutOfMemory}!?RenderedBag {
        const bag = self.eg.nodes.items[bag_node].node.bag;
        var flat: std.ArrayListUnmanaged(TemplateExpr) = .{};
        try self.eg.flattenPattern(self.allocator(), bag.term_id, pattern, &flat);
        const children = try self.allocator().alloc(
            ?*const Term,
            bag.members.len,
        );
        @memset(children, null);
        var matched: std.ArrayListUnmanaged(u32) = .{};
        for (flat.items) |pm| {
            if (!try self.claimBagMembers(
                bag,
                children,
                &matched,
                pm,
                subst,
                binder_masks,
            )) {
                return null;
            }
        }
        for (children, bag.members) |*child, member| {
            if (child.* != null) continue;
            if (!allow_leftover) return null;
            child.* = (try self.classTerm(member, 0)) orelse return null;
        }
        const term = try self.allocator().create(Term);
        term.* = .{ .node = bag_node, .children = children };
        std.mem.sort(u32, matched.items, {}, std.sort.asc(u32));
        return .{ .term = term, .matched = matched.items };
    }

    /// Claim and render the member position(s) covered by one flattened
    /// pattern member's instance.
    fn claimBagMembers(
        self: *ExplainCtx,
        bag: ENode.Bag,
        children: []?*const Term,
        matched: *std.ArrayListUnmanaged(u32),
        pm: TemplateExpr,
        subst: []const ?Child,
        binder_masks: []const u32,
    ) error{OutOfMemory}!bool {
        const inst = (try self.eg.instantiate(pm, subst)) orelse {
            return false;
        };
        const root = self.eg.find(inst.class);
        for (bag.members, 0..) |member, idx| {
            if (children[idx] != null) continue;
            if (self.eg.find(member) != root) continue;
            children[idx] = switch (pm) {
                .binder => |b| (try self.bindingTerm(
                    subst[b] orelse return false,
                    binder_masks[b],
                )) orelse return false,
                .app => (try self.renderPattern(
                    root,
                    pm,
                    subst,
                    binder_masks,
                )) orelse return false,
            };
            try matched.append(self.allocator(), @intCast(idx));
            return true;
        }
        // A binder bound to a sub-bag (residual binding) spans several
        // members; claim each individually with the binder's mask.
        if (pm != .binder) return false;
        const mask_id = binder_masks[pm.binder];
        const sub_node = self.eg.bag_in_class.get(
            EGraph.bagKey(bag.term_id, root),
        ) orelse return false;
        const sub_members = self.eg.nodes.items[sub_node].node.bag.members;
        for (sub_members) |sub_member| {
            const sub_root = self.eg.find(sub_member);
            var claimed = false;
            for (bag.members, 0..) |member, idx| {
                if (children[idx] != null) continue;
                if (self.eg.find(member) != sub_root) continue;
                children[idx] = (try self.classTerm(
                    sub_member,
                    mask_id,
                )) orelse return false;
                try matched.append(self.allocator(), @intCast(idx));
                claimed = true;
                break;
            }
            if (!claimed) return false;
        }
        return true;
    }

    /// Render a pattern instance as a resolved term. A bare binder renders
    /// its binding; an application finds a member node of `class` matching
    /// the pattern under the substitution (first member in id order) so
    /// the term is anchored on real graph nodes.
    fn renderPattern(
        self: *ExplainCtx,
        class: EClassId,
        pattern: TemplateExpr,
        subst: []const ?Child,
        binder_masks: []const u32,
    ) error{OutOfMemory}!?*const Term {
        switch (pattern) {
            .binder => |binder_idx| {
                const binding = subst[binder_idx] orelse return null;
                return try self.bindingTerm(binding, binder_masks[binder_idx]);
            },
            .app => |pattern_app| {
                const root = self.eg.find(class);
                const members = self.eg.class_index.get(root) orelse {
                    return null;
                };
                member: for (members.items) |member_id| {
                    const member = switch (self.eg.nodes.items[member_id].node) {
                        .app => |app| app,
                        .leaf => continue,
                        .bag => |member_bag| {
                            // A same-head pattern against a bag member:
                            // exact-cover instance rendering.
                            if (member_bag.term_id != pattern_app.term_id) {
                                continue;
                            }
                            const rendered = (try self.renderBag(
                                member_id,
                                pattern,
                                subst,
                                binder_masks,
                                false,
                            )) orelse continue;
                            return rendered.term;
                        },
                    };
                    if (member.term_id != pattern_app.term_id) continue;
                    if (member.children.len != pattern_app.args.len) continue;
                    const children = try self.allocator().alloc(
                        ?*const Term,
                        member.children.len,
                    );
                    for (
                        pattern_app.args,
                        member.children,
                        0..,
                    ) |sub_pattern, child, idx| {
                        switch (child) {
                            .bound => |leaf| {
                                const binder_idx = switch (sub_pattern) {
                                    .binder => |b| b,
                                    .app => continue :member,
                                };
                                const binding = subst[binder_idx] orelse {
                                    continue :member;
                                };
                                if (binding != .bound or
                                    binding.bound != leaf)
                                {
                                    continue :member;
                                }
                                children[idx] = null;
                            },
                            .class => |child_class| {
                                switch (sub_pattern) {
                                    .binder => |b| {
                                        const binding = subst[b] orelse {
                                            continue :member;
                                        };
                                        if (!self.eg.bindingsCompatible(
                                            binding,
                                            .{ .class = child_class },
                                        )) continue :member;
                                        children[idx] = (try self.bindingTerm(
                                            binding,
                                            binder_masks[b],
                                        )) orelse continue :member;
                                    },
                                    .app => {
                                        children[idx] =
                                            (try self.renderPattern(
                                                child_class,
                                                sub_pattern,
                                                subst,
                                                binder_masks,
                                            )) orelse continue :member;
                                    },
                                }
                            },
                        }
                    }
                    const term = try self.allocator().create(Term);
                    term.* = .{ .node = member_id, .children = children };
                    return term;
                }
                return null;
            },
        }
    }

    /// The representative term of a binding: the binder's step-consistent
    /// rendering (class extraction under the binder's avoid-mask for
    /// class bindings, the atom's own leaf node for bound bindings used
    /// in term positions).
    fn bindingTerm(
        self: *ExplainCtx,
        binding: Child,
        mask_id: u32,
    ) error{OutOfMemory}!?*const Term {
        switch (binding) {
            .class => |c| return try self.classTerm(c, mask_id),
            .bound => |leaf| {
                const node_id = (try self.eg.lookupNode(
                    .{ .leaf = leaf },
                )) orelse return null;
                const term = try self.allocator().create(Term);
                term.* = .{ .node = node_id, .children = &.{} };
                return term;
            },
        }
    }
};


test {
    _ = @import("egraph/tests.zig");
}
