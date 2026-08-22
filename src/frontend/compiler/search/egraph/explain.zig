//! Explanation extraction for the `conversion?` egraph: renders the
//! union-forest path between two resolved terms as a sequence of
//! single-rule rewrite `Step`s. `EGraph.explain` (in `egraph.zig`) is the
//! entry point; it builds an `ExplainCtx` over the saturated graph and the
//! rule slice. The step vocabulary defined here (`Term`, `Step`,
//! `BindingValue`, `ExplainOptions`) is re-exported by `egraph.zig`, so
//! drivers keep a single egraph import.

const std = @import("std");
const TemplateExpr = @import("../../../rules.zig").TemplateExpr;

const eg_mod = @import("../egraph.zig");
const EGraph = eg_mod.EGraph;
const EClassId = eg_mod.EClassId;
const ENodeId = eg_mod.ENodeId;
const LeafId = eg_mod.LeafId;
const Child = eg_mod.Child;
const ENode = eg_mod.ENode;
const Rule = eg_mod.Rule;
const Justification = eg_mod.Justification;
const SpliceJust = eg_mod.SpliceJust;
const SpliceExpansion = eg_mod.SpliceExpansion;
const ExplEdge = eg_mod.ExplEdge;
const justEndpoints = eg_mod.justEndpoints;

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
        /// A splice-edge re-tree: `before` and `after` are the same member
        /// multiset grouped differently; the lowering is a pure AC
        /// alignment (no theorem cited).
        ac_flatten,
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
    /// Total route attempts across the extraction. Failed routes roll
    /// their steps back (so `max_steps` does not bound cumulative work),
    /// and each failing pair retries up to two detours — an adversarial
    /// nest of failing pairs could otherwise branch exponentially. Far
    /// above any legitimate chain (which needs about one attempt per
    /// alignment).
    max_routes: usize = 4096,
};

const Traversed = struct {
    just: Justification,
    /// True when the traversal runs the justification's semantic direction
    /// (endpoint a -> endpoint b).
    forward: bool,
};

const AlignKey = struct {
    from: ENodeId,
    to: ENodeId,
};

pub const ExplainCtx = struct {
    eg: *EGraph,
    rules: []const Rule,
    opts: ExplainOptions,
    steps: std.ArrayListUnmanaged(Step) = .{},
    depth: usize = 0,
    /// Route attempts consumed (successful and rolled-back alike); see
    /// `ExplainOptions.max_routes`.
    routes: usize = 0,
    /// (from node, to node) alignment subgoals currently active on the
    /// recursion stack. Re-entering the same node-pair means the forest-path /
    /// re-anchoring is circling a cyclic e-class (idempotence / absorption
    /// unions merge a class into a same-head compound containing itself);
    /// cutting the re-entry keeps extraction well-founded.
    active: std.AutoHashMapUnmanaged(AlignKey, void) = .{},
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
    /// Per-binder term overrides for the rule edge currently rendering
    /// its endpoints (null outside `renderRuleEndpoints`). A residual
    /// binder claimed member-wise as a same-head sub-bag must render as
    /// that exact bag term EVERYWHERE in the edge — endpoint children,
    /// the opposite endpoint's pattern rendering, and the step bindings —
    /// or the lowering's rule-instance seam cannot align (the class's
    /// minimal representative may not even share the bag's head).
    rule_binder_terms: ?[]?*const Term = null,
    /// Root of the class the currently-rendering rule edge lives in
    /// (null outside `renderRuleEndpoints`). Bindings that land in this
    /// class are self-referential — see `selfRefBindingTerm`.
    edge_self_root: ?EClassId = null,
    /// Lazily built undirected adjacency over forest + alternate edges;
    /// see `routeAdj`.
    route_adj: ?[]std.ArrayListUnmanaged(RouteEdge) = null,
    /// Lazily computed per-rule-slot single-orientation flags; see
    /// `ruleDirected`.
    rule_directed: ?[]const bool = null,
    /// Reused `weightedPath` scratch (one distance/backlink slot per
    /// node); allocated once, wiped per call — the weighted search runs
    /// on every alignment.
    dijkstra: ?struct {
        dist: []usize,
        prev: []?WeightedPrev,
    } = null,

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
                    // Mirrors the dep gate's `leafAvoids`: a leaf is
                    // masked out when it IS a masked atom or its declared
                    // deps include one (a `(m: tm y)` theorem variable
                    // never renders where y must be avoided).
                    .leaf => |leaf| for (atoms) |atom| {
                        if (!self.eg.leafAvoids(leaf, atom)) {
                            continue :node_loop;
                        }
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

    pub fn explainTerms(
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

        // Guard against re-entering the same node-pair alignment while it is
        // already on the recursion stack. Idempotence / absorption unions make
        // an e-class self-containing (a same-head compound whose child is the
        // class itself, e.g. `(hZ:x0)+(hZ:x0) = hZ:x0`); aligning the minimal
        // form to that compound then re-poses the identical `(from, to)`
        // subgoal one position deeper, expanding without bound. A genuinely
        // nested repeat of one node-pair only arises from such self-reference,
        // so cutting it keeps extraction well-founded (finite: at most one
        // active entry per ordered node-pair).
        const key = AlignKey{ .from = from.node, .to = to.node };
        if (self.active.contains(key)) return false;
        try self.active.put(self.allocator(), key, {});
        defer _ = self.active.remove(key);

        // Primary route: cheapest over the full recorded edge graph
        // (forest + no-op alternates), where cost prefers traversing
        // directed rules along their enrolled (reducing) direction. The
        // union forest's tree route is union-recording order and can
        // wander through expand/re-contract cycles the lowering then pays
        // for line by line; the weighted route states the same conversion
        // through the reductions the big-step grouping can absorb.
        const path = (try self.weightedPath(from.node, to.node)) orelse {
            return false;
        };
        const mark = self.steps.items.len;
        if (try self.processPath(from, to, path, pos)) return true;
        self.steps.shrinkRetainingCapacity(mark);

        // A route can be inherently circular on a self-containing class:
        // an edge on the path re-poses the path's own endpoints as its
        // child obligation (e.g. an assoc instance whose subterm slot
        // holds the very sum being aligned). Retry with the forest's tree
        // route, then the BFS-shortest route — a differently-shaped
        // detour is exactly what escapes the circularity.
        const tree = try self.forestPath(from.node, to.node);
        if (tree != null and !sameRoute(path, tree.?)) {
            if (try self.processPath(from, to, tree.?, pos)) return true;
            self.steps.shrinkRetainingCapacity(mark);
        }
        const alt = (try self.bfsPath(from.node, to.node)) orelse return false;
        if (sameRoute(path, alt)) return false;
        if (tree != null and sameRoute(tree.?, alt)) return false;
        if (try self.processPath(from, to, alt, pos)) return true;
        self.steps.shrinkRetainingCapacity(mark);
        return false;
    }

    /// Process one route's edges in order, then close the residual gap to
    /// `to`. Anchored endpoints keep the running term's node in lockstep
    /// with the route vertices, so the closing call reduces to the
    /// shape-equal fast path; it is a real re-alignment only when an
    /// endpoint fell back to class-anchored rendering.
    fn processPath(
        self: *ExplainCtx,
        from: *const Term,
        to: *const Term,
        path: []const Traversed,
        pos: []const u32,
    ) error{OutOfMemory}!bool {
        self.routes += 1;
        if (self.routes > self.opts.max_routes) return false;
        var current = from;
        for (path) |edge| {
            current = (try self.processEdge(current, edge, pos)) orelse {
                return false;
            };
        }
        return try self.explainTerms(current, to, pos);
    }

    const RouteEdge = struct {
        just: Justification,
        /// Traversal along this entry runs the justification's semantic
        /// direction (endpoint a -> endpoint b).
        forward: bool,
        to: ENodeId,
    };

    /// Undirected adjacency over the full recorded edge graph (forest +
    /// alternates); materialized only when a tree path fails.
    fn routeAdj(
        self: *ExplainCtx,
    ) error{OutOfMemory}![]std.ArrayListUnmanaged(RouteEdge) {
        if (self.route_adj) |adj| return adj;
        const adj = try self.allocator().alloc(
            std.ArrayListUnmanaged(RouteEdge),
            self.eg.nodes.items.len,
        );
        @memset(adj, .{});
        for (self.eg.expl_parent.items) |maybe_edge| {
            const edge = maybe_edge orelse continue;
            try self.addRouteEdge(adj, edge.just);
        }
        for (self.eg.alt_edges.items) |just| {
            try self.addRouteEdge(adj, just);
        }
        self.route_adj = adj;
        return adj;
    }

    fn addRouteEdge(
        self: *ExplainCtx,
        adj: []std.ArrayListUnmanaged(RouteEdge),
        just: Justification,
    ) error{OutOfMemory}!void {
        const ends = justEndpoints(just);
        try adj[ends.a].append(self.allocator(), .{
            .just = just,
            .forward = true,
            .to = ends.b,
        });
        try adj[ends.b].append(self.allocator(), .{
            .just = just,
            .forward = false,
            .to = ends.a,
        });
    }

    /// Shortest route between two same-class nodes over forest +
    /// alternate edges (deterministic: adjacency in recording order, FIFO
    /// traversal). Null when unreachable.
    fn bfsPath(
        self: *ExplainCtx,
        n1: ENodeId,
        n2: ENodeId,
    ) error{OutOfMemory}!?[]const Traversed {
        const adj = try self.routeAdj();
        const Prev = struct {
            from: ENodeId,
            just: Justification,
            forward: bool,
        };
        const prev = try self.allocator().alloc(?Prev, adj.len);
        @memset(prev, null);
        var queue: std.ArrayListUnmanaged(ENodeId) = .{};
        try queue.append(self.allocator(), n1);
        var head: usize = 0;
        search: while (head < queue.items.len) {
            const u = queue.items[head];
            head += 1;
            for (adj[u].items) |re| {
                if (re.to == n1 or prev[re.to] != null) continue;
                prev[re.to] = .{
                    .from = u,
                    .just = re.just,
                    .forward = re.forward,
                };
                if (re.to == n2) break :search;
                try queue.append(self.allocator(), re.to);
            }
        } else return null;
        var route: std.ArrayListUnmanaged(Traversed) = .{};
        var cursor = n2;
        while (cursor != n1) {
            const link = prev[cursor].?;
            try route.append(self.allocator(), .{
                .just = link.just,
                .forward = link.forward,
            });
            cursor = link.from;
        }
        std.mem.reverse(Traversed, route.items);
        return route.items;
    }

    /// Emission-cost heuristic for traversing one recorded edge. A
    /// directed rule (a `@compute` fold or a theorem enrolled in a
    /// single orientation) is cheap along its enrolled direction — a
    /// reducing step the big-step lowering can group with the debris it
    /// spawns — and expensive against it, where the lowering must
    /// interpose the relation's `symm` and any big-step group breaks.
    /// Everything else is plain route length.
    fn edgeCost(self: *ExplainCtx, re: RouteEdge) error{OutOfMemory}!usize {
        return switch (re.just) {
            .congruence, .splice => 1,
            .pool_equation => 2,
            .rule => |r| blk: {
                const directed = try self.ruleDirected();
                if (!directed[r.rule_slot]) break :blk 2;
                break :blk if (re.forward) 1 else 6;
            },
        };
    }

    /// Per rule slot: enrolled in one direction only. Both orientations
    /// of a `both` enrollment land as two slots sharing a `rule_id`;
    /// `@compute` rules are single-orientation by construction.
    fn ruleDirected(self: *ExplainCtx) error{OutOfMemory}![]const bool {
        if (self.rule_directed) |directed| return directed;
        const directed = try self.allocator().alloc(bool, self.rules.len);
        var counts: std.AutoHashMapUnmanaged(u32, u32) = .{};
        defer counts.deinit(self.allocator());
        for (self.rules) |rule| {
            const gop = try counts.getOrPut(self.allocator(), rule.rule_id);
            if (!gop.found_existing) gop.value_ptr.* = 0;
            gop.value_ptr.* += 1;
        }
        for (self.rules, 0..) |rule, idx| {
            directed[idx] = rule.compute or
                counts.get(rule.rule_id).? == 1;
        }
        self.rule_directed = directed;
        return directed;
    }

    const WeightedPrev = struct {
        from: ENodeId,
        just: Justification,
        forward: bool,
    };

    const WeightedItem = struct {
        cost: usize,
        /// Monotone discovery counter: deterministic tie-break, and
        /// equal-cost pops settle in discovery order.
        seq: usize,
        node: ENodeId,

        fn order(_: void, a: @This(), b: @This()) std.math.Order {
            if (a.cost != b.cost) return std.math.order(a.cost, b.cost);
            return std.math.order(a.seq, b.seq);
        }
    };

    /// Cheapest route between two same-class nodes over forest +
    /// alternate edges under `edgeCost` (Dijkstra; deterministic:
    /// adjacency in recording order, ties by discovery order). Null when
    /// unreachable.
    fn weightedPath(
        self: *ExplainCtx,
        n1: ENodeId,
        n2: ENodeId,
    ) error{OutOfMemory}!?[]const Traversed {
        const adj = try self.routeAdj();
        const alloc = self.allocator();
        if (self.dijkstra == null) {
            self.dijkstra = .{
                .dist = try alloc.alloc(usize, adj.len),
                .prev = try alloc.alloc(?WeightedPrev, adj.len),
            };
        }
        const dist = self.dijkstra.?.dist;
        @memset(dist, std.math.maxInt(usize));
        const prev = self.dijkstra.?.prev;
        @memset(prev, null);
        var queue = std.PriorityQueue(WeightedItem, void, WeightedItem.order)
            .init(alloc, {});
        defer queue.deinit();
        dist[n1] = 0;
        var seq: usize = 0;
        try queue.add(.{ .cost = 0, .seq = seq, .node = n1 });
        while (queue.removeOrNull()) |item| {
            if (item.cost > dist[item.node]) continue;
            if (item.node == n2) break;
            for (adj[item.node].items) |re| {
                const cost = item.cost + try self.edgeCost(re);
                if (cost >= dist[re.to]) continue;
                dist[re.to] = cost;
                prev[re.to] = .{
                    .from = item.node,
                    .just = re.just,
                    .forward = re.forward,
                };
                seq += 1;
                try queue.add(.{ .cost = cost, .seq = seq, .node = re.to });
            }
        }
        if (n1 != n2 and prev[n2] == null) return null;
        var route: std.ArrayListUnmanaged(Traversed) = .{};
        var cursor = n2;
        while (cursor != n1) {
            const link = prev[cursor].?;
            try route.append(alloc, .{
                .just = link.just,
                .forward = link.forward,
            });
            cursor = link.from;
        }
        std.mem.reverse(Traversed, route.items);
        return route.items;
    }

    fn sameRoute(a: []const Traversed, b: []const Traversed) bool {
        if (a.len != b.len) return false;
        for (a, b) |x, y| {
            if (x.forward != y.forward) return false;
            if (!sameJust(x.just, y.just)) return false;
        }
        return true;
    }

    fn sameJust(a: Justification, b: Justification) bool {
        if (std.meta.activeTag(a) != std.meta.activeTag(b)) return false;
        return switch (a) {
            .rule => |r| r.rule_slot == b.rule.rule_slot and
                r.from_node == b.rule.from_node and
                r.to_node == b.rule.to_node,
            .congruence => |c| c.left == b.congruence.left and
                c.right == b.congruence.right,
            .pool_equation => |eq| eq.pool_index ==
                b.pool_equation.pool_index,
            .splice => |sp| sp.from == b.splice.from and
                sp.to == b.splice.to,
        };
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
                // Two rendering attempts: the default representatives
                // first (keeps every previously-extracting chain
                // identical), then — only when aligning the chain onto
                // that rendering fails — a retry preferring the
                // newest-minimal member for bindings that land in the
                // edge's own class (see `selfRefBindingTerm`; vacuous
                // rewrites make such bindings self-referential and the
                // default representative circular).
                // The retry only exists for edges that HAVE a
                // self-referential binding; elsewhere a failed default
                // alignment must fall through to the caller's route-level
                // retry untouched.
                var has_self_ref = false;
                {
                    const edge_root = self.eg.find(
                        self.eg.nodes.items[before_node].class,
                    );
                    for (rule_just.subst) |maybe_binding| {
                        const binding = maybe_binding orelse continue;
                        if (binding != .class) continue;
                        if (self.eg.find(binding.class) == edge_root) {
                            has_self_ref = true;
                            break;
                        }
                    }
                }
                const max_attempts: usize =
                    if (has_self_ref) 2 else 1;
                const step_mark = self.steps.items.len;
                var rendered: RenderedEndpoints = undefined;
                var attempt: usize = 0;
                aligned: while (true) : (attempt += 1) {
                    if (attempt == max_attempts) return null;
                    self.steps.shrinkRetainingCapacity(step_mark);
                    rendered = (try self.renderRuleEndpoints(
                        rule,
                        pattern_in,
                        pattern_out,
                        before_node,
                        after_node,
                        rule_just.subst,
                        binder_masks,
                        if (current.node == before_node) current else null,
                        attempt == 1,
                    )) orelse return null;
                    if (try self.explainTerms(current, rendered.lhs, pos)) {
                        break :aligned;
                    }
                }
                const lhs = rendered.lhs;
                const rhs = rendered.rhs;

                const bindings = try self.allocator().alloc(
                    ?BindingValue,
                    rule.num_binders,
                );
                for (rule_just.subst, 0..) |maybe_binding, idx| {
                    if (rendered.overrides[idx]) |term| {
                        bindings[idx] = .{ .term = term };
                        continue;
                    }
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
                const bag_info = rendered.bag_info;
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
            .splice => |sp| {
                return try self.processSplice(current, sp, edge.forward, pos);
            },
        }
    }

    /// A splice edge: the nested node and its flat twin denote the same
    /// multiset once each expanded member is rewritten (in its own class)
    /// to the same-head bag it expanded through. The member rewrites are
    /// ordinary recursive explanations at the member position; the
    /// residual nested-vs-flat difference is one `.ac_flatten` step that
    /// lowers to a pure AC re-tree.
    fn processSplice(
        self: *ExplainCtx,
        current: *const Term,
        sp: SpliceJust,
        forward: bool,
        pos: []const u32,
    ) error{OutOfMemory}!?*const Term {
        const anchor_node = if (forward) sp.from else sp.to;
        const result_node = if (forward) sp.to else sp.from;
        var aligned = current;
        if (!nodeShapeEql(self.eg, aligned.node, anchor_node)) {
            const anchor = (try self.termForNode(anchor_node, 0)) orelse {
                return null;
            };
            if (!try self.explainTerms(aligned, anchor, pos)) return null;
            aligned = anchor;
        }
        const anchor_bag = switch (self.eg.nodes.items[aligned.node].node) {
            .bag => |bag| bag,
            else => return null,
        };
        if (forward) {
            // Nested -> flat. Pair the anchored children with the snapshot
            // members by class, rewrite each expanded child to its
            // expansion term, then flatten.
            const map = (try self.pairSnapshot(
                anchor_bag.members,
                sp.members,
            )) orelse return null;
            const children = try self.allocator().alloc(
                ?*const Term,
                anchor_bag.members.len,
            );
            var leaves: std.ArrayListUnmanaged(*const Term) = .{};
            var leaf_roots: std.ArrayListUnmanaged(EClassId) = .{};
            for (anchor_bag.members, 0..) |member, idx| {
                const child = aligned.children[idx].?;
                const exp = sp.expansion[map[idx]] orelse {
                    children[idx] = child;
                    try leaves.append(self.allocator(), child);
                    try leaf_roots.append(
                        self.allocator(),
                        self.eg.find(member),
                    );
                    continue;
                };
                const target = (try self.expansionTerm(exp)) orelse {
                    return null;
                };
                if (!termEql(self.eg, child, target)) {
                    const child_pos = try self.pushPos(pos, @intCast(idx));
                    if (!try self.explainTerms(child, target, child_pos)) {
                        return null;
                    }
                }
                children[idx] = target;
                if (!try self.expansionLeaves(
                    exp,
                    target,
                    &leaves,
                    &leaf_roots,
                )) return null;
            }
            const nested = try self.allocator().create(Term);
            nested.* = .{ .node = aligned.node, .children = children };
            const flat = (try self.pairFlatChildren(
                result_node,
                leaves.items,
                leaf_roots.items,
            )) orelse return null;
            try self.steps.append(self.allocator(), .{
                .source = .ac_flatten,
                .needs_symm = false,
                .position = pos,
                .before = nested,
                .after = flat,
                .bindings = &.{},
            });
            return flat;
        }
        // Flat -> nested: rebuild the expansion trees, claiming the flat
        // children as leaves (terms are reused verbatim; only the
        // grouping changes).
        const claimed = try self.allocator().alloc(bool, aligned.children.len);
        @memset(claimed, false);
        const from_members = self.eg.nodes.items[sp.from].node.bag.members;
        const map = (try self.pairSnapshot(
            from_members,
            sp.members,
        )) orelse return null;
        const children = try self.allocator().alloc(
            ?*const Term,
            from_members.len,
        );
        for (from_members, 0..) |member, idx| {
            children[idx] = if (sp.expansion[map[idx]]) |exp|
                (try self.regroupExpansion(exp, aligned, claimed)) orelse {
                    return null;
                }
            else
                (self.claimFlatLeaf(
                    self.eg.find(member),
                    aligned,
                    claimed,
                )) orelse return null;
        }
        for (claimed) |flag| if (!flag) return null;
        const nested = try self.allocator().create(Term);
        nested.* = .{ .node = sp.from, .children = children };
        try self.steps.append(self.allocator(), .{
            .source = .ac_flatten,
            .needs_symm = false,
            .position = pos,
            .before = aligned,
            .after = nested,
            .bindings = &.{},
        });
        return nested;
    }

    /// Pair a node's current member list against a mint-time snapshot:
    /// `out[i]` is the snapshot index covering current member `i`
    /// (leftmost-unused by class root — member lists re-sort in place as
    /// unions land, so positions move but the multiset of roots agrees).
    /// Null when they no longer correspond.
    fn pairSnapshot(
        self: *ExplainCtx,
        members: []const EClassId,
        snapshot: []const EClassId,
    ) error{OutOfMemory}!?[]const usize {
        if (members.len != snapshot.len) return null;
        const out = try self.allocator().alloc(usize, members.len);
        const used = try self.allocator().alloc(bool, snapshot.len);
        @memset(used, false);
        for (members, 0..) |member, idx| {
            const root = self.eg.find(member);
            out[idx] = for (snapshot, 0..) |snap, j| {
                if (used[j]) continue;
                if (self.eg.find(snap) == root) break j;
            } else return null;
            used[out[idx]] = true;
        }
        return out;
    }

    /// Rendered term of one expansion tree: the recorded same-head bag
    /// node with extraction representatives at kept members and deeper
    /// expansion terms below. Children parallel the node's CURRENT member
    /// order (the snapshot only classifies which members expanded).
    fn expansionTerm(
        self: *ExplainCtx,
        exp: *const SpliceExpansion,
    ) error{OutOfMemory}!?*const Term {
        const members = self.eg.nodes.items[exp.node].node.bag.members;
        const map = (try self.pairSnapshot(members, exp.members)) orelse {
            return null;
        };
        const children = try self.allocator().alloc(
            ?*const Term,
            members.len,
        );
        for (members, 0..) |member, idx| {
            children[idx] = if (exp.entries[map[idx]]) |deeper|
                (try self.expansionTerm(deeper)) orelse return null
            else
                (try self.classTerm(member, 0)) orelse return null;
        }
        const term = try self.allocator().create(Term);
        term.* = .{ .node = exp.node, .children = children };
        return term;
    }

    /// Collect the flat leaves of an expansion term (parallel walk of the
    /// expansion tree and its rendered term) with their class roots.
    fn expansionLeaves(
        self: *ExplainCtx,
        exp: *const SpliceExpansion,
        term: *const Term,
        leaves: *std.ArrayListUnmanaged(*const Term),
        leaf_roots: *std.ArrayListUnmanaged(EClassId),
    ) error{OutOfMemory}!bool {
        const members = self.eg.nodes.items[exp.node].node.bag.members;
        const map = (try self.pairSnapshot(
            members,
            exp.members,
        )) orelse return false;
        for (members, 0..) |member, idx| {
            if (exp.entries[map[idx]]) |deeper| {
                if (!try self.expansionLeaves(
                    deeper,
                    term.children[idx].?,
                    leaves,
                    leaf_roots,
                )) return false;
            } else {
                try leaves.append(self.allocator(), term.children[idx].?);
                try leaf_roots.append(
                    self.allocator(),
                    self.eg.find(member),
                );
            }
        }
        return true;
    }

    /// Pair collected leaves with the flat twin's current member order
    /// (leftmost-unused by class root).
    fn pairFlatChildren(
        self: *ExplainCtx,
        flat_node: ENodeId,
        leaves: []const *const Term,
        leaf_roots: []const EClassId,
    ) error{OutOfMemory}!?*const Term {
        const flat_members = self.eg.nodes.items[flat_node].node.bag.members;
        if (flat_members.len != leaves.len) return null;
        const children = try self.allocator().alloc(
            ?*const Term,
            flat_members.len,
        );
        @memset(children, null);
        for (leaves, leaf_roots) |leaf, root| {
            const slot = for (flat_members, 0..) |member, idx| {
                if (children[idx] != null) continue;
                if (self.eg.find(member) == root) break idx;
            } else return null;
            children[slot] = leaf;
        }
        const term = try self.allocator().create(Term);
        term.* = .{ .node = flat_node, .children = children };
        return term;
    }

    /// Rebuild one expansion tree from a flat term's children (reverse
    /// splice): leaves claim unclaimed flat children by class root.
    fn regroupExpansion(
        self: *ExplainCtx,
        exp: *const SpliceExpansion,
        flat: *const Term,
        claimed: []bool,
    ) error{OutOfMemory}!?*const Term {
        const children = try self.allocator().alloc(
            ?*const Term,
            exp.members.len,
        );
        for (exp.members, exp.entries, 0..) |member, entry, idx| {
            children[idx] = if (entry) |deeper|
                (try self.regroupExpansion(deeper, flat, claimed)) orelse {
                    return null;
                }
            else
                (self.claimFlatLeaf(
                    self.eg.find(member),
                    flat,
                    claimed,
                )) orelse return null;
        }
        const term = try self.allocator().create(Term);
        term.* = .{ .node = exp.node, .children = children };
        return term;
    }

    fn claimFlatLeaf(
        self: *ExplainCtx,
        root: EClassId,
        flat: *const Term,
        claimed: []bool,
    ) ?*const Term {
        const members = self.eg.nodes.items[flat.node].node.bag.members;
        for (members, 0..) |member, idx| {
            if (claimed[idx]) continue;
            if (self.eg.find(member) != root) continue;
            claimed[idx] = true;
            return flat.children[idx].?;
        }
        return null;
    }

    const RenderedEndpoints = struct {
        lhs: *const Term,
        rhs: *const Term,
        bag_info: ?Step.BagInfo,
        /// Edge-scoped binder term overrides (residual sub-bag claims);
        /// null entries fall back to the class representative.
        overrides: []?*const Term,
    };

    /// Render both endpoints of a rule edge, each anchored at the edge's
    /// exact recorded node (bag endpoints because the extension members
    /// live there; tree endpoints so edge processing stays in node-identity
    /// lockstep with the forest path — see `renderEndpointAt`). Rendering
    /// runs to a fixpoint over the binder overrides: a residual claim on
    /// one endpoint fixes the binder's term, and every other rendering of
    /// that binder must then be redone against it.
    fn renderRuleEndpoints(
        self: *ExplainCtx,
        rule: Rule,
        pattern_in: TemplateExpr,
        pattern_out: TemplateExpr,
        before_node: ENodeId,
        after_node: ENodeId,
        subst: []const ?Child,
        binder_masks: []const u32,
        seed: ?*const Term,
        prefer_newest_self_ref: bool,
    ) error{OutOfMemory}!?RenderedEndpoints {
        const overrides = try self.allocator().alloc(
            ?*const Term,
            rule.num_binders,
        );
        @memset(overrides, null);
        // Seed binder overrides from the chain's in-hand term: rendering
        // a binding via its class representative can pick a member from
        // ELSEWHERE in the chain when the binding's class merged into the
        // chain's own class (vacuous rewrites like `x + 0 = x` or
        // `sb x e a = e` union a node with its own child class), and the
        // resulting child obligation re-poses the alignment in flight —
        // a cycle the active-guard then kills. The in-hand subterm is
        // already rendered, mask-checked here, and denotes the same
        // class, so pinning it keeps the whole edge in lockstep with the
        // chain, exactly as node anchoring does for the endpoints.
        if (seed) |term| {
            self.seedOverridesFromTerm(
                pattern_in,
                term,
                subst,
                binder_masks,
                overrides,
            );
        }
        const saved = self.rule_binder_terms;
        self.rule_binder_terms = overrides;
        defer self.rule_binder_terms = saved;
        // Retry-only: mark the edge's own class while its endpoints
        // render, so a binding that lands THERE gets the newest-minimal
        // representative instead of the default oldest one — see
        // `selfRefBindingTerm` and the caller's two-attempt loop.
        const saved_root = self.edge_self_root;
        self.edge_self_root = if (prefer_newest_self_ref)
            self.eg.find(self.eg.nodes.items[before_node].class)
        else
            null;
        defer self.edge_self_root = saved_root;

        const before_is_bag =
            self.eg.nodes.items[before_node].node == .bag;
        const after_is_bag =
            self.eg.nodes.items[after_node].node == .bag;
        var pass: usize = 0;
        while (true) : (pass += 1) {
            var fills: usize = 0;
            for (overrides) |entry| fills += @intFromBool(entry != null);
            var bag_info: ?Step.BagInfo = null;
            var lhs: *const Term = undefined;
            var rhs: *const Term = undefined;
            if (before_is_bag or after_is_bag) {
                var matched_before: []const u32 = &.{};
                var matched_after: []const u32 = &.{};
                if (before_is_bag) {
                    const rendered = (try self.renderBag(
                        before_node,
                        pattern_in,
                        subst,
                        binder_masks,
                        true,
                    )) orelse return null;
                    lhs = rendered.term;
                    matched_before = rendered.matched;
                } else {
                    lhs = (try self.renderEndpointAt(
                        before_node,
                        pattern_in,
                        subst,
                        binder_masks,
                    )) orelse return null;
                }
                if (after_is_bag) {
                    const rendered = (try self.renderBag(
                        after_node,
                        pattern_out,
                        subst,
                        binder_masks,
                        true,
                    )) orelse return null;
                    rhs = rendered.term;
                    matched_after = rendered.matched;
                } else {
                    rhs = (try self.renderEndpointAt(
                        after_node,
                        pattern_out,
                        subst,
                        binder_masks,
                    )) orelse return null;
                }
                bag_info = .{
                    .matched_before = matched_before,
                    .matched_after = matched_after,
                };
            } else {
                lhs = (try self.renderEndpointAt(
                    before_node,
                    pattern_in,
                    subst,
                    binder_masks,
                )) orelse return null;
                rhs = (try self.renderEndpointAt(
                    after_node,
                    pattern_out,
                    subst,
                    binder_masks,
                )) orelse return null;
            }
            var fills_after: usize = 0;
            for (overrides) |entry| fills_after += @intFromBool(entry != null);
            if (fills_after == fills or pass >= 4) {
                return .{
                    .lhs = lhs,
                    .rhs = rhs,
                    .bag_info = bag_info,
                    .overrides = overrides,
                };
            }
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
                .binder => |b| (try self.binderTerm(
                    b,
                    subst,
                    binder_masks,
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
        // Structured member whose re-instantiated class matches nothing:
        // instantiation canonicalizes with TODAY's splice state, which can
        // diverge from the fire-time state — a rule target that minted a
        // nested same-head sum spliced it away when the inner class was
        // bag-only, but by explain time that class has folded to a value
        // (gained a non-bag node, exempting it from splicing), so the
        // fresh interning lands in a class the union never touched. Fall
        // back to structure-matching the pattern against the recorded
        // members themselves.
        if (pm == .app) {
            for (bag.members, 0..) |member, idx| {
                if (children[idx] != null) continue;
                const member_root = self.eg.find(member);
                if (try self.renderPattern(
                    member_root,
                    pm,
                    subst,
                    binder_masks,
                )) |term| {
                    children[idx] = term;
                    try matched.append(self.allocator(), @intCast(idx));
                    return true;
                }
            }
            return false;
        }
        // A binder bound to a sub-bag (residual binding) spans several
        // members; claim each individually with the binder's mask. The
        // class may hold several same-head bag nodes (splice twins at
        // different depths); try each against the enclosing bag's members
        // and keep the first full claim. The winning decomposition is
        // recorded as the binder's edge-scoped term so every other
        // rendering of the binder in this edge matches it member-wise.
        const mask_id = binder_masks[pm.binder];
        if (self.rule_binder_terms) |overrides| {
            if (overrides[pm.binder]) |term| {
                return try self.claimTermMembers(bag, children, matched, term);
            }
        }
        const class_members = self.eg.class_index.get(root) orelse {
            return false;
        };
        candidate: for (class_members.items) |cand_id| {
            const sub = switch (self.eg.nodes.items[cand_id].node) {
                .bag => |sub| sub,
                else => continue,
            };
            if (sub.term_id != bag.term_id) continue;
            const mark = matched.items.len;
            const sub_terms = try self.allocator().alloc(
                ?*const Term,
                sub.members.len,
            );
            for (sub.members, 0..) |sub_member, sub_idx| {
                const sub_root = self.eg.find(sub_member);
                var claimed = false;
                for (bag.members, 0..) |member, idx| {
                    if (children[idx] != null) continue;
                    if (self.eg.find(member) != sub_root) continue;
                    const term = (try self.classTerm(
                        sub_member,
                        mask_id,
                    )) orelse return false;
                    children[idx] = term;
                    sub_terms[sub_idx] = term;
                    try matched.append(self.allocator(), @intCast(idx));
                    claimed = true;
                    break;
                }
                if (!claimed) {
                    for (matched.items[mark..]) |undo| {
                        children[undo] = null;
                    }
                    matched.shrinkRetainingCapacity(mark);
                    continue :candidate;
                }
            }
            if (self.rule_binder_terms) |overrides| {
                const term = try self.allocator().create(Term);
                term.* = .{ .node = cand_id, .children = sub_terms };
                overrides[pm.binder] = term;
            }
            return true;
        }
        return false;
    }

    /// Claim the enclosing bag's member positions covered by an already
    /// fixed sub-bag term (a binder override), reusing its child terms.
    fn claimTermMembers(
        self: *ExplainCtx,
        bag: ENode.Bag,
        children: []?*const Term,
        matched: *std.ArrayListUnmanaged(u32),
        term: *const Term,
    ) error{OutOfMemory}!bool {
        const sub = switch (self.eg.nodes.items[term.node].node) {
            .bag => |sub| sub,
            else => return false,
        };
        if (sub.term_id != bag.term_id) return false;
        for (sub.members, term.children) |sub_member, sub_child| {
            const sub_root = self.eg.find(sub_member);
            var claimed = false;
            for (bag.members, 0..) |member, idx| {
                if (children[idx] != null) continue;
                if (self.eg.find(member) != sub_root) continue;
                children[idx] = sub_child.?;
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
                return try self.binderTerm(binder_idx, subst, binder_masks);
            },
            .app => {
                const root = self.eg.find(class);
                const members = self.eg.class_index.get(root) orelse {
                    return null;
                };
                for (members.items) |member_id| {
                    if (try self.renderPatternAt(
                        member_id,
                        pattern,
                        subst,
                        binder_masks,
                    )) |term| return term;
                }
                return null;
            },
        }
    }

    /// Render an application pattern's instance anchored at one exact
    /// node. Null when this node does not instantiate the pattern under
    /// `subst` (class-anchored callers scan on to the next member).
    fn renderPatternAt(
        self: *ExplainCtx,
        node_id: ENodeId,
        pattern: TemplateExpr,
        subst: []const ?Child,
        binder_masks: []const u32,
    ) error{OutOfMemory}!?*const Term {
        const pattern_app = switch (pattern) {
            .app => |app| app,
            .binder => return null,
        };
        const member = switch (self.eg.nodes.items[node_id].node) {
            .app => |app| app,
            .leaf => return null,
            .bag => |member_bag| {
                // A same-head pattern against a bag member: exact-cover
                // instance rendering.
                if (member_bag.term_id != pattern_app.term_id) {
                    return null;
                }
                const rendered = (try self.renderBag(
                    node_id,
                    pattern,
                    subst,
                    binder_masks,
                    false,
                )) orelse return null;
                return rendered.term;
            },
        };
        if (member.term_id != pattern_app.term_id) return null;
        if (member.children.len != pattern_app.args.len) return null;
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
                        .app => return null,
                    };
                    const binding = subst[binder_idx] orelse {
                        return null;
                    };
                    if (binding != .bound or
                        binding.bound != leaf)
                    {
                        return null;
                    }
                    children[idx] = null;
                },
                .class => |child_class| {
                    switch (sub_pattern) {
                        .binder => |b| {
                            const binding = subst[b] orelse {
                                return null;
                            };
                            if (!self.eg.bindingsCompatible(
                                binding,
                                .{ .class = child_class },
                            )) return null;
                            children[idx] = (try self.binderTerm(
                                b,
                                subst,
                                binder_masks,
                            )) orelse return null;
                        },
                        .app => {
                            children[idx] =
                                (try self.renderPattern(
                                    child_class,
                                    sub_pattern,
                                    subst,
                                    binder_masks,
                                )) orelse return null;
                        },
                    }
                },
            }
        }
        const term = try self.allocator().create(Term);
        term.* = .{ .node = node_id, .children = children };
        return term;
    }

    /// Render a rule-edge endpoint anchored at the edge's exact recorded
    /// node. Anchoring keeps the running term's node identity in lockstep
    /// with the explanation-forest vertices, so every bridge call in edge
    /// processing short-circuits through its shape-equal fast path and
    /// descends only into strictly smaller children — the whole-term
    /// re-anchors that diverge on self-containing classes stay dead. Falls
    /// back to class-anchored rendering when the exact node cannot
    /// instantiate the pattern (the pre-anchoring behavior).
    fn renderEndpointAt(
        self: *ExplainCtx,
        node_id: ENodeId,
        pattern: TemplateExpr,
        subst: []const ?Child,
        binder_masks: []const u32,
    ) error{OutOfMemory}!?*const Term {
        switch (pattern) {
            .app => {
                if (try self.renderPatternAt(
                    node_id,
                    pattern,
                    subst,
                    binder_masks,
                )) |term| return term;
                return try self.renderPattern(
                    self.eg.find(self.eg.nodes.items[node_id].class),
                    pattern,
                    subst,
                    binder_masks,
                );
            },
            .binder => |b| {
                const rep = (try self.binderTerm(
                    b,
                    subst,
                    binder_masks,
                )) orelse return null;
                if (nodeShapeEql(self.eg, rep.node, node_id)) return rep;
                // An override already pinned (seeded from the in-hand
                // term, or by the other endpoint) WINS even off-anchor:
                // overwriting it here would desynchronize a side already
                // rendered with it — the render fixpoint only detects
                // fill-count growth, not overwrites — and the citation
                // would pair endpoints from two different members of the
                // binding's class. Anchor drift costs the caller a
                // residual re-alignment, which processPath handles.
                if (self.rule_binder_terms) |overrides| {
                    if (overrides[b] != null) return rep;
                }
                // A bare-binder endpoint whose class representative is not
                // the recorded vertex's shape (a self-containing class
                // folds the compound away): anchor at the vertex and pin
                // the binder override so the step's citation renders the
                // same term everywhere in this edge.
                const anchored = (try self.termForNode(
                    node_id,
                    binder_masks[b],
                )) orelse return rep;
                if (self.rule_binder_terms) |overrides| {
                    overrides[b] = anchored;
                }
                return anchored;
            },
        }
    }

    /// Walk `pattern` against an already-rendered term, pinning each
    /// term-position binder's first structural occurrence as its
    /// edge-scoped override — provided the subterm satisfies the
    /// binder's avoid-mask (a mask-violating subterm falls back to the
    /// class representative, which `ensureExtraction` mask-filters).
    /// Bound-position and already-pinned binders are skipped; a shape
    /// mismatch (spliced bag, drifted representative) skips silently.
    fn seedOverridesFromTerm(
        self: *ExplainCtx,
        pattern: TemplateExpr,
        term: *const Term,
        subst: []const ?Child,
        binder_masks: []const u32,
        overrides: []?*const Term,
    ) void {
        switch (pattern) {
            .binder => |b| {
                if (overrides[b] != null) return;
                const binding = subst[b] orelse return;
                if (binding != .class) return;
                // The walk can descend through a same-head member that
                // is NOT the one the match resolved, so this subterm may
                // sit in a different class than the recorded binding —
                // harvesting it would make the citation a different
                // (wrong) instance. Only class-consistent subterms pin.
                const term_root = self.eg.find(
                    self.eg.nodes.items[term.node].class,
                );
                if (self.eg.find(binding.class) != term_root) return;
                const atoms = self.maskAtoms(binder_masks[b]);
                if (!self.termAvoidsAtoms(term, atoms)) return;
                overrides[b] = term;
            },
            .app => |app| {
                const stored = self.eg.nodes.items[term.node].node;
                switch (stored) {
                    .app => |napp| {
                        if (napp.term_id != app.term_id) return;
                        if (app.args.len != term.children.len) return;
                        for (app.args, term.children) |arg, maybe_child| {
                            const child = maybe_child orelse continue;
                            self.seedOverridesFromTerm(
                                arg,
                                child,
                                subst,
                                binder_masks,
                                overrides,
                            );
                        }
                    },
                    .leaf, .bag => return,
                }
            },
        }
    }

    /// Whether a rendered term's denotation avoids every listed atom,
    /// counting declared leaf dependencies (`leafAvoids`).
    fn termAvoidsAtoms(
        self: *const ExplainCtx,
        term: *const Term,
        atoms: []const LeafId,
    ) bool {
        if (atoms.len == 0) return true;
        switch (self.eg.nodes.items[term.node].node) {
            .leaf => |leaf| {
                for (atoms) |atom| {
                    if (!self.eg.leafAvoids(leaf, atom)) return false;
                }
            },
            .app => |app| {
                for (app.children) |child| {
                    if (child != .bound) continue;
                    for (atoms) |atom| {
                        if (child.bound == atom) return false;
                    }
                }
                for (term.children) |maybe_child| {
                    const child = maybe_child orelse continue;
                    if (!self.termAvoidsAtoms(child, atoms)) return false;
                }
            },
            .bag => {
                for (term.children) |maybe_child| {
                    const child = maybe_child orelse return false;
                    if (!self.termAvoidsAtoms(child, atoms)) return false;
                }
            },
        }
        return true;
    }

    /// The rendering of rule binder `b` under the current edge: the
    /// edge-scoped override when one is active (see `rule_binder_terms`),
    /// else the binding's representative term.
    fn binderTerm(
        self: *ExplainCtx,
        b: usize,
        subst: []const ?Child,
        binder_masks: []const u32,
    ) error{OutOfMemory}!?*const Term {
        if (self.rule_binder_terms) |overrides| {
            if (overrides[b]) |term| return term;
        }
        const binding = subst[b] orelse return null;
        return try self.bindingTerm(binding, binder_masks[b]);
    }

    /// Representative for a rule-edge binding whose class IS the edge's
    /// own class: vacuous rewrites (`x + 0 = x`, `sb x e a = e`) union a
    /// node with its own child class, so the binding's class holds both
    /// the written side's tower and the value it reduced to. The default
    /// representative (oldest minimal member) is the written side there,
    /// and rendering it re-poses the tower currently being explained — a
    /// cycle the alignment guard kills. Among minimal-cost mask-avoiding
    /// members, prefer the NEWEST node: fold-minted values postdate the
    /// written tower. Children still render as default representatives.
    fn selfRefBindingTerm(
        self: *ExplainCtx,
        class: EClassId,
        mask_id: u32,
    ) error{OutOfMemory}!?*const Term {
        try self.ensureExtraction(mask_id);
        const root = self.eg.find(class);
        const atoms = self.maskAtoms(mask_id);
        var best: ?ENodeId = null;
        var best_cost: usize = 0;
        node_loop: for (self.eg.nodes.items, 0..) |stored, node_id| {
            if (self.eg.find(stored.class) != root) continue;
            var cost: usize = 1;
            switch (stored.node) {
                .leaf => |leaf| for (atoms) |atom| {
                    if (!self.eg.leafAvoids(leaf, atom)) {
                        continue :node_loop;
                    }
                },
                .app => |app| for (app.children) |child| switch (child) {
                    .bound => |leaf| if (maskContains(atoms, leaf)) {
                        continue :node_loop;
                    },
                    .class => |c| {
                        cost += self.class_cost.get(
                            maskedKey(self.eg.find(c), mask_id),
                        ) orelse continue :node_loop;
                    },
                },
                .bag => |bag| for (bag.members) |member| {
                    cost += self.class_cost.get(
                        maskedKey(self.eg.find(member), mask_id),
                    ) orelse continue :node_loop;
                },
            }
            if (best == null or cost < best_cost or
                (cost == best_cost and node_id > best.?))
            {
                best = @intCast(node_id);
                best_cost = cost;
            }
        }
        const node = best orelse return null;
        return try self.termForNode(node, mask_id);
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
            .class => |c| {
                if (self.edge_self_root) |root| {
                    if (self.eg.find(c) == root) {
                        return try self.selfRefBindingTerm(c, mask_id);
                    }
                }
                return try self.classTerm(c, mask_id);
            },
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
