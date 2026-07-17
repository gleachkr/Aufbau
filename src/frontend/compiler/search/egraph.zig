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

    pub const App = struct {
        term_id: u32,
        children: []const Child,
    };
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
        /// binder target).
        to_node: ENodeId,
        /// The substitution the match produced (indexed by rule binder).
        subst: []const ?Child,
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
};

pub const SaturateOptions = struct {
    max_iterations: usize = 16,
    max_nodes: usize = 10_000,
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
        const canon = try self.canonicalize(node);
        if (self.memo.get(canon)) |node_id| {
            return self.find(self.nodes.items[node_id].class);
        }
        const class: EClassId = @intCast(self.parents.items.len);
        try self.parents.append(self.allocator, class);
        const node_id: ENodeId = @intCast(self.nodes.items.len);
        try self.nodes.append(self.allocator, .{
            .node = canon,
            .class = class,
        });
        try self.class_node.append(self.allocator, node_id);
        try self.expl_parent.append(self.allocator, null);
        try self.memo.put(self.allocator, canon, node_id);
        if (canon == .leaf) {
            try self.leaf_classes.put(self.allocator, canon.leaf, class);
        }
        return class;
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
            for (self.nodes.items, 0..) |*stored, idx| {
                stored.class = self.find(stored.class);
                stored.node = try self.canonicalize(stored.node);
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
        _ = try self.rebuild();
        while (stats.iterations < opts.max_iterations) {
            stats.iterations += 1;
            try self.buildClassIndex();

            var matches: std.ArrayListUnmanaged(Match) = .{};
            const matched_nodes = self.nodes.items.len;
            for (0..matched_nodes) |node_id| {
                const app = switch (self.nodes.items[node_id].node) {
                    .app => |app| app,
                    .leaf => continue,
                };
                for (rules, 0..) |rule, rule_slot| {
                    const pattern = rule.match_side.app;
                    if (pattern.term_id != app.term_id) continue;
                    if (pattern.args.len != app.children.len) continue;
                    try self.matchRule(
                        rule,
                        @intCast(rule_slot),
                        @intCast(node_id),
                        &matches,
                    );
                }
            }

            var changed = false;
            for (matches.items) |m| {
                const target = (try self.instantiate(
                    rules[m.rule_slot].target_side,
                    m.subst,
                )) orelse continue;
                const from = self.find(self.nodes.items[m.root_node].class);
                const merged = try self.merge(from, target.class, .{
                    .rule = .{
                        .rule_slot = m.rule_slot,
                        .from_node = m.root_node,
                        .to_node = target.node,
                        .subst = m.subst,
                    },
                });
                if (merged) {
                    changed = true;
                    stats.unions_applied += 1;
                }
                if (self.nodes.items.len > opts.max_nodes) {
                    _ = try self.rebuild();
                    stats.outcome = .node_capped;
                    return stats;
                }
            }

            const grew = self.nodes.items.len != matched_nodes;
            const congr_changed = try self.rebuild();
            if (!changed and !grew and !congr_changed) {
                stats.outcome = .saturated;
                return stats;
            }
        }
        return stats;
    }

    fn canonicalize(self: *const EGraph, node: ENode) !ENode {
        switch (node) {
            .leaf => return node,
            .app => |app| {
                const children = try self.allocator.alloc(
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
        }
    }

    fn congruenceAllowed(self: *const EGraph, node: ENode) bool {
        return switch (node) {
            // Distinct leaves never share a canonical shape, and one leaf
            // is deduped at add time; defensive false.
            .leaf => false,
            .app => |app| self.congr_heads.contains(app.term_id),
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
    };

    fn matchRule(
        self: *EGraph,
        rule: Rule,
        rule_slot: u32,
        root_node: ENodeId,
        matches: *std.ArrayListUnmanaged(Match),
    ) !void {
        const pattern = rule.match_side.app;
        const node = self.nodes.items[root_node].node.app;
        const pairs = try self.allocator.alloc(PatternPair, pattern.args.len);
        for (pattern.args, node.children, 0..) |p, c, idx| {
            pairs[idx] = .{ .pattern = p, .child = c };
        }
        const subst = try self.allocator.alloc(?Child, rule.num_binders);
        @memset(subst, null);

        var solutions: std.ArrayListUnmanaged([]const ?Child) = .{};
        try self.solvePairs(pairs, 0, subst, &solutions);
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
    ) !void {
        if (idx == pairs.len) {
            const copy = try self.allocator.dupe(?Child, subst);
            try solutions.append(self.allocator, copy);
            return;
        }
        const pair = pairs[idx];
        switch (pair.pattern) {
            .binder => |binder_idx| {
                if (subst[binder_idx]) |existing| {
                    if (!self.bindingsCompatible(existing, pair.child)) {
                        return;
                    }
                    try self.solvePairs(pairs, idx + 1, subst, solutions);
                } else {
                    subst[binder_idx] = self.normalizeBinding(pair.child);
                    try self.solvePairs(pairs, idx + 1, subst, solutions);
                    subst[binder_idx] = null;
                }
            },
            .app => |pattern_app| switch (pair.child) {
                .bound => return,
                .class => |class| {
                    const root = self.find(class);
                    const members = self.class_index.get(root) orelse return;
                    for (members.items) |member_id| {
                        const member = switch (
                            self.nodes.items[member_id].node
                        ) {
                            .app => |app| app,
                            .leaf => continue,
                        };
                        if (member.term_id != pattern_app.term_id) continue;
                        if (member.children.len != pattern_app.args.len) {
                            continue;
                        }
                        const extended = try self.allocator.alloc(
                            PatternPair,
                            pattern_app.args.len + (pairs.len - idx - 1),
                        );
                        for (
                            pattern_app.args,
                            member.children,
                            0..,
                        ) |p, c, i| {
                            extended[i] = .{ .pattern = p, .child = c };
                        }
                        @memcpy(
                            extended[pattern_app.args.len..],
                            pairs[idx + 1 ..],
                        );
                        try self.solvePairs(extended, 0, subst, solutions);
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
        try ctx.computeExtraction();
        if (!try ctx.explainTerms(from, to, &.{})) return null;
        return ctx.steps.items;
    }
};

/// A resolved term: a concrete tree of graph nodes, one representative per
/// e-class hole. `children` parallels the node's children; entries are null
/// at bound positions (the atom is part of the node identity).
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

    source: Source,
    needs_symm: bool,
    /// Argument-index path from the formula root to the redex.
    position: []const u32,
    before: *const Term,
    after: *const Term,
    /// Indexed by rule binder; entries the rule never bound are null.
    bindings: []const ?BindingValue,
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
    /// Extraction state: minimal-size representative per class root.
    class_cost: std.AutoArrayHashMapUnmanaged(EClassId, usize) = .{},
    class_best: std.AutoArrayHashMapUnmanaged(EClassId, ENodeId) = .{},
    class_term: std.AutoArrayHashMapUnmanaged(EClassId, *const Term) = .{},

    fn allocator(self: *ExplainCtx) std.mem.Allocator {
        return self.eg.allocator;
    }

    /// Fixpoint pass computing, per class root, the minimal-size member
    /// node (ties broken by first node id). Well-founded by construction:
    /// a best node's children always have strictly smaller cost.
    fn computeExtraction(self: *ExplainCtx) !void {
        while (true) {
            var changed = false;
            node_loop: for (self.eg.nodes.items, 0..) |stored, node_id| {
                var cost: usize = 1;
                switch (stored.node) {
                    .leaf => {},
                    .app => |app| for (app.children) |child| {
                        switch (child) {
                            .bound => {},
                            .class => |c| {
                                const child_cost = self.class_cost.get(
                                    self.eg.find(c),
                                ) orelse continue :node_loop;
                                cost += child_cost;
                            },
                        }
                    },
                }
                const root = self.eg.find(stored.class);
                const gop = try self.class_cost.getOrPut(
                    self.allocator(),
                    root,
                );
                if (!gop.found_existing or cost < gop.value_ptr.*) {
                    gop.value_ptr.* = cost;
                    try self.class_best.put(
                        self.allocator(),
                        root,
                        @intCast(node_id),
                    );
                    changed = true;
                }
            }
            if (!changed) break;
        }
    }

    /// The extracted representative term of a class (memoized per root).
    fn classTerm(
        self: *ExplainCtx,
        class: EClassId,
    ) error{OutOfMemory}!?*const Term {
        const root = self.eg.find(class);
        if (self.class_term.get(root)) |term| return term;
        const best = self.class_best.get(root) orelse return null;
        const term = (try self.termForNode(best)) orelse return null;
        try self.class_term.put(self.allocator(), root, term);
        return term;
    }

    /// A resolved term with `node` at the top and extracted representatives
    /// below.
    fn termForNode(
        self: *ExplainCtx,
        node_id: ENodeId,
    ) error{OutOfMemory}!?*const Term {
        const node = self.eg.nodes.items[node_id].node;
        const children: []?*const Term = switch (node) {
            .leaf => &.{},
            .app => |app| blk: {
                const children = try self.allocator().alloc(
                    ?*const Term,
                    app.children.len,
                );
                for (app.children, 0..) |child, idx| {
                    children[idx] = switch (child) {
                        .bound => null,
                        .class => |c| (try self.classTerm(c)) orelse {
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
                    const anchor = (try self.termForNode(u)) orelse {
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

                const class = self.eg.find(
                    self.eg.nodes.items[current.node].class,
                );
                const lhs = (try self.renderPattern(
                    class,
                    pattern_in,
                    rule_just.subst,
                )) orelse return null;
                if (!try self.explainTerms(current, lhs, pos)) return null;
                const rhs = (try self.renderPattern(
                    class,
                    pattern_out,
                    rule_just.subst,
                )) orelse return null;

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
                            .term = (try self.classTerm(c)) orelse {
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
                });
                return rhs;
            },
            .pool_equation => |eq| {
                // The seeded side terms are the step endpoints verbatim:
                // the lowering cites the pool entry's exact formula, so no
                // representative substitution is allowed here.
                const before = if (edge.forward) eq.lhs else eq.rhs;
                const after = if (edge.forward) eq.rhs else eq.lhs;
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

    /// Render a pattern instance as a resolved term. A bare binder renders
    /// its binding; an application finds a member node of `class` matching
    /// the pattern under the substitution (first member in id order) so
    /// the term is anchored on real graph nodes.
    fn renderPattern(
        self: *ExplainCtx,
        class: EClassId,
        pattern: TemplateExpr,
        subst: []const ?Child,
    ) error{OutOfMemory}!?*const Term {
        switch (pattern) {
            .binder => |binder_idx| {
                const binding = subst[binder_idx] orelse return null;
                return try self.bindingTerm(binding);
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
                                        )) orelse continue :member;
                                    },
                                    .app => {
                                        children[idx] =
                                            (try self.renderPattern(
                                                child_class,
                                                sub_pattern,
                                                subst,
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
    /// rendering (class extraction for class bindings, the atom's own leaf
    /// node for bound bindings used in term positions).
    fn bindingTerm(
        self: *ExplainCtx,
        binding: Child,
    ) error{OutOfMemory}!?*const Term {
        switch (binding) {
            .class => |c| return try self.classTerm(c),
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

// ------------------------------------------------------------------------
// Tests
// ------------------------------------------------------------------------

const testing = std.testing;

const ADD: u32 = 1;
const F: u32 = 2;
const ALL: u32 = 3;

fn testAdd2(eg: *EGraph, term_id: u32, a: Child, b: Child) !EClassId {
    return eg.add(.{ .app = .{
        .term_id = term_id,
        .children = &.{ a, b },
    } });
}

test "egraph hashcons dedupes structurally equal nodes" {
    var arena_state = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena_state.deinit();
    var eg = EGraph.init(arena_state.allocator());

    const x = try eg.add(.{ .leaf = 10 });
    const y = try eg.add(.{ .leaf = 11 });
    const first = try testAdd2(&eg, ADD, .{ .class = x }, .{ .class = y });
    const classes_before = eg.parents.items.len;
    const second = try testAdd2(&eg, ADD, .{ .class = x }, .{ .class = y });
    try testing.expectEqual(first, second);
    try testing.expectEqual(classes_before, eg.parents.items.len);
    try testing.expectEqual(@as(usize, 3), eg.eNodeCount());
}

test "egraph rebuild closes congruence only for enrolled heads" {
    var arena_state = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena_state.deinit();

    // Enrolled: f(a) and f(b) merge once a ~ b.
    var eg = EGraph.init(arena_state.allocator());
    try eg.congr_heads.put(eg.allocator, F, {});
    const a = try eg.add(.{ .leaf = 1 });
    const b = try eg.add(.{ .leaf = 2 });
    const fa = try testAdd2(&eg, F, .{ .class = a }, .{ .class = a });
    const fb = try testAdd2(&eg, F, .{ .class = b }, .{ .class = b });
    try testing.expect(!eg.sameClass(fa, fb));
    _ = try eg.merge(a, b, .{ .congruence = .{ .left = 0, .right = 1 } });
    const ids_before = eg.parents.items.len;
    _ = try eg.rebuild();
    try testing.expect(eg.sameClass(fa, fb));
    // Rebuild reuses ids — the microegg pitfall.
    try testing.expectEqual(ids_before, eg.parents.items.len);

    // Not enrolled: same setup stays split.
    var eg2 = EGraph.init(arena_state.allocator());
    const a2 = try eg2.add(.{ .leaf = 1 });
    const b2 = try eg2.add(.{ .leaf = 2 });
    const fa2 = try testAdd2(&eg2, F, .{ .class = a2 }, .{ .class = a2 });
    const fb2 = try testAdd2(&eg2, F, .{ .class = b2 }, .{ .class = b2 });
    _ = try eg2.merge(a2, b2, .{ .congruence = .{ .left = 0, .right = 1 } });
    _ = try eg2.rebuild();
    try testing.expect(!eg2.sameClass(fa2, fb2));
}

test "egraph keeps bound-position children rigid" {
    var arena_state = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena_state.deinit();
    var eg = EGraph.init(arena_state.allocator());
    try eg.congr_heads.put(eg.allocator, ALL, {});
    try eg.bound_masks.put(eg.allocator, ALL, 0b01);

    const p = try eg.add(.{ .leaf = 20 });
    const q = try eg.add(.{ .leaf = 21 });
    // all x. p / all y. p: identical body class, different bound atom —
    // congruence must NOT merge them (no @congr lemma can).
    const all_x_p = try testAdd2(&eg, ALL, .{ .bound = 1 }, .{ .class = p });
    const all_y_p = try testAdd2(&eg, ALL, .{ .bound = 2 }, .{ .class = p });
    // all x. p / all x. q with p ~ q: same bound atom — merges.
    const all_x_q = try testAdd2(&eg, ALL, .{ .bound = 1 }, .{ .class = q });
    _ = try eg.merge(p, q, .{ .congruence = .{ .left = 0, .right = 1 } });
    _ = try eg.rebuild();
    try testing.expect(!eg.sameClass(all_x_p, all_y_p));
    try testing.expect(eg.sameClass(all_x_p, all_x_q));
}

const BINDER_A = TemplateExpr{ .binder = 0 };
const BINDER_B = TemplateExpr{ .binder = 1 };
const BINDER_C = TemplateExpr{ .binder = 2 };

fn app2(comptime term_id: u32, comptime a: TemplateExpr, comptime b: TemplateExpr) TemplateExpr {
    return .{ .app = .{ .term_id = term_id, .args = &.{ a, b } } };
}

// add(a, b) ~ add(b, a)
const COMM_MATCH = app2(ADD, BINDER_A, BINDER_B);
const COMM_TARGET = app2(ADD, BINDER_B, BINDER_A);
// add(add(a, b), c) ~ add(a, add(b, c))
const ASSOC_MATCH = app2(ADD, app2(ADD, BINDER_A, BINDER_B), BINDER_C);
const ASSOC_TARGET = app2(ADD, BINDER_A, app2(ADD, BINDER_B, BINDER_C));

const AC_RULES = [_]Rule{
    .{
        .rule_id = 100,
        .reversed = false,
        .match_side = ASSOC_MATCH,
        .target_side = ASSOC_TARGET,
        .num_binders = 3,
    },
    .{
        .rule_id = 100,
        .reversed = true,
        .match_side = ASSOC_TARGET,
        .target_side = ASSOC_MATCH,
        .num_binders = 3,
    },
    .{
        .rule_id = 101,
        .reversed = false,
        .match_side = COMM_MATCH,
        .target_side = COMM_TARGET,
        .num_binders = 2,
    },
};

test "egraph saturation applies a commutativity rule to fixpoint" {
    var arena_state = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena_state.deinit();
    var eg = EGraph.init(arena_state.allocator());
    try eg.congr_heads.put(eg.allocator, ADD, {});

    const x = try eg.add(.{ .leaf = 1 });
    const y = try eg.add(.{ .leaf = 2 });
    const xy = try testAdd2(&eg, ADD, .{ .class = x }, .{ .class = y });
    const yx = try testAdd2(&eg, ADD, .{ .class = y }, .{ .class = x });
    try testing.expect(!eg.sameClass(xy, yx));

    const stats = try eg.saturate(AC_RULES[2..], .{});
    try testing.expectEqual(SaturateOutcome.saturated, stats.outcome);
    try testing.expect(eg.sameClass(xy, yx));
    try testing.expect(!eg.sameClass(xy, x));
}

test "egraph binder consistency: idempotent contraction matches only squares" {
    var arena_state = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena_state.deinit();
    var eg = EGraph.init(arena_state.allocator());
    try eg.congr_heads.put(eg.allocator, ADD, {});

    // add(a, a) ~ a
    const idem = [_]Rule{.{
        .rule_id = 102,
        .reversed = false,
        .match_side = app2(ADD, BINDER_A, BINDER_A),
        .target_side = BINDER_A,
        .num_binders = 1,
    }};

    const x = try eg.add(.{ .leaf = 1 });
    const y = try eg.add(.{ .leaf = 2 });
    const xy = try testAdd2(&eg, ADD, .{ .class = x }, .{ .class = y });
    const xx = try testAdd2(&eg, ADD, .{ .class = x }, .{ .class = x });

    const stats = try eg.saturate(&idem, .{});
    try testing.expectEqual(SaturateOutcome.saturated, stats.outcome);
    try testing.expect(eg.sameClass(xx, x));
    try testing.expect(!eg.sameClass(xy, x));
    try testing.expect(!eg.sameClass(xy, y));
}

test "egraph node cap stops saturation with a capped outcome" {
    var arena_state = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena_state.deinit();
    var eg = EGraph.init(arena_state.allocator());
    try eg.congr_heads.put(eg.allocator, ADD, {});

    // add(a, b) ~ add(f(a, b), b): each round the F node lands in a fresh
    // class (F is not a rule head and not congruence-enrolled), so the
    // matched ADD class accrues a genuinely new member every iteration and
    // the node cap must trip. (An `add(a,b) ~ add(add(a,b),b)` rule would
    // NOT work here: the unrolling collapses into one cyclic e-class and
    // saturates — that is the egraph working as intended.)
    const grow = [_]Rule{.{
        .rule_id = 103,
        .reversed = false,
        .match_side = app2(ADD, BINDER_A, BINDER_B),
        .target_side = app2(ADD, app2(F, BINDER_A, BINDER_B), BINDER_B),
        .num_binders = 2,
    }};

    const x = try eg.add(.{ .leaf = 1 });
    const y = try eg.add(.{ .leaf = 2 });
    _ = try testAdd2(&eg, ADD, .{ .class = x }, .{ .class = y });

    const stats = try eg.saturate(&grow, .{ .max_nodes = 32 });
    try testing.expectEqual(SaturateOutcome.node_capped, stats.outcome);
}

/// Left-comb sum of `n` fresh leaves: add(x1, add(x2, ... add(x_{n-1}, x_n))).
fn seedSum(eg: *EGraph, n: u32) !EClassId {
    var acc = try eg.add(.{ .leaf = n });
    var i: u32 = n - 1;
    while (true) {
        const leaf = try eg.add(.{ .leaf = i });
        acc = try testAdd2(eg, ADD, .{ .class = leaf }, .{ .class = acc });
        if (i == 1) break;
        i -= 1;
    }
    return acc;
}

/// The microegg closed-form AC oracle: a sum of n variables under
/// assoc(both) + comm saturates to exactly 2^n - 1 e-classes and
/// 3^n - 2^(n+1) + 1 add-nodes plus n leaf nodes.
fn checkAcOracle(n: u32, opts: SaturateOptions) !void {
    var arena_state = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena_state.deinit();
    var eg = EGraph.init(arena_state.allocator());
    try eg.congr_heads.put(eg.allocator, ADD, {});

    _ = try seedSum(&eg, n);
    const stats = try eg.saturate(&AC_RULES, opts);
    try testing.expectEqual(SaturateOutcome.saturated, stats.outcome);

    const expected_classes = (std.math.pow(usize, 2, n)) - 1;
    const expected_nodes = std.math.pow(usize, 3, n) -
        std.math.pow(usize, 2, n + 1) + 1 + n;
    try testing.expectEqual(expected_classes, eg.classCount());
    try testing.expectEqual(expected_nodes, eg.eNodeCount());
}

// --- Explanation tests -------------------------------------------------

fn termClassOf(eg: *const EGraph, term: *const Term) EClassId {
    return eg.find(eg.nodes.items[term.node].class);
}

fn tLeaf(eg: *EGraph, leaf: u32) !*const Term {
    _ = try eg.add(.{ .leaf = leaf });
    const node = (try eg.lookupNode(.{ .leaf = leaf })).?;
    const term = try eg.allocator.create(Term);
    term.* = .{ .node = node, .children = &.{} };
    return term;
}

fn tApp2(
    eg: *EGraph,
    term_id: u32,
    a: *const Term,
    b: *const Term,
) !*const Term {
    const shape = ENode{ .app = .{ .term_id = term_id, .children = &.{
        .{ .class = termClassOf(eg, a) },
        .{ .class = termClassOf(eg, b) },
    } } };
    _ = try eg.add(shape);
    const node = (try eg.lookupNode(shape)).?;
    const children = try eg.allocator.alloc(?*const Term, 2);
    children[0] = a;
    children[1] = b;
    const term = try eg.allocator.create(Term);
    term.* = .{ .node = node, .children = children };
    return term;
}

/// Replay validator: apply each step's rewrite at its position, requiring
/// the redex to match `before` exactly. Returns the final term.
fn applyStepAt(
    eg: *EGraph,
    term: *const Term,
    position: []const u32,
    before: *const Term,
    after: *const Term,
) !?*const Term {
    if (position.len == 0) {
        if (!termEql(eg, term, before)) return null;
        return after;
    }
    const idx = position[0];
    const child = term.children[idx] orelse return null;
    const replaced = (try applyStepAt(
        eg,
        child,
        position[1..],
        before,
        after,
    )) orelse return null;
    const children = try eg.allocator.dupe(?*const Term, term.children);
    children[idx] = replaced;
    const rebuilt = try eg.allocator.create(Term);
    rebuilt.* = .{ .node = term.node, .children = children };
    return rebuilt;
}

fn applySteps(
    eg: *EGraph,
    from: *const Term,
    steps: []const Step,
) !?*const Term {
    var current = from;
    for (steps) |step| {
        current = (try applyStepAt(
            eg,
            current,
            step.position,
            step.before,
            step.after,
        )) orelse return null;
    }
    return current;
}

fn expectValidChain(
    eg: *EGraph,
    from: *const Term,
    to: *const Term,
    steps: []const Step,
) !void {
    const final = (try applySteps(eg, from, steps)) orelse {
        return error.ChainBroken;
    };
    try testing.expect(termEql(eg, final, to));
}

test "egraph explains a root commutativity step" {
    var arena_state = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena_state.deinit();
    var eg = EGraph.init(arena_state.allocator());
    try eg.congr_heads.put(eg.allocator, ADD, {});

    const x = try tLeaf(&eg, 1);
    const y = try tLeaf(&eg, 2);
    const from = try tApp2(&eg, ADD, x, y);
    const to = try tApp2(&eg, ADD, y, x);

    const rules = AC_RULES[2..];
    _ = try eg.saturate(rules, .{});
    const steps = (try eg.explain(rules, from, to, .{})) orelse {
        return error.ExpectedExplanation;
    };
    try testing.expectEqual(@as(usize, 1), steps.len);
    try testing.expectEqual(@as(u32, 101), steps[0].source.rule);
    try testing.expect(!steps[0].needs_symm);
    try testing.expectEqual(@as(usize, 0), steps[0].position.len);
    try expectValidChain(&eg, from, to, steps);
}

test "egraph explains a congruence-lifted step at a position" {
    var arena_state = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena_state.deinit();
    var eg = EGraph.init(arena_state.allocator());
    try eg.congr_heads.put(eg.allocator, ADD, {});
    try eg.congr_heads.put(eg.allocator, F, {});

    const x = try tLeaf(&eg, 1);
    const y = try tLeaf(&eg, 2);
    const z = try tLeaf(&eg, 3);
    const from = try tApp2(&eg, F, try tApp2(&eg, ADD, x, y), z);
    const to = try tApp2(&eg, F, try tApp2(&eg, ADD, y, x), z);

    const rules = AC_RULES[2..];
    _ = try eg.saturate(rules, .{});
    const steps = (try eg.explain(rules, from, to, .{})) orelse {
        return error.ExpectedExplanation;
    };
    try testing.expectEqual(@as(usize, 1), steps.len);
    try testing.expectEqualSlices(u32, &.{0}, steps[0].position);
    try expectValidChain(&eg, from, to, steps);
}

test "egraph explains bare-binder contraction in both directions" {
    var arena_state = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena_state.deinit();
    var eg = EGraph.init(arena_state.allocator());
    try eg.congr_heads.put(eg.allocator, ADD, {});

    // add(a, a) ~ a
    const idem = [_]Rule{.{
        .rule_id = 102,
        .reversed = false,
        .match_side = app2(ADD, BINDER_A, BINDER_A),
        .target_side = BINDER_A,
        .num_binders = 1,
    }};

    const x = try tLeaf(&eg, 1);
    const xx = try tApp2(&eg, ADD, x, x);
    _ = try eg.saturate(&idem, .{});

    // Forward: the contraction as annotated.
    const forward = (try eg.explain(&idem, xx, x, .{})) orelse {
        return error.ExpectedExplanation;
    };
    try testing.expectEqual(@as(usize, 1), forward.len);
    try testing.expect(!forward[0].needs_symm);
    try testing.expect(termEql(&eg, forward[0].after, x));
    try expectValidChain(&eg, xx, x, forward);
    // The binding renders the contracted class's representative.
    try testing.expect(forward[0].bindings[0] != null);
    try testing.expect(termEql(&eg, forward[0].bindings[0].?.term, x));

    // Reverse traversal: the same edge lowers through symm.
    const reverse = (try eg.explain(&idem, x, xx, .{})) orelse {
        return error.ExpectedExplanation;
    };
    try testing.expectEqual(@as(usize, 1), reverse.len);
    try testing.expect(reverse[0].needs_symm);
    try expectValidChain(&eg, x, xx, reverse);
}

test "egraph explains through a pool-equation ground union" {
    var arena_state = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena_state.deinit();
    var eg = EGraph.init(arena_state.allocator());
    try eg.congr_heads.put(eg.allocator, F, {});

    const x = try tLeaf(&eg, 1);
    const y = try tLeaf(&eg, 2);
    const fx = try tApp2(&eg, F, x, x);
    const fy = try tApp2(&eg, F, y, y);
    _ = try eg.merge(
        termClassOf(&eg, x),
        termClassOf(&eg, y),
        .{ .pool_equation = .{ .pool_index = 3, .lhs = x, .rhs = y } },
    );
    _ = try eg.saturate(&.{}, .{});
    try testing.expect(eg.sameClass(
        termClassOf(&eg, fx),
        termClassOf(&eg, fy),
    ));

    // Forward: both congruence positions rewrite x -> y, citing the pool
    // entry as-is.
    const forward = (try eg.explain(&.{}, fx, fy, .{})) orelse {
        return error.ExpectedExplanation;
    };
    try testing.expectEqual(@as(usize, 2), forward.len);
    for (forward) |step| {
        try testing.expectEqual(@as(u32, 3), step.source.pool_equation);
        try testing.expect(!step.needs_symm);
        try testing.expectEqual(@as(usize, 1), step.position.len);
    }
    try expectValidChain(&eg, fx, fy, forward);

    // Reverse traversal of the same edge needs symm.
    const reverse = (try eg.explain(&.{}, fy, fx, .{})) orelse {
        return error.ExpectedExplanation;
    };
    try testing.expectEqual(@as(usize, 2), reverse.len);
    for (reverse) |step| {
        try testing.expectEqual(@as(u32, 3), step.source.pool_equation);
        try testing.expect(step.needs_symm);
    }
    try expectValidChain(&eg, fy, fx, reverse);
}

test "egraph explains a two-step nested rewrite chain" {
    var arena_state = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena_state.deinit();
    var eg = EGraph.init(arena_state.allocator());
    try eg.congr_heads.put(eg.allocator, ADD, {});

    const x = try tLeaf(&eg, 1);
    const y = try tLeaf(&eg, 2);
    const z = try tLeaf(&eg, 3);
    const from = try tApp2(&eg, ADD, try tApp2(&eg, ADD, x, y), z);
    const to = try tApp2(&eg, ADD, z, try tApp2(&eg, ADD, y, x));

    const rules = AC_RULES[2..];
    _ = try eg.saturate(rules, .{});
    const steps = (try eg.explain(rules, from, to, .{})) orelse {
        return error.ExpectedExplanation;
    };
    try testing.expectEqual(@as(usize, 2), steps.len);
    try expectValidChain(&eg, from, to, steps);
}

test "egraph AC oracle: four-variable closed form" {
    try checkAcOracle(4, .{});
}

test "egraph AC oracle: seven-variable closed form" {
    try checkAcOracle(7, .{ .max_iterations = 64, .max_nodes = 1_000_000 });
}
