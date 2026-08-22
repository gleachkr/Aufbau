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
//!   rigid atoms, and the `@congr` lemmas require them identical on both
//!   sides. Alpha-equivalence is NOT primitive; `@conversion alpha`
//!   rules close specific renamings as ordinary theorem-instance unions
//!   via the pairing scheduler (`collectAlphaMatches`), so a class MAY
//!   hold binder nodes with different bound atoms once such a rule
//!   fires — code may not assume one bound atom per class.
//!
//! Every union records a justification edge (`unions`) for explanation
//! extraction. The whole structure lives for one search call and MUST be
//! allocated from a per-call arena: nothing here frees, and abandoned
//! buffers (canonicalization copies, the per-iteration class index) lean on
//! arena teardown.

const std = @import("std");
const TemplateExpr = @import("../../rules.zig").TemplateExpr;

const alpha_mod = @import("egraph/alpha.zig");
const explain_mod = @import("egraph/explain.zig");
const AlphaInstance = alpha_mod.AlphaInstance;

// Extraction vocabulary lives in `egraph/explain.zig`; re-exported here so
// drivers keep a single egraph import.
pub const Term = explain_mod.Term;
pub const termEql = explain_mod.termEql;
pub const BindingValue = explain_mod.BindingValue;
pub const Step = explain_mod.Step;
pub const ExplainOptions = explain_mod.ExplainOptions;

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
    /// True for a `@compute` enrollment: the rule is excluded from the
    /// general saturation match loop and applied only by the directed
    /// fold scheduler (`foldCompute`), which fires at most one
    /// designated redex per class per round. Bound binders ride the
    /// same dep gate as general rules (enrollment guarantees the match
    /// side binds every binder, so a fold never mints a fresh one); a
    /// dep-deferred designated redex stays unconsumed.
    compute: bool = false,
    /// True for a `@conversion alpha` enrollment: excluded from the
    /// general match loop (the target uses a binder the match side does
    /// not bind) and driven by the alpha pairing scheduler, which
    /// completes the substitution with an existing binder atom instead
    /// of inventing one. See `collectAlphaMatches`.
    alpha: bool = false,
    /// For an alpha rule: binder slot of the renamed (match-side) bound
    /// binder.
    alpha_old_slot: u32 = 0,
    /// For an alpha rule: binder slot of the fresh (target-only) bound
    /// binder the scheduler supplies.
    alpha_new_slot: u32 = 0,
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
    /// A rebuild splice: `to` is the flattened twin minted for `from` when
    /// a member class acquired a same-head bag. Stored nodes keep their
    /// member multiset for life (explanation edges reference them by
    /// shape), so the spliced canonical form becomes a separate node
    /// linked by this edge. The two sides denote the same member multiset
    /// once each expanded member is rewritten to its same-head bag; the
    /// residual difference is a pure AC re-tree.
    splice: SpliceJust,
};

pub const SpliceJust = struct {
    from: ENodeId,
    to: ENodeId,
    /// Snapshot of `from`'s member list at mint time, parallel to
    /// `expansion` (member lists re-sort in place as unions land, so
    /// explain-time pairing goes through this snapshot by class).
    members: []const EClassId,
    /// Per snapshot member: null = kept atomic in `to`, else the
    /// expansion tree it contributed.
    expansion: []const ?*const SpliceExpansion,
};

/// One level of a member-class expansion recorded when a splice twin is
/// minted: the same-head bag node the class expanded through, a snapshot
/// of that node's member list, and per-member deeper expansions. Mirrors
/// the `spliceInto` recursion that produced the twin's flat member list.
pub const SpliceExpansion = struct {
    node: ENodeId,
    members: []const EClassId,
    entries: []const ?*const SpliceExpansion,
};

/// Does `binder_idx` occur in `pattern` at a position that does NOT splice
/// into an enclosing `term_id` bag? Positions on the same-head binary spine
/// (starting `spliceable`) flatten away under bag interning; any other
/// position is structural.
fn binderOccursStructurally(
    pattern: TemplateExpr,
    term_id: u32,
    binder_idx: u32,
    spliceable: bool,
) bool {
    switch (pattern) {
        .binder => |b| return b == binder_idx and !spliceable,
        .app => |app| {
            const same_head = app.term_id == term_id and app.args.len == 2;
            for (app.args) |arg| {
                if (binderOccursStructurally(
                    arg,
                    term_id,
                    binder_idx,
                    spliceable and same_head,
                )) return true;
            }
            return false;
        },
    }
}

pub fn justEndpoints(just: Justification) struct { a: ENodeId, b: ENodeId } {
    return switch (just) {
        .rule => |rule| .{ .a = rule.from_node, .b = rule.to_node },
        .congruence => |congr| .{ .a = congr.left, .b = congr.right },
        .pool_equation => |eq| .{ .a = eq.lhs.node, .b = eq.rhs.node },
        .splice => |sp| .{ .a = sp.from, .b = sp.to },
    };
}

/// Order-insensitive key for an edge's endpoint node-pair (alt-edge
/// dedup and the re-fire edge marker share it).
fn nodePairKey(a: ENodeId, b: ENodeId) u64 {
    const lo = @min(a, b);
    const hi = @max(a, b);
    return (@as(u64, lo) << 32) | hi;
}

pub const UnionEdge = struct {
    a: EClassId,
    b: EClassId,
    just: Justification,
};

pub const ExplEdge = struct {
    to: ENodeId,
    just: Justification,
    /// True when the justification's semantic direction (endpoint a -> b)
    /// runs child -> parent along this link.
    forward: bool,
};

pub const SaturateOutcome = enum {
    saturated,
    iteration_capped,
    node_capped,
    /// A budget-capped iteration made no progress at all — no union, no
    /// node, no congruence repair, not even a newly recorded applied
    /// effect. Collection is deterministic, so every further iteration
    /// would re-enumerate the same capped frontier bit-for-bit: raising
    /// `iters:` cannot help. Still NOT a forced negative (the capped
    /// frontier was never fully explored).
    budget_fixpoint,
};

pub const SaturateStats = struct {
    outcome: SaturateOutcome,
    iterations: usize = 0,
    unions_applied: usize = 0,
    /// Matches refused by the dep gate this run. A nonzero count on a
    /// saturated miss means dependency constraints (not rule coverage)
    /// blocked at least one candidate union.
    dep_deferred: usize = 0,
    /// Match enumerations (tree `solvePairs` walks and AC bag
    /// assignments alike) truncated by the per-match or per-iteration
    /// budget this run, plus bag splices abandoned at
    /// `max_splice_members` (the node keeps its unspliced shape, so
    /// congruent joins only the flat form reveals are skipped). A
    /// nonzero count on a saturated miss means the miss is NOT a forced
    /// negative — some assignments were never tried.
    ac_match_capped: usize = 0,
    /// Cyclic `bag_in_class` entries dropped by rebuild passes this run.
    /// Dropping keeps member lists finite but forfeits some congruence
    /// merges, so a nonzero count on a saturated miss means the miss is
    /// NOT a forced negative in the AC quotient.
    ac_cyclic_dropped: usize = 0,
    /// Unions applied by the `@compute` fold scheduler this run (a
    /// subset of `unions_applied`). Zero with compute rules enrolled
    /// means the fold never found a redex.
    fold_applied: usize = 0,
    /// Unions applied from alpha-scheduler matches this run (a subset of
    /// `unions_applied`). Each is a literal instance of an `alpha` rule;
    /// the enrolled substitution rules and gated congruence close the
    /// rest of the renaming.
    alpha_applied: usize = 0,
    /// Alpha pairing-filter comparisons the run's FINAL collection pass
    /// resolved approximately (cycle-conservative memo reads, greedy bag
    /// alignment failures, truncated instance enumeration, renaming
    /// environments past `max_rename_depth`). Earlier
    /// passes don't count: an approximate or capped pass never commits
    /// to the settled cache, so its whole delta is re-derived — with
    /// fresh budget — by the next pass, and a saturated fixpoint's final
    /// pass (its own comparisons plus the exact committed verdicts it
    /// reuses) speaks for the whole run. Zero on a saturated outcome
    /// means the alpha filter was exact and the miss is a forced
    /// negative (within the enrolled rule closure); nonzero means
    /// renaming opportunities may have been skipped.
    alpha_filter_skips: usize = 0,
    /// Alpha instance-pair comparisons this run. Pairs whose verdict the
    /// settled cache already holds are skipped and never count, so on an
    /// unchanged egraph a repeat saturation reports zero.
    alpha_pairs_compared: usize = 0,
};

pub const SaturateOptions = struct {
    max_iterations: usize = 16,
    max_nodes: usize = 10_000,
    /// Enumeration budget per (rule, node) match call, charged per
    /// candidate member processed in tree `solvePairs` walks and per AC
    /// bag-assignment step alike. Trips count in `ac_match_capped`.
    ac_match_budget: usize = 10_000,
    /// Retained-match budget per iteration. Charged AFTER dedup, so
    /// matches whose effect was already applied in an earlier iteration
    /// are free — each iteration's budget goes entirely to new unions and
    /// the search ratchets forward through a dense frontier instead of
    /// flooding one iteration. Trips count in `ac_match_capped` (they
    /// weaken a forced negative).
    ac_iter_match_budget: usize = 2_048,
    /// Total enumeration budget per iteration, shared across every
    /// (rule, node) match call. `ac_match_budget` bounds one call, but
    /// on a dense frontier (hundreds of same-head AC rules against
    /// thousands of merge-heavy bag nodes) the CALLS multiply beyond
    /// any per-call bound and one iteration's match phase runs minutes.
    /// This pool bounds their sum; exhaustion stops collecting for the
    /// iteration and counts in `ac_match_capped` like the other budget
    /// trips.
    ac_iter_step_budget: usize = 1_000_000,
    /// Bounds the rounds of the per-iteration `@compute` fold pass.
    /// Each round fires at most one designated redex per class, so this
    /// caps cascade DEPTH (the step pool above bounds match volume): a
    /// k-digit carry cascade folds in O(k) rounds, and a non-terminating
    /// compute rule set stops here instead of minting forever. Trips
    /// count in `ac_match_capped` like every other budget.
    fold_round_budget: usize = 256,
};

/// Member cap on one bag splice expansion. The splice cycle guard keeps
/// self-containing classes finite, but it is a per-path guard: a class
/// referenced twice expands twice, and chains of nested same-head sum
/// classes (digit-carry rules mint them) compound that duplication into
/// flat forms exponentially longer than the node graph. A splice that
/// would exceed this many members is abandoned whole — the node keeps
/// its unspliced shape and the trip counts in `ac_match_capped` — so
/// the pathological corner degrades to an honest capped miss instead of
/// exhausting memory. The value also bounds what every later touch of a
/// flat form costs (hashing, sorting, member assignment), so it sits
/// well above real proof bags (wide conjunctions run tens of members)
/// but far below where per-iteration wall time becomes minutes.
pub const max_splice_members: usize = 256;

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
    /// find-updated in place — safe because bound children are rigid and
    /// class children only move within their class. A bag's member
    /// MULTISET never changes after insert: explanation edges render
    /// against the shapes recorded at union time, so a pending splice
    /// mints a twin node (`.splice` edge) instead of rewriting history.
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
    /// Lowest bag node id per `(term_id, root)` WITHOUT the
    /// atomic-representative exemption (cyclic entries are still
    /// dropped). This is the FULL expansion view: splice-twin minting and
    /// residual-binder rendering must see every same-head bag a class
    /// denotes, even where the canonical form keeps the class atomic.
    bag_node_index: std.AutoArrayHashMapUnmanaged(u64, ENodeId) = .{},
    /// Nodes whose fully spliced form was minted as a twin node (nested
    /// node id -> twin node id). A twinned node's own shape is final;
    /// further member expansion deepens through the twin's chain.
    splice_twin: std.AutoHashMapUnmanaged(ENodeId, ENodeId) = .{},
    /// Nodes whose splice expansion tripped `max_splice_members`. Sticky:
    /// expansions only grow as more classes come to denote same-head bags
    /// (merges never shrink a member occurrence count), so a capped node
    /// would trip on every later rebuild pass too — this set skips those
    /// doomed re-attempts (each burns a cap's worth of appends and a
    /// sort). The trip was counted in `ac_match_capped_total` once, when
    /// it first happened.
    splice_capped_nodes: std.AutoHashMapUnmanaged(ENodeId, void) = .{},
    /// Declared bound-atom dependencies per leaf, supplied by the driver
    /// from the theorem's binder list. A theorem variable `(m: tm y)`
    /// depends on `y` with no structural occurrence the graph could see,
    /// so avoidability checks (dep gate AND extraction representative
    /// selection) must consult this alongside structural occurrence —
    /// otherwise a capture-unsound instance is admitted and the emitted
    /// chain dies in the verifier with a DepViolation.
    leaf_deps: std.AutoHashMapUnmanaged(LeafId, []const LeafId) = .{},
    /// Nodes whose designated `@compute` fold redex was applied (see
    /// `foldCompute`), mapped to the rendered size of the redex that
    /// fired. Sticky and STRUCTURAL — match-effect keys are
    /// canonical-root-relative and refresh on every merge, so without
    /// this ledger a node re-fires its consumed redex under a fresh key
    /// after every union touching its class, re-deriving the alternative
    /// regroupings the normalization strategy exists to avoid. A class's
    /// cascade continues through the newer result nodes the fold minted.
    /// The stored size admits exactly one relaxation: a consumed node may
    /// re-fire on a redex at most HALF the consumed size (a reduced
    /// member appeared in an operand class, or a later-declared rule
    /// reads a member the designated fire ignored) — geometric decrease,
    /// so never a livelock, and near-size regroupings stay dead. See
    /// `foldCompute`.
    fold_consumed: std.AutoHashMapUnmanaged(ENodeId, usize) = .{},
    /// Set when a saturation iteration was budget-capped yet changed
    /// nothing (see `SaturateOutcome.budget_fixpoint`); later `saturate`
    /// calls return immediately instead of re-running the identical
    /// iteration. Cleared by any real union or node insertion, so
    /// external graph mutation between calls re-arms saturation.
    budget_fixpoint: bool = false,
    /// Remaining assignment budget for the current top-level bag match;
    /// reset per (rule, node) match call.
    ac_budget_remaining: usize = 0,
    /// Set when an enumeration actually early-outs on an empty budget —
    /// distinguishes truncation from an enumeration that completed on
    /// exactly its last budget unit. Reset per (rule, node) match call.
    ac_budget_hit: bool = false,
    /// Target side of the rule being matched (set for the duration of one
    /// matchRule/matchRuleBag call); consulted by the residual-only binder
    /// cut (`binderResidualOnly`).
    ac_active_target: ?TemplateExpr = null,
    /// Node `matchRule` is currently anchored on and its canonical class;
    /// when a structured subpattern descends back into that class,
    /// `solvePairs` skips members younger than the anchor node (the
    /// self-containing-class cycle guard — see the descent site).
    match_anchor: ?MatchAnchor = null,
    /// Total bag-match budget trips (monotone; `saturate` reports deltas).
    ac_match_capped_total: usize = 0,
    /// Total cyclic bag-index entries dropped (monotone; `saturate`
    /// reports deltas).
    ac_cyclic_dropped_total: usize = 0,
    /// Alpha pairing-filter comparisons the CURRENT collection pass
    /// resolved approximately (cycle-conservative memo reads, greedy bag
    /// alignment failures, truncated instance enumeration). Reset at the
    /// start of each `collectAlphaMatches` call, so after a saturated
    /// fixpoint it describes exactly the final (complete, deterministic)
    /// pass: zero means the filter was exact at fixpoint.
    alpha_filter_skips: usize = 0,
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
    /// Justifications whose union was a no-op (classes already merged),
    /// plus same-class congruent duplicates found during rebuild. The
    /// forest keeps only class-merging edges, so its unique tree path
    /// between two nodes can be inherently circular on a self-containing
    /// class (an edge on the path re-poses the path's own endpoints as a
    /// child obligation). These edges give extraction acyclic detours;
    /// they are never primary. Deduplicated per endpoint node-pair.
    alt_edges: std.ArrayListUnmanaged(Justification) = .{},
    alt_seen: std.AutoHashMapUnmanaged(u64, void) = .{},
    /// Root class -> member node ids; rebuilt per saturation iteration.
    class_index: std.AutoArrayHashMapUnmanaged(
        EClassId,
        std.ArrayListUnmanaged(ENodeId),
    ) = .{},
    /// Match dedup state; lives on the egraph (not one `saturate` call) so
    /// the `applied` set survives drivers that saturate one iteration at a
    /// time. Without that persistence a dense already-applied frontier can
    /// re-fill the per-iteration retained-match budget forever: every call
    /// re-collects the same no-op effects, caps, and starves the matches
    /// past the cut — a livelock at a node fixpoint that never saturates.
    match_dedup: MatchDedup = .{},
    /// Incremental alpha scan state: per alpha rule slot, the instances
    /// discovered by the last COMMITTED collection pass (substs owned by
    /// the egraph allocator, node-ordered). A pass commits only when it
    /// ran to completion with zero approximate resolutions, so committed
    /// pair verdicts are exact; they stay valid until structure reachable
    /// downward from an instance's class changes, which the pass detects
    /// via the union-log delta (see `collectAlphaMatches`). The
    /// watermarks name the node / union-log prefixes the last committed
    /// pass accounted for.
    alpha_settled: std.AutoHashMapUnmanaged(
        u32,
        std.ArrayListUnmanaged(AlphaInstance),
    ) = .{},
    alpha_node_watermark: usize = 0,
    alpha_union_watermark: usize = 0,
    /// Total alpha instance-pair comparisons (monotone; `saturate`
    /// reports deltas). Clean pairs answered by the settled cache never
    /// count — the measure of what incrementality saves.
    alpha_pairs_compared_total: usize = 0,

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
    /// Canonicalize with the splice-cap fallback: a `SpliceCapped` trip
    /// counts in `ac_match_capped_total` and degrades to the unspliced
    /// shape, so storage paths never see the error.
    fn canonicalizeOrCap(
        self: *EGraph,
        node: ENode,
        self_class: ?EClassId,
        alloc: std.mem.Allocator,
    ) error{OutOfMemory}!ENode {
        return self.canonicalizeInto(
            node,
            self_class,
            alloc,
            .splice,
        ) catch |err| switch (err) {
            error.SpliceCapped => blk: {
                self.ac_match_capped_total += 1;
                break :blk self.canonicalizeInto(
                    node,
                    self_class,
                    alloc,
                    .no_splice,
                ) catch |e| switch (e) {
                    error.SpliceCapped => unreachable,
                    error.OutOfMemory => return error.OutOfMemory,
                };
            },
            error.OutOfMemory => return error.OutOfMemory,
        };
    }

    fn addWith(
        self: *EGraph,
        node: ENode,
        scratch: std.mem.Allocator,
    ) !EClassId {
        const canon = try self.canonicalizeOrCap(node, null, scratch);
        if (self.memo.get(canon)) |node_id| {
            return self.find(self.nodes.items[node_id].class);
        }
        const owned = try self.ownNode(canon);
        self.budget_fixpoint = false;
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
            try self.bag_node_index.put(
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
        const canon = try self.canonicalizeOrCap(node, null, self.allocator);
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
        if (root_a == root_b) {
            try self.recordAltEdge(just);
            return false;
        }
        self.parents.items[root_a] = root_b;
        self.budget_fixpoint = false;
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

    /// Keep one alternate edge per endpoint node-pair (first wins).
    fn recordAltEdge(self: *EGraph, just: Justification) !void {
        const ends = justEndpoints(just);
        if (ends.a == ends.b) return;
        const key = nodePairKey(ends.a, ends.b);
        const gop = try self.alt_seen.getOrPut(self.allocator, key);
        if (gop.found_existing) return;
        try self.alt_edges.append(self.allocator, just);
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
    ///
    /// Stable-shape invariant: a stored bag node's member MULTISET never
    /// changes after insert (member ids only move within their class and
    /// re-sort). When a member class acquires a same-head bag, the spliced
    /// canonical form is minted as a twin node in the same class, linked
    /// by a `.splice` explanation edge — explanation edges reference nodes
    /// recorded at union time, and re-splicing them in place would erase
    /// the shapes those edges render against.
    pub fn rebuild(self: *EGraph) !bool {
        var any = false;
        // Rebuild re-canonicalizes every node every pass; on large bag
        // graphs the member arrays are the dominant allocation, and most
        // nodes are already canonical. Canonicalize into a reusable
        // scratch arena and copy into the egraph arena only when the
        // canonical form actually changed.
        var scratch_state = std.heap.ArenaAllocator.init(
            std.heap.page_allocator,
        );
        defer scratch_state.deinit();
        const scratch = scratch_state.allocator();
        while (true) {
            var changed = false;
            self.memo.clearRetainingCapacity();
            _ = scratch_state.reset(.retain_capacity);
            try self.refreshBagIndex(scratch);
            var mints: std.ArrayListUnmanaged(PendingTwin) = .{};
            for (self.nodes.items, 0..) |*stored, idx| {
                stored.class = self.find(stored.class);
                switch (stored.node) {
                    .bag => |bag| {
                        // Stored bag shapes are stable: find-update and
                        // re-sort only. When the full expansion view says
                        // a member class denotes a same-head bag, the
                        // flat form is minted as a twin instead.
                        const nosplice = try self.sortMembersOnly(
                            bag,
                            scratch,
                        );
                        if (!nodeEql(nosplice, stored.node)) {
                            stored.node = try self.ownNode(nosplice);
                        }
                        if (self.splice_twin.get(@intCast(idx)) == null and
                            !self.splice_capped_nodes.contains(
                                @intCast(idx),
                            ))
                        {
                            // A capped expansion mints no twin: the flat
                            // form this node's congruent joins need would
                            // be over-budget, so the joins are skipped
                            // and the trip weakens any forced negative.
                            if (self.fullSplice(
                                stored.node.bag.term_id,
                                stored.node.bag.members,
                                stored.class,
                                scratch,
                            )) |full| {
                                if (full.bag.members.len !=
                                    stored.node.bag.members.len)
                                {
                                    try mints.append(scratch, .{
                                        .from = @intCast(idx),
                                        .flat = full,
                                        .just = try self.buildSpliceJust(
                                            @intCast(idx),
                                            scratch,
                                        ),
                                    });
                                }
                            } else |err| switch (err) {
                                error.SpliceCapped => {
                                    self.ac_match_capped_total += 1;
                                    try self.splice_capped_nodes.put(
                                        self.allocator,
                                        @intCast(idx),
                                        {},
                                    );
                                },
                                error.OutOfMemory => {
                                    return error.OutOfMemory;
                                },
                            }
                        }
                    },
                    else => {
                        const canon = try self.canonicalizeOrCap(
                            stored.node,
                            stored.class,
                            scratch,
                        );
                        if (!nodeEql(canon, stored.node)) {
                            stored.node = try self.ownNode(canon);
                        }
                    },
                }
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
                if (other_class == stored.class) {
                    // Same-class duplicate shapes never union, but the
                    // congruent-twin link is an extraction detour around
                    // circular tree paths in self-containing classes.
                    if (self.congruenceAllowed(stored.node)) {
                        try self.recordAltEdge(.{ .congruence = .{
                            .left = gop.value_ptr.*,
                            .right = @intCast(idx),
                        } });
                    }
                    continue;
                }
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
            for (mints.items) |mint| {
                try self.mintSpliceTwin(mint);
                changed = true;
            }
            if (!changed) break;
        }
        return any;
    }

    const PendingTwin = struct {
        from: ENodeId,
        /// Scratch-backed fully spliced shape.
        flat: ENode,
        /// Fully arena-backed justification (snapshots taken at detection
        /// time, before later merges in the same pass move any finds).
        just: Justification,
    };

    /// Find-update and re-sort a bag's members without splicing: the
    /// stable stored shape of a node whose spliced form lives in a twin.
    fn sortMembersOnly(
        self: *const EGraph,
        bag: ENode.Bag,
        alloc: std.mem.Allocator,
    ) !ENode {
        const members = try alloc.dupe(EClassId, bag.members);
        for (members) |*member| member.* = self.find(member.*);
        std.mem.sort(EClassId, members, {}, std.sort.asc(EClassId));
        return .{ .bag = .{ .term_id = bag.term_id, .members = members } };
    }

    /// Record the splice justification for `from` against the current
    /// bag-index state — the same state `canonicalizeInto` just spliced
    /// with. All slices land in the egraph arena (the justification
    /// outlives the pass).
    fn buildSpliceJust(
        self: *EGraph,
        from: ENodeId,
        scratch: std.mem.Allocator,
    ) !Justification {
        const bag = self.nodes.items[from].node.bag;
        var visited: std.ArrayListUnmanaged(EClassId) = .{};
        try visited.append(
            scratch,
            self.find(self.nodes.items[from].class),
        );
        const members = try self.allocator.alloc(
            EClassId,
            bag.members.len,
        );
        const expansion = try self.allocator.alloc(
            ?*const SpliceExpansion,
            bag.members.len,
        );
        for (bag.members, 0..) |member, idx| {
            members[idx] = self.find(member);
            expansion[idx] = try self.buildSpliceExpansion(
                bag.term_id,
                members[idx],
                &visited,
                scratch,
            );
        }
        return .{
            .splice = .{
                .from = from,
                .to = undefined, // patched by mintSpliceTwin
                .members = members,
                .expansion = expansion,
            },
        };
    }

    /// Mirror of the full-view splice recursion, recording the expansion
    /// tree instead of the flat list. Null exactly where the expansion
    /// keeps the class atomic (no same-head bag, or the cycle guard).
    fn buildSpliceExpansion(
        self: *EGraph,
        term_id: u32,
        root: EClassId,
        visited: *std.ArrayListUnmanaged(EClassId),
        scratch: std.mem.Allocator,
    ) error{OutOfMemory}!?*const SpliceExpansion {
        const bag_node = self.bag_node_index.get(
            bagKey(term_id, root),
        ) orelse return null;
        if (std.mem.indexOfScalar(
            EClassId,
            visited.items,
            root,
        ) != null) return null;
        try visited.append(scratch, root);
        defer _ = visited.pop();
        const sub = self.nodes.items[bag_node].node.bag;
        const members = try self.allocator.alloc(
            EClassId,
            sub.members.len,
        );
        const entries = try self.allocator.alloc(
            ?*const SpliceExpansion,
            sub.members.len,
        );
        for (sub.members, 0..) |member, idx| {
            members[idx] = self.find(member);
            entries[idx] = try self.buildSpliceExpansion(
                term_id,
                members[idx],
                visited,
                scratch,
            );
        }
        const exp = try self.allocator.create(SpliceExpansion);
        exp.* = .{
            .node = bag_node,
            .members = members,
            .entries = entries,
        };
        return exp;
    }

    /// Append the flat twin node into `from`'s class and hang the splice
    /// edge off it (a fresh node is a leaf of the explanation forest, so
    /// no re-rooting is needed). The twin enters the memo on the next
    /// rebuild pass, where a shape collision with another class merges
    /// through the ordinary congruence path.
    fn mintSpliceTwin(self: *EGraph, mint: PendingTwin) !void {
        var just = mint.just;
        const node_id: ENodeId = @intCast(self.nodes.items.len);
        just.splice.to = node_id;
        try self.nodes.append(self.allocator, .{
            .node = try self.ownNode(mint.flat),
            .class = self.find(self.nodes.items[mint.from].class),
        });
        try self.expl_parent.append(self.allocator, .{
            .to = mint.from,
            .just = just,
            // Semantic direction (from -> to) runs parent -> child along
            // this link, so the child -> parent traversal is reversed.
            .forward = false,
        });
        try self.splice_twin.put(self.allocator, mint.from, node_id);
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
    fn refreshBagIndex(self: *EGraph, scratch: std.mem.Allocator) !void {
        self.bag_in_class.clearRetainingCapacity();
        // Classes holding an atomic representative (a leaf or a plain
        // application) are exempt from splicing. Once a cancellation
        // unions some `x + (-x)` bag into zero's class, splicing through
        // that class would replace every zero-valued member with
        // cancellation junk (`{zero, t}` canonicalizes to `{a, -a, t}`),
        // making the unit rules that normalize a cancelled sum away
        // (x+0 -> x) permanently unmatchable. The atomic member is the
        // productive canonical choice; the class's bag nodes stay
        // reachable through congruence and direct matching.
        var atomic_roots: std.AutoHashMapUnmanaged(EClassId, void) = .{};
        for (self.nodes.items) |stored| {
            switch (stored.node) {
                .bag => {},
                .leaf, .app => try atomic_roots.put(
                    scratch,
                    self.find(stored.class),
                    {},
                ),
            }
        }
        self.bag_node_index.clearRetainingCapacity();
        for (self.nodes.items, 0..) |stored, idx| {
            const bag = switch (stored.node) {
                .bag => |bag| bag,
                else => continue,
            };
            const root = self.find(stored.class);
            const key = bagKey(bag.term_id, root);
            const node_gop = try self.bag_node_index.getOrPut(
                self.allocator,
                key,
            );
            if (!node_gop.found_existing or node_gop.value_ptr.* > idx) {
                node_gop.value_ptr.* = @intCast(idx);
            }
            if (atomic_roots.contains(root)) continue;
            const gop = try self.bag_in_class.getOrPut(self.allocator, key);
            if (!gop.found_existing or gop.value_ptr.* > idx) {
                gop.value_ptr.* = @intCast(idx);
            }
        }
        var cyclic: std.ArrayListUnmanaged(u64) = .{};
        for (self.bag_node_index.keys()) |key| {
            const term_id: u32 = @intCast(key >> 32);
            const root: EClassId = @truncate(key);
            if (try self.bagExpansionReenters(term_id, root, scratch)) {
                try cyclic.append(scratch, key);
            }
        }
        for (cyclic.items) |key| {
            _ = self.bag_in_class.swapRemove(key);
            _ = self.bag_node_index.swapRemove(key);
        }
        self.ac_cyclic_dropped_total += cyclic.items.len;
    }

    /// True when the transitive same-head member expansion of `root`'s
    /// bag reaches `root` again (over the full, unexempted view).
    fn bagExpansionReenters(
        self: *const EGraph,
        term_id: u32,
        root: EClassId,
        scratch: std.mem.Allocator,
    ) !bool {
        var stack: std.ArrayListUnmanaged(EClassId) = .{};
        var seen: std.ArrayListUnmanaged(EClassId) = .{};
        const bag_node = self.bag_node_index.get(bagKey(term_id, root)).?;
        for (self.nodes.items[bag_node].node.bag.members) |member| {
            try stack.append(scratch, self.find(member));
        }
        while (stack.pop()) |class| {
            if (class == root) return true;
            if (std.mem.indexOfScalar(
                EClassId,
                seen.items,
                class,
            ) != null) continue;
            try seen.append(scratch, class);
            const node = self.bag_node_index.get(
                bagKey(term_id, class),
            ) orelse continue;
            for (self.nodes.items[node].node.bag.members) |member| {
                try stack.append(scratch, self.find(member));
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
        const pairs_start = self.alpha_pairs_compared_total;
        var has_compute = false;
        var has_alpha = false;
        for (rules) |rule| {
            if (rule.compute) has_compute = true;
            if (rule.alpha) has_alpha = true;
        }
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
        const dedup = &self.match_dedup;
        _ = try self.rebuild();
        while (stats.iterations < opts.max_iterations) {
            if (self.budget_fixpoint) {
                stats.outcome = .budget_fixpoint;
                return self.finishStats(stats, capped_start, cyclic_start, pairs_start);
            }
            stats.iterations += 1;
            dedup.iter.clearRetainingCapacity();
            const applied_before = dedup.applied.count();
            const nodes_before = self.nodes.items.len;

            var changed = false;
            var iter_capped = false;
            // `@compute` rules fold first: the directed pass consumes the
            // computation before the general loop's undirected matching
            // can breed its regroupings.
            if (has_compute) {
                const fold = try self.foldCompute(
                    rules,
                    opts,
                    dedup,
                    &scratch_state,
                    &stats,
                );
                if (fold.node_capped) {
                    _ = try self.rebuild();
                    stats.outcome = .node_capped;
                    return self.finishStats(stats, capped_start, cyclic_start, pairs_start);
                }
                if (fold.capped) iter_capped = true;
                if (fold.changed) changed = true;
                dedup.iter.clearRetainingCapacity();
            }
            try self.buildClassIndex();

            var matches: std.ArrayListUnmanaged(Match) = .{};
            var iter_steps: usize = opts.ac_iter_step_budget;
            const matched_nodes = self.nodes.items.len;
            // Alpha scheduler first: it creates no nodes, only retained
            // matches. It draws from its OWN step pool (sized like the
            // general one) so heavy pairing scans can never starve the
            // ordinary rule loop of its whole iteration budget; a trip
            // still marks the iteration capped, keeping fixpoint claims
            // honest.
            if (has_alpha) {
                var alpha_steps: usize = opts.ac_iter_step_budget;
                _ = scratch_state.reset(.retain_capacity);
                try alpha_mod.collectAlphaMatches(
                    self,
                    rules,
                    opts,
                    &matches,
                    dedup,
                    &alpha_steps,
                    &iter_capped,
                    scratch_state.allocator(),
                );
            }
            collect: for (0..matched_nodes) |node_id| {
                switch (self.nodes.items[node_id].node) {
                    .leaf => {},
                    .app => |app| for (rules, 0..) |rule, rule_slot| {
                        if (rule.compute or rule.alpha) continue;
                        const pattern = rule.match_side.app;
                        if (pattern.term_id != app.term_id) continue;
                        if (pattern.args.len != app.children.len) continue;
                        const allotted = @min(
                            opts.ac_match_budget,
                            iter_steps,
                        );
                        if (allotted == 0) {
                            iter_capped = true;
                            self.ac_match_capped_total += 1;
                            break :collect;
                        }
                        self.ac_budget_remaining = allotted;
                        self.ac_budget_hit = false;
                        _ = scratch_state.reset(.retain_capacity);
                        try self.matchRule(
                            rule,
                            @intCast(rule_slot),
                            @intCast(node_id),
                            &matches,
                            dedup,
                            scratch_state.allocator(),
                        );
                        iter_steps -= allotted - self.ac_budget_remaining;
                        if (self.ac_budget_hit) {
                            self.ac_match_capped_total += 1;
                        }
                    },
                    .bag => |bag| for (rules, 0..) |rule, rule_slot| {
                        if (rule.compute or rule.alpha) continue;
                        const pattern = rule.match_side.app;
                        if (pattern.term_id != bag.term_id) continue;
                        const allotted = @min(
                            opts.ac_match_budget,
                            iter_steps,
                        );
                        if (allotted == 0) {
                            iter_capped = true;
                            self.ac_match_capped_total += 1;
                            break :collect;
                        }
                        self.ac_budget_remaining = allotted;
                        self.ac_budget_hit = false;
                        _ = scratch_state.reset(.retain_capacity);
                        try self.matchRuleBag(
                            rule,
                            @intCast(rule_slot),
                            @intCast(node_id),
                            &matches,
                            dedup,
                            scratch_state.allocator(),
                        );
                        iter_steps -= allotted - self.ac_budget_remaining;
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
                    return self.finishStats(stats, capped_start, cyclic_start, pairs_start);
                }
                // Per-iteration retained-match budget: on a dense frontier
                // (AC bags, or AC-style laws enrolled as plain tree
                // rewrites) one unthrottled iteration can retain tens of
                // thousands of new-effect matches whose applied unions make
                // the NEXT frontier combinatorially worse. Stop collecting,
                // apply what we have, and let later iterations continue —
                // already-applied effects are deduped free, so every
                // iteration's budget goes to fresh unions.
                if (matches.items.len >= opts.ac_iter_match_budget) {
                    iter_capped = true;
                    self.ac_match_capped_total += 1;
                    break;
                }
            }

            var avoid_cache: AvoidCache = .{};
            for (matches.items) |m| {
                switch (try self.applyMatch(
                    rules,
                    m,
                    dedup,
                    &stats,
                    &avoid_cache,
                )) {
                    .merged => changed = true,
                    .noop, .dep_deferred, .instantiation_failed => {},
                }
                if (self.nodes.items.len > opts.max_nodes) {
                    _ = try self.rebuild();
                    stats.outcome = .node_capped;
                    return self.finishStats(stats, capped_start, cyclic_start, pairs_start);
                }
            }

            const grew = self.nodes.items.len != nodes_before;
            const congr_changed = try self.rebuild();
            // A capped collection pass is not a fixpoint claim: uncollected
            // matches may remain even when the collected ones all no-oped.
            if (!changed and !grew and !congr_changed and !iter_capped) {
                stats.outcome = .saturated;
                return self.finishStats(stats, capped_start, cyclic_start, pairs_start);
            }
            // Deterministic no-progress under a budget cap: nothing this
            // iteration changed — no union, no node, no congruence repair,
            // not even a newly recorded applied effect — yet collection
            // was capped. Collection is deterministic, so the next
            // iteration would re-enumerate the same capped frontier
            // bit-for-bit; stop instead of burning the remaining budget.
            if (!changed and !grew and !congr_changed and
                dedup.applied.count() == applied_before)
            {
                self.budget_fixpoint = true;
                stats.outcome = .budget_fixpoint;
                return self.finishStats(stats, capped_start, cyclic_start, pairs_start);
            }
        }
        return self.finishStats(stats, capped_start, cyclic_start, pairs_start);
    }

    fn finishStats(
        self: *const EGraph,
        stats: SaturateStats,
        capped_start: usize,
        cyclic_start: usize,
        pairs_start: usize,
    ) SaturateStats {
        var out = stats;
        out.ac_match_capped = self.ac_match_capped_total - capped_start;
        out.ac_cyclic_dropped = self.ac_cyclic_dropped_total - cyclic_start;
        out.alpha_filter_skips = self.alpha_filter_skips;
        out.alpha_pairs_compared =
            self.alpha_pairs_compared_total - pairs_start;
        return out;
    }

    const MatchApplyOutcome = enum {
        merged,
        noop,
        dep_deferred,
        instantiation_failed,
    };

    /// Apply one collected match: dep gate, target instantiation,
    /// extension rejoin, union, applied-ledger entry. Shared by the
    /// general apply loop and the fold scheduler so both record
    /// identical explanation edges and dedup state. The union holds after
    /// `merged`/`noop` (so identical-effect matches are dropped at
    /// collection from then on); dep-deferred and instantiation-failed
    /// matches are NOT recorded and stay eligible for retry. Node-cap
    /// policing stays with the callers.
    fn applyMatch(
        self: *EGraph,
        rules: []const Rule,
        m: Match,
        dedup: *MatchDedup,
        stats: *SaturateStats,
        avoid_cache: *AvoidCache,
    ) !MatchApplyOutcome {
        if (!try self.depGateAllows(
            rules[m.rule_slot],
            m.subst,
            avoid_cache,
        )) {
            stats.dep_deferred += 1;
            return .dep_deferred;
        }
        const target = (try self.instantiate(
            rules[m.rule_slot].target_side,
            m.subst,
        )) orelse return .instantiation_failed;
        var to_class = target.class;
        var to_node = target.node;
        if (m.extension.len != 0) {
            // Extension semantics: the rewrite hit a sub-multiset of the
            // bag; the target rejoins the leftover members before the
            // union.
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
            stats.unions_applied += 1;
            if (rules[m.rule_slot].alpha) stats.alpha_applied += 1;
        }
        try dedup.applied.put(self.allocator, m.key, {});
        return if (merged) .merged else .noop;
    }

    const FoldOutcome = struct {
        changed: bool = false,
        capped: bool = false,
        node_capped: bool = false,
    };

    /// Per-round minimal rendered-size table for the fold scheduler's
    /// size-decreasing re-fire gate.
    const FoldSizes = std.AutoHashMapUnmanaged(EClassId, usize);

    /// A class none of whose members render finitely (every member is
    /// cyclic through the class itself) has no `FoldSizes` entry; matches
    /// binding it measure as this sentinel, so they can never pass the
    /// re-fire gate — but any later finite match beats them.
    const fold_unrenderable: usize = std.math.maxInt(usize);

    /// Minimal rendered term size per class root — the explain-side
    /// `ensureExtraction` fixpoint, sans avoid-masks. Well-founded by
    /// construction (a finite entry's children have strictly smaller
    /// cost). Allocated in the round scratch arena: roots move every
    /// round, so entries must not outlive one.
    fn computeFoldSizes(
        self: *EGraph,
        scratch: std.mem.Allocator,
    ) !FoldSizes {
        var sizes: FoldSizes = .{};
        while (true) {
            var changed = false;
            node_loop: for (self.nodes.items) |stored| {
                var cost: usize = 1;
                switch (stored.node) {
                    .leaf => {},
                    .app => |app| for (app.children) |child| switch (child) {
                        .bound => cost +|= 1,
                        .class => |c| {
                            cost +|= sizes.get(self.find(c)) orelse
                                continue :node_loop;
                        },
                    },
                    .bag => |bag| for (bag.members) |member| {
                        cost +|= sizes.get(self.find(member)) orelse
                            continue :node_loop;
                    },
                }
                const root = self.find(stored.class);
                const gop = try sizes.getOrPut(scratch, root);
                if (!gop.found_existing or cost < gop.value_ptr.*) {
                    gop.value_ptr.* = cost;
                    changed = true;
                }
            }
            if (!changed) break;
        }
        return sizes;
    }

    fn foldSizeOf(
        self: *EGraph,
        sizes: *const FoldSizes,
        class: EClassId,
    ) usize {
        return sizes.get(self.find(class)) orelse fold_unrenderable;
    }

    /// Rendered size of a collected fold match: the match side with every
    /// binder at its binding's minimal representative, plus (for AC
    /// matches) the leftover members the target rejoins. It measures the
    /// redex as a TERM, not the pattern, so measures are comparable
    /// across rules — a later-declared rule reading a reduced member
    /// beats an earlier rule's fire through an unreduced one.
    fn foldMatchMeasure(
        self: *EGraph,
        sizes: *const FoldSizes,
        rule: Rule,
        m: Match,
    ) usize {
        var total = self.foldTemplateSize(sizes, rule.match_side, m.subst);
        for (m.extension) |member| {
            total +|= self.foldSizeOf(sizes, member);
        }
        return total;
    }

    fn foldTemplateSize(
        self: *EGraph,
        sizes: *const FoldSizes,
        template: TemplateExpr,
        subst: []const ?Child,
    ) usize {
        switch (template) {
            .binder => |idx| {
                const child = subst[idx] orelse return 1;
                return switch (child) {
                    .bound => 1,
                    .class => |c| self.foldSizeOf(sizes, c),
                };
            },
            .app => |app| {
                var total: usize = 1;
                for (app.args) |arg| {
                    total +|= self.foldTemplateSize(sizes, arg, subst);
                }
                return total;
            },
        }
    }

    /// Cheapest redex ANY match rooted at `node` could render at current
    /// sizes: every binding lives inside the node's operand classes
    /// (bare binders bind the class itself; structured sub-patterns
    /// render a member, never below the class minimum), so one plus the
    /// children's minimal sizes bounds every measure from below. Lets
    /// the scan skip consumed nodes without re-matching when no strictly
    /// smaller redex can exist.
    fn foldNodeLowerBound(
        self: *EGraph,
        sizes: *const FoldSizes,
        node: ENode,
    ) usize {
        var total: usize = 1;
        switch (node) {
            .leaf => {},
            .app => |app| for (app.children) |child| switch (child) {
                .bound => total +|= 1,
                .class => |c| total +|= self.foldSizeOf(sizes, c),
            },
            .bag => |bag| for (bag.members) |member| {
                total +|= self.foldSizeOf(sizes, member);
            },
        }
        return total;
    }

    /// Directed folding for `@compute` rules. Undirected saturation is
    /// the wrong engine for computational rule sets (digit tables, carry
    /// cascades): every regrouping of a bag matches, every application
    /// order mints distinct intermediate classes, and the closure is
    /// exponential in what a rewrite engine computes in linearly many
    /// steps. This pass runs the compute subset as a normalization
    /// strategy instead:
    ///
    ///   - each node fires its designated redex — the first fresh match
    ///     in (rule, enumeration) order — and is consumed at that redex's
    ///     rendered size (`fold_consumed`): the cascade continues through
    ///     the result nodes the fold mints, and alternative pairings of a
    ///     consumed shape never fire — that closure is exactly what a
    ///     rewrite strategy exists to avoid. ONE relaxation: once fold
    ///     rounds reach fixpoint, RE-FIRE rounds let a consumed app node
    ///     fire again on a redex at most HALF its consumed size, which
    ///     happens when the original fire anchored on an operand member
    ///     that was later out-reduced (the reduced member did not exist
    ///     yet, or a later-declared rule reads it while an earlier rule
    ///     won on the unreduced one). Halving — not mere decrease — is
    ///     the junk filter: on a self-containing class (a vacuous-sb
    ///     member, Y-style unrolling) cycle artifacts shave only a node
    ///     or two off the rendering, while a genuinely reduced anchor
    ///     shrinks the redex substantially; geometric decrease also
    ///     bounds a node's re-fires to log(size). Bags never re-fire —
    ///     a bag's "smaller match" is a different sub-multiset pairing,
    ///     the regrouping the ledger exists to refuse. A re-fire whose
    ///     union already holds still records its rule edge as an
    ///     alternate, giving extraction the forward route through
    ///     reduced forms instead of a backward expansion through the
    ///     stale anchor (each backward step breaks a big-step group);
    ///   - per round, each class fires at most once, and nodes scan in
    ///     ASCENDING id order over a round-start snapshot — the general
    ///     apply loop's orientation, which keeps recorded rule edges
    ///     firing before their subterm results merge (extraction renders
    ///     rule endpoints from the recorded substitution, and an already-
    ///     merged binding class renders as a different representative
    ///     than the anchored after-node, a seam only the fold rule
    ///     itself could prove);
    ///   - rounds repeat to fixpoint under `fold_round_budget`, with one
    ///     `ac_iter_step_budget` pool across the whole pass.
    ///
    /// There is no groundness restriction: `conversion?` matches, it
    /// never narrows, so a theorem variable in a substitution is an
    /// inert constant and firing on it is ordinary evaluation over the
    /// extended signature (proving with fresh constants IS proving
    /// universally). Fold unions are ordinary rule unions (same
    /// justification, same dedup ledger), so extraction and lowering are
    /// unchanged. For a confluent compute set the strategy reaches the
    /// same normal forms as exhaustive saturation; a non-confluent set
    /// reaches SOME fold — never unsound, merely less complete, and
    /// every budget trip counts in `ac_match_capped` so a subsequent
    /// miss stays honest.
    fn foldCompute(
        self: *EGraph,
        rules: []const Rule,
        opts: SaturateOptions,
        dedup: *MatchDedup,
        scratch_state: *std.heap.ArenaAllocator,
        stats: *SaturateStats,
    ) !FoldOutcome {
        var out = FoldOutcome{};
        var fold_steps: usize = opts.ac_iter_step_budget;
        var dirty = false;
        var rounds: usize = 0;
        // Fold rounds run the primary computation exactly as always
        // (consumed nodes are skipped outright — no re-match cost while
        // the cascade is still spending its budget). Only once they reach
        // fixpoint do re-fire rounds sweep the consumed nodes for
        // half-size-or-smaller redexes, spending leftover budget; a
        // re-fire that MERGES can seed new designated fires, so it
        // drops the loop back into fold mode.
        var mode: enum { fold, refire } = .fold;
        round: while (rounds < opts.fold_round_budget) : (rounds += 1) {
            dedup.iter.clearRetainingCapacity();
            _ = scratch_state.reset(.retain_capacity);
            const scratch = scratch_state.allocator();
            // The matchers resolve structured pattern members through
            // `class_index`; every round's merges move nodes between
            // classes, so it must be fresh per round.
            try self.buildClassIndex();
            // Round-start size table for the re-fire gate; mid-round
            // fires leave it slightly stale, which only ever OVERSTATES a
            // recorded measure — the decreasing gate stays well-founded
            // either way.
            const sizes = try self.computeFoldSizes(scratch);
            var fired_classes: std.AutoHashMapUnmanaged(EClassId, void) = .{};
            var avoid_cache: AvoidCache = .{};
            var fired = false;
            var refired = false;
            // Round-start snapshot: nodes a fire mints wait for the next
            // round, so within one round every fire's binding classes are
            // in their pre-round state.
            const round_nodes = self.nodes.items.len;
            var node_id: usize = 0;
            scan: while (node_id < round_nodes) : (node_id += 1) {
                const stored = self.nodes.items[node_id];
                if (stored.node == .leaf) continue;
                // Effect keys are canonical-root-relative and refresh on
                // every merge, so without this structural ledger a node
                // would re-fire its consumed redex under a fresh key after
                // every union touching its class — re-deriving exactly the
                // regrouping junk the strategy avoids. Re-fire rounds
                // reconsider a consumed node only when its operand
                // classes prove a half-size redex could now render (the
                // cheap bound spares the expensive re-match in the
                // common case).
                const consumed = self.fold_consumed.get(@intCast(node_id));
                if (consumed) |past| {
                    if (mode == .fold) continue;
                    // App redexes only: an app re-fire is the same
                    // structural redex evaluated on a more-reduced
                    // operand member. A bag's "smaller match" is a
                    // DIFFERENT sub-multiset pairing — the alternative
                    // regrouping the consumed ledger exists to refuse.
                    if (stored.node != .app) continue;
                    if (self.foldNodeLowerBound(&sizes, stored.node) >
                        past / 2)
                        continue;
                }
                const root = self.find(stored.class);
                if (fired_classes.contains(root)) continue;
                var matches: std.ArrayListUnmanaged(Match) = .{};
                for (rules, 0..) |rule, rule_slot| {
                    if (!rule.compute) continue;
                    const pattern = rule.match_side.app;
                    switch (stored.node) {
                        .leaf => unreachable,
                        .app => |app| {
                            if (pattern.term_id != app.term_id) continue;
                            if (pattern.args.len != app.children.len)
                                continue;
                        },
                        .bag => |bag| {
                            if (pattern.term_id != bag.term_id) continue;
                        },
                    }
                    const allotted = @min(opts.ac_match_budget, fold_steps);
                    if (allotted == 0) {
                        out.capped = true;
                        self.ac_match_capped_total += 1;
                        break :round;
                    }
                    self.ac_budget_remaining = allotted;
                    self.ac_budget_hit = false;
                    matches.clearRetainingCapacity();
                    switch (stored.node) {
                        .leaf => unreachable,
                        .app => try self.matchRule(
                            rule,
                            @intCast(rule_slot),
                            @intCast(node_id),
                            &matches,
                            dedup,
                            scratch,
                        ),
                        .bag => try self.matchRuleBag(
                            rule,
                            @intCast(rule_slot),
                            @intCast(node_id),
                            &matches,
                            dedup,
                            scratch,
                        ),
                    }
                    fold_steps -= allotted - self.ac_budget_remaining;
                    if (self.ac_budget_hit) {
                        out.capped = true;
                        self.ac_match_capped_total += 1;
                    }
                    // Binder-subset matching materializes sub-bags via
                    // add(); police that growth like the collect loop.
                    if (self.nodes.items.len > opts.max_nodes) {
                        out.node_capped = true;
                        return out;
                    }
                    if (matches.items.len == 0) continue;
                    // The node's designated redex: the first fresh match
                    // in (rule, enumeration) order — or, for a consumed
                    // node, the first one at most half the size of the
                    // fire already on the ledger.
                    for (matches.items) |m| {
                        const measure =
                            self.foldMatchMeasure(&sizes, rule, m);
                        if (consumed) |past| {
                            // Halving, not mere decrease: a genuinely
                            // out-reduced anchor shrinks the redex
                            // substantially, while a self-containing
                            // class's cycle artifacts (a vacuous-sb or
                            // Y-unrolling member) only shave a node or
                            // two off the rendering. Geometric decrease
                            // also bounds a node's re-fires to
                            // log(size).
                            if (measure > past / 2) continue;
                        }
                        switch (try self.applyMatch(
                            rules,
                            m,
                            dedup,
                            stats,
                            &avoid_cache,
                        )) {
                            .merged => {
                                try self.fold_consumed.put(
                                    self.allocator,
                                    @intCast(node_id),
                                    measure,
                                );
                                try fired_classes.put(scratch, root, {});
                                fired = true;
                                dirty = true;
                                out.changed = true;
                                stats.fold_applied += 1;
                                if (self.nodes.items.len > opts.max_nodes) {
                                    out.node_capped = true;
                                    return out;
                                }
                                continue :scan;
                            },
                            .noop => {
                                // The union already held: the redex is
                                // just as reduced as after a real merge.
                                try self.fold_consumed.put(
                                    self.allocator,
                                    @intCast(node_id),
                                    measure,
                                );
                                // A no-op RE-fire still made progress —
                                // it recorded the forward rule edge as an
                                // alternate and shrank the ledger entry —
                                // so keep re-fire rounds alive for the
                                // even-smaller match it may have shadowed.
                                if (consumed != null) refired = true;
                                continue :scan;
                            },
                            .dep_deferred,
                            .instantiation_failed,
                            => continue,
                        }
                    }
                }
            }
            if (out.capped) break;
            if (fired) {
                // A merge — fold or re-fire — can seed fresh designated
                // fires; run fold rounds again.
                mode = .fold;
                _ = try self.rebuild();
                dirty = false;
                if (self.nodes.items.len > opts.max_nodes) {
                    out.node_capped = true;
                    return out;
                }
                continue;
            }
            if (mode == .fold) {
                mode = .refire;
                continue;
            }
            if (!refired) break;
        }
        if (rounds >= opts.fold_round_budget) {
            out.capped = true;
            self.ac_match_capped_total += 1;
        }
        // Leave the graph congruence-repaired for the general collect
        // pass that follows (its matchers read the bag indexes rebuild
        // refreshes).
        if (dirty) {
            _ = try self.rebuild();
            if (self.nodes.items.len > opts.max_nodes) {
                out.node_capped = true;
            }
        }
        return out;
    }

    pub const AvoidCache = std.AutoArrayHashMapUnmanaged(LeafId, []const bool);

    /// Per-class snapshot of `avoidable(class, atom)`: the class can
    /// denote at least one term in which `atom` does not occur. Monotone
    /// in graph growth (members only accumulate under adds and merges),
    /// so a stale false only defers a match to a later iteration — it
    /// never admits a bad one.
    /// A leaf denotes a term free of `atom` unless it IS the atom or its
    /// declared dependencies include it.
    pub fn leafAvoids(self: *const EGraph, leaf: LeafId, atom: LeafId) bool {
        if (leaf == atom) return false;
        if (self.leaf_deps.get(leaf)) |deps| {
            for (deps) |dep| if (dep == atom) return false;
        }
        return true;
    }

    fn computeAvoidable(self: *EGraph, atom: LeafId) ![]const bool {
        const avoid = try self.allocator.alloc(bool, self.parents.items.len);
        @memset(avoid, false);
        while (true) {
            var changed = false;
            node_loop: for (self.nodes.items) |stored| {
                const root = self.find(stored.class);
                if (avoid[root]) continue;
                switch (stored.node) {
                    .leaf => |leaf| if (!self.leafAvoids(leaf, atom)) {
                        continue :node_loop;
                    },
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
    pub fn depGateAllows(
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
                    if (!try self.classAvoids(self.find(c), atom, cache)) {
                        return false;
                    }
                },
            }
        }
        return true;
    }

    /// Cached `avoidable(class, atom)` lookup (see `computeAvoidable`).
    /// `root` must be a canonical class id.
    pub fn classAvoids(
        self: *EGraph,
        root: EClassId,
        atom: LeafId,
        cache: *AvoidCache,
    ) !bool {
        const gop = try cache.getOrPut(self.allocator, atom);
        if (!gop.found_existing) {
            gop.value_ptr.* = try self.computeAvoidable(atom);
        }
        const avoid = gop.value_ptr.*;
        return root < avoid.len and avoid[root];
    }

    fn canonicalize(self: *const EGraph, node: ENode) !ENode {
        return self.canonicalizeInto(node, null, self.allocator, .splice);
    }

    fn canonicalizeWith(
        self: *const EGraph,
        node: ENode,
        self_class: ?EClassId,
    ) SpliceError!ENode {
        return self.canonicalizeInto(node, self_class, self.allocator, .splice);
    }

    /// `.no_splice` is the fallback shape after a `SpliceCapped` trip:
    /// members are find-updated and sorted but member classes denoting
    /// same-head bags stay atomic, so equal multisets may intern as
    /// distinct shapes. Callers count the trip in `ac_match_capped_total`
    /// (missed congruent joins weaken a forced negative).
    const SpliceMode = enum { splice, no_splice };

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
        mode: SpliceMode,
    ) SpliceError!ENode {
        switch (node) {
            .leaf => return node,
            .app => |app| {
                // An AC-policied binary application interns as a bag.
                if (app.children.len == 2 and
                    app.children[0] == .class and
                    app.children[1] == .class and
                    self.ac_heads.contains(app.term_id))
                {
                    const members: [2]EClassId = .{
                        app.children[0].class,
                        app.children[1].class,
                    };
                    return switch (mode) {
                        .splice => try self.canonicalBag(
                            app.term_id,
                            &members,
                            self_class,
                            alloc,
                        ),
                        .no_splice => try self.sortMembersOnly(.{
                            .term_id = app.term_id,
                            .members = &members,
                        }, alloc),
                    };
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
            .bag => |bag| return switch (mode) {
                .splice => try self.canonicalBag(
                    bag.term_id,
                    bag.members,
                    self_class,
                    alloc,
                ),
                .no_splice => try self.sortMembersOnly(bag, alloc),
            },
        }
    }

    fn bagKey(term_id: u32, root: EClassId) u64 {
        return (@as(u64, term_id) << 32) | root;
    }

    /// Splice, canonicalize, and sort bag members: any member class that
    /// denotes a same-head bag contributes its members instead of itself
    /// (recursively), so every grouping of the same multiset interns to
    /// one shape. Uses the canonical (exempted) index.
    const SpliceError = error{ OutOfMemory, SpliceCapped };

    fn canonicalBag(
        self: *const EGraph,
        term_id: u32,
        members: []const EClassId,
        self_class: ?EClassId,
        alloc: std.mem.Allocator,
    ) SpliceError!ENode {
        return try self.spliceBag(
            &self.bag_in_class,
            term_id,
            members,
            self_class,
            alloc,
        );
    }

    /// `canonicalBag` over the FULL (unexempted) view — the shape a
    /// splice twin carries so flat arrivals congruence-join the class
    /// even where the canonical form keeps an atomic member.
    fn fullSplice(
        self: *const EGraph,
        term_id: u32,
        members: []const EClassId,
        self_class: ?EClassId,
        alloc: std.mem.Allocator,
    ) SpliceError!ENode {
        return try self.spliceBag(
            &self.bag_node_index,
            term_id,
            members,
            self_class,
            alloc,
        );
    }

    fn spliceBag(
        self: *const EGraph,
        index: *const std.AutoArrayHashMapUnmanaged(u64, ENodeId),
        term_id: u32,
        members: []const EClassId,
        self_class: ?EClassId,
        alloc: std.mem.Allocator,
    ) SpliceError!ENode {
        var out: std.ArrayListUnmanaged(EClassId) = .{};
        var visited: std.ArrayListUnmanaged(EClassId) = .{};
        if (self_class) |class| {
            try visited.append(alloc, self.find(class));
        }
        for (members) |member| {
            try self.spliceInto(
                index,
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
    /// class denotes one in `index`. `visited` is the ancestor set of the
    /// current expansion: re-entering a class keeps it atomic, so bags
    /// over cyclic classes (absorption-style unions) stay finite. The
    /// cost is full canonicality in that corner — strictly better than
    /// the unbounded minting the same corner causes in tree
    /// representation. The guard is per-path, though, so shared classes
    /// still expand once per reference and the flat form can outgrow the
    /// node graph exponentially; `max_splice_members` abandons such an
    /// expansion whole (see the constant's doc).
    fn spliceInto(
        self: *const EGraph,
        index: *const std.AutoArrayHashMapUnmanaged(u64, ENodeId),
        term_id: u32,
        root: EClassId,
        out: *std.ArrayListUnmanaged(EClassId),
        visited: *std.ArrayListUnmanaged(EClassId),
        alloc: std.mem.Allocator,
    ) SpliceError!void {
        if (out.items.len >= max_splice_members) return error.SpliceCapped;
        const bag_node = index.get(bagKey(term_id, root)) orelse {
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
                index,
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

    pub const Match = struct {
        rule_slot: u32,
        root_node: ENodeId,
        subst: []const ?Child,
        /// Unmatched bag members (canonical roots at match time) of an AC
        /// match; the apply loop wraps the target with them.
        extension: []const EClassId = &.{},
        /// Effect key at collection time (see `matchEffectKey`).
        key: u64,
    };

    /// Content key of a match's effect: the union it applies is fully
    /// determined by the rule, the matched class, the canonical
    /// substitution, and the extension multiset. Two matches sharing a key
    /// are interchangeable — once either is applied the other is a no-op —
    /// so collection retains only the first (which is also the one the
    /// pre-dedup apply order would have recorded the explanation edge for).
    pub fn matchEffectKey(
        self: *EGraph,
        rule_slot: u32,
        root_node: ENodeId,
        subst: []const ?Child,
        extension: []const EClassId,
    ) u64 {
        var h = std.hash.Wyhash.init(0x0136);
        h.update(std.mem.asBytes(&rule_slot));
        const root = self.find(self.nodes.items[root_node].class);
        h.update(std.mem.asBytes(&root));
        for (subst) |entry| {
            var tag: u8 = 0;
            var value: u64 = 0;
            if (entry) |child| switch (child) {
                .class => |id| {
                    tag = 1;
                    value = self.find(id);
                },
                .bound => |leaf| {
                    tag = 2;
                    value = leaf;
                },
            };
            h.update(std.mem.asBytes(&tag));
            h.update(std.mem.asBytes(&value));
        }
        // Extension entries are canonical roots in member order; members
        // are kept sorted by root, so the order is stable across nodes of
        // one class. (An unsorted slice would only weaken dedup, never
        // conflate distinct effects.)
        h.update(std.mem.sliceAsBytes(extension));
        return h.final();
    }

    /// Match dedup state for the egraph's lifetime (see the `match_dedup`
    /// field). `applied` persists across iterations AND `saturate` calls: a
    /// key goes in only once its union has actually been applied
    /// (union-find merges are monotone, so an identical later match is
    /// guaranteed a no-op). Dep-deferred matches are NOT recorded, so
    /// they are re-collected and retried next iteration. `iter` additionally
    /// collapses same-effect matches within one collection pass. Maps live
    /// on the egraph arena like every other egraph structure.
    pub const MatchDedup = struct {
        applied: std.AutoHashMapUnmanaged(u64, void) = .{},
        iter: std.AutoHashMapUnmanaged(u64, void) = .{},
    };

    /// Anchor of a `matchRule` call in progress (see `match_anchor`).
    const MatchAnchor = struct { root: EClassId, node: ENodeId };

    fn matchRule(
        self: *EGraph,
        rule: Rule,
        rule_slot: u32,
        root_node: ENodeId,
        matches: *std.ArrayListUnmanaged(Match),
        dedup: *MatchDedup,
        scratch: std.mem.Allocator,
    ) !void {
        const pattern = rule.match_side.app;
        const node = self.nodes.items[root_node].node.app;
        self.ac_active_target = rule.target_side;
        defer self.ac_active_target = null;
        self.match_anchor = .{
            .root = self.find(self.nodes.items[root_node].class),
            .node = root_node,
        };
        defer self.match_anchor = null;
        const pairs = try scratch.alloc(PatternPair, pattern.args.len);
        for (pattern.args, node.children, 0..) |p, c, idx| {
            pairs[idx] = .{ .pattern = p, .child = c };
        }
        const subst = try scratch.alloc(?Child, rule.num_binders);
        @memset(subst, null);

        // Solutions stage in scratch; only new-effect ones are copied into
        // the run allocator and retained.
        var solutions: std.ArrayListUnmanaged([]const ?Child) = .{};
        try self.solvePairs(pairs, 0, subst, &solutions, scratch, scratch);
        for (solutions.items) |solution| {
            const key = self.matchEffectKey(rule_slot, root_node, solution, &.{});
            if (dedup.applied.contains(key)) continue;
            const gop = try dedup.iter.getOrPut(self.allocator, key);
            if (gop.found_existing) continue;
            try matches.append(self.allocator, .{
                .rule_slot = rule_slot,
                .root_node = root_node,
                .subst = try self.allocator.dupe(?Child, solution),
                .key = key,
            });
        }
    }

    pub const PatternPair = struct {
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
    pub fn flattenPattern(
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

    /// True when binding this binder to any sub-multiset and rejoining the
    /// leftover as extension splices to the same flat bag as binding the
    /// full residual: the binder is absent from the rule's target side, or
    /// every occurrence lies on the target's same-head spine (the target
    /// IS the binder, or the binder sits directly under the AC head).
    /// Unit and annihilator rules (x+0→x, x·0→0) are the archetypes —
    /// without this cut their subset enumeration mints one sub-bag and one
    /// union per sub-multiset of every matching bag, an exponential
    /// attractor of derivable-but-useless facts.
    fn binderResidualOnly(
        self: *const EGraph,
        term_id: u32,
        binder_idx: u32,
    ) bool {
        const target = self.ac_active_target orelse return false;
        return !binderOccursStructurally(target, term_id, binder_idx, true);
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
        dedup: *MatchDedup,
        scratch: std.mem.Allocator,
    ) !void {
        const bag = self.nodes.items[root_node].node.bag;
        self.ac_active_target = rule.target_side;
        defer self.ac_active_target = null;
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
            scratch,
            scratch,
        );
        for (solutions.items) |solution| {
            const key = self.matchEffectKey(
                rule_slot,
                root_node,
                solution.subst,
                solution.extension,
            );
            if (dedup.applied.contains(key)) continue;
            const gop = try dedup.iter.getOrPut(self.allocator, key);
            if (gop.found_existing) continue;
            try matches.append(self.allocator, .{
                .rule_slot = rule_slot,
                .root_node = root_node,
                .subst = try self.allocator.dupe(?Child, solution.subst),
                .extension = try self.allocator.dupe(
                    EClassId,
                    solution.extension,
                ),
                .key = key,
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
                    // Occurrence dedup: members are sorted by canonical
                    // root, so equal-class occurrences are adjacent; claim
                    // only the leftmost unused one. Any occurrence of the
                    // same class yields the same substitution and the same
                    // extension multiset, so the others are pure duplicates.
                    if (idx > 0 and !used[idx - 1] and
                        self.find(bag.members[idx - 1]) == self.find(member))
                    {
                        continue;
                    }
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
                // A sole trailing unbound binder takes the full residual
                // outright when subset choices are provably redundant: an
                // exact-cover match (no extension) leaves it no other
                // option, and a residual-only binder makes every
                // subset/extension split splice-equivalent to the full
                // residual (see binderResidualOnly).
                if (p_idx == pattern_members.len - 1 and
                    subst[binder_idx] == null and
                    (!allow_extension or
                        self.binderResidualOnly(
                            bag.term_id,
                            @intCast(binder_idx),
                        )))
                {
                    var residual: std.ArrayListUnmanaged(usize) = .{};
                    for (used, 0..) |is_used, i| {
                        if (!is_used) try residual.append(scratch, i);
                    }
                    if (residual.items.len == 0) return;
                    for (residual.items) |i| used[i] = true;
                    defer for (residual.items) |i| {
                        used[i] = false;
                    };
                    try self.applyBinderSubset(
                        bag,
                        pattern_members,
                        p_idx,
                        subst,
                        used,
                        allow_extension,
                        solutions,
                        binder_idx,
                        residual.items,
                        dest,
                        scratch,
                    );
                    return;
                }
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
            // Occurrence dedup (see the structured-member arm): a subset
            // may pick a later occurrence of a class only when every
            // earlier equal-class occurrence is already used, so each
            // distinct class sub-multiset is enumerated exactly once.
            if (idx > 0 and !used[idx - 1] and
                self.find(bag.members[idx - 1]) == self.find(bag.members[idx]))
            {
                continue;
            }
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
    pub fn solvePairs(
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
                    // Cycle guard: a structured subpattern descending
                    // into the ANCHOR's own class is matching the
                    // anchor inside itself — only possible once a class
                    // contains a node built over the class (a vacuous
                    // substitution image `[x/z]p ~ p`, or a pool
                    // equation merging a term with its own subterm).
                    // Such a class can still hold finite members that
                    // legitimately match, so the descent proceeds — but
                    // only over members OLDER than the anchor node.
                    // Anything the current saturation's own fires mint
                    // through this anchor is appended later, so the age
                    // filter breaks the debris loop where each pass
                    // re-derives a one-level-deeper image of the
                    // previous mint (the mint outruns the collapse that
                    // proves it redundant by one iteration). Skipping a
                    // younger candidate is conservative, so it counts
                    // as a budget-style trip against forced negatives.
                    const anchor_cap: ?ENodeId = cap: {
                        const anchor = self.match_anchor orelse
                            break :cap null;
                        break :cap if (root == anchor.root)
                            anchor.node
                        else
                            null;
                    };
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
                                if (anchor_cap) |cap_node| {
                                    if (member_id >= cap_node) {
                                        self.ac_match_capped_total += 1;
                                        continue;
                                    }
                                }
                                // Per-candidate charge (the tree analogue
                                // of the bag arms' enumeration charges):
                                // a nested pattern against merge-heavy
                                // classes branches here, members ^ depth
                                // worklist allocations that all live until
                                // the (rule, node) call returns. Every
                                // solution and every recursion passes
                                // through a charged candidate, so this
                                // bounds the whole tree enumeration.
                                if (self.ac_budget_remaining == 0) {
                                    self.ac_budget_hit = true;
                                    return;
                                }
                                self.ac_budget_remaining -= 1;
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
                                if (anchor_cap) |cap_node| {
                                    if (member_id >= cap_node) {
                                        self.ac_match_capped_total += 1;
                                        continue;
                                    }
                                }
                                // Same per-candidate charge as the app
                                // arm; the bag assignment below charges
                                // its own enumeration on top.
                                if (self.ac_budget_remaining == 0) {
                                    self.ac_budget_hit = true;
                                    return;
                                }
                                self.ac_budget_remaining -= 1;
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

    pub fn bindingsCompatible(self: *const EGraph, a: Child, b: Child) bool {
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
    pub fn instantiate(
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
        var ctx = explain_mod.ExplainCtx{
            .eg = self,
            .rules = rules,
            .opts = opts,
        };
        if (!try ctx.explainTerms(from, to, &.{})) return null;
        return ctx.steps.items;
    }
};

test {
    _ = @import("egraph/tests.zig");
}
