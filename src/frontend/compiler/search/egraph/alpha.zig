//! Alpha pairing scheduler for the `conversion?` egraph: pairs up
//! match-side instances of each `@conversion alpha` rule whose bodies
//! correspond under a lexical renaming and retains matches that fire the
//! generic rule with the fresh binder slot completed by the partner's
//! atom (`collectAlphaMatches`, called from `EGraph.saturate`).
//!
//! Split out of `egraph.zig`: functions take the graph as `self`, and the
//! state the scheduler drives — the settled-instance cache
//! (`alpha_settled`), the incremental-scan watermarks, and the
//! filter-skip / pair counters — lives on the `EGraph` itself.

const std = @import("std");

const eg_mod = @import("../egraph.zig");
const EGraph = eg_mod.EGraph;
const EClassId = eg_mod.EClassId;
const ENodeId = eg_mod.ENodeId;
const LeafId = eg_mod.LeafId;
const Child = eg_mod.Child;
const Rule = eg_mod.Rule;
const SaturateOptions = eg_mod.SaturateOptions;
const Match = EGraph.Match;
const MatchDedup = EGraph.MatchDedup;
const AvoidCache = EGraph.AvoidCache;
const PatternPair = EGraph.PatternPair;

/// One matched instance of an alpha rule's match side: the anchor
/// node, its solved substitution (fresh slot still null), and the
/// bound atom at the renamed slot.
pub const AlphaInstance = struct {
    node: ENodeId,
    root: EClassId,
    subst: []const ?Child,
    atom: LeafId,
};

/// One lexical rename binding: descending through a pair of
/// corresponding binder positions maps the left atom to the right
/// one for the subtrees in scope.
const RenamePair = struct { old: LeafId, new: LeafId };

/// Nesting bound for the renaming environment. Ordinary terms stay
/// within their binder depth; only a binder cycle through a class (a
/// self-referential union) can grow the environment past it, where
/// the walk would otherwise extend it forever. A trip is an
/// approximate refusal, counted in `alpha_filter_skips`.
const max_rename_depth = 32;

/// `renamedEq` memo keyed by canonical class pair PLUS the full
/// renaming environment, one collection pass long (no unions land
/// while collecting, so roots are stable). The environment is part
/// of the key because the same class pair can correspond under one
/// renaming and not another — an environment-blind key would let a
/// decoy instance pair poison a later valid pair's verdict. An
/// in-progress entry reads as `false`: cycles resolve conservatively
/// (counted in `alpha_filter_skips`). Key environments alias
/// pass-scratch slices, so the memo must not outlive the pass.
const RenameVerdict = enum { in_progress, no, yes };
const RenameKey = struct {
    c: EClassId,
    d: EClassId,
    env: []const RenamePair,
};
const RenameKeyContext = struct {
    pub fn hash(_: RenameKeyContext, key: RenameKey) u64 {
        var h = std.hash.Wyhash.init(0x9e3779b97f4a7c15);
        h.update(std.mem.asBytes(&key.c));
        h.update(std.mem.asBytes(&key.d));
        for (key.env) |e| {
            h.update(std.mem.asBytes(&e.old));
            h.update(std.mem.asBytes(&e.new));
        }
        return h.final();
    }
    pub fn eql(_: RenameKeyContext, a: RenameKey, b: RenameKey) bool {
        if (a.c != b.c or a.d != b.d) return false;
        if (a.env.len != b.env.len) return false;
        for (a.env, b.env) |ea, eb| {
            if (ea.old != eb.old or ea.new != eb.new) return false;
        }
        return true;
    }
};
const RenameMemo = std.HashMapUnmanaged(
    RenameKey,
    RenameVerdict,
    RenameKeyContext,
    std.hash_map.default_max_load_percentage,
);

/// Alpha scheduler: pair up match-side instances of each `alpha` rule
/// whose bodies correspond under a lexical renaming — the anchor
/// atom pair, extended through nested binder pairs as the walk
/// descends — and retain a match that fires the GENERIC rule with
/// the fresh binder slot completed by the partner's atom. The
/// applied union is a literal theorem instance (`A x p ~ A z
/// ([x/z] p)`); the enrolled substitution rules plus gated
/// congruence close the remaining gap to the partner, so extraction
/// sees only ordinary edges. A pair differing at SEVERAL binder
/// depths closes outside-in: only the outermost instance fires now;
/// once substitution commutation (an enrolled sb rule per nestable
/// binder head — a documented theory prerequisite) pushes the image
/// through the inner binder, a later pass discovers the materialized
/// inner pair as an ordinary depth-one candidate.
/// The correspondence check is a firing FILTER for economy,
/// never for soundness — the dep gate refuses capture at apply time
/// regardless — and it is approximate by design (greedy bag
/// alignment, cycle-conservative, budget-bounded). Approximate
/// resolutions are counted in `alpha_filter_skips` (reset here, so
/// the count always describes the latest pass): a saturated miss is
/// a forced negative only when the final pass counted none.
///
/// The scan is INCREMENTAL across passes. Every semantic change to
/// the egraph flows through the union log (nodes are append-only and
/// a new node starts its own class), so a pass first derives the set
/// of DIRTY roots — classes whose downward-reachable structure
/// changed since the last committed pass — by seeding from the
/// union-log delta and propagating upward through node children to a
/// fixpoint. A committed verdict depends only on structure reachable
/// downward from the pair's instances (correspondence walk, dep
/// gate, and `classAvoids` alike), so instances on clean classes
/// keep their committed verdicts: only new/dirty nodes are
/// re-solved, and only pairs with a fresh side are re-compared.
/// Verdict-stable skipped pairs also need no retry for firing: an
/// applied pair is in the dedup ledger, and a dep-deferred pair's
/// gate can only open when its structure changes, which dirties it.
/// A pass COMMITS (advances the watermarks and the settled cache)
/// only when it ran to completion with zero approximate resolutions;
/// otherwise the next pass re-derives the same delta with fresh
/// budget — exactly the retry the full rescan used to provide.
pub fn collectAlphaMatches(
    self: *EGraph,
    rules: []const Rule,
    opts: SaturateOptions,
    matches: *std.ArrayListUnmanaged(Match),
    dedup: *MatchDedup,
    iter_steps: *usize,
    iter_capped: *bool,
    scratch: std.mem.Allocator,
) !void {
    var avoid_cache: AvoidCache = .{};
    self.alpha_filter_skips = 0;
    const node_mark = self.nodes.items.len;
    const union_mark = self.unions.items.len;
    const dirty = try collectDirtyRoots(self, scratch);

    // Scratch entry: an instance plus whether this pass solved it
    // (fresh) or the settled cache supplied it (clean).
    const Entry = struct { inst: AlphaInstance, fresh: bool };
    const Pending = struct {
        rule_slot: u32,
        entries: []const Entry,
    };
    var pending: std.ArrayListUnmanaged(Pending) = .{};
    var complete = true;

    collect: for (rules, 0..) |rule, rule_slot| {
        if (!rule.alpha) continue;
        if (rule.match_side != .app) continue;
        const pattern = rule.match_side.app;

        // Settled instances on clean classes keep their verdicts;
        // ones on dirty classes are superseded by the re-solve below.
        var clean: std.ArrayListUnmanaged(AlphaInstance) = .{};
        if (self.alpha_settled.get(@intCast(rule_slot))) |cached| {
            for (cached.items) |inst| {
                if (dirty.contains(self.find(inst.root))) continue;
                try clean.append(scratch, inst);
            }
        }

        var fresh: std.ArrayListUnmanaged(AlphaInstance) = .{};
        for (self.nodes.items, 0..) |stored, node_id| {
            const app = switch (stored.node) {
                .app => |a| a,
                else => continue,
            };
            if (app.term_id != pattern.term_id) continue;
            if (app.children.len != pattern.args.len) continue;
            const root = self.find(stored.class);
            if (node_id < self.alpha_node_watermark and
                !dirty.contains(root)) continue;
            if (!chargeAlphaStep(self, iter_steps, iter_capped)) {
                complete = false;
                break :collect;
            }
            const pairs = try scratch.alloc(
                PatternPair,
                pattern.args.len,
            );
            for (pattern.args, app.children, 0..) |p, c, idx| {
                pairs[idx] = .{ .pattern = p, .child = c };
            }
            const subst = try scratch.alloc(?Child, rule.num_binders);
            @memset(subst, null);
            const allotted = @min(opts.ac_match_budget, iter_steps.*);
            self.ac_budget_remaining = allotted;
            self.ac_budget_hit = false;
            var solutions: std.ArrayListUnmanaged([]const ?Child) = .{};
            try self.solvePairs(
                pairs,
                0,
                subst,
                &solutions,
                scratch,
                scratch,
            );
            iter_steps.* -= allotted - self.ac_budget_remaining;
            if (self.ac_budget_hit) {
                self.ac_match_capped_total += 1;
                // A truncated enumeration may have dropped instances,
                // so this pass's verdicts are no longer exact.
                self.alpha_filter_skips += 1;
            }
            for (solutions.items) |sol| {
                const binding = sol[rule.alpha_old_slot] orelse continue;
                if (binding != .bound) continue;
                try fresh.append(scratch, .{
                    .node = @intCast(node_id),
                    .root = root,
                    .subst = sol,
                    .atom = binding.bound,
                });
            }
        }

        // Merge clean and fresh by node id (both are node-ordered)
        // so pair enumeration order matches the full rescan's.
        var entries = try scratch.alloc(
            Entry,
            clean.items.len + fresh.items.len,
        );
        {
            var ci: usize = 0;
            var fi: usize = 0;
            for (entries) |*slot| {
                const take_clean = fi >= fresh.items.len or
                    (ci < clean.items.len and
                        clean.items[ci].node < fresh.items[fi].node);
                if (take_clean) {
                    slot.* = .{ .inst = clean.items[ci], .fresh = false };
                    ci += 1;
                } else {
                    slot.* = .{ .inst = fresh.items[fi], .fresh = true };
                    fi += 1;
                }
            }
        }

        if (fresh.items.len == 0) {
            // No fresh side means no comparable pair; keep the
            // settled entries for the commit below.
            try pending.append(scratch, .{
                .rule_slot = @intCast(rule_slot),
                .entries = entries,
            });
            continue;
        }
        var memo: RenameMemo = .{};
        for (entries, 0..) |ea, i| {
            for (entries[i + 1 ..]) |eb| {
                // Both sides clean: the verdict was committed by an
                // exact pass and nothing it depends on changed.
                if (!ea.fresh and !eb.fresh) continue;
                const a = ea.inst;
                const b = eb.inst;
                if (a.atom == b.atom) continue;
                if (a.root == b.root) continue;
                if (!chargeAlphaStep(self, iter_steps, iter_capped)) {
                    complete = false;
                    break :collect;
                }
                self.alpha_pairs_compared_total += 1;
                if (!try alphaInstancesCorrespond(
                    self,
                    rule,
                    a,
                    b,
                    &memo,
                    &avoid_cache,
                    iter_steps,
                    iter_capped,
                    scratch,
                )) continue;
                try appendAlphaMatch(
                    self,
                    rule,
                    @intCast(rule_slot),
                    a,
                    b,
                    matches,
                    dedup,
                    &avoid_cache,
                );
                if (matches.items.len >= opts.ac_iter_match_budget) {
                    iter_capped.* = true;
                    self.ac_match_capped_total += 1;
                    complete = false;
                    break :collect;
                }
            }
        }

        try pending.append(scratch, .{
            .rule_slot = @intCast(rule_slot),
            .entries = entries,
        });
    }

    if (!complete or self.alpha_filter_skips != 0) return;
    // Commit: with the watermarks advanced, the merged entry lists
    // become the settled caches. Clean substs already live on the
    // egraph allocator; fresh ones move off the pass scratch here.
    for (pending.items) |p| {
        const gop = try self.alpha_settled.getOrPut(
            self.allocator,
            p.rule_slot,
        );
        if (!gop.found_existing) gop.value_ptr.* = .{};
        const list = gop.value_ptr;
        list.clearRetainingCapacity();
        for (p.entries) |entry| {
            var inst = entry.inst;
            if (entry.fresh) {
                inst.subst = try self.allocator.dupe(?Child, inst.subst);
            }
            try list.append(self.allocator, inst);
        }
    }
    self.alpha_node_watermark = node_mark;
    self.alpha_union_watermark = union_mark;
}

/// Roots whose downward-reachable structure changed since
/// `alpha_union_watermark`: seeded from the union-log delta (every
/// class-content change is a union; new nodes start fresh classes),
/// then propagated upward through node children until a fixpoint.
/// Like `rebuild`, this is a repeated full-node scan — each round
/// marks at least one new root or stops, and rounds are bounded by
/// the term dag's height.
fn collectDirtyRoots(
    self: *EGraph,
    scratch: std.mem.Allocator,
) !std.AutoHashMapUnmanaged(EClassId, void) {
    var dirty: std.AutoHashMapUnmanaged(EClassId, void) = .{};
    for (self.unions.items[self.alpha_union_watermark..]) |edge| {
        try dirty.put(scratch, self.find(edge.a), {});
    }
    if (dirty.count() == 0) return dirty;
    var spread = true;
    while (spread) {
        spread = false;
        for (self.nodes.items) |stored| {
            const root = self.find(stored.class);
            if (dirty.contains(root)) continue;
            const touches = switch (stored.node) {
                .leaf => false,
                .app => |app| blk: {
                    for (app.children) |child| switch (child) {
                        .class => |c| if (dirty.contains(
                            self.find(c),
                        )) break :blk true,
                        .bound => {},
                    };
                    break :blk false;
                },
                .bag => |bag| blk: {
                    for (bag.members) |member| {
                        if (dirty.contains(self.find(member))) {
                            break :blk true;
                        }
                    }
                    break :blk false;
                },
            };
            if (!touches) continue;
            try dirty.put(scratch, root, {});
            spread = true;
        }
    }
    return dirty;
}

/// Charge one unit of the shared iteration step budget; a trip caps
/// the collection pass (counted like every other budget trip).
fn chargeAlphaStep(
    self: *EGraph,
    iter_steps: *usize,
    iter_capped: *bool,
) bool {
    if (iter_steps.* == 0) {
        iter_capped.* = true;
        self.ac_match_capped_total += 1;
        return false;
    }
    iter_steps.* -= 1;
    return true;
}

/// Do two instances' substitutions correspond under renaming
/// `a.atom` to `b.atom`? Bound slots other than the renamed one must
/// bind identical atoms distinct from both rename endpoints; term
/// slots must satisfy `renamedEq` under the singleton environment —
/// the body walk extends it lexically at nested binder pairs.
fn alphaInstancesCorrespond(
    self: *EGraph,
    rule: Rule,
    a: AlphaInstance,
    b: AlphaInstance,
    memo: *RenameMemo,
    avoid_cache: *AvoidCache,
    iter_steps: *usize,
    iter_capped: *bool,
    scratch: std.mem.Allocator,
) error{OutOfMemory}!bool {
    // Scratch-allocated (not stack): memo keys alias this slice and
    // outlive the call.
    const env = try scratch.alloc(RenamePair, 1);
    env[0] = .{ .old = a.atom, .new = b.atom };
    for (a.subst, b.subst, 0..) |ea, eb, slot| {
        if (slot == rule.alpha_old_slot) continue;
        if (slot == rule.alpha_new_slot) continue;
        const ca = ea orelse {
            if (eb == null) continue;
            return false;
        };
        const cb = eb orelse return false;
        switch (ca) {
            .bound => |la| {
                if (cb != .bound) return false;
                // A second bound slot touching either rename endpoint
                // is doomed at the distinctness gate anyway.
                if (la == a.atom or cb.bound == b.atom) return false;
                if (cb.bound != la) return false;
            },
            .class => |cc| {
                if (cb != .class) return false;
                if (!try renamedEq(
                    self,
                    cc,
                    cb.class,
                    env,
                    memo,
                    avoid_cache,
                    iter_steps,
                    iter_capped,
                    scratch,
                )) return false;
            },
        }
    }
    return true;
}

/// Lexical atom correspondence under a renaming environment: the
/// innermost entry mentioning the left atom on its old side or the
/// right atom on its new side decides; atoms no entry mentions must
/// be equal. The one-sided triggers are what make shadowing
/// explicit — an atom rebound further in refers to the inner
/// binder, and a right atom equal to some entry's new side is bound
/// there, never free.
fn atomsCorrespond(env: []const RenamePair, a: LeafId, b: LeafId) bool {
    var i = env.len;
    while (i > 0) {
        i -= 1;
        const e = env[i];
        if (e.old == a or e.new == b) return e.old == a and e.new == b;
    }
    return a == b;
}

/// Equal classes correspond under `env` exactly when the renaming
/// is the identity on them: the class must avoid every effectively
/// renamed atom (innermost entry per old atom decides; identity
/// entries rename nothing). The entries' new sides are deliberately
/// ignored, mirroring the single-rename rule: a capture this admits
/// is refused by the dep gate at fire time.
fn classAvoidsEnv(
    self: *EGraph,
    root: EClassId,
    env: []const RenamePair,
    cache: *AvoidCache,
) !bool {
    outer: for (env, 0..) |e, i| {
        if (e.old == e.new) continue;
        for (env[i + 1 ..]) |inner| {
            if (inner.old == e.old) continue :outer;
        }
        if (!try self.classAvoids(root, e.old, cache)) return false;
    }
    return true;
}

/// Approximate check that class `d` denotes `c` renamed per `env`
/// (innermost entry last). Equal classes correspond when the
/// renaming is the identity on them; a mapped atom's own leaf class
/// corresponds to its image's; otherwise some member-node pair must
/// correspond structurally, extending the environment through
/// nested binder pairs. False negatives skip a fire; false
/// positives cost one refused-or-useless (but sound) instance.
fn renamedEq(
    self: *EGraph,
    c: EClassId,
    d: EClassId,
    env: []const RenamePair,
    memo: *RenameMemo,
    avoid_cache: *AvoidCache,
    iter_steps: *usize,
    iter_capped: *bool,
    scratch: std.mem.Allocator,
) error{OutOfMemory}!bool {
    const rc = self.find(c);
    const rd = self.find(d);
    if (rc == rd) return classAvoidsEnv(self, rc, env, avoid_cache);
    {
        var i = env.len;
        while (i > 0) {
            i -= 1;
            const e = env[i];
            const xc = self.leaf_classes.get(e.old) orelse continue;
            const zc = self.leaf_classes.get(e.new) orelse continue;
            if (self.find(xc) == rc and self.find(zc) == rd and
                atomsCorrespond(env, e.old, e.new)) return true;
        }
    }
    const key = RenameKey{ .c = rc, .d = rd, .env = env };
    if (memo.get(key)) |cached| switch (cached) {
        .yes => return true,
        .no => return false,
        // In-progress pairs read false: a correspondence may not
        // assume itself on a cyclic class. That verdict is
        // conservative, not exact — count it.
        .in_progress => {
            self.alpha_filter_skips += 1;
            return false;
        },
    };
    try memo.put(scratch, key, .in_progress);
    var result = false;
    if (self.class_index.get(rc)) |ca| {
        if (self.class_index.get(rd)) |cb| {
            outer: for (ca.items) |na| {
                for (cb.items) |nb| {
                    if (!chargeAlphaStep(self, iter_steps, iter_capped)) {
                        break :outer;
                    }
                    if (try renamedNodeEq(
                        self,
                        na,
                        nb,
                        env,
                        memo,
                        avoid_cache,
                        iter_steps,
                        iter_capped,
                        scratch,
                    )) {
                        result = true;
                        break :outer;
                    }
                }
            }
        }
    }
    try memo.put(scratch, key, if (result) RenameVerdict.yes else .no);
    return result;
}

fn renamedNodeEq(
    self: *EGraph,
    na: ENodeId,
    nb: ENodeId,
    env: []const RenamePair,
    memo: *RenameMemo,
    avoid_cache: *AvoidCache,
    iter_steps: *usize,
    iter_capped: *bool,
    scratch: std.mem.Allocator,
) error{OutOfMemory}!bool {
    const a = self.nodes.items[na].node;
    const b = self.nodes.items[nb].node;
    switch (a) {
        // Equal leaves share a class and never reach here; a
        // cross-class leaf pair corresponds only through the
        // environment.
        .leaf => |la| return b == .leaf and
            atomsCorrespond(env, la, b.leaf),
        .app => |aa| {
            if (b != .app) return false;
            const ba = b.app;
            if (aa.term_id != ba.term_id) return false;
            if (aa.children.len != ba.children.len) return false;
            // Binder positions are BINDING occurrences: each pair
            // extends the lexical environment for every child of
            // this node — including equal-atom pairs, whose entries
            // shadow any outer entry touching either atom. Scope is
            // over-approximated to all siblings; an argument outside
            // the binder's real scope cannot contain it, so the
            // extra entry is vacuous there.
            var bound_pairs: usize = 0;
            for (aa.children, ba.children) |ac, bc| {
                if ((ac == .bound) != (bc == .bound)) return false;
                if (ac == .bound) bound_pairs += 1;
            }
            var inner = env;
            if (bound_pairs != 0) {
                if (env.len + bound_pairs > max_rename_depth) {
                    // Only a binder cycle through a class nests this
                    // deep; refuse approximately.
                    self.alpha_filter_skips += 1;
                    return false;
                }
                const ext = try scratch.alloc(
                    RenamePair,
                    env.len + bound_pairs,
                );
                @memcpy(ext[0..env.len], env);
                var at = env.len;
                for (aa.children, ba.children) |ac, bc| {
                    if (ac != .bound) continue;
                    ext[at] = .{ .old = ac.bound, .new = bc.bound };
                    at += 1;
                }
                inner = ext;
            }
            for (aa.children, ba.children) |ac, bc| {
                if (ac != .class) continue;
                if (!try renamedEq(
                    self,
                    ac.class,
                    bc.class,
                    inner,
                    memo,
                    avoid_cache,
                    iter_steps,
                    iter_capped,
                    scratch,
                )) return false;
            }
            return true;
        },
        .bag => |ab| {
            if (b != .bag) return false;
            const bb = b.bag;
            if (ab.term_id != bb.term_id) return false;
            if (ab.members.len != bb.members.len) return false;
            // Greedy multiset alignment: consume equal rename-inert
            // roots first, then first-fit renamed partners. Greedy
            // failures are affordable false negatives.
            const used = try scratch.alloc(bool, bb.members.len);
            @memset(used, false);
            for (ab.members) |ma| {
                const ra = self.find(ma);
                var placed = false;
                for (bb.members, 0..) |mb, idx| {
                    if (used[idx]) continue;
                    if (self.find(mb) != ra) continue;
                    if (!try classAvoidsEnv(self, ra, env, avoid_cache)) {
                        continue;
                    }
                    used[idx] = true;
                    placed = true;
                    break;
                }
                if (placed) continue;
                for (bb.members, 0..) |mb, idx| {
                    if (used[idx]) continue;
                    if (try renamedEq(
                        self,
                        ma,
                        mb,
                        env,
                        memo,
                        avoid_cache,
                        iter_steps,
                        iter_capped,
                        scratch,
                    )) {
                        used[idx] = true;
                        placed = true;
                        break;
                    }
                }
                if (!placed) {
                    // A greedy failure may be a false negative (an
                    // earlier first-fit placement can consume this
                    // member's only partner) — count it.
                    self.alpha_filter_skips += 1;
                    return false;
                }
            }
            return true;
        },
    }
}

/// Retain one direction of a corresponding pair: fire anchored at
/// `a` renaming toward `b`'s atom when the dep gate admits it now,
/// else the reverse anchor (capture can be one-sided). A pair the
/// gate refuses both ways is still retained forward: gating is
/// monotone, so the deferred match retries like any other.
fn appendAlphaMatch(
    self: *EGraph,
    rule: Rule,
    rule_slot: u32,
    a: AlphaInstance,
    b: AlphaInstance,
    matches: *std.ArrayListUnmanaged(Match),
    dedup: *MatchDedup,
    avoid_cache: *AvoidCache,
) !void {
    const forward = try completeAlphaSubst(self, rule, a, b.atom);
    if (try self.depGateAllows(rule, forward, avoid_cache)) {
        return retainAlphaMatch(
            self,
            rule_slot,
            a.node,
            forward,
            matches,
            dedup,
        );
    }
    const reverse = try completeAlphaSubst(self, rule, b, a.atom);
    if (try self.depGateAllows(rule, reverse, avoid_cache)) {
        return retainAlphaMatch(
            self,
            rule_slot,
            b.node,
            reverse,
            matches,
            dedup,
        );
    }
    return retainAlphaMatch(
        self,
        rule_slot,
        a.node,
        forward,
        matches,
        dedup,
    );
}

fn completeAlphaSubst(
    self: *EGraph,
    rule: Rule,
    inst: AlphaInstance,
    fresh: LeafId,
) ![]?Child {
    const subst = try self.allocator.dupe(?Child, inst.subst);
    subst[rule.alpha_new_slot] = .{ .bound = fresh };
    return subst;
}

/// Same retained-match dedup as `matchRule`'s tail.
fn retainAlphaMatch(
    self: *EGraph,
    rule_slot: u32,
    node: ENodeId,
    subst: []const ?Child,
    matches: *std.ArrayListUnmanaged(Match),
    dedup: *MatchDedup,
) !void {
    const key = self.matchEffectKey(rule_slot, node, subst, &.{});
    if (dedup.applied.contains(key)) return;
    const gop = try dedup.iter.getOrPut(self.allocator, key);
    if (gop.found_existing) return;
    try matches.append(self.allocator, .{
        .rule_slot = rule_slot,
        .root_node = node,
        .subst = subst,
        .key = key,
    });
}
