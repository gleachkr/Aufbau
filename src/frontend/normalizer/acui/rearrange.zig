//! A proof that two expressions are equal when they differ only in how the
//! members of their ACUI bags are ordered, grouped and repeated. It moves
//! the members that are out of place, so its size follows how far they
//! move. Sorting both sides to their normal forms instead costs the square
//! of the bag's size, however close the two orders already are.
const std = @import("std");
const ExprId = @import("../../expr.zig").ExprId;
const ExprNode = @import("../../expr.zig").ExprNode;
const ResolvedRelation = @import("../../rewrite_registry.zig").ResolvedRelation;
const ResolvedStructuralCombiner =
    @import("../../rewrite_registry.zig").ResolvedStructuralCombiner;
const AcuiBag = @import("../../acui_bag.zig");
const AcuiSupport = @import("../../acui_support.zig");
const ProofEmit = @import("../proof_emit.zig");
const Support = @import("../support.zig");
const NormalizeResult = @import("../types.zig").NormalizeResult;

/// A proof of `lhs` = `rhs`, or null when they differ by more than a
/// rearrangement (`AcuiSupport.Context.isRearrangement`): as written, with
/// the defs standing in their bags opened, or with the members of their
/// bags then normalized one by one. The inner null is a proof of an
/// expression equal to itself.
pub fn buildRearrangement(
    self: anytype,
    lhs: ExprId,
    rhs: ExprId,
) anyerror!??usize {
    const support = try self.support();
    var proved: Proved = .empty;
    defer proved.deinit(self.allocator);
    if (try support.isRearrangement(lhs, rhs)) return try rearrange(self, &proved, lhs, rhs);

    // A def standing for a bag, or for a member of one, may hide members
    // the other side lists: `tree_b` against `g ; φ`. Opened on both
    // sides, the two may again differ only by a rearrangement, proved
    // between the unfoldings the verifier checks.
    var opened: Opened = .empty;
    defer opened.deinit(self.allocator);
    const lhs_open = try openDefs(self, &opened, lhs, false);
    const rhs_open = try openDefs(self, &opened, rhs, false);
    const relation = Support.relationFor(self, lhs) orelse return null;
    if ((lhs_open != lhs or rhs_open != rhs) and
        try support.isRearrangement(lhs_open, rhs_open))
    {
        return try chain(
            self,
            relation,
            .{ lhs, lhs_open, rhs_open, rhs },
            .{
                try ProofEmit.emitTransparentRelationProof(self, relation, lhs, lhs_open),
                try rearrange(self, &proved, lhs_open, rhs_open),
                try ProofEmit.emitTransparentRelationProof(self, relation, rhs_open, rhs),
            },
        );
    }

    // A member may still need rewriting: `Γ ; {x/t} φ` against `Γ ; φ[t]`.
    // Sorting both sides would rewrite it, but costs the square of the
    // bag's size; normalizing each member where it stands, the two may
    // again differ only by a rearrangement.
    var normalized: Normalized = .empty;
    defer normalized.deinit(self.allocator);
    const lhs_norm = try normalizeMembers(self, &normalized, lhs_open) orelse return null;
    const rhs_norm = try normalizeMembers(self, &normalized, rhs_open) orelse return null;
    if (lhs_norm.result_expr == lhs_open and rhs_norm.result_expr == rhs_open) return null;
    if (!try support.isRearrangement(lhs_norm.result_expr, rhs_norm.result_expr)) return null;
    const lhs_to_norm = try ProofEmit.composeTransitivity(
        self,
        relation,
        lhs,
        lhs_open,
        lhs_norm.result_expr,
        try ProofEmit.emitTransparentRelationProof(self, relation, lhs, lhs_open),
        lhs_norm.conv_line_idx,
    );
    const rhs_to_norm = try ProofEmit.composeTransitivity(
        self,
        relation,
        rhs,
        rhs_open,
        rhs_norm.result_expr,
        try ProofEmit.emitTransparentRelationProof(self, relation, rhs, rhs_open),
        rhs_norm.conv_line_idx,
    );
    return try chain(
        self,
        relation,
        .{ lhs, lhs_norm.result_expr, rhs_norm.result_expr, rhs },
        .{
            lhs_to_norm,
            try rearrange(self, &proved, lhs_norm.result_expr, rhs_norm.result_expr),
            if (rhs_to_norm) |proof|
                try ProofEmit.emitSymm(self, relation, rhs, rhs_norm.result_expr, proof)
            else
                null,
        },
    );
}

/// A proof of `exprs[0]` to `exprs[3]` from `steps`, a proof of each
/// expression to the next; a null step is an expression equal to the next.
fn chain(
    self: anytype,
    relation: ResolvedRelation,
    exprs: [4]ExprId,
    steps: [3]?usize,
) anyerror!?usize {
    const first_two = try ProofEmit.composeTransitivity(
        self,
        relation,
        exprs[0],
        exprs[1],
        exprs[2],
        steps[0],
        steps[1],
    );
    return try ProofEmit.composeTransitivity(
        self,
        relation,
        exprs[0],
        exprs[2],
        exprs[3],
        first_two,
        steps[2],
    );
}

/// `normalizeMembers` results, by expression.
const Normalized = std.AutoHashMapUnmanaged(ExprId, ?NormalizeResult);

/// `expr_id` normalized but for the order of its commutative bags: each
/// member is normalized where it stands, and so is each subterm holding
/// no bag. Null when `expr_id` holds no commutative bag at all.
fn normalizeMembers(
    self: anytype,
    normalized: *Normalized,
    expr_id: ExprId,
) anyerror!?NormalizeResult {
    if (normalized.get(expr_id)) |hit| return hit;
    const result = try normalizeMembersUncached(self, normalized, expr_id);
    try normalized.put(self.allocator, expr_id, result);
    return result;
}

fn normalizeMembersUncached(
    self: anytype,
    normalized: *Normalized,
    expr_id: ExprId,
) anyerror!?NormalizeResult {
    const app = appOf(self, expr_id) orelse return null;
    const members = try self.allocator.alloc(?NormalizeResult, app.args.len);
    defer self.allocator.free(members);
    var holds_bag = try isCommutativeBag(self, expr_id);
    for (app.args, members) |arg, *member| {
        member.* = try normalizeMembers(self, normalized, arg);
        holds_bag = holds_bag or member.* != null;
    }
    // Normalized whole by the caller, so a conversion with no bag in it
    // normalizes nothing here.
    if (!holds_bag) return null;
    const args = try self.allocator.alloc(ExprId, app.args.len);
    defer self.allocator.free(args);
    const proofs = try self.allocator.alloc(?usize, app.args.len);
    defer self.allocator.free(proofs);
    for (app.args, members, args, proofs) |arg, member, *out, *proof| {
        const result = member orelse try self.normalize(arg);
        out.* = result.result_expr;
        proof.* = result.conv_line_idx;
    }
    if (std.mem.eql(ExprId, app.args, args)) {
        return .{ .result_expr = expr_id, .conv_line_idx = null };
    }
    return .{
        .result_expr = try self.theorem.interner.internApp(app.term_id, args),
        .conv_line_idx = try ProofEmit.emitCongruenceLine(
            self,
            app.term_id,
            app.args,
            args,
            proofs,
        ),
    };
}

/// `openDefs` results, by expression and whether it stands in a bag.
const Opened = std.AutoHashMapUnmanaged(struct { ExprId, bool }, ExprId);

/// `expr_id` with each def that stands in a commutative bag unfolded: a
/// member of one, or a def whose body is one. `in_bag` says `expr_id` is
/// a member.
fn openDefs(
    self: anytype,
    opened: *Opened,
    expr_id: ExprId,
    in_bag: bool,
) anyerror!ExprId {
    if (opened.get(.{ expr_id, in_bag })) |hit| return hit;
    const result = try openDefsUncached(self, opened, expr_id, in_bag);
    try opened.put(self.allocator, .{ expr_id, in_bag }, result);
    return result;
}

fn openDefsUncached(
    self: anytype,
    opened: *Opened,
    expr_id: ExprId,
    in_bag: bool,
) anyerror!ExprId {
    const app = appOf(self, expr_id) orelse return expr_id;
    if (try isCommutativeBag(self, expr_id)) {
        const parts = [_]ExprId{
            try openDefs(self, opened, app.args[0], true),
            try openDefs(self, opened, app.args[1], true),
        };
        if (parts[0] == app.args[0] and parts[1] == app.args[1]) return expr_id;
        return try self.theorem.interner.internApp(app.term_id, &parts);
    }
    if (self.env.openableDef(app.term_id) != null) {
        if (try (try self.defOps()).unfoldConcreteDef(expr_id)) |body| {
            if (in_bag or try isCommutativeBag(self, body)) {
                return try openDefs(self, opened, body, true);
            }
        }
    }
    const args = try self.allocator.alloc(ExprId, app.args.len);
    defer self.allocator.free(args);
    var changed = false;
    for (app.args, args) |arg, *out| {
        out.* = try openDefs(self, opened, arg, false);
        changed = changed or out.* != arg;
    }
    if (!changed) return expr_id;
    return try self.theorem.interner.internApp(app.term_id, args);
}

fn isCommutativeBag(self: anytype, expr_id: ExprId) anyerror!bool {
    const app = appOf(self, expr_id) orelse return false;
    if (app.args.len != 2) return false;
    const bag = try self.registry.resolveStructuralCombiner(self.env, app.term_id) orelse
        return false;
    return bag.comm_id != null;
}

/// The pairs of subterms already proved equal, with their proofs: the two
/// sides share subterms, and a shared pair is proved once however many
/// paths reach it.
const Proved = std.AutoHashMapUnmanaged([2]ExprId, ?usize);

/// `lhs` = `rhs`, which differ only by a rearrangement.
fn rearrange(
    self: anytype,
    proved: *Proved,
    lhs: ExprId,
    rhs: ExprId,
) anyerror!?usize {
    if (lhs == rhs) return null;
    if (proved.get(.{ lhs, rhs })) |proof| return proof;
    const proof = try rearrangeApp(self, proved, lhs, rhs);
    try proved.put(self.allocator, .{ lhs, rhs }, proof);
    return proof;
}

fn rearrangeApp(
    self: anytype,
    proved: *Proved,
    lhs: ExprId,
    rhs: ExprId,
) anyerror!?usize {
    const lhs_app = appOf(self, lhs).?;
    const rhs_app = appOf(self, rhs).?;
    if (lhs_app.args.len == 2) {
        if (try self.registry.resolveStructuralCombiner(
            self.env,
            lhs_app.term_id,
        )) |acui| {
            var mover: Mover(@TypeOf(self)) = .{
                .engine = self,
                .support = try self.support(),
                .acui = acui,
                .relation = Support.relationFor(self, lhs) orelse
                    return error.MissingStructuralMetadata,
            };
            return try mover.permute(lhs, rhs);
        }
    }
    const proofs = try self.allocator.alloc(?usize, lhs_app.args.len);
    defer self.allocator.free(proofs);
    for (lhs_app.args, rhs_app.args, proofs) |lhs_arg, rhs_arg, *proof| {
        proof.* = try rearrange(self, proved, lhs_arg, rhs_arg);
    }
    return try ProofEmit.emitCongruenceLine(
        self,
        lhs_app.term_id,
        lhs_app.args,
        rhs_app.args,
        proofs,
    );
}

fn appOf(self: anytype, expr_id: ExprId) ?ExprNode.App {
    return switch (self.theorem.interner.node(expr_id).*) {
        .app => |app| app,
        .variable, .placeholder => null,
    };
}

/// The moves of one bag's combiner, between two bags holding the same
/// members.
fn Mover(comptime Engine: type) type {
    return struct {
        const Self = @This();

        engine: Engine,
        support: *AcuiSupport.Context,
        acui: ResolvedStructuralCombiner,
        relation: ResolvedRelation,

        /// Without idempotence a member's repeats count, and are moved
        /// one at a time; with it, a member's repeats merge into one.
        fn merges(self: *const Self) bool {
            return self.acui.idem_id != null;
        }

        fn sameMembers(self: *Self, lhs: ExprId, rhs: ExprId) anyerror!bool {
            return try self.support.sameMembers(lhs, rhs, self.acui);
        }

        fn contains(self: *const Self, bag: ExprId, member: ExprId) bool {
            return self.spine().holds(self.engine.theorem, bag, member);
        }

        fn split(self: *const Self, expr_id: ExprId) ?[2]ExprId {
            return self.spine().split(self.engine.theorem, expr_id);
        }

        fn spine(self: *const Self) AcuiBag.Spine {
            return .raw(self.acui.head_term_id);
        }

        fn join(self: *Self, lhs: ExprId, rhs: ExprId) anyerror!ExprId {
            return try self.engine.theorem.interner.internApp(
                self.acui.head_term_id,
                &.{ lhs, rhs },
            );
        }

        fn compose(
            self: *Self,
            original: ExprId,
            mid: ExprId,
            final: ExprId,
            first: ?usize,
            second: ?usize,
        ) anyerror!?usize {
            return try ProofEmit.composeTransitivity(
                self.engine,
                self.relation,
                original,
                mid,
                final,
                first,
                second,
            );
        }

        /// `old_lhs ; old_rhs` = `new_lhs ; new_rhs` from proofs of its
        /// two sides.
        fn congruence(
            self: *Self,
            old: [2]ExprId,
            new: [2]ExprId,
            proofs: [2]?usize,
        ) anyerror!?usize {
            return try ProofEmit.emitCongruenceLine(
                self.engine,
                self.acui.head_term_id,
                &old,
                &new,
                &proofs,
            );
        }

        /// `lhs` = `rhs`, two bags holding the same members. A side whose
        /// two parts already hold the parts of the other is matched part
        /// for part; otherwise `rhs` is regrouped to end in a single member
        /// (and `lhs` too when that member lies deep in its right spine),
        /// and the last member of `rhs` is moved to the end of `lhs`, or
        /// the last member of `lhs` into its place in `rhs`, whichever is
        /// out of place, and the rest matched.
        fn permute(self: *Self, lhs: ExprId, rhs: ExprId) anyerror!?usize {
            if (lhs == rhs) return null;
            const rhs_parts = self.split(rhs) orelse {
                return try self.contract(lhs, rhs);
            };
            if (self.split(lhs)) |lhs_parts| {
                if (try self.sameMembers(lhs_parts[0], rhs_parts[0]) and
                    try self.sameMembers(lhs_parts[1], rhs_parts[1]))
                {
                    return try self.congruence(lhs_parts, rhs_parts, .{
                        try self.permute(lhs_parts[0], rhs_parts[0]),
                        try self.permute(lhs_parts[1], rhs_parts[1]),
                    });
                }
            }
            const front = rhs_parts[0];
            if (self.split(rhs_parts[1])) |back| {
                // `front ; (b ; c)` read as `(front ; b) ; c`, so that its
                // last part is a single member.
                const regrouped = try self.join(
                    try self.join(front, back[0]),
                    back[1],
                );
                return try self.compose(
                    lhs,
                    regrouped,
                    rhs,
                    try self.permute(lhs, regrouped),
                    try ProofEmit.emitAssoc(
                        self.engine,
                        front,
                        back[0],
                        back[1],
                        self.relation,
                        self.acui,
                    ),
                );
            }
            const last = rhs_parts[1];
            if (self.merges() and self.contains(front, last)) {
                // `front ; last` = `front`, which already holds `last`.
                const absorbed = try self.absorb(front, last);
                return try self.compose(
                    lhs,
                    front,
                    rhs,
                    try self.permute(lhs, front),
                    try ProofEmit.emitSymm(
                        self.engine,
                        self.relation,
                        rhs,
                        front,
                        absorbed,
                    ),
                );
            }
            if (self.split(lhs)) |lhs_parts| regroup: {
                const back = self.split(lhs_parts[1]) orelse break :regroup;
                if (self.contains(back[1], last)) {
                    // `a ; (b ; c)` read as `(a ; b) ; c`, as `rhs` is
                    // above, when `last` is to come out of `c`: dug out
                    // from under the right spine instead, every member
                    // moved would cost the depth of that spine.
                    const regrouped = try self.join(
                        try self.join(lhs_parts[0], back[0]),
                        back[1],
                    );
                    return try self.compose(
                        lhs,
                        regrouped,
                        rhs,
                        try ProofEmit.emitAssocSymm(
                            self.engine,
                            lhs_parts[0],
                            back[0],
                            back[1],
                            self.relation,
                            self.acui,
                        ),
                        try self.permute(regrouped, rhs),
                    );
                }
            }
            if (try self.lastOutOfPlace(lhs, rhs)) |lhs_parts| {
                // `front ; a` = `rest ; a` = `rhs`, moving `a` into its place
                // in `rhs` rather than every member after that place out.
                const placed = try self.extract(rhs, lhs_parts[1]);
                const moved = try self.join(placed.rest, lhs_parts[1]);
                return try self.compose(
                    lhs,
                    moved,
                    rhs,
                    try self.congruence(lhs_parts, .{ placed.rest, lhs_parts[1] }, .{
                        try self.permute(lhs_parts[0], placed.rest),
                        null,
                    }),
                    try ProofEmit.emitSymm(
                        self.engine,
                        self.relation,
                        rhs,
                        moved,
                        placed.proof.?,
                    ),
                );
            }
            const extracted = try self.extract(lhs, last);
            const moved = try self.join(extracted.rest, last);
            return try self.compose(
                lhs,
                moved,
                rhs,
                extracted.proof,
                try self.congruence(.{ extracted.rest, last }, rhs_parts, .{
                    try self.permute(extracted.rest, front),
                    null,
                }),
            );
        }

        /// The parts of `lhs` when its last member, rather than the last
        /// member of `rhs`, is the one to move: when taking it out of both
        /// sides leaves them ending alike for longer than taking out the
        /// last member of `rhs` does. Null when `rhs`'s last member should
        /// move, when `lhs` does not end in a single member, or when its
        /// front holds that member too and repeats merge.
        fn lastOutOfPlace(self: *Self, lhs: ExprId, rhs: ExprId) anyerror!?[2]ExprId {
            const lhs_parts = self.split(lhs) orelse return null;
            if (self.split(lhs_parts[1]) != null) return null;
            if (self.merges() and self.contains(lhs_parts[0], lhs_parts[1])) return null;
            const allocator = self.engine.allocator;
            var lhs_members: std.ArrayListUnmanaged(ExprId) = .empty;
            defer lhs_members.deinit(allocator);
            var rhs_members: std.ArrayListUnmanaged(ExprId) = .empty;
            defer rhs_members.deinit(allocator);
            try self.spine().collect(allocator, self.engine.theorem, lhs, &lhs_members);
            try self.spine().collect(allocator, self.engine.theorem, rhs, &rhs_members);
            const lhs_items = lhs_members.items;
            const rhs_items = rhs_members.items;
            const lhs_last = lhs_items.len - 1;
            const rhs_last = rhs_items.len - 1;
            const lhs_moves = endingAlike(
                lhs_items,
                lhs_last,
                rhs_items,
                lastIndexOf(rhs_items, lhs_items[lhs_last]),
            );
            const rhs_moves = endingAlike(
                lhs_items,
                lastIndexOf(lhs_items, rhs_items[rhs_last]),
                rhs_items,
                rhs_last,
            );
            return if (lhs_moves > rhs_moves) lhs_parts else null;
        }

        fn lastIndexOf(items: []const ExprId, member: ExprId) usize {
            var idx = items.len;
            while (idx > 0) {
                idx -= 1;
                if (items[idx] == member) return idx;
            }
            unreachable;
        }

        /// How many members `lhs` and `rhs` end with alike, each without
        /// the member at its `skip` index.
        fn endingAlike(lhs: []const ExprId, lhs_skip: usize, rhs: []const ExprId, rhs_skip: usize) usize {
            var lhs_idx = lhs.len;
            var rhs_idx = rhs.len;
            var count: usize = 0;
            while (true) {
                if (lhs_idx > 0 and lhs_idx - 1 == lhs_skip) lhs_idx -= 1;
                if (rhs_idx > 0 and rhs_idx - 1 == rhs_skip) rhs_idx -= 1;
                if (lhs_idx == 0 or rhs_idx == 0) return count;
                lhs_idx -= 1;
                rhs_idx -= 1;
                if (lhs[lhs_idx] != rhs[rhs_idx]) return count;
                count += 1;
            }
        }

        /// `bag` = `member`, a bag whose members are all `member`.
        fn contract(self: *Self, bag: ExprId, member: ExprId) anyerror!?usize {
            if (bag == member) return null;
            const parts = self.split(bag) orelse
                return error.MissingStructuralMetadata;
            const doubled = try self.join(member, member);
            return try self.compose(
                bag,
                doubled,
                member,
                try self.congruence(parts, .{ member, member }, .{
                    try self.contract(parts[0], member),
                    try self.contract(parts[1], member),
                }),
                try ProofEmit.emitIdem(
                    self.engine,
                    member,
                    self.relation,
                    self.acui,
                ),
            );
        }

        /// `bag ; member` = `bag`, for a `bag` that holds `member`.
        fn absorb(self: *Self, bag: ExprId, member: ExprId) anyerror!usize {
            if (bag == member) {
                return try ProofEmit.emitIdem(
                    self.engine,
                    member,
                    self.relation,
                    self.acui,
                );
            }
            const taken = try self.extractOne(bag, member);
            const merged = try self.mergeTaken(bag, member, taken);
            const proof = taken.proof orelse return merged;
            const rest = try self.join(taken.rest, member);
            return (try self.compose(
                try self.join(bag, member),
                rest,
                bag,
                merged,
                try ProofEmit.emitSymm(self.engine, self.relation, bag, rest, proof),
            )).?;
        }

        const Extracted = struct {
            /// `bag` without the member.
            rest: ExprId,
            /// `bag` = `rest ; member`.
            proof: ?usize,
        };

        /// `bag` = `rest ; member`, with `rest` holding no `member`: every
        /// repeat goes when they merge, one occurrence when they do not.
        fn extract(self: *Self, bag: ExprId, member: ExprId) anyerror!Extracted {
            var result = try self.extractOne(bag, member);
            if (!self.merges()) return result;
            while (self.contains(result.rest, member)) {
                const taken = try self.extractOne(result.rest, member);
                const proof = try self.compose(
                    bag,
                    try self.join(result.rest, member),
                    try self.join(taken.rest, member),
                    result.proof,
                    try self.mergeTaken(result.rest, member, taken),
                );
                result = .{ .rest = taken.rest, .proof = proof };
            }
            return result;
        }

        /// `bag ; member` = `rest ; member`, given `taken`, a proof that
        /// `bag` = `rest ; member`: the member taken out merges with the
        /// one after it.
        fn mergeTaken(
            self: *Self,
            bag: ExprId,
            member: ExprId,
            taken: Extracted,
        ) anyerror!usize {
            const appended = try self.join(bag, member);
            const reappended = try self.join(taken.rest, member);
            const doubled = try self.join(member, member);
            const grouped = try self.join(taken.rest, doubled);
            const to_grouped = try self.compose(
                appended,
                try self.join(reappended, member),
                grouped,
                try self.congruence(
                    .{ bag, member },
                    .{ reappended, member },
                    .{ taken.proof, null },
                ),
                try ProofEmit.emitAssoc(
                    self.engine,
                    taken.rest,
                    member,
                    member,
                    self.relation,
                    self.acui,
                ),
            );
            return (try self.compose(
                appended,
                grouped,
                reappended,
                to_grouped,
                try self.congruence(.{ taken.rest, doubled }, .{
                    taken.rest,
                    member,
                }, .{ null, try ProofEmit.emitIdem(
                    self.engine,
                    member,
                    self.relation,
                    self.acui,
                ) }),
            )).?;
        }

        /// `bag` = `rest ; member`, taking out one occurrence of `member`
        /// from `bag`, which holds it and something else: from the back
        /// part when that holds it, else through `lead`.
        fn extractOne(self: *Self, bag: ExprId, member: ExprId) anyerror!Extracted {
            const parts = self.split(bag) orelse
                return error.MissingStructuralMetadata;
            const front = parts[0];
            const back = parts[1];
            if (back == member) return .{ .rest = front, .proof = null };
            if (self.split(back) != null and self.contains(back, member)) {
                // `front ; back` = `front ; (inner ; m)` = `(front ; inner) ; m`
                const inner = try self.extractOne(back, member);
                const rest = try self.join(front, inner.rest);
                const grouped = try self.join(front, try self.join(inner.rest, member));
                return .{ .rest = rest, .proof = try self.compose(
                    bag,
                    grouped,
                    try self.join(rest, member),
                    try self.congruence(
                        parts,
                        .{ front, try self.join(inner.rest, member) },
                        .{ null, inner.proof },
                    ),
                    try ProofEmit.emitAssocSymm(
                        self.engine,
                        front,
                        inner.rest,
                        member,
                        self.relation,
                        self.acui,
                    ),
                ) };
            }
            // `m ; rest` = `rest ; m`
            const led = try self.lead(bag, member);
            const leading = try self.join(member, led.rest);
            return .{ .rest = led.rest, .proof = try self.compose(
                bag,
                leading,
                try self.join(led.rest, member),
                led.proof,
                try ProofEmit.emitComm(
                    self.engine,
                    member,
                    led.rest,
                    self.relation,
                    self.acui,
                ),
            ) };
        }

        /// `bag` = `member ; rest`, taking out one occurrence of `member`
        /// from `bag`, which holds it and something else. Carried at the
        /// front, the member rises a level with one regrouping, where
        /// carried at the back it needs two and a swap.
        fn lead(self: *Self, bag: ExprId, member: ExprId) anyerror!Extracted {
            const parts = self.split(bag) orelse
                return error.MissingStructuralMetadata;
            const front = parts[0];
            const back = parts[1];
            if (front == member) return .{ .rest = back, .proof = null };
            if (back == member) {
                return .{ .rest = front, .proof = try ProofEmit.emitComm(
                    self.engine,
                    front,
                    member,
                    self.relation,
                    self.acui,
                ) };
            }
            if (!self.contains(front, member)) {
                // `front ; (inner ; m)` = `(front ; inner) ; m` = `m ; (front ; inner)`
                const taken = try self.extractOne(bag, member);
                return .{ .rest = taken.rest, .proof = try self.compose(
                    bag,
                    try self.join(taken.rest, member),
                    try self.join(member, taken.rest),
                    taken.proof,
                    try ProofEmit.emitComm(
                        self.engine,
                        taken.rest,
                        member,
                        self.relation,
                        self.acui,
                    ),
                ) };
            }
            // `(m ; inner) ; back` = `m ; (inner ; back)`
            const inner = try self.lead(front, member);
            const pulled = try self.join(member, inner.rest);
            const rest = try self.join(inner.rest, back);
            return .{ .rest = rest, .proof = try self.compose(
                bag,
                try self.join(pulled, back),
                try self.join(member, rest),
                try self.congruence(parts, .{ pulled, back }, .{ inner.proof, null }),
                try ProofEmit.emitAssoc(
                    self.engine,
                    member,
                    inner.rest,
                    back,
                    self.relation,
                    self.acui,
                ),
            ) };
        }
    };
}
