//! The key of the transparent matcher's failure memo
//! (`matchSymbolicToSymbolicState`): the part of the session a comparison
//! can read or write.

const Types = @import("../types.zig");
const MatchState = @import("../match_state.zig");
const WitnessState = @import("./witness_state.zig");

const BoundValue = Types.BoundValue;
const WitnessMap = Types.WitnessMap;
const WitnessSlotMap = Types.WitnessSlotMap;
const SymbolicExpr = Types.SymbolicExpr;
const MatchSession = MatchState.MatchSession;

/// The part of `state` that matching `lhs` against `rhs` can read or write,
/// for the transparent matcher's failure memo. Dummies other expansions
/// minted and bindings no path reaches stay out, so a pair revisited after
/// unrelated siblings or expansions grew the session still hits (#587).
///
/// Reachable, over-approximated by `Types.Mentions`:
/// - the binders the pair mentions and those their bound values mention, and
///   every concrete binding: an actual reads back as the binder whose `raw`
///   it is (`symbolicForExistingConcreteBinding`);
/// - the dummy slots the pair or a reachable binding mentions; slots whose
///   witness is a placeholder and every slot of `materialized_witness_slots`,
///   since a placeholder reads back as its slot (`slotForWitness`); closed
///   under alias classes and distinct groups, which `alignDummySlots` and
///   `witnessRespectsDistinctness` read.
///
/// Slots past the end of the session are hashed as such: an expansion mints
/// the next slots, so whether a mentioned slot exists yet matters, but not
/// how many unrelated slots came before it.
pub fn hashMatchSessionReachable(
    self: anytype,
    state: *MatchSession,
    lhs: *const SymbolicExpr,
    rhs: *const SymbolicExpr,
) anyerror!u64 {
    const allocator = self.shared.allocator;
    const reach = Types.mentions(lhs).join(Types.mentions(rhs));
    var h: u64 = 0x5be0cd19137e2179;

    var binders = reach.binders;
    while (true) {
        var grown = binders;
        for (state.bindings, 0..) |binding_opt, idx| {
            const binding = binding_opt orelse continue;
            if (!bindingReachable(binding, idx, binders)) continue;
            grown |= Types.mentions(boundValueExpr(binding)).binders;
        }
        if (grown == binders) break;
        binders = grown;
    }

    const slot_count = state.symbolic_dummy_infos.items.len;
    const marks = &state.memo_key_marks;
    try marks.resize(allocator, slot_count);
    @memset(marks.items, 0);
    const roots = &state.memo_key_roots;
    try roots.resize(allocator, slot_count);
    for (roots.items, 0..) |*root, slot| {
        root.* = try WitnessState.resolveDummySlot(slot, state);
    }

    var past_end = markSlotRange(marks.items, reach);
    h = Types.mixHash(h, state.bindings.len);
    for (state.bindings, 0..) |binding_opt, idx| {
        if (binding_opt) |binding| {
            if (!bindingReachable(binding, idx, binders)) continue;
            h = Types.mixHash(Types.mixHash(h, idx), hashBoundValue(binding));
            past_end = markSlotRange(
                marks.items,
                Types.mentions(boundValueExpr(binding)),
            ) or past_end;
        } else if (Types.binderBit(idx) & binders != 0) {
            h = Types.mixHash(Types.mixHash(h, idx), 0);
        }
    }
    if (past_end) h = Types.mixHash(h, slot_count);

    for ([_]WitnessMap{ state.witnesses, state.materialized_witnesses }) |map| {
        var it = map.iterator();
        while (it.next()) |entry| {
            const node = self.shared.theorem.interner.node(entry.value_ptr.*);
            if (node.* == .placeholder and entry.key_ptr.* < slot_count) {
                marks.items[entry.key_ptr.*] |= slot_mark;
            }
        }
    }
    var slot_it = state.materialized_witness_slots.valueIterator();
    while (slot_it.next()) |slot| {
        if (slot.* < slot_count) marks.items[slot.*] |= slot_mark;
    }
    h = hashWitnessSlotMap(h, state.materialized_witness_slots);

    // Close under classes and groups; a group id is a slot index, so its
    // mark shares the slot's byte.
    var changed = true;
    while (changed) {
        changed = false;
        for (state.symbolic_dummy_infos.items, 0..) |info, slot| {
            const root = roots.items[slot];
            var in = marks.items[slot] & slot_mark != 0 or
                marks.items[root] & slot_mark != 0;
            if (info.distinct_group) |group| {
                in = in or marks.items[group] & group_mark != 0;
                if (in and marks.items[group] & group_mark == 0) {
                    marks.items[group] |= group_mark;
                    changed = true;
                }
            }
            if (!in) continue;
            for ([2]usize{ slot, root }) |s| {
                if (marks.items[s] & slot_mark == 0) {
                    marks.items[s] |= slot_mark;
                    changed = true;
                }
            }
        }
    }

    for (state.symbolic_dummy_infos.items, 0..) |info, slot| {
        if (marks.items[slot] & slot_mark == 0) continue;
        h = Types.mixHash(h, slot);
        h = Types.mixHashBytes(h, info.sort_name);
        h = Types.mixHash(h, @intFromBool(info.bound));
        h = Types.mixHash(h, info.forbidden_deps);
        h = Types.mixHash(h, if (info.distinct_group) |group| group + 1 else 0);
        h = Types.mixHash(h, if (state.dummy_aliases.get(slot)) |to| to + 1 else 0);
        h = Types.mixHash(h, if (state.witnesses.get(slot)) |w| w + 1 else 0);
        h = Types.mixHash(
            h,
            if (state.materialized_witnesses.get(slot)) |w| w + 1 else 0,
        );
    }
    return h;
}

const slot_mark: u8 = 1;
const group_mark: u8 = 2;

fn bindingReachable(binding: BoundValue, idx: usize, binders: u64) bool {
    return binding == .concrete or Types.binderBit(idx) & binders != 0;
}

fn boundValueExpr(binding: BoundValue) *const SymbolicExpr {
    return switch (binding) {
        .concrete => |concrete| concrete.repr,
        .symbolic => |symbolic| symbolic.expr,
    };
}

/// Mark the slots of `mentions` that exist; true when some do not yet.
fn markSlotRange(marks: []u8, mentions: Types.Mentions) bool {
    const hi = @min(mentions.dummy_hi, marks.len);
    var slot: usize = mentions.dummy_lo;
    while (slot < hi) : (slot += 1) marks[slot] |= slot_mark;
    return mentions.dummy_hi > marks.len;
}

fn hashBoundValue(bound: BoundValue) u64 {
    return switch (bound) {
        .concrete => |concrete| blk: {
            var h = Types.mixHash(0x6a09e667f3bcc908, 6);
            h = Types.mixHash(h, concrete.raw);
            h = Types.mixHash(h, @backingInt(concrete.mode));
            h = Types.mixHash(h, Types.symbolicHash(concrete.repr));
            break :blk h;
        },
        .symbolic => |symbolic| blk: {
            var h = Types.mixHash(0x6a09e667f3bcc908, 7);
            h = Types.mixHash(h, @backingInt(symbolic.mode));
            h = Types.mixHash(h, Types.symbolicHash(symbolic.expr));
            break :blk h;
        },
    };
}

/// Fold a map's entries into `h` order-independently (xor + wrapping sum of
/// per-entry hashes, plus the count), so the result does not depend on
/// iteration order.
fn hashIntMap(h: u64, comptime tag: u64, map: anytype) u64 {
    var count: u64 = 0;
    var xor_acc: u64 = 0;
    var sum_acc: u64 = 0;
    var it = map.iterator();
    while (it.next()) |entry| {
        const kh = Types.mixHash(0x243f6a8885a308d3, @intCast(entry.key_ptr.*));
        const eh = Types.mixHash(kh, @intCast(entry.value_ptr.*));
        count += 1;
        xor_acc ^= eh;
        sum_acc +%= eh;
    }
    var out = Types.mixHash(h, tag);
    out = Types.mixHash(out, count);
    out = Types.mixHash(out, xor_acc);
    return Types.mixHash(out, sum_acc);
}

fn hashWitnessSlotMap(h: u64, map: WitnessSlotMap) u64 {
    return hashIntMap(h, 9, map);
}
