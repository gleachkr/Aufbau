const std = @import("std");
const ArenaAllocator = @import("../arena_allocator.zig").ArenaAllocator;
const ExprId = @import("../expr.zig").ExprId;
const TheoremContext = @import("../expr.zig").TheoremContext;
const GlobalEnv = @import("../env.zig").GlobalEnv;
const RuleDecl = @import("../env.zig").RuleDecl;
const MmbWriter = @import("./mmb_writer.zig");
const TermRecord = MmbWriter.TermRecord;
const DefOps = @import("../def_ops.zig");
const ArgInfo = @import("../parse_recovery.zig").ArgInfo;
const binderDepsToBoundArgDeps =
    @import("../parse_recovery.zig").binderDepsToBoundArgDeps;
const MM0Parser = @import("../parse_recovery.zig").MM0Parser;
const TermStmt = @import("../parse_recovery.zig").TermStmt;
const ProofCmd = @import("../../trusted/proof.zig").ProofCmd;
const UnifyCmd = @import("../../trusted/proof.zig").UnifyCmd;
const Arg = @import("../../trusted/args.zig").Arg;
const CheckedIr = @import("../checked_ir.zig");
const CheckedLine = CheckedIr.CheckedLine;
const CheckedRef = CheckedIr.CheckedRef;

const ExprSlotMap = std.AutoHashMapUnmanaged(ExprId, u32);

/// The heap MMB verifiers typically give a proof by default: ours, and
/// mm0-c's unless it is rebuilt with a larger `HEAP_SIZE`.
pub const default_verifier_heap_len = @import("../../trusted/constants.zig").HEAP_SIZE;

/// A written proof stream and the heap entries replaying it takes.
pub const ProofBody = struct {
    bytes: []const u8,
    heap_len: u32,
};

/// A proof or unify stream recorded command by command, its saves settled
/// only once the whole stream is known. Emission saves every line and every
/// term so that a later use can refer to it; `toBytes` then writes a save
/// that nothing reads back unsaved (`Term`, `Thm`, `UTerm`) or drops it (a
/// bare `Save`), and moves the heap slots after it down, so the verifier's
/// heap holds only what the stream reads back.
fn Stream(comptime Op: type) type {
    return struct {
        const Self = @This();
        const Cmd = struct { op: Op, data: u32 };

        cmds: std.ArrayListUnmanaged(Cmd) = .empty,
        /// The heap slots (the variables) that precede the stream's own.
        fixed_slots: u32,
        /// The heap slots taken so far, as emitted.
        heap_len: u32,

        fn init(fixed_slots: u32) Self {
            return .{ .fixed_slots = fixed_slots, .heap_len = fixed_slots };
        }

        fn deinit(self: *Self, allocator: std.mem.Allocator) void {
            self.cmds.deinit(allocator);
        }

        /// Appends a command that takes no heap slot.
        fn append(self: *Self, allocator: std.mem.Allocator, op: Op, data: u32) !void {
            std.debug.assert(slotUse(op) == .none or slotUse(op) == .read);
            try self.cmds.append(allocator, .{ .op = op, .data = data });
        }

        /// Appends a command that takes a heap slot, and returns the slot.
        fn appendSlot(self: *Self, allocator: std.mem.Allocator, op: Op, data: u32) !u32 {
            std.debug.assert(slotUse(op) == .kept or slotUse(op) == .save);
            const slot = self.heap_len;
            self.heap_len = try std.math.add(u32, self.heap_len, 1);
            try self.cmds.append(allocator, .{ .op = op, .data = data });
            return slot;
        }

        fn toBytes(self: *const Self, allocator: std.mem.Allocator) !ProofBody {
            var read = try std.DynamicBitSetUnmanaged.initEmpty(allocator, self.heap_len);
            defer read.deinit(allocator);
            for (self.cmds.items) |cmd| {
                if (slotUse(cmd.op) == .read) read.set(cmd.data);
            }
            // Slots are allocated in stream order, so walking the stream again
            // meets each slot-taking command at its emitted slot `old`.
            const moved = try allocator.alloc(u32, self.heap_len);
            defer allocator.free(moved);
            for (moved[0..self.fixed_slots], 0..) |*slot, idx| slot.* = @intCast(idx);
            var old = self.fixed_slots;
            var new = self.fixed_slots;
            var bytes: std.ArrayListUnmanaged(u8) = .empty;
            errdefer bytes.deinit(allocator);
            for (self.cmds.items) |cmd| switch (slotUse(cmd.op)) {
                .read => try MmbWriter.appendCmd(&bytes, allocator, cmd.op, moved[cmd.data]),
                .kept, .save => {
                    if (slotUse(cmd.op) == .kept or read.isSet(old)) {
                        moved[old] = new;
                        new += 1;
                        try MmbWriter.appendCmd(&bytes, allocator, cmd.op, cmd.data);
                    } else if (unsaved(cmd.op)) |op| {
                        try MmbWriter.appendCmd(&bytes, allocator, op, cmd.data);
                    }
                    old += 1;
                },
                .none => try MmbWriter.appendCmd(&bytes, allocator, cmd.op, cmd.data),
            };
            std.debug.assert(old == self.heap_len);
            return .{ .bytes = try bytes.toOwnedSlice(allocator), .heap_len = new };
        }

        const SlotUse = enum {
            none,
            /// Reads back the slot in its data.
            read,
            /// Always takes a slot.
            kept,
            /// Takes a slot only when something reads it back.
            save,
        };

        fn slotUse(op: Op) SlotUse {
            return switch (Op) {
                ProofCmd => switch (op) {
                    .Ref => .read,
                    .Dummy, .Hyp => .kept,
                    .TermSave, .ThmSave, .Save => .save,
                    else => .none,
                },
                UnifyCmd => switch (op) {
                    .URef => .read,
                    .UDummy => .kept,
                    .UTermSave => .save,
                    else => .none,
                },
                else => @compileError("not a stream opcode"),
            };
        }

        /// A save's unsaved form; a bare `Save` has none and is dropped.
        fn unsaved(op: Op) ?Op {
            return switch (Op) {
                ProofCmd => switch (op) {
                    .TermSave => .Term,
                    .ThmSave => .Thm,
                    else => null,
                },
                UnifyCmd => switch (op) {
                    .UTermSave => .UTerm,
                    else => null,
                },
                else => @compileError("not a stream opcode"),
            };
        }
    };
}

const ProofStream = Stream(ProofCmd);
const UnifyStream = Stream(UnifyCmd);

/// Emits a unify stream. It is pre-order: a term is matched, and saved,
/// before its arguments.
const UnifyEmitter = struct {
    allocator: std.mem.Allocator,
    theorem: *const TheoremContext,
    stream: UnifyStream,
    slots: ExprSlotMap = .empty,

    fn init(
        allocator: std.mem.Allocator,
        theorem: *const TheoremContext,
    ) !UnifyEmitter {
        var emitter = UnifyEmitter{
            .allocator = allocator,
            .theorem = theorem,
            .stream = .init(@intCast(theorem.theorem_vars.items.len)),
        };
        errdefer emitter.deinit();
        for (theorem.theorem_vars.items, 0..) |expr_id, idx| {
            try emitter.slots.put(allocator, expr_id, @intCast(idx));
        }
        return emitter;
    }

    fn deinit(self: *UnifyEmitter) void {
        self.stream.deinit(self.allocator);
        self.slots.deinit(self.allocator);
    }

    fn emitExpr(self: *UnifyEmitter, expr_id: ExprId) !void {
        if (self.slots.get(expr_id)) |slot| {
            return self.stream.append(self.allocator, .URef, slot);
        }

        switch (self.theorem.interner.node(expr_id).*) {
            .variable => |var_id| switch (var_id) {
                .theorem_var => return error.UnboundExprVariable,
                .dummy_var => |dummy_id| {
                    const info = try self.theorem.requireDummyInfo(dummy_id);
                    const slot = try self.stream.appendSlot(self.allocator, .UDummy, info.sort_id);
                    try self.slots.put(self.allocator, expr_id, slot);
                },
            },
            .placeholder => |id| return CheckedIr.leakageError(self.theorem, id),
            .app => |app| {
                const slot = try self.stream.appendSlot(self.allocator, .UTermSave, app.term_id);
                try self.slots.put(self.allocator, expr_id, slot);
                for (app.args) |arg| {
                    try self.emitExpr(arg);
                }
            },
        }
    }

    /// An assertion's conclusion, then its hypotheses. `UHyp` pushes the
    /// next hypothesis target onto the unify stack before replay continues,
    /// so to replay them in source order the stream stores them in reverse.
    fn emitAssertion(self: *UnifyEmitter, concl: ExprId, hyps: []const ExprId) !void {
        try self.emitExpr(concl);
        var hyp_idx = hyps.len;
        while (hyp_idx > 0) {
            hyp_idx -= 1;
            try self.stream.append(self.allocator, .UHyp, 0);
            try self.emitExpr(hyps[hyp_idx]);
        }
    }

    /// Ends the stream and writes it out, its unread saves settled.
    fn finish(self: *UnifyEmitter) ![]const u8 {
        try self.stream.append(self.allocator, .End, 0);
        const body = try self.stream.toBytes(self.allocator);
        return body.bytes;
    }
};

/// Emits a proof stream: a theorem's from its checked lines, or a def's or
/// axiom's, which have no lines, from its expressions alone.
const ProofEmitter = struct {
    allocator: std.mem.Allocator,
    theorem: *const TheoremContext,
    /// Only a theorem's transport lines read it, for their conversions.
    env: ?*const GlobalEnv,
    lines: []const CheckedLine,
    stream: ProofStream,
    expr_slots: ExprSlotMap = .empty,
    hyp_slots: []u32,
    /// Each emitted line's slot.
    line_slots: []?u32,

    fn init(
        allocator: std.mem.Allocator,
        theorem: *const TheoremContext,
        env: ?*const GlobalEnv,
        lines: []const CheckedLine,
    ) !ProofEmitter {
        const hyp_slots = try allocator.alloc(u32, theorem.theorem_hyps.items.len);
        errdefer allocator.free(hyp_slots);
        const line_slots = try allocator.alloc(?u32, lines.len);
        errdefer allocator.free(line_slots);
        @memset(line_slots, null);
        var emitter = ProofEmitter{
            .allocator = allocator,
            .theorem = theorem,
            .env = env,
            .lines = lines,
            .stream = .init(@intCast(theorem.theorem_vars.items.len)),
            .hyp_slots = hyp_slots,
            .line_slots = line_slots,
        };
        errdefer emitter.expr_slots.deinit(allocator);
        for (theorem.theorem_vars.items, 0..) |expr_id, idx| {
            try emitter.expr_slots.put(allocator, expr_id, @intCast(idx));
        }
        return emitter;
    }

    fn deinit(self: *ProofEmitter) void {
        self.stream.deinit(self.allocator);
        self.expr_slots.deinit(self.allocator);
        self.allocator.free(self.hyp_slots);
        self.allocator.free(self.line_slots);
    }

    /// Post-order: an expression's arguments are built, and saved, before it.
    fn emitExpr(self: *ProofEmitter, expr_id: ExprId) !void {
        if (self.expr_slots.get(expr_id)) |slot| {
            return self.stream.append(self.allocator, .Ref, slot);
        }

        const slot = switch (self.theorem.interner.node(expr_id).*) {
            .variable => |var_id| switch (var_id) {
                .theorem_var => return error.UnboundExprVariable,
                .dummy_var => |dummy_id| blk: {
                    const info = try self.theorem.requireDummyInfo(dummy_id);
                    break :blk try self.stream.appendSlot(self.allocator, .Dummy, info.sort_id);
                },
            },
            .placeholder => |id| return CheckedIr.leakageError(self.theorem, id),
            .app => |app| blk: {
                for (app.args) |arg| {
                    try self.emitExpr(arg);
                }
                break :blk try self.stream.appendSlot(self.allocator, .TermSave, app.term_id);
            },
        };
        try self.expr_slots.put(self.allocator, expr_id, slot);
    }

    fn emitHyps(self: *ProofEmitter) !void {
        for (self.theorem.theorem_hyps.items, self.hyp_slots) |hyp, *slot| {
            try self.emitExpr(hyp);
            slot.* = try self.stream.appendSlot(self.allocator, .Hyp, 0);
        }
    }

    fn emitLine(
        self: *ProofEmitter,
        line_idx: usize,
    ) anyerror!void {
        if (self.line_slots[line_idx]) |slot| {
            return self.stream.append(self.allocator, .Ref, slot);
        }

        const line = self.lines[line_idx];
        self.line_slots[line_idx] = switch (line.data) {
            .rule => |rule| blk: {
                for (rule.refs) |ref| {
                    try self.emitRef(ref);
                }
                for (rule.bindings) |binding| {
                    try self.emitExpr(binding);
                }
                try self.emitExpr(line.expr);
                break :blk try self.stream.appendSlot(self.allocator, .ThmSave, rule.rule_id);
            },
            .transport => |transport| blk: {
                try self.emitExpr(line.expr);
                try self.emitRef(transport.source);
                try self.stream.append(self.allocator, .Conv, 0);
                try self.emitConversion(line.expr, transport.source_expr);
                break :blk try self.stream.appendSlot(self.allocator, .Save, 0);
            },
            .sorry => blk: {
                // Mid-stream form: `Sorry: S, e -> S, |- e`. The admitted
                // proof is saved like any other line so later references
                // reach it through the heap.
                try self.emitExpr(line.expr);
                try self.stream.append(self.allocator, .Sorry, 0);
                break :blk try self.stream.appendSlot(self.allocator, .Save, 0);
            },
        };
    }

    fn emitRef(
        self: *ProofEmitter,
        ref: CheckedRef,
    ) anyerror!void {
        switch (ref) {
            .hyp => |idx| try self.stream.append(self.allocator, .Ref, self.hyp_slots[idx]),
            .line => |idx| try self.emitLine(idx),
        }
    }

    fn emitConversion(
        self: *ProofEmitter,
        target_expr: ExprId,
        source_expr: ExprId,
    ) !void {
        var def_ops = DefOps.Context.init(
            self.allocator,
            @constCast(self.theorem),
            self.env.?,
        );
        defer def_ops.deinit();
        const plan = try def_ops.compareTransparent(
            target_expr,
            source_expr,
        ) orelse return error.MissingConversionPlan;
        try self.emitConversionPlan(plan);
    }

    fn emitConversionPlan(
        self: *ProofEmitter,
        plan: *const DefOps.ConversionPlan,
    ) !void {
        switch (plan.*) {
            .refl => try self.stream.append(self.allocator, .Refl, 0),
            .unfold_lhs => |step| {
                try self.emitExpr(step.witness);
                try self.stream.append(self.allocator, .Unfold, 0);
                try self.emitConversionPlan(step.next);
            },
            .unfold_rhs => |step| {
                try self.stream.append(self.allocator, .Symm, 0);
                try self.emitExpr(step.witness);
                try self.stream.append(self.allocator, .Unfold, 0);
                try self.stream.append(self.allocator, .Symm, 0);
                try self.emitConversionPlan(step.next);
            },
            .cong => |step| {
                try self.stream.append(self.allocator, .Cong, 0);
                for (step.children) |child| {
                    try self.emitConversionPlan(child);
                }
            },
        }
    }

    /// Ends the stream and writes it out, its unread saves settled.
    fn finish(self: *ProofEmitter) !ProofBody {
        try self.stream.append(self.allocator, .End, 0);
        return try self.stream.toBytes(self.allocator);
    }
};

pub fn compileTermRecord(
    allocator: std.mem.Allocator,
    parser: *MM0Parser,
    stmt: TermStmt,
) !TermRecord {
    var theorem = TheoremContext.init(allocator);
    defer theorem.deinit();
    try theorem.seedTerm(parser, stmt);

    const unify = if (stmt.body) |body| blk: {
        const expr_id = try theorem.internParsedExpr(body);
        break :blk try buildTermUnifyStream(allocator, &theorem, expr_id);
    } else &.{};

    return .{
        .args = try buildArgArray(parser, stmt.args),
        .ret_sort = try lookupSortId(parser, stmt.ret_sort_name),
        .ret_deps = stmt.ret_deps,
        .is_def = stmt.is_def,
        .unify = unify,
        .name = stmt.name,
        .var_names = stmt.arg_names,
    };
}

pub fn buildArgArray(
    parser: *MM0Parser,
    args: []const ArgInfo,
) ![]const Arg {
    const result = try parser.core.allocator.alloc(Arg, args.len);
    for (args, 0..) |arg, idx| {
        // ArgInfo masks are binder-indexed (dummies included); MMB Arg
        // masks index the bound args only. A dependency on a dummy is not
        // representable in MMB.
        const remapped = binderDepsToBoundArgDeps(args, arg.deps);
        if (remapped.dummy_deps != 0) return error.ArgDependencyOnDummy;
        result[idx] = .{
            .deps = remapped.deps,
            .reserved = 0,
            .sort = try lookupSortId(parser, arg.sort_name),
            .bound = arg.bound,
        };
    }
    return result;
}

pub fn lookupSortId(parser: *const MM0Parser, sort_name: []const u8) !u7 {
    const sort_id = parser.core.sort_names.get(sort_name) orelse return error.UnknownSort;
    return @intCast(sort_id);
}

fn validateProofBoundaryExpr(
    theorem: *const TheoremContext,
    expr_id: ExprId,
) !void {
    try CheckedIr.validateNoPlaceholderExpr(theorem, expr_id);
}

fn validateProofBoundaryExprs(
    theorem: *const TheoremContext,
    exprs: []const ExprId,
) !void {
    try CheckedIr.validateNoPlaceholderSlice(theorem, exprs);
}

fn buildDefProofBodyFromExpr(
    allocator: std.mem.Allocator,
    theorem: *const TheoremContext,
    expr_id: ExprId,
) ![]const u8 {
    try validateProofBoundaryExpr(theorem, expr_id);

    var emitter = try ProofEmitter.init(allocator, theorem, null, &.{});
    defer emitter.deinit();
    try emitter.emitExpr(expr_id);
    const body = try emitter.finish();
    return body.bytes;
}

pub fn buildDefProofBody(
    allocator: std.mem.Allocator,
    parser: *const MM0Parser,
    stmt: TermStmt,
) ![]const u8 {
    var theorem = TheoremContext.init(allocator);
    defer theorem.deinit();
    try theorem.seedTerm(parser, stmt);
    const body = stmt.body orelse return error.ExpectedDefinitionBody;
    const expr_id = try theorem.internParsedExpr(body);
    return try buildDefProofBodyFromExpr(allocator, &theorem, expr_id);
}

pub fn buildAxiomProofBody(
    allocator: std.mem.Allocator,
    theorem: *const TheoremContext,
    concl: ExprId,
) ![]const u8 {
    try validateProofBoundaryExprs(theorem, theorem.theorem_hyps.items);
    try validateProofBoundaryExpr(theorem, concl);

    var emitter = try ProofEmitter.init(allocator, theorem, null, &.{});
    defer emitter.deinit();
    try emitter.emitHyps();
    try emitter.emitExpr(concl);
    const body = try emitter.finish();
    return body.bytes;
}

pub fn buildTermUnifyStream(
    allocator: std.mem.Allocator,
    theorem: *const TheoremContext,
    body: ExprId,
) ![]const u8 {
    try validateProofBoundaryExpr(theorem, body);

    var emitter = try UnifyEmitter.init(allocator, theorem);
    defer emitter.deinit();
    try emitter.emitExpr(body);
    return try emitter.finish();
}

pub fn buildAssertionUnifyStream(
    allocator: std.mem.Allocator,
    theorem: *const TheoremContext,
    concl: ExprId,
) ![]const u8 {
    try validateProofBoundaryExprs(theorem, theorem.theorem_hyps.items);
    try validateProofBoundaryExpr(theorem, concl);

    var emitter = try UnifyEmitter.init(allocator, theorem);
    defer emitter.deinit();
    try emitter.emitAssertion(concl, theorem.theorem_hyps.items);
    return try emitter.finish();
}

pub fn buildRuleUnifyStream(
    allocator: std.mem.Allocator,
    rule: *const RuleDecl,
) ![]const u8 {
    // For inference we rebuild the cited rule's unify stream from the same
    // binder-indexed templates that drive explicit instantiation. This keeps
    // one source of truth for theorem shape instead of maintaining a second,
    // compiler-only matcher by hand.
    var theorem = TheoremContext.init(allocator);
    defer theorem.deinit();
    try theorem.seedBinderCount(rule.args.len);

    const binders = theorem.theorem_vars.items;
    const concl = try theorem.instantiateTemplate(rule.concl, binders);
    const hyps = try allocator.alloc(ExprId, rule.hyps.len);
    defer allocator.free(hyps);
    for (rule.hyps, hyps) |template, *hyp| {
        hyp.* = try theorem.instantiateTemplate(template, binders);
    }

    var emitter = try UnifyEmitter.init(allocator, &theorem);
    defer emitter.deinit();
    try emitter.emitAssertion(concl, hyps);
    return try emitter.finish();
}

pub fn buildTheoremProofBody(
    allocator: std.mem.Allocator,
    theorem: *TheoremContext,
    env: *const GlobalEnv,
    lines: []const CheckedLine,
) !ProofBody {
    try validateProofBoundaryExprs(theorem, theorem.theorem_hyps.items);
    try CheckedIr.validateLinesCached(theorem, lines);
    if (try CheckedIr.firstDepViolation(env, theorem, lines)) |_| {
        return error.DepViolation;
    }

    var emitter = try ProofEmitter.init(allocator, theorem, env, lines);
    defer emitter.deinit();
    try emitter.emitHyps();
    try emitter.emitLine(lines.len - 1);
    return try emitter.finish();
}

pub fn buildHypNames(
    allocator: std.mem.Allocator,
    count: usize,
) ![]const ?[]const u8 {
    const names = try allocator.alloc(?[]const u8, count);
    for (0..count) |idx| {
        names[idx] = try hypText(allocator, idx + 1);
    }
    return names;
}

pub fn buildTheoremVarNames(
    allocator: std.mem.Allocator,
    arg_names: []const ?[]const u8,
    dummy_count: usize,
) ![]const ?[]const u8 {
    const names = try allocator.alloc(?[]const u8, arg_names.len + dummy_count);
    @memcpy(names[0..arg_names.len], arg_names);
    @memset(names[arg_names.len..], null);
    return names;
}

pub fn hypText(
    allocator: std.mem.Allocator,
    index: usize,
) ![]const u8 {
    return try std.fmt.allocPrint(allocator, "#{d}", .{index});
}

test "ProofStream writes unread saves unsaved and moves later slots down" {
    const allocator = std.testing.allocator;
    // Slot 0 is a variable; the stream allocates slots 1 through 6.
    var stream: ProofStream = .init(1);
    defer stream.deinit(allocator);
    const emitted = [_]ProofStream.Cmd{
        .{ .op = .Ref, .data = 0 },
        .{ .op = .TermSave, .data = 7 }, // slot 1, unread
        .{ .op = .TermSave, .data = 8 }, // slot 2
        .{ .op = .Dummy, .data = 1 }, // slot 3, kept unread
        .{ .op = .ThmSave, .data = 9 }, // slot 4, unread
        .{ .op = .Save, .data = 0 }, // slot 5, unread
        .{ .op = .Save, .data = 0 }, // slot 6
        .{ .op = .Ref, .data = 2 },
        .{ .op = .Ref, .data = 6 },
        .{ .op = .Ref, .data = 3 },
        .{ .op = .End, .data = 0 },
    };
    for (emitted) |cmd| switch (ProofStream.slotUse(cmd.op)) {
        .kept, .save => _ = try stream.appendSlot(allocator, cmd.op, cmd.data),
        .none, .read => try stream.append(allocator, cmd.op, cmd.data),
    };
    const body = try stream.toBytes(allocator);
    defer allocator.free(body.bytes);
    try std.testing.expectEqual(@as(u32, 4), body.heap_len);
    const bytes = body.bytes;

    var expected: std.ArrayListUnmanaged(u8) = .empty;
    defer expected.deinit(allocator);
    const written = [_]ProofStream.Cmd{
        .{ .op = .Ref, .data = 0 },
        .{ .op = .Term, .data = 7 },
        .{ .op = .TermSave, .data = 8 }, // now slot 1
        .{ .op = .Dummy, .data = 1 }, // now slot 2
        .{ .op = .Thm, .data = 9 },
        .{ .op = .Save, .data = 0 }, // now slot 3
        .{ .op = .Ref, .data = 1 },
        .{ .op = .Ref, .data = 3 },
        .{ .op = .Ref, .data = 2 },
        .{ .op = .End, .data = 0 },
    };
    for (written) |cmd| try MmbWriter.appendCmd(&expected, allocator, cmd.op, cmd.data);
    try std.testing.expectEqualSlices(u8, expected.items, bytes);
}

test "a unify stream saves only what it reads back" {
    var theorem = TheoremContext.init(std.testing.allocator);
    defer theorem.deinit();

    // `f (g c) (g c)`: the second `g c` reads back the first, so `c` inside
    // it is never read back and is matched unsaved.
    const c = try theorem.interner.internApp(2, &.{});
    const g_c = try theorem.interner.internApp(1, &.{c});
    const f = try theorem.interner.internApp(0, &.{ g_c, g_c });
    const bytes = try buildTermUnifyStream(std.testing.allocator, &theorem, f);
    defer std.testing.allocator.free(bytes);

    var expected: std.ArrayListUnmanaged(u8) = .empty;
    defer expected.deinit(std.testing.allocator);
    const written = [_]UnifyStream.Cmd{
        .{ .op = .UTerm, .data = 0 },
        .{ .op = .UTermSave, .data = 1 }, // slot 0
        .{ .op = .UTerm, .data = 2 },
        .{ .op = .URef, .data = 0 },
        .{ .op = .End, .data = 0 },
    };
    for (written) |cmd| {
        try MmbWriter.appendCmd(&expected, std.testing.allocator, cmd.op, cmd.data);
    }
    try std.testing.expectEqualSlices(u8, expected.items, bytes);
}

test "buildAxiomProofBody reports unsolved metas distinctly" {
    var theorem = TheoremContext.init(std.testing.allocator);
    defer theorem.deinit();

    const meta = try theorem.addMetaPlaceholderResolved("obj");
    try std.testing.expectError(
        error.UnsolvedMetaLeakage,
        buildAxiomProofBody(std.testing.allocator, &theorem, meta),
    );
}

test "buildAxiomProofBody rejects placeholders" {
    var theorem = TheoremContext.init(std.testing.allocator);
    defer theorem.deinit();

    const placeholder = try theorem.addPlaceholderResolved("obj");
    try std.testing.expectError(
        error.PlaceholderLeakage,
        buildAxiomProofBody(std.testing.allocator, &theorem, placeholder),
    );
}

test "buildTermUnifyStream rejects placeholders" {
    var theorem = TheoremContext.init(std.testing.allocator);
    defer theorem.deinit();

    const placeholder = try theorem.addPlaceholderResolved("obj");
    try std.testing.expectError(
        error.PlaceholderLeakage,
        buildTermUnifyStream(std.testing.allocator, &theorem, placeholder),
    );
}

test "buildAssertionUnifyStream rejects placeholders in hypotheses" {
    var theorem = TheoremContext.init(std.testing.allocator);
    defer theorem.deinit();
    try theorem.seedBinderCount(1);

    const placeholder = try theorem.addPlaceholderResolved("obj");
    try theorem.theorem_hyps.append(std.testing.allocator, placeholder);

    try std.testing.expectError(
        error.PlaceholderLeakage,
        buildAssertionUnifyStream(
            std.testing.allocator,
            &theorem,
            theorem.theorem_vars.items[0],
        ),
    );
}

test "buildDefProofBody rejects placeholders after term seeding" {
    var theorem = TheoremContext.init(std.testing.allocator);
    defer theorem.deinit();

    const placeholder = try theorem.addPlaceholderResolved("obj");
    try std.testing.expectError(
        error.PlaceholderLeakage,
        buildDefProofBodyFromExpr(
            std.testing.allocator,
            &theorem,
            placeholder,
        ),
    );
}

test "buildTheoremProofBody rejects placeholders in checked lines" {
    var arena = ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();

    var theorem = TheoremContext.init(arena.allocator());
    defer theorem.deinit();
    try theorem.seedBinderCount(1);

    const placeholder = try theorem.addPlaceholderResolved("obj");
    const bindings = [_]ExprId{theorem.theorem_vars.items[0]};
    const lines = [_]CheckedLine{.{
        .expr = placeholder,
        .data = .{ .rule = .{
            .rule_id = 0,
            .bindings = &bindings,
            .refs = &.{},
        } },
    }};

    var env = GlobalEnv.init(arena.allocator());

    try std.testing.expectError(
        error.PlaceholderLeakage,
        buildTheoremProofBody(arena.allocator(), &theorem, &env, &lines),
    );
}
