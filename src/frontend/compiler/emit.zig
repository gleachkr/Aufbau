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

/// A proof stream recorded command by command, its saves settled only once
/// the whole stream is known. Emission saves every line and every term so
/// that a later use can `Ref` it; `toBytes` then writes a `TermSave`,
/// `ThmSave` or `Save` that no `Ref` reads as `Term`, `Thm` or nothing, and
/// moves the heap slots after it down, so the verifier's heap holds only
/// what the proof reads back.
const ProofStream = struct {
    cmds: std.ArrayListUnmanaged(Cmd) = .empty,

    const Cmd = struct { op: ProofCmd, data: u32 };

    fn deinit(self: *ProofStream, allocator: std.mem.Allocator) void {
        self.cmds.deinit(allocator);
    }

    fn append(
        self: *ProofStream,
        allocator: std.mem.Allocator,
        op: ProofCmd,
        data: u32,
    ) !void {
        try self.cmds.append(allocator, .{ .op = op, .data = data });
    }

    /// `fixed_slots` heap slots (the variables) precede the stream's own;
    /// `heap_len` is the slot count the stream was emitted against.
    fn toBytes(
        self: *const ProofStream,
        allocator: std.mem.Allocator,
        fixed_slots: u32,
        heap_len: u32,
    ) ![]const u8 {
        var read = try std.DynamicBitSetUnmanaged.initEmpty(allocator, heap_len);
        defer read.deinit(allocator);
        for (self.cmds.items) |cmd| {
            if (cmd.op == .Ref) read.set(cmd.data);
        }
        // Slots are allocated in stream order, so walking the stream again
        // meets each save at its emitted slot `old`.
        const moved = try allocator.alloc(u32, heap_len);
        defer allocator.free(moved);
        for (moved[0..fixed_slots], 0..) |*slot, idx| slot.* = @intCast(idx);
        var old = fixed_slots;
        var new = fixed_slots;
        var bytes: std.ArrayListUnmanaged(u8) = .empty;
        errdefer bytes.deinit(allocator);
        for (self.cmds.items) |cmd| switch (cmd.op) {
            .Ref => try MmbWriter.appendCmd(&bytes, allocator, ProofCmd.Ref, moved[cmd.data]),
            .Dummy, .Hyp, .TermSave, .ThmSave, .Save => {
                // `Dummy` and `Hyp` always take a slot, a save only when read.
                if (read.isSet(old) or cmd.op == .Dummy or cmd.op == .Hyp) {
                    moved[old] = new;
                    new += 1;
                    try MmbWriter.appendCmd(&bytes, allocator, cmd.op, cmd.data);
                } else if (unsaved(cmd.op)) |op| {
                    try MmbWriter.appendCmd(&bytes, allocator, op, cmd.data);
                }
                old += 1;
            },
            else => try MmbWriter.appendCmd(&bytes, allocator, cmd.op, cmd.data),
        };
        std.debug.assert(old == heap_len);
        return try bytes.toOwnedSlice(allocator);
    }

    /// A save's unsaved form; a bare `Save` has none and is dropped.
    fn unsaved(op: ProofCmd) ?ProofCmd {
        return switch (op) {
            .TermSave => .Term,
            .ThmSave => .Thm,
            else => null,
        };
    }
};

/// Post-order emit of an expression's proof-stream construction, memoizing each
/// sub-expression to its heap slot in `expr_slots`. Shared verbatim by
/// `ExprProofEmitter` and `TheoremProofEmitter`, which differ only in the extra
/// state they carry around this emission core.
fn emitProofExpr(
    allocator: std.mem.Allocator,
    theorem: *const TheoremContext,
    stream: *ProofStream,
    expr_slots: *ExprSlotMap,
    heap_len: *u32,
    expr_id: ExprId,
) !void {
    if (expr_slots.get(expr_id)) |slot| {
        try stream.append(allocator, .Ref, slot);
        return;
    }

    const node = theorem.interner.node(expr_id);
    switch (node.*) {
        .variable => |var_id| switch (var_id) {
            .theorem_var => return error.UnboundExprVariable,
            .dummy_var => |dummy_id| {
                const info = try theorem.requireDummyInfo(dummy_id);
                try stream.append(allocator, .Dummy, info.sort_id);
                const slot = heap_len.*;
                heap_len.* = try std.math.add(u32, heap_len.*, 1);
                try expr_slots.put(allocator, expr_id, slot);
            },
        },
        .placeholder => |id| return CheckedIr.leakageError(
            theorem,
            id,
        ),
        .app => |app| {
            for (app.args) |arg| {
                try emitProofExpr(allocator, theorem, stream, expr_slots, heap_len, arg);
            }
            try stream.append(allocator, .TermSave, app.term_id);
            const slot = heap_len.*;
            heap_len.* = try std.math.add(u32, heap_len.*, 1);
            try expr_slots.put(allocator, expr_id, slot);
        },
    }
}

pub const ExprProofEmitter = struct {
    allocator: std.mem.Allocator,
    theorem: *const TheoremContext,
    stream: ProofStream = .{},
    expr_slots: ExprSlotMap = .empty,
    heap_len: u32,

    pub fn init(
        allocator: std.mem.Allocator,
        theorem: *const TheoremContext,
    ) ExprProofEmitter {
        var emitter = ExprProofEmitter{
            .allocator = allocator,
            .theorem = theorem,
            .heap_len = @intCast(theorem.theorem_vars.items.len),
        };
        for (theorem.theorem_vars.items, 0..) |expr_id, idx| {
            emitter.expr_slots.put(allocator, expr_id, @intCast(idx)) catch unreachable;
        }
        return emitter;
    }

    pub fn deinit(self: *ExprProofEmitter) void {
        self.stream.deinit(self.allocator);
        self.expr_slots.deinit(self.allocator);
    }

    /// Ends the stream and writes it out, its unread saves settled.
    pub fn finish(self: *ExprProofEmitter) ![]const u8 {
        try self.stream.append(self.allocator, .End, 0);
        return try self.stream.toBytes(
            self.allocator,
            @intCast(self.theorem.theorem_vars.items.len),
            self.heap_len,
        );
    }

    pub fn emitExpr(self: *ExprProofEmitter, expr_id: ExprId) !void {
        return emitProofExpr(
            self.allocator,
            self.theorem,
            &self.stream,
            &self.expr_slots,
            &self.heap_len,
            expr_id,
        );
    }
};

pub const UnifyEmitter = struct {
    allocator: std.mem.Allocator,
    theorem: *const TheoremContext,
    bytes: std.ArrayListUnmanaged(u8) = .empty,
    slots: ExprSlotMap = .empty,
    remaining_uses: std.AutoHashMapUnmanaged(ExprId, u32) = .empty,
    heap_len: u32,

    pub fn init(
        allocator: std.mem.Allocator,
        theorem: *const TheoremContext,
    ) UnifyEmitter {
        var emitter = UnifyEmitter{
            .allocator = allocator,
            .theorem = theorem,
            .heap_len = @intCast(theorem.theorem_vars.items.len),
        };
        for (theorem.theorem_vars.items, 0..) |expr_id, idx| {
            emitter.slots.put(allocator, expr_id, @intCast(idx)) catch unreachable;
        }
        return emitter;
    }

    pub fn deinit(self: *UnifyEmitter) void {
        self.bytes.deinit(self.allocator);
        self.slots.deinit(self.allocator);
        self.remaining_uses.deinit(self.allocator);
    }

    pub fn noteExprUse(self: *UnifyEmitter, expr_id: ExprId) !void {
        const gop = try self.remaining_uses.getOrPut(self.allocator, expr_id);
        if (gop.found_existing) {
            gop.value_ptr.* = try std.math.add(u32, gop.value_ptr.*, 1);
        } else {
            gop.value_ptr.* = 1;
        }
        switch (self.theorem.interner.node(expr_id).*) {
            .variable => {},
            .placeholder => |id| return CheckedIr.leakageError(
                self.theorem,
                id,
            ),
            .app => |app| {
                for (app.args) |arg| {
                    try self.noteExprUse(arg);
                }
            },
        }
    }

    fn claimFirstUse(self: *UnifyEmitter, expr_id: ExprId) !bool {
        const remaining = self.remaining_uses.getPtr(expr_id) orelse {
            return error.UnknownExprUseCount;
        };
        const count = remaining.*;
        if (count == 0) return error.InvalidExprUseCount;
        remaining.* = count - 1;
        return count > 1;
    }

    pub fn emitExpr(self: *UnifyEmitter, expr_id: ExprId) !void {
        if (self.slots.get(expr_id)) |slot| {
            try MmbWriter.appendCmd(&self.bytes, self.allocator, UnifyCmd.URef, slot);
            return;
        }

        const save_for_ref = try self.claimFirstUse(expr_id);
        const node = self.theorem.interner.node(expr_id);
        switch (node.*) {
            .variable => |var_id| switch (var_id) {
                .theorem_var => return error.UnboundExprVariable,
                .dummy_var => |dummy_id| {
                    const info = try self.theorem.requireDummyInfo(dummy_id);
                    try MmbWriter.appendCmd(
                        &self.bytes,
                        self.allocator,
                        UnifyCmd.UDummy,
                        info.sort_id,
                    );
                    // Verifier-side `UDummy` always appends to the unify
                    // heap. Even single-use dummies reserve a slot and shift
                    // later `URef` indices.
                    const slot = self.heap_len;
                    self.heap_len = try std.math.add(u32, self.heap_len, 1);
                    if (save_for_ref) {
                        try self.slots.put(self.allocator, expr_id, slot);
                    }
                },
            },
            .placeholder => |id| return CheckedIr.leakageError(
                self.theorem,
                id,
            ),
            .app => |app| {
                try MmbWriter.appendCmd(
                    &self.bytes,
                    self.allocator,
                    if (save_for_ref) UnifyCmd.UTermSave else UnifyCmd.UTerm,
                    app.term_id,
                );
                if (save_for_ref) {
                    const slot = self.heap_len;
                    self.heap_len = try std.math.add(u32, self.heap_len, 1);
                    try self.slots.put(self.allocator, expr_id, slot);
                }
                for (app.args) |arg| {
                    try self.emitExpr(arg);
                }
            },
        }
    }
};

pub const TheoremProofEmitter = struct {
    allocator: std.mem.Allocator,
    theorem: *const TheoremContext,
    env: *const GlobalEnv,
    lines: []const CheckedLine,
    stream: ProofStream = .{},
    expr_slots: ExprSlotMap = .empty,
    heap_len: u32,
    hyp_slots: []u32,
    line_slots: []u32,
    emitted: []bool,

    pub fn init(
        allocator: std.mem.Allocator,
        theorem: *const TheoremContext,
        env: *const GlobalEnv,
        lines: []const CheckedLine,
    ) !TheoremProofEmitter {
        var emitter = TheoremProofEmitter{
            .allocator = allocator,
            .theorem = theorem,
            .env = env,
            .lines = lines,
            .heap_len = @intCast(theorem.theorem_vars.items.len),
            .hyp_slots = try allocator.alloc(u32, theorem.theorem_hyps.items.len),
            .line_slots = try allocator.alloc(u32, lines.len),
            .emitted = try allocator.alloc(bool, lines.len),
        };
        @memset(emitter.emitted, false);
        for (theorem.theorem_vars.items, 0..) |expr_id, idx| {
            try emitter.expr_slots.put(allocator, expr_id, @intCast(idx));
        }
        return emitter;
    }

    pub fn deinit(self: *TheoremProofEmitter) void {
        self.stream.deinit(self.allocator);
        self.expr_slots.deinit(self.allocator);
        self.allocator.free(self.hyp_slots);
        self.allocator.free(self.line_slots);
        self.allocator.free(self.emitted);
    }

    pub fn emitHyps(self: *TheoremProofEmitter) !void {
        for (self.theorem.theorem_hyps.items, 0..) |hyp, idx| {
            try self.emitExpr(hyp);
            try self.stream.append(self.allocator, .Hyp, 0);
            self.hyp_slots[idx] = self.heap_len;
            self.heap_len = try std.math.add(u32, self.heap_len, 1);
        }
    }

    pub fn emitLine(
        self: *TheoremProofEmitter,
        line_idx: usize,
    ) anyerror!void {
        if (self.emitted[line_idx]) {
            try self.stream.append(self.allocator, .Ref, self.line_slots[line_idx]);
            return;
        }

        const line = self.lines[line_idx];
        switch (line.data) {
            .rule => |rule| {
                for (rule.refs) |ref| {
                    try self.emitRef(ref);
                }
                for (rule.bindings) |binding| {
                    try self.emitExpr(binding);
                }
                try self.emitExpr(line.expr);
                try self.stream.append(self.allocator, .ThmSave, rule.rule_id);
            },
            .transport => |transport| {
                try self.emitExpr(line.expr);
                try self.emitRef(transport.source);
                try self.stream.append(self.allocator, .Conv, 0);
                try self.emitConversion(line.expr, transport.source_expr);
                try self.stream.append(self.allocator, .Save, 0);
            },
            .sorry => {
                // Mid-stream form: `Sorry: S, e -> S, |- e`. The admitted
                // proof is saved like any other line so later references
                // reach it through the heap.
                try self.emitExpr(line.expr);
                try self.stream.append(self.allocator, .Sorry, 0);
                try self.stream.append(self.allocator, .Save, 0);
            },
        }
        self.line_slots[line_idx] = self.heap_len;
        self.heap_len = try std.math.add(u32, self.heap_len, 1);
        self.emitted[line_idx] = true;
    }

    fn emitRef(
        self: *TheoremProofEmitter,
        ref: CheckedRef,
    ) anyerror!void {
        switch (ref) {
            .hyp => |idx| try self.stream.append(self.allocator, .Ref, self.hyp_slots[idx]),
            .line => |idx| try self.emitLine(idx),
        }
    }

    fn emitConversion(
        self: *TheoremProofEmitter,
        target_expr: ExprId,
        source_expr: ExprId,
    ) !void {
        var def_ops = DefOps.Context.init(
            self.allocator,
            @constCast(self.theorem),
            self.env,
        );
        defer def_ops.deinit();
        const plan = try def_ops.compareTransparent(
            target_expr,
            source_expr,
        ) orelse return error.MissingConversionPlan;
        try self.emitConversionPlan(plan);
    }

    fn emitConversionPlan(
        self: *TheoremProofEmitter,
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
    pub fn finish(self: *TheoremProofEmitter) ![]const u8 {
        try self.stream.append(self.allocator, .End, 0);
        return try self.stream.toBytes(
            self.allocator,
            @intCast(self.theorem.theorem_vars.items.len),
            self.heap_len,
        );
    }

    pub fn emitExpr(self: *TheoremProofEmitter, expr_id: ExprId) !void {
        return emitProofExpr(
            self.allocator,
            self.theorem,
            &self.stream,
            &self.expr_slots,
            &self.heap_len,
            expr_id,
        );
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

    var emitter = ExprProofEmitter.init(allocator, theorem);
    defer emitter.deinit();
    try emitter.emitExpr(expr_id);
    return try emitter.finish();
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

    var emitter = ExprProofEmitter.init(allocator, theorem);
    defer emitter.deinit();
    for (theorem.theorem_hyps.items) |hyp| {
        try emitter.emitExpr(hyp);
        try emitter.stream.append(allocator, .Hyp, 0);
        emitter.heap_len = try std.math.add(u32, emitter.heap_len, 1);
    }
    try emitter.emitExpr(concl);
    return try emitter.finish();
}

pub fn buildTermUnifyStream(
    allocator: std.mem.Allocator,
    theorem: *const TheoremContext,
    body: ExprId,
) ![]const u8 {
    try validateProofBoundaryExpr(theorem, body);

    var emitter = UnifyEmitter.init(allocator, theorem);
    defer emitter.deinit();
    try emitter.noteExprUse(body);
    try emitter.emitExpr(body);
    try MmbWriter.appendCmd(&emitter.bytes, allocator, UnifyCmd.End, 0);
    return try emitter.bytes.toOwnedSlice(allocator);
}

pub fn buildAssertionUnifyStream(
    allocator: std.mem.Allocator,
    theorem: *const TheoremContext,
    concl: ExprId,
) ![]const u8 {
    try validateProofBoundaryExprs(theorem, theorem.theorem_hyps.items);
    try validateProofBoundaryExpr(theorem, concl);

    var emitter = UnifyEmitter.init(allocator, theorem);
    defer emitter.deinit();
    try emitter.noteExprUse(concl);
    var hyp_idx = theorem.theorem_hyps.items.len;
    while (hyp_idx > 0) {
        hyp_idx -= 1;
        try emitter.noteExprUse(theorem.theorem_hyps.items[hyp_idx]);
    }
    try emitter.emitExpr(concl);
    // `UHyp` pushes the next hypothesis target onto the unify stack before
    // replay continues. To make hypotheses replay in source order, the stream
    // therefore stores them in reverse.
    hyp_idx = theorem.theorem_hyps.items.len;
    while (hyp_idx > 0) {
        hyp_idx -= 1;
        try MmbWriter.appendCmd(&emitter.bytes, allocator, UnifyCmd.UHyp, 0);
        try emitter.emitExpr(theorem.theorem_hyps.items[hyp_idx]);
    }
    try MmbWriter.appendCmd(&emitter.bytes, allocator, UnifyCmd.End, 0);
    return try emitter.bytes.toOwnedSlice(allocator);
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

    var emitter = UnifyEmitter.init(allocator, &theorem);
    defer emitter.deinit();

    const binders = theorem.theorem_vars.items;
    const concl = try theorem.instantiateTemplate(rule.concl, binders);
    try emitter.noteExprUse(concl);

    var hyps = try allocator.alloc(ExprId, rule.hyps.len);
    defer allocator.free(hyps);
    var hyp_idx = rule.hyps.len;
    while (hyp_idx > 0) {
        hyp_idx -= 1;
        const hyp = try theorem.instantiateTemplate(rule.hyps[hyp_idx], binders);
        hyps[hyp_idx] = hyp;
        try emitter.noteExprUse(hyp);
    }

    try emitter.emitExpr(concl);
    hyp_idx = rule.hyps.len;
    while (hyp_idx > 0) {
        hyp_idx -= 1;
        try MmbWriter.appendCmd(&emitter.bytes, allocator, UnifyCmd.UHyp, 0);
        try emitter.emitExpr(hyps[hyp_idx]);
    }

    try MmbWriter.appendCmd(&emitter.bytes, allocator, UnifyCmd.End, 0);
    return try emitter.bytes.toOwnedSlice(allocator);
}

pub fn buildTheoremProofBody(
    allocator: std.mem.Allocator,
    theorem: *TheoremContext,
    env: *const GlobalEnv,
    lines: []const CheckedLine,
) ![]const u8 {
    try validateProofBoundaryExprs(theorem, theorem.theorem_hyps.items);
    try CheckedIr.validateLinesCached(theorem, lines);
    if (try CheckedIr.firstDepViolation(env, theorem, lines)) |_| {
        return error.DepViolation;
    }

    var emitter = try TheoremProofEmitter.init(allocator, theorem, env, lines);
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
    var stream: ProofStream = .{};
    defer stream.deinit(allocator);
    // Slot 0 is a variable; the stream allocates slots 1 through 6.
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
    for (emitted) |cmd| try stream.append(allocator, cmd.op, cmd.data);
    const bytes = try stream.toBytes(allocator, 1, 7);
    defer allocator.free(bytes);

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
