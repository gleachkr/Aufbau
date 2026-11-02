//! A path index, after `../clipper.zig`, over the core's facts and over
//! each head's rule conclusions: each path into an item has a cell
//! recording, per token, the items with that token there, and the items
//! with a wildcard there. A query keeps the items that apply the goal's
//! token at every path where both are rigid, walking the goal's
//! expression itself. Wildcards are placeholders (a goal's once its bound
//! wvars are resolved), a conclusion's binders and the terms the matcher
//! treats specially there (`Terms.isRigid`), and applications that unfold
//! or read as a bag.
//! Every item a query drops clashes with the goal (`Terms.clash`,
//! `Terms.conclusionClash`), and no fact it drops might equal it
//! (`Terms.mightEqual`); those still screen the rest, so the search is
//! unchanged. Bindings made after a query only add clashes, so its result
//! stays a superset while they hold.

const std = @import("std");
const ExprId = @import("../../../expr.zig").ExprId;
const TemplateExpr = @import("../../../rules.zig").TemplateExpr;
const Terms = @import("./terms.zig").Terms;

const none = std.math.maxInt(u32);

const Entry = struct {
    token: u64,
    /// The offset of its set in `TermIndex.sets`.
    set: u32,
};

const Cell = struct {
    /// The items with a wildcard here: they meet any goal node at or
    /// below this path.
    wild: u32 = none,
    /// The items with a rigid node here, per token.
    tokens: std.ArrayListUnmanaged(Entry) = .empty,
    /// The cell of each argument position below.
    children: std.ArrayListUnmanaged(u32) = .empty,
    depth: u32,

    fn find(self: *const Cell, token: u64) u32 {
        for (self.tokens.items) |entry| if (entry.token == token) return entry.set;
        return none;
    }
};

/// What an application of `term_id` reads as: its term, or null when it
/// unfolds or reads as a bag.
fn appToken(terms: *const Terms, term_id: u32) ?u64 {
    return if (terms.opensDef(term_id) or terms.bagFor(term_id) != null) null else term_id;
}

/// What a goal or fact node reads as: an application's token, a
/// variable's own id, or null for a placeholder.
fn exprToken(terms: *const Terms, expr: ExprId) ?u64 {
    return switch (terms.theorem.interner.node(expr).*) {
        .app => |app| appToken(terms, app.term_id),
        .variable => (1 << 32) | @as(u64, expr),
        .placeholder => null,
    };
}

pub const TermIndex = struct {
    allocator: std.mem.Allocator,
    /// How many items, and the `u64` words of one set of them.
    count: usize,
    words: u32,
    added: usize = 0,
    sets: std.ArrayListUnmanaged(u64) = .empty,
    cells: std.ArrayListUnmanaged(Cell) = .empty,
    depth: u32 = 0,

    pub fn init(allocator: std.mem.Allocator, count: usize) !TermIndex {
        var self = TermIndex{ .allocator = allocator, .count = count, .words = @intCast((count + 63) / 64) };
        try self.cells.append(allocator, .{ .depth = 0 });
        return self;
    }

    pub fn deinit(self: *TermIndex) void {
        for (self.cells.items) |*cell| {
            cell.tokens.deinit(self.allocator);
            cell.children.deinit(self.allocator);
        }
        self.cells.deinit(self.allocator);
        self.sets.deinit(self.allocator);
    }

    /// Add a fact, the next item.
    pub fn addExpr(self: *TermIndex, terms: *const Terms, expr: ExprId) !void {
        try self.insertExpr(terms, expr, 0, self.added);
        self.added += 1;
    }

    /// Add a rule conclusion, the next item.
    pub fn addTemplate(self: *TermIndex, terms: *const Terms, template: TemplateExpr) !void {
        try self.insertTemplate(terms, template, 0, self.added);
        self.added += 1;
    }

    /// The `u64` words a query needs (`query`).
    pub fn scratchLen(self: *const TermIndex) usize {
        return (self.depth + 2) * self.words;
    }

    /// The items that might meet `goal`, as a set in the first `words` of
    /// `scratch` (`scratchLen` long).
    pub fn query(self: *const TermIndex, terms: *const Terms, goal: ExprId, scratch: []u64) Picks {
        const live = scratch[0..self.words];
        @memset(live, std.math.maxInt(u64));
        if (self.count % 64 != 0) live[live.len - 1] = (@as(u64, 1) << @intCast(self.count % 64)) - 1;
        _ = self.meet(terms, goal, 0, live, scratch[self.words..], null);
        return .{ .live = live };
    }

    fn insertExpr(self: *TermIndex, terms: *const Terms, expr: ExprId, cell: u32, item: usize) !void {
        const token = exprToken(terms, expr) orelse return self.addWild(cell, item);
        try self.addToken(cell, token, item);
        const args = switch (terms.theorem.interner.node(expr).*) {
            .app => |app| app.args,
            else => return,
        };
        for (args, 0..) |arg, position| try self.insertExpr(terms, arg, try self.child(cell, position), item);
    }

    fn insertTemplate(self: *TermIndex, terms: *const Terms, template: TemplateExpr, cell: u32, item: usize) !void {
        const app = switch (template) {
            .binder => return self.addWild(cell, item),
            .app => |app| app,
        };
        if (!terms.isRigid(app.term_id)) return self.addWild(cell, item);
        try self.addToken(cell, app.term_id, item);
        for (app.args, 0..) |arg, position| try self.insertTemplate(terms, arg, try self.child(cell, position), item);
    }

    fn addWild(self: *TermIndex, cell: u32, item: usize) !void {
        if (self.cells.items[cell].wild == none) self.cells.items[cell].wild = try self.newSet();
        self.add(self.cells.items[cell].wild, item);
    }

    fn addToken(self: *TermIndex, cell: u32, token: u64, item: usize) !void {
        var set = self.cells.items[cell].find(token);
        if (set == none) {
            set = try self.newSet();
            try self.cells.items[cell].tokens.append(self.allocator, .{ .token = token, .set = set });
        }
        self.add(set, item);
    }

    fn child(self: *TermIndex, cell: u32, position: usize) !u32 {
        while (self.cells.items[cell].children.items.len <= position) {
            const id: u32 = @intCast(self.cells.items.len);
            const depth = self.cells.items[cell].depth + 1;
            try self.cells.append(self.allocator, .{ .depth = depth });
            try self.cells.items[cell].children.append(self.allocator, id);
            self.depth = @max(self.depth, depth);
        }
        return self.cells.items[cell].children.items[position];
    }

    fn newSet(self: *TermIndex) !u32 {
        const at: u32 = @intCast(self.sets.items.len);
        try self.sets.appendNTimes(self.allocator, 0, self.words);
        return at;
    }

    fn add(self: *TermIndex, set: u32, item: usize) void {
        std.debug.assert(item < self.count);
        self.sets.items[set + item / 64] |= @as(u64, 1) << @intCast(item % 64);
    }

    /// Narrow `live` to the items that might meet `expr` at `cell_id`;
    /// false once none is left. `covers` holds a set per depth, for the
    /// items a wildcard above covers.
    fn meet(
        self: *const TermIndex,
        terms: *const Terms,
        expr: ExprId,
        cell_id: u32,
        live: []u64,
        covers: []u64,
        above: ?[]const u64,
    ) bool {
        const cell = &self.cells.items[cell_id];
        const cover: ?[]const u64 = if (cell.wild == none) above else blk: {
            const out = covers[cell.depth * self.words ..][0..self.words];
            const wild = self.sets.items[cell.wild..][0..self.words];
            for (out, wild, 0..) |*word, bits, n| word.* = bits | if (above) |words| words[n] else 0;
            break :blk out;
        };
        const at = terms.wvars.resolve(expr);
        const token = exprToken(terms, at) orelse return true;
        const set = cell.find(token);
        var left: u64 = 0;
        var rigid: u64 = 0;
        for (live, 0..) |*word, n| {
            const covered = if (cover) |words| words[n] else 0;
            const bits = if (set == none) 0 else self.sets.items[set + n];
            word.* &= bits | covered;
            left |= word.*;
            rigid |= word.* & ~covered;
        }
        // Below, only the items a wildcard does not cover can drop.
        if (rigid == 0) return left != 0;
        const args = switch (terms.theorem.interner.node(at).*) {
            .app => |app| app.args,
            else => return true,
        };
        for (args, 0..) |arg, position| {
            if (position >= cell.children.items.len) break;
            if (!self.meet(terms, arg, cell.children.items[position], live, covers, cover)) return false;
        }
        return true;
    }
};

/// The items of a query's result, lowest first.
pub const Picks = struct {
    live: []const u64,
    word: usize = 0,
    bits: ?u64 = null,

    pub fn next(self: *Picks) ?usize {
        var bits = self.bits orelse (if (self.live.len == 0) return null else self.live[0]);
        while (bits == 0) {
            self.word += 1;
            if (self.word >= self.live.len) {
                self.bits = 0;
                return null;
            }
            bits = self.live[self.word];
        }
        self.bits = bits & (bits - 1);
        return self.word * 64 + @ctz(bits);
    }
};
