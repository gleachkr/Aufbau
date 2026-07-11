const std = @import("std");
const env_mod = @import("./env.zig");
const rules = @import("./rules.zig");
const pretty_print = @import("./pretty_print.zig");

const GlobalEnv = env_mod.GlobalEnv;
const TemplateExpr = rules.TemplateExpr;

/// Pretty-printed snapshots of every assertion and definition the pipeline
/// registered, captured at end-of-run while the parser (the notation
/// provider) and `GlobalEnv` are still alive. Presentation layers — the wasm
/// meta JSON and the editor's goal display — read the snapshots after the
/// pipeline arena is gone.
///
/// Owned by the `Compiler` facade and threaded through `CompilerContext` as
/// an optional pointer (the `hole_inference_sink` pattern), so paths that
/// don't ask for statements pay nothing.
pub const StatementSink = struct {
    pub const Kind = enum { axiom, theorem, def };

    pub const Statement = struct {
        name: []const u8,
        kind: Kind,
        is_local: bool,
        /// Rendered hypotheses; meaningful only when `concl` is non-null
        /// (assertions render all-or-nothing so a display never mixes
        /// rendered and unrendered formulas).
        hyps: []const []const u8 = &.{},
        concl: ?[]const u8 = null,
        /// Definitions: binder groups and return sort, e.g. `(a: wff): wff`.
        signature: ?[]const u8 = null,
        /// Definitions: the current definiens, when present and renderable.
        body: ?[]const u8 = null,
    };

    arena: std.heap.ArenaAllocator,
    statements: std.ArrayListUnmanaged(Statement) = .{},

    pub fn init(allocator: std.mem.Allocator) StatementSink {
        return .{ .arena = std.heap.ArenaAllocator.init(allocator) };
    }

    pub fn deinit(self: *StatementSink) void {
        self.arena.deinit();
        self.* = undefined;
    }

    pub fn reset(self: *StatementSink) void {
        self.statements = .{};
        _ = self.arena.reset(.retain_capacity);
    }

    pub fn items(self: *const StatementSink) []const Statement {
        return self.statements.items;
    }

    /// Snapshot `env` using `parser`'s notation (any provider exposing
    /// `notationForTerm`/`isCoercionTerm` — the trusted parser or the
    /// recovery wrapper). Never fails the pipeline: on allocation failure
    /// the sink is simply left empty.
    pub fn capture(
        self: *StatementSink,
        parser: anytype,
        env: *const GlobalEnv,
    ) void {
        self.reset();
        self.captureAll(parser, env) catch self.reset();
    }

    fn captureAll(
        self: *StatementSink,
        parser: anytype,
        env: *const GlobalEnv,
    ) !void {
        const allocator = self.arena.allocator();
        for (env.rules.items) |rule| {
            var stmt = Statement{
                .name = try allocator.dupe(u8, rule.name),
                .kind = switch (rule.kind) {
                    .axiom => .axiom,
                    .theorem => .theorem,
                },
                .is_local = rule.is_local,
            };
            const view = TemplateView{ .env = env, .names = rule.arg_names };
            if (try pretty_print.render(allocator, parser, view, rule.concl)) |concl| {
                const hyps = try allocator.alloc([]const u8, rule.hyps.len);
                const all_rendered = for (rule.hyps, 0..) |hyp, idx| {
                    hyps[idx] = try pretty_print.render(
                        allocator,
                        parser,
                        view,
                        hyp,
                    ) orelse break false;
                } else true;
                if (all_rendered) {
                    stmt.concl = concl;
                    stmt.hyps = hyps;
                }
            }
            try self.statements.append(allocator, stmt);
        }
        for (env.terms.items) |term| {
            if (!term.is_def or !term.available) continue;
            var stmt = Statement{
                .name = try allocator.dupe(u8, term.name),
                .kind = .def,
                .is_local = false,
                .signature = try renderTermSignature(allocator, term),
            };
            if (term.body) |body| {
                // Body templates index args first, then hidden dummies
                // (`GlobalEnv.buildTermDecl`).
                const view = TemplateView{
                    .env = env,
                    .names = term.arg_names,
                    .extra_names = term.dummy_names,
                };
                stmt.body = try pretty_print.render(allocator, parser, view, body);
            }
            try self.statements.append(allocator, stmt);
        }
    }
};

/// `pretty_print` view adapter over the binder-indexed `TemplateExpr` shapes
/// that `GlobalEnv` retains for every rule and definition. Binder leaves
/// resolve through the declaration's recorded names; an anonymous binder
/// fails the render (the caller keeps its source-verbatim fallback).
const TemplateView = struct {
    env: *const GlobalEnv,
    names: []const ?[]const u8,
    /// Names for binder indices past `names.len` (a def body's hidden
    /// dummies, appended after the visible args).
    extra_names: []const ?[]const u8 = &.{},

    pub const Node = TemplateExpr;

    pub fn nodeInfo(
        self: TemplateView,
        node: TemplateExpr,
    ) pretty_print.NodeInfo(TemplateExpr) {
        switch (node) {
            .binder => |idx| {
                const name = if (idx < self.names.len)
                    self.names[idx]
                else if (idx - self.names.len < self.extra_names.len)
                    self.extra_names[idx - self.names.len]
                else
                    null;
                return if (name) |n| .{ .atom = n } else .missing;
            },
            .app => |app| {
                if (!self.env.hasAvailableTerm(app.term_id)) return .missing;
                return .{ .app = .{ .term_id = app.term_id, .args = app.args } };
            },
        }
    }

    pub fn termName(self: TemplateView, term_id: u32) ?[]const u8 {
        if (!self.env.hasAvailableTerm(term_id)) return null;
        return self.env.terms.items[term_id].name;
    }
};

/// `(a: wff) {x: obj}: wff` — the visible binder groups and return sort of a
/// definition. Hidden dummies are deliberately absent: they are the def's
/// private business, which is the whole point of body fillers.
fn renderTermSignature(
    allocator: std.mem.Allocator,
    term: env_mod.TermDecl,
) ![]const u8 {
    var out: std.ArrayListUnmanaged(u8) = .{};
    errdefer out.deinit(allocator);
    for (term.args, 0..) |arg, idx| {
        try out.appendSlice(allocator, if (arg.bound) "{" else "(");
        const name = if (idx < term.arg_names.len) term.arg_names[idx] else null;
        try out.appendSlice(allocator, name orelse "_");
        try out.appendSlice(allocator, ": ");
        try out.appendSlice(allocator, arg.sort_name);
        try out.appendSlice(allocator, if (arg.bound) "} " else ") ");
    }
    if (term.args.len != 0) _ = out.pop(); // drop the trailing group space
    try out.appendSlice(allocator, ": ");
    try out.appendSlice(allocator, term.ret_sort_name);
    return try out.toOwnedSlice(allocator);
}
