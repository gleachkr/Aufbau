const std = @import("std");
const expr = @import("./expr.zig");
const ExprId = expr.ExprId;
const VarId = expr.VarId;
const PlaceholderId = expr.PlaceholderId;
const TheoremContext = expr.TheoremContext;
const GlobalEnv = @import("./env.zig").GlobalEnv;
const Expr = @import("../trusted/expressions.zig").Expr;
const pretty_print = @import("./pretty_print.zig");

/// Shared `pretty_print` view adapter over the frontend interner. Both the
/// search recipe renderer (`forward.Namer`) and the diagnostic renderer
/// (`view_trace`) read the identical representation — `theorem.interner` nodes
/// plus `env.terms` for term names — and differ only in how a variable or
/// placeholder leaf resolves to a printable name. That single difference is the
/// `Resolver` type parameter, which must expose:
///
///   pub fn variableAtom(self, var_id: VarId) pretty_print.NodeInfo(ExprId)
///   pub fn placeholderAtom(self, pid: PlaceholderId) pretty_print.NodeInfo(ExprId)
///
/// Each returns `.atom` for a resolved name or `.missing` to fail the render
/// (search returns `.missing` for unnamed leaves; diagnostics synthesize an
/// internal coordinate so they never fail).
pub fn View(comptime Resolver: type) type {
    return struct {
        resolver: Resolver,
        theorem: *const TheoremContext,
        env: *const GlobalEnv,

        const Self = @This();
        pub const Node = ExprId;

        pub fn nodeInfo(self: Self, node: ExprId) pretty_print.NodeInfo(ExprId) {
            return switch (self.theorem.interner.node(node).*) {
                .variable => |var_id| self.resolver.variableAtom(var_id),
                .placeholder => |pid| self.resolver.placeholderAtom(pid),
                .app => |app| if (app.term_id >= self.env.terms.items.len)
                    .missing
                else
                    .{ .app = .{
                        .term_id = app.term_id,
                        .args = app.args,
                    } },
            };
        }

        pub fn termName(self: Self, term_id: u32) ?[]const u8 {
            if (term_id >= self.env.terms.items.len) return null;
            return self.env.terms.items[term_id].name;
        }
    };
}

/// Populate `out` with `VarId.hashKey -> source name` by inverting a
/// `name -> *const Expr` binder map (the checker's `NameExprMap`) through the
/// theorem's `parser_vars` (`*const Expr -> VarId`). Entries whose expression
/// is not a recorded variable are skipped. Shared by `forward.Namer` and the
/// diagnostic `DiagNames` so the inversion lives in one place.
pub fn invertNameMap(
    allocator: std.mem.Allocator,
    theorem: *const TheoremContext,
    name_exprs: *const std.StringHashMap(*const Expr),
    out: *std.AutoHashMapUnmanaged(u64, []const u8),
) !void {
    var it = name_exprs.iterator();
    while (it.next()) |entry| {
        const var_id = theorem.parser_vars.get(entry.value_ptr.*) orelse
            continue;
        try out.put(allocator, var_id.hashKey(), entry.key_ptr.*);
    }
}
