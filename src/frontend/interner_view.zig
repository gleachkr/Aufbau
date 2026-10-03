const std = @import("std");
const expr = @import("./expr.zig");
const ExprId = expr.ExprId;
const VarId = expr.VarId;
const PlaceholderId = expr.PlaceholderId;
const TheoremContext = expr.TheoremContext;
const GlobalEnv = @import("./env.zig").GlobalEnv;
const Expr = @import("../trusted/expressions.zig").Expr;
const pretty_print = @import("./pretty_print.zig");

/// How a variable or placeholder leaf prints. Real variables print under
/// their source name; what happens to a leaf without one is the caller's
/// choice.
pub const Names = struct {
    /// Encoded VarId -> source name.
    vars: *const std.AutoHashMapUnmanaged(u64, []const u8),
    /// Names chosen for placeholders (the search's stand-ins), if any.
    placeholders: ?*const std.AutoHashMapUnmanaged(PlaceholderId, []const u8) = null,
    /// Where to write an internal coordinate (`v#`, `.d#`, `.p#`) for a leaf
    /// without a name, so the render never fails (diagnostics). Null fails
    /// the render instead, for text that must parse back. The printer copies
    /// each atom before asking for the next, so one buffer serves them all.
    coord_buf: ?*[24]u8 = null,

    fn variableAtom(self: Names, var_id: VarId) pretty_print.NodeInfo(ExprId) {
        if (self.vars.get(var_id.hashKey())) |name| return .{ .atom = name };
        const buf = self.coord_buf orelse return .missing;
        return .{ .atom = switch (var_id) {
            .theorem_var => |idx| std.fmt.bufPrint(buf, "v{d}", .{idx}),
            .dummy_var => |idx| std.fmt.bufPrint(buf, ".d{d}", .{idx}),
        } catch unreachable };
    }

    fn placeholderAtom(self: Names, pid: PlaceholderId) pretty_print.NodeInfo(ExprId) {
        if (self.placeholders) |chosen| {
            if (chosen.get(pid)) |name| return .{ .atom = name };
        }
        const buf = self.coord_buf orelse return .missing;
        return .{ .atom = std.fmt.bufPrint(buf, ".p{d}", .{pid}) catch unreachable };
    }
};

/// `pretty_print` view over the frontend interner: `theorem.interner` nodes,
/// `env.terms` for term names, and `names` for the leaves. Shared by the
/// search's recipe renderer (`forward.Namer`) and the diagnostic and source
/// renderers (`view_trace`).
pub const View = struct {
    names: Names,
    theorem: *const TheoremContext,
    env: *const GlobalEnv,

    pub const Node = ExprId;

    pub fn nodeInfo(self: View, node: ExprId) pretty_print.NodeInfo(ExprId) {
        return switch (self.theorem.interner.node(node).*) {
            .variable => |var_id| self.names.variableAtom(var_id),
            .placeholder => |pid| self.names.placeholderAtom(pid),
            .app => |app| if (app.term_id >= self.env.terms.items.len)
                .missing
            else
                .{ .app = .{
                    .term_id = app.term_id,
                    .args = app.args,
                } },
        };
    }

    pub fn termName(self: View, term_id: u32) ?[]const u8 {
        if (term_id >= self.env.terms.items.len) return null;
        return self.env.terms.items[term_id].name;
    }
};

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
