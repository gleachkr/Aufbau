const std = @import("std");
const ExprModule = @import("../expr.zig");
const ExprId = @import("../expr.zig").ExprId;
const types = @import("./types.zig");
const StructuralProfile = types.StructuralProfile;

pub fn collectItems(
    self: anytype,
    expr_id: ExprId,
    profile: StructuralProfile,
    out: *std.ArrayListUnmanaged(ExprId),
) anyerror!void {
    ExprModule.work_ticks_walk +%= 1;
    const node = self.theorem.interner.node(expr_id);
    switch (node.*) {
        .variable => try out.append(self.allocator, expr_id),
        .placeholder => try out.append(self.allocator, expr_id),
        .app => |app| {
            if (app.term_id == profile.headTermId() and app.args.len == 2) {
                try collectItems(self, app.args[0], profile, out);
                try collectItems(self, app.args[1], profile, out);
                return;
            }
            if (app.term_id == profile.unitTermId() and app.args.len == 0 and
                profile.combiner.supportsLeftUnit() and
                profile.combiner.supportsRightUnit())
            {
                return;
            }
            try out.append(self.allocator, expr_id);
        },
    }
}
