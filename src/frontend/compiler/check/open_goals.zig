//! Open goals: `by ?` on a line, `[?]` in a reference slot. An open goal is
//! a step still to be proved. Analysis admits it, with the statement its
//! position gives it, and reports that goal; a compile refuses it, since
//! there is nothing to emit.

const std = @import("std");
const ExprId = @import("../../expr.zig").ExprId;
const TheoremContext = @import("../../expr.zig").TheoremContext;
const GlobalEnv = @import("../../env.zig").GlobalEnv;
const MM0Parser = @import("../../parse_recovery.zig").MM0Parser;
const ProofScript = @import("../../proof_script.zig");
const RuleApplication = ProofScript.RuleApplication;
const CompilerDiag = @import("../../diag.zig");
const CompilerContext = @import("../context.zig").CompilerContext;
const ViewTrace = @import("../../view_trace.zig");
const interner_view = @import("../../interner_view.zig");
const pretty_print = @import("../../pretty_print.zig");
const PlaceholderId = @import("../../expr.zig").PlaceholderId;
const NameExprMap = @import("./types.zig").NameExprMap;

/// Whether this run admits open goals: every analysis does (the editor,
/// `abc search`, the analysis behind a failed compile). A plain compile
/// stops at the first one.
pub fn admitted(self: *const CompilerContext) bool {
    return self.allow_search_placeholders or self.keep_checking != null;
}

/// The diagnostic for the open goal `marker`. `goal` is its statement in
/// source notation, or null when the line does not determine it.
pub fn diagnostic(
    theorem_name: []const u8,
    line_label: []const u8,
    marker: RuleApplication,
    goal: ?[]const u8,
) CompilerDiag.Diagnostic {
    return CompilerDiag.withPhase(.{
        .kind = .open_goal,
        .err = error.OpenGoal,
        .source = .proof,
        .theorem_name = theorem_name,
        .line_label = line_label,
        .span = marker.rule_span,
        .detail = .{ .open_goal = .{ .goal = goal } },
    }, .theorem_application);
}

/// What a line's check learned about one of its open goals: the goal of
/// the `?` at proof offset `at` (its `rule_span.start`), or null when the
/// check did not fix it. The text lives as long as the run's allocator.
pub const Record = struct {
    at: usize,
    goal: ?[]const u8,
};

/// The records of the line being checked. A check that is retried or
/// abandoned (a speculative attempt, a binding retry) truncates them back
/// to where it started, so only the kept elaboration's goals remain.
pub const Records = std.ArrayListUnmanaged(Record);

/// Report each open goal in `app` once, in source order, with the goal the
/// line's check recorded for it. Every `?` is reported whether or not the
/// check reached it, so the count is the number of `?` in the source. One
/// with bindings is malformed (`OpenGoalBindings`), not an open goal.
pub fn reportLine(
    self: *CompilerContext,
    theorem_name: []const u8,
    line_label: []const u8,
    app: RuleApplication,
    records: []const Record,
) void {
    if (ProofScript.isOpenGoalRuleName(app.rule_name) and !hasBindings(app)) {
        report(self, diagnostic(
            theorem_name,
            line_label,
            app,
            recordedGoal(records, app.rule_span.start),
        ));
    }
    for (app.refs) |ref| switch (ref) {
        .application => |child| reportLine(self, theorem_name, line_label, child, records),
        .hyp, .line => {},
    };
}

/// The latest record for the `?` at `at`.
fn recordedGoal(records: []const Record, at: usize) ?[]const u8 {
    var idx = records.len;
    while (idx > 0) {
        idx -= 1;
        if (records[idx].at == at) return records[idx].goal;
    }
    return null;
}

/// An editor host (`allow_search_placeholders`) gets a warning, so the goal
/// shows without failing the theorem; the analysis behind a failed compile
/// gets an error per open goal, so the command line lists them all.
fn report(self: *CompilerContext, diag: CompilerDiag.Diagnostic) void {
    if (self.allow_search_placeholders) {
        self.addWarning(diag);
    } else {
        self.addPrimaryDiagnostic(diag);
    }
}

/// `goal` printed the way a proof line would state it, or null when it
/// does not print. A part the position does not fix yet (a placeholder)
/// prints as its sort's hole token, or `_` for a sort without one.
/// Allocated on `allocator`; the diagnostic sink keeps its own copy.
pub fn formatGoal(
    allocator: std.mem.Allocator,
    theorem: *const TheoremContext,
    env: *const GlobalEnv,
    parser: *const MM0Parser,
    theorem_vars: *const NameExprMap,
    goal: ExprId,
) !?[]const u8 {
    return try render(allocator, theorem, env, parser, theorem_vars, goal, "_", null);
}

/// `formatGoal`, with each placeholder in `named` printed as its name.
pub fn formatGoalNamed(
    allocator: std.mem.Allocator,
    theorem: *const TheoremContext,
    env: *const GlobalEnv,
    parser: *const MM0Parser,
    theorem_vars: *const NameExprMap,
    goal: ExprId,
    named: *const std.AutoHashMapUnmanaged(PlaceholderId, []const u8),
) !?[]const u8 {
    return try render(allocator, theorem, env, parser, theorem_vars, goal, "_", named);
}

/// `goal` as source text to write into a proof, or null when it cannot be
/// written: a hole whose sort has no `@hole` token, or notation that does
/// not render.
pub fn formatStatement(
    allocator: std.mem.Allocator,
    theorem: *const TheoremContext,
    env: *const GlobalEnv,
    parser: *const MM0Parser,
    theorem_vars: *const NameExprMap,
    goal: ExprId,
) !?[]const u8 {
    return try render(allocator, theorem, env, parser, theorem_vars, goal, null, null);
}

/// `goal` in source notation, each hole named by its sort's hole token, or
/// by `fallback` when the sort has none. Null when a hole has no name.
fn render(
    allocator: std.mem.Allocator,
    theorem: *const TheoremContext,
    env: *const GlobalEnv,
    parser: *const MM0Parser,
    theorem_vars: *const NameExprMap,
    goal: ExprId,
    fallback: ?[]const u8,
    named: ?*const std.AutoHashMapUnmanaged(PlaceholderId, []const u8),
) !?[]const u8 {
    var names = try ViewTrace.DiagNames.build(
        allocator,
        theorem,
        parser,
        theorem_vars,
    );
    defer names.deinit(allocator);
    var holes: std.AutoHashMapUnmanaged(PlaceholderId, []const u8) = .empty;
    defer holes.deinit(allocator);
    if (named) |preset| {
        var it = preset.iterator();
        while (it.next()) |entry| try holes.put(allocator, entry.key_ptr.*, entry.value_ptr.*);
    }
    if (!try nameHoles(allocator, theorem, parser, goal, fallback, &holes)) return null;
    const view: interner_view.View = .{
        .names = .{ .vars = &names.map, .placeholders = &holes },
        .theorem = theorem,
        .env = env,
    };
    return try pretty_print.render(allocator, parser, view, goal, .{ .overflow = .fail });
}

/// Each placeholder under `root`, named by its sort's hole token or
/// `fallback`. False when some placeholder gets no name.
fn nameHoles(
    allocator: std.mem.Allocator,
    theorem: *const TheoremContext,
    parser: *const MM0Parser,
    root: ExprId,
    fallback: ?[]const u8,
    holes: *std.AutoHashMapUnmanaged(PlaceholderId, []const u8),
) !bool {
    switch (theorem.interner.node(root).*) {
        .variable => {},
        .placeholder => |pid| {
            if (holes.contains(pid)) return true;
            const token = if (theorem.placeholderInfo(pid)) |known|
                parser.core.sort_hole_tokens.get(known.sort_name) orelse fallback
            else
                fallback;
            try holes.put(allocator, pid, token orelse return false);
        },
        .app => |app| for (app.args) |arg| {
            if (!try nameHoles(allocator, theorem, parser, arg, fallback, holes)) return false;
        },
    }
    return true;
}

/// A line justified by `?` must not carry bindings: they name the
/// variables of a rule, and there is none. References are allowed.
pub fn hasBindings(marker: RuleApplication) bool {
    return marker.arg_bindings.len != 0 or marker.search_params.len != 0;
}
