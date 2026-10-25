//! `@auto focus` rules: a theory's synchronous rules for focused search.
//!
//! `--| @auto focus $ PRINCIPAL $ : CONT...` names the formula an application
//! decomposes (PRINCIPAL, in the conclusion) and, for each hypothesis in
//! order, the formula that stays in focus there (`$ FORMULA $`), or `_` for a
//! hypothesis that releases focus. Applied at an unfocused goal, a focus rule
//! is a *decide*: one depth level, after which its premises keep the
//! continuations in focus. A focused goal applies only focus rules that
//! decompose the focused formula and premise-free closers, and those steps
//! are depth-free: a chain is bounded by the formula's structure, not the
//! depth budget (`search/generate.zig`, `docs/proof_search.md`).
//!
//! Each formula is read as a *site* in its statement: the path to it from the
//! statement's root, where entering an `@acui` bag picks a member. The search
//! works with sites, not formulas: a hypothesis's continuation is whatever
//! occupies its site in the actual subgoal (for a bag site, the one member the
//! subgoal adds to the goal's bag), since the subgoal may be normalized past
//! the rule's literal premise (`[x/t] p` read as the substituted formula).

const std = @import("std");
const GlobalEnv = @import("./env.zig").GlobalEnv;
const ExprId = @import("./expr.zig").ExprId;
const TheoremContext = @import("./expr.zig").TheoremContext;
const TemplateExpr = @import("./rules.zig").TemplateExpr;
const RewriteRegistry = @import("./rewrite_registry.zig").RewriteRegistry;
const AcuiBag = @import("./acui_bag.zig");
const AssertionStmt = @import("./parse_recovery.zig").AssertionStmt;
const MM0Parser = @import("./parse_recovery.zig").MM0Parser;
const Views = @import("./views.zig");

/// One step from a node to a child: an application argument, or a member of
/// the `@acui` bag the node heads (the combiner's head term).
pub const Step = union(enum) {
    arg: u32,
    member: u32,
};

/// Where a formula sits in a statement.
pub const Site = struct {
    steps: []const Step,

    pub fn eql(a: Site, b: Site) bool {
        if (a.steps.len != b.steps.len) return false;
        for (a.steps, b.steps) |x, y| {
            if (!std.meta.eql(x, y)) return false;
        }
        return true;
    }
};

pub const FocusDecl = struct {
    /// The rule's conclusion head term.
    concl_head: u32,
    /// The decomposed formula, over the rule's binders.
    principal: TemplateExpr,
    principal_site: Site,
    /// One per hypothesis: where the continuation sits, or null when the
    /// hypothesis releases focus.
    continuations: []const ?Site,
};

/// Parse the rule's `@auto focus` annotation, if any, into `registry`. Runs
/// after the registry's own pass (which skips `focus`), since the formulas
/// need the math parser. Focus implies `@auto backward`.
pub fn processFocusAnnotations(
    allocator: std.mem.Allocator,
    parser: *const MM0Parser,
    env: *const GlobalEnv,
    registry: *RewriteRegistry,
    assertion: AssertionStmt,
    annotations: []const []const u8,
) !void {
    const rule_id = env.getRuleId(assertion.name) orelse return;
    for (annotations) |ann| {
        var words = std.mem.tokenizeAny(u8, ann, " \t");
        if (!std.mem.eql(u8, words.next() orelse continue, "@auto")) continue;
        if (!std.mem.eql(u8, words.next() orelse continue, "focus")) continue;
        if (registry.auto_focus_rules.contains(rule_id)) return error.InvalidFocusAnnotation;
        // An eager rule is invertible, a focus rule is not: the two modes
        // ask for opposite treatment of the same step.
        if (registry.eagerPriority(rule_id) != null) return error.FocusRuleIsEager;
        const decl = try parseFocus(
            allocator,
            parser,
            env,
            registry,
            rule_id,
            assertion,
            words.rest(),
        );
        try registry.auto_backward_rules.put(rule_id, {});
        try registry.auto_focus_rules.put(rule_id, decl);
    }
}

const Token = union(enum) {
    math: []const u8,
    colon,
    release,
};

const Tokenizer = struct {
    text: []const u8,
    pos: usize = 0,

    fn next(self: *Tokenizer) !?Token {
        while (self.pos < self.text.len and std.ascii.isWhitespace(self.text[self.pos])) self.pos += 1;
        if (self.pos >= self.text.len) return null;
        const start = self.pos;
        switch (self.text[start]) {
            '$' => {
                const end = std.mem.indexOfScalarPos(u8, self.text, start + 1, '$') orelse
                    return error.InvalidFocusAnnotation;
                self.pos = end + 1;
                return .{ .math = self.text[start + 1 .. end] };
            },
            ':' => {
                self.pos += 1;
                return .colon;
            },
            '_' => {
                self.pos += 1;
                // `_x` is a misspelled name, not a release.
                if (self.pos < self.text.len and self.text[self.pos] != '$' and
                    !std.ascii.isWhitespace(self.text[self.pos]))
                {
                    return error.InvalidFocusAnnotation;
                }
                return .release;
            },
            else => return error.InvalidFocusAnnotation,
        }
    }
};

fn parseFocus(
    allocator: std.mem.Allocator,
    parser: *const MM0Parser,
    env: *const GlobalEnv,
    registry: *const RewriteRegistry,
    rule_id: u32,
    assertion: AssertionStmt,
    text: []const u8,
) !FocusDecl {
    const rule = &env.rules.items[rule_id];
    const concl_head = switch (rule.concl) {
        .app => |app| app.term_id,
        .binder => return error.InvalidFocusAnnotation,
    };
    var tokens = Tokenizer{ .text = std.mem.trimEnd(u8, text, " \t\r\n;") };
    const principal_text = switch (try tokens.next() orelse return error.InvalidFocusAnnotation) {
        .math => |math| math,
        else => return error.InvalidFocusAnnotation,
    };
    const colon = try tokens.next() orelse return error.InvalidFocusAnnotation;
    if (colon != .colon) return error.InvalidFocusAnnotation;
    const principal = try parseFormula(allocator, parser, assertion, principal_text);
    // A bare binder decomposes nothing: the principal names a connective.
    if (principal != .app) return error.InvalidFocusAnnotation;
    const principal_site = try findSite(allocator, env, registry, rule.concl, principal, null);

    const continuations = try allocator.alloc(?Site, rule.hyps.len);
    for (continuations, rule.hyps) |*slot, hyp| {
        slot.* = switch (try tokens.next() orelse return error.InvalidFocusAnnotation) {
            .math => |math| try findSite(
                allocator,
                env,
                registry,
                hyp,
                try parseFormula(allocator, parser, assertion, math),
                rule.concl,
            ),
            .release => null,
            .colon => return error.InvalidFocusAnnotation,
        };
    }
    if (try tokens.next() != null) return error.InvalidFocusAnnotation;
    return .{
        .concl_head = concl_head,
        .principal = principal,
        .principal_site = principal_site,
        .continuations = continuations,
    };
}

fn parseFormula(
    allocator: std.mem.Allocator,
    parser: *const MM0Parser,
    assertion: AssertionStmt,
    math: []const u8,
) !TemplateExpr {
    const expr = Views.parseAnnotationMath(allocator, parser, assertion.arg_names, assertion.arg_exprs, math) catch |err| switch (err) {
        error.OutOfMemory => return error.OutOfMemory,
        else => return error.InvalidFocusAnnotation,
    };
    return TemplateExpr.fromExpr(allocator, expr, assertion.arg_exprs) catch
        error.InvalidFocusAnnotation;
}

/// The one site of `formula` in `statement`. For a hypothesis (`concl` set),
/// occurrences inside a bag member the conclusion's bag at the same place
/// also holds are not new, so they do not count.
fn findSite(
    allocator: std.mem.Allocator,
    env: *const GlobalEnv,
    registry: *const RewriteRegistry,
    statement: TemplateExpr,
    formula: TemplateExpr,
    concl: ?TemplateExpr,
) !Site {
    var search = SiteSearch{
        .allocator = allocator,
        .env = env,
        .registry = registry,
        .formula = formula,
        .concl = concl,
    };
    defer search.path.deinit(allocator);
    try search.visit(statement);
    if (search.found == 0) return error.FocusFormulaNotFound;
    if (search.found > 1) return error.FocusFormulaAmbiguous;
    return search.site.?;
}

const SiteSearch = struct {
    allocator: std.mem.Allocator,
    env: *const GlobalEnv,
    registry: *const RewriteRegistry,
    formula: TemplateExpr,
    concl: ?TemplateExpr,
    path: std.ArrayListUnmanaged(Step) = .empty,
    found: usize = 0,
    site: ?Site = null,

    fn visit(self: *SiteSearch, node: TemplateExpr) error{OutOfMemory}!void {
        if (node.eql(self.formula)) {
            self.found += 1;
            if (self.site == null) self.site = .{ .steps = try self.allocator.dupe(Step, self.path.items) };
            return;
        }
        const app = switch (node) {
            .app => |app| app,
            .binder => return,
        };
        if (AcuiBag.Combiner.of(self.registry, self.env, app.term_id)) |combiner| {
            // Below a bag member a nested bag has no counterpart in the goal
            // (`formulaAt` could only read a one-member one), so no site
            // lies inside it.
            for (self.path.items) |step| if (step == .member) return;
            var members: std.ArrayListUnmanaged(TemplateExpr) = .empty;
            defer members.deinit(self.allocator);
            try combiner.spine().collectTemplate(self.allocator, node, &members);
            var old: std.ArrayListUnmanaged(TemplateExpr) = .empty;
            defer old.deinit(self.allocator);
            if (self.concl) |concl| if (self.nodeAt(concl)) |bag| {
                try combiner.spine().collectTemplate(self.allocator, bag, &old);
            };
            for (members.items) |member| {
                if (holdsMember(old.items, member)) continue;
                try self.path.append(self.allocator, .{ .member = app.term_id });
                defer self.path.items.len -= 1;
                try self.visit(member);
            }
            return;
        }
        for (app.args, 0..) |arg, idx| {
            try self.path.append(self.allocator, .{ .arg = @intCast(idx) });
            defer self.path.items.len -= 1;
            try self.visit(arg);
        }
    }

    /// The conclusion's node at the current path, where the hypothesis's bag
    /// is. Null once the path has entered a bag member: below that the new
    /// member has no counterpart in the conclusion.
    fn nodeAt(self: *const SiteSearch, concl: TemplateExpr) ?TemplateExpr {
        var node = concl;
        for (self.path.items) |step| {
            node = switch (step) {
                .arg => |idx| switch (node) {
                    .app => |app| if (idx < app.args.len) app.args[idx] else return null,
                    .binder => return null,
                },
                .member => return null,
            };
        }
        return node;
    }
};

fn holdsMember(members: []const TemplateExpr, member: TemplateExpr) bool {
    for (members) |other| {
        if (other.eql(member)) return true;
    }
    return false;
}

/// Whether `expr` has the shape of `template`. A binder matches anything when
/// `bindings` is null or leaves it unbound; a bound binder matches its value.
/// A placeholder on either side matches anything: an open goal's metas may
/// still become the formula.
pub fn matchesTemplate(
    theorem: *const TheoremContext,
    template: TemplateExpr,
    bindings: ?[]const ?ExprId,
    expr: ExprId,
) bool {
    switch (template) {
        .binder => |idx| {
            const values = bindings orelse return true;
            const value = (if (idx < values.len) values[idx] else null) orelse return true;
            return value == expr or theorem.containsPlaceholder(value) or theorem.containsPlaceholder(expr);
        },
        .app => |app| return switch (theorem.interner.node(expr).*) {
            .placeholder => true,
            .variable => false,
            .app => |node| node.term_id == app.term_id and node.args.len == app.args.len and
                for (app.args, node.args) |arg, child| {
                    if (!matchesTemplate(theorem, arg, bindings, child)) break false;
                } else true,
        },
    }
}

/// The formula at `site` in the subgoal `child` of the goal `parent`: at a bag
/// step, the one member `child`'s bag adds to `parent`'s bag at the same
/// place. Null when the shapes do not follow the site or the bag gained no
/// member, or several.
pub fn formulaAt(
    env: *const GlobalEnv,
    registry: *const RewriteRegistry,
    theorem: *const TheoremContext,
    site: Site,
    parent: ExprId,
    child: ExprId,
) ?ExprId {
    var old: ?ExprId = parent;
    var node = child;
    for (site.steps) |step| switch (step) {
        .arg => |idx| {
            node = argAt(theorem, node, idx) orelse return null;
            if (old) |o| old = argAt(theorem, o, idx) orelse return null;
        },
        .member => |head| {
            const combiner = AcuiBag.Combiner.of(registry, env, head) orelse return null;
            const members = combiner.flatten(theorem, node) orelse return null;
            // Below a bag step the parent has no counterpart: every member
            // of a nested bag is new.
            const old_members = if (old) |o| combiner.flatten(theorem, o) orelse return null else AcuiBag.ExprBag{};
            var new: ?ExprId = null;
            for (members.slice()) |member| {
                if (std.mem.indexOfScalar(ExprId, old_members.slice(), member) != null) continue;
                if (new != null and new.? != member) return null;
                new = member;
            }
            node = new orelse return null;
            old = null;
        },
    };
    return node;
}

fn argAt(theorem: *const TheoremContext, expr: ExprId, idx: u32) ?ExprId {
    return switch (theorem.interner.node(expr).*) {
        .app => |app| if (idx < app.args.len) app.args[idx] else null,
        .variable, .placeholder => null,
    };
}

/// Whether some focus rule could decompose `formula` sitting at `site` in a
/// goal `goal`: its conclusion has `goal`'s head, its principal the same
/// site and `formula`'s shape. When none can, the focus is released.
pub fn decomposable(
    registry: *const RewriteRegistry,
    theorem: *const TheoremContext,
    goal: ExprId,
    site: Site,
    formula: ExprId,
) bool {
    const head = switch (theorem.interner.node(goal).*) {
        .app => |app| app.term_id,
        .variable, .placeholder => return false,
    };
    // An open goal's meta could become any formula: nothing to decompose yet.
    if (theorem.interner.node(formula).* != .app) return false;
    var it = registry.auto_focus_rules.valueIterator();
    while (it.next()) |decl| {
        if (decl.concl_head == head and decl.principal_site.eql(site) and
            matchesTemplate(theorem, decl.principal, null, formula))
        {
            return true;
        }
    }
    return false;
}
