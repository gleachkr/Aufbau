const std = @import("std");
const ArenaAllocator = @import("../../arena_allocator.zig").ArenaAllocator;

const clipper = @import("./clipper.zig");
const Env = @import("../../env.zig");
const ExprMod = @import("../../expr.zig");
const Parser = @import("../../parse_recovery.zig");
const RewriteRegistry = @import("../../rewrite_registry.zig").RewriteRegistry;
const TemplateExpr = @import("../../rules.zig").TemplateExpr;
const TrustedExpr = @import("../../../trusted/expressions.zig").Expr;

const ArgInfo = Parser.ArgInfo;
const ExprId = ExprMod.ExprId;
const ExprNode = ExprMod.ExprNode;
const GlobalEnv = Env.GlobalEnv;
const TermDecl = Env.TermDecl;
const TheoremContext = ExprMod.TheoremContext;

pub const Options = struct {
    max_unfold_depth: usize = 4,
    max_nodes: usize = 256,
};

// NOTE: `ref_index.ShapeCache` memoizes `fromTemplateWithBindings` results
// under a key that serializes exactly the theorem-dependent inputs this
// builder reads (node structure; variable kind+index+sort; placeholder sort;
// binder-arg sorts). If a change makes the builder read anything new from the
// theorem, mirror it into `ref_index.zig`'s key serializers or the cache
// silently returns stale shapes.
//
// Every `from*` entry point returns a shape the caller owns and frees with
// `deinitShape`.
pub const Builder = struct {
    allocator: std.mem.Allocator,
    env: *const GlobalEnv,
    registry: ?*const RewriteRegistry = null,
    options: Options = .{},

    pub fn init(
        allocator: std.mem.Allocator,
        env: *const GlobalEnv,
        options: Options,
    ) Builder {
        return .{ .allocator = allocator, .env = env, .options = options };
    }

    pub fn initWithRegistry(
        allocator: std.mem.Allocator,
        env: *const GlobalEnv,
        registry: *const RewriteRegistry,
        options: Options,
    ) Builder {
        return .{
            .allocator = allocator,
            .env = env,
            .registry = registry,
            .options = options,
        };
    }

    pub fn fromTemplate(
        self: *const Builder,
        template: TemplateExpr,
        args: []const ArgInfo,
    ) !clipper.ShapeNode {
        const scope = TemplateScope{ .rule = args };
        return try self.fromTemplateScope(template, &scope);
    }

    pub fn fromTemplateWithBindings(
        self: *const Builder,
        theorem: *const TheoremContext,
        template: TemplateExpr,
        args: []const ArgInfo,
        bindings: []const ?ExprId,
    ) !clipper.ShapeNode {
        const scope = TemplateScope{ .bound_rule = .{
            .args = args,
            .theorem = theorem,
            .bindings = bindings,
        } };
        return try self.fromTemplateScope(template, &scope);
    }

    fn fromTemplateScope(
        self: *const Builder,
        template: TemplateExpr,
        scope: *const TemplateScope,
    ) !clipper.ShapeNode {
        var acui_sorts = try self.acuiSorts();
        defer acui_sorts.deinit(self.allocator);
        var state = State.init(self.options);
        state.acui_sorts = &acui_sorts;
        return try self.templateShape(template, scope, &state);
    }

    pub fn fromExprId(
        self: *const Builder,
        theorem: *const TheoremContext,
        expr_id: ExprId,
    ) !clipper.ShapeNode {
        const scope = ExprScope{ .theorem = theorem };
        var acui_sorts = try self.acuiSorts();
        defer acui_sorts.deinit(self.allocator);
        var state = State.init(self.options);
        state.acui_sorts = &acui_sorts;
        return try self.exprShape(expr_id, &scope, &state);
    }

    pub fn fromSurfaceExpr(
        self: *const Builder,
        expr: *const TrustedExpr,
    ) !clipper.ShapeNode {
        const scope = SurfaceScope{ .root = {} };
        var acui_sorts = try self.acuiSorts();
        defer acui_sorts.deinit(self.allocator);
        var state = State.init(self.options);
        state.acui_sorts = &acui_sorts;
        return try self.surfaceShape(expr, &scope, &state);
    }

    // Build the shape of a single ACUI-region member `wrapper(pattern)` (e.g.
    // `hyp([x/u]p)`) for injection into a recover-source context query. The
    // pattern is shaped concretely except at the recover hole, which is widened
    // to a covering wildcard so it matches whatever witness the real context
    // member carries. Rendered as stored members are, with the wrapper head
    // kept concrete, and with transparent defs in the pattern unfolded so they
    // line up with the index's unfolded ref members. Caller owns the result.
    pub fn recoverMemberShape(
        self: *const Builder,
        theorem: *const TheoremContext,
        wrapper_term_id: u32,
        pattern: ExprId,
        hole: ExprId,
    ) !clipper.ShapeNode {
        var acui_sorts = try self.acuiSorts();
        defer acui_sorts.deinit(self.allocator);

        const wrapper_decl = self.lookupTerm(wrapper_term_id) orelse
            return error.UnknownTerm;
        const wrapper_sort = try sortFromName(self.env, wrapper_decl.ret_sort_name);

        var state = State.init(self.options);
        state.hole = hole;
        state.acui_sorts = &acui_sorts;
        const scope = ExprScope{ .theorem = theorem };
        const inner = try self.exprShape(pattern, &scope, &state);

        const children = self.allocator.alloc(clipper.ShapeNode, 1) catch |err| {
            deinitShape(self.allocator, inner);
            return err;
        };
        children[0] = inner;
        // A member keeps its own head: no region wrap around the wrapper.
        const member = concrete(wrapper_term_id, wrapper_sort, children);
        return member;
    }

    fn templateShape(
        self: *const Builder,
        template: TemplateExpr,
        scope: *const TemplateScope,
        state: *State,
    ) anyerror!clipper.ShapeNode {
        const sort_id = try self.templateSort(template, scope);
        if (state.consumeNode(sort_id)) |fallback| return fallback;

        return switch (template) {
            .binder => |idx| switch (scope.*) {
                .rule => .{ .wildcard = sort_id },
                .bound_rule => |bound| blk: {
                    if (idx < bound.bindings.len) {
                        if (bound.bindings[idx]) |expr_id| {
                            const expr_scope = ExprScope{
                                .theorem = bound.theorem,
                            };
                            break :blk try self.exprShape(
                                expr_id,
                                &expr_scope,
                                state,
                            );
                        }
                    }
                    break :blk .{ .wildcard = sort_id };
                },
                .def_body => |def_scope| blk: {
                    if (idx < def_scope.args.len) {
                        break :blk try self.templateShape(
                            def_scope.args[idx],
                            def_scope.parent,
                            state,
                        );
                    }
                    break :blk .{ .wildcard = sort_id };
                },
            },
            .app => |app| blk: {
                const decl = self.lookupTerm(app.term_id) orelse {
                    return error.UnknownTerm;
                };
                if (!self.isAcuiRoot(app.term_id) and isTransparentDef(decl)) {
                    if (!state.canUnfold()) return .{ .wildcard = sort_id };
                    if (app.args.len == decl.args.len) {
                        state.enterUnfold();
                        defer state.leaveUnfold();
                        const def_scope = TemplateScope{ .def_body = .{
                            .parent = scope,
                            .args = app.args,
                            .dummies = decl.dummy_args,
                        } };
                        break :blk try self.templateShape(
                            decl.body.?,
                            &def_scope,
                            state,
                        );
                    }
                }
                if (self.headIsReducible(app.term_id)) break :blk .{ .wildcard = sort_id };

                const children = try self.allocator.alloc(
                    clipper.ShapeNode,
                    app.args.len,
                );
                errdefer self.allocator.free(children);
                for (app.args, 0..) |arg, idx| {
                    children[idx] = try self.templateShape(
                        arg,
                        scope,
                        state,
                    );
                }
                break :blk try self.finish(state, app.term_id, sort_id, children);
            },
        };
    }

    fn exprShape(
        self: *const Builder,
        expr_id: ExprId,
        scope: *const ExprScope,
        state: *State,
    ) anyerror!clipper.ShapeNode {
        ExprMod.work_ticks_walk +%= 1;
        const node = try scope.node(expr_id);
        const sort_id = try self.nodeSort(expr_id, node, scope);
        return self.exprShapeOf(expr_id, node, sort_id, scope, state);
    }

    /// `exprShape` for a def binder, whose caller already read the sort of
    /// the argument it resolves to.
    fn exprShapeSorted(
        self: *const Builder,
        expr_id: ExprId,
        sort_id: clipper.SortId,
        scope: *const ExprScope,
        state: *State,
    ) anyerror!clipper.ShapeNode {
        ExprMod.work_ticks_walk +%= 1;
        const node = try scope.node(expr_id);
        return self.exprShapeOf(expr_id, node, sort_id, scope, state);
    }

    fn exprShapeOf(
        self: *const Builder,
        expr_id: ExprId,
        node: *const ExprNode,
        sort_id: clipper.SortId,
        scope: *const ExprScope,
        state: *State,
    ) anyerror!clipper.ShapeNode {
        if (state.hole) |h| {
            if (expr_id == h) return .{ .wildcard = sort_id };
        }
        if (state.consumeNode(sort_id)) |fallback| return fallback;

        return switch (node.*) {
            .variable => |var_id| try self.finishLeaf(state, varLeaf(var_id, sort_id)),
            .placeholder => .{ .wildcard = sort_id },
            .app => |app| blk: {
                const decl = self.lookupTerm(app.term_id) orelse {
                    return error.UnknownTerm;
                };
                if (!self.isAcuiRoot(app.term_id) and isTransparentDef(decl)) {
                    if (!state.canUnfold()) return .{ .wildcard = sort_id };
                    if (app.args.len == decl.args.len) {
                        state.enterUnfold();
                        defer state.leaveUnfold();
                        const def_scope = ExprScope{ .def_body = .{
                            .parent = scope,
                            .args = app.args,
                            .dummies = decl.dummy_args,
                        } };
                        break :blk try self.templateExprShape(
                            decl.body.?,
                            &def_scope,
                            state,
                        );
                    }
                }
                if (self.headIsReducible(app.term_id)) break :blk .{ .wildcard = sort_id };

                const children = try self.allocator.alloc(
                    clipper.ShapeNode,
                    app.args.len,
                );
                errdefer self.allocator.free(children);
                for (app.args, 0..) |arg, idx| {
                    children[idx] = try self.exprShape(
                        arg,
                        scope,
                        state,
                    );
                }
                break :blk try self.finish(state, app.term_id, sort_id, children);
            },
        };
    }

    fn templateExprShape(
        self: *const Builder,
        template: TemplateExpr,
        scope: *const ExprScope,
        state: *State,
    ) anyerror!clipper.ShapeNode {
        const sort_id = try self.templateExprSort(template, scope);
        return self.templateExprShapeSorted(template, sort_id, scope, state);
    }

    fn templateExprShapeSorted(
        self: *const Builder,
        template: TemplateExpr,
        sort_id: clipper.SortId,
        scope: *const ExprScope,
        state: *State,
    ) anyerror!clipper.ShapeNode {
        ExprMod.work_ticks_walk +%= 1;
        if (state.consumeNode(sort_id)) |fallback| return fallback;

        return switch (template) {
            .binder => |idx| switch (scope.*) {
                .theorem => .{ .wildcard = sort_id },
                .def_body => |def_scope| blk: {
                    if (idx < def_scope.args.len) {
                        break :blk try self.exprShapeSorted(
                            def_scope.args[idx],
                            sort_id,
                            def_scope.parent,
                            state,
                        );
                    }
                    break :blk .{ .wildcard = sort_id };
                },
            },
            .app => |app| blk: {
                const decl = self.lookupTerm(app.term_id) orelse {
                    return error.UnknownTerm;
                };
                if (!self.isAcuiRoot(app.term_id) and isTransparentDef(decl)) {
                    if (!state.canUnfold()) return .{ .wildcard = sort_id };
                    if (app.args.len == decl.args.len) {
                        state.enterUnfold();
                        defer state.leaveUnfold();
                        const def_scope = TemplateExprViaScope{
                            .outer = .{ .expr = scope },
                            .args = app.args,
                            .dummies = decl.dummy_args,
                        };
                        break :blk try self.templateExprShapeVia(
                            decl.body.?,
                            &def_scope,
                            state,
                        );
                    }
                }
                if (self.headIsReducible(app.term_id)) break :blk .{ .wildcard = sort_id };

                const children = try self.allocator.alloc(
                    clipper.ShapeNode,
                    app.args.len,
                );
                errdefer self.allocator.free(children);
                for (app.args, 0..) |arg, idx| {
                    children[idx] = try self.templateExprShape(
                        arg,
                        scope,
                        state,
                    );
                }
                break :blk try self.finish(state, app.term_id, sort_id, children);
            },
        };
    }

    fn templateExprShapeVia(
        self: *const Builder,
        template: TemplateExpr,
        scope: *const TemplateExprViaScope,
        state: *State,
    ) anyerror!clipper.ShapeNode {
        const sort_id = try self.templateExprSortVia(template, scope);
        return self.templateExprShapeViaSorted(template, sort_id, scope, state);
    }

    fn templateExprShapeViaSorted(
        self: *const Builder,
        template: TemplateExpr,
        sort_id: clipper.SortId,
        scope: *const TemplateExprViaScope,
        state: *State,
    ) anyerror!clipper.ShapeNode {
        ExprMod.work_ticks_walk +%= 1;
        if (state.consumeNode(sort_id)) |fallback| return fallback;

        return switch (template) {
            .binder => |idx| blk: {
                if (idx < scope.args.len) {
                    break :blk switch (scope.outer) {
                        .expr => |e| try self.templateExprShapeSorted(
                            scope.args[idx],
                            sort_id,
                            e,
                            state,
                        ),
                        .via => |v| try self.templateExprShapeViaSorted(
                            scope.args[idx],
                            sort_id,
                            v,
                            state,
                        ),
                    };
                }
                break :blk .{ .wildcard = sort_id };
            },
            .app => |app| blk: {
                const decl = self.lookupTerm(app.term_id) orelse {
                    return error.UnknownTerm;
                };
                if (!self.isAcuiRoot(app.term_id) and isTransparentDef(decl)) {
                    if (!state.canUnfold()) return .{ .wildcard = sort_id };
                    if (app.args.len == decl.args.len) {
                        state.enterUnfold();
                        defer state.leaveUnfold();
                        const nested = TemplateExprViaScope{
                            // The inner def's args live in the *current* via
                            // scope, so chain to it (not to scope.outer).
                            .outer = .{ .via = scope },
                            .args = app.args,
                            .dummies = decl.dummy_args,
                        };
                        break :blk try self.templateExprShapeVia(
                            decl.body.?,
                            &nested,
                            state,
                        );
                    }
                }
                if (self.headIsReducible(app.term_id)) break :blk .{ .wildcard = sort_id };
                const children = try self.allocator.alloc(
                    clipper.ShapeNode,
                    app.args.len,
                );
                errdefer self.allocator.free(children);
                for (app.args, 0..) |arg, idx| {
                    children[idx] = try self.templateExprShapeVia(
                        arg,
                        scope,
                        state,
                    );
                }
                break :blk try self.finish(state, app.term_id, sort_id, children);
            },
        };
    }

    fn surfaceShape(
        self: *const Builder,
        expr: *const TrustedExpr,
        scope: *const SurfaceScope,
        state: *State,
    ) anyerror!clipper.ShapeNode {
        const sort_id: clipper.SortId = expr.sort();
        if (state.consumeNode(sort_id)) |fallback| return fallback;

        return switch (expr.*) {
            .variable => .{ .hole = sort_id },
            .hole => .{ .hole = sort_id },
            .term => |term_app| blk: {
                const decl = self.lookupTerm(term_app.id) orelse {
                    return error.UnknownTerm;
                };
                if (!self.isAcuiRoot(term_app.id) and isTransparentDef(decl)) {
                    if (!state.canUnfold()) return .{ .hole = sort_id };
                    if (term_app.args.len == decl.args.len) {
                        state.enterUnfold();
                        defer state.leaveUnfold();
                        const def_scope = SurfaceScope{ .def_body = .{
                            .args = term_app.args,
                            .dummies = decl.dummy_args,
                        } };
                        break :blk try self.templateSurfaceShape(
                            decl.body.?,
                            &def_scope,
                            state,
                        );
                    }
                }
                if (self.headIsReducible(term_app.id)) break :blk .{ .hole = sort_id };

                const children = try self.allocator.alloc(
                    clipper.ShapeNode,
                    term_app.args.len,
                );
                errdefer self.allocator.free(children);
                for (term_app.args, 0..) |arg, idx| {
                    children[idx] = try self.surfaceShape(
                        arg,
                        scope,
                        state,
                    );
                }
                break :blk try self.finish(state, term_app.id, sort_id, children);
            },
        };
    }

    fn templateSurfaceShape(
        self: *const Builder,
        template: TemplateExpr,
        scope: *const SurfaceScope,
        state: *State,
    ) anyerror!clipper.ShapeNode {
        const sort_id = try self.templateSurfaceSort(template, scope);
        if (state.consumeNode(sort_id)) |fallback| return fallback;

        return switch (template) {
            .binder => |idx| switch (scope.*) {
                .root => .{ .hole = sort_id },
                .def_body => |def_scope| blk: {
                    if (idx < def_scope.args.len) {
                        break :blk try self.surfaceShape(
                            def_scope.args[idx],
                            &SurfaceScope{ .root = {} },
                            state,
                        );
                    }
                    break :blk .{ .hole = sort_id };
                },
            },
            .app => |app| blk: {
                const decl = self.lookupTerm(app.term_id) orelse {
                    return error.UnknownTerm;
                };
                if (!self.isAcuiRoot(app.term_id) and isTransparentDef(decl)) {
                    if (!state.canUnfold()) return .{ .hole = sort_id };
                    if (app.args.len == decl.args.len) {
                        state.enterUnfold();
                        defer state.leaveUnfold();
                        const def_scope = TemplateSurfaceScope{
                            .outer = .{ .surface = scope },
                            .args = app.args,
                            .dummies = decl.dummy_args,
                        };
                        break :blk try self.templateSurfaceShapeVia(
                            decl.body.?,
                            &def_scope,
                            state,
                        );
                    }
                }
                if (self.headIsReducible(app.term_id)) break :blk .{ .hole = sort_id };

                const children = try self.allocator.alloc(
                    clipper.ShapeNode,
                    app.args.len,
                );
                errdefer self.allocator.free(children);
                for (app.args, 0..) |arg, idx| {
                    children[idx] = try self.templateSurfaceShape(
                        arg,
                        scope,
                        state,
                    );
                }
                break :blk try self.finish(state, app.term_id, sort_id, children);
            },
        };
    }

    fn templateSurfaceShapeVia(
        self: *const Builder,
        template: TemplateExpr,
        scope: *const TemplateSurfaceScope,
        state: *State,
    ) anyerror!clipper.ShapeNode {
        const sort_id = try self.templateSurfaceSortVia(template, scope);
        if (state.consumeNode(sort_id)) |fallback| return fallback;

        return switch (template) {
            .binder => |idx| blk: {
                if (idx < scope.args.len) {
                    break :blk switch (scope.outer) {
                        .surface => |outer| try self.templateSurfaceShape(
                            scope.args[idx],
                            outer,
                            state,
                        ),
                        .via => |outer| try self.templateSurfaceShapeVia(
                            scope.args[idx],
                            outer,
                            state,
                        ),
                    };
                }
                break :blk .{ .hole = sort_id };
            },
            .app => |app| blk: {
                const decl = self.lookupTerm(app.term_id) orelse {
                    return error.UnknownTerm;
                };
                if (!self.isAcuiRoot(app.term_id) and isTransparentDef(decl)) {
                    if (!state.canUnfold()) return .{ .hole = sort_id };
                    if (app.args.len == decl.args.len) {
                        state.enterUnfold();
                        defer state.leaveUnfold();
                        const nested = TemplateSurfaceScope{
                            // The inner def's args live in the *current* via
                            // scope, so chain to it (not to scope.outer).
                            .outer = .{ .via = scope },
                            .args = app.args,
                            .dummies = decl.dummy_args,
                        };
                        break :blk try self.templateSurfaceShapeVia(
                            decl.body.?,
                            &nested,
                            state,
                        );
                    }
                }
                if (self.headIsReducible(app.term_id)) break :blk .{ .hole = sort_id };
                const children = try self.allocator.alloc(
                    clipper.ShapeNode,
                    app.args.len,
                );
                errdefer self.allocator.free(children);
                for (app.args, 0..) |arg, idx| {
                    children[idx] = try self.templateSurfaceShapeVia(
                        arg,
                        scope,
                        state,
                    );
                }
                break :blk try self.finish(state, app.term_id, sort_id, children);
            },
        };
    }

    fn templateSort(
        self: *const Builder,
        template: TemplateExpr,
        scope: *const TemplateScope,
    ) anyerror!clipper.SortId {
        return switch (template) {
            .binder => |idx| switch (scope.*) {
                .rule => |args| try sortFromArg(self.env, args[idx]),
                .bound_rule => |bound| try sortFromArg(self.env, bound.args[idx]),
                .def_body => |def_scope| blk: {
                    if (idx < def_scope.args.len) {
                        break :blk try self.templateSort(
                            def_scope.args[idx],
                            def_scope.parent,
                        );
                    }
                    const dummy_idx = idx - def_scope.args.len;
                    break :blk try sortFromArg(
                        self.env,
                        def_scope.dummies[dummy_idx],
                    );
                },
            },
            .app => |app| try self.termSort(app.term_id),
        };
    }

    fn exprSort(
        self: *const Builder,
        expr_id: ExprId,
        scope: *const ExprScope,
    ) anyerror!clipper.SortId {
        return self.nodeSort(expr_id, try scope.node(expr_id), scope);
    }

    fn nodeSort(
        self: *const Builder,
        expr_id: ExprId,
        node: *const ExprNode,
        scope: *const ExprScope,
    ) anyerror!clipper.SortId {
        return switch (node.*) {
            .app => |app| try self.termSort(app.term_id),
            .variable, .placeholder => blk: {
                const sort_name = try scope.leafSortName(expr_id);
                break :blk try sortFromName(self.env, sort_name);
            },
        };
    }

    fn templateExprSort(
        self: *const Builder,
        template: TemplateExpr,
        scope: *const ExprScope,
    ) anyerror!clipper.SortId {
        return switch (template) {
            .binder => |idx| switch (scope.*) {
                .theorem => error.UnknownTemplateBinder,
                .def_body => |def_scope| blk: {
                    if (idx < def_scope.args.len) {
                        break :blk try self.exprSort(
                            def_scope.args[idx],
                            def_scope.parent,
                        );
                    }
                    const dummy_idx = idx - def_scope.args.len;
                    if (dummy_idx >= def_scope.dummies.len) {
                        return error.UnknownTemplateBinder;
                    }
                    break :blk try sortFromArg(
                        self.env,
                        def_scope.dummies[dummy_idx],
                    );
                },
            },
            .app => |app| try self.termSort(app.term_id),
        };
    }

    fn templateExprSortVia(
        self: *const Builder,
        template: TemplateExpr,
        scope: *const TemplateExprViaScope,
    ) anyerror!clipper.SortId {
        return switch (template) {
            .binder => |idx| blk: {
                if (idx < scope.args.len) {
                    break :blk switch (scope.outer) {
                        .expr => |e| try self.templateExprSort(
                            scope.args[idx],
                            e,
                        ),
                        .via => |v| try self.templateExprSortVia(
                            scope.args[idx],
                            v,
                        ),
                    };
                }
                const dummy_idx = idx - scope.args.len;
                if (dummy_idx >= scope.dummies.len) {
                    return error.UnknownTemplateBinder;
                }
                break :blk try sortFromArg(self.env, scope.dummies[dummy_idx]);
            },
            .app => |app| try self.termSort(app.term_id),
        };
    }

    fn templateSurfaceSort(
        self: *const Builder,
        template: TemplateExpr,
        scope: *const SurfaceScope,
    ) anyerror!clipper.SortId {
        return switch (template) {
            .binder => |idx| switch (scope.*) {
                .root => error.UnknownTemplateBinder,
                .def_body => |def_scope| blk: {
                    if (idx < def_scope.args.len) {
                        break :blk def_scope.args[idx].sort();
                    }
                    const dummy_idx = idx - def_scope.args.len;
                    if (dummy_idx >= def_scope.dummies.len) {
                        return error.UnknownTemplateBinder;
                    }
                    break :blk try sortFromArg(
                        self.env,
                        def_scope.dummies[dummy_idx],
                    );
                },
            },
            .app => |app| try self.termSort(app.term_id),
        };
    }

    fn templateSurfaceSortVia(
        self: *const Builder,
        template: TemplateExpr,
        scope: *const TemplateSurfaceScope,
    ) anyerror!clipper.SortId {
        return switch (template) {
            .binder => |idx| blk: {
                if (idx < scope.args.len) {
                    break :blk switch (scope.outer) {
                        .surface => |outer| try self.templateSurfaceSort(
                            scope.args[idx],
                            outer,
                        ),
                        .via => |outer| try self.templateSurfaceSortVia(
                            scope.args[idx],
                            outer,
                        ),
                    };
                }
                const dummy_idx = idx - scope.args.len;
                if (dummy_idx >= scope.dummies.len) {
                    return error.UnknownTemplateBinder;
                }
                break :blk try sortFromArg(self.env, scope.dummies[dummy_idx]);
            },
            .app => |app| try self.termSort(app.term_id),
        };
    }

    fn termSort(self: *const Builder, term_id: u32) anyerror!clipper.SortId {
        const decl = self.lookupTerm(term_id) orelse return error.UnknownTerm;
        if (decl.ret_sort_id) |sort_id| return sort_id;
        return try sortFromName(self.env, decl.ret_sort_name);
    }

    fn lookupTerm(self: *const Builder, term_id: u32) ?*const TermDecl {
        if (!self.env.hasAvailableTerm(term_id)) return null;
        return &self.env.terms.items[term_id];
    }

    fn isAcuiRoot(self: *const Builder, term_id: u32) bool {
        const registry = self.registry orelse return false;
        return registry.acui_by_head.contains(term_id);
    }

    // A term that heads a `@rewrite` rule's LHS can be rewritten away to a
    // *different* head (e.g. `sb_ty`/`sb_tm` substitution: `[x/x]A ~ A`,
    // `[y/x][y/.]B`, … all reduce to whatever `A`/`B` is headed by). Its head
    // therefore carries no reliable shape key: a ref written in reduced form
    // (`Id A x x`) and the rule template that produces it un-reduced
    // (`[y/x][q/refl A x] (Id A y x)`) never line up under a `sb_ty`-keyed
    // index, which silently empties the per-hyp pool — the documented
    // substitution-head gap that view-annotated rules dodge but view-less
    // eliminators (`J_elim`, `nat_ind_*`, `app_elim`) fall into. Widen such a
    // head to a covering wildcard so the index pre-filter only *loosens*
    // (never excludes a valid ref); `tryCandidate`'s real normalized matcher
    // then reconciles the two forms. This mirrors transparent-def unfolding:
    // a head that conversion can change is not a discriminating key.
    // `@congr`/`@alpha` heads (e.g. `suc`, `+` constructors) stay rigid — only
    // `rewrites_by_head` membership reduces a head, per `canonicalizeRewrite`.
    fn headIsReducible(self: *const Builder, term_id: u32) bool {
        const registry = self.registry orelse return false;
        return registry.rewrites_by_head.contains(term_id);
    }

    fn acuiUnitId(self: *const Builder, head_id: u32) ?u32 {
        const registry = self.registry orelse return null;
        const combiner = registry.acui_by_head.get(head_id) orelse return null;
        return self.env.term_names.get(combiner.unit_term_name);
    }

    // Set of result sorts of the declared ACUI combiners. A position of one of
    // these sorts is a (possibly one-member) ACUI region; caller owns the set.
    fn acuiSorts(self: *const Builder) !SortSet {
        var set = SortSet{};
        errdefer set.deinit(self.allocator);
        const registry = self.registry orelse return set;
        var it = registry.acui_by_head.keyIterator();
        while (it.next()) |head_ptr| {
            const decl = self.lookupTerm(head_ptr.*) orelse continue;
            const sort_id = try sortFromName(self.env, decl.ret_sort_name);
            try set.put(self.allocator, sort_id, {});
        }
        return set;
    }

    // Puts a freshly built application into the index's normal form: an
    // ACUI combiner's application becomes the region of its flattened
    // members, and any other term of an ACUI sort a one-member region.
    // `children` are already in normal form; the result owns them.
    fn finish(
        self: *const Builder,
        state: *const State,
        term_id: u32,
        sort_id: clipper.SortId,
        children: []clipper.ShapeNode,
    ) !clipper.ShapeNode {
        const acui_sorts = state.acui_sorts orelse return concrete(term_id, sort_id, children);
        if (self.isAcuiRoot(term_id)) return try self.region(term_id, sort_id, children);
        const body = concrete(term_id, sort_id, children);
        if (!acui_sorts.contains(sort_id)) return body;
        const members = self.allocator.alloc(clipper.ShapeNode, 1) catch |err| {
            deinitShape(self.allocator, body);
            return err;
        };
        members[0] = body;
        return .{ .acui = .{ .sort = sort_id, .members = members } };
    }

    // A variable leaf of an ACUI sort is a one-member region, like any other
    // term of that sort.
    fn finishLeaf(
        self: *const Builder,
        state: *const State,
        leaf: clipper.ShapeNode,
    ) !clipper.ShapeNode {
        const acui_sorts = state.acui_sorts orelse return leaf;
        const node = switch (leaf) {
            .concrete => |node| node,
            else => return leaf,
        };
        if (!acui_sorts.contains(node.sort)) return leaf;
        const members = try self.allocator.alloc(clipper.ShapeNode, 1);
        members[0] = leaf;
        return .{ .acui = .{ .sort = node.sort, .members = members } };
    }

    // The region of combiner `head` applied to `children`. A child region
    // of the same combiner is spliced in, the unit is absorbed, and a
    // one-member wrap is unwrapped, since a member keeps its own head.
    fn region(
        self: *const Builder,
        head: u32,
        sort_id: clipper.SortId,
        children: []clipper.ShapeNode,
    ) !clipper.ShapeNode {
        const unit_id = self.acuiUnitId(head);
        var count: usize = 0;
        for (children) |child| count += regionShare(child, head, unit_id);
        const members = self.allocator.alloc(clipper.ShapeNode, count) catch |err| {
            for (children) |child| deinitShape(self.allocator, child);
            self.allocator.free(children);
            return err;
        };
        var at: usize = 0;
        for (children) |child| {
            switch (child) {
                .acui => |node| {
                    if (node.head == head) {
                        @memcpy(members[at..][0..node.members.len], node.members);
                        at += node.members.len;
                        self.allocator.free(node.members);
                        continue;
                    }
                    if (node.head == null) {
                        const inner = node.members[0];
                        self.allocator.free(node.members);
                        if (isUnitLeaf(inner, unit_id)) {
                            deinitShape(self.allocator, inner);
                            continue;
                        }
                        members[at] = inner;
                        at += 1;
                        continue;
                    }
                },
                .concrete => if (isUnitLeaf(child, unit_id)) {
                    deinitShape(self.allocator, child);
                    continue;
                },
                .wildcard, .hole => {},
            }
            members[at] = child;
            at += 1;
        }
        std.debug.assert(at == count);
        self.allocator.free(children);
        return .{ .acui = .{ .sort = sort_id, .members = members, .head = head } };
    }
};

const SortSet = std.AutoHashMapUnmanaged(clipper.SortId, void);

const TemplateScope = union(enum) {
    rule: []const ArgInfo,
    bound_rule: BoundTemplateScope,
    def_body: TemplateDefScope,
};

const BoundTemplateScope = struct {
    args: []const ArgInfo,
    theorem: *const TheoremContext,
    bindings: []const ?ExprId,
};

const TemplateDefScope = struct {
    parent: *const TemplateScope,
    args: []const TemplateExpr,
    dummies: []const ArgInfo,
};

const ExprScope = union(enum) {
    theorem: *const TheoremContext,
    def_body: ExprDefScope,

    fn node(self: *const ExprScope, expr_id: ExprId) !*const ExprNode {
        return switch (self.*) {
            .theorem => |theorem| theorem.interner.node(expr_id),
            .def_body => |def_scope| def_scope.parent.node(expr_id),
        };
    }

    fn leafSortName(
        self: *const ExprScope,
        expr_id: ExprId,
    ) ![]const u8 {
        return switch (self.*) {
            .theorem => |theorem| blk: {
                const info = try theorem.currentLeafInfo(expr_id);
                break :blk if (info) |leaf| leaf.sort_name else {
                    return error.ExpectedExprLeaf;
                };
            },
            .def_body => |def_scope| def_scope.parent.leafSortName(expr_id),
        };
    }
};

const ExprDefScope = struct {
    parent: *const ExprScope,
    args: []const ExprId,
    dummies: []const ArgInfo,
};

const TemplateExprViaScope = struct {
    // A via scope's args are templates that live in `outer`. When defs nest, the
    // inner def's args live in the enclosing *via* scope, not its ExprScope base
    // — so `outer` must be able to chain to another via scope, otherwise an
    // inner arg referencing an outer def's dummy is resolved one scope level too
    // far out and mis-indexes the dummies.
    outer: TemplateExprViaOuter,
    args: []const TemplateExpr,
    dummies: []const ArgInfo,
};

const TemplateExprViaOuter = union(enum) {
    expr: *const ExprScope,
    via: *const TemplateExprViaScope,
};

const SurfaceScope = union(enum) {
    root,
    def_body: SurfaceDefScope,
};

const SurfaceDefScope = struct {
    args: []const *const TrustedExpr,
    dummies: []const ArgInfo,
};

const TemplateSurfaceScope = struct {
    outer: TemplateSurfaceOuter,
    args: []const TemplateExpr,
    dummies: []const ArgInfo,
};

const TemplateSurfaceOuter = union(enum) {
    surface: *const SurfaceScope,
    via: *const TemplateSurfaceScope,
};

const State = struct {
    nodes_left: usize,
    unfold_left: usize,
    // When set, any `exprShape` of this exact ExprId renders as a covering
    // wildcard. Used to widen a `@recover` hole inside an injected ACUI member
    // query: the pattern `p` is shaped concretely except at the hole `x`, whose
    // occurrences must match the witness the recovered context member carries.
    hole: ?ExprId = null,
    /// The ACUI sorts to normalize regions for while building (see
    /// `Builder.finish`); null builds the plain tree.
    acui_sorts: ?*const SortSet = null,

    fn init(options: Options) State {
        return .{
            .nodes_left = options.max_nodes,
            .unfold_left = options.max_unfold_depth,
        };
    }

    fn consumeNode(self: *State, sort_id: clipper.SortId) ?clipper.ShapeNode {
        if (self.nodes_left == 0) return .{ .wildcard = sort_id };
        self.nodes_left -= 1;
        return null;
    }

    fn canUnfold(self: *const State) bool {
        return self.unfold_left > 0 and self.nodes_left > 0;
    }

    fn enterUnfold(self: *State) void {
        self.unfold_left -= 1;
    }

    fn leaveUnfold(self: *State) void {
        self.unfold_left += 1;
    }
};

/// How many members `child` gives a region of combiner `head`.
fn regionShare(child: clipper.ShapeNode, head: u32, unit_id: ?u32) usize {
    return switch (child) {
        .acui => |node| if (node.head == head)
            node.members.len
        else if (node.head == null and isUnitLeaf(node.members[0], unit_id))
            0
        else
            1,
        .concrete => if (isUnitLeaf(child, unit_id)) 0 else 1,
        .wildcard, .hole => 1,
    };
}

fn isUnitLeaf(shape: clipper.ShapeNode, unit_id: ?u32) bool {
    const unit = unit_id orelse return false;
    return switch (shape) {
        .concrete => |node| node.token.term_id == unit and node.children.len == 0,
        else => false,
    };
}

fn concrete(
    term_id: u32,
    sort_id: clipper.SortId,
    children: []const clipper.ShapeNode,
) clipper.ShapeNode {
    return .{ .concrete = .{
        .token = .{ .term_id = term_id, .arity = @intCast(children.len) },
        .sort = sort_id,
        .children = children,
    } };
}

// Token namespace for ground variable leaves. Inference is one-sided pattern
// matching: a variable appearing in a concrete (user-supplied) line is a ground
// atom, not a unification variable, so both theorem_var and dummy_var
// discriminate in the index exactly like a nullary term would. (Pattern holes
// live only on the template side and are rendered as wildcards by
// `templateShape`.) The two kinds get disjoint sub-namespaces via the high bits;
// real term ids index env term declarations and are always well below 2^30, so
// the namespace is collision-free. Only `placeholder` (a genuine unfilled hole)
// stays a covering wildcard.
const var_token_flag: u32 = 1 << 31;
const var_token_dummy: u32 = 1 << 30;
const var_token_id_limit: u32 = 1 << 30;

fn varLeaf(var_id: ExprMod.VarId, sort_id: clipper.SortId) clipper.ShapeNode {
    const term_id: u32 = switch (var_id) {
        .theorem_var => |id| if (id >= var_token_id_limit)
            return .{ .wildcard = sort_id }
        else
            var_token_flag | id,
        .dummy_var => |id| if (id >= var_token_id_limit)
            return .{ .wildcard = sort_id }
        else
            var_token_flag | var_token_dummy | id,
    };
    return .{ .concrete = .{
        .token = .{ .term_id = term_id, .arity = 0 },
        .sort = sort_id,
        .children = &.{},
    } };
}

fn sortFromArg(env: *const GlobalEnv, info: ArgInfo) anyerror!clipper.SortId {
    return sortFromName(env, info.sort_name);
}

fn sortFromName(env: *const GlobalEnv, sort_name: []const u8) anyerror!clipper.SortId {
    const sort_id = env.sort_names.get(sort_name) orelse return error.UnknownSort;
    return @intCast(sort_id);
}

fn isTransparentDef(term: *const TermDecl) bool {
    return term.available and term.is_def and term.body != null;
}

pub fn deinitShape(allocator: std.mem.Allocator, shape: clipper.ShapeNode) void {
    switch (shape) {
        .concrete => |node| {
            for (node.children) |child| deinitShape(allocator, child);
            allocator.free(node.children);
        },
        .acui => |node| {
            for (node.members) |member| deinitShape(allocator, member);
            allocator.free(node.members);
        },
        .wildcard, .hole => {},
    }
}

fn shapeEql(a: clipper.ShapeNode, b: clipper.ShapeNode) bool {
    return switch (a) {
        .wildcard => |lhs| switch (b) {
            .wildcard => |rhs| lhs == rhs,
            else => false,
        },
        .hole => |lhs| switch (b) {
            .hole => |rhs| lhs == rhs,
            else => false,
        },
        .concrete => |lhs| switch (b) {
            .concrete => |rhs| blk: {
                if (lhs.sort != rhs.sort) break :blk false;
                if (!std.meta.eql(lhs.token, rhs.token)) break :blk false;
                if (lhs.children.len != rhs.children.len) break :blk false;
                for (lhs.children, rhs.children) |l_child, r_child| {
                    if (!shapeEql(l_child, r_child)) break :blk false;
                }
                break :blk true;
            },
            else => false,
        },
        .acui => |lhs| switch (b) {
            .acui => |rhs| blk: {
                if (lhs.sort != rhs.sort) break :blk false;
                if (lhs.members.len != rhs.members.len) break :blk false;
                for (lhs.members, rhs.members) |l_member, r_member| {
                    if (!shapeEql(l_member, r_member)) break :blk false;
                }
                break :blk true;
            },
            else => false,
        },
    };
}

const s_obj: clipper.SortId = 0;
const s_wff: clipper.SortId = 1;
const t_a: u32 = 0;
const t_b: u32 = 1;
const t_p: u32 = 2;
const t_q: u32 = 3;
const t_r: u32 = 4;
const t_wrap: u32 = 5;

fn makeArg(sort_name: []const u8) ArgInfo {
    return .{ .sort_name = sort_name, .bound = false, .deps = 0 };
}

fn testTerm(
    name: []const u8,
    args: []const ArgInfo,
    ret: []const u8,
    body: ?TemplateExpr,
) TermDecl {
    return .{
        .name = name,
        .args = args,
        .arg_names = &.{},
        .dummy_args = &.{},
        .dummy_names = &.{},
        .ret_sort_name = ret,
        .is_def = body != null,
        .body = body,
    };
}

fn populateEnv(env: *GlobalEnv, allocator: std.mem.Allocator) !void {
    try env.sort_names.put("obj", @intCast(s_obj));
    try env.sort_names.put("wff", @intCast(s_wff));

    const obj_args = try allocator.alloc(ArgInfo, 1);
    obj_args[0] = makeArg("obj");
    const wff_args = try allocator.alloc(ArgInfo, 1);
    wff_args[0] = makeArg("wff");

    const q_body_args = try allocator.alloc(TemplateExpr, 1);
    q_body_args[0] = .{ .binder = 0 };
    const q_body = TemplateExpr{ .app = .{
        .term_id = t_p,
        .args = q_body_args,
    } };

    try env.terms.append(allocator, testTerm("a", &.{}, "obj", null));
    try env.terms.append(allocator, testTerm("b", &.{}, "obj", null));
    try env.terms.append(allocator, testTerm("P", obj_args, "wff", null));
    try env.terms.append(allocator, testTerm("Q", obj_args, "wff", q_body));
    try env.terms.append(allocator, testTerm("R", obj_args, "wff", null));
    try env.terms.append(allocator, testTerm("wrap", wff_args, "wff", null));
}

fn appShape(
    term_id: u32,
    sort_id: clipper.SortId,
    children: []const clipper.ShapeNode,
) clipper.ShapeNode {
    return concrete(term_id, sort_id, children);
}

test "shape keeps a pinned binder concrete even when it depends on an unbound bound var" {
    // Models `ex_elim`'s `p: wff x`: a pinned wff binder (`p`, here `P(a)`)
    // whose value carries a free occurrence of an eigenvariable `x`. There is
    // no difference in MM0 between a free and a quantifier-bound variable — they
    // are the same interned `Expr` — so a free occurrence of `x` shapes exactly
    // like the bound occurrence the ref index stores. The shape stays concrete
    // and fully discriminating whether or not `x` is bound; any ambiguity in how
    // a sibling hypothesis pins `p` is resolved upstream in the matcher
    // (`matchOneHypViaView` defers ACUI-split member assignments), not by
    // widening the index pre-filter.
    var arena = ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    var env = GlobalEnv.init(allocator);
    try populateEnv(&env, allocator);

    var theorem = TheoremContext.init(allocator);
    defer theorem.deinit();
    const a_expr = try theorem.interner.internApp(t_a, &.{});
    const body = try theorem.interner.internApp(t_p, &.{a_expr}); // P(a): wff

    // arg 0: bound obj var `x` owning dep bit 0. arg 1: wff `p` depending on x.
    const args = [_]ArgInfo{
        .{ .sort_name = "obj", .bound = true, .deps = 1 << 0 },
        .{ .sort_name = "wff", .bound = false, .deps = 1 << 0 },
    };
    const template = TemplateExpr{ .binder = 1 };
    const builder = Builder.init(allocator, &env, .{});
    const a_children = [_]clipper.ShapeNode{appShape(t_a, s_obj, &.{})};
    const expected = appShape(t_p, s_wff, &a_children);

    // `x` unbound: concrete shape kept (no widening).
    {
        const bindings = [_]?ExprId{ null, body };
        const shape = try builder.fromTemplateWithBindings(
            &theorem,
            template,
            &args,
            &bindings,
        );
        defer deinitShape(allocator, shape);
        try std.testing.expect(shapeEql(expected, shape));
    }

    // `x` bound: same concrete shape.
    {
        const x_val = try theorem.interner.internApp(t_b, &.{});
        const bindings = [_]?ExprId{ x_val, body };
        const shape = try builder.fromTemplateWithBindings(
            &theorem,
            template,
            &args,
            &bindings,
        );
        defer deinitShape(allocator, shape);
        try std.testing.expect(shapeEql(expected, shape));
    }
}

fn expectItems(
    index: *const clipper.Index,
    query_shape: clipper.ShapeNode,
    expected: []const clipper.ItemId,
) !void {
    var bits = try index.query(query_shape);
    defer bits.deinit(index.allocator);
    const actual = try index.collect(&bits);
    defer index.allocator.free(actual);
    try std.testing.expectEqualSlices(clipper.ItemId, expected, actual);
}

test "shape emits theorem templates with binders as wildcards" {
    var arena = ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    var env = GlobalEnv.init(allocator);
    try populateEnv(&env, allocator);

    const builder = Builder.init(allocator, &env, .{});
    const children = try allocator.alloc(TemplateExpr, 1);
    children[0] = .{ .binder = 0 };
    const shape = try builder.fromTemplate(
        .{ .app = .{ .term_id = t_p, .args = children } },
        &[_]ArgInfo{makeArg("obj")},
    );
    defer deinitShape(allocator, shape);

    var index = try clipper.Index.init(allocator);
    defer index.deinit();
    const item = index.addItem();
    try index.insertShape(item, shape);

    const a_children = [_]clipper.ShapeNode{appShape(t_a, s_obj, &.{})};
    try expectItems(&index, appShape(t_p, s_wff, &a_children), &.{item});
}

test "shape emits concrete ExprId trees" {
    var arena = ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    var env = GlobalEnv.init(allocator);
    try populateEnv(&env, allocator);

    var theorem = TheoremContext.init(allocator);
    defer theorem.deinit();
    const a_expr = try theorem.interner.internApp(t_a, &.{});
    const p_expr = try theorem.interner.internApp(t_p, &.{a_expr});

    const builder = Builder.init(allocator, &env, .{});
    const shape = try builder.fromExprId(&theorem, p_expr);
    defer deinitShape(allocator, shape);

    const a_children = [_]clipper.ShapeNode{appShape(t_a, s_obj, &.{})};
    const expected = appShape(t_p, s_wff, &a_children);
    try std.testing.expect(shapeEql(expected, shape));
}

test "shape routes ACUI-rooted regions through the member slot" {
    var arena = ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    var env = GlobalEnv.init(allocator);
    try populateEnv(&env, allocator);
    var registry = RewriteRegistry.init(allocator);
    try registry.acui_by_head.put(t_wrap, .{
        .unit_term_name = "",
        .assoc_name = "",
        .comm_name = null,
        .idem_name = null,
    });

    var theorem = TheoremContext.init(allocator);
    defer theorem.deinit();
    const a_expr = try theorem.interner.internApp(t_a, &.{});
    const p_expr = try theorem.interner.internApp(t_p, &.{a_expr});
    const wrapped_expr = try theorem.interner.internApp(t_wrap, &.{p_expr});

    const builder = Builder.initWithRegistry(allocator, &env, &registry, .{});
    const shape = try builder.fromExprId(&theorem, wrapped_expr);
    defer deinitShape(allocator, shape);

    switch (shape) {
        .acui => |node| {
            try std.testing.expectEqual(s_wff, node.sort);
            try std.testing.expectEqual(@as(usize, 1), node.members.len);
            switch (node.members[0]) {
                .concrete => |member| try std.testing.expectEqual(
                    @as(u32, t_p),
                    member.token.term_id,
                ),
                else => return error.ExpectedConcreteMember,
            }
        },
        else => return error.ExpectedAcuiRegion,
    }
}

test "shape emits holey surface expressions" {
    var arena = ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    var env = GlobalEnv.init(allocator);
    try populateEnv(&env, allocator);

    const hole = try allocator.create(TrustedExpr);
    hole.* = .{ .hole = .{ .sort = @intCast(s_obj), .token = "_" } };
    const p_args = try allocator.alloc(*const TrustedExpr, 1);
    p_args[0] = hole;
    const p_expr = try allocator.create(TrustedExpr);
    p_expr.* = .{ .term = .{
        .sort = @intCast(s_wff),
        .deps = 0,
        .id = t_p,
        .args = p_args,
    } };

    const builder = Builder.init(allocator, &env, .{});
    const shape = try builder.fromSurfaceExpr(p_expr);
    defer deinitShape(allocator, shape);

    var index = try clipper.Index.init(allocator);
    defer index.deinit();
    const item = index.addItem();
    const a_children = [_]clipper.ShapeNode{appShape(t_a, s_obj, &.{})};
    try index.insertShape(item, appShape(t_p, s_wff, &a_children));
    try expectItems(&index, shape, &.{item});
}

test "shape resolves a holey goal's nested definitions in their own scope" {
    // `outer(x) := inner(b, x)` and `inner(v, w) := Q(v)`, where `Q(u) :=
    // P(u)`. Shaping the surface goal `outer(a)` unfolds three definitions;
    // `Q`'s argument is `inner`'s first binder, which is `b` here, not
    // `outer`'s first binder `a`.
    var arena = ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    var env = GlobalEnv.init(allocator);
    try populateEnv(&env, allocator);

    const inner_args = try allocator.alloc(ArgInfo, 2);
    inner_args[0] = makeArg("obj");
    inner_args[1] = makeArg("obj");
    const inner_body_args = try allocator.alloc(TemplateExpr, 1);
    inner_body_args[0] = .{ .binder = 0 };
    try env.terms.append(allocator, testTerm("inner", inner_args, "wff", .{ .app = .{
        .term_id = t_q,
        .args = inner_body_args,
    } }));
    const t_inner: u32 = @intCast(env.terms.items.len - 1);

    const outer_args = try allocator.alloc(ArgInfo, 1);
    outer_args[0] = makeArg("obj");
    const outer_body_args = try allocator.alloc(TemplateExpr, 2);
    outer_body_args[0] = .{ .app = .{ .term_id = t_b, .args = &.{} } };
    outer_body_args[1] = .{ .binder = 0 };
    try env.terms.append(allocator, testTerm("outer", outer_args, "wff", .{ .app = .{
        .term_id = t_inner,
        .args = outer_body_args,
    } }));
    const t_outer: u32 = @intCast(env.terms.items.len - 1);

    const a_expr = try allocator.create(TrustedExpr);
    a_expr.* = .{ .term = .{ .sort = @intCast(s_obj), .deps = 0, .id = t_a, .args = &.{} } };
    const goal_args = try allocator.alloc(*const TrustedExpr, 1);
    goal_args[0] = a_expr;
    const goal = try allocator.create(TrustedExpr);
    goal.* = .{ .term = .{
        .sort = @intCast(s_wff),
        .deps = 0,
        .id = t_outer,
        .args = goal_args,
    } };

    const builder = Builder.init(allocator, &env, .{});
    const shape = try builder.fromSurfaceExpr(goal);
    defer deinitShape(allocator, shape);

    const b_children = [_]clipper.ShapeNode{appShape(t_b, s_obj, &.{})};
    try std.testing.expect(shapeEql(appShape(t_p, s_wff, &b_children), shape));
}

test "shape unfolds transparent definitions instead of all-sort fallback" {
    var arena = ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    var env = GlobalEnv.init(allocator);
    try populateEnv(&env, allocator);

    const q_args = try allocator.alloc(TemplateExpr, 1);
    q_args[0] = .{ .binder = 0 };
    const builder = Builder.init(allocator, &env, .{});
    const shape = try builder.fromTemplate(
        .{ .app = .{ .term_id = t_q, .args = q_args } },
        &[_]ArgInfo{makeArg("obj")},
    );
    defer deinitShape(allocator, shape);

    var index = try clipper.Index.init(allocator);
    defer index.deinit();
    const item = index.addItem();
    try index.insertShape(item, shape);

    const a_children = [_]clipper.ShapeNode{appShape(t_a, s_obj, &.{})};
    try expectItems(&index, appShape(t_p, s_wff, &a_children), &.{item});
    try expectItems(&index, appShape(t_r, s_wff, &a_children), &.{});
}

test "shape budget exhaustion falls back to local wildcards" {
    var arena = ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    var env = GlobalEnv.init(allocator);
    try populateEnv(&env, allocator);

    const q_args = try allocator.alloc(TemplateExpr, 1);
    q_args[0] = .{ .binder = 0 };
    const wrap_args = try allocator.alloc(TemplateExpr, 1);
    wrap_args[0] = .{ .app = .{ .term_id = t_q, .args = q_args } };
    const builder = Builder.init(allocator, &env, .{
        .max_unfold_depth = 0,
    });
    const shape = try builder.fromTemplate(
        .{ .app = .{ .term_id = t_wrap, .args = wrap_args } },
        &[_]ArgInfo{makeArg("obj")},
    );
    defer deinitShape(allocator, shape);

    var index = try clipper.Index.init(allocator);
    defer index.deinit();
    const item = index.addItem();
    try index.insertShape(item, shape);

    const a_children = [_]clipper.ShapeNode{appShape(t_a, s_obj, &.{})};
    const r_children = [_]clipper.ShapeNode{
        appShape(t_r, s_wff, &a_children),
    };
    try expectItems(&index, appShape(t_wrap, s_wff, &r_children), &.{item});
    try expectItems(&index, appShape(t_r, s_wff, &a_children), &.{});
}
