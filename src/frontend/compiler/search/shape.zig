const std = @import("std");

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
    max_variants: usize = 4,
    include_opaque_def_variant: bool = false,
    acui_normalize: bool = true,
};

pub const ShapeSet = struct {
    allocator: std.mem.Allocator,
    variants: []clipper.ShapeNode,

    pub fn deinit(self: *ShapeSet) void {
        const allocator = self.allocator;
        for (self.variants) |shape| deinitShape(allocator, shape);
        allocator.free(self.variants);
        self.* = .{ .allocator = allocator, .variants = &.{} };
    }
};

// NOTE: `ref_index.ShapeCache` memoizes `fromTemplateWithBindings` results
// under a key that serializes exactly the theorem-dependent inputs this
// builder reads (node structure; variable kind+index+sort; placeholder sort;
// binder-arg sorts). If a change makes the builder read anything new from the
// theorem, mirror it into `ref_index.zig`'s key serializers or the cache
// silently returns stale shapes.
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
    ) !ShapeSet {
        const scope = TemplateScope{ .rule = args };
        return try self.fromTemplateScope(template, &scope);
    }

    pub fn fromTemplateWithBindings(
        self: *const Builder,
        theorem: *const TheoremContext,
        template: TemplateExpr,
        args: []const ArgInfo,
        bindings: []const ?ExprId,
    ) !ShapeSet {
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
    ) !ShapeSet {
        var result = VariantList.init(self.allocator, self.options.max_variants);
        errdefer result.deinit();
        var acui_sorts = try self.acuiSorts();
        defer acui_sorts.deinit(self.allocator);

        if (self.options.include_opaque_def_variant and
            isTransparentDefTemplateRoot(self.env, template))
        {
            var state = State.init(self.options);
            const shape = try self.templateShape(template, scope, &state, false);
            try self.appendNormalized(&result, &acui_sorts, shape);
        }

        var state = State.init(self.options);
        const shape = try self.templateShape(template, scope, &state, true);
        try self.appendNormalized(&result, &acui_sorts, shape);
        return try result.finish();
    }

    pub fn fromExprId(
        self: *const Builder,
        theorem: *const TheoremContext,
        expr_id: ExprId,
    ) !ShapeSet {
        const scope = ExprScope{ .theorem = theorem };
        var result = VariantList.init(self.allocator, self.options.max_variants);
        errdefer result.deinit();
        var acui_sorts = try self.acuiSorts();
        defer acui_sorts.deinit(self.allocator);

        if (self.options.include_opaque_def_variant and
            isTransparentDefExprRoot(self.env, theorem, expr_id))
        {
            var state = State.init(self.options);
            const shape = try self.exprShape(expr_id, &scope, &state, false);
            try self.appendNormalized(&result, &acui_sorts, shape);
        }

        var state = State.init(self.options);
        const shape = try self.exprShape(expr_id, &scope, &state, true);
        try self.appendNormalized(&result, &acui_sorts, shape);
        return try result.finish();
    }

    pub fn fromSurfaceExpr(
        self: *const Builder,
        expr: *const TrustedExpr,
    ) !ShapeSet {
        const scope = SurfaceScope{ .root = {} };
        var result = VariantList.init(self.allocator, self.options.max_variants);
        errdefer result.deinit();
        var acui_sorts = try self.acuiSorts();
        defer acui_sorts.deinit(self.allocator);

        if (self.options.include_opaque_def_variant and
            isTransparentDefSurfaceRoot(self.env, expr))
        {
            var state = State.init(self.options);
            const shape = try self.surfaceShape(expr, &scope, &state, false);
            try self.appendNormalized(&result, &acui_sorts, shape);
        }

        var state = State.init(self.options);
        const shape = try self.surfaceShape(expr, &scope, &state, true);
        try self.appendNormalized(&result, &acui_sorts, shape);
        return try result.finish();
    }

    // Build the shape of a single ACUI-region member `wrapper(pattern)` (e.g.
    // `hyp([x/u]p)`) for injection into a recover-source context query. The
    // pattern is shaped concretely except at the recover hole, which is widened
    // to a covering wildcard so it matches whatever witness the real context
    // member carries. Rendered through `memberBody` (same path as stored
    // members) and with `unfold_defs` so transparent defs in the pattern line
    // up with the index's unfolded ref members. Caller owns the result.
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
        const scope = ExprScope{ .theorem = theorem };
        const inner = try self.exprShape(pattern, &scope, &state, true);

        const children = self.allocator.alloc(clipper.ShapeNode, 1) catch |err| {
            deinitShape(self.allocator, inner);
            return err;
        };
        children[0] = inner;
        const wrapped = concrete(wrapper_term_id, wrapper_sort, children);
        defer deinitShape(self.allocator, wrapped);

        return try self.memberBody(wrapped.concrete, &acui_sorts);
    }

    fn templateShape(
        self: *const Builder,
        template: TemplateExpr,
        scope: *const TemplateScope,
        state: *State,
        unfold_defs: bool,
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
                                unfold_defs,
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
                            unfold_defs,
                        );
                    }
                    break :blk .{ .wildcard = sort_id };
                },
            },
            .app => |app| blk: {
                const decl = self.lookupTerm(app.term_id) orelse {
                    return error.UnknownTerm;
                };
                if (unfold_defs and !self.isAcuiRoot(app.term_id) and isTransparentDef(decl)) {
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
                            unfold_defs,
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
                        unfold_defs,
                    );
                }
                break :blk concrete(app.term_id, sort_id, children);
            },
        };
    }

    fn exprShape(
        self: *const Builder,
        expr_id: ExprId,
        scope: *const ExprScope,
        state: *State,
        unfold_defs: bool,
    ) anyerror!clipper.ShapeNode {
        ExprMod.work_ticks_walk +%= 1;
        const sort_id = try self.exprSort(expr_id, scope);
        if (state.hole) |h| {
            if (expr_id == h) return .{ .wildcard = sort_id };
        }
        if (state.consumeNode(sort_id)) |fallback| return fallback;

        const node = try scope.node(expr_id);
        return switch (node.*) {
            .variable => |var_id| varLeaf(var_id, sort_id),
            .placeholder => .{ .wildcard = sort_id },
            .app => |app| blk: {
                const decl = self.lookupTerm(app.term_id) orelse {
                    return error.UnknownTerm;
                };
                if (unfold_defs and !self.isAcuiRoot(app.term_id) and isTransparentDef(decl)) {
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
                            unfold_defs,
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
                        unfold_defs,
                    );
                }
                break :blk concrete(app.term_id, sort_id, children);
            },
        };
    }

    fn templateExprShape(
        self: *const Builder,
        template: TemplateExpr,
        scope: *const ExprScope,
        state: *State,
        unfold_defs: bool,
    ) anyerror!clipper.ShapeNode {
        ExprMod.work_ticks_walk +%= 1;
        const sort_id = try self.templateExprSort(template, scope);
        if (state.consumeNode(sort_id)) |fallback| return fallback;

        return switch (template) {
            .binder => |idx| switch (scope.*) {
                .theorem => .{ .wildcard = sort_id },
                .def_body => |def_scope| blk: {
                    if (idx < def_scope.args.len) {
                        break :blk try self.exprShape(
                            def_scope.args[idx],
                            def_scope.parent,
                            state,
                            unfold_defs,
                        );
                    }
                    break :blk .{ .wildcard = sort_id };
                },
            },
            .app => |app| blk: {
                const decl = self.lookupTerm(app.term_id) orelse {
                    return error.UnknownTerm;
                };
                if (unfold_defs and !self.isAcuiRoot(app.term_id) and isTransparentDef(decl)) {
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
                            unfold_defs,
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
                        unfold_defs,
                    );
                }
                break :blk concrete(app.term_id, sort_id, children);
            },
        };
    }

    fn templateExprShapeVia(
        self: *const Builder,
        template: TemplateExpr,
        scope: *const TemplateExprViaScope,
        state: *State,
        unfold_defs: bool,
    ) anyerror!clipper.ShapeNode {
        ExprMod.work_ticks_walk +%= 1;
        const sort_id = try self.templateExprSortVia(template, scope);
        if (state.consumeNode(sort_id)) |fallback| return fallback;

        return switch (template) {
            .binder => |idx| blk: {
                if (idx < scope.args.len) {
                    break :blk switch (scope.outer) {
                        .expr => |e| try self.templateExprShape(
                            scope.args[idx],
                            e,
                            state,
                            unfold_defs,
                        ),
                        .via => |v| try self.templateExprShapeVia(
                            scope.args[idx],
                            v,
                            state,
                            unfold_defs,
                        ),
                    };
                }
                break :blk .{ .wildcard = sort_id };
            },
            .app => |app| blk: {
                const decl = self.lookupTerm(app.term_id) orelse {
                    return error.UnknownTerm;
                };
                if (unfold_defs and !self.isAcuiRoot(app.term_id) and isTransparentDef(decl)) {
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
                            unfold_defs,
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
                        unfold_defs,
                    );
                }
                break :blk concrete(app.term_id, sort_id, children);
            },
        };
    }

    fn surfaceShape(
        self: *const Builder,
        expr: *const TrustedExpr,
        scope: *const SurfaceScope,
        state: *State,
        unfold_defs: bool,
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
                if (unfold_defs and !self.isAcuiRoot(term_app.id) and isTransparentDef(decl)) {
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
                            unfold_defs,
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
                        unfold_defs,
                    );
                }
                break :blk concrete(term_app.id, sort_id, children);
            },
        };
    }

    fn templateSurfaceShape(
        self: *const Builder,
        template: TemplateExpr,
        scope: *const SurfaceScope,
        state: *State,
        unfold_defs: bool,
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
                            unfold_defs,
                        );
                    }
                    break :blk .{ .hole = sort_id };
                },
            },
            .app => |app| blk: {
                const decl = self.lookupTerm(app.term_id) orelse {
                    return error.UnknownTerm;
                };
                if (unfold_defs and !self.isAcuiRoot(app.term_id) and isTransparentDef(decl)) {
                    if (!state.canUnfold()) return .{ .hole = sort_id };
                    if (app.args.len == decl.args.len) {
                        state.enterUnfold();
                        defer state.leaveUnfold();
                        const def_scope = TemplateSurfaceScope{
                            .outer = scope,
                            .args = app.args,
                            .dummies = decl.dummy_args,
                        };
                        break :blk try self.templateSurfaceShapeVia(
                            decl.body.?,
                            &def_scope,
                            state,
                            unfold_defs,
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
                        unfold_defs,
                    );
                }
                break :blk concrete(app.term_id, sort_id, children);
            },
        };
    }

    fn templateSurfaceShapeVia(
        self: *const Builder,
        template: TemplateExpr,
        scope: *const TemplateSurfaceScope,
        state: *State,
        unfold_defs: bool,
    ) anyerror!clipper.ShapeNode {
        const sort_id = try self.templateSurfaceSortVia(template, scope);
        if (state.consumeNode(sort_id)) |fallback| return fallback;

        return switch (template) {
            .binder => |idx| blk: {
                if (idx < scope.args.len) {
                    break :blk try self.templateSurfaceShape(
                        scope.args[idx],
                        scope.outer,
                        state,
                        unfold_defs,
                    );
                }
                break :blk .{ .hole = sort_id };
            },
            .app => |app| blk: {
                const decl = self.lookupTerm(app.term_id) orelse {
                    return error.UnknownTerm;
                };
                if (unfold_defs and !self.isAcuiRoot(app.term_id) and isTransparentDef(decl)) {
                    if (!state.canUnfold()) return .{ .hole = sort_id };
                    if (app.args.len == decl.args.len) {
                        state.enterUnfold();
                        defer state.leaveUnfold();
                        const nested = TemplateSurfaceScope{
                            .outer = scope.outer,
                            .args = app.args,
                            .dummies = decl.dummy_args,
                        };
                        break :blk try self.templateSurfaceShapeVia(
                            decl.body.?,
                            &nested,
                            state,
                            unfold_defs,
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
                        unfold_defs,
                    );
                }
                break :blk concrete(app.term_id, sort_id, children);
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
        const node = try scope.node(expr_id);
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
                    break :blk try self.templateSurfaceSort(
                        scope.args[idx],
                        scope.outer,
                    );
                }
                const dummy_idx = idx - scope.args.len;
                break :blk try sortFromArg(self.env, scope.dummies[dummy_idx]);
            },
            .app => |app| try self.termSort(app.term_id),
        };
    }

    fn termSort(self: *const Builder, term_id: u32) anyerror!clipper.SortId {
        const decl = self.lookupTerm(term_id) orelse return error.UnknownTerm;
        return try sortFromName(self.env, decl.ret_sort_name);
    }

    fn lookupTerm(self: *const Builder, term_id: u32) ?*const TermDecl {
        if (!self.env.hasAvailableTerm(term_id)) return null;
        return &self.env.terms.items[term_id];
    }

    fn isAcuiRoot(self: *const Builder, term_id: u32) bool {
        if (!self.options.acui_normalize) return false;
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
        if (!self.options.acui_normalize) return set;
        const registry = self.registry orelse return set;
        var it = registry.acui_by_head.keyIterator();
        while (it.next()) |head_ptr| {
            const decl = self.lookupTerm(head_ptr.*) orelse continue;
            const sort_id = try sortFromName(self.env, decl.ret_sort_name);
            try set.put(self.allocator, sort_id, {});
        }
        return set;
    }

    // Rewrite a freshly built shape tree so ACUI regions route their members
    // through the clipper member slot (see clipper.AcuiNode). Builds a fresh
    // tree; the caller frees the input. `acui_sorts` is empty when there is no
    // registry, so this is a deep copy in that case.
    fn acuiNormalize(
        self: *const Builder,
        shape: clipper.ShapeNode,
        acui_sorts: *const SortSet,
    ) anyerror!clipper.ShapeNode {
        ExprMod.work_ticks_walk +%= 1;
        switch (shape) {
            .wildcard, .hole => return shape, // unknown whole region -> covering
            .acui => |node| {
                const members = try self.allocator.alloc(
                    clipper.ShapeNode,
                    node.members.len,
                );
                var built: usize = 0;
                errdefer {
                    for (members[0..built]) |m| deinitShape(self.allocator, m);
                    self.allocator.free(members);
                }
                for (node.members, 0..) |member, idx| {
                    members[idx] = try self.regionMember(member, acui_sorts);
                    built = idx + 1;
                }
                return .{ .acui = .{ .sort = node.sort, .members = members } };
            },
            .concrete => |node| {
                if (self.isAcuiRoot(node.token.term_id)) {
                    return try self.acuiRegionShape(node, acui_sorts);
                }
                const body = try self.memberBody(node, acui_sorts);
                if (acui_sorts.contains(node.sort)) {
                    // Non-combiner term of an ACUI sort: a one-member region, so
                    // unit absorption against a multi-member region matches.
                    errdefer deinitShape(self.allocator, body);
                    const members = try self.allocator.alloc(clipper.ShapeNode, 1);
                    members[0] = body;
                    return .{ .acui = .{ .sort = node.sort, .members = members } };
                }
                return body;
            },
        }
    }

    // A concrete node rendered with its head kept concrete (no region wrap) and
    // its children normalized. Used for ACUI members and ordinary terms.
    fn memberBody(
        self: *const Builder,
        node: clipper.ConcreteNode,
        acui_sorts: *const SortSet,
    ) anyerror!clipper.ShapeNode {
        const children = try self.allocator.alloc(
            clipper.ShapeNode,
            node.children.len,
        );
        var built: usize = 0;
        errdefer {
            for (children[0..built]) |c| deinitShape(self.allocator, c);
            self.allocator.free(children);
        }
        for (node.children, 0..) |child, idx| {
            children[idx] = try self.acuiNormalize(child, acui_sorts);
            built = idx + 1;
        }
        return .{ .concrete = .{
            .token = node.token,
            .sort = node.sort,
            .children = children,
        } };
    }

    fn acuiRegionShape(
        self: *const Builder,
        node: clipper.ConcreteNode,
        acui_sorts: *const SortSet,
    ) anyerror!clipper.ShapeNode {
        const head_id = node.token.term_id;
        const unit_id = self.acuiUnitId(head_id);
        var members = std.ArrayListUnmanaged(clipper.ShapeNode){};
        errdefer {
            for (members.items) |m| deinitShape(self.allocator, m);
            members.deinit(self.allocator);
        }
        try self.collectRegionMembers(head_id, node, unit_id, &members, acui_sorts);
        const owned = try members.toOwnedSlice(self.allocator);
        return .{ .acui = .{ .sort = node.sort, .members = owned } };
    }

    // Flatten nested applications of `head_id` into member shapes, dropping the
    // (absorbed) unit element. Member position is erased by the slot.
    fn collectRegionMembers(
        self: *const Builder,
        head_id: u32,
        node: clipper.ConcreteNode,
        unit_id: ?u32,
        out: *std.ArrayListUnmanaged(clipper.ShapeNode),
        acui_sorts: *const SortSet,
    ) anyerror!void {
        for (node.children) |child| {
            switch (child) {
                .concrete => |cn| {
                    if (cn.token.term_id == head_id) {
                        try self.collectRegionMembers(
                            head_id,
                            cn,
                            unit_id,
                            out,
                            acui_sorts,
                        );
                        continue;
                    }
                    if (unit_id != null and cn.token.term_id == unit_id.? and
                        cn.children.len == 0)
                    {
                        continue; // unit is absorbed, not a member
                    }
                    const member = try self.regionMember(child, acui_sorts);
                    errdefer deinitShape(self.allocator, member);
                    try out.append(self.allocator, member);
                },
                .wildcard, .hole => try out.append(self.allocator, child),
                .acui => {
                    const member = try self.regionMember(child, acui_sorts);
                    errdefer deinitShape(self.allocator, member);
                    try out.append(self.allocator, member);
                },
            }
        }
    }

    // Render an ACUI member: a nested region for a different ACUI combiner,
    // otherwise the term with its head kept concrete (members are not wrapped).
    fn regionMember(
        self: *const Builder,
        child: clipper.ShapeNode,
        acui_sorts: *const SortSet,
    ) anyerror!clipper.ShapeNode {
        return switch (child) {
            .wildcard, .hole => child,
            .acui => try self.acuiNormalize(child, acui_sorts),
            .concrete => |cn| if (self.isAcuiRoot(cn.token.term_id))
                try self.acuiNormalize(child, acui_sorts)
            else
                try self.memberBody(cn, acui_sorts),
        };
    }

    fn appendNormalized(
        self: *const Builder,
        result: *VariantList,
        acui_sorts: *const SortSet,
        shape: clipper.ShapeNode,
    ) !void {
        const norm = blk: {
            errdefer deinitShape(self.allocator, shape);
            break :blk try self.acuiNormalize(shape, acui_sorts);
        };
        deinitShape(self.allocator, shape);
        errdefer deinitShape(self.allocator, norm);
        try result.appendOwned(norm);
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
    outer: *const SurfaceScope,
    args: []const TemplateExpr,
    dummies: []const ArgInfo,
};

const State = struct {
    nodes_left: usize,
    unfold_left: usize,
    // When set, any `exprShape` of this exact ExprId renders as a covering
    // wildcard. Used to widen a `@recover` hole inside an injected ACUI member
    // query: the pattern `p` is shaped concretely except at the hole `x`, whose
    // occurrences must match the witness the recovered context member carries.
    hole: ?ExprId = null,

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

const VariantList = struct {
    allocator: std.mem.Allocator,
    max_variants: usize,
    variants: std.ArrayListUnmanaged(clipper.ShapeNode) = .{},

    fn init(allocator: std.mem.Allocator, max_variants: usize) VariantList {
        return .{ .allocator = allocator, .max_variants = max_variants };
    }

    fn deinit(self: *VariantList) void {
        for (self.variants.items) |shape| deinitShape(self.allocator, shape);
        self.variants.deinit(self.allocator);
    }

    fn appendOwned(self: *VariantList, shape: clipper.ShapeNode) !void {
        if (self.max_variants == 0) {
            deinitShape(self.allocator, shape);
            return;
        }
        for (self.variants.items) |existing| {
            if (shapeEql(existing, shape)) {
                deinitShape(self.allocator, shape);
                return;
            }
        }
        if (self.variants.items.len >= self.max_variants) {
            deinitShape(self.allocator, shape);
            return;
        }
        try self.variants.append(self.allocator, shape);
    }

    fn finish(self: *VariantList) !ShapeSet {
        if (self.variants.items.len == 0) return error.NoShapeVariants;
        const owned = try self.variants.toOwnedSlice(self.allocator);
        return .{ .allocator = self.allocator, .variants = owned };
    }
};

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

fn isTransparentDefTemplateRoot(
    env: *const GlobalEnv,
    template: TemplateExpr,
) bool {
    return switch (template) {
        .app => |app| if (env.hasAvailableTerm(app.term_id))
            isTransparentDef(&env.terms.items[app.term_id])
        else
            false,
        .binder => false,
    };
}

fn isTransparentDefExprRoot(
    env: *const GlobalEnv,
    theorem: *const TheoremContext,
    expr_id: ExprId,
) bool {
    return switch (theorem.interner.node(expr_id).*) {
        .app => |app| if (env.hasAvailableTerm(app.term_id))
            isTransparentDef(&env.terms.items[app.term_id])
        else
            false,
        else => false,
    };
}

fn isTransparentDefSurfaceRoot(
    env: *const GlobalEnv,
    expr: *const TrustedExpr,
) bool {
    return switch (expr.*) {
        .term => |app| if (env.hasAvailableTerm(app.id))
            isTransparentDef(&env.terms.items[app.id])
        else
            false,
        else => false,
    };
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
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
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
        var shapes = try builder.fromTemplateWithBindings(
            &theorem,
            template,
            &args,
            &bindings,
        );
        defer shapes.deinit();
        try std.testing.expectEqual(@as(usize, 1), shapes.variants.len);
        try std.testing.expect(shapeEql(expected, shapes.variants[0]));
    }

    // `x` bound: same concrete shape.
    {
        const x_val = try theorem.interner.internApp(t_b, &.{});
        const bindings = [_]?ExprId{ x_val, body };
        var shapes = try builder.fromTemplateWithBindings(
            &theorem,
            template,
            &args,
            &bindings,
        );
        defer shapes.deinit();
        try std.testing.expect(shapeEql(expected, shapes.variants[0]));
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
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    var env = GlobalEnv.init(allocator);
    try populateEnv(&env, allocator);

    const builder = Builder.init(allocator, &env, .{});
    const children = try allocator.alloc(TemplateExpr, 1);
    children[0] = .{ .binder = 0 };
    var shapes = try builder.fromTemplate(
        .{ .app = .{ .term_id = t_p, .args = children } },
        &[_]ArgInfo{makeArg("obj")},
    );
    defer shapes.deinit();

    var index = try clipper.Index.init(allocator);
    defer index.deinit();
    const item = index.addItem();
    try index.insertShape(item, shapes.variants[0]);

    const a_children = [_]clipper.ShapeNode{appShape(t_a, s_obj, &.{})};
    try expectItems(&index, appShape(t_p, s_wff, &a_children), &.{item});
}

test "shape emits concrete ExprId trees" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    var env = GlobalEnv.init(allocator);
    try populateEnv(&env, allocator);

    var theorem = TheoremContext.init(allocator);
    defer theorem.deinit();
    const a_expr = try theorem.interner.internApp(t_a, &.{});
    const p_expr = try theorem.interner.internApp(t_p, &.{a_expr});

    const builder = Builder.init(allocator, &env, .{});
    var shapes = try builder.fromExprId(&theorem, p_expr);
    defer shapes.deinit();

    const a_children = [_]clipper.ShapeNode{appShape(t_a, s_obj, &.{})};
    const expected = appShape(t_p, s_wff, &a_children);
    try std.testing.expect(shapeEql(expected, shapes.variants[0]));
}

test "shape routes ACUI-rooted regions through the member slot" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
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
    var shapes = try builder.fromExprId(&theorem, wrapped_expr);
    defer shapes.deinit();

    try std.testing.expectEqual(@as(usize, 1), shapes.variants.len);
    switch (shapes.variants[0]) {
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
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
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
    var shapes = try builder.fromSurfaceExpr(p_expr);
    defer shapes.deinit();

    var index = try clipper.Index.init(allocator);
    defer index.deinit();
    const item = index.addItem();
    const a_children = [_]clipper.ShapeNode{appShape(t_a, s_obj, &.{})};
    try index.insertShape(item, appShape(t_p, s_wff, &a_children));
    try expectItems(&index, shapes.variants[0], &.{item});
}

test "shape unfolds transparent definitions instead of all-sort fallback" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    var env = GlobalEnv.init(allocator);
    try populateEnv(&env, allocator);

    const q_args = try allocator.alloc(TemplateExpr, 1);
    q_args[0] = .{ .binder = 0 };
    const builder = Builder.init(allocator, &env, .{});
    var shapes = try builder.fromTemplate(
        .{ .app = .{ .term_id = t_q, .args = q_args } },
        &[_]ArgInfo{makeArg("obj")},
    );
    defer shapes.deinit();

    var index = try clipper.Index.init(allocator);
    defer index.deinit();
    const item = index.addItem();
    try index.insertShape(item, shapes.variants[0]);

    const a_children = [_]clipper.ShapeNode{appShape(t_a, s_obj, &.{})};
    try expectItems(&index, appShape(t_p, s_wff, &a_children), &.{item});
    try expectItems(&index, appShape(t_r, s_wff, &a_children), &.{});
}

test "shape budget exhaustion falls back to local wildcards" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
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
    var shapes = try builder.fromTemplate(
        .{ .app = .{ .term_id = t_wrap, .args = wrap_args } },
        &[_]ArgInfo{makeArg("obj")},
    );
    defer shapes.deinit();

    var index = try clipper.Index.init(allocator);
    defer index.deinit();
    const item = index.addItem();
    try index.insertShape(item, shapes.variants[0]);

    const a_children = [_]clipper.ShapeNode{appShape(t_a, s_obj, &.{})};
    const r_children = [_]clipper.ShapeNode{
        appShape(t_r, s_wff, &a_children),
    };
    try expectItems(&index, appShape(t_wrap, s_wff, &r_children), &.{item});
    try expectItems(&index, appShape(t_r, s_wff, &a_children), &.{});
}

test "shape variant cap prevents transparent def index blowup" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();
    var env = GlobalEnv.init(allocator);
    try populateEnv(&env, allocator);

    const q_args = try allocator.alloc(TemplateExpr, 1);
    q_args[0] = .{ .binder = 0 };
    const template = TemplateExpr{ .app = .{ .term_id = t_q, .args = q_args } };
    const args = &[_]ArgInfo{makeArg("obj")};

    const capped_builder = Builder.init(allocator, &env, .{
        .include_opaque_def_variant = true,
        .max_variants = 1,
    });
    var capped = try capped_builder.fromTemplate(template, args);
    defer capped.deinit();
    try std.testing.expectEqual(@as(usize, 1), capped.variants.len);

    const uncapped_builder = Builder.init(allocator, &env, .{
        .include_opaque_def_variant = true,
        .max_variants = 2,
    });
    var uncapped = try uncapped_builder.fromTemplate(template, args);
    defer uncapped.deinit();
    try std.testing.expectEqual(@as(usize, 2), uncapped.variants.len);
}
