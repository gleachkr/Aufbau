const std = @import("std");
const TermDecl = @import("../../env.zig").TermDecl;
const ExprId = @import("../../expr.zig").ExprId;
const AcuiCacheKey = @import("../../expr.zig").AcuiCacheKey;
const DefCacheKey = @import("../../expr.zig").DefCacheKey;
const ExprApp = @import("../../expr.zig").ExprNode.App;
const TemplateExpr = @import("../../rules.zig").TemplateExpr;
const AcuiSupport = @import("../../acui_support.zig");
const SharedContextMod = @import("../shared_context.zig");
const Types = @import("../types.zig");
const MatchState = @import("../match_state.zig");
const WitnessState = @import("./witness_state.zig");

const ConversionPlan = Types.ConversionPlan;
const SymbolicExpr = Types.SymbolicExpr;
const BindingMode = Types.BindingMode;
const MatchSession = MatchState.MatchSession;
const semantic_match_budget: usize = 8;

fn assertCacheIdentity(self: anytype) void {
    const registry_addr: usize = if (self.shared.registry) |registry|
        @intFromPtr(registry)
    else
        0;
    self.shared.theorem.assertDefOpsCacheIdentity(
        @intFromPtr(self.shared.env),
        registry_addr,
    );
}

pub fn defCoversItem(
    self: anytype,
    def_expr: ExprId,
    item_expr: ExprId,
) anyerror!bool {
    return (try planDefCoversItem(self, def_expr, item_expr)) != null;
}

pub fn planDefCoversItem(
    self: anytype,
    def_expr: ExprId,
    item_expr: ExprId,
) anyerror!?*const ConversionPlan {
    return try planDefToTarget(self, def_expr, item_expr, .lhs);
}

pub fn instantiateDefTowardAcuiItem(
    self: anytype,
    def_expr: ExprId,
    item_expr: ExprId,
    head_term_id: u32,
) anyerror!?ExprId {
    // Pure in (def_expr, item_expr, head_term_id) under the fixed env/registry
    // invariant asserted here. This uses a fresh session per call, and
    // transient def_ops contexts re-issue it for every ACUI leaf-pair.
    assertCacheIdentity(self);
    const key = AcuiCacheKey{
        .def_expr = def_expr,
        .item_expr = item_expr,
        .head_term_id = head_term_id,
        .has_registry = self.shared.registry != null,
    };
    if (self.shared.theorem.instantiate_acui_cache.get(key)) |cached| {
        return cached;
    }
    const result = try instantiateDefTowardAcuiItemUncached(
        self,
        def_expr,
        item_expr,
        head_term_id,
    );
    try self.shared.theorem.instantiate_acui_cache.put(
        self.shared.theorem.allocator,
        key,
        result,
    );
    return result;
}

fn instantiateDefTowardAcuiItemUncached(
    self: anytype,
    def_expr: ExprId,
    item_expr: ExprId,
    head_term_id: u32,
) anyerror!?ExprId {
    _ = getConcreteDef(self, def_expr) orelse return null;
    var session = try MatchSession.init(self.shared.allocator, 0);
    defer session.deinit(self.shared.allocator);
    const symbolic = try expandConcreteDef(
        self,
        def_expr,
        &session,
    ) orelse return null;

    if (!try matchSymbolicAcuiLeafToExprState(
        self,
        symbolic,
        item_expr,
        head_term_id,
        &session,
    ) and !try self.matchSymbolicAcuiLeafToExprSemantic(
        symbolic,
        item_expr,
        head_term_id,
        &session,
        semantic_match_budget,
    )) {
        return null;
    }
    return try WitnessState.materializeFinalSymbolic(
        self,
        symbolic,
        &session,
    );
}

pub fn planDefToTarget(
    self: anytype,
    def_expr: ExprId,
    target_expr: ExprId,
    side: enum { lhs, rhs },
) anyerror!?*const ConversionPlan {
    const witness = try instantiateDefTowardExpr(self, def_expr, target_expr) orelse {
        return null;
    };
    const next = switch (side) {
        .lhs => try compareTransparent(self, witness, target_expr),
        .rhs => try compareTransparent(self, target_expr, witness),
    } orelse {
        return null;
    };
    return switch (side) {
        .lhs => try allocPlan(self, .{ .unfold_lhs = .{
            .witness = witness,
            .next = next,
        } }),
        .rhs => try allocPlan(self, .{ .unfold_rhs = .{
            .witness = witness,
            .next = next,
        } }),
    };
}

pub fn compareTransparent(
    self: anytype,
    lhs: ExprId,
    rhs: ExprId,
) anyerror!?*const ConversionPlan {
    if (lhs == rhs) {
        return try allocPlan(self, .refl);
    }

    // Negative memo: doomed `tryCandidate`s exhaust the bidirectional
    // def/ACUI search to prove two exprs are *not* def-equal, re-deriving the
    // same incomparable pair millions of times. The verdict is pure in
    // `(lhs, rhs)` under the fixed env/registry invariant asserted here.
    // Positive plans are NOT cached (they are request-arena pointers); they
    // are cheap relative to the doomed search.
    assertCacheIdentity(self);
    const key = DefCacheKey{
        .def_expr = lhs,
        .target_expr = rhs,
        .has_registry = self.shared.registry != null,
    };
    if (self.shared.theorem.compare_transparent_neg.contains(key)) {
        return null;
    }

    if (try compareTransparentUncached(self, lhs, rhs)) |plan| {
        return plan;
    }

    try self.shared.theorem.compare_transparent_neg.put(
        self.shared.theorem.allocator,
        key,
        {},
    );
    return null;
}

fn compareTransparentUncached(
    self: anytype,
    lhs: ExprId,
    rhs: ExprId,
) anyerror!?*const ConversionPlan {
    const lhs_node = self.shared.theorem.interner.node(lhs);
    const rhs_node = self.shared.theorem.interner.node(rhs);
    if (lhs_node.* == .app and rhs_node.* == .app) {
        const lhs_app = lhs_node.app;
        const rhs_app = rhs_node.app;
        if (lhs_app.term_id == rhs_app.term_id and
            lhs_app.args.len == rhs_app.args.len)
        {
            const children = try self.shared.allocator.alloc(
                *const ConversionPlan,
                lhs_app.args.len,
            );
            for (lhs_app.args, rhs_app.args, 0..) |lhs_arg, rhs_arg, idx| {
                children[idx] = try compareTransparent(
                    self,
                    lhs_arg,
                    rhs_arg,
                ) orelse {
                    return null;
                };
            }
            return try allocPlan(self, .{ .cong = .{ .children = children } });
        }
    }

    if (try planDefToTarget(self, lhs, rhs, .lhs)) |plan| {
        return plan;
    }
    if (try planDefToTarget(self, rhs, lhs, .rhs)) |plan| {
        return plan;
    }
    return null;
}

pub fn matchTemplateTransparent(
    self: anytype,
    template: TemplateExpr,
    actual: ExprId,
    bindings: []?ExprId,
) anyerror!bool {
    var state = try MatchSession.init(self.shared.allocator, bindings.len);
    defer state.deinit(self.shared.allocator);

    var witness_slots: std.AutoHashMapUnmanaged(ExprId, usize) = .empty;
    defer witness_slots.deinit(self.shared.allocator);
    for (bindings, 0..) |binding, idx| {
        state.seedBinding(idx, if (binding) |expr_id|
            try WitnessState.rebuildBoundValue(
                self,
                expr_id,
                &state,
                &witness_slots,
                .exact,
            )
        else
            null);
    }

    if (!try matchTemplateRecState(self, template, actual, &state)) {
        return false;
    }
    try WitnessState.representResolvedBindings(self, &state, bindings);
    return true;
}

pub fn instantiateDefTowardExpr(
    self: anytype,
    def_expr: ExprId,
    target_expr: ExprId,
) anyerror!?ExprId {
    // Pure memo: this query depends only on `(def_expr, target_expr)` under
    // the fixed env/registry invariant asserted here. It builds a fresh empty
    // session per attempt and takes no caller state. The transient ACUI def_ops
    // contexts re-issue the same query millions of times, so cache on the
    // shared, per-theorem interner context.
    assertCacheIdentity(self);
    const key = DefCacheKey{
        .def_expr = def_expr,
        .target_expr = target_expr,
        .has_registry = self.shared.registry != null,
    };
    if (self.shared.theorem.instantiate_def_cache.get(key)) |cached| {
        return cached;
    }

    const result = try instantiateDefTowardExprUncached(
        self,
        def_expr,
        target_expr,
    );

    try self.shared.theorem.instantiate_def_cache.put(
        self.shared.theorem.allocator,
        key,
        result,
    );
    return result;
}

fn instantiateDefTowardExprUncached(
    self: anytype,
    def_expr: ExprId,
    target_expr: ExprId,
) anyerror!?ExprId {
    _ = getConcreteDef(self, def_expr) orelse return null;

    if (try instantiateDefTowardExprViaSearch(
        self,
        def_expr,
        target_expr,
    )) |witness| {
        return witness;
    }
    return try instantiateDefTowardExprViaTargetGuidance(
        self,
        def_expr,
        target_expr,
    );
}

pub fn instantiateDefTowardExprViaSearch(
    self: anytype,
    def_expr: ExprId,
    target_expr: ExprId,
) anyerror!?ExprId {
    var session = try MatchSession.init(self.shared.allocator, 0);
    defer session.deinit(self.shared.allocator);
    const symbolic = try expandConcreteDef(
        self,
        def_expr,
        &session,
    ) orelse return null;

    if (!try matchSymbolicToExprState(
        self,
        symbolic,
        target_expr,
        &session,
    ) and !try self.matchSymbolicToExprSemantic(
        symbolic,
        target_expr,
        &session,
        semantic_match_budget,
    )) {
        return null;
    }
    return try WitnessState.materializeResolvedSymbolic(
        self,
        symbolic,
        &session,
    );
}

pub fn instantiateDefTowardExprViaTargetGuidance(
    self: anytype,
    def_expr: ExprId,
    target_expr: ExprId,
) anyerror!?ExprId {
    var session = try MatchSession.init(self.shared.allocator, 0);
    defer session.deinit(self.shared.allocator);
    const symbolic = try expandConcreteDef(
        self,
        def_expr,
        &session,
    ) orelse return null;

    while (true) {
        if (try WitnessState.materializeResolvedSymbolic(
            self,
            symbolic,
            &session,
        )) |witness| {
            return witness;
        }
        if (!try guideSymbolicWitnessesFromTarget(
            self,
            symbolic,
            target_expr,
            &session,
        )) {
            return null;
        }
    }
}

pub fn guideSymbolicWitnessesFromTarget(
    self: anytype,
    symbolic: *const SymbolicExpr,
    target_expr: ExprId,
    state: *MatchSession,
) anyerror!bool {
    const symbolic_app = switch (symbolic.*) {
        .app => |app| app,
        else => return false,
    };
    const target_node = self.shared.theorem.interner.node(target_expr);
    const target_app = switch (target_node.*) {
        .app => |app| app,
        .variable => return try guideSymbolicWitnessesFromAcuiTarget(
            self,
            symbolic,
            target_expr,
            state,
        ),
        .placeholder => return try guideSymbolicWitnessesFromAcuiTarget(
            self,
            symbolic,
            target_expr,
            state,
        ),
    };

    if (symbolic_app.term_id == target_app.term_id and
        symbolic_app.args.len == target_app.args.len)
    {
        var snapshot = try WitnessState.saveMatchSnapshot(self, state);
        defer WitnessState.deinitMatchSnapshot(self, &snapshot);

        var made_progress = false;
        var same_head_failed = false;
        for (symbolic_app.args, target_app.args) |symbolic_arg, target_arg| {
            if (try tryMatchSymbolicToExprDirect(
                self,
                symbolic_arg,
                target_arg,
                state,
            )) {
                continue;
            }
            if (!try guideSymbolicWitnessesFromTarget(
                self,
                symbolic_arg,
                target_arg,
                state,
            )) {
                same_head_failed = true;
                break;
            }
            made_progress = true;
        }
        if (!same_head_failed) {
            if (made_progress) return true;
            try WitnessState.restoreMatchSnapshot(self, &snapshot, state);
        } else {
            try WitnessState.restoreMatchSnapshot(self, &snapshot, state);
        }
    }

    return try guideSymbolicWitnessesFromAcuiTarget(
        self,
        symbolic,
        target_expr,
        state,
    );
}

pub fn guideSymbolicWitnessesFromAcuiTarget(
    self: anytype,
    symbolic: *const SymbolicExpr,
    target_expr: ExprId,
    state: *MatchSession,
) anyerror!bool {
    const registry = self.shared.registry orelse return false;
    const symbolic_sort = WitnessState.symbolicSortName(self, symbolic, state) orelse {
        return false;
    };
    const acui = try registry.resolveStructuralCombinerForSort(
        self.shared.env,
        symbolic_sort,
    ) orelse return false;

    var support = AcuiSupport.Context.init(
        self.shared.allocator,
        self.shared.theorem,
        self.shared.env,
        registry,
    );
    defer support.deinit();
    if (!support.exprMatchesCombinerSort(target_expr, acui)) return false;

    var items = std.ArrayListUnmanaged(ExprId){};
    defer items.deinit(self.shared.allocator);
    try support.collectConcreteSetItems(
        target_expr,
        acui,
        &items,
    );

    for (items.items) |item_expr| {
        var snapshot = try WitnessState.saveMatchSnapshot(self, state);
        defer WitnessState.deinitMatchSnapshot(self, &snapshot);

        if (!try matchSymbolicAcuiLeafToExprState(
            self,
            symbolic,
            item_expr,
            acui.head_term_id,
            state,
        ) and !try self.matchSymbolicAcuiLeafToExprSemantic(
            symbolic,
            item_expr,
            acui.head_term_id,
            state,
            semantic_match_budget,
        )) {
            try WitnessState.restoreMatchSnapshot(self, &snapshot, state);
            continue;
        }
        return true;
    }
    return false;
}

fn matchResolvedTemplateConcrete(
    self: anytype,
    template: TemplateExpr,
    actual: ExprId,
    state: *MatchSession,
) anyerror!bool {
    // This is only for subtrees whose binders were already solved by earlier
    // matches. Once a template subtree is fully concrete, transparent matching
    // should use the same concrete relation as explicit checking rather than
    // insisting on more symbolic replay.
    const symbolic = try symbolicFromTemplate(self, template);
    const resolved = try WitnessState.materializeResolvedSymbolic(
        self,
        symbolic,
        state,
    ) orelse return false;
    return try WitnessState.concreteExprsMatchMode(
        self,
        resolved,
        actual,
        state,
        .transparent,
    );
}

pub fn matchTemplateRecState(
    self: anytype,
    template: TemplateExpr,
    actual: ExprId,
    state: *MatchSession,
) anyerror!bool {
    return switch (template) {
        .binder => |idx| blk: {
            break :blk try WitnessState.assignBinderFromExpr(
                self,
                idx,
                actual,
                state,
                .transparent,
            );
        },
        .app => |app| blk: {
            if (try matchTemplateAppDirectState(self, app, actual, state)) {
                break :blk true;
            }

            if (try matchExpandedTemplateAppState(self, app, actual, state)) {
                break :blk true;
            }

            if (try matchActualDefToTemplateState(
                self,
                template,
                actual,
                state,
            )) {
                break :blk true;
            }

            // Structural replay and def expansion did not match, but earlier
            // hypotheses may already have solved every binder in this subtree.
            // In that case, compare the resolved concrete expression directly.
            break :blk try matchResolvedTemplateConcrete(
                self,
                template,
                actual,
                state,
            );
        },
    };
}

pub fn matchTemplateAppDirectState(
    self: anytype,
    app: TemplateExpr.App,
    actual: ExprId,
    state: *MatchSession,
) anyerror!bool {
    const actual_node = self.shared.theorem.interner.node(actual);
    const actual_app = switch (actual_node.*) {
        .app => |value| value,
        .variable => return false,
        .placeholder => return false,
    };
    if (actual_app.term_id != app.term_id or
        actual_app.args.len != app.args.len)
    {
        return false;
    }

    var snapshot = try WitnessState.saveMatchSnapshot(self, state);
    defer WitnessState.deinitMatchSnapshot(self, &snapshot);

    for (app.args, actual_app.args) |tmpl_arg, actual_arg| {
        if (!try matchTemplateRecState(self, tmpl_arg, actual_arg, state)) {
            try WitnessState.restoreMatchSnapshot(self, &snapshot, state);
            return false;
        }
    }
    return true;
}

pub fn matchExpandedTemplateAppState(
    self: anytype,
    app: TemplateExpr.App,
    actual: ExprId,
    state: *MatchSession,
) anyerror!bool {
    var snapshot = try WitnessState.saveMatchSnapshot(self, state);
    defer WitnessState.deinitMatchSnapshot(self, &snapshot);

    const symbolic = try expandTemplateApp(self, app, state) orelse return false;
    if (try matchSymbolicToExprState(self, symbolic, actual, state)) {
        return true;
    }

    try WitnessState.restoreMatchSnapshot(self, &snapshot, state);
    return false;
}

pub fn matchActualDefToTemplateState(
    self: anytype,
    template: TemplateExpr,
    actual: ExprId,
    state: *MatchSession,
) anyerror!bool {
    _ = getConcreteDef(self, actual) orelse return false;

    var snapshot = try WitnessState.saveMatchSnapshot(self, state);
    defer WitnessState.deinitMatchSnapshot(self, &snapshot);

    const symbolic_template = try symbolicFromTemplate(self, template);
    const symbolic_actual = try expandConcreteDef(self, actual, state) orelse {
        return false;
    };
    if (try matchSymbolicToSymbolicState(
        self,
        symbolic_template,
        symbolic_actual,
        state,
    )) {
        return true;
    }

    try WitnessState.restoreMatchSnapshot(self, &snapshot, state);
    return false;
}

pub fn matchSymbolicToExprState(
    self: anytype,
    symbolic: *const SymbolicExpr,
    actual: ExprId,
    state: *MatchSession,
) anyerror!bool {
    return switch (symbolic.*) {
        .binder => |idx| blk: {
            break :blk try WitnessState.assignBinderFromExpr(
                self,
                idx,
                actual,
                state,
                .transparent,
            );
        },
        .fixed => |expr_id| {
            return (try compareTransparent(self, expr_id, actual)) != null;
        },
        .dummy => |slot| {
            const info = state.symbolic_dummy_infos.items[slot];
            return try WitnessState.matchSymbolicDummyState(
                self,
                slot,
                info,
                actual,
                state,
            );
        },
        .app => |app| {
            var snapshot = try WitnessState.saveMatchSnapshot(self, state);
            defer WitnessState.deinitMatchSnapshot(self, &snapshot);

            const actual_node = self.shared.theorem.interner.node(actual);
            if (actual_node.* == .app) {
                const actual_app = actual_node.app;
                if (actual_app.term_id == app.term_id and
                    actual_app.args.len == app.args.len)
                {
                    for (app.args, actual_app.args) |sym_arg, actual_arg| {
                        if (!try matchSymbolicToExprState(
                            self,
                            sym_arg,
                            actual_arg,
                            state,
                        )) {
                            try WitnessState.restoreMatchSnapshot(
                                self,
                                &snapshot,
                                state,
                            );
                            break;
                        }
                    } else {
                        return true;
                    }
                }
            }

            try WitnessState.restoreMatchSnapshot(self, &snapshot, state);

            if (try expandSymbolicApp(self, app, state)) |expanded| {
                if (try matchSymbolicToExprState(
                    self,
                    expanded,
                    actual,
                    state,
                )) {
                    return true;
                }
                try WitnessState.restoreMatchSnapshot(self, &snapshot, state);
            }

            if (try expandConcreteDef(self, actual, state)) |expanded_actual| {
                if (try matchSymbolicToSymbolicState(
                    self,
                    symbolic,
                    expanded_actual,
                    state,
                )) {
                    return true;
                }
                try WitnessState.restoreMatchSnapshot(self, &snapshot, state);
            }
            return false;
        },
    };
}

pub fn matchExprToSymbolic(
    self: anytype,
    actual: ExprId,
    symbolic: *const SymbolicExpr,
    state: *MatchSession,
    assign_mode: BindingMode,
) anyerror!bool {
    return switch (symbolic.*) {
        .binder => |idx| blk: {
            break :blk try WitnessState.assignBinderFromExpr(
                self,
                idx,
                actual,
                state,
                assign_mode,
            );
        },
        .fixed => |expr_id| {
            return (try compareTransparent(self, actual, expr_id)) != null;
        },
        .dummy => |slot| {
            const info = state.symbolic_dummy_infos.items[slot];
            return try WitnessState.matchSymbolicDummyState(
                self,
                slot,
                info,
                actual,
                state,
            );
        },
        .app => |app| {
            var snapshot = try WitnessState.saveMatchSnapshot(self, state);
            defer WitnessState.deinitMatchSnapshot(self, &snapshot);

            const actual_node = self.shared.theorem.interner.node(actual);
            if (actual_node.* == .app) {
                const actual_app = actual_node.app;
                if (actual_app.term_id == app.term_id and
                    actual_app.args.len == app.args.len)
                {
                    for (actual_app.args, app.args) |actual_arg, sym_arg| {
                        if (!try matchExprToSymbolic(
                            self,
                            actual_arg,
                            sym_arg,
                            state,
                            assign_mode,
                        )) {
                            try WitnessState.restoreMatchSnapshot(
                                self,
                                &snapshot,
                                state,
                            );
                            break;
                        }
                    } else {
                        return true;
                    }
                }
            }

            try WitnessState.restoreMatchSnapshot(self, &snapshot, state);

            if (try expandConcreteDef(self, actual, state)) |expanded_actual| {
                if (try matchSymbolicToSymbolicState(
                    self,
                    expanded_actual,
                    symbolic,
                    state,
                )) {
                    return true;
                }
                try WitnessState.restoreMatchSnapshot(self, &snapshot, state);
            }

            if (try expandSymbolicApp(self, app, state)) |expanded| {
                if (try matchExprToSymbolic(
                    self,
                    actual,
                    expanded,
                    state,
                    assign_mode,
                )) {
                    return true;
                }
                try WitnessState.restoreMatchSnapshot(self, &snapshot, state);
            }
            return false;
        },
    };
}

const SemanticSearch = @import("./semantic_search.zig");

pub fn matchSymbolicToSymbolicState(
    self: anytype,
    lhs: *const SymbolicExpr,
    rhs: *const SymbolicExpr,
    state: *MatchSession,
) anyerror!bool {
    // Negative memo: this inner matcher does an unbudgeted bidirectional
    // def-unfold and is invoked at every node of the outer semantic search,
    // so it re-explores structurally-identical (lhs, rhs) pairs under the same
    // state exponentially. The verdict is pure in (lhs, rhs, state); we cache
    // only failures (success mutates `state` and cannot be replayed from a
    // key). Rollback-safe because the key includes the state hash.
    //
    // Consulted at every depth. The per-call key cost is two structural
    // hashes (lhs, rhs) plus a state hash; structural hashing dominates for the
    // large, shallow exprs near the recursion root (e.g. church), where the
    // memo rarely fires — a measured ~10-25% per-fixture tax there. That tax is
    // the thing `SymbolicExpr` interning would erase (O(1) keys), at which point
    // the structural hashes become id lookups; the memo logic is unchanged.
    const key = blk: {
        const lh = SemanticSearch.hashSymbolicForSearch(self, lhs);
        const rh = SemanticSearch.hashSymbolicForSearch(self, rhs);
        const sh = try SemanticSearch.hashMatchSessionForSearch(self, state);
        var h = Types.mixHash(0xa1b2c3d4e5f60718, lh);
        h = Types.mixHash(h, rh);
        break :blk Types.mixHash(h, sh);
    };
    if (state.sym_match_neg.contains(key)) {
        return false;
    }
    const result = try matchSymbolicToSymbolicStateInner(self, lhs, rhs, state);
    if (!result) {
        try state.sym_match_neg.put(self.shared.allocator, key, {});
    }
    return result;
}

fn matchSymbolicToSymbolicStateInner(
    self: anytype,
    lhs: *const SymbolicExpr,
    rhs: *const SymbolicExpr,
    state: *MatchSession,
) anyerror!bool {
    return switch (lhs.*) {
        .binder => |idx| blk: {
            break :blk try WitnessState.assignBinderFromSymbolic(
                self,
                idx,
                rhs,
                state,
                .transparent,
            );
        },
        .fixed => |expr_id| {
            return try matchExprToSymbolic(
                self,
                expr_id,
                rhs,
                state,
                .transparent,
            );
        },
        .dummy => |slot| {
            return try WitnessState.matchDummyToSymbolic(self, slot, rhs, state);
        },
        .app => |lhs_app| {
            var snapshot = try WitnessState.saveMatchSnapshot(self, state);
            defer WitnessState.deinitMatchSnapshot(self, &snapshot);

            if (rhs.* == .app) {
                const rhs_app = rhs.app;
                if (lhs_app.term_id == rhs_app.term_id and
                    lhs_app.args.len == rhs_app.args.len)
                {
                    for (lhs_app.args, rhs_app.args) |lhs_arg, rhs_arg| {
                        if (!try matchSymbolicToSymbolicState(
                            self,
                            lhs_arg,
                            rhs_arg,
                            state,
                        )) {
                            try WitnessState.restoreMatchSnapshot(
                                self,
                                &snapshot,
                                state,
                            );
                            break;
                        }
                    } else {
                        return true;
                    }
                }
            }

            try WitnessState.restoreMatchSnapshot(self, &snapshot, state);

            if (try expandSymbolicApp(self, lhs_app, state)) |expanded_lhs| {
                if (try matchSymbolicToSymbolicState(
                    self,
                    expanded_lhs,
                    rhs,
                    state,
                )) {
                    return true;
                }
                try WitnessState.restoreMatchSnapshot(self, &snapshot, state);
            }
            if (rhs.* == .app) {
                if (try expandSymbolicApp(self, rhs.app, state)) |expanded_rhs| {
                    if (try matchSymbolicToSymbolicState(
                        self,
                        lhs,
                        expanded_rhs,
                        state,
                    )) {
                        return true;
                    }
                    try WitnessState.restoreMatchSnapshot(
                        self,
                        &snapshot,
                        state,
                    );
                }
            }
            return false;
        },
    };
}

pub fn tryMatchTemplateStateDirect(
    self: anytype,
    template: TemplateExpr,
    actual: ExprId,
    state: *MatchSession,
) anyerror!bool {
    var snapshot = try WitnessState.saveMatchSnapshot(self, state);
    defer WitnessState.deinitMatchSnapshot(self, &snapshot);
    if (try matchTemplateRecState(self, template, actual, state)) {
        return true;
    }
    try WitnessState.restoreMatchSnapshot(self, &snapshot, state);
    return false;
}

pub fn tryMatchSymbolicToExprDirect(
    self: anytype,
    symbolic: *const SymbolicExpr,
    actual: ExprId,
    state: *MatchSession,
) anyerror!bool {
    var snapshot = try WitnessState.saveMatchSnapshot(self, state);
    defer WitnessState.deinitMatchSnapshot(self, &snapshot);
    if (try matchSymbolicToExprState(self, symbolic, actual, state)) {
        return true;
    }
    try WitnessState.restoreMatchSnapshot(self, &snapshot, state);
    return false;
}
pub fn matchSymbolicAcuiLeafToExprState(
    self: anytype,
    symbolic: *const SymbolicExpr,
    actual: ExprId,
    head_term_id: u32,
    state: *MatchSession,
) anyerror!bool {
    switch (symbolic.*) {
        .app => |app| {
            if (app.term_id == head_term_id and app.args.len == 2) {
                var snapshot = try WitnessState.saveMatchSnapshot(self, state);
                defer WitnessState.deinitMatchSnapshot(self, &snapshot);

                if (try matchSymbolicAcuiLeafToExprState(
                    self,
                    app.args[0],
                    actual,
                    head_term_id,
                    state,
                )) {
                    return true;
                }
                try WitnessState.restoreMatchSnapshot(self, &snapshot, state);
                if (try matchSymbolicAcuiLeafToExprState(
                    self,
                    app.args[1],
                    actual,
                    head_term_id,
                    state,
                )) {
                    return true;
                }
                try WitnessState.restoreMatchSnapshot(self, &snapshot, state);
                return false;
            }
        },
        else => {},
    }
    return try tryMatchSymbolicToExprDirect(self, symbolic, actual, state);
}

pub fn expandTemplateApp(
    self: anytype,
    app: TemplateExpr.App,
    state: *MatchSession,
) anyerror!?*const SymbolicExpr {
    const term = getOpenableTerm(self, app.term_id) orelse return null;
    const body = term.body orelse return null;

    // Throwaway expansion scaffolding: scratch, like the `SymbolicExpr`
    // nodes it feeds (`allocSymbolic`). Anything that outlives the context
    // is deep-cloned at export (`cloneSymbolicExpr`).
    const subst = try self.shared.scratch().alloc(
        *const SymbolicExpr,
        term.args.len + term.dummy_args.len,
    );
    for (app.args, 0..) |arg, idx| {
        subst[idx] = try symbolicFromTemplate(self, arg);
    }
    for (term.dummy_args, 0..) |dummy_arg, idx| {
        const slot = try state.addDummyInfo(self.shared.allocator, .{
            .sort_name = dummy_arg.sort_name,
            .bound = dummy_arg.bound,
        });
        subst[term.args.len + idx] = try self.allocSymbolic(
            .{ .dummy = slot },
        );
    }
    return try symbolicFromStableTemplateSubst(self, body, subst);
}

pub fn expandConcreteDef(
    self: anytype,
    expr_id: ExprId,
    state: *MatchSession,
) anyerror!?*const SymbolicExpr {
    const def = getConcreteDef(self, expr_id) orelse return null;

    const subst = try self.shared.scratch().alloc(
        *const SymbolicExpr,
        def.term.args.len + def.term.dummy_args.len,
    );
    for (def.app.args, 0..) |arg, idx| {
        subst[idx] = try self.allocSymbolic(.{ .fixed = arg });
    }
    for (def.term.dummy_args, 0..) |dummy_arg, idx| {
        const slot = try state.addDummyInfo(self.shared.allocator, .{
            .sort_name = dummy_arg.sort_name,
            .bound = dummy_arg.bound,
        });
        subst[def.term.args.len + idx] = try self.allocSymbolic(
            .{ .dummy = slot },
        );
    }
    return try symbolicFromStableTemplateSubst(self, def.body, subst);
}

pub fn expandSymbolicApp(
    self: anytype,
    app: SymbolicExpr.App,
    state: *MatchSession,
) anyerror!?*const SymbolicExpr {
    const term = getOpenableTerm(self, app.term_id) orelse return null;
    const body = term.body orelse return null;

    const subst = try self.shared.scratch().alloc(
        *const SymbolicExpr,
        term.args.len + term.dummy_args.len,
    );
    @memcpy(subst[0..term.args.len], app.args);
    for (term.dummy_args, 0..) |dummy_arg, idx| {
        const slot = try state.addDummyInfo(self.shared.allocator, .{
            .sort_name = dummy_arg.sort_name,
            .bound = dummy_arg.bound,
        });
        subst[term.args.len + idx] = try self.allocSymbolic(
            .{ .dummy = slot },
        );
    }
    return try symbolicFromStableTemplateSubst(self, body, subst);
}

pub fn symbolicFromTemplate(
    self: anytype,
    template: TemplateExpr,
) anyerror!*const SymbolicExpr {
    return try symbolicFromStableTemplateSubst(self, template, null);
}

/// Memoized `symbolicFromTemplateSubst` for STABLE templates — templates
/// living in env/registry/view storage for the whole def_ops context (term
/// and def bodies, rewrite-rule sides, view templates). Every `TemplateExpr`
/// in the program today qualifies (`TemplateExpr.fromExpr` is only called
/// while building env rules and view decls); a future TRANSIENT template must
/// use the plain `symbolicFromTemplateSubst`, or its recycled args-pointer
/// could alias a stale memo key. The memo is exact, not heuristic: the callee
/// is a pure function of (template structure, subst pointers) and returns the
/// canonical interned node, so a hit is pointer-identical to a rebuild. This
/// skips the whole rebuild-and-reprobe walk that dominates def-unfold-heavy
/// matching (martin_lof/church, task #43).
pub fn symbolicFromStableTemplateSubst(
    self: anytype,
    template: TemplateExpr,
    subst: ?[]const *const SymbolicExpr,
) anyerror!*const SymbolicExpr {
    const app = switch (template) {
        // A bare binder is a subst lookup / leaf intern — cheaper than the
        // memo probe itself.
        .binder => return try symbolicFromTemplateSubst(self, template, subst),
        .app => |app| app,
    };
    // A zero-arity app's result depends only on term_id; the intern probe it
    // does is already as cheap as a memo probe.
    if (app.args.len == 0) {
        return try symbolicFromTemplateSubst(self, template, subst);
    }
    const key = SharedContextMod.TemplateSubstMemoKey{
        .template_args_ptr = @intFromPtr(app.args.ptr),
        .template_args_len = app.args.len,
        .term_id = app.term_id,
        .subst = subst orelse &.{},
    };
    if (self.shared.templateSubstMemoGet(key)) |hit| return hit;
    const result = try symbolicFromTemplateSubst(self, template, subst);
    try self.shared.templateSubstMemoPut(key, result);
    return result;
}

pub fn symbolicFromTemplateSubst(
    self: anytype,
    template: TemplateExpr,
    subst: ?[]const *const SymbolicExpr,
) anyerror!*const SymbolicExpr {
    switch (template) {
        .binder => |idx| {
            if (subst) |args| {
                if (idx >= args.len) return error.TemplateBinderOutOfRange;
                return args[idx];
            }
            return try self.allocSymbolic(.{ .binder = idx });
        },
        .app => |app| {
            // Build children into a per-frame stack buffer (recursion gives
            // each level its own frame, so buffers never clobber) and let
            // `internSymbolicApp` copy into the arena only on a miss — this is
            // the hottest node builder on def-unfold-heavy theories, and the
            // pre-allocated-scratch-args form leaked one array per intern hit.
            // Arities above the inline capacity fall back to the arena path.
            const inline_cap = 16;
            if (app.args.len <= inline_cap) {
                var buf: [inline_cap]*const SymbolicExpr = undefined;
                for (app.args, 0..) |arg, idx| {
                    buf[idx] = try symbolicFromTemplateSubst(self, arg, subst);
                }
                return try self.shared.internSymbolicApp(
                    app.term_id,
                    buf[0..app.args.len],
                );
            }
            const args = try self.shared.scratch().alloc(
                *const SymbolicExpr,
                app.args.len,
            );
            for (app.args, 0..) |arg, idx| {
                args[idx] = try symbolicFromTemplateSubst(self, arg, subst);
            }
            return try self.allocSymbolic(.{ .app = .{
                .term_id = app.term_id,
                .args = args,
            } });
        },
    }
}

pub fn getConcreteDef(self: anytype, expr_id: ExprId) ?struct {
    app: ExprApp,
    term: *const TermDecl,
    body: TemplateExpr,
} {
    const node = self.shared.theorem.interner.node(expr_id);
    const app = switch (node.*) {
        .app => |value| value,
        .variable => return null,
        .placeholder => return null,
    };
    const term = getOpenableTerm(self, app.term_id) orelse return null;
    const body = term.body orelse return null;
    return .{
        .app = app,
        .term = term,
        .body = body,
    };
}

pub fn getOpenableTerm(self: anytype, term_id: u32) ?*const TermDecl {
    if (term_id >= self.shared.env.terms.items.len) return null;
    const term = &self.shared.env.terms.items[term_id];
    if (!term.is_def or term.body == null) return null;
    return term;
}

pub fn allocPlan(
    self: anytype,
    plan: ConversionPlan,
) anyerror!*const ConversionPlan {
    const node = try self.shared.allocator.create(ConversionPlan);
    node.* = plan;
    return node;
}
