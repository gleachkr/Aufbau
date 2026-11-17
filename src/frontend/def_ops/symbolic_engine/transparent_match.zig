const std = @import("std");
const TermDecl = @import("../../env.zig").TermDecl;
const head_class = @import("../../head_class.zig");
const ExprId = @import("../../expr.zig").ExprId;
const AcuiCacheKey = @import("../../expr.zig").AcuiCacheKey;
const DefCacheKey = @import("../../expr.zig").DefCacheKey;
const UnfoldCacheKey = @import("../../expr.zig").UnfoldCacheKey;
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
const HiddenWitnessProvider = Types.HiddenWitnessProvider;
const MatchSession = MatchState.MatchSession;
const MatchSnapshot = MatchState.MatchSnapshot;

/// Under `holes_match_anything`, an actual expression holding a meta is
/// only partly known: it fixes no binder, dummy or fixed subterm it faces,
/// and only its visible structure is matched (below the hole-free heads). A
/// holey line's final check compares it with the instantiated rule.
fn holeyActual(self: anytype, actual: ExprId) bool {
    if (!self.shared.holes_match_anything) return false;
    return self.shared.theorem.containsMetaLeaf(actual);
}

/// `holeyActual` for the actual side of a symbolic match: a meta in any of
/// its fixed subterms.
fn holeySymbolicActual(self: anytype, actual: *const SymbolicExpr) bool {
    if (!self.shared.holes_match_anything) return false;
    return switch (actual.*) {
        .fixed => |expr_id| holeyActual(self, expr_id),
        .binder, .dummy => false,
        .app => |app| for (app.args) |arg| {
            if (holeySymbolicActual(self, arg)) break true;
        } else false,
    };
}

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
    rewrites: bool,
) anyerror!?ExprId {
    // Pure in (def_expr, item_expr, head_term_id, rewrites) under the fixed env/registry
    // invariant asserted here. This uses a fresh session per call, and
    // transient def_ops contexts re-issue it for every ACUI leaf-pair.
    assertCacheIdentity(self);
    const key = AcuiCacheKey{
        .def_expr = def_expr,
        .item_expr = item_expr,
        .head_term_id = head_term_id,
        .has_registry = self.shared.registry != null,
        .rewrites = rewrites,
        .holes_match_anything = holeyActual(self, def_expr) or holeyActual(self, item_expr),
    };
    if (self.shared.theorem.instantiate_acui_cache.get(key)) |cached| {
        return cached;
    }
    const result = try instantiateDefTowardAcuiItemUncached(
        self,
        def_expr,
        item_expr,
        head_term_id,
        rewrites,
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
    rewrites: bool,
) anyerror!?ExprId {
    _ = getConcreteDef(self, def_expr) orelse return null;
    var session = try MatchSession.init(self.shared.allocator, 0);
    defer session.deinit(self.shared.allocator);
    // A bag compared modulo rewriting holds normal forms: the def's body is
    // compared at its normal form, like `unfoldDefToward`'s. Without
    // rewriting, as it stands.
    session.rewrites = if (rewrites) .unfoldings else .none;
    const symbolic = try expandConcreteDef(
        self,
        def_expr,
        &session,
    ) orelse return null;

    if (!try matchSymbolicAcuiLeafToExprState(
        self,
        try openedForMatch(self, symbolic, &session) orelse symbolic,
        item_expr,
        head_term_id,
        &session,
    )) {
        return null;
    }
    return try WitnessState.materializeFinalSymbolic(
        self,
        symbolic,
        &session,
    );
}

/// The body of a concrete def application with its arguments
/// substituted: the one unfolding a def without hidden dummies has. Null
/// for a non-def head or a def whose unfolding would have to invent a
/// dummy witness.
pub fn unfoldConcreteDef(
    self: anytype,
    def_expr: ExprId,
) anyerror!?ExprId {
    const def = getConcreteDef(self, def_expr) orelse return null;
    if (def.term.dummy_args.len != 0) return null;
    var session = try MatchSession.init(self.shared.allocator, 0);
    defer session.deinit(self.shared.allocator);
    const symbolic = try expandConcreteDef(
        self,
        def_expr,
        &session,
    ) orelse return null;
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
    const witness = try unfoldDefToward(self, def_expr, target_expr, false, null) orelse {
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

/// The deterministic unfolding of `def_expr` toward `target_expr`: its
/// body, with each dummy read off the target by the deterministic match, or
/// by the target's guidance when the match leaves one open, or else asked
/// of `provider`. A def without dummies has one unfolding. With `rewrites`,
/// the body, the target, and every def body the match opens on either side
/// are compared in their `@rewrite` normal forms (dummies left open, first
/// rule wins), so a dummy the rules erase or move is read where it lands.
/// Nothing here searches over rewrites or unfolding orders.
pub fn unfoldDefToward(
    self: anytype,
    def_expr: ExprId,
    target_expr: ExprId,
    rewrites: bool,
    provider: ?HiddenWitnessProvider,
) anyerror!?ExprId {
    // Pure in the key under the fixed env/registry invariant asserted here,
    // except where `provider` supplies a witness the match left open: that
    // result is not cached. The common target asks the same pair again for
    // every comparison that reaches it.
    assertCacheIdentity(self);
    const key = UnfoldCacheKey{
        .def_expr = def_expr,
        .target_expr = target_expr,
        .has_registry = self.shared.registry != null,
        .rewrites = rewrites,
        .holes_match_anything = holeyActual(self, def_expr) or holeyActual(self, target_expr),
    };
    const cache = &self.shared.theorem.unfold_toward_cache;
    if (cache.get(key)) |cached| return cached;
    var provided = false;
    const result = try unfoldDefTowardUncached(self, def_expr, target_expr, rewrites, provider, &provided);
    if (!provided) try cache.put(self.shared.theorem.allocator, key, result);
    return result;
}

fn unfoldDefTowardUncached(
    self: anytype,
    def_expr: ExprId,
    target_expr: ExprId,
    rewrites: bool,
    provider: ?HiddenWitnessProvider,
    provided: *bool,
) anyerror!?ExprId {
    const def = getConcreteDef(self, def_expr) orelse return null;
    if (def.term.dummy_args.len == 0) return try unfoldConcreteDef(self, def_expr);
    var session = try MatchSession.init(self.shared.allocator, 0);
    defer session.deinit(self.shared.allocator);
    session.rewrites = if (rewrites) .unfoldings else .none;
    const symbolic = try expandConcreteDef(self, def_expr, &session) orelse return null;
    const compared = try openedForMatch(self, symbolic, &session) orelse symbolic;
    const target = if (rewrites) try normalExpr(self, target_expr, &session) else target_expr;
    const matched = try matchSymbolicToExprState(self, compared, target, &session);
    if (matched) {
        if (try WitnessState.materializeResolvedSymbolic(self, symbolic, &session)) |witness| {
            return witness;
        }
    }
    if (try unfoldByTargetGuidance(self, def_expr, target_expr, session.rewrites)) |witness| {
        return witness;
    }
    if (!matched) return null;
    provided.* = true;
    return try provideUnresolvedWitnesses(self, symbolic, &session, provider orelse return null);
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
        .holes_match_anything = holeyActual(self, lhs) or holeyActual(self, rhs),
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
            const mismatch: ?usize = for (lhs_app.args, rhs_app.args, 0..) |lhs_arg, rhs_arg, idx| {
                children[idx] = try compareTransparent(
                    self,
                    lhs_arg,
                    rhs_arg,
                ) orelse break idx;
            } else null;
            const idx = mismatch orelse {
                return try allocPlan(self, .{ .cong = .{ .children = children } });
            };
            // A def may drop or bury the arg that differs (`K a b ≡ K a c`
            // for `K x y := x`), so fall through to the unfold attempts below.
            // If the head forces that arg, unfolding cannot reconcile it.
            if (head_class.argDetermined(
                self.shared.env,
                self.shared.registry,
                lhs_app.term_id,
                idx,
            )) return null;
        }
    }

    return switch (laterDef(self, exprHead(self, lhs), exprHead(self, rhs)) orelse return null) {
        .lhs => try planDefToTarget(self, lhs, rhs, .lhs),
        .rhs => try planDefToTarget(self, rhs, lhs, .rhs),
    };
}

pub const Side = enum { lhs, rhs };

/// A def body a transparent matcher has just opened, in the form it is
/// compared in: its `@rewrite` normal form when the session compares modulo
/// rewriting (dummies left open, first rule wins), else as it stands.
/// A concrete expression's `@rewrite` normal form, or the expression itself
/// when no rule fires (or the rules run out of fuel).
fn normalExpr(self: anytype, expr_id: ExprId, state: *MatchSession) anyerror!ExprId {
    if (self.shared.registry == null) return expr_id;
    const fixed = try self.allocSymbolic(.{ .fixed = expr_id });
    const normal = try DirectedNormalize.normalForm(self, fixed, state) orelse return expr_id;
    if (!normal.changed) return expr_id;
    return try WitnessState.symbolicToConcreteIfPlain(self, normal.expr, state) orelse expr_id;
}

fn openedForMatch(
    self: anytype,
    opened: ?*const SymbolicExpr,
    state: *MatchSession,
) anyerror!?*const SymbolicExpr {
    const body = opened orelse return null;
    if (state.rewrites == .none) return body;
    return try DirectedNormalize.bigStepSymbolic(self, body, state) orelse body;
}

/// Which side a comparison unfolds: the one whose head is the later def, or
/// the left on a tie. A def's body mentions only earlier terms, so the later
/// head can only meet the other side by being unfolded, and each comparison
/// takes one path instead of searching over unfolding orders. Null when
/// neither head is a def: the heads are fixed and the terms differ.
pub fn laterDef(self: anytype, lhs_term: ?u32, rhs_term: ?u32) ?Side {
    const lhs_def = openableHead(self, lhs_term);
    const rhs_def = openableHead(self, rhs_term);
    if (lhs_def) |l| {
        if (rhs_def) |r| return if (l >= r) .lhs else .rhs;
        return .lhs;
    }
    return if (rhs_def != null) .rhs else null;
}

fn openableHead(self: anytype, term_id: ?u32) ?u32 {
    const id = term_id orelse return null;
    return if (getOpenableTerm(self, id) != null) id else null;
}

pub fn exprHead(self: anytype, expr_id: ExprId) ?u32 {
    return switch (self.shared.theorem.interner.node(expr_id).*) {
        .app => |app| app.term_id,
        else => null,
    };
}

pub fn matchTemplateTransparent(
    self: anytype,
    template: TemplateExpr,
    actual: ExprId,
    bindings: []?ExprId,
    residue: ?*bool,
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

    var snapshot = try WitnessState.saveMatchSnapshot(self, &state);
    defer WitnessState.deinitMatchSnapshot(self, &snapshot);
    if (!try matchTemplateSettled(self, template, actual, &state, &snapshot)) {
        return false;
    }
    try WitnessState.representResolvedBindings(self, &state, bindings);
    if (residue) |out| {
        out.* = false;
        for (state.bindings, bindings) |bound, materialized| {
            if (bound != null and materialized == null) {
                out.* = true;
                break;
            }
        }
    }
    return true;
}

/// `symbolic` with the dummies its match left open filled by `provider`.
fn provideUnresolvedWitnesses(
    self: anytype,
    symbolic: *const SymbolicExpr,
    session: *MatchSession,
    provider: HiddenWitnessProvider,
) anyerror!?ExprId {
    const roots = try WitnessState.collectUnresolvedRootsInSymbolicOwned(
        self,
        symbolic,
        session,
    );
    defer self.shared.allocator.free(roots);
    if (roots.len == 0) return null;
    sortUnresolvedRoots(roots);

    const extra_used_deps =
        try WitnessState.collectConcreteDepsInSymbolicRoot(
            self,
            symbolic,
            session,
        );
    const assignments = try provider.provide(
        self.shared.allocator,
        roots,
        extra_used_deps,
    ) orelse return null;
    defer self.shared.allocator.free(assignments);
    try WitnessState.applyMaterializedDummyAssignments(
        self,
        session,
        assignments,
    );
    return try WitnessState.materializeResolvedSymbolic(
        self,
        symbolic,
        session,
    );
}

fn sortUnresolvedRoots(roots: []Types.UnresolvedDummyRoot) void {
    var i: usize = 1;
    while (i < roots.len) : (i += 1) {
        const root = roots[i];
        var j = i;
        while (j > 0 and roots[j - 1].root_slot > root.root_slot) : (j -= 1) {
            roots[j] = roots[j - 1];
        }
        roots[j] = root;
    }
}

fn unfoldByTargetGuidance(
    self: anytype,
    def_expr: ExprId,
    target_expr: ExprId,
    rewrites: MatchState.Rewriting,
) anyerror!?ExprId {
    var session = try MatchSession.init(self.shared.allocator, 0);
    defer session.deinit(self.shared.allocator);
    session.rewrites = rewrites;
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

    var items = std.ArrayListUnmanaged(ExprId).empty;
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
    if (state.rewrites == .all and self.shared.registry != null) {
        if (try WitnessState.concreteExprsMatchModuloRewrites(self, resolved, actual, state)) return true;
    }
    return try WitnessState.concreteExprsMatchMode(self, resolved, actual, state, .transparent);
}

pub fn matchTemplateRecState(
    self: anytype,
    template: TemplateExpr,
    actual: ExprId,
    state: *MatchSession,
) anyerror!bool {
    if (holeyActual(self, actual) and (template == .binder or
        self.shared.theorem.isPlaceholder(actual))) return true;
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
            if (try matchResolvedTemplateConcrete(
                self,
                template,
                actual,
                state,
            )) {
                break :blk true;
            }

            if (try matchTemplateToNormalActual(self, template, actual, state)) {
                break :blk true;
            }

            // A rewrite-head node proves nothing by mismatching structurally:
            // `[x/t] p` may match only once rewritten, and cannot be rewritten
            // until `x` and `p` are known. Defer it, let the siblings bind
            // what they can, and settle it at the boundary by instantiation
            // and normalization.
            break :blk try deferRewriteHeadMismatch(
                self,
                template,
                app,
                actual,
                state,
            );
        },
    };
}

fn deferRewriteHeadMismatch(
    self: anytype,
    template: TemplateExpr,
    app: TemplateExpr.App,
    actual: ExprId,
    state: *MatchSession,
) anyerror!bool {
    if (state.deferral_suspended != 0) return false;
    const registry = self.shared.registry orelse return false;
    if (registry.getRewriteRules(app.term_id).len == 0) return false;
    try state.deferred.append(self.shared.allocator, .{
        .template = template,
        .actual = actual,
    });
    return true;
}

/// Walk `template` against `actual` with sibling deferral, then settle every
/// node deferred by the walk. A provisional result never escapes: if a
/// deferred node cannot be settled, the state is rolled back to `snapshot`
/// and the walk repeats with deferral suspended, so callers see exactly the
/// pre-deferral outcome set plus the matches deferral unlocks. Callers roll
/// back on `false`.
fn matchTemplateSettled(
    self: anytype,
    template: TemplateExpr,
    actual: ExprId,
    state: *MatchSession,
    snapshot: *const MatchSnapshot,
) anyerror!bool {
    const start = snapshot.deferred_len;
    if (!try matchTemplateRecState(self, template, actual, state)) return false;
    if (state.deferred.items.len == start) return true;
    if (try drainDeferredNodes(self, state, start)) return true;

    try WitnessState.restoreMatchSnapshot(self, snapshot, state);
    state.deferral_suspended += 1;
    defer state.deferral_suspended -= 1;
    return try matchTemplateRecState(self, template, actual, state);
}

fn drainDeferredNodes(
    self: anytype,
    state: *MatchSession,
    start: usize,
) anyerror!bool {
    state.deferral_suspended += 1;
    defer state.deferral_suspended -= 1;
    // Settling a deferred node compares it modulo rewriting: its binders are
    // bound now, so the redex can reduce.
    const rewrites = state.rewrites;
    state.rewrites = .all;
    defer state.rewrites = rewrites;
    var idx = start;
    while (idx < state.deferred.items.len) : (idx += 1) {
        const node = state.deferred.items[idx];
        const symbolic = try symbolicFromTemplate(self, node.template);
        if (!try tryMatchSymbolicToExprDirect(self, symbolic, node.actual, state)) {
            return false;
        }
    }
    state.deferred.shrinkRetainingCapacity(start);
    return true;
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
    if (state.rewrites != .all) return try matchSymbolicToExprOnce(self, symbolic, actual, state);
    var snapshot = try WitnessState.saveMatchSnapshot(self, state);
    defer WitnessState.deinitMatchSnapshot(self, &snapshot);
    if (try matchSymbolicToExprOnce(self, symbolic, actual, state)) return true;
    try WitnessState.restoreMatchSnapshot(self, &snapshot, state);
    return try matchNormalForms(self, symbolic, try self.allocSymbolic(.{ .fixed = actual }), state);
}

fn matchSymbolicToExprOnce(
    self: anytype,
    symbolic: *const SymbolicExpr,
    actual: ExprId,
    state: *MatchSession,
) anyerror!bool {
    if (holeyActual(self, actual) and (symbolic.* != .app or
        self.shared.theorem.isPlaceholder(actual))) return true;
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
            return try fixedMatches(self, expr_id, actual, state);
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
                    const mismatch: ?usize = for (app.args, actual_app.args, 0..) |sym_arg, actual_arg, idx| {
                        if (!try matchSymbolicToExprState(
                            self,
                            sym_arg,
                            actual_arg,
                            state,
                        )) break idx;
                    } else null;
                    const idx = mismatch orelse return true;
                    try WitnessState.restoreMatchSnapshot(self, &snapshot, state);
                    if (head_class.argDetermined(
                        self.shared.env,
                        self.shared.registry,
                        app.term_id,
                        idx,
                    )) return false;
                }
            }

            const matched = switch (laterDef(self, app.term_id, exprHead(self, actual)) orelse return false) {
                .lhs => try matchSymbolicToExprState(
                    self,
                    try openedForMatch(self, try expandSymbolicApp(self, app, state), state) orelse return false,
                    actual,
                    state,
                ),
                .rhs => try matchSymbolicToSymbolicState(
                    self,
                    symbolic,
                    try openedForMatch(self, try expandConcreteDef(self, actual, state), state) orelse return false,
                    state,
                ),
            };
            if (!matched) try WitnessState.restoreMatchSnapshot(self, &snapshot, state);
            return matched;
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
    if (state.rewrites != .all) return try matchExprToSymbolicOnce(self, actual, symbolic, state, assign_mode);
    var snapshot = try WitnessState.saveMatchSnapshot(self, state);
    defer WitnessState.deinitMatchSnapshot(self, &snapshot);
    if (try matchExprToSymbolicOnce(self, actual, symbolic, state, assign_mode)) return true;
    try WitnessState.restoreMatchSnapshot(self, &snapshot, state);
    return try matchNormalForms(self, try self.allocSymbolic(.{ .fixed = actual }), symbolic, state);
}

fn matchExprToSymbolicOnce(
    self: anytype,
    actual: ExprId,
    symbolic: *const SymbolicExpr,
    state: *MatchSession,
    assign_mode: BindingMode,
) anyerror!bool {
    if (holeyActual(self, actual) and (symbolic.* != .app or
        self.shared.theorem.isPlaceholder(actual))) return true;
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
            return try fixedMatches(self, actual, expr_id, state);
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
                    const mismatch: ?usize = for (actual_app.args, app.args, 0..) |actual_arg, sym_arg, idx| {
                        if (!try matchExprToSymbolic(
                            self,
                            actual_arg,
                            sym_arg,
                            state,
                            assign_mode,
                        )) break idx;
                    } else null;
                    const idx = mismatch orelse return true;
                    try WitnessState.restoreMatchSnapshot(self, &snapshot, state);
                    if (head_class.argDetermined(
                        self.shared.env,
                        self.shared.registry,
                        app.term_id,
                        idx,
                    )) return false;
                }
            }

            const matched = switch (laterDef(self, exprHead(self, actual), app.term_id) orelse return false) {
                .lhs => try matchSymbolicToSymbolicState(
                    self,
                    try openedForMatch(self, try expandConcreteDef(self, actual, state), state) orelse return false,
                    symbolic,
                    state,
                ),
                .rhs => try matchExprToSymbolic(
                    self,
                    actual,
                    try openedForMatch(self, try expandSymbolicApp(self, app, state), state) orelse return false,
                    state,
                    assign_mode,
                ),
            };
            if (!matched) try WitnessState.restoreMatchSnapshot(self, &snapshot, state);
            return matched;
        },
    };
}

const MatchMemoKey = @import("./match_memo_key.zig");
const DirectedNormalize = @import("./directed_normalize.zig");

/// Two concrete expressions: transparently equal, or, comparing modulo
/// `@rewrite`, equal as `.normalized` concrete expressions (normal forms,
/// ACUI rearrangement, a meet through defs).
fn fixedMatches(self: anytype, lhs: ExprId, rhs: ExprId, state: *MatchSession) anyerror!bool {
    if ((try compareTransparent(self, lhs, rhs)) != null) return true;
    if (state.rewrites != .all or self.shared.registry == null) return false;
    return try WitnessState.concreteExprsMatchModuloRewrites(self, lhs, rhs, state);
}

/// Comparing modulo `@rewrite`, a mismatch is final only between normal
/// forms: compare the two sides again at their normal forms when either
/// differs from what was compared. A normal form is a fixpoint, so the
/// retry's own mismatch is final. Bound binders are read through the
/// session; a redex over an unbound binder stays as it is.
fn matchNormalForms(
    self: anytype,
    lhs: *const SymbolicExpr,
    rhs: *const SymbolicExpr,
    state: *MatchSession,
) anyerror!bool {
    if (self.shared.registry == null) return false;
    const lhs_normal = try DirectedNormalize.normalForm(self, lhs, state) orelse return false;
    const rhs_normal = try DirectedNormalize.normalForm(self, rhs, state) orelse return false;
    if (!lhs_normal.changed and !rhs_normal.changed) return false;
    return try matchSymbolicToSymbolicState(self, lhs_normal.expr, rhs_normal.expr, state);
}

/// A template node against the normal form of an actual it mismatched,
/// comparing modulo `@rewrite`.
fn matchTemplateToNormalActual(
    self: anytype,
    template: TemplateExpr,
    actual: ExprId,
    state: *MatchSession,
) anyerror!bool {
    if (state.rewrites != .all) return false;
    const normal_expr = try normalExpr(self, actual, state);
    if (normal_expr == actual) return false;
    var snapshot = try WitnessState.saveMatchSnapshot(self, state);
    defer WitnessState.deinitMatchSnapshot(self, &snapshot);
    if (try matchTemplateRecState(self, template, normal_expr, state)) return true;
    try WitnessState.restoreMatchSnapshot(self, &snapshot, state);
    return false;
}

/// Match `template` against `actual` modulo `@rewrite` (see
/// `MatchSession.rewrites`): the transparent walk, with normal forms taken
/// only where it mismatches. Deterministic: no rule choice, no unfolding
/// order, nothing to search.
pub fn matchTemplateModuloRewrites(
    self: anytype,
    template: TemplateExpr,
    actual: ExprId,
    state: *MatchSession,
) anyerror!bool {
    if (self.shared.registry == null) return try tryMatchTemplateStateDirect(self, template, actual, state);
    const rewrites = state.rewrites;
    state.rewrites = .all;
    defer state.rewrites = rewrites;
    return try tryMatchTemplateStateDirect(self, template, actual, state);
}

/// `matchTemplateModuloRewrites` for a symbolic pattern.
pub fn matchSymbolicToExprModuloRewrites(
    self: anytype,
    symbolic: *const SymbolicExpr,
    actual: ExprId,
    state: *MatchSession,
) anyerror!bool {
    if (self.shared.registry == null) return try tryMatchSymbolicToExprDirect(self, symbolic, actual, state);
    const rewrites = state.rewrites;
    state.rewrites = .all;
    defer state.rewrites = rewrites;
    return try tryMatchSymbolicToExprDirect(self, symbolic, actual, state);
}

pub fn matchSymbolicToSymbolicState(
    self: anytype,
    lhs: *const SymbolicExpr,
    rhs: *const SymbolicExpr,
    state: *MatchSession,
) anyerror!bool {
    // Negative memo: an unfolding shares the arguments it substitutes, so
    // one pair is reached along every path to it, and a failing comparison
    // would be repeated each time. The verdict is pure in (lhs, rhs) and the state they reach
    // (`hashMatchSessionReachable`); we cache only failures (success mutates
    // `state` and cannot be replayed from a key). Rollback-safe because the
    // key includes that state. Keying on the whole session would miss every
    // revisit after a sibling or an expansion minted unrelated dummies (#587).
    //
    // Consulted at every depth. The per-call key cost is two structural
    // hashes (lhs, rhs) plus a state hash; structural hashing dominates for the
    // large, shallow exprs near the recursion root (e.g. church), where the
    // memo rarely fires — a measured ~10-25% per-fixture tax there. That tax is
    // the thing `SymbolicExpr` interning would erase (O(1) keys), at which point
    // the structural hashes become id lookups; the memo logic is unchanged.
    const key = blk: {
        const lh = Types.symbolicHash(lhs);
        const rh = Types.symbolicHash(rhs);
        const sh = try MatchMemoKey.hashMatchSessionReachable(self, state, lhs, rhs);
        var h = Types.mixHash(0xa1b2c3d4e5f60718, lh);
        h = Types.mixHash(h, rh);
        // A meta matches anything only under the flag: keep those
        // verdicts apart (`DefCacheKey`).
        if (self.shared.holes_match_anything) h = Types.mixHash(h, 1);
        h = Types.mixHash(h, @backingInt(state.rewrites));
        break :blk Types.mixHash(h, sh);
    };
    if (state.sym_match_neg.contains(key)) {
        return false;
    }
    const result = if (state.rewrites != .all)
        try matchSymbolicToSymbolicStateInner(self, lhs, rhs, state)
    else blk: {
        var snapshot = try WitnessState.saveMatchSnapshot(self, state);
        defer WitnessState.deinitMatchSnapshot(self, &snapshot);
        if (try matchSymbolicToSymbolicStateInner(self, lhs, rhs, state)) break :blk true;
        try WitnessState.restoreMatchSnapshot(self, &snapshot, state);
        break :blk try matchNormalForms(self, lhs, rhs, state);
    };
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
    // A fixed side is a concrete expression, which the app case below cannot
    // take apart, so an app is matched against it as one. A def unfolded by
    // `expandConcreteDef` keeps its arguments fixed: `ra_add z z w` becomes
    // `⟨ kr_add , scons (cv z) … ⟩` with `cv z` fixed, against a pattern's
    // own `cv z`.
    if (rhs.* == .fixed and (lhs.* == .app or holeyActual(self, rhs.fixed))) {
        return try matchSymbolicToExprState(self, lhs, rhs.fixed, state);
    }
    if (lhs.* != .app and holeySymbolicActual(self, rhs)) return true;
    // Either side can hold the pattern: an actual whose def opened is
    // compared on the left (`matchExprToSymbolic`). A binder or dummy on the
    // right takes an app on the left as it is, as it would on the left.
    if (lhs.* == .app) switch (rhs.*) {
        .binder => |idx| return try WitnessState.assignBinderFromSymbolic(
            self,
            idx,
            lhs,
            state,
            .transparent,
        ),
        .dummy => |slot| return try WitnessState.matchDummyToSymbolic(self, slot, lhs, state),
        .app, .fixed => {},
    };
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
                    const mismatch: ?usize = for (lhs_app.args, rhs_app.args, 0..) |lhs_arg, rhs_arg, idx| {
                        if (!try matchSymbolicToSymbolicState(
                            self,
                            lhs_arg,
                            rhs_arg,
                            state,
                        )) break idx;
                    } else null;
                    const idx = mismatch orelse return true;
                    try WitnessState.restoreMatchSnapshot(self, &snapshot, state);
                    if (head_class.argDetermined(
                        self.shared.env,
                        self.shared.registry,
                        lhs_app.term_id,
                        idx,
                    )) return false;
                }
            }

            const rhs_head: ?u32 = if (rhs.* == .app) rhs.app.term_id else null;
            const matched = switch (laterDef(self, lhs_app.term_id, rhs_head) orelse return false) {
                .lhs => try matchSymbolicToSymbolicState(
                    self,
                    try openedForMatch(self, try expandSymbolicApp(self, lhs_app, state), state) orelse return false,
                    rhs,
                    state,
                ),
                .rhs => try matchSymbolicToSymbolicState(
                    self,
                    lhs,
                    try openedForMatch(self, try expandSymbolicApp(self, rhs.app, state), state) orelse return false,
                    state,
                ),
            };
            if (!matched) try WitnessState.restoreMatchSnapshot(self, &snapshot, state);
            return matched;
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
    if (try matchTemplateSettled(self, template, actual, state, &snapshot)) {
        return true;
    }
    try WitnessState.restoreMatchSnapshot(self, &snapshot, state);
    return false;
}

/// Walk `template` against `actual` as `tryMatchTemplateStateDirect` does,
/// but leave the nodes it sets aside unsettled: the result binds what the
/// rest of the formula forces, for a normalized comparison to finish. On a
/// mismatch outside those nodes the state is rolled back.
pub fn tryMatchTemplateUnsettledState(
    self: anytype,
    template: TemplateExpr,
    actual: ExprId,
    state: *MatchSession,
) anyerror!bool {
    var snapshot = try WitnessState.saveMatchSnapshot(self, state);
    defer WitnessState.deinitMatchSnapshot(self, &snapshot);
    if (!try matchTemplateRecState(self, template, actual, state)) {
        try WitnessState.restoreMatchSnapshot(self, &snapshot, state);
        return false;
    }
    state.deferred.shrinkRetainingCapacity(snapshot.deferred_len);
    return true;
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

/// Dep bits of the parts of `symbolic` that are already concrete at call
/// time (`.fixed` leaves, recursively through apps). Unresolved binders and
/// dummies contribute nothing: this is a stable under-approximation used for
/// capture masks — it must only contain bits that are certainly part of the
/// argument instantiation, whatever the rest resolves to later. Memoized per
/// interned node, so an unfolding chain that keeps wrapping the previous
/// argument walks each node once (#431).
pub fn fixedSymbolicDeps(
    self: anytype,
    symbolic: *const SymbolicExpr,
) anyerror!u55 {
    switch (symbolic.*) {
        .binder, .dummy => return 0,
        .fixed, .app => {},
    }
    if (self.shared.fixedDepsSlot(symbolic)) |slot| {
        if (slot.*) |deps| return deps;
    }
    const deps = switch (symbolic.*) {
        .fixed => |expr_id| try WitnessState.exprDeps(self, expr_id),
        .app => |app| blk: {
            var acc: u55 = 0;
            for (app.args) |arg| acc |= try fixedSymbolicDeps(self, arg);
            break :blk acc;
        },
        .binder, .dummy => unreachable,
    };
    if (self.shared.fixedDepsSlot(symbolic)) |slot| slot.* = deps;
    return deps;
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
    var forbidden_deps: u55 = 0;
    for (app.args, 0..) |arg, idx| {
        subst[idx] = try symbolicFromTemplate(self, arg);
        forbidden_deps |= try fixedSymbolicDeps(self, subst[idx]);
    }
    const distinct_group = state.symbolic_dummy_infos.items.len;
    for (term.dummy_args, 0..) |dummy_arg, idx| {
        const slot = try state.addDummyInfo(self.shared.allocator, .{
            .sort_name = dummy_arg.sort_name,
            .bound = dummy_arg.bound,
            .forbidden_deps = forbidden_deps,
            .distinct_group = if (dummy_arg.bound) distinct_group else null,
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
    // Only the dummy slots read the argument deps.
    const has_dummies = def.term.dummy_args.len != 0;
    var forbidden_deps: u55 = 0;
    for (def.app.args, 0..) |arg, idx| {
        subst[idx] = try self.allocSymbolic(.{ .fixed = arg });
        if (has_dummies) forbidden_deps |= try WitnessState.exprDeps(self, arg);
    }
    const distinct_group = state.symbolic_dummy_infos.items.len;
    for (def.term.dummy_args, 0..) |dummy_arg, idx| {
        const slot = try state.addDummyInfo(self.shared.allocator, .{
            .sort_name = dummy_arg.sort_name,
            .bound = dummy_arg.bound,
            .forbidden_deps = forbidden_deps,
            .distinct_group = if (dummy_arg.bound) distinct_group else null,
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
    var forbidden_deps: u55 = 0;
    for (app.args) |arg| {
        forbidden_deps |= try fixedSymbolicDeps(self, arg);
    }
    const distinct_group = state.symbolic_dummy_infos.items.len;
    for (term.dummy_args, 0..) |dummy_arg, idx| {
        const slot = try state.addDummyInfo(self.shared.allocator, .{
            .sort_name = dummy_arg.sort_name,
            .bound = dummy_arg.bound,
            .forbidden_deps = forbidden_deps,
            .distinct_group = if (dummy_arg.bound) distinct_group else null,
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
    return try symbolicFromTemplateSubst(self, template, null);
}

/// Memoized `symbolicFromTemplateSubst` for STABLE templates — templates
/// living in env/registry storage for the whole def_ops context: term and
/// def bodies and rewrite-rule sides, which are its only callers. A template
/// that came from a caller (`symbolicFromTemplate`) may be built per call,
/// and a recycled args pointer would alias a stale memo key, so those take
/// the plain `symbolicFromTemplateSubst`. The memo is exact, not heuristic: the callee
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
    return self.shared.env.openableDef(term_id);
}

pub fn allocPlan(
    self: anytype,
    plan: ConversionPlan,
) anyerror!*const ConversionPlan {
    const node = try self.shared.allocator.create(ConversionPlan);
    node.* = plan;
    return node;
}
