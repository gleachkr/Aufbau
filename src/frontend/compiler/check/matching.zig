const std = @import("std");
const ExprId = @import("../../expr.zig").ExprId;
const TheoremContext = @import("../../expr.zig").TheoremContext;
const GlobalEnv = @import("../../env.zig").GlobalEnv;
const RewriteRegistry = @import("../../rewrite_registry.zig").RewriteRegistry;
const Inference = @import("../inference.zig");
const Normalize = @import("../normalize.zig");
const DebugConfig = @import("../../debug.zig").DebugConfig;
const CheckedIr = @import("../../checked_ir.zig");
const CheckedLine = CheckedIr.CheckedLine;
const CheckedRef = CheckedIr.CheckedRef;
const appendRuleLine = CheckedIr.appendRuleLine;
const appendTransportLine = CheckedIr.appendTransportLine;
const CompilerDiag = @import("../../diag.zig");
const AcuiSupport = @import("../../acui_support.zig");
const DefOps = @import("../../def_ops.zig");
const FreshSelect = @import("../fresh_select.zig");

const HiddenWitnessProviderContext = struct {
    theorem: *TheoremContext,
    fresh: Inference.HiddenWitnessFreshContext,
    compared_exprs: [2]ExprId,

    fn provider(self: *HiddenWitnessProviderContext) DefOps.HiddenWitnessProvider {
        return .{
            .context = self,
            .provideFn = provide,
        };
    }

    fn provide(
        raw_context: *anyopaque,
        allocator: std.mem.Allocator,
        roots: []const DefOps.UnresolvedDummyRoot,
        extra_used_deps: u55,
    ) anyerror!?[]DefOps.MaterializedDummyAssignment {
        const self: *HiddenWitnessProviderContext =
            @ptrCast(@alignCast(raw_context));
        return FreshSelect.materializeHiddenRoots(
            allocator,
            self.fresh,
            self.theorem,
            roots,
            0,
            &self.compared_exprs,
            &.{},
            extra_used_deps,
        );
    }
};

pub const ConversionContext = struct {
    allocator: std.mem.Allocator,
    theorem: *TheoremContext,
    registry: *RewriteRegistry,
    env: *const GlobalEnv,
    checked: *std.ArrayListUnmanaged(CheckedLine),
    scratch: *CompilerDiag.Scratch,
    debug: DebugConfig,
    /// Lets a rung name hidden def dummies with theorem variables. Null
    /// for a probe that may be abandoned, which must not allocate them.
    fresh: ?Inference.HiddenWitnessFreshContext = null,
};

/// What proves a conversion's source statement: an existing line or
/// hypothesis, or a rule application whose line is not appended yet. A
/// rung appends the rule line only once it has committed, so a failed rung
/// leaves the application's bindings and refs with the caller.
pub const Source = union(enum) {
    ref: CheckedRef,
    rule: RuleApplication,

    pub const RuleApplication = struct {
        rule_id: u32,
        bindings: []const ExprId,
        refs: []const CheckedRef,
    };
};

/// Turns `source`, a proof of `have`, into a proof of `want`, or returns
/// null when no rung relates them. This one ladder serves a hypothesis
/// reference, a line's stated conclusion and the theorem's final line, so
/// a statement accepted in one place is accepted in the others. The rungs,
/// in order: identity; definition unfolding; folding `want`'s definition
/// applications into `have`; normalizing both sides to a common target;
/// normalizing `have` and unfolding to `want`; unfolding `have` to the
/// normal form of `want`. A failed rung's lines are rolled back, and a rung
/// that throws hands over to the next.
pub fn convertTo(
    ctx: ConversionContext,
    source: Source,
    have: ExprId,
    want: ExprId,
) !?CheckedRef {
    if (have == want) return try materialize(ctx, source, have);

    if (try Inference.canConvertTransparent(
        ctx.allocator,
        ctx.theorem,
        ctx.env,
        want,
        have,
    )) {
        return try transport(
            ctx,
            want,
            have,
            try materialize(ctx, source, have),
        );
    }

    var provider_context: HiddenWitnessProviderContext = undefined;
    const provider: ?DefOps.HiddenWitnessProvider =
        if (ctx.fresh) |fresh| blk: {
            provider_context = .{
                .theorem = ctx.theorem,
                .fresh = fresh,
                .compared_exprs = .{ want, have },
            };
            break :blk provider_context.provider();
        } else null;

    // A rung that throws (a rewrite under a term with no @congr, say) only
    // rules itself out: a later rung may relate the two without that step.
    // The first such error, with its scratch detail, is reported if no rung
    // succeeds.
    var first_err: ?anyerror = null;
    inline for (.{
        convertFolded,
        convertNormalized,
        convertNormalizedThenUnfolded,
        convertUnfoldedToNormalForm,
    }) |rung| {
        const mark = ctx.checked.items.len;
        const rung_scratch = ctx.scratch.mark();
        if (rung(ctx, provider, source, have, want)) |maybe_ref| {
            if (maybe_ref) |ref| return ref;
        } else |err| {
            if (err == error.OutOfMemory) return err;
            if (first_err == null) {
                first_err = err;
            } else {
                ctx.scratch.discard(rung_scratch);
            }
        }
        CheckedIr.rollbackToMark(ctx.allocator, ctx.checked, mark);
    }
    if (first_err) |err| return err;
    return null;
}

/// Appends a rule application whose rule derives `derived`, converted to
/// the conclusion the line states. Returns the index of the line proving
/// `stated`, or null with nothing appended.
pub fn tryBuildConclusionLine(
    ctx: ConversionContext,
    stated: ExprId,
    derived: ExprId,
    rule_id: u32,
    bindings: []const ExprId,
    refs: []const CheckedRef,
) !?usize {
    const ref = try convertTo(ctx, .{ .rule = .{
        .rule_id = rule_id,
        .bindings = bindings,
        .refs = refs,
    } }, derived, stated) orelse return null;
    return ref.line;
}

fn materialize(
    ctx: ConversionContext,
    source: Source,
    have: ExprId,
) !CheckedRef {
    return switch (source) {
        .ref => |ref| ref,
        .rule => |app| .{ .line = try appendRuleLine(
            ctx.checked,
            ctx.allocator,
            have,
            app.rule_id,
            app.bindings,
            app.refs,
        ) },
    };
}

fn transport(
    ctx: ConversionContext,
    target: ExprId,
    source_expr: ExprId,
    source_ref: CheckedRef,
) !CheckedRef {
    return .{ .line = try appendTransportLine(
        ctx.checked,
        ctx.allocator,
        target,
        source_expr,
        source_ref,
    ) };
}

/// `want` may keep a definition folded where `have` has its body: fold
/// those definition applications into `have`, unfold back to it, and
/// normalize the folded statement to `want`.
fn convertFolded(
    ctx: ConversionContext,
    provider: ?DefOps.HiddenWitnessProvider,
    source: Source,
    have: ExprId,
    want: ExprId,
) !?CheckedRef {
    var folder: Folder = .{ .ctx = ctx };
    defer folder.memo.deinit(ctx.allocator);
    const intermediate = try folder.fold(have, want) orelse return null;
    if (intermediate == have) return null;
    if (!try Inference.canConvertTransparent(
        ctx.allocator,
        ctx.theorem,
        ctx.env,
        intermediate,
        have,
    )) return null;

    var conversion = if (intermediate == want)
        null
    else
        try Normalize.buildNormalizedConversionWithProviderAndDebug(
            ctx.allocator,
            ctx.theorem,
            ctx.registry,
            ctx.env,
            ctx.checked,
            ctx.scratch,
            intermediate,
            want,
            provider,
            ctx.debug,
        ) orelse return null;
    defer if (conversion) |*conversion_mut| conversion_mut.normalizer.deinit();

    const folded = try transport(
        ctx,
        intermediate,
        have,
        try materialize(ctx, source, have),
    );
    if (conversion) |*conversion_mut| {
        if (conversion_mut.conv_line_idx) |conv_idx| {
            return .{ .line = try conversion_mut.normalizer.emitTransport(
                conversion_mut.relation,
                want,
                intermediate,
                conv_idx,
                folded,
            ) };
        }
    }
    return folded;
}

fn convertNormalized(
    ctx: ConversionContext,
    provider: ?DefOps.HiddenWitnessProvider,
    source: Source,
    have: ExprId,
    want: ExprId,
) !?CheckedRef {
    var conversion = try Normalize.buildNormalizedConversionWithProviderAndDebug(
        ctx.allocator,
        ctx.theorem,
        ctx.registry,
        ctx.env,
        ctx.checked,
        ctx.scratch,
        have,
        want,
        provider,
        ctx.debug,
    ) orelse return null;
    defer conversion.normalizer.deinit();
    const source_ref = try materialize(ctx, source, have);
    const conv_idx = conversion.conv_line_idx orelse return source_ref;
    return .{ .line = try conversion.normalizer.emitTransport(
        conversion.relation,
        want,
        have,
        conv_idx,
        source_ref,
    ) };
}

/// `have` normalizes to a statement that unfolds to `want`.
fn convertNormalizedThenUnfolded(
    ctx: ConversionContext,
    provider: ?DefOps.HiddenWitnessProvider,
    source: Source,
    have: ExprId,
    want: ExprId,
) !?CheckedRef {
    _ = provider;
    var normalization = try Normalize.buildExpectedNormalizationWithDebug(
        ctx.allocator,
        ctx.theorem,
        ctx.registry,
        ctx.env,
        ctx.checked,
        ctx.scratch,
        have,
        ctx.debug,
    ) orelse return null;
    defer normalization.normalizer.deinit();
    const normalized = normalization.normalized_expr;
    if (!try Inference.canConvertTransparent(
        ctx.allocator,
        ctx.theorem,
        ctx.env,
        want,
        normalized,
    )) return null;

    const source_ref = try materialize(ctx, source, have);
    const normalized_ref: CheckedRef =
        if (normalization.conv_line_idx) |conv_idx| .{
            .line = try normalization.normalizer.emitTransport(
                normalization.relation,
                normalized,
                have,
                conv_idx,
                source_ref,
            ),
        } else source_ref;
    if (want == normalized) return normalized_ref;
    return try transport(ctx, want, normalized, normalized_ref);
}

/// `have` unfolds to the normal form of `want`.
fn convertUnfoldedToNormalForm(
    ctx: ConversionContext,
    provider: ?DefOps.HiddenWitnessProvider,
    source: Source,
    have: ExprId,
    want: ExprId,
) !?CheckedRef {
    _ = provider;
    var normalization = try Normalize.buildExpectedNormalizationWithDebug(
        ctx.allocator,
        ctx.theorem,
        ctx.registry,
        ctx.env,
        ctx.checked,
        ctx.scratch,
        want,
        ctx.debug,
    ) orelse return null;
    defer normalization.normalizer.deinit();
    const normalized = normalization.normalized_expr;
    if (!try Inference.canConvertTransparent(
        ctx.allocator,
        ctx.theorem,
        ctx.env,
        normalized,
        have,
    )) return null;

    const source_ref = try materialize(ctx, source, have);
    const normalized_ref = if (have == normalized)
        source_ref
    else
        try transport(ctx, normalized, have, source_ref);
    const conv_idx = normalization.conv_line_idx orelse return normalized_ref;
    const symm_idx = try normalization.normalizer.emitSymm(
        normalization.relation,
        want,
        normalized,
        conv_idx,
    );
    return .{ .line = try normalization.normalizer.emitTransport(
        normalization.relation,
        want,
        normalized,
        symm_idx,
        normalized_ref,
    ) };
}

/// Rebuilds `raw` with the definition applications of `user` folded back
/// in wherever the two walk in step. Memoized on the pair, since both may
/// share subterms.
const Folder = struct {
    ctx: ConversionContext,
    memo: std.AutoHashMapUnmanaged([2]ExprId, ?ExprId) = .empty,

    fn fold(self: *Folder, raw: ExprId, user: ExprId) anyerror!?ExprId {
        if (raw == user) return null;
        const key: [2]ExprId = .{ raw, user };
        if (self.memo.get(key)) |cached| return cached;
        const result = try self.foldUncached(raw, user);
        try self.memo.put(self.ctx.allocator, key, result);
        return result;
    }

    fn foldUncached(self: *Folder, raw: ExprId, user: ExprId) !?ExprId {
        const ctx = self.ctx;
        if (isDefinitionApp(ctx.env, ctx.theorem, user)) {
            if (try Inference.canConvertTransparent(
                ctx.allocator,
                ctx.theorem,
                ctx.env,
                user,
                raw,
            )) return user;
        }

        if (try foldAcuiLeaf(ctx, raw, user)) |folded| return folded;

        const raw_node = ctx.theorem.interner.node(raw);
        const user_node = ctx.theorem.interner.node(user);
        if (raw_node.* != .app or user_node.* != .app) return null;
        const raw_app = raw_node.app;
        const user_app = user_node.app;
        if (raw_app.term_id != user_app.term_id) return null;
        if (raw_app.args.len != user_app.args.len) return null;

        var changed = false;
        const new_args = try ctx.allocator.dupe(ExprId, raw_app.args);
        defer ctx.allocator.free(new_args);
        for (raw_app.args, user_app.args, 0..) |raw_arg, user_arg, idx| {
            if (try self.fold(raw_arg, user_arg)) |folded_arg| {
                new_args[idx] = folded_arg;
                changed = true;
            }
        }
        if (!changed) return null;
        return try ctx.theorem.interner.internApp(raw_app.term_id, new_args);
    }
};

/// Under a shared ACUI combiner, replaces the first leaf of `raw` that a
/// definition-application item of `user` unfolds to.
fn foldAcuiLeaf(
    ctx: ConversionContext,
    raw: ExprId,
    user: ExprId,
) !?ExprId {
    var support = AcuiSupport.Context.init(
        ctx.allocator,
        ctx.theorem,
        ctx.env,
        ctx.registry,
    );
    defer support.deinit();
    const acui = try support.sharedStructuralCombiner(raw, user) orelse {
        return null;
    };

    var user_items = std.ArrayListUnmanaged(ExprId).empty;
    defer user_items.deinit(ctx.allocator);
    try support.collectConcreteSetItems(user, acui, &user_items);
    var def_items = std.ArrayListUnmanaged(ExprId).empty;
    defer def_items.deinit(ctx.allocator);
    for (user_items.items) |item| {
        if (isDefinitionApp(ctx.env, ctx.theorem, item)) {
            try def_items.append(ctx.allocator, item);
        }
    }
    if (def_items.items.len == 0) return null;

    var raw_items = std.ArrayListUnmanaged(AcuiSupport.LeafInfo).empty;
    defer raw_items.deinit(ctx.allocator);
    try support.collectLeafInfos(raw, acui.head_term_id, &raw_items);

    for (raw_items.items) |raw_leaf| {
        for (def_items.items) |def_item| {
            if (raw_leaf.expr_id == def_item) continue;
            if (!try Inference.canConvertTransparent(
                ctx.allocator,
                ctx.theorem,
                ctx.env,
                def_item,
                raw_leaf.expr_id,
            )) continue;
            var replaced = false;
            return try replaceFirstAcuiLeaf(
                ctx.allocator,
                ctx.theorem,
                raw,
                acui.head_term_id,
                raw_leaf.expr_id,
                def_item,
                &replaced,
            );
        }
    }
    return null;
}

fn replaceFirstAcuiLeaf(
    allocator: std.mem.Allocator,
    theorem: *TheoremContext,
    expr: ExprId,
    head_term_id: u32,
    old_leaf: ExprId,
    new_leaf: ExprId,
    replaced: *bool,
) !ExprId {
    if (!replaced.* and expr == old_leaf) {
        replaced.* = true;
        return new_leaf;
    }
    const node = theorem.interner.node(expr);
    if (node.* != .app) return expr;
    const app = node.app;
    if (app.term_id != head_term_id or app.args.len != 2) return expr;

    var new_args = try allocator.dupe(ExprId, app.args);
    defer allocator.free(new_args);
    new_args[0] = try replaceFirstAcuiLeaf(
        allocator,
        theorem,
        app.args[0],
        head_term_id,
        old_leaf,
        new_leaf,
        replaced,
    );
    new_args[1] = try replaceFirstAcuiLeaf(
        allocator,
        theorem,
        app.args[1],
        head_term_id,
        old_leaf,
        new_leaf,
        replaced,
    );
    if (!replaced.*) return expr;
    return try theorem.interner.internApp(app.term_id, new_args);
}

fn isDefinitionApp(
    env: *const GlobalEnv,
    theorem: *TheoremContext,
    expr: ExprId,
) bool {
    const node = theorem.interner.node(expr);
    const app = switch (node.*) {
        .app => |value| value,
        .variable, .placeholder => return false,
    };
    if (app.term_id >= env.terms.items.len) return false;
    return env.terms.items[app.term_id].is_def;
}
