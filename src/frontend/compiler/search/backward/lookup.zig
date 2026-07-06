//! Reference-index lookup for a hypothesis slot: turn a (rule, hyp, current
//! bindings) slot into its candidate reference pool — pool refs plus, when a
//! derived-ref index was requested, the derived candidates from the same shape
//! build — including the `@view` path and the sort resolution the index keys
//! on. Split out of `backtrack.zig`.

const std = @import("std");
const types = @import("../types.zig");
const clipper = @import("../clipper.zig");
const ref_index_mod = @import("../ref_index.zig");
const match = @import("./match.zig");
const ExprId = @import("../../../expr.zig").ExprId;
const TheoremContext = @import("../../../expr.zig").TheoremContext;
const TemplateExpr = @import("../../../rules.zig").TemplateExpr;
const ArgInfo = @import("../../../parse_recovery.zig").ArgInfo;
const GlobalEnv = @import("../../../env.zig").GlobalEnv;
const Context = types.Context;
const SearchCounters = types.SearchCounters;
const ApplyCandidate = types.ApplyCandidate;
const findRecoverSourceLocation = match.findRecoverSourceLocation;
const seedViewBindingsForMatch = match.seedViewBindingsForMatch;
const seedViewBindingsFromRule = match.seedViewBindingsFromRule;

/// A slot's reference lookup: pool-ref candidates plus (when a derived-ref
/// index was passed) the derived-ref candidates from the SAME shape build —
/// see `ref_index_mod.Index.DualLookup`. `derived` is null when no derived
/// index was requested or the lookup fell back to a sort scan; callers then
/// scan the whole derived pool.
pub const HypLookup = struct {
    pool: ref_index_mod.LookupResult,
    derived: ?ref_index_mod.LookupResult,

    pub fn deinit(self: *HypLookup) void {
        self.pool.deinit();
        if (self.derived) |*lookup| lookup.deinit();
        self.* = undefined;
    }
};

pub fn lookupHypReferences(
    context: *const Context,
    ref_index: *const ref_index_mod.Index,
    derived_index: ?*const ref_index_mod.Index,
    candidate: *const ApplyCandidate,
    bindings: []const ?ExprId,
    position: usize,
    phase: types.HypLookupPhase,
    depth: usize,
    count_total: bool,
    counters: ?*SearchCounters,
) !HypLookup {
    const rule = &context.env.rules.items[candidate.rule_id];
    const hyp = candidate.unresolved_hyps[position];
    const sort_id = try hypothesisSort(context.env, rule.*, hyp.index);
    var fallback = types.HypLookupFallback.none;
    // Prefer the view hypothesis shape when one is declared. The view is the
    // surface form refs are expected to take; the raw template may demand
    // structure (substitution heads, ACUI rearrangements) that only
    // materializes after normalization, which would empty the candidate
    // pool here even though the validator could accept it.
    const lookup: HypLookup = if (context.views.get(candidate.rule_id)) |view|
        try lookupHypReferencesViaView(
            context.allocator,
            ref_index,
            derived_index,
            &candidate.theorem,
            view,
            hyp.index,
            bindings,
            candidate.view_concl_seed,
            counters,
        )
    else blk: {
        const dual = ref_index.lookupTemplateDual(
            derived_index,
            &candidate.theorem,
            rule.hyps[hyp.index],
            rule.args,
            bindings,
            counters,
        ) catch |err| switch (err) {
            error.OutOfMemory => return err,
            else => {
                fallback = .template_error;
                break :blk .{
                    .pool = try ref_index.lookupSort(sort_id, true, counters),
                    .derived = null,
                };
            },
        };
        break :blk .{ .pool = dual.primary, .derived = dual.secondary };
    };
    if (lookup.pool.broad and fallback == .none) fallback = .broad_shape;
    if (counters) |actual| {
        if (count_total) {
            actual.per_hyp_filtered_ref_list_total += lookup.pool.indices.len;
        }
        actual.recordHypLookup(candidate.rule_name, .{
            .hyp_index = hyp.index,
            .depth = depth,
            .phase = phase,
            .filtered_len = lookup.pool.indices.len,
            .fallback = fallback,
        });
    }
    return lookup;
}

fn lookupHypReferencesViaView(
    allocator: std.mem.Allocator,
    ref_index: *const ref_index_mod.Index,
    derived_index: ?*const ref_index_mod.Index,
    theorem: *const TheoremContext,
    view: types.ViewDecl,
    hyp_index: usize,
    rule_bindings: []const ?ExprId,
    view_concl_seed: ?[]const ?ExprId,
    counters: ?*SearchCounters,
) !HypLookup {
    const view_bindings = try allocator.alloc(?ExprId, view.num_binders);
    defer allocator.free(view_bindings);
    seedViewBindingsFromRule(view, rule_bindings, view_bindings);

    // Push any resolvable `@recover` coupling into the index as a context-member
    // containment query (see `lookupTemplateInjected`). Only fires when the
    // recover source still sits in this hypothesis's ambiguous ACUI context but
    // its pattern and hole are already pinned by the conclusion or an
    // earlier-matched hypothesis.
    var inj_buf: [4]ref_index_mod.Index.RecoverMemberInjection = undefined;
    var inj_count: usize = 0;
    if (view.derived_bindings.len > 0) {
        const seed_bindings = try allocator.alloc(?ExprId, view.num_binders);
        defer allocator.free(seed_bindings);
        seedViewBindingsForMatch(
            view,
            rule_bindings,
            view_concl_seed,
            seed_bindings,
        );
        for (view.derived_bindings) |derived| {
            if (inj_count >= inj_buf.len) break;
            const rec = switch (derived) {
                .recover => |r| r,
                .abstract => continue,
            };
            if (rec.target_view_idx >= seed_bindings.len) continue;
            if (rec.source_view_idx >= seed_bindings.len) continue;
            if (rec.pattern_view_idx >= seed_bindings.len) continue;
            if (rec.hole_view_idx >= seed_bindings.len) continue;
            // Same load-bearing rule as the per-hyp recover guard: validation
            // skips a recover law whose target is already pinned, so this
            // lookup-time injection would be an unsound prune in that state.
            if (seed_bindings[rec.target_view_idx] != null) continue;
            // A pinned source is already judged by the per-hyp recover guard.
            if (seed_bindings[rec.source_view_idx] != null) continue;
            const pattern = seed_bindings[rec.pattern_view_idx] orelse continue;
            const hole = seed_bindings[rec.hole_view_idx] orelse continue;
            const loc = findRecoverSourceLocation(
                ref_index.context,
                view,
                rec.source_view_idx,
            ) orelse continue;
            if (loc.hyp_index != hyp_index) continue;
            inj_buf[inj_count] = .{
                .turnstile_term_id = loc.turnstile_term_id,
                .ctx_arg_index = loc.ctx_arg_index,
                .wrapper_term_id = loc.wrapper_term_id,
                .pattern = pattern,
                .hole = hole,
            };
            inj_count += 1;
            if (counters) |actual| actual.recover_member_injections += 1;
        }
    }

    if (inj_count == 0) {
        const dual = try ref_index.lookupTemplateDual(
            derived_index,
            theorem,
            view.hyps[hyp_index],
            view.arg_infos,
            view_bindings,
            counters,
        );
        return .{ .pool = dual.primary, .derived = dual.secondary };
    }
    const dual = try ref_index.lookupTemplateInjectedDual(
        derived_index,
        theorem,
        view.hyps[hyp_index],
        view.arg_infos,
        view_bindings,
        inj_buf[0..inj_count],
        counters,
    );
    return .{ .pool = dual.primary, .derived = dual.secondary };
}

fn hypothesisSort(
    env: *const GlobalEnv,
    rule: @import("../../../env.zig").RuleDecl,
    hyp_index: usize,
) !clipper.SortId {
    if (hyp_index >= rule.hyps.len) return error.UnknownHypothesis;
    return templateSort(env, rule.hyps[hyp_index], rule.args);
}

fn templateSort(
    env: *const GlobalEnv,
    template: TemplateExpr,
    args: []const ArgInfo,
) !clipper.SortId {
    const sort_name = switch (template) {
        .app => |app| blk: {
            if (!env.hasAvailableTerm(app.term_id)) return error.UnknownTerm;
            break :blk env.terms.items[app.term_id].ret_sort_name;
        },
        .binder => |idx| blk: {
            if (idx >= args.len) return error.UnknownTemplateBinder;
            break :blk args[idx].sort_name;
        },
    };
    const sort_id = env.sort_names.get(sort_name) orelse return error.UnknownSort;
    return @intCast(sort_id);
}
