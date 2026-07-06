//! Necessary-condition prefilter on the ACUI *context* of deduction rules.
//!
//! Deduction rules in an ACUI-context theory have conclusions like
//! `g , h ⊢ r` = `nd(join(g, h), r)`, where the context `join(g, h)` is an
//! associative/commutative/idempotent/unit combiner (`@acui`) whose members are
//! the active hypotheses. For the rule to apply, that conclusion context must
//! ACUI-equal the goal context. A hypothesis context can have extra members
//! only when the rule discharges them.
//!
//! The prune counts extra rigid context members for both view rules and raw
//! rules whose conclusion carries a bare context binder (`G ⊢ a`) and whose
//! hypotheses reveal the combiner (`G, p ⊢ a`). For raw rules it keeps the
//! discharged member templates and, when the current search bindings are
//! available, requires each absent ref-context member to be compatible with one
//! of those templates. That cuts the `inst`-style false positives where any one
//! extra assumption fits the numeric discharge budget even when it is not the
//! equation the rule can discharge.
//!
//! Soundness is deliberately conservative:
//!   * members compared to the goal are counted only when they have a rigid app
//!     head; variables and reducible heads are no-opinion;
//!   * a discharged template is budgeted as one concrete member only when it is
//!     a rigid, non-ACUI, non-`@rewrite`, non-def app; a non-carried bare binder
//!     or reducible member makes the whole hypothesis abstain;
//!   * template-shape pruning is only an added filter. If the shape comparison
//!     cannot prove a definite mismatch, the member is considered compatible.
//! Read-only; no interning or placeholder minting.

const std = @import("std");
const ExprId = @import("../../expr.zig").ExprId;
const TheoremContext = @import("../../expr.zig").TheoremContext;
const TemplateExpr = @import("../../rules.zig").TemplateExpr;
const ArgInfo = @import("../../parse_recovery.zig").ArgInfo;
const env_mod = @import("../../env.zig");
const ViewDecl = @import("../views.zig").ViewDecl;
const types = @import("./types.zig");
const Context = types.Context;
const def_match = @import("./backward/def_match.zig");
const semantic = @import("./backward/semantic.zig");
const OpenTerms = @import("../inference/open_terms.zig");
const Fill = @import("./abstract_prune.zig").Fill;

const max_hyps = 24;
const max_members = 64;
const max_binders = 128;
const max_discharged_members = 8;

pub const Info = struct {
    turnstile_term_id: u32,
    ctx_arg_index: u32,
    acui_head_id: u32,
    unit_term_id: ?u32,
    num_hyps: usize,
    /// Per hypothesis discharge budget (max ref-context members that may be
    /// absent from the goal context). `null` = abstain on this hypothesis.
    hyp_budgets: [max_hyps]?u8,
    /// The discharged member templates. Only meaningful when `hyp_budgets[i]`
    /// is non-null; the length is equal to that budget.
    discharged: [max_hyps][max_discharged_members]TemplateExpr,
    /// Parallel to `discharged`: whether that template mentions a bound binder.
    discharged_has_bound: [max_hyps][max_discharged_members]bool,
};

pub fn analyzeView(context: *const Context, view: ViewDecl) ?Info {
    return analyzeTemplates(
        context,
        view.concl,
        view.hyps,
        view.arg_infos,
        view.num_binders,
    );
}

pub fn analyzeRule(context: *const Context, rule: env_mod.RuleDecl) ?Info {
    return analyzeTemplates(
        context,
        rule.concl,
        rule.hyps,
        rule.args,
        rule.args.len,
    );
}

/// Statically analyse conclusion/hypothesis context structure. Returns null
/// when there is no ACUI context position we can reason about.
pub fn analyzeTemplates(
    context: *const Context,
    concl: TemplateExpr,
    hyps: []const TemplateExpr,
    arg_infos: []const ArgInfo,
    num_binders: usize,
) ?Info {
    if (hyps.len > max_hyps) return null;
    if (num_binders > max_binders) return null;
    if (concl != .app) return null;
    const turnstile = concl.app.term_id;

    const site = findContextSite(context, concl, hyps, arg_infos) orelse
        return null;
    const k = site.ctx_arg_index;
    const acui_head = site.acui_head_id;
    const unit = unitId(context, acui_head);

    var concl_members: [max_members]TemplateExpr = undefined;
    var concl_len: usize = 0;
    if (!flattenAcuiTemplate(
        concl.app.args[k],
        acui_head,
        &concl_members,
        &concl_len,
    )) return null;

    var info = Info{
        .turnstile_term_id = turnstile,
        .ctx_arg_index = @intCast(k),
        .acui_head_id = acui_head,
        .unit_term_id = unit,
        .num_hyps = hyps.len,
        .hyp_budgets = [_]?u8{null} ** max_hyps,
        .discharged = undefined,
        .discharged_has_bound = undefined,
    };
    for (hyps, 0..) |h, i| {
        info.hyp_budgets[i] = hypBudget(
            context,
            h,
            turnstile,
            k,
            acui_head,
            unit,
            concl_members[0..concl_len],
            arg_infos,
            &info.discharged[i],
            &info.discharged_has_bound[i],
        );
    }
    return info;
}

const ContextSite = struct { ctx_arg_index: usize, acui_head_id: u32 };

fn findContextSite(
    context: *const Context,
    concl: TemplateExpr,
    hyps: []const TemplateExpr,
    arg_infos: []const ArgInfo,
) ?ContextSite {
    std.debug.assert(concl == .app);
    const turnstile = concl.app.term_id;

    for (concl.app.args, 0..) |arg, i| {
        if (templateAcuiHead(context, arg)) |head| {
            return .{ .ctx_arg_index = i, .acui_head_id = head };
        }
    }

    for (hyps) |h| {
        if (h != .app or h.app.term_id != turnstile) continue;
        const limit = @min(concl.app.args.len, h.app.args.len);
        for (0..limit) |i| {
            const head = templateAcuiHead(context, h.app.args[i]) orelse
                continue;
            if (!sameTemplateSort(
                context,
                concl.app.args[i],
                h.app.args[i],
                arg_infos,
            )) continue;
            return .{ .ctx_arg_index = i, .acui_head_id = head };
        }
    }
    return null;
}

fn templateAcuiHead(context: *const Context, t: TemplateExpr) ?u32 {
    if (t != .app) return null;
    if (context.registry.acui_by_head.contains(t.app.term_id)) return t.app.term_id;
    return null;
}

fn sameTemplateSort(
    context: *const Context,
    a: TemplateExpr,
    b: TemplateExpr,
    arg_infos: []const ArgInfo,
) bool {
    const sa = templateSortName(context, a, arg_infos) orelse return false;
    const sb = templateSortName(context, b, arg_infos) orelse return false;
    return std.mem.eql(u8, sa, sb);
}

fn templateSortName(
    context: *const Context,
    t: TemplateExpr,
    arg_infos: []const ArgInfo,
) ?[]const u8 {
    return switch (t) {
        .binder => |vi| if (vi < arg_infos.len) arg_infos[vi].sort_name else null,
        .app => |a| if (a.term_id < context.env.terms.items.len)
            context.env.terms.items[a.term_id].ret_sort_name
        else
            null,
    };
}

fn unitId(context: *const Context, acui_head: u32) ?u32 {
    const combiner = context.registry.acui_by_head.get(acui_head) orelse return null;
    if (combiner.unit_term_id) |u| return u;
    return context.env.term_names.get(combiner.unit_term_name);
}

/// Discharge budget for one hypothesis: the count of context-member templates
/// that are NOT carried into the conclusion context, provided each is a rigid
/// single-member shape. Returns null (abstain) when any member could expand to an
/// unbounded number of concrete members (a non-carried bare binder, an ACUI head,
/// or a reducible head), or the hypothesis has no analysable context position.
fn hypBudget(
    context: *const Context,
    h: TemplateExpr,
    turnstile: u32,
    k: usize,
    acui_head: u32,
    unit: ?u32,
    concl_members: []const TemplateExpr,
    arg_infos: []const ArgInfo,
    discharged: *[max_discharged_members]TemplateExpr,
    discharged_has_bound: *[max_discharged_members]bool,
) ?u8 {
    if (h != .app or h.app.term_id != turnstile or k >= h.app.args.len) return null;
    var members: [max_members]TemplateExpr = undefined;
    var len: usize = 0;
    if (!flattenAcuiTemplate(h.app.args[k], acui_head, &members, &len)) return null;

    var budget: u8 = 0;
    for (members[0..len]) |m| {
        if (templateIsUnit(m, unit)) continue;
        if (templateCarriedByConclusion(m, concl_members)) continue;

        switch (m) {
            .binder => return null,
            .app => |a| {
                // A discharged member is budgeted as exactly one concrete member
                // only if it is rigid (non-ACUI, non-def, non-`@rewrite`);
                // anything reducible could unfold/rearrange to several members.
                if (context.registry.acui_by_head.contains(a.term_id)) return null;
                if (semantic.termNeedsSemantic(context, a.term_id)) return null;
                if (budget >= max_discharged_members) return null;
                discharged[budget] = m;
                discharged_has_bound[budget] = templateHasBoundBinder(
                    m,
                    arg_infos,
                );
                budget += 1;
            },
        }
    }
    return budget;
}

fn templateIsUnit(t: TemplateExpr, unit: ?u32) bool {
    const u = unit orelse return false;
    return t == .app and t.app.term_id == u and t.app.args.len == 0;
}

fn templateCarriedByConclusion(
    member: TemplateExpr,
    concl_members: []const TemplateExpr,
) bool {
    for (concl_members) |candidate| {
        if (templateEqual(member, candidate)) return true;
    }
    return false;
}

fn templateHasBoundBinder(
    template: TemplateExpr,
    arg_infos: []const ArgInfo,
) bool {
    switch (template) {
        .binder => |idx| return idx < arg_infos.len and arg_infos[idx].bound,
        .app => |app| {
            for (app.args) |arg| {
                if (templateHasBoundBinder(arg, arg_infos)) return true;
            }
            return false;
        },
    }
}

fn templateEqual(a: TemplateExpr, b: TemplateExpr) bool {
    switch (a) {
        .binder => |ai| return b == .binder and b.binder == ai,
        .app => |aa| {
            if (b != .app) return false;
            if (aa.term_id != b.app.term_id) return false;
            if (aa.args.len != b.app.args.len) return false;
            for (aa.args, b.app.args) |la, rb| {
                if (!templateEqual(la, rb)) return false;
            }
            return true;
        },
    }
}

fn flattenAcuiTemplate(
    t: TemplateExpr,
    acui_head: u32,
    out: *[max_members]TemplateExpr,
    len: *usize,
) bool {
    switch (t) {
        .app => |a| {
            if (a.term_id == acui_head) {
                for (a.args) |arg| {
                    if (!flattenAcuiTemplate(arg, acui_head, out, len)) return false;
                }
                return true;
            }
        },
        else => {},
    }
    if (len.* >= out.len) return false;
    out[len.*] = t;
    len.* += 1;
    return true;
}

/// True when, for some assigned hypothesis, the ref's context contributes more
/// rigid members absent from the goal context than the rule can discharge, or a
/// binding-aware discharged template shape makes such a member impossible.
pub fn contextInfeasible(
    theorem: *TheoremContext,
    context: *const Context,
    info: Info,
    goal_expr: ?ExprId,
    fills: []const Fill,
    bindings: ?[]const ?ExprId,
) bool {
    const g = goal_expr orelse return false;
    const gn = theorem.interner.node(g);
    if (gn.* != .app or gn.app.term_id != info.turnstile_term_id) return false;
    if (info.ctx_arg_index >= gn.app.args.len) return false;

    var goal_members: [max_members]ExprId = undefined;
    var goal_len: usize = 0;
    if (!flattenAcuiExpr(
        theorem,
        gn.app.args[info.ctx_arg_index],
        info.acui_head_id,
        info.unit_term_id,
        &goal_members,
        &goal_len,
    )) return false;

    for (fills) |fill| {
        if (fill.hyp_index >= info.num_hyps) continue;
        const budget_u8 = info.hyp_budgets[fill.hyp_index] orelse continue;
        const budget: usize = budget_u8;
        const rn = theorem.interner.node(fill.ref_expr);
        if (rn.* != .app or rn.app.term_id != info.turnstile_term_id) continue;
        if (info.ctx_arg_index >= rn.app.args.len) continue;

        var ref_members: [max_members]ExprId = undefined;
        var ref_len: usize = 0;
        if (!flattenAcuiExpr(
            theorem,
            rn.app.args[info.ctx_arg_index],
            info.acui_head_id,
            info.unit_term_id,
            &ref_members,
            &ref_len,
        )) continue;

        var absent_members: [max_members]ExprId = undefined;
        var absent_len: usize = 0;
        for (ref_members[0..ref_len]) |m| {
            const mn = theorem.interner.node(m);
            // Only a rigid-headed app can be a definite mismatch. Variables (the
            // absorbing/ambient context binders) and reducible heads are
            // no-opinion — they might unify with or rewrite to a goal member.
            if (mn.* != .app) continue;
            if (def_match.rigidHeadOf(context, mn.app.term_id) == null) continue;
            if (memberPossiblyInList(context, theorem, m, goal_members[0..goal_len])) continue;
            appendDistinctExpr(&absent_members, &absent_len, m);
        }
        if (absent_len > budget) return true;
        if (bindings) |b| {
            const patterns = info.discharged[fill.hyp_index][0..budget];
            const has_bound = info.discharged_has_bound[fill.hyp_index][0..budget];
            if (!absentMembersFitPatterns(
                context,
                theorem,
                absent_members[0..absent_len],
                patterns,
                b,
            )) return true;
            if (!dischargedPatternsSupported(
                context,
                theorem,
                ref_members[0..ref_len],
                patterns,
                has_bound,
                b,
            )) return true;
        }
    }
    return false;
}

fn appendDistinctExpr(
    out: *[max_members]ExprId,
    len: *usize,
    item: ExprId,
) void {
    for (out[0..len.*]) |existing| {
        if (item == existing) return;
    }
    if (len.* >= out.len) return;
    out[len.*] = item;
    len.* += 1;
}

fn absentMembersFitPatterns(
    context: *const Context,
    theorem: *const TheoremContext,
    absent: []const ExprId,
    patterns: []const TemplateExpr,
    bindings: []const ?ExprId,
) bool {
    var used: [max_discharged_members]bool = [_]bool{false} ** max_discharged_members;
    return matchAbsentPattern(context, theorem, absent, patterns, bindings, &used, 0);
}

fn matchAbsentPattern(
    context: *const Context,
    theorem: *const TheoremContext,
    absent: []const ExprId,
    patterns: []const TemplateExpr,
    bindings: []const ?ExprId,
    used: *[max_discharged_members]bool,
    idx: usize,
) bool {
    if (idx >= absent.len) return true;
    for (patterns, 0..) |pattern, i| {
        if (i >= used.len or used[i]) continue;
        if (def_match.templateDefiniteMismatch(
            context,
            theorem,
            pattern,
            absent[idx],
            bindings,
        )) continue;
        used[i] = true;
        if (matchAbsentPattern(
            context,
            theorem,
            absent,
            patterns,
            bindings,
            used,
            idx + 1,
        )) return true;
        used[i] = false;
    }
    return false;
}

fn dischargedPatternsSupported(
    context: *const Context,
    theorem: *TheoremContext,
    ref_members: []const ExprId,
    patterns: []const TemplateExpr,
    patterns_have_bound: []const bool,
    bindings: []const ?ExprId,
) bool {
    for (patterns, 0..) |pattern, i| {
        const concrete = (OpenTerms.instantiateTemplateConcrete(
            theorem,
            pattern,
            bindings,
        ) catch return true) orelse {
            if (i >= patterns_have_bound.len or !patterns_have_bound[i]) continue;
            if (templateCouldBeHidden(theorem, ref_members)) continue;
            if (!templatePossiblyInList(context, theorem, pattern, ref_members, bindings)) {
                return false;
            }
            continue;
        };
        const deps = exprDeps(theorem, concrete) catch return true;
        const has_bound = exprHasBoundLeaf(theorem, concrete) catch return true;
        if (patternCouldBeHidden(theorem, ref_members, deps, has_bound)) continue;
        if (!memberPossiblyInList(context, theorem, concrete, ref_members)) {
            return false;
        }
    }
    return true;
}

fn templateCouldBeHidden(
    theorem: *const TheoremContext,
    ref_members: []const ExprId,
) bool {
    for (ref_members) |member| {
        switch (theorem.interner.node(member).*) {
            .variable, .placeholder => {
                const deps = exprDeps(theorem, member) catch return true;
                if (deps != 0) return true;
            },
            .app => {},
        }
    }
    return false;
}

fn templatePossiblyInList(
    context: *const Context,
    theorem: *const TheoremContext,
    pattern: TemplateExpr,
    list: []const ExprId,
    bindings: []const ?ExprId,
) bool {
    for (list) |candidate| {
        if (!def_match.templateDefiniteMismatch(
            context,
            theorem,
            pattern,
            candidate,
            bindings,
        )) return true;
    }
    return false;
}

fn patternCouldBeHidden(
    theorem: *const TheoremContext,
    ref_members: []const ExprId,
    pattern_deps: u55,
    pattern_has_bound_leaf: bool,
) bool {
    for (ref_members) |member| {
        const node = theorem.interner.node(member);
        switch (node.*) {
            .variable, .placeholder => {
                const deps = exprDeps(theorem, member) catch return true;
                if (pattern_has_bound_leaf and deps == 0) continue;
                if ((pattern_deps & ~deps) == 0) return true;
            },
            .app => {},
        }
    }
    return false;
}

fn exprDeps(theorem: *const TheoremContext, expr: ExprId) !u55 {
    return switch (theorem.interner.node(expr).*) {
        .variable, .placeholder => blk: {
            const info = (try theorem.currentLeafInfo(expr)) orelse break :blk 0;
            break :blk info.deps;
        },
        .app => |app| blk: {
            var deps: u55 = 0;
            for (app.args) |arg| deps |= try exprDeps(theorem, arg);
            break :blk deps;
        },
    };
}

fn exprHasBoundLeaf(theorem: *const TheoremContext, expr: ExprId) !bool {
    return switch (theorem.interner.node(expr).*) {
        .variable, .placeholder => blk: {
            const info = (try theorem.currentLeafInfo(expr)) orelse break :blk false;
            break :blk info.bound;
        },
        .app => |app| blk: {
            for (app.args) |arg| {
                if (try exprHasBoundLeaf(theorem, arg)) break :blk true;
            }
            break :blk false;
        },
    };
}

fn memberPossiblyInList(
    context: *const Context,
    theorem: *const TheoremContext,
    member: ExprId,
    list: []const ExprId,
) bool {
    for (list) |candidate| {
        if (!def_match.rigidExprMismatch(context, theorem, member, candidate)) {
            return true;
        }
    }
    return false;
}

fn flattenAcuiExpr(
    theorem: *const TheoremContext,
    e: ExprId,
    acui_head: u32,
    unit: ?u32,
    out: *[max_members]ExprId,
    len: *usize,
) bool {
    const n = theorem.interner.node(e);
    if (n.* == .app) {
        if (n.app.term_id == acui_head) {
            for (n.app.args) |arg| {
                if (!flattenAcuiExpr(theorem, arg, acui_head, unit, out, len)) return false;
            }
            return true;
        }
        if (unit) |u| {
            if (n.app.term_id == u and n.app.args.len == 0) return true;
        }
    }
    if (len.* >= out.len) return false;
    out[len.*] = e;
    len.* += 1;
    return true;
}
