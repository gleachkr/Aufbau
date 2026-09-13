const std = @import("std");
const GlobalEnv = @import("./env.zig").GlobalEnv;
const ExprId = @import("./expr.zig").ExprId;
const ExprNode = @import("./expr.zig").ExprNode;
const TheoremContext = @import("./expr.zig").TheoremContext;
const RewriteRegistry = @import("./rewrite_registry.zig").RewriteRegistry;
const Canonicalizer = @import("./canonicalizer.zig").Canonicalizer;
const BindingValidation = @import("./binding_validation.zig");
const DefOps = @import("./def_ops.zig");
const BindingSeed = DefOps.BindingSeed;
const BoundValue = @import("./def_ops/types.zig").BoundValue;
const SymbolicExpr = @import("./def_ops/types.zig").SymbolicExpr;
const ViewTrace = @import("./view_trace.zig");
const TemplateExpr = @import("./rules.zig").TemplateExpr;

pub const RecoverDecl = struct {
    target_view_idx: usize,
    source_view_idx: usize,
    pattern_view_idx: usize,
    hole_view_idx: usize,
    /// Declared sort of the target binder. Equal to the hole binder's sort
    /// for classic enrollments; for cross-sort enrollments (sorts meeting in
    /// the coercion graph) the walk re-sorts recovered subtrees to this sort.
    target_sort_name: []const u8,
};

/// One plug slot of `@abstract`. A bare binder name is the trivial template
/// `.binder`; a `$ … $` pattern is a template over the view binders.
pub const AbstractPlug = struct {
    template: TemplateExpr,
    /// True for a `$ … $` pattern: it is matched at walk sites and may solve
    /// the view binders it mentions. False for a bare name: the binder's
    /// resolved value is the plug and must be solved before the walk runs.
    pattern: bool,
    /// Declared sort of the plug: the binder's sort, or the pattern's sort.
    sort_name: []const u8,

    /// The view binder index of a bare-name plug.
    pub fn bareBinder(self: AbstractPlug) ?usize {
        if (self.pattern) return null;
        return self.template.binder;
    }
};

pub const AbstractDecl = struct {
    target_view_idx: usize,
    left_view_idx: usize,
    right_view_idx: usize,
    hole_view_idx: usize,
    left_plug: AbstractPlug,
    right_plug: AbstractPlug,

    pub fn hasPattern(self: AbstractDecl) bool {
        return self.left_plug.pattern or self.right_plug.pattern;
    }
};

pub const DerivedBinding = union(enum) {
    recover: RecoverDecl,
    abstract: AbstractDecl,
};

/// Marks every view binder the derived bindings may solve: each target, plus
/// the binders an `@abstract` plug pattern mentions (solved at its sites).
pub fn markSolvedBinders(bindings: []const DerivedBinding, out: []bool) void {
    for (bindings) |binding| switch (binding) {
        .recover => |recover| out[recover.target_view_idx] = true,
        .abstract => |abstract| {
            out[abstract.target_view_idx] = true;
            if (abstract.left_plug.pattern) {
                markTemplateBinders(abstract.left_plug.template, out);
            }
            if (abstract.right_plug.pattern) {
                markTemplateBinders(abstract.right_plug.template, out);
            }
        },
    };
}

/// A runtime failure of `@recover` / `@abstract`: the view matched, but the
/// derived binding could not be read off the solved expressions. Such a
/// failure names the real cause of a binder the view was meant to solve.
pub fn isDerivedBindingFailure(err: anyerror) bool {
    return switch (err) {
        error.AbstractConflict,
        error.AbstractNoPlugOccurrence,
        error.AbstractPatternConflict,
        error.AbstractPatternNoSite,
        error.AbstractStructureMismatch,
        error.RecoverConflict,
        error.RecoverHoleNotFound,
        error.RecoverStructureMismatch,
        => true,
        else => false,
    };
}

fn markTemplateBinders(template: TemplateExpr, out: []bool) void {
    switch (template) {
        .binder => |idx| out[idx] = true,
        .app => |app| for (app.args) |arg| markTemplateBinders(arg, out),
    }
}

const ApplyResult = enum {
    no_progress,
    progress,
};

/// Immutable view-match state consumed by @recover / @abstract.
/// This captures the currently resolved structure before representative
/// projection rewrites it into semantic representatives.
pub const MatchSnapshot = struct {
    dummy_witnesses: ?[]const ?ExprId = null,
    view_bindings: []?ExprId,
    view_seeds: ?[]const BindingSeed = null,
};

const preprocess_max_depth: usize = 32;

pub fn applyDerivedBindings(
    theorem: *TheoremContext,
    env: *const GlobalEnv,
    registry: *RewriteRegistry,
    snapshot: MatchSnapshot,
    derived_bindings: []const DerivedBinding,
    view_arg_names: []const ?[]const u8,
    debug_views: bool,
) !void {
    var changed = true;
    while (changed) {
        changed = false;
        for (derived_bindings) |binding| {
            switch (try applyDerivedBinding(
                theorem,
                env,
                registry,
                snapshot,
                binding,
                view_arg_names,
                debug_views,
            )) {
                .no_progress => {},
                .progress => changed = true,
            }
        }
    }
}

fn applyDerivedBinding(
    theorem: *TheoremContext,
    env: *const GlobalEnv,
    registry: *RewriteRegistry,
    snapshot: MatchSnapshot,
    binding: DerivedBinding,
    view_arg_names: []const ?[]const u8,
    debug_views: bool,
) !ApplyResult {
    return switch (binding) {
        .recover => |recover| try applyRecoverBinding(
            theorem,
            env,
            registry,
            snapshot,
            recover,
            view_arg_names,
            debug_views,
        ),
        .abstract => |abstract| try applyAbstractBinding(
            theorem,
            env,
            registry,
            snapshot.view_bindings,
            abstract,
        ),
    };
}

fn applyRecoverBinding(
    theorem: *TheoremContext,
    env: *const GlobalEnv,
    registry: *RewriteRegistry,
    snapshot: MatchSnapshot,
    recover: RecoverDecl,
    view_arg_names: []const ?[]const u8,
    debug_views: bool,
) !ApplyResult {
    const view_bindings = snapshot.view_bindings;
    const view_seeds = snapshot.view_seeds;

    if (view_bindings[recover.target_view_idx] != null) {
        return .no_progress;
    }
    if (debug_views) {
        try ViewTrace.printRecoverState(
            theorem.allocator,
            theorem,
            env,
            view_arg_names,
            recover.target_view_idx,
            recover.source_view_idx,
            recover.pattern_view_idx,
            recover.hole_view_idx,
            view_bindings,
            view_seeds,
        );
    }

    const source_expr = view_bindings[recover.source_view_idx] orelse {
        return .no_progress;
    };
    const hole_expr = view_bindings[recover.hole_view_idx];

    if (view_bindings[recover.pattern_view_idx]) |pattern_expr| {
        if (hole_expr) |concrete_hole_expr| {
            if (try concreteRecoverCandidate(
                theorem,
                env,
                registry,
                source_expr,
                pattern_expr,
                concrete_hole_expr,
                recover.target_sort_name,
                debug_views,
            )) |candidate| {
                view_bindings[recover.target_view_idx] = candidate;
                return .progress;
            }
            if (debug_views) {
                ViewTrace.printMessage(
                    "concrete recover did not expose the hole; " ++
                        "trying symbolic seed",
                    .{},
                );
            }
        } else if (debug_views) {
            ViewTrace.printMessage(
                "concrete recover skipped; hole has only symbolic seed",
                .{},
            );
        }
    }

    const seeds = view_seeds orelse return .no_progress;
    if (recover.pattern_view_idx >= seeds.len or
        recover.hole_view_idx >= seeds.len)
    {
        return .no_progress;
    }
    if (hole_expr == null and seeds[recover.hole_view_idx] == .none) {
        return .no_progress;
    }

    var candidate: ?ExprId = null;
    var skipped_equal_hole = false;
    var dummy_bindings: std.AutoHashMapUnmanaged(usize, ExprId) = .empty;
    defer dummy_bindings.deinit(theorem.allocator);

    const found = recoverBindingCandidateFromSeed(
        theorem,
        env,
        snapshot.dummy_witnesses,
        source_expr,
        seeds[recover.pattern_view_idx],
        recover.hole_view_idx,
        hole_expr,
        seeds[recover.hole_view_idx],
        recover.target_sort_name,
        view_bindings,
        seeds,
        &dummy_bindings,
        &candidate,
        &skipped_equal_hole,
    ) catch |err| switch (err) {
        error.RecoverStructureMismatch => blk: {
            skipped_equal_hole = false;
            break :blk false;
        },
        else => return err,
    };
    const source_matches_pattern =
        if (view_bindings[recover.pattern_view_idx]) |pattern_expr|
            source_expr == pattern_expr
        else
            false;
    if (!found and !skipped_equal_hole and !source_matches_pattern) {
        if (debug_views) {
            ViewTrace.printMessage(
                "symbolic recover did not find hole",
                .{},
            );
        }
        if (hole_expr == null) {
            return .no_progress;
        }
        return error.RecoverHoleNotFound;
    }

    if (!found) {
        candidate = hole_expr orelse return .no_progress;
    }

    if (debug_views) {
        ViewTrace.printMessage(
            "symbolic recover found hole",
            .{},
        );
    }
    view_bindings[recover.target_view_idx] = candidate;
    return .progress;
}

fn recoverBindingCandidateFromSeed(
    theorem: *const TheoremContext,
    env: *const GlobalEnv,
    dummy_witnesses: ?[]const ?ExprId,
    source_expr: ExprId,
    seed: BindingSeed,
    hole_view_idx: usize,
    hole_expr: ?ExprId,
    hole_seed: BindingSeed,
    target_sort: []const u8,
    view_bindings: []const ?ExprId,
    view_seeds: []const BindingSeed,
    dummy_bindings: *std.AutoHashMapUnmanaged(usize, ExprId),
    candidate: *?ExprId,
    skipped_equal_hole: *bool,
) anyerror!bool {
    return switch (seed) {
        .none => false,
        .exact => |expr_id| blk: {
            const concrete_hole_expr = hole_expr orelse break :blk false;
            break :blk try recoverBindingCandidate(
                theorem,
                env,
                source_expr,
                expr_id,
                concrete_hole_expr,
                target_sort,
                candidate,
                skipped_equal_hole,
            );
        },
        .semantic => |semantic| blk: {
            const concrete_hole_expr = hole_expr orelse break :blk false;
            break :blk try recoverBindingCandidate(
                theorem,
                env,
                source_expr,
                semantic.expr_id,
                concrete_hole_expr,
                target_sort,
                candidate,
                skipped_equal_hole,
            );
        },
        .bound => |bound| try recoverBindingCandidateFromBoundValue(
            theorem,
            env,
            dummy_witnesses,
            source_expr,
            bound,
            hole_view_idx,
            hole_expr,
            hole_seed,
            target_sort,
            view_bindings,
            view_seeds,
            dummy_bindings,
            candidate,
            skipped_equal_hole,
        ),
    };
}

fn recoverBindingCandidateFromBoundValue(
    theorem: *const TheoremContext,
    env: *const GlobalEnv,
    dummy_witnesses: ?[]const ?ExprId,
    source_expr: ExprId,
    bound: BoundValue,
    hole_view_idx: usize,
    hole_expr: ?ExprId,
    hole_seed: BindingSeed,
    target_sort: []const u8,
    view_bindings: []const ?ExprId,
    view_seeds: []const BindingSeed,
    dummy_bindings: *std.AutoHashMapUnmanaged(usize, ExprId),
    candidate: *?ExprId,
    skipped_equal_hole: *bool,
) anyerror!bool {
    return switch (bound) {
        .concrete => |concrete| blk: {
            const concrete_hole_expr = hole_expr orelse break :blk false;
            break :blk try recoverBindingCandidate(
                theorem,
                env,
                source_expr,
                concrete.raw,
                concrete_hole_expr,
                target_sort,
                candidate,
                skipped_equal_hole,
            );
        },
        .symbolic => |symbolic| try recoverBindingCandidateSymbolic(
            theorem,
            env,
            dummy_witnesses,
            source_expr,
            symbolic.expr,
            hole_view_idx,
            hole_expr,
            hole_seed,
            target_sort,
            view_bindings,
            view_seeds,
            dummy_bindings,
            candidate,
            skipped_equal_hole,
        ),
    };
}

fn recoverBindingCandidateSymbolic(
    theorem: *const TheoremContext,
    env: *const GlobalEnv,
    dummy_witnesses: ?[]const ?ExprId,
    source_expr: ExprId,
    symbolic: *const SymbolicExpr,
    hole_view_idx: usize,
    hole_expr: ?ExprId,
    hole_seed: BindingSeed,
    target_sort: []const u8,
    view_bindings: []const ?ExprId,
    view_seeds: []const BindingSeed,
    dummy_bindings: *std.AutoHashMapUnmanaged(usize, ExprId),
    candidate: *?ExprId,
    skipped_equal_hole: *bool,
) anyerror!bool {
    return switch (symbolic.*) {
        .binder => |idx| blk: {
            if (idx == hole_view_idx) {
                if (candidate.*) |existing| {
                    if (existing != source_expr) return error.RecoverConflict;
                } else {
                    candidate.* = source_expr;
                }
                break :blk true;
            }
            if (idx < view_bindings.len) {
                if (view_bindings[idx]) |expr_id| {
                    const concrete_hole_expr = hole_expr orelse break :blk false;
                    break :blk try recoverBindingCandidate(
                        theorem,
                        env,
                        source_expr,
                        expr_id,
                        concrete_hole_expr,
                        target_sort,
                        candidate,
                        skipped_equal_hole,
                    );
                }
            }
            if (idx >= view_seeds.len) return error.TemplateBinderOutOfRange;
            break :blk try recoverBindingCandidateFromSeed(
                theorem,
                env,
                dummy_witnesses,
                source_expr,
                view_seeds[idx],
                hole_view_idx,
                hole_expr,
                hole_seed,
                target_sort,
                view_bindings,
                view_seeds,
                dummy_bindings,
                candidate,
                skipped_equal_hole,
            );
        },
        .fixed => |expr_id| blk: {
            const concrete_hole_expr = hole_expr orelse break :blk false;
            break :blk try recoverBindingCandidate(
                theorem,
                env,
                source_expr,
                expr_id,
                concrete_hole_expr,
                target_sort,
                candidate,
                skipped_equal_hole,
            );
        },
        .dummy => |slot| blk: {
            // Prefer live dummy witnesses when the hole already has a
            // concrete expression. Raw slot identity is too coarse in that
            // case, because the same hidden binder can occur inside larger
            // subtrees that only normalize to the hole after rewrites.
            if (hole_expr) |concrete_hole_expr| {
                if (dummy_witnesses) |witnesses| {
                    if (slot < witnesses.len) {
                        if (witnesses[slot]) |witness| {
                            if (witness == concrete_hole_expr) {
                                if (candidate.*) |existing| {
                                    if (existing != source_expr) {
                                        return error.RecoverConflict;
                                    }
                                } else {
                                    candidate.* = source_expr;
                                }
                                break :blk true;
                            }
                        }
                    }
                }
            } else if (holeSeedMatchesDummy(hole_seed, slot)) {
                if (candidate.*) |existing| {
                    if (existing != source_expr) {
                        return error.RecoverStructureMismatch;
                    }
                } else {
                    candidate.* = source_expr;
                }
                break :blk true;
            }
            if (dummy_bindings.get(slot)) |existing| {
                if (existing != source_expr) {
                    return error.RecoverStructureMismatch;
                }
            } else {
                try dummy_bindings.put(theorem.allocator, slot, source_expr);
            }
            break :blk false;
        },
        .app => |pattern_app| blk: {
            // A coercion chain around exactly the hole is a cross-sort
            // recovery site: re-sort the whole source subtree instead of
            // matching the coercion heads structurally (the source side
            // carries the *other* sort's chain).
            if (symbolicCoercionChainHole(env, symbolic, hole_view_idx)) {
                const recovered = resortExprToSort(
                    theorem,
                    env,
                    source_expr,
                    target_sort,
                ) orelse return error.RecoverStructureMismatch;
                if (candidate.*) |existing| {
                    if (existing != recovered) return error.RecoverConflict;
                } else {
                    candidate.* = recovered;
                }
                break :blk true;
            }
            const source_node = theorem.interner.node(source_expr);
            const source_app = switch (source_node.*) {
                .variable => return error.RecoverStructureMismatch,
                .placeholder => return error.RecoverStructureMismatch,
                .app => |app| app,
            };
            if (source_app.term_id != pattern_app.term_id) {
                return error.RecoverStructureMismatch;
            }
            if (source_app.args.len != pattern_app.args.len) {
                return error.RecoverStructureMismatch;
            }
            var found = false;
            for (source_app.args, pattern_app.args, 0..) |
                source_arg,
                pattern_arg,
                idx,
            | {
                if (recoverShouldSkipSymbolicArg(
                    env,
                    source_app.term_id,
                    idx,
                    source_arg,
                    pattern_arg,
                    hole_view_idx,
                    hole_expr,
                    skipped_equal_hole,
                )) continue;
                found = (try recoverBindingCandidateSymbolic(
                    theorem,
                    env,
                    dummy_witnesses,
                    source_arg,
                    pattern_arg,
                    hole_view_idx,
                    hole_expr,
                    hole_seed,
                    target_sort,
                    view_bindings,
                    view_seeds,
                    dummy_bindings,
                    candidate,
                    skipped_equal_hole,
                )) or found;
            }
            break :blk found;
        },
    };
}

/// Whether `symbolic` is a chain of one or more coercion applications whose
/// innermost argument is exactly the hole binder.
fn symbolicCoercionChainHole(
    env: *const GlobalEnv,
    symbolic: *const SymbolicExpr,
    hole_view_idx: usize,
) bool {
    var current = symbolic;
    while (true) {
        const app = switch (current.*) {
            .app => |a| a,
            else => return false,
        };
        if (app.args.len != 1 or !env.isCoercionTerm(app.term_id)) {
            return false;
        }
        const arg = app.args[0];
        switch (arg.*) {
            .binder => |idx| return idx == hole_view_idx,
            .app => current = arg,
            else => return false,
        }
    }
}

fn holeSeedMatchesDummy(seed: BindingSeed, slot: usize) bool {
    return switch (seed) {
        .bound => |bound| switch (bound) {
            .symbolic => |symbolic| switch (symbolic.expr.*) {
                .dummy => |seed_slot| seed_slot == slot,
                else => false,
            },
            .concrete => false,
        },
        else => false,
    };
}

/// The concrete acceptance relation for a recover source: the raw
/// structural walk, then the aligned (preprocessed) retry — the same two
/// paths `applyRecoverBinding` tries before falling back to symbolic
/// seeds. Returns the recovered target candidate on acceptance, null when
/// neither concrete path accepts. Only a structural mismatch means "no";
/// other errors propagate. Also used read-only by the view matcher to
/// judge trial context splits, so the filter and the committing pass
/// cannot drift apart.
pub fn concreteRecoverCandidate(
    theorem: *TheoremContext,
    env: *const GlobalEnv,
    registry: *RewriteRegistry,
    source_expr: ExprId,
    pattern_expr: ExprId,
    hole_expr: ExprId,
    target_sort: []const u8,
    debug_views: bool,
) !?ExprId {
    var candidate: ?ExprId = null;
    var skipped_equal_hole = false;
    const found = recoverBindingCandidate(
        theorem,
        env,
        source_expr,
        pattern_expr,
        hole_expr,
        target_sort,
        &candidate,
        &skipped_equal_hole,
    ) catch |err| switch (err) {
        error.RecoverStructureMismatch => blk: {
            skipped_equal_hole = false;
            break :blk false;
        },
        else => return err,
    };
    if (found or skipped_equal_hole or source_expr == pattern_expr) {
        if (debug_views) {
            ViewTrace.printMessage(
                "raw recover matched concrete pattern",
                .{},
            );
        }
        if (!found) candidate = hole_expr;
        return candidate orelse hole_expr;
    }

    const aligned_source = try preprocessDerivedExpr(
        theorem,
        env,
        registry,
        source_expr,
    );
    const aligned_pattern = try preprocessDerivedExpr(
        theorem,
        env,
        registry,
        pattern_expr,
    );

    candidate = null;
    skipped_equal_hole = false;
    const aligned_found = recoverBindingCandidate(
        theorem,
        env,
        aligned_source,
        aligned_pattern,
        hole_expr,
        target_sort,
        &candidate,
        &skipped_equal_hole,
    ) catch |err| switch (err) {
        error.RecoverStructureMismatch => blk: {
            skipped_equal_hole = false;
            break :blk false;
        },
        else => return err,
    };
    if (aligned_found or skipped_equal_hole or
        aligned_source == aligned_pattern)
    {
        if (debug_views) {
            ViewTrace.printMessage(
                "aligned recover matched concrete pattern",
                .{},
            );
        }
        if (!aligned_found) candidate = hole_expr;
        return candidate orelse hole_expr;
    }
    return null;
}

fn recoverBindingCandidate(
    theorem: *const TheoremContext,
    env: *const GlobalEnv,
    source_expr: ExprId,
    pattern_expr: ExprId,
    hole_expr: ExprId,
    target_sort: []const u8,
    candidate: *?ExprId,
    skipped_equal_hole: *bool,
) !bool {
    if (pattern_expr == hole_expr) {
        if (candidate.*) |existing| {
            if (existing != source_expr) return error.RecoverConflict;
        } else {
            candidate.* = source_expr;
        }
        return true;
    }
    // A coercion chain around exactly the hole is a cross-sort recovery
    // site: the source side carries the other sort's chain (or none), so
    // re-sort the whole source subtree instead of matching the coercion
    // heads structurally. Failure to re-sort correctly rejects sources
    // whose subtree is not coercion-reachable from the target sort (e.g. a
    // compound term where an eigenvariable is required).
    if (concreteCoercionChainHole(theorem, env, pattern_expr, hole_expr)) {
        const recovered = resortExprToSort(
            theorem,
            env,
            source_expr,
            target_sort,
        ) orelse return error.RecoverStructureMismatch;
        if (candidate.*) |existing| {
            if (existing != recovered) return error.RecoverConflict;
        } else {
            candidate.* = recovered;
        }
        return true;
    }

    const source_node = theorem.interner.node(source_expr);
    const pattern_node = theorem.interner.node(pattern_expr);
    return switch (pattern_node.*) {
        .variable => switch (source_node.*) {
            .variable => return false,
            .placeholder => return false,
            .app => |source_app| return recoverBindingFromSourceWrapper(
                theorem,
                env,
                source_app,
                pattern_expr,
                hole_expr,
                target_sort,
                candidate,
            ),
        },
        .placeholder => switch (source_node.*) {
            .variable => return false,
            .placeholder => return false,
            .app => |source_app| return recoverBindingFromSourceWrapper(
                theorem,
                env,
                source_app,
                pattern_expr,
                hole_expr,
                target_sort,
                candidate,
            ),
        },
        .app => |pattern_app| switch (source_node.*) {
            .variable => return error.RecoverStructureMismatch,
            .placeholder => return error.RecoverStructureMismatch,
            .app => |source_app| blk: {
                if (source_app.term_id != pattern_app.term_id) {
                    return error.RecoverStructureMismatch;
                }
                if (source_app.args.len != pattern_app.args.len) {
                    return error.RecoverStructureMismatch;
                }
                var found = false;
                for (source_app.args, pattern_app.args, 0..) |
                    source_arg,
                    pattern_arg,
                    idx,
                | {
                    if (recoverShouldSkipConcreteArg(
                        env,
                        source_app.term_id,
                        idx,
                        source_arg,
                        pattern_arg,
                        hole_expr,
                        skipped_equal_hole,
                    )) continue;
                    found = (try recoverBindingCandidate(
                        theorem,
                        env,
                        source_arg,
                        pattern_arg,
                        hole_expr,
                        target_sort,
                        candidate,
                        skipped_equal_hole,
                    )) or found;
                }
                break :blk found;
            },
        },
    };
}

/// Whether `pattern_expr` is a chain of one or more coercion applications
/// whose innermost argument is exactly `hole_expr`.
fn concreteCoercionChainHole(
    theorem: *const TheoremContext,
    env: *const GlobalEnv,
    pattern_expr: ExprId,
    hole_expr: ExprId,
) bool {
    var current = pattern_expr;
    while (true) {
        const app = switch (theorem.interner.node(current).*) {
            .app => |a| a,
            else => return false,
        };
        if (app.args.len != 1 or !env.isCoercionTerm(app.term_id)) {
            return false;
        }
        current = app.args[0];
        if (current == hole_expr) return true;
    }
}

/// Re-sort `expr_id` to `target_sort` by stripping leading coercion
/// applications: the identity when the sorts already agree, the coercion
/// argument (recursively) otherwise. Null when no prefix strip lands at the
/// target sort — the subtree genuinely has a different sort.
fn resortExprToSort(
    theorem: *const TheoremContext,
    env: *const GlobalEnv,
    expr_id: ExprId,
    target_sort: []const u8,
) ?ExprId {
    var current = expr_id;
    while (true) {
        const info = BindingValidation.currentExprInfo(
            env,
            theorem,
            current,
        ) catch return null;
        if (std.mem.eql(u8, info.sort_name, target_sort)) return current;
        const app = switch (theorem.interner.node(current).*) {
            .app => |a| a,
            else => return null,
        };
        if (app.args.len != 1 or !env.isCoercionTerm(app.term_id)) {
            return null;
        }
        current = app.args[0];
    }
}

fn recoverBindingFromSourceWrapper(
    theorem: *const TheoremContext,
    env: *const GlobalEnv,
    source_app: ExprNode.App,
    pattern_expr: ExprId,
    hole_expr: ExprId,
    target_sort: []const u8,
    candidate: *?ExprId,
) !bool {
    // This is intentionally heuristic: when the source has one extra wrapper
    // around a leaf pattern, choose the unique direct wrapper argument that
    // has the target sort and is not obviously the hole or pattern itself.
    // Cross-sort enrollments get a second tier: a unique argument whose
    // coercion chain strips to the target sort, considered only when no
    // argument has the target sort outright.
    var wrapper_candidate: ?ExprId = null;
    for (source_app.args) |source_arg| {
        if (source_arg == hole_expr or source_arg == pattern_expr) continue;
        const arg_info = try BindingValidation.currentExprInfo(
            env,
            theorem,
            source_arg,
        );
        if (!std.mem.eql(u8, arg_info.sort_name, target_sort)) {
            continue;
        }
        if (wrapper_candidate != null) {
            return error.RecoverStructureMismatch;
        }
        wrapper_candidate = source_arg;
    }
    if (wrapper_candidate == null) {
        for (source_app.args) |source_arg| {
            if (source_arg == hole_expr or source_arg == pattern_expr) {
                continue;
            }
            const resorted = resortExprToSort(
                theorem,
                env,
                source_arg,
                target_sort,
            ) orelse continue;
            if (resorted == source_arg) continue;
            if (wrapper_candidate != null) {
                return error.RecoverStructureMismatch;
            }
            wrapper_candidate = resorted;
        }
    }
    const recovered = wrapper_candidate orelse {
        return error.RecoverStructureMismatch;
    };
    if (candidate.*) |existing| {
        if (existing != recovered) return error.RecoverConflict;
    } else {
        candidate.* = recovered;
    }
    return true;
}

fn recoverShouldSkipConcreteArg(
    env: *const GlobalEnv,
    term_id: u32,
    arg_idx: usize,
    source_arg: ExprId,
    pattern_arg: ExprId,
    hole_expr: ExprId,
    skipped_equal_hole: *bool,
) bool {
    if (!recoverArgIsBound(env, term_id, arg_idx)) return false;
    if (source_arg != hole_expr or pattern_arg != hole_expr) return false;
    skipped_equal_hole.* = true;
    return true;
}

fn recoverShouldSkipSymbolicArg(
    env: *const GlobalEnv,
    term_id: u32,
    arg_idx: usize,
    source_arg: ExprId,
    pattern_arg: *const SymbolicExpr,
    hole_view_idx: usize,
    hole_expr: ?ExprId,
    skipped_equal_hole: *bool,
) bool {
    if (!recoverArgIsBound(env, term_id, arg_idx)) return false;
    const concrete_hole = hole_expr orelse return false;
    if (source_arg != concrete_hole) return false;
    if (pattern_arg.* != .binder) return false;
    if (pattern_arg.binder != hole_view_idx) return false;
    skipped_equal_hole.* = true;
    return true;
}

fn recoverArgIsBound(
    env: *const GlobalEnv,
    term_id: u32,
    arg_idx: usize,
) bool {
    if (term_id >= env.terms.items.len) return false;
    const term = &env.terms.items[term_id];
    if (arg_idx >= term.args.len) return false;
    return term.args[arg_idx].bound;
}

fn applyAbstractBinding(
    theorem: *TheoremContext,
    env: *const GlobalEnv,
    registry: *RewriteRegistry,
    view_bindings: []?ExprId,
    abstract: AbstractDecl,
) !ApplyResult {
    const left_expr = view_bindings[abstract.left_view_idx] orelse {
        return .no_progress;
    };
    const right_expr = view_bindings[abstract.right_view_idx] orelse {
        return .no_progress;
    };
    const raw_hole_expr = view_bindings[abstract.hole_view_idx] orelse {
        return .no_progress;
    };
    // A bare-name plug is its binder's resolved value; a pattern plug is
    // matched at the sites and needs nothing solved up front.
    if (abstract.left_plug.bareBinder()) |idx| {
        if (view_bindings[idx] == null) return .no_progress;
    }
    if (abstract.right_plug.bareBinder()) |idx| {
        if (view_bindings[idx] == null) return .no_progress;
    }
    // Cross-sort plugs: plug sites sit at the plugs' sort, so substitute
    // the hole wrapped in the coercion route up to that sort, keeping the
    // constructed context well-sorted.
    const plug_sort_name = if (abstract.left_plug.bareBinder()) |idx| blk: {
        const info = try BindingValidation.currentExprInfo(
            env,
            theorem,
            view_bindings[idx].?,
        );
        break :blk info.sort_name;
    } else abstract.left_plug.sort_name;
    const hole_expr = (try abstractWrapHoleToPlugSort(
        theorem,
        env,
        raw_hole_expr,
        plug_sort_name,
    )) orelse return .no_progress;

    const allocator = theorem.allocator;
    const working = try allocator.dupe(?ExprId, view_bindings);
    defer allocator.free(working);
    const base = try allocator.dupe(?ExprId, view_bindings);
    defer allocator.free(base);
    const scratch = try allocator.alloc(?ExprId, view_bindings.len);
    defer allocator.free(scratch);

    var walk = PlugWalk{
        .theorem = theorem,
        .abstract = abstract,
        .hole_expr = hole_expr,
        .bindings = working,
        .base = base,
        .scratch = scratch,
    };
    const raw_candidate = abstractContextExpr(
        &walk,
        left_expr,
        right_expr,
    ) catch |err| switch (err) {
        error.AbstractStructureMismatch => null,
        else => return err,
    };
    if (raw_candidate) |candidate| {
        if (walk.found_plug) {
            return try commitAbstractResult(
                view_bindings,
                working,
                abstract.target_view_idx,
                candidate,
            );
        }
    }

    const aligned_left = try preprocessDerivedExpr(
        theorem,
        env,
        registry,
        left_expr,
    );
    const aligned_right = try preprocessDerivedExpr(
        theorem,
        env,
        registry,
        right_expr,
    );
    // The retry matches the plugs against the preprocessed sides, so every
    // solved binder a plug mentions is preprocessed the same way; pattern
    // structure itself is left alone.
    @memcpy(working, view_bindings);
    try preprocessPlugBindings(
        theorem,
        env,
        registry,
        abstract.left_plug.template,
        working,
    );
    try preprocessPlugBindings(
        theorem,
        env,
        registry,
        abstract.right_plug.template,
        working,
    );
    @memcpy(base, working);

    walk = PlugWalk{
        .theorem = theorem,
        .abstract = abstract,
        .hole_expr = hole_expr,
        .bindings = working,
        .base = base,
        .scratch = scratch,
    };
    const candidate = abstractContextExpr(
        &walk,
        aligned_left,
        aligned_right,
    ) catch |err| switch (err) {
        error.AbstractStructureMismatch => {
            if (walk.disagreement) return error.AbstractPatternConflict;
            return err;
        },
        else => return err,
    };
    if (!walk.found_plug) {
        if (walk.disagreement) return error.AbstractPatternConflict;
        if (abstract.hasPattern()) return error.AbstractPatternNoSite;
        return error.AbstractNoPlugOccurrence;
    }
    return try commitAbstractResult(
        view_bindings,
        working,
        abstract.target_view_idx,
        candidate,
    );
}

/// Record the walk's result: the target context, plus every view binder the
/// plug patterns solved at their sites. An explicit target that differs from
/// the recovered context is a conflict.
fn commitAbstractResult(
    view_bindings: []?ExprId,
    working: []const ?ExprId,
    target_view_idx: usize,
    candidate: ExprId,
) !ApplyResult {
    var progress = false;
    if (view_bindings[target_view_idx]) |existing| {
        if (existing != candidate) return error.AbstractConflict;
    } else {
        view_bindings[target_view_idx] = candidate;
        progress = true;
    }
    for (working, 0..) |value, idx| {
        if (view_bindings[idx] != null) continue;
        if (value) |solved| {
            view_bindings[idx] = solved;
            progress = true;
        }
    }
    return if (progress) .progress else .no_progress;
}

fn preprocessPlugBindings(
    theorem: *TheoremContext,
    env: *const GlobalEnv,
    registry: *RewriteRegistry,
    template: TemplateExpr,
    bindings: []?ExprId,
) !void {
    switch (template) {
        .binder => |idx| {
            if (bindings[idx]) |value| {
                bindings[idx] = try preprocessDerivedExpr(
                    theorem,
                    env,
                    registry,
                    value,
                );
            }
        },
        .app => |app| for (app.args) |arg| {
            try preprocessPlugBindings(theorem, env, registry, arg, bindings);
        },
    }
}

/// State of one `@abstract` walk. The plugs are matched as templates over the
/// view binders against `bindings`, which starts as the solved view state
/// and accumulates the binders solved at accepted sites, so every site shares
/// one substitution. A bare-name plug is the trivial template `.binder` whose
/// binder is already solved, so matching it is the exact-value check the
/// bare form has always made.
pub const PlugWalk = struct {
    theorem: *TheoremContext,
    abstract: AbstractDecl,
    hole_expr: ExprId,
    /// Working substitution: committed view bindings plus site solutions.
    bindings: []?ExprId,
    /// The substitution before any site was accepted.
    base: []const ?ExprId,
    /// Rollback buffer for a failed site attempt.
    scratch: []?ExprId,
    found_plug: bool = false,
    /// A later site fit the plug shapes on its own but disagreed with an
    /// earlier site's solution. Turns the walk's failure into a conflict
    /// report rather than a structure mismatch.
    disagreement: bool = false,

    /// Pattern plugs never match a subtree that is identical on both sides:
    /// nothing is replaced there, and a spurious site would only constrain
    /// the shared substitution.
    pub fn identityFirst(self: *const PlugWalk) bool {
        return self.abstract.hasPattern();
    }

    /// Try the pair as a plug site. On success the binders the plugs solved
    /// stay in `bindings`; on failure `bindings` is unchanged.
    pub fn trySite(self: *PlugWalk, left_expr: ExprId, right_expr: ExprId) bool {
        @memcpy(self.scratch, self.bindings);
        if (self.theorem.matchTemplate(
            self.abstract.left_plug.template,
            left_expr,
            self.bindings,
        ) and self.theorem.matchTemplate(
            self.abstract.right_plug.template,
            right_expr,
            self.bindings,
        )) {
            self.found_plug = true;
            return true;
        }
        @memcpy(self.bindings, self.scratch);
        if (self.found_plug and !self.disagreement) {
            @memcpy(self.scratch, self.base);
            if (self.theorem.matchTemplate(
                self.abstract.left_plug.template,
                left_expr,
                self.scratch,
            ) and self.theorem.matchTemplate(
                self.abstract.right_plug.template,
                right_expr,
                self.scratch,
            )) {
                self.disagreement = true;
            }
        }
        return false;
    }
};

/// Wrap `hole_expr` in the coercion route up to the plugs' sort (the
/// identity when the sorts already agree). Null when no route exists: the
/// cross-sort enrollment only guaranteed a common target, not that the hole
/// is coercible up to the plugs.
fn abstractWrapHoleToPlugSort(
    theorem: *TheoremContext,
    env: *const GlobalEnv,
    hole_expr: ExprId,
    plug_sort_name: []const u8,
) !?ExprId {
    const hole_info = try BindingValidation.currentExprInfo(
        env,
        theorem,
        hole_expr,
    );
    if (std.mem.eql(u8, hole_info.sort_name, plug_sort_name)) {
        return hole_expr;
    }
    var route: std.ArrayListUnmanaged(u32) = .empty;
    defer route.deinit(theorem.allocator);
    if (!try env.coercionRoute(
        hole_info.sort_name,
        plug_sort_name,
        theorem.allocator,
        &route,
    )) {
        return null;
    }
    var current = hole_expr;
    for (route.items) |term_id| {
        current = try theorem.interner.internApp(term_id, &.{current});
    }
    return current;
}

fn abstractContextExpr(
    walk: *PlugWalk,
    left_expr: ExprId,
    right_expr: ExprId,
) !ExprId {
    if (walk.identityFirst() and left_expr == right_expr) return left_expr;
    if (walk.trySite(left_expr, right_expr)) return walk.hole_expr;

    const theorem = walk.theorem;
    const left_node = theorem.interner.node(left_expr);
    const right_node = theorem.interner.node(right_expr);
    return switch (left_node.*) {
        .variable, .placeholder => switch (right_node.*) {
            .variable, .placeholder => {
                if (left_expr != right_expr) return error.AbstractStructureMismatch;
                return left_expr;
            },
            .app => return error.AbstractStructureMismatch,
        },
        .app => |left_app| switch (right_node.*) {
            .variable, .placeholder => return error.AbstractStructureMismatch,
            .app => |right_app| blk: {
                if (left_app.term_id != right_app.term_id) {
                    return error.AbstractStructureMismatch;
                }
                if (left_app.args.len != right_app.args.len) {
                    return error.AbstractStructureMismatch;
                }
                const args = try theorem.allocator.alloc(ExprId, left_app.args.len);
                errdefer theorem.allocator.free(args);
                for (left_app.args, right_app.args, 0..) |left_arg, right_arg, idx| {
                    args[idx] = try abstractContextExpr(walk, left_arg, right_arg);
                }
                break :blk try theorem.interner.internAppOwned(
                    left_app.term_id,
                    args,
                );
            },
        },
    };
}

fn preprocessDerivedExpr(
    theorem: *TheoremContext,
    env: *const GlobalEnv,
    registry: *RewriteRegistry,
    expr_id: ExprId,
) !ExprId {
    var arena = std.heap.ArenaAllocator.init(theorem.allocator);
    defer arena.deinit();

    var canonicalizer = Canonicalizer.init(
        arena.allocator(),
        theorem,
        registry,
        env,
    );
    return try preprocessDerivedExprInner(
        &canonicalizer,
        theorem,
        env,
        expr_id,
        0,
    );
}

fn preprocessDerivedExprInner(
    canonicalizer: *Canonicalizer,
    theorem: *TheoremContext,
    env: *const GlobalEnv,
    expr_id: ExprId,
    depth: usize,
) !ExprId {
    if (depth >= preprocess_max_depth) return expr_id;

    if (try expandConcreteDefForDerived(theorem, env, expr_id)) |expanded| {
        if (expanded != expr_id) {
            return try preprocessDerivedExprInner(
                canonicalizer,
                theorem,
                env,
                expanded,
                depth + 1,
            );
        }
    }

    var current = expr_id;
    const node = theorem.interner.node(current);
    switch (node.*) {
        .variable => {},
        .placeholder => {},
        .app => |app| {
            const args = try canonicalizer.allocator.alloc(ExprId, app.args.len);
            var any_changed = false;
            for (app.args, 0..) |arg, idx| {
                const aligned_arg = try preprocessDerivedExprInner(
                    canonicalizer,
                    theorem,
                    env,
                    arg,
                    depth + 1,
                );
                args[idx] = aligned_arg;
                any_changed = any_changed or aligned_arg != arg;
            }
            if (any_changed) {
                current = try theorem.interner.internApp(app.term_id, args);
            }
        },
    }

    current = try canonicalizer.canonicalize(current);
    if (try expandConcreteDefForDerived(theorem, env, current)) |expanded| {
        if (expanded != current) {
            return try preprocessDerivedExprInner(
                canonicalizer,
                theorem,
                env,
                expanded,
                depth + 1,
            );
        }
    }
    return current;
}

fn expandConcreteDefForDerived(
    theorem: *TheoremContext,
    env: *const GlobalEnv,
    expr_id: ExprId,
) !?ExprId {
    const node = theorem.interner.node(expr_id);
    const app = switch (node.*) {
        .app => |value| value,
        .variable => return null,
        .placeholder => return null,
    };
    if (app.term_id >= env.terms.items.len) return null;

    const term = &env.terms.items[app.term_id];
    if (!term.is_def or term.body == null) return null;
    if (term.dummy_args.len != 0) return null;
    if (term.args.len != app.args.len) return null;

    return try theorem.instantiateTemplate(term.body.?, app.args);
}
