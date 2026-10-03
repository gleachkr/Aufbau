const std = @import("std");

const ExprModule = @import("../../trusted/expressions.zig");
const Expr = ExprModule.Expr;
const SourceSpan = ExprModule.SourceSpan;
const SurfaceExpr = @import("../surface_expr.zig");
const MM0Parser = @import("../parse_recovery.zig").MM0Parser;
const ArgInfo = @import("../parse_recovery.zig").ArgInfo;
const ExprId = @import("../expr.zig").ExprId;
const TheoremContext = @import("../expr.zig").TheoremContext;
const GlobalEnv = @import("../env.zig").GlobalEnv;
const TermDecl = @import("../env.zig").TermDecl;
const RuleDecl = @import("../env.zig").RuleDecl;
const TemplateExpr = @import("../rules.zig").TemplateExpr;
const DefOps = @import("../def_ops.zig");
const AcuiBag = @import("../acui_bag.zig");
const Views = @import("../views.zig");
const Canonicalizer = @import("../canonicalizer.zig").Canonicalizer;
const RewriteRegistry = @import("../rewrite_registry.zig").RewriteRegistry;
const ResolvedStructuralCombiner =
    @import("../rewrite_registry.zig").ResolvedStructuralCombiner;
const CompilerVars = @import("./vars.zig");
const Idents = @import("../idents.zig");
const Inference = @import("./inference.zig");

const annotationMatchesTag = Idents.annotationMatchesTag;

pub const NameExprMap = std.StringHashMap(*const Expr);
pub const SortVarRegistry = CompilerVars.SortVarRegistry;

pub const contains = SurfaceExpr.containsHole;
pub const firstHoleSourceSpan = SurfaceExpr.firstHoleSourceSpan;
const exprIdSortName = SurfaceExpr.exprIdSortName;
const sortName = SurfaceExpr.parserSortName;
pub const containsStructuralHole = SurfaceExpr.containsStructuralHole;

pub fn processSortHoleAnnotations(
    parser: *MM0Parser,
    sort_name: []const u8,
    annotations: []const []const u8,
    sort_vars: *const SortVarRegistry,
) !void {
    const hole_tag = "@hole";

    var hole_token: ?[]const u8 = null;
    for (annotations) |ann| {
        if (!annotationMatchesTag(ann, hole_tag)) continue;

        if (hole_token != null) return error.DuplicateHoleAnnotation;
        const tail = std.mem.trim(u8, ann[hole_tag.len..], " \t\r\n");
        if (tail.len == 0) return error.InvalidHoleAnnotation;

        var iter = std.mem.tokenizeAny(u8, tail, " \t\r\n");
        const token = iter.next() orelse return error.InvalidHoleAnnotation;
        if (iter.next() != null) return error.InvalidHoleAnnotation;
        if (sort_vars.getTokenDecl(token) != null) {
            return error.HoleTokenNameCollision;
        }
        hole_token = token;
    }

    if (hole_token) |token| {
        try parser.registerHoleTokenForSort(sort_name, token);
    }
}

pub const ParsedAssertion = union(enum) {
    concrete: ExprId,
    holey: *const Expr,
};

/// A holey assertion in both forms: as written, for diagnostics and fills,
/// and interned once with a line hole for each hole (`internWithLineHoles`),
/// for the matchers.
pub const HoleyLine = struct {
    surface: *const Expr,
    /// Null for a whole-line hole: it constrains nothing, and minting a line
    /// hole for it would cost every unhinted inline step.
    interned: ?ExprId,

    pub fn init(
        theorem: *TheoremContext,
        env: *const GlobalEnv,
        surface: *const Expr,
    ) !HoleyLine {
        if (surface.* == .hole) return .{ .surface = surface, .interned = null };
        return .{
            .surface = surface,
            .interned = try internWithLineHoles(theorem, env, surface) orelse
                return error.UnknownSort,
        };
    }

    /// The interned line, a whole-line hole minted as one line hole.
    pub fn internedIn(
        self: HoleyLine,
        theorem: *TheoremContext,
        env: *const GlobalEnv,
    ) !ExprId {
        if (self.interned) |interned| return interned;
        return try internWithLineHoles(theorem, env, self.surface) orelse
            error.UnknownSort;
    }
};

pub const InferenceFailure = union(enum) {
    hypothesis_mismatch: struct {
        /// Source-order index of the cited premise / rule hypothesis.
        index: usize,
        /// What the cited premise proves.
        ref_expr: ExprId,
    },
    visible_structure_mismatch: VisibleMismatchDetail,
    missing_binder: struct {
        index: usize,
        name: ?[]const u8,
    },
};

/// Where the visible (non-hole) structure clashed with the rule template.
pub const VisibleMismatchDetail = union(enum) {
    unknown,
    /// The template requires an application of `expected_term_id`, but the
    /// visible statement has `actual_term_id` (null: a variable) there.
    head_clash: struct {
        expected_term_id: u32,
        actual_term_id: ?u32,
    },
    /// A rule binder already bound to `existing` while the visible statement
    /// requires `actual` at another occurrence of the same binder.
    binder_conflict: struct {
        binder_idx: usize,
        existing: ExprId,
        actual: ExprId,
    },
};

pub const InferenceReport = struct {
    failure: ?InferenceFailure = null,
};

pub const ConcreteMatchFailure = union(enum) {
    visible_structure_mismatch,
    hole_sort_mismatch: struct {
        token: []const u8,
        token_span: ?SourceSpan,
        expected_sort_name: []const u8,
        actual_sort_name: []const u8,
    },
    /// Out-of-order filling needs one hole per ACUI combination.
    acui_several_holes: struct {
        combiner_name: []const u8,
        token_span: ?SourceSpan,
    },
    /// A hole inside one member of an ACUI combination is filled only by
    /// position.
    acui_hole_in_member: struct {
        combiner_name: []const u8,
        token_span: ?SourceSpan,
    },
};

pub const ConcreteMatchReport = struct {
    failure: ?ConcreteMatchFailure = null,
};

pub fn parseAssertion(
    parser: *MM0Parser,
    theorem: *TheoremContext,
    theorem_vars: *NameExprMap,
    sort_vars: *const SortVarRegistry,
    math: []const u8,
) !ParsedAssertion {
    try CompilerVars.ensureMathTextVars(
        parser,
        theorem,
        theorem_vars,
        sort_vars,
        math,
    );
    const expr = try parser.parseHoleyFormulaText(math, theorem_vars);
    if (contains(expr)) return .{ .holey = expr };
    return .{ .concrete = try theorem.internParsedExpr(expr) };
}

pub fn inferBindingsFromAssertionDetailed(
    allocator: std.mem.Allocator,
    theorem: *TheoremContext,
    rule: *const RuleDecl,
    partial_bindings: []const ?ExprId,
    ref_exprs: []const ExprId,
    holey: *const Expr,
    report: *InferenceReport,
) ![]const ExprId {
    const bindings = try allocator.dupe(?ExprId, partial_bindings);
    defer allocator.free(bindings);

    for (rule.hyps, ref_exprs, 0..) |hyp, ref_expr, idx| {
        if (!theorem.matchTemplate(hyp, ref_expr, bindings)) {
            setInferenceFailure(report, .{ .hypothesis_mismatch = .{
                .index = idx,
                .ref_expr = ref_expr,
            } });
            return error.UnifyMismatch;
        }
    }

    if (!try matchTemplateToSurface(
        theorem,
        rule.concl,
        holey,
        bindings,
        report,
    )) {
        return error.HoleyInferenceMismatch;
    }

    if (firstMissingBinding(bindings)) |idx| {
        setInferenceFailure(report, .{ .missing_binder = .{
            .index = idx,
            .name = if (idx < rule.arg_names.len) rule.arg_names[idx] else null,
        } });
        return error.MissingBinderAssignment;
    }

    const concrete = try allocator.alloc(ExprId, bindings.len);
    for (bindings, 0..) |binding, idx| {
        concrete[idx] = binding.?;
    }
    return concrete;
}

pub fn matchTemplateToSurface(
    theorem: *TheoremContext,
    template: TemplateExpr,
    holey: *const Expr,
    bindings: []?ExprId,
    report: ?*InferenceReport,
) !bool {
    switch (holey.*) {
        .hole => return true,
        .variable => {
            const expr_id = try theorem.internParsedExpr(holey);
            if (theorem.matchTemplate(template, expr_id, bindings)) {
                return true;
            }
            setInferenceFailure(
                report,
                .{ .visible_structure_mismatch = switch (template) {
                    .app => |tmpl_app| .{ .head_clash = .{
                        .expected_term_id = tmpl_app.term_id,
                        .actual_term_id = null,
                    } },
                    .binder => .unknown,
                } },
            );
            return false;
        },
        .term => |holey_term| switch (template) {
            .binder => |idx| {
                // Like a bare hole, a subterm with a hole in it fixes
                // nothing; the binder keeps whatever the rest of the match
                // gives it, and holey validation checks the line later.
                if (SurfaceExpr.containsHole(holey)) return true;
                const expr_id = try theorem.internParsedExpr(holey);
                if (idx >= bindings.len) {
                    setInferenceFailure(
                        report,
                        .{ .visible_structure_mismatch = .unknown },
                    );
                    return false;
                }
                if (bindings[idx]) |existing| {
                    if (existing == expr_id) return true;
                    setInferenceFailure(
                        report,
                        .{ .visible_structure_mismatch = .{
                            .binder_conflict = .{
                                .binder_idx = idx,
                                .existing = existing,
                                .actual = expr_id,
                            },
                        } },
                    );
                    return false;
                }
                bindings[idx] = expr_id;
                return true;
            },
            .app => |tmpl_app| {
                if (tmpl_app.term_id != holey_term.id) {
                    setInferenceFailure(
                        report,
                        .{ .visible_structure_mismatch = .{ .head_clash = .{
                            .expected_term_id = tmpl_app.term_id,
                            .actual_term_id = holey_term.id,
                        } } },
                    );
                    return false;
                }
                if (tmpl_app.args.len != holey_term.args.len) {
                    setInferenceFailure(
                        report,
                        .{ .visible_structure_mismatch = .unknown },
                    );
                    return false;
                }
                for (tmpl_app.args, holey_term.args) |tmpl_arg, holey_arg| {
                    if (!try matchTemplateToSurface(
                        theorem,
                        tmpl_arg,
                        holey_arg,
                        bindings,
                        report,
                    )) return false;
                }
                return true;
            },
        },
    }
}

/// `matchTemplateToSurface`, all or nothing: on a mismatch `bindings` goes
/// back to what it was, using `snap` as scratch.
pub fn foldTemplateToSurface(
    theorem: *TheoremContext,
    template: TemplateExpr,
    holey: *const Expr,
    bindings: []?ExprId,
    snap: []?ExprId,
) !bool {
    @memcpy(snap, bindings);
    if (try matchTemplateToSurface(theorem, template, holey, bindings, null)) return true;
    @memcpy(bindings, snap);
    return false;
}

/// Intern a holey surface with a fresh line hole for each hole: a holey line
/// (`HoleyLine`) or an inline minor's holey hint. Line holes are meta
/// wildcards that spend no dependency slot, so a theorem may check any
/// number of holey lines. Null when a hole's sort is unknown.
pub fn internWithLineHoles(
    theorem: *TheoremContext,
    env: *const GlobalEnv,
    holey: *const Expr,
) !?ExprId {
    return SurfaceExpr.internHoley(theorem, env, holey, {}, mintLineHole);
}

pub fn mintLineHole(_: void, theorem: *TheoremContext, sort_name: []const u8) anyerror!?ExprId {
    return try theorem.addLineHolePlaceholder(sort_name);
}

/// Fill holes from the same visible positions in a selected candidate.
///
/// This does not prove that non-hole subtrees match the candidate. Callers
/// that use the result must still validate the resulting concrete line through
/// the ordinary rule-application pipeline.
pub fn materializeSurfaceWithCandidate(
    parser: *MM0Parser,
    theorem: *TheoremContext,
    env: *const GlobalEnv,
    holey: *const Expr,
    candidate: ExprId,
    report: *ConcreteMatchReport,
) anyerror!?ExprId {
    if (!contains(holey)) {
        const visible = try theorem.internParsedExpr(holey);
        const visible_sort = try exprIdSortName(theorem, env, visible);
        const candidate_sort = try exprIdSortName(theorem, env, candidate);
        if (std.mem.eql(u8, visible_sort, candidate_sort)) return visible;
        setConcreteFailure(report, .visible_structure_mismatch);
        return null;
    }

    switch (holey.*) {
        .hole => |hole| return if (try holeFits(parser, theorem, env, hole, candidate, report))
            candidate
        else
            null,
        .variable => unreachable,
        .term => |holey_term| {
            const node = theorem.interner.node(candidate);
            const candidate_app = switch (node.*) {
                .app => |app| app,
                else => {
                    setConcreteFailure(report, .visible_structure_mismatch);
                    return null;
                },
            };
            if (holey_term.id != candidate_app.term_id or
                holey_term.args.len != candidate_app.args.len)
            {
                if (try materializeThroughDef(
                    parser,
                    theorem,
                    env,
                    holey_term,
                    candidate,
                    report,
                )) |filled| return filled;
                if (try materializeAgainstUnfolded(
                    parser,
                    theorem,
                    env,
                    holey,
                    candidate,
                    report,
                )) |filled| return filled;
                setConcreteFailure(report, .visible_structure_mismatch);
                return null;
            }

            const args = try theorem.allocator.alloc(ExprId, holey_term.args.len);
            errdefer theorem.allocator.free(args);
            for (holey_term.args, candidate_app.args, 0..) |
                arg,
                candidate_arg,
                idx,
            | {
                args[idx] = (try materializeSurfaceWithCandidate(
                    parser,
                    theorem,
                    env,
                    arg,
                    candidate_arg,
                    report,
                )) orelse {
                    theorem.allocator.free(args);
                    return null;
                };
            }
            return try theorem.interner.internAppOwned(holey_term.id, args);
        },
    }
}

/// Fill a holey application of a definition from a candidate that has the
/// definition unfolded: match the body, with the definition's arguments and
/// hidden variables as binders, against the candidate, then fill each
/// argument from the value its binder took. Null when the head is not a
/// definition, the body does not match, or it leaves an argument open.
fn materializeThroughDef(
    parser: *MM0Parser,
    theorem: *TheoremContext,
    env: *const GlobalEnv,
    holey_term: anytype,
    candidate: ExprId,
    report: *ConcreteMatchReport,
) anyerror!?ExprId {
    const term = env.openableDef(holey_term.id) orelse return null;
    if (term.args.len != holey_term.args.len) return null;
    const values = try matchDefBody(theorem, env, term, candidate, null) orelse
        return null;
    defer theorem.allocator.free(values);

    const allocator = theorem.allocator;
    const filled = filled: {
        const args = try allocator.alloc(ExprId, holey_term.args.len);
        // The interner owns `args` once `internAppOwned` succeeds.
        errdefer allocator.free(args);
        for (holey_term.args, values[0..holey_term.args.len], 0..) |arg, value, idx| {
            args[idx] = (try materializeSurfaceWithCandidate(
                parser,
                theorem,
                env,
                arg,
                value orelse {
                    allocator.free(args);
                    return null;
                },
                report,
            )) orelse {
                allocator.free(args);
                return null;
            };
        }
        break :filled try theorem.interner.internAppOwned(holey_term.id, args);
    };
    return try keepIfConverts(theorem, env, candidate, filled);
}

/// Fill `holey` from a candidate that keeps a definition folded where the
/// line has it unfolded: match the definition's body, its arguments fixed to
/// the candidate's and its hidden variables free, against the line with its
/// holes as wildcards, then fill from the candidate unfolded with the hidden
/// variables the line names. Null when the candidate's head is not a
/// definition or the line leaves a hidden variable open.
fn materializeAgainstUnfolded(
    parser: *MM0Parser,
    theorem: *TheoremContext,
    env: *const GlobalEnv,
    holey: *const Expr,
    candidate: ExprId,
    report: *ConcreteMatchReport,
) anyerror!?ExprId {
    const candidate_app = theorem.interner.node(candidate).app;
    const term = env.openableDef(candidate_app.term_id) orelse return null;
    if (term.args.len != candidate_app.args.len) return null;
    // The line writes out the body, so it has the body's head. Checked
    // first: interning the line mints line holes in the theorem.
    const body_head = switch (term.body.?) {
        .app => |app| app.term_id,
        .binder => return null,
    };
    if (holey.* != .term or holey.term.id != body_head) return null;
    const holey_id = try internWithLineHoles(theorem, env, holey) orelse
        return null;
    const values = try matchDefBody(
        theorem,
        env,
        term,
        holey_id,
        candidate_app.args,
    ) orelse return null;
    defer theorem.allocator.free(values);

    const binders = try theorem.allocator.alloc(ExprId, values.len);
    defer theorem.allocator.free(binders);
    for (values, 0..) |value, idx| {
        const expr = value orelse return null;
        if (theorem.containsLineHole(expr)) return null;
        binders[idx] = expr;
    }
    const unfolded = try theorem.instantiateTemplate(term.body.?, binders);
    const filled = try materializeSurfaceWithCandidate(
        parser,
        theorem,
        env,
        holey,
        unfolded,
        report,
    ) orelse return null;
    return try keepIfConverts(theorem, env, candidate, filled);
}

/// `filled` when it is `candidate` up to unfolding. A fill takes the line's
/// hole-free parts as written, so a fill through a definition can disagree
/// with the candidate where the def's body put them.
pub fn keepIfConverts(
    theorem: *TheoremContext,
    env: *const GlobalEnv,
    candidate: ExprId,
    filled: ExprId,
) !?ExprId {
    if (!try Inference.canConvertTransparent(theorem.allocator, theorem, env, candidate, filled))
        return null;
    return filled;
}

/// The fill of `holey` from `candidate` (`materializeSurfaceWithCandidate`,
/// which sees through the definitions the line keeps folded), when the filled
/// line is `candidate` up to unfolding. Null otherwise.
pub fn fillThroughDefs(
    parser: *MM0Parser,
    theorem: *TheoremContext,
    env: *const GlobalEnv,
    holey: *const Expr,
    candidate: ExprId,
) !?ExprId {
    var report = ConcreteMatchReport{};
    const filled = try materializeSurfaceWithCandidate(
        parser,
        theorem,
        env,
        holey,
        candidate,
        &report,
    ) orelse return null;
    return try keepIfConverts(theorem, env, candidate, filled);
}

/// The values a definition's arguments and hidden variables take when its
/// body is matched against `target` by transparent matching (`args` fixes
/// the arguments; line holes in `target` match anything). Caller frees.
/// Null when the body does not match.
fn matchDefBody(
    theorem: *TheoremContext,
    env: *const GlobalEnv,
    term: *const TermDecl,
    target: ExprId,
    args: ?[]const ExprId,
) !?[]?ExprId {
    const allocator = theorem.allocator;
    const arg_infos = try allocator.alloc(
        ArgInfo,
        term.args.len + term.dummy_args.len,
    );
    defer allocator.free(arg_infos);
    @memcpy(arg_infos[0..term.args.len], term.args);
    @memcpy(arg_infos[term.args.len..], term.dummy_args);
    const seeds = try allocator.alloc(DefOps.BindingSeed, arg_infos.len);
    defer allocator.free(seeds);
    @memset(seeds, .none);
    if (args) |fixed| for (fixed, 0..) |arg, idx| {
        seeds[idx] = .{ .exact = arg };
    };

    var def_ops = DefOps.Context.init(allocator, theorem, env);
    defer def_ops.deinit();
    def_ops.shared.line_holes_match_anything = true;
    var session = try def_ops.beginRuleMatch(arg_infos, seeds);
    defer session.deinit();
    // A fill is a fallback on the way to a diagnosed mismatch: a match
    // error is no match.
    const matched = session.matchTransparent(term.body.?, target) catch |err| {
        if (err == error.OutOfMemory) return err;
        return null;
    };
    if (!matched) return null;
    return try session.materializeOptionalBindings();
}

/// Fill holes like `materializeSurfaceWithCandidate`, except under an ACUI
/// combiner: there one hole standing for whole members takes the members of
/// the candidate the visible ones leave over, in any order (the fewest, under
/// idempotence; the unit when none are left). Null for a combination with
/// several holes or a hole inside a member (`acuiFrameObstacle` says which),
/// and wherever the visible parts do not fit.
///
/// Like the positional fill, the result is only a proposal: callers compare
/// it with the candidate modulo ACUI.
pub fn materializeSurfaceModuloAcui(
    parser: *MM0Parser,
    theorem: *TheoremContext,
    env: *const GlobalEnv,
    registry: *RewriteRegistry,
    canonicalizer: *Canonicalizer,
    holey: *const Expr,
    candidate: ExprId,
) !?ExprId {
    var report = ConcreteMatchReport{};
    const holey_term = switch (holey.*) {
        .term => |term| term,
        else => return try materializeSurfaceWithCandidate(
            parser,
            theorem,
            env,
            holey,
            candidate,
            &report,
        ),
    };
    if (!contains(holey)) {
        return try materializeSurfaceWithCandidate(
            parser,
            theorem,
            env,
            holey,
            candidate,
            &report,
        );
    }
    if (holey_term.args.len == 2) {
        if (try registry.resolveStructuralCombiner(env, holey_term.id)) |acui| {
            return try fillAcuiFrame(
                parser,
                theorem,
                env,
                canonicalizer,
                acui,
                holey,
                candidate,
            );
        }
    }

    const candidate_app = switch (theorem.interner.node(candidate).*) {
        .app => |app| app,
        else => return null,
    };
    if (holey_term.id != candidate_app.term_id or
        holey_term.args.len != candidate_app.args.len)
    {
        return null;
    }
    const args = try theorem.allocator.alloc(ExprId, holey_term.args.len);
    errdefer theorem.allocator.free(args);
    for (holey_term.args, candidate_app.args, 0..) |arg, candidate_arg, idx| {
        args[idx] = (try materializeSurfaceModuloAcui(
            parser,
            theorem,
            env,
            registry,
            canonicalizer,
            arg,
            candidate_arg,
        )) orelse {
            theorem.allocator.free(args);
            return null;
        };
    }
    return try theorem.interner.internAppOwned(holey_term.id, args);
}

fn fillAcuiFrame(
    parser: *MM0Parser,
    theorem: *TheoremContext,
    env: *const GlobalEnv,
    canonicalizer: *Canonicalizer,
    acui: ResolvedStructuralCombiner,
    holey: *const Expr,
    candidate: ExprId,
) !?ExprId {
    const allocator = theorem.allocator;
    var members = std.ArrayListUnmanaged(*const Expr){};
    defer members.deinit(allocator);
    try collectSurfaceMembers(allocator, holey, acui.head_term_id, &members);
    const frame_hole = switch (frameOf(env, acui, members.items)) {
        .frame => |hole| hole,
        .obstacle => return null,
    };

    const combiner = AcuiBag.Combiner.fromResolved(acui);
    const items_bag = combiner.flatten(
        theorem,
        try canonicalizer.canonicalize(candidate),
    ) orelse return null;
    const items = items_bag.slice();
    var before = AcuiBag.ExprBag{};
    var after = AcuiBag.ExprBag{};
    var past_hole = false;
    for (members.items) |member| {
        if (member == frame_hole) {
            past_hole = true;
            continue;
        }
        const visible = try canonicalizer.canonicalize(
            try theorem.internParsedExpr(member),
        );
        if (combiner.isUnit(theorem, visible)) continue;
        if (!(if (past_hole) after.append(visible) else before.append(visible))) return null;
    }

    // The hole takes the members the visible ones leave. Under C that is a
    // bag difference; in a sequence the visible members must be the
    // candidate's leading and trailing ones, and the hole takes the run
    // between them.
    var rest: std.ArrayListUnmanaged(ExprId) = .empty;
    defer rest.deinit(allocator);
    if (combiner.law.isCommutative()) {
        var visible = before;
        for (after.slice()) |member| if (!visible.append(member)) return null;
        rest = (try Views.subtractMembers(
            allocator,
            theorem,
            items,
            visible.slice(),
            combiner.law.isIdempotent(),
            true,
        )) orelse return null;
    } else {
        if (before.len + after.len > items.len) return null;
        const tail = items.len - after.len;
        if (!std.mem.eql(ExprId, items[0..before.len], before.slice())) return null;
        if (!std.mem.eql(ExprId, items[tail..], after.slice())) return null;
        try rest.appendSlice(allocator, items[before.len..tail]);
    }

    var report = ConcreteMatchReport{};
    const filled = (try materializeSurfaceWithCandidate(
        parser,
        theorem,
        env,
        frame_hole,
        (try combiner.build(theorem, rest.items)) orelse return null,
        &report,
    )) orelse return null;
    return try internWithFrame(
        theorem,
        holey,
        acui.head_term_id,
        frame_hole,
        filled,
    );
}

/// Why the first ACUI combination of `holey` that holds a hole cannot be
/// filled out of order, if one cannot.
pub fn acuiFrameObstacle(
    allocator: std.mem.Allocator,
    env: *const GlobalEnv,
    registry: *RewriteRegistry,
    holey: *const Expr,
) !?ConcreteMatchFailure {
    if (!contains(holey)) return null;
    const term = switch (holey.*) {
        .term => |term| term,
        else => return null,
    };
    if (term.args.len == 2) {
        if (try registry.resolveStructuralCombiner(env, term.id)) |acui| {
            var members = std.ArrayListUnmanaged(*const Expr){};
            defer members.deinit(allocator);
            try collectSurfaceMembers(
                allocator,
                holey,
                acui.head_term_id,
                &members,
            );
            // A member holding a hole is itself an obstacle, so there is
            // nothing further down to report.
            return switch (frameOf(env, acui, members.items)) {
                .frame => null,
                .obstacle => |obstacle| obstacle,
            };
        }
    }
    for (term.args) |arg| {
        if (try acuiFrameObstacle(allocator, env, registry, arg)) |obstacle| {
            return obstacle;
        }
    }
    return null;
}

const Frame = union(enum) {
    /// The combination's one hole, standing for whole members.
    frame: *const Expr,
    obstacle: ConcreteMatchFailure,
};

/// The hole that stands for the leftover members of a combination holding
/// at least one hole.
fn frameOf(
    env: *const GlobalEnv,
    acui: ResolvedStructuralCombiner,
    members: []const *const Expr,
) Frame {
    const combiner_name = env.terms.items[acui.head_term_id].name;
    var frame: ?*const Expr = null;
    for (members) |member| {
        switch (member.*) {
            .hole => |hole| {
                if (frame != null) return .{ .obstacle = .{
                    .acui_several_holes = .{
                        .combiner_name = combiner_name,
                        .token_span = hole.token_span,
                    },
                } };
                frame = member;
            },
            else => if (contains(member)) return .{ .obstacle = .{
                .acui_hole_in_member = .{
                    .combiner_name = combiner_name,
                    .token_span = firstHoleSourceSpan(member),
                },
            } },
        }
    }
    return .{ .frame = frame.? };
}

/// The members of a surface combination: its leaves under `head`.
fn collectSurfaceMembers(
    allocator: std.mem.Allocator,
    expr: *const Expr,
    head: u32,
    out: *std.ArrayListUnmanaged(*const Expr),
) !void {
    switch (expr.*) {
        .term => |term| if (term.id == head and term.args.len == 2) {
            try collectSurfaceMembers(allocator, term.args[0], head, out);
            try collectSurfaceMembers(allocator, term.args[1], head, out);
            return;
        },
        else => {},
    }
    try out.append(allocator, expr);
}

/// Intern a surface combination as written, with `filled` in place of the
/// frame hole.
fn internWithFrame(
    theorem: *TheoremContext,
    expr: *const Expr,
    head: u32,
    frame: *const Expr,
    filled: ExprId,
) !ExprId {
    if (expr == frame) return filled;
    switch (expr.*) {
        .term => |term| if (term.id == head and term.args.len == 2) {
            return try theorem.interner.internApp(head, &.{
                try internWithFrame(theorem, term.args[0], head, frame, filled),
                try internWithFrame(theorem, term.args[1], head, frame, filled),
            });
        },
        else => {},
    }
    return try theorem.internParsedExpr(expr);
}

/// Match a holey assertion against a selected concrete candidate.
///
/// This is intentionally a candidate-validation relation, not a candidate
/// inference relation.  Holes only check sort compatibility.  Visible subtrees
/// with no nested holes may match either exactly or by transparent definition
/// conversion; mixed trees still require the same visible head and arity before
/// recursing into their arguments.
pub fn matchesConcrete(
    allocator: std.mem.Allocator,
    parser: *MM0Parser,
    theorem: *TheoremContext,
    env: *const GlobalEnv,
    holey: *const Expr,
    concrete: ExprId,
    report: *ConcreteMatchReport,
) !bool {
    var def_ops = DefOps.Context.init(allocator, theorem, env);
    defer def_ops.deinit();
    return try matchesConcreteSemanticallyWithContext(
        &def_ops,
        parser,
        theorem,
        env,
        holey,
        concrete,
        report,
    );
}

fn matchesConcreteSemanticallyWithContext(
    def_ops: *DefOps.Context,
    parser: *MM0Parser,
    theorem: *TheoremContext,
    env: *const GlobalEnv,
    holey: *const Expr,
    concrete: ExprId,
    report: *ConcreteMatchReport,
) !bool {
    if (!contains(holey)) {
        const visible = try theorem.internParsedExpr(holey);
        if (visible == concrete) return true;
        if ((try def_ops.compareTransparent(visible, concrete)) != null) {
            return true;
        }
        setConcreteFailure(report, .visible_structure_mismatch);
        return false;
    }

    switch (holey.*) {
        .hole => |hole| return try holeFits(parser, theorem, env, hole, concrete, report),
        .variable => unreachable,
        .term => |holey_term| {
            const node = theorem.interner.node(concrete);
            const concrete_app = switch (node.*) {
                .app => |app| app,
                else => {
                    setConcreteFailure(report, .visible_structure_mismatch);
                    return false;
                },
            };
            if (holey_term.id != concrete_app.term_id) {
                setConcreteFailure(report, .visible_structure_mismatch);
                return false;
            }
            if (holey_term.args.len != concrete_app.args.len) {
                setConcreteFailure(report, .visible_structure_mismatch);
                return false;
            }
            for (holey_term.args, concrete_app.args) |arg, actual_arg| {
                if (!try matchesConcreteSemanticallyWithContext(
                    def_ops,
                    parser,
                    theorem,
                    env,
                    arg,
                    actual_arg,
                    report,
                )) return false;
            }
            return true;
        },
    }
}

/// True when `expr` has the sort of `hole`; otherwise records the mismatch.
fn holeFits(
    parser: *MM0Parser,
    theorem: *const TheoremContext,
    env: *const GlobalEnv,
    hole: anytype,
    expr: ExprId,
    report: *ConcreteMatchReport,
) !bool {
    const actual_sort_name = try exprIdSortName(theorem, env, expr);
    const actual_sort = parser.core.sort_names.get(actual_sort_name) orelse
        return error.UnknownSort;
    if (hole.sort == actual_sort) return true;
    setConcreteFailure(report, .{ .hole_sort_mismatch = .{
        .token = hole.token,
        .token_span = hole.token_span,
        .expected_sort_name = sortName(parser, hole.sort),
        .actual_sort_name = actual_sort_name,
    } });
    return false;
}

fn setInferenceFailure(
    maybe_report: ?*InferenceReport,
    failure: InferenceFailure,
) void {
    const report = maybe_report orelse return;
    if (report.failure == null) report.failure = failure;
}

fn setConcreteFailure(
    report: *ConcreteMatchReport,
    failure: ConcreteMatchFailure,
) void {
    if (report.failure == null) report.failure = failure;
}

fn firstMissingBinding(bindings: []const ?ExprId) ?usize {
    for (bindings, 0..) |binding, idx| {
        if (binding == null) return idx;
    }
    return null;
}

const TestFixture = struct {
    parser: MM0Parser,
    env: GlobalEnv,
    theorem: TheoremContext,
    vars: NameExprMap,
    sort_vars: SortVarRegistry,
    rule_id: u32,
    wff_sort: u7,
    obj_sort: u7,

    fn init(allocator: std.mem.Allocator) !TestFixture {
        const src =
            \\delimiter $ ( ) $;
            \\provable sort wff;
            \\sort obj;
            \\term imp (a b: wff): wff; infixr imp: $->$ prec 25;
            \\axiom ax_keep (a b: wff): $ a $ > $ a -> b -> a $;
            \\theorem th (a b: wff): $ a $ > $ a -> b -> a $;
        ;

        var parser = MM0Parser.init(src, allocator);
        var env = GlobalEnv.init(allocator);
        var theorem_assertion: ?@import(
            "../../trusted/parse.zig",
        ).AssertionStmt = null;
        var rule_id: ?u32 = null;

        while (try parser.next()) |stmt| {
            try env.addStmt(stmt);
            switch (stmt) {
                .assertion => |assertion| {
                    if (std.mem.eql(u8, assertion.name, "ax_keep")) {
                        rule_id = @intCast(env.rules.items.len - 1);
                    }
                    if (std.mem.eql(u8, assertion.name, "th")) {
                        theorem_assertion = assertion;
                    }
                },
                else => {},
            }
        }
        try parser.registerHoleTokenForSort("wff", "_wff");

        var theorem = TheoremContext.init(allocator);
        try theorem.seedAssertion(theorem_assertion.?);

        var vars = NameExprMap.init(allocator);
        for (
            theorem_assertion.?.arg_names,
            theorem_assertion.?.arg_exprs,
        ) |maybe_name, expr| {
            if (maybe_name) |name| try vars.put(name, expr);
        }

        return .{
            .parser = parser,
            .env = env,
            .theorem = theorem,
            .vars = vars,
            .sort_vars = SortVarRegistry.init(allocator),
            .rule_id = rule_id.?,
            .wff_sort = @intCast(parser.core.sort_names.get("wff").?),
            .obj_sort = @intCast(parser.core.sort_names.get("obj").?),
        };
    }

    fn deinit(self: *TestFixture) void {
        self.sort_vars.deinit();
        self.vars.deinit();
        self.theorem.deinit();
    }
};

test "hole detection walks nested surface expressions" {
    const allocator = std.testing.allocator;
    const hole = try allocator.create(Expr);
    defer allocator.destroy(hole);
    hole.* = .{ .hole = .{ .sort = 0, .token = "_wff" } };

    const variable = try allocator.create(Expr);
    defer allocator.destroy(variable);
    variable.* = .{ .variable = .{
        .sort = 0,
        .bound = false,
        .deps = 0,
    } };

    const args = try allocator.alloc(*const Expr, 2);
    defer allocator.free(args);
    args[0] = variable;
    args[1] = hole;

    const term = try allocator.create(Expr);
    defer allocator.destroy(term);
    term.* = .{ .term = .{
        .sort = 0,
        .deps = 0,
        .id = 0,
        .args = args,
    } };

    try std.testing.expect(!contains(variable));
    try std.testing.expect(contains(hole));
    try std.testing.expect(contains(term));
}

test "holey assertion parse keeps holes out of the theorem dag" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var fixture = try TestFixture.init(arena.allocator());
    defer fixture.deinit();

    const before = fixture.theorem.interner.count();
    const holey = try parseAssertion(
        &fixture.parser,
        &fixture.theorem,
        &fixture.vars,
        &fixture.sort_vars,
        "_wff -> b -> _wff",
    );
    try std.testing.expectEqual(before, fixture.theorem.interner.count());
    try std.testing.expectEqual(.holey, std.meta.activeTag(holey));

    const concrete = try parseAssertion(
        &fixture.parser,
        &fixture.theorem,
        &fixture.vars,
        &fixture.sort_vars,
        "a -> b -> a",
    );
    try std.testing.expectEqual(.concrete, std.meta.activeTag(concrete));
    try std.testing.expect(fixture.theorem.interner.count() > before);
}

test "holey matching checks concrete hole sorts" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var fixture = try TestFixture.init(arena.allocator());
    defer fixture.deinit();

    const concrete_parsed = try fixture.parser.parseMathText(
        "a -> b -> a",
        &fixture.vars,
    );
    const concrete = try fixture.theorem.internParsedExpr(concrete_parsed);
    const holey = try fixture.parser.parseHoleyFormulaText(
        "_wff -> b -> _wff",
        &fixture.vars,
    );
    var report = ConcreteMatchReport{};
    try std.testing.expect(try matchesConcrete(
        arena.allocator(),
        &fixture.parser,
        &fixture.theorem,
        &fixture.env,
        holey,
        concrete,
        &report,
    ));

    const wrong_hole = try arena.allocator().create(Expr);
    wrong_hole.* = .{ .hole = .{
        .sort = fixture.obj_sort,
        .token = "_obj",
    } };
    try std.testing.expect(!try matchesConcrete(
        arena.allocator(),
        &fixture.parser,
        &fixture.theorem,
        &fixture.env,
        wrong_hole,
        fixture.theorem.theorem_vars.items[0],
        &report,
    ));
    try std.testing.expectEqual(.hole_sort_mismatch, std.meta.activeTag(report.failure.?));
}

test "holey template matching binds visible conclusion structure" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var fixture = try TestFixture.init(arena.allocator());
    defer fixture.deinit();

    const rule = &fixture.env.rules.items[fixture.rule_id];
    const holey = try fixture.parser.parseHoleyFormulaText(
        "_wff -> b -> _wff",
        &fixture.vars,
    );
    const partial = try arena.allocator().alloc(?ExprId, rule.args.len);
    @memset(partial, null);

    try std.testing.expect(try matchTemplateToSurface(
        &fixture.theorem,
        rule.concl,
        holey,
        partial,
        null,
    ));
    try std.testing.expect(partial[0] == null);
    try std.testing.expect(partial[1] != null);
}

test "holey template matching leaves a binder facing a holey subterm unbound" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var fixture = try TestFixture.init(arena.allocator());
    defer fixture.deinit();

    const rule = &fixture.env.rules.items[fixture.rule_id];
    const partial = try arena.allocator().alloc(?ExprId, rule.args.len);
    const a = try fixture.theorem.internParsedExpr(fixture.vars.get("a").?);
    const b = try fixture.theorem.internParsedExpr(fixture.vars.get("b").?);

    // `a` first faces `a -> _wff`, which fixes nothing, then binds to the
    // concrete `a -> b` at its second occurrence.
    @memset(partial, null);
    const later_concrete = try fixture.parser.parseHoleyFormulaText(
        "(a -> _wff) -> b -> (a -> b)",
        &fixture.vars,
    );
    try std.testing.expect(try matchTemplateToSurface(
        &fixture.theorem,
        rule.concl,
        later_concrete,
        partial,
        null,
    ));
    try std.testing.expect(partial[0] != null);
    try std.testing.expectEqual(b, partial[1].?);

    // A binding made before the holey subterm is kept as it is.
    @memset(partial, null);
    partial[0] = a;
    const holey_only = try fixture.parser.parseHoleyFormulaText(
        "(b -> _wff) -> b -> _wff",
        &fixture.vars,
    );
    try std.testing.expect(try matchTemplateToSurface(
        &fixture.theorem,
        rule.concl,
        holey_only,
        partial,
        null,
    ));
    try std.testing.expectEqual(a, partial[0].?);
    try std.testing.expectEqual(b, partial[1].?);
}
