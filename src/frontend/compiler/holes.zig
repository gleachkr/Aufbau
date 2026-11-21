const std = @import("std");
const ArenaAllocator = @import("../arena_allocator.zig").ArenaAllocator;

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
const Canonicalizer = @import("../normalizer.zig").Canonicalizer;
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

    const unknown_tag = "@unknown";
    var prefix: ?[]const u8 = null;
    for (annotations) |ann| {
        if (!annotationMatchesTag(ann, unknown_tag)) continue;

        if (prefix != null) return error.DuplicateUnknownAnnotation;
        const tail = std.mem.trim(u8, ann[unknown_tag.len..], " \t\r\n");
        var iter = std.mem.tokenizeAny(u8, tail, " \t\r\n");
        const token = iter.next() orelse return error.InvalidUnknownAnnotation;
        if (iter.next() != null) return error.InvalidUnknownAnnotation;
        var var_tokens = sort_vars.tokens.keyIterator();
        while (var_tokens.next()) |var_token| {
            if (std.mem.startsWith(u8, var_token.*, token) and var_token.len > token.len) {
                return error.UnknownPrefixCollision;
            }
        }
        prefix = token;
    }

    if (prefix) |token| {
        try parser.registerUnknownPrefixForSort(sort_name, token);
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
    /// Out-of-order filling takes at most one bare hole per ACUI
    /// combination.
    acui_several_holes: struct {
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
/// number of holey lines. A named unknown's hole keeps its name
/// (`PlaceholderInfo.name`) for printing. Null when a hole's sort is unknown.
pub fn internWithLineHoles(
    theorem: *TheoremContext,
    env: *const GlobalEnv,
    holey: *const Expr,
) !?ExprId {
    return SurfaceExpr.internHoley(theorem, env, holey, {}, mintLineHole);
}

fn mintLineHole(_: void, theorem: *TheoremContext, sort_name: []const u8, name: ?[]const u8) anyerror!?ExprId {
    return try theorem.addNamedLineHolePlaceholder(sort_name, name);
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
    def_ops.shared.holes_match_anything = true;
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

/// Names filled while filling a line (`materializeSurfaceModuloAcui`): each
/// occurrence of a named unknown takes one value.
pub const NameFills = struct {
    /// Values names already have.
    bound: *const std.StringHashMapUnmanaged(ExprId),
    /// Names this fill binds, in binding order, so a failed pairing can
    /// drop the ones it added.
    fills: std.StringArrayHashMapUnmanaged(ExprId) = .empty,
    /// The pairing search stopped at `pairing_step_limit`.
    limit_hit: bool = false,

    pub fn deinit(self: *NameFills, allocator: std.mem.Allocator) void {
        self.fills.deinit(allocator);
    }
};

/// Pairings one `materializeSurfaceModuloAcui` call with names may try.
/// Only names make pairing a search: without them each member's fit is
/// independent, and one matching decides.
pub const pairing_step_limit = 1_000_000;

/// Fill holes like `materializeSurfaceWithCandidate`, except under an ACUI
/// combiner, where a member holding a hole is not tied to its position.
/// Under commutativity each such member is paired with a member of the
/// candidate the hole-free ones leave, and a bare hole takes the members
/// left after that: the fewest, under idempotence, and the unit when none
/// are left. In a sequence the members before and after the bare hole are
/// the candidate's first and last ones, in order, and the hole takes the
/// run between them. Null for a combination with two bare holes
/// (`acuiFrameObstacle`), and wherever the visible parts do not fit.
///
/// With `names`, every occurrence of a named unknown takes one value: a
/// pairing that fills a name two ways is undone and another one tried, up
/// to `pairing_step_limit` tries (then null, with `names.limit_hit` set).
/// Without `names` holes are independent.
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
    names: ?*NameFills,
) !?ExprId {
    var fill: AcuiFill = .{
        .parser = parser,
        .theorem = theorem,
        .env = env,
        .registry = registry,
        .canonicalizer = canonicalizer,
        .names = names,
    };
    return fill.fill(holey, candidate) catch |err| switch (err) {
        error.PairingStepLimit => {
            names.?.limit_hit = true;
            return null;
        },
        else => return err,
    };
}

const AcuiFill = struct {
    parser: *MM0Parser,
    theorem: *TheoremContext,
    env: *const GlobalEnv,
    registry: *RewriteRegistry,
    canonicalizer: *Canonicalizer,
    names: ?*NameFills,
    steps: usize = 0,

    fn fill(self: *AcuiFill, holey: *const Expr, candidate: ExprId) anyerror!?ExprId {
        var report = ConcreteMatchReport{};
        if (!contains(holey)) {
            // A part without holes must be its candidate, as written: a
            // pairing is chosen by what fits.
            const written = try self.theorem.internParsedExpr(holey);
            if (try self.same(written, candidate)) return written;
            return try keepIfConverts(self.theorem, self.env, candidate, written);
        }
        switch (holey.*) {
            .variable => unreachable,
            .hole => |hole| {
                if (!try holeFits(self.parser, self.theorem, self.env, hole, candidate, &report)) {
                    return null;
                }
                const name = hole.name orelse return candidate;
                const names = self.names orelse return candidate;
                const value = names.bound.get(name) orelse names.fills.get(name) orelse {
                    try names.fills.put(self.theorem.allocator, name, candidate);
                    return candidate;
                };
                return if (try self.same(value, candidate)) candidate else null;
            },
            .term => |term| {
                if (term.args.len == 2) {
                    if (try self.registry.resolveStructuralCombiner(self.env, term.id)) |acui| {
                        return try self.fillCombination(acui, holey, candidate);
                    }
                }
                const app = switch (self.theorem.interner.node(candidate).*) {
                    .app => |app| app,
                    else => return null,
                };
                if (term.id != app.term_id or term.args.len != app.args.len) return null;
                const args = try self.theorem.allocator.alloc(ExprId, term.args.len);
                defer self.theorem.allocator.free(args);
                for (term.args, app.args, args) |arg, candidate_arg, *out| {
                    out.* = (try self.fill(arg, candidate_arg)) orelse return null;
                }
                return try self.theorem.interner.internApp(term.id, args);
            },
        }
    }

    fn same(self: *AcuiFill, lhs: ExprId, rhs: ExprId) !bool {
        if (lhs == rhs) return true;
        return (try self.canonicalizer.canonicalize(lhs)) ==
            (try self.canonicalizer.canonicalize(rhs));
    }

    /// The members of a combination holding a hole, sorted out.
    const Bag = struct {
        combiner: AcuiBag.Combiner,
        members: []const *const Expr,
        /// Each member's fill, set as members are placed.
        member_fills: []ExprId,
        /// The members that take an item of the candidate, in order: the
        /// visible ones (units written out take none) and those holding
        /// a hole that are not a bare hole.
        placed: std.ArrayListUnmanaged(usize) = .empty,
        /// How many of `placed` come before the bare hole.
        before: usize = 0,
        /// The bare hole taking the members nothing else takes.
        frame: ?usize = null,

        fn isOpen(self: *const Bag, idx: usize) bool {
            return contains(self.members[idx]);
        }
    };

    fn fillCombination(
        self: *AcuiFill,
        acui: ResolvedStructuralCombiner,
        holey: *const Expr,
        candidate: ExprId,
    ) !?ExprId {
        const allocator = self.theorem.allocator;
        var members: std.ArrayListUnmanaged(*const Expr) = .empty;
        defer members.deinit(allocator);
        try collectSurfaceMembers(allocator, holey, acui.head_term_id, &members);
        const combiner = AcuiBag.Combiner.fromResolved(acui);
        const items = combiner.flatten(
            self.theorem,
            try self.canonicalizer.canonicalize(candidate),
        ) orelse return null;

        var bag: Bag = .{
            .combiner = combiner,
            .members = members.items,
            .member_fills = try allocator.alloc(ExprId, members.items.len),
        };
        defer allocator.free(bag.member_fills);
        defer bag.placed.deinit(allocator);
        for (members.items, 0..) |member, idx| {
            if (member.* == .hole) {
                if (bag.frame != null) return null;
                bag.frame = idx;
                continue;
            }
            if (!contains(member)) {
                const written = try self.theorem.internParsedExpr(member);
                bag.member_fills[idx] = written;
                if (combiner.isUnit(self.theorem, try self.canonicalizer.canonicalize(written))) {
                    continue;
                }
            }
            try bag.placed.append(allocator, idx);
            if (bag.frame == null) bag.before += 1;
        }

        const placed = if (combiner.law.isCommutative())
            try self.pairMembers(&bag, items.slice())
        else
            try self.alignMembers(&bag, items.slice());
        if (!placed) return null;
        var next: usize = 0;
        return try rebuildMembers(
            self.theorem,
            holey,
            acui.head_term_id,
            bag.member_fills,
            &next,
        );
    }

    /// A visible member's value as the candidate's members are read.
    fn visibleValue(self: *AcuiFill, bag: *const Bag, idx: usize) !ExprId {
        return try self.canonicalizer.canonicalize(bag.member_fills[idx]);
    }

    /// Sequence: the members before the bare hole fill from the candidate's
    /// first ones, those after it from its last ones; the hole takes the
    /// run between. Without a bare hole the counts agree.
    fn alignMembers(self: *AcuiFill, bag: *Bag, items: []const ExprId) !bool {
        const placed = bag.placed.items;
        if (placed.len > items.len) return false;
        if (bag.frame == null and placed.len != items.len) return false;
        const tail = items.len - (placed.len - bag.before);
        for (placed, 0..) |idx, k| {
            const item = if (k < bag.before) items[k] else items[tail + (k - bag.before)];
            if (!bag.isOpen(idx)) {
                if (try self.visibleValue(bag, idx) != item) return false;
                continue;
            }
            bag.member_fills[idx] = (try self.fill(bag.members[idx], item)) orelse return false;
        }
        return try self.fillFrame(bag, items[bag.before..tail]);
    }

    /// Commutative: visible members take their copies of the candidate's
    /// members, and each open member is paired with one of the rest.
    fn pairMembers(self: *AcuiFill, bag: *Bag, items: []const ExprId) !bool {
        const allocator = self.theorem.allocator;
        var visible = AcuiBag.ExprBag{};
        var open: std.ArrayListUnmanaged(usize) = .empty;
        defer open.deinit(allocator);
        for (bag.placed.items) |idx| {
            if (bag.isOpen(idx)) {
                try open.append(allocator, idx);
            } else if (!visible.append(try self.visibleValue(bag, idx))) return false;
        }
        var rest = (try Views.subtractMembers(
            allocator,
            self.theorem,
            items,
            visible.slice(),
            bag.combiner.law.isIdempotent(),
            true,
        )) orelse return false;
        defer rest.deinit(allocator);

        var pairing: Pairing = .{
            .allocator = allocator,
            .bag = bag,
            .open = open.items,
            .rest = rest.items,
            .idempotent = bag.combiner.law.isIdempotent(),
            .fits = try allocator.alloc(?ExprId, open.items.len * rest.items.len),
            .compat = try allocator.alloc(bool, open.items.len * rest.items.len),
            .taken = try allocator.alloc(usize, rest.items.len),
        };
        defer pairing.deinit();
        @memset(pairing.taken, 0);
        // Each open member against each item, its names filled on their
        // own: a pairing that fits with names fits here.
        var named = false;
        {
            const names = self.names;
            defer self.names = names;
            self.names = null;
            for (open.items, 0..) |idx, i| {
                if (SurfaceExpr.containsNamedHole(bag.members[idx])) named = true;
                for (rest.items, 0..) |item, j| {
                    const fit = try self.fill(bag.members[idx], item);
                    pairing.fits[i * rest.items.len + j] = fit;
                    pairing.compat[i * rest.items.len + j] = fit != null;
                }
            }
        }
        const chosen = try allocator.alloc(usize, open.items.len);
        defer allocator.free(chosen);
        if (!try pairing.match(chosen)) return false;
        if (!named or self.names == null) {
            for (open.items, chosen, 0..) |idx, j, i| {
                bag.member_fills[idx] = pairing.fits[i * rest.items.len + j].?;
                pairing.taken[j] += 1;
            }
            return try self.fillLeft(&pairing);
        }
        return try self.search(&pairing, 0);
    }

    const Pairing = struct {
        allocator: std.mem.Allocator,
        bag: *Bag,
        open: []const usize,
        rest: []const ExprId,
        idempotent: bool,
        /// `fits[i * rest.len + j]`: open member `i` filled from item `j`,
        /// names filled on their own.
        fits: []?ExprId,
        compat: []bool,
        /// How many open members each item is paired with.
        taken: []usize,

        fn deinit(self: *Pairing) void {
            self.allocator.free(self.fits);
            self.allocator.free(self.compat);
            self.allocator.free(self.taken);
        }

        fn fitsItem(self: *const Pairing, i: usize, j: usize) bool {
            return self.compat[i * self.rest.len + j];
        }

        /// A pairing of every open member, names ignored, into `chosen`.
        /// Without idempotence each member takes an item of its own, and
        /// without a bare hole they take every item. Under idempotence an
        /// item may be shared; the most items are taken, so the bare hole
        /// takes the fewest, and without one every item is taken.
        fn match(self: *const Pairing, chosen: []usize) !bool {
            const open = self.open.len;
            const items = self.rest.len;
            if (!self.idempotent) {
                if (open > items) return false;
                if (self.bag.frame == null and open != items) return false;
                var matching = try AcuiBag.Matching.init(self.allocator, self.compat, open, items);
                defer matching.deinit(self.allocator);
                if (!matching.run(null)) return false;
                for (matching.owner, 0..) |owner, j| if (owner) |i| {
                    chosen[i] = j;
                };
                return true;
            }
            const transposed = try self.allocator.alloc(bool, open * items);
            defer self.allocator.free(transposed);
            for (0..open) |i| for (0..items) |j| {
                transposed[j * open + i] = self.fitsItem(i, j);
            };
            var matching = try AcuiBag.Matching.init(self.allocator, transposed, items, open);
            defer matching.deinit(self.allocator);
            if (matching.runMaximum() != items and self.bag.frame == null) return false;
            for (chosen, 0..) |*out, i| {
                out.* = matching.owner[i] orelse for (0..items) |j| {
                    if (self.fitsItem(i, j)) break j;
                } else return false;
            }
            return true;
        }
    };

    /// Pair `pairing.open[k..]` with names filled alike, by search over the
    /// pairs `match` allows; then fill the bare hole.
    fn search(self: *AcuiFill, pairing: *Pairing, k: usize) !bool {
        if (k == pairing.open.len) return try self.fillLeft(pairing);
        const names = self.names.?;
        const idx = pairing.open[k];
        for (pairing.rest, 0..) |item, j| {
            if (!pairing.fitsItem(k, j)) continue;
            if (pairing.taken[j] != 0 and !pairing.idempotent) continue;
            // An item equal to one tried before, in the same state, fills
            // alike.
            if (std.mem.indexOfScalar(ExprId, pairing.rest[0..j], item)) |earlier| {
                if ((pairing.taken[earlier] == 0) == (pairing.taken[j] == 0)) continue;
            }
            self.steps += 1;
            if (self.steps > pairing_step_limit) return error.PairingStepLimit;
            const mark = names.fills.count();
            if (try self.fill(pairing.bag.members[idx], item)) |member_fill| {
                pairing.taken[j] += 1;
                pairing.bag.member_fills[idx] = member_fill;
                if (try self.search(pairing, k + 1)) return true;
                pairing.taken[j] -= 1;
            }
            names.fills.shrinkRetainingCapacity(mark);
        }
        return false;
    }

    /// The bare hole takes the items no open member takes; without one,
    /// there must be none.
    fn fillLeft(self: *AcuiFill, pairing: *const Pairing) !bool {
        var left: std.ArrayListUnmanaged(ExprId) = .empty;
        defer left.deinit(self.theorem.allocator);
        for (pairing.rest, pairing.taken) |item, taken| {
            if (taken == 0) try left.append(self.theorem.allocator, item);
        }
        return try self.fillFrame(pairing.bag, left.items);
    }

    fn fillFrame(self: *AcuiFill, bag: *Bag, left: []const ExprId) !bool {
        const frame = bag.frame orelse return left.len == 0;
        const value = (try bag.combiner.build(self.theorem, left)) orelse return false;
        const mark = if (self.names) |names| names.fills.count() else 0;
        bag.member_fills[frame] = (try self.fill(bag.members[frame], value)) orelse {
            if (self.names) |names| names.fills.shrinkRetainingCapacity(mark);
            return false;
        };
        return true;
    }
};

/// `expr`'s spine under `head` with its members, left to right, replaced
/// by `fills`.
fn rebuildMembers(
    theorem: *TheoremContext,
    expr: *const Expr,
    head: u32,
    fills: []const ExprId,
    next: *usize,
) !ExprId {
    switch (expr.*) {
        .term => |term| if (term.id == head and term.args.len == 2) {
            const lhs = try rebuildMembers(theorem, term.args[0], head, fills, next);
            const rhs = try rebuildMembers(theorem, term.args[1], head, fills, next);
            return try theorem.interner.internApp(head, &.{ lhs, rhs });
        },
        else => {},
    }
    defer next.* += 1;
    return fills[next.*];
}

/// Why the first ACUI combination of `holey` that holds a hole cannot be
/// filled out of order, if one cannot: it has two bare holes, which could
/// split the leftover members any way.
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
            var members = std.ArrayListUnmanaged(*const Expr).empty;
            defer members.deinit(allocator);
            try collectSurfaceMembers(allocator, holey, acui.head_term_id, &members);
            var frame: ?*const Expr = null;
            for (members.items) |member| {
                if (member.* != .hole) {
                    if (try acuiFrameObstacle(allocator, env, registry, member)) |obstacle| {
                        return obstacle;
                    }
                    continue;
                }
                if (frame != null) return .{ .acui_several_holes = .{
                    .combiner_name = env.terms.items[acui.head_term_id].name,
                    .token_span = member.hole.token_span,
                } };
                frame = member;
            }
            return null;
        }
    }
    for (term.args) |arg| {
        if (try acuiFrameObstacle(allocator, env, registry, arg)) |obstacle| {
            return obstacle;
        }
    }
    return null;
}

/// The members of a surface combination: its leaves under `head`.
pub fn collectSurfaceMembers(
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

test "holey assertion parse interns nothing" {
    var arena = ArenaAllocator.init(std.testing.allocator);
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
    var arena = ArenaAllocator.init(std.testing.allocator);
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
    var arena = ArenaAllocator.init(std.testing.allocator);
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
    var arena = ArenaAllocator.init(std.testing.allocator);
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
