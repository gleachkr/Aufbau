const std = @import("std");
const GlobalEnv = @import("./env.zig").GlobalEnv;
const RuleDecl = @import("./env.zig").RuleDecl;
const TemplateExpr = @import("./rules.zig").TemplateExpr;
const hasPremiseOnlyBinder = @import("./rules.zig").hasPremiseOnlyBinder;
const templateBinderMask = @import("./rules.zig").templateBinderMask;

/// True when a rule has a premise-only binder (see
/// `rules.hasPremiseOnlyBinder`) — the binder a backward application would
/// have to defer. `@auto eager` rejects such rules because their
/// invertible-shape guarantee fails.
fn ruleDefersWitness(rule: *const RuleDecl) bool {
    return hasPremiseOnlyBinder(rule.concl, rule.hyps);
}

/// A relation bundle defines an equivalence relation on a sort, with the
/// theorem names needed to compose conversion proofs.
pub const RelationBundle = struct {
    sort_name: []const u8,
    rel_term_name: []const u8,
    refl_name: []const u8,
    trans_name: []const u8,
    symm_name: []const u8,
    transport_name: []const u8,
    /// Resolved lazily from names.
    rel_term_id: ?u32 = null,
    refl_id: ?u32 = null,
    trans_id: ?u32 = null,
    symm_id: ?u32 = null,
    transport_id: ?u32 = null,
    /// Lazily-computed shape verdict: bundle rules must have no bound
    /// binders, or the lines extraction emits from them carry
    /// disjointness obligations nothing discharges.
    shape_ok: ?bool = null,
};

/// Resolved relation with all IDs known.
pub const ResolvedRelation = struct {
    /// The operand sort the relation equates.
    sort_name: []const u8,
    rel_term_id: u32,
    refl_id: u32,
    trans_id: u32,
    symm_id: u32,
    transport_id: ?u32,
};

/// One `@auto trigger` pattern: a prefix term tree e-matched against the
/// goal's subterms by the `auto?` seeding retry phase. A `binder` node
/// captures the annotated rule's binder at that index from the matched
/// position; `wildcard` matches anything. Ground by construction: every rule
/// binder not named by the pattern must default to an ACUI unit (validated
/// at annotation time), so each match mints one fully concrete rule instance.
pub const TriggerPattern = union(enum) {
    app: App,
    binder: usize,
    wildcard,

    pub const App = struct {
        term_id: u32,
        args: []const TriggerPattern,
    };
};

/// A rewrite rule: lhs ~ rhs, indexed by the head term_id of lhs.
pub const RewriteRule = struct {
    rule_id: u32,
    lhs: TemplateExpr,
    rhs: TemplateExpr,
    num_binders: usize,
    head_term_id: u32,
};

/// The role a `@conversion` annotation assigns its theorem. Direction
/// tokens (`ltr`/`rtl`/`both`) enroll ordinary saturation rules; the role
/// tokens `assoc`/`comm` instead certify the conclusion head's algebraic
/// law, letting `conversion?` absorb it into term representation (see
/// `docs/design_notes/ac_representation.md`). Role-annotated theorems are
/// validated against the exact law shape at annotation time.
pub const ConversionRole = enum { none, assoc, comm };

/// A `@conversion` rule: a hypothesis-free theorem concluding `rel(lhs, rhs)`
/// for a registered `@relation`, enrolled for egraph saturation in
/// `conversion?` search. `ltr`/`rtl` record which orientations may be
/// e-matched (the matched side's binders instantiate the other side); a
/// `both` annotation sets both flags. Unlike `@rewrite` rules these never
/// feed the normalizer, so enrollment cannot change any existing search or
/// compilation behavior.
///
/// A role-annotated theorem (`role != .none`) records `head_term_id` — the
/// binary operator whose law it certifies. Until the bag representation
/// lands these enroll with both direction flags set (identical to `both`),
/// so enrollment stays semantics-preserving.
pub const ConversionRule = struct {
    rule_id: u32,
    lhs: TemplateExpr,
    rhs: TemplateExpr,
    num_binders: usize,
    ltr: bool,
    rtl: bool,
    role: ConversionRole = .none,
    /// The certified operator for a role rule; null for direction rules.
    head_term_id: ?u32 = null,
};

/// A `@conversion`-enrolled definition: the def's own equation
/// `rel(definiens, head args)` as rule templates for egraph saturation.
/// `lhs` is the definiens (binder space = the def's args followed by its
/// hidden dummies, matching `TermDecl.body`); `rhs` is the synthesized head
/// application over the arg binders. `fold` e-matches the definiens and
/// instantiates the head; `unfold` the reverse. A def with hidden dummy
/// binders may only enroll `fold`: unfolding would have to invent a dummy
/// witness at every match (see
/// `docs/design_notes/conversion_def_folding.md`).
pub const DefConversionRule = struct {
    term_id: u32,
    lhs: TemplateExpr,
    rhs: TemplateExpr,
    num_binders: usize,
    fold: bool,
    unfold: bool,
};

/// A special alpha-renaming rule used only by freshening.
pub const AlphaRule = struct {
    rule_id: u32,
    lhs: TemplateExpr,
    rhs: TemplateExpr,
    num_binders: usize,
    head_term_id: u32,
    old_idx: usize,
    new_idx: usize,
};

/// A congruence rule for a specific head term.
pub const CongruenceRule = struct {
    rule_id: u32,
    head_term_id: u32,
    num_binders: usize,
};

const UnitRule = struct {
    rule_id: u32,
    reversed: bool,
};

pub const StructuralCombiner = struct {
    unit_term_name: []const u8,
    assoc_name: []const u8,
    comm_name: ?[]const u8,
    idem_name: ?[]const u8,
    unit_term_id: ?u32 = null,
    assoc_id: ?u32 = null,
    comm_id: ?u32 = null,
    idem_id: ?u32 = null,
    left_unit_rule: ?UnitRule = null,
    right_unit_rule: ?UnitRule = null,
    left_unit_rule_searched: bool = false,
    right_unit_rule_searched: bool = false,
};

pub const ResolvedStructuralCombiner = struct {
    head_term_id: u32,
    unit_term_id: u32,
    assoc_id: u32,
    comm_id: ?u32,
    idem_id: ?u32,
    left_unit_rule_id: ?u32,
    left_unit_rule_reversed: bool,
    right_unit_rule_id: ?u32,
    right_unit_rule_reversed: bool,

    pub fn supportsLeftUnit(self: ResolvedStructuralCombiner) bool {
        return self.left_unit_rule_id != null or
            (self.comm_id != null and self.right_unit_rule_id != null);
    }

    pub fn supportsRightUnit(self: ResolvedStructuralCombiner) bool {
        return self.right_unit_rule_id != null or
            (self.comm_id != null and self.left_unit_rule_id != null);
    }
};

pub const RewriteRegistry = struct {
    allocator: std.mem.Allocator,
    /// Relation bundles keyed by sort name.
    relations: std.StringHashMap(RelationBundle),
    /// Rewrite rules indexed by LHS head term_id.
    rewrites_by_head: std.AutoHashMap(
        u32,
        std.ArrayListUnmanaged(RewriteRule),
    ),
    /// Alpha rules indexed by LHS head term_id.
    alpha_by_head: std.AutoHashMap(
        u32,
        std.ArrayListUnmanaged(AlphaRule),
    ),
    /// Congruence rules by head term_id.
    congr_by_head: std.AutoHashMap(u32, CongruenceRule),
    /// Fallback rules by rule_id.
    fallbacks: std.AutoHashMap(u32, u32),
    /// Rules marked for `auto?` forward saturation.
    auto_forward_rules: std.AutoHashMap(u32, void),
    /// Rules whose unresolved hypothesis binders may become existential
    /// subgoal holes in `auto?` backward generation.
    auto_backward_rules: std.AutoHashMap(u32, void),
    /// `@auto eager` rules by rule_id → intra-band priority (1 = tried
    /// earliest). Eager implies backward enrollment and is validated at
    /// annotation time to have every hypothesis binder conclusion-determined
    /// (see `processEager`).
    auto_eager_rules: std.AutoHashMap(u32, u8),
    /// ACUI structural metadata by combiner head term_id.
    acui_by_head: std.AutoHashMap(u32, StructuralCombiner),
    /// `@auto trigger` patterns by rule_id (one list entry per annotation
    /// line). Only hypothesis-free rules may carry triggers.
    trigger_by_rule: std.AutoHashMap(
        u32,
        std.ArrayListUnmanaged(TriggerPattern),
    ),
    /// `@conversion` rules in declaration order. The egraph builds its own
    /// match-side head indexes per search call; the registry keeps a flat
    /// list.
    conversions: std.ArrayListUnmanaged(ConversionRule) = .{},
    /// `@conversion`-enrolled defs in declaration order.
    def_conversions: std.ArrayListUnmanaged(DefConversionRule) = .{},
    /// `@compute` rules in declaration order: single-direction conversion
    /// rules (exactly one of ltr/rtl, role always .none) the egraph
    /// applies through its directed fold scheduler instead of general
    /// saturation.
    computes: std.ArrayListUnmanaged(ConversionRule) = .{},

    pub fn init(allocator: std.mem.Allocator) RewriteRegistry {
        return .{
            .allocator = allocator,
            .relations = std.StringHashMap(RelationBundle).init(allocator),
            .rewrites_by_head = std.AutoHashMap(
                u32,
                std.ArrayListUnmanaged(RewriteRule),
            ).init(allocator),
            .alpha_by_head = std.AutoHashMap(
                u32,
                std.ArrayListUnmanaged(AlphaRule),
            ).init(allocator),
            .congr_by_head = std.AutoHashMap(u32, CongruenceRule).init(
                allocator,
            ),
            .fallbacks = std.AutoHashMap(u32, u32).init(allocator),
            .auto_forward_rules = std.AutoHashMap(u32, void).init(allocator),
            .auto_backward_rules = std.AutoHashMap(u32, void).init(allocator),
            .auto_eager_rules = std.AutoHashMap(u32, u8).init(allocator),
            .acui_by_head = std.AutoHashMap(u32, StructuralCombiner).init(
                allocator,
            ),
            .trigger_by_rule = std.AutoHashMap(
                u32,
                std.ArrayListUnmanaged(TriggerPattern),
            ).init(allocator),
        };
    }

    pub fn processAnnotations(
        self: *RewriteRegistry,
        env: *const GlobalEnv,
        stmt_name: []const u8,
        annotations: []const []const u8,
    ) !void {
        for (annotations) |ann| {
            try self.processOneAnnotation(env, stmt_name, ann);
        }
    }

    fn processOneAnnotation(
        self: *RewriteRegistry,
        env: *const GlobalEnv,
        stmt_name: []const u8,
        annotation: []const u8,
    ) !void {
        var iter = std.mem.tokenizeAny(u8, annotation, " \t");
        const directive = iter.next() orelse return;

        if (std.mem.eql(u8, directive, "@relation")) {
            try self.processRelation(&iter);
        } else if (std.mem.eql(u8, directive, "@rewrite")) {
            try self.processRewrite(env, stmt_name, &iter);
        } else if (std.mem.eql(u8, directive, "@alpha")) {
            try self.processAlpha(env, stmt_name, &iter);
        } else if (std.mem.eql(u8, directive, "@conversion")) {
            try self.processConversion(env, stmt_name, &iter);
        } else if (std.mem.eql(u8, directive, "@compute")) {
            try self.processCompute(env, stmt_name, &iter);
        } else if (std.mem.eql(u8, directive, "@congr")) {
            try self.processCongr(env, stmt_name);
        } else if (std.mem.eql(u8, directive, "@fallback")) {
            try self.processFallback(env, stmt_name, &iter);
        } else if (std.mem.eql(u8, directive, "@auto")) {
            try self.processAuto(env, stmt_name, &iter);
        } else if (std.mem.eql(u8, directive, "@acui")) {
            try self.processAcui(env, stmt_name, &iter);
        }
    }

    fn processRelation(
        self: *RewriteRegistry,
        iter: *std.mem.TokenIterator(u8, .any),
    ) !void {
        const sort_name = iter.next() orelse return;
        const rel_term = iter.next() orelse return;
        const refl = iter.next() orelse return;
        const trans = iter.next() orelse return;
        const symm = iter.next() orelse return;
        const transport = iter.next() orelse return;

        try self.relations.put(sort_name, .{
            .sort_name = sort_name,
            .rel_term_name = rel_term,
            .refl_name = refl,
            .trans_name = trans,
            .symm_name = symm,
            .transport_name = transport,
        });
    }

    fn processRewrite(
        self: *RewriteRegistry,
        env: *const GlobalEnv,
        stmt_name: []const u8,
        iter: *std.mem.TokenIterator(u8, .any),
    ) !void {
        _ = iter;
        const rule_id = env.getRuleId(stmt_name) orelse return;
        const rule = &env.rules.items[rule_id];

        // The conclusion should be of the form `rel(lhs, rhs)` where rel
        // is a registered relation term.
        switch (rule.concl) {
            .app => |app| {
                if (app.args.len != 2) return;
                const lhs = app.args[0];
                const rhs = app.args[1];
                const head_id = getHeadTermId(lhs) orelse return;

                const gop = try self.rewrites_by_head.getOrPut(head_id);
                if (!gop.found_existing) {
                    gop.value_ptr.* = .{};
                }
                try gop.value_ptr.append(self.allocator, .{
                    .rule_id = rule_id,
                    .lhs = lhs,
                    .rhs = rhs,
                    .num_binders = rule.args.len,
                    .head_term_id = head_id,
                });
            },
            else => {},
        }
    }

    fn processConversion(
        self: *RewriteRegistry,
        env: *const GlobalEnv,
        stmt_name: []const u8,
        iter: *std.mem.TokenIterator(u8, .any),
    ) !void {
        const token = iter.next() orelse {
            return error.InvalidConversionAnnotation;
        };
        if (iter.next() != null) return error.InvalidConversionAnnotation;

        // On a term statement the annotation enrolls the definition itself
        // (orientation tokens `unfold`/`fold`/`both`); everything below is
        // the theorem path.
        const maybe_rule_id = env.getRuleId(stmt_name);
        if (maybe_rule_id == null) {
            if (env.term_names.get(stmt_name)) |term_id| {
                return self.processDefConversion(env, term_id, token);
            }
            return;
        }
        const rule_id = maybe_rule_id.?;

        const role: ConversionRole = if (std.mem.eql(u8, token, "assoc"))
            .assoc
        else if (std.mem.eql(u8, token, "comm"))
            .comm
        else
            .none;
        const both = std.mem.eql(u8, token, "both");
        // Role rules enroll with both orientations (same as `both`). This
        // is permanent, not transitional: a head holding both certificates
        // plus @congr is absorbed into bag interning at search time and
        // skipped from enrollment there, but a single-certificate head
        // relies on these flags to saturate as an ordinary rule.
        const ltr = both or role != .none or std.mem.eql(u8, token, "ltr");
        const rtl = both or role != .none or std.mem.eql(u8, token, "rtl");
        if (!ltr and !rtl) return error.InvalidConversionAnnotation;

        const rule = &env.rules.items[rule_id];

        for (self.conversions.items) |existing| {
            if (existing.rule_id == rule_id) {
                return error.DuplicateConversionAnnotation;
            }
        }
        // One egraph enrollment per theorem: a rule is saturated OR folded.
        for (self.computes.items) |existing| {
            if (existing.rule_id == rule_id) {
                return error.DuplicateConversionAnnotation;
            }
        }

        // Conditional conversion rules would need side-condition discharge
        // during egraph saturation; not supported.
        if (rule.hyps.len != 0) return error.ConversionRuleHasHypotheses;

        const app = switch (rule.concl) {
            .app => |value| value,
            else => return error.ConversionConclusionNotRelation,
        };
        if (app.args.len != 2) return error.ConversionConclusionNotRelation;
        try self.validateConversionRelation(env, app.term_id);

        const lhs = app.args[0];
        const rhs = app.args[1];

        // Role certificates are validated against the exact law shape
        // (before the generic orientation checks, whose validity the shape
        // implies — the role-specific diagnostic is the useful one).
        var head_term_id: ?u32 = null;
        if (role != .none) {
            // A representation-level law cannot carry dependency side
            // conditions, so the certificate must be binder-clean.
            for (rule.args) |arg| {
                if (arg.bound) return error.ConversionRoleBoundBinder;
            }
            const head = switch (role) {
                .comm => try validateCommShape(rule, lhs, rhs),
                .assoc => try validateAssocShape(rule, lhs, rhs),
                .none => unreachable,
            };
            // A registered @relation head must stay a plain application:
            // local equations cite `rel(lhs, rhs)` nodes directly, and an
            // absorbed relation would intern them as bags.
            var rel_it = self.relations.valueIterator();
            while (rel_it.next()) |relation| {
                const rel_id = env.term_names.get(
                    relation.rel_term_name,
                ) orelse continue;
                if (rel_id == head) {
                    return error.ConversionRoleRelationHead;
                }
            }
            // One certificate per law per operator.
            for (self.conversions.items) |existing| {
                if (existing.role == role and existing.head_term_id == head) {
                    return error.DuplicateConversionRoleForHead;
                }
            }
            head_term_id = head;
        }

        if (ltr) try validateConversionOrientation(lhs, rhs);
        if (rtl) try validateConversionOrientation(rhs, lhs);

        try self.conversions.append(self.allocator, .{
            .rule_id = rule_id,
            .lhs = lhs,
            .rhs = rhs,
            .num_binders = rule.args.len,
            .ltr = ltr,
            .rtl = rtl,
            .role = role,
            .head_term_id = head_term_id,
        });
    }

    /// Enroll a hypothesis-free `rel(lhs, rhs)` theorem as a `@compute`
    /// rule: a single-direction rewrite the `conversion?` egraph applies
    /// through its directed fold scheduler instead of general
    /// saturation. Bound binders are fine: the orientation check below
    /// guarantees the match side binds every binder the target uses (a
    /// fold never mints a fresh one), and dependency side conditions
    /// ride the same dep gate as general saturation rules.
    fn processCompute(
        self: *RewriteRegistry,
        env: *const GlobalEnv,
        stmt_name: []const u8,
        iter: *std.mem.TokenIterator(u8, .any),
    ) !void {
        const token = iter.next() orelse {
            return error.InvalidComputeAnnotation;
        };
        if (iter.next() != null) return error.InvalidComputeAnnotation;

        const ltr = std.mem.eql(u8, token, "ltr");
        const rtl = std.mem.eql(u8, token, "rtl");
        if (!ltr and !rtl) return error.InvalidComputeAnnotation;

        // Theorem statements only (term-side annotations are whitelisted
        // upstream, so a def can't reach here; an unknown name is skipped
        // like the other rule annotations).
        const rule_id = env.getRuleId(stmt_name) orelse return;
        const rule = &env.rules.items[rule_id];

        for (self.computes.items) |existing| {
            if (existing.rule_id == rule_id) {
                return error.DuplicateComputeAnnotation;
            }
        }
        for (self.conversions.items) |existing| {
            if (existing.rule_id == rule_id) {
                return error.DuplicateComputeAnnotation;
            }
        }

        if (rule.hyps.len != 0) return error.ComputeRuleHasHypotheses;

        const app = switch (rule.concl) {
            .app => |value| value,
            else => return error.ComputeConclusionNotRelation,
        };
        if (app.args.len != 2) return error.ComputeConclusionNotRelation;
        self.validateConversionRelation(env, app.term_id) catch |err| {
            return switch (err) {
                error.ConversionMissingRelation => error.ComputeMissingRelation,
                else => err,
            };
        };

        const lhs = app.args[0];
        const rhs = app.args[1];
        const orient_err = if (ltr)
            validateConversionOrientation(lhs, rhs)
        else
            validateConversionOrientation(rhs, lhs);
        orient_err catch |err| {
            return switch (err) {
                error.ConversionBareMatchSide => error.ComputeBareMatchSide,
                error.ConversionBinderNotCovered => error.ComputeBinderNotCovered,
            };
        };

        try self.computes.append(self.allocator, .{
            .rule_id = rule_id,
            .lhs = lhs,
            .rhs = rhs,
            .num_binders = rule.args.len,
            .ltr = ltr,
            .rtl = rtl,
            .role = .none,
        });
    }

    /// Enroll a definition for `conversion?` saturation. The orientation
    /// token picks the e-matched direction(s): `fold` matches the definiens
    /// and folds it to `head args`, `unfold` the reverse, `both` enrolls
    /// both directions. A def with hidden dummy binders may only enroll
    /// `fold` — its unfold direction would have to invent a fresh dummy
    /// witness at every match, while the fold direction merely binds an
    /// existing variable and checks freshness (see
    /// `docs/design_notes/conversion_def_folding.md`).
    fn processDefConversion(
        self: *RewriteRegistry,
        env: *const GlobalEnv,
        term_id: u32,
        token: []const u8,
    ) !void {
        const both = std.mem.eql(u8, token, "both");
        const fold = both or std.mem.eql(u8, token, "fold");
        const unfold = both or std.mem.eql(u8, token, "unfold");
        if (!fold and !unfold) return error.InvalidDefConversionAnnotation;

        const term = &env.terms.items[term_id];
        if (!term.available or !term.is_def) return error.ConversionTermNotDef;
        const body = term.body orelse return error.ConversionTermNotDef;

        if (term.dummy_args.len != 0 and unfold) {
            return error.ConversionDefUnfoldHiddenDummies;
        }

        for (self.def_conversions.items) |existing| {
            if (existing.term_id == term_id) {
                return error.DuplicateConversionAnnotation;
            }
        }

        // Lowering states each def step as a `refl` line the checker
        // closes through transparent unfolding, so the def's sort needs
        // the full relation vocabulary.
        const relation = self.getRelationForSort(
            term.ret_sort_name,
        ) orelse return error.ConversionMissingRelation;
        try validateBundleRuleShapes(env, relation);

        // Synthesized `head args` side over the arg binders (hidden
        // dummies never appear on the head side).
        const head_args = try self.allocator.alloc(
            TemplateExpr,
            term.args.len,
        );
        for (head_args, 0..) |*slot, idx| slot.* = .{ .binder = idx };
        const head = TemplateExpr{
            .app = .{ .term_id = term_id, .args = head_args },
        };

        // Same coverage rules as theorem orientations: the match side must
        // be an application binding every binder the target instantiates
        // (fold additionally requires the definiens to mention every arg —
        // an egraph rule cannot invent the dropped ones).
        if (fold) try validateConversionOrientation(body, head);
        if (unfold) try validateConversionOrientation(head, body);

        try self.def_conversions.append(self.allocator, .{
            .term_id = term_id,
            .lhs = body,
            .rhs = head,
            .num_binders = term.args.len + term.dummy_args.len,
            .fold = fold,
            .unfold = unfold,
        });
    }

    /// The conclusion head must be the registered `@relation` term for its
    /// operand sort — otherwise proof extraction has no
    /// refl/trans/symm/transport vocabulary to lower a conversion chain with.
    fn validateConversionRelation(
        self: *const RewriteRegistry,
        env: *const GlobalEnv,
        rel_term_id: u32,
    ) !void {
        if (rel_term_id >= env.terms.items.len) {
            return error.ConversionMissingRelation;
        }
        const rel_term = &env.terms.items[rel_term_id];
        if (!rel_term.available or rel_term.args.len != 2) {
            return error.ConversionMissingRelation;
        }
        const relation = self.getRelationForSort(
            rel_term.args[0].sort_name,
        ) orelse return error.ConversionMissingRelation;
        const expected = env.term_names.get(relation.rel_term_name) orelse {
            return error.ConversionMissingRelation;
        };
        if (rel_term_id != expected) return error.ConversionMissingRelation;
        try validateBundleRuleShapes(env, relation);
    }

    fn processAlpha(
        self: *RewriteRegistry,
        env: *const GlobalEnv,
        stmt_name: []const u8,
        iter: *std.mem.TokenIterator(u8, .any),
    ) !void {
        const rule_id = env.getRuleId(stmt_name) orelse return;
        const rule = &env.rules.items[rule_id];

        const old_name = iter.next() orelse return error.InvalidAlphaAnnotation;
        const new_name = iter.next() orelse return error.InvalidAlphaAnnotation;
        if (iter.next() != null) return error.InvalidAlphaAnnotation;

        if (rule.hyps.len != 0) {
            return error.AlphaRuleHasHypotheses;
        }

        const old_idx = findRuleArgIndex(rule, old_name) orelse {
            return error.UnknownAlphaBinder;
        };
        const new_idx = findRuleArgIndex(rule, new_name) orelse {
            return error.UnknownAlphaBinder;
        };
        if (!rule.args[old_idx].bound or !rule.args[new_idx].bound) {
            return error.AlphaRequiresBoundBinders;
        }
        if (!std.mem.eql(
            u8,
            rule.args[old_idx].sort_name,
            rule.args[new_idx].sort_name,
        )) {
            return error.AlphaSortMismatch;
        }

        switch (rule.concl) {
            .app => |app| {
                if (app.args.len != 2) {
                    return error.AlphaConclusionMustBeBinaryRelation;
                }
                const lhs = app.args[0];
                const rhs = app.args[1];
                const head_id = getHeadTermId(lhs) orelse {
                    return error.AlphaConclusionUnsupported;
                };

                const gop = try self.alpha_by_head.getOrPut(head_id);
                if (!gop.found_existing) {
                    gop.value_ptr.* = .{};
                }
                try gop.value_ptr.append(self.allocator, .{
                    .rule_id = rule_id,
                    .lhs = lhs,
                    .rhs = rhs,
                    .num_binders = rule.args.len,
                    .head_term_id = head_id,
                    .old_idx = old_idx,
                    .new_idx = new_idx,
                });
            },
            else => return error.AlphaConclusionMustBeBinaryRelation,
        }
    }

    fn processCongr(
        self: *RewriteRegistry,
        env: *const GlobalEnv,
        stmt_name: []const u8,
    ) !void {
        const rule_id = env.getRuleId(stmt_name) orelse return;
        const rule = &env.rules.items[rule_id];
        const app = switch (rule.concl) {
            .app => |value| value,
            else => return error.InvalidCongruenceAnnotation,
        };
        if (app.args.len != 2) return error.InvalidCongruenceAnnotation;

        const head_id = try self.validateCongrRule(
            env,
            rule,
            app.args[0],
            app.args[1],
        );
        try self.validateCongrRelation(env, head_id, app.term_id);
        try self.congr_by_head.put(head_id, .{
            .rule_id = rule_id,
            .head_term_id = head_id,
            .num_binders = rule.args.len,
        });
    }

    fn validateCongrRule(
        self: *RewriteRegistry,
        env: *const GlobalEnv,
        rule: *const RuleDecl,
        lhs: TemplateExpr,
        rhs: TemplateExpr,
    ) !u32 {
        const lhs_app = switch (lhs) {
            .app => |value| value,
            else => return error.InvalidCongruenceAnnotation,
        };
        const rhs_app = switch (rhs) {
            .app => |value| value,
            else => return error.InvalidCongruenceAnnotation,
        };
        if (lhs_app.term_id != rhs_app.term_id) {
            return error.InvalidCongruenceAnnotation;
        }
        if (lhs_app.term_id >= env.terms.items.len) {
            return error.InvalidCongruenceAnnotation;
        }

        const term = &env.terms.items[lhs_app.term_id];
        if (!term.available) return error.InvalidCongruenceAnnotation;
        if (lhs_app.args.len != term.args.len or
            rhs_app.args.len != term.args.len)
        {
            return error.InvalidCongruenceAnnotation;
        }

        var binder_idx: usize = 0;
        var hyp_idx: usize = 0;
        for (term.args, lhs_app.args, rhs_app.args) |
            term_arg,
            lhs_arg,
            rhs_arg,
        | {
            try expectRuleArgCompatible(
                rule,
                binder_idx,
                term_arg,
                term_arg.bound,
            );

            if (term_arg.bound) {
                if (!isBinder(lhs_arg, binder_idx) or
                    !isBinder(rhs_arg, binder_idx))
                {
                    return error.CongruenceBinderOrderMismatch;
                }
                binder_idx += 1;
                continue;
            }

            const old_idx = binder_idx;
            const new_idx = binder_idx + 1;
            if (!isBinder(lhs_arg, old_idx) or !isBinder(rhs_arg, new_idx)) {
                return error.CongruenceBinderOrderMismatch;
            }
            try expectRuleArgCompatible(rule, new_idx, term_arg, false);
            // Congruence lifts instantiate old/new with arbitrary child
            // terms, which may contain any bound atom the head term
            // permits at this position. The rule binders must admit those
            // dependencies, or every lift over such a child violates
            // disjointness. Bit k indexes the k'th bound arg in both
            // masks: the rule's bound binders are exactly the term's
            // bound args, in order (enforced by this loop).
            if (term_arg.deps & ~rule.args[old_idx].deps != 0 or
                term_arg.deps & ~rule.args[new_idx].deps != 0)
            {
                return error.CongruenceBinderMissingDeps;
            }
            try self.validateCongrHyp(
                env,
                rule,
                hyp_idx,
                term_arg.sort_name,
                old_idx,
                new_idx,
            );
            binder_idx += 2;
            hyp_idx += 1;
        }
        if (binder_idx != rule.args.len or hyp_idx != rule.hyps.len) {
            return error.InvalidCongruenceAnnotation;
        }

        return lhs_app.term_id;
    }

    fn validateCongrRelation(
        self: *RewriteRegistry,
        env: *const GlobalEnv,
        head_id: u32,
        rel_term_id: u32,
    ) !void {
        if (head_id >= env.terms.items.len) {
            return error.InvalidCongruenceAnnotation;
        }
        const term = &env.terms.items[head_id];
        const relation = self.getRelationForSort(term.ret_sort_name) orelse {
            return error.InvalidCongruenceAnnotation;
        };
        const expected_rel_term_id = env.term_names.get(
            relation.rel_term_name,
        ) orelse {
            return error.InvalidCongruenceAnnotation;
        };
        if (rel_term_id != expected_rel_term_id) {
            return error.InvalidCongruenceAnnotation;
        }
        try validateBundleRuleShapes(env, relation);
    }

    fn validateCongrHyp(
        self: *RewriteRegistry,
        env: *const GlobalEnv,
        rule: *const RuleDecl,
        hyp_idx: usize,
        sort_name: []const u8,
        old_idx: usize,
        new_idx: usize,
    ) !void {
        if (hyp_idx >= rule.hyps.len) {
            return error.InvalidCongruenceAnnotation;
        }
        const hyp_app = switch (rule.hyps[hyp_idx]) {
            .app => |value| value,
            else => return error.InvalidCongruenceAnnotation,
        };
        if (hyp_app.args.len != 2) return error.InvalidCongruenceAnnotation;
        if (!isBinder(hyp_app.args[0], old_idx) or
            !isBinder(hyp_app.args[1], new_idx))
        {
            return error.CongruenceBinderOrderMismatch;
        }

        const relation = self.getRelationForSort(sort_name) orelse {
            return error.InvalidCongruenceAnnotation;
        };
        const rel_term_id = env.term_names.get(relation.rel_term_name) orelse {
            return error.InvalidCongruenceAnnotation;
        };
        if (hyp_app.term_id != rel_term_id) {
            return error.InvalidCongruenceAnnotation;
        }
    }

    fn processFallback(
        self: *RewriteRegistry,
        env: *const GlobalEnv,
        stmt_name: []const u8,
        iter: *std.mem.TokenIterator(u8, .any),
    ) !void {
        const rule_id = env.getRuleId(stmt_name) orelse return;
        if (self.fallbacks.contains(rule_id)) {
            return error.DuplicateFallbackAnnotation;
        }
        const target_name = iter.next() orelse {
            return error.InvalidFallbackAnnotation;
        };
        if (iter.next() != null) {
            return error.InvalidFallbackAnnotation;
        }
        const target_id = env.getRuleId(target_name) orelse {
            return error.UnknownFallbackRule;
        };
        try self.fallbacks.put(rule_id, target_id);
    }

    fn processAuto(
        self: *RewriteRegistry,
        env: *const GlobalEnv,
        stmt_name: []const u8,
        iter: *std.mem.TokenIterator(u8, .any),
    ) !void {
        const mode = iter.next() orelse return error.InvalidAutoAnnotation;
        if (std.mem.eql(u8, mode, "trigger")) {
            return self.processTrigger(env, stmt_name, iter.rest());
        }
        if (std.mem.eql(u8, mode, "eager")) {
            return self.processEager(env, stmt_name, iter);
        }
        if (iter.next() != null) return error.InvalidAutoAnnotation;
        if (std.mem.eql(u8, mode, "forward")) {
            const rule_id = env.getRuleId(stmt_name) orelse return;
            try self.auto_forward_rules.put(rule_id, {});
        } else if (std.mem.eql(u8, mode, "backward")) {
            const rule_id = env.getRuleId(stmt_name) orelse return;
            try self.auto_backward_rules.put(rule_id, {});
        } else {
            return error.InvalidAutoAnnotation;
        }
    }

    /// Parse one `@auto eager [N]` annotation: the rule joins the eager band —
    /// tried before other enrolled backward rules, committed to once an
    /// application reaches its subgoals (the set-commit cut), and exempt from
    /// the `max_depth` budget (a "don't-care" decomposition step; see
    /// `docs/design_notes/eager_rule_scheduling.md`). `N` is the intra-band
    /// priority (1 = earliest, the default). Eager implies `@auto backward`
    /// enrollment.
    ///
    /// Validation: the rule must be invertible-shaped — every hypothesis
    /// binder determined by the conclusion (witness class 1 in
    /// `search/backward/backtrack.zig`). A premise-only witness binder (`rex`-style
    /// contraction) would make a depth-free eager step a self-feeding
    /// cascade, so it is an annotation error.
    fn processEager(
        self: *RewriteRegistry,
        env: *const GlobalEnv,
        stmt_name: []const u8,
        iter: *std.mem.TokenIterator(u8, .any),
    ) !void {
        var priority: u8 = 1;
        if (iter.next()) |token| {
            priority = std.fmt.parseInt(u8, token, 10) catch
                return error.InvalidAutoAnnotation;
            if (priority == 0) return error.InvalidAutoAnnotation;
            if (iter.next() != null) return error.InvalidAutoAnnotation;
        }
        const rule_id = env.getRuleId(stmt_name) orelse return;
        const rule = &env.rules.items[rule_id];
        if (ruleDefersWitness(rule)) return error.EagerRuleDefersWitness;
        try self.auto_backward_rules.put(rule_id, {});
        try self.auto_eager_rules.put(rule_id, priority);
    }

    /// Parse and validate one `@auto trigger PATTERN` annotation. The pattern
    /// is a parenthesized prefix term tree over term *names*, the rule's own
    /// binder names (captures), and `_` (wildcard) — e.g. `(im p _)`. Ground
    /// seeds only: a rule binder the pattern does not name must be a
    /// non-bound binder of an ACUI-combiner sort (it defaults to the unit at
    /// harvest time); anything else is an annotation error. Only
    /// hypothesis-free rules qualify (a seed has no premise recipe).
    fn processTrigger(
        self: *RewriteRegistry,
        env: *const GlobalEnv,
        stmt_name: []const u8,
        pattern_text: []const u8,
    ) !void {
        const rule_id = env.getRuleId(stmt_name) orelse return;
        const rule = &env.rules.items[rule_id];
        if (rule.hyps.len != 0) return error.TriggerRuleHasHypotheses;

        var tokens = TriggerTokenizer{ .text = pattern_text };
        const pattern = try self.parseTriggerNode(env, rule, &tokens);
        if (tokens.next() != null) return error.InvalidTriggerAnnotation;
        // A bare capture or wildcard root would match every subterm of its
        // sort — the Z3 lesson is explicit patterns, so the root must name a
        // term head.
        if (pattern != .app) return error.InvalidTriggerAnnotation;

        const named = try self.allocator.alloc(bool, rule.args.len);
        defer self.allocator.free(named);
        @memset(named, false);
        try validateTriggerApp(env, rule, pattern.app, named);
        for (rule.args, named) |arg, is_named| {
            if (is_named) continue;
            if (arg.bound or
                !self.combinerSortRegistered(env, arg.sort_name))
            {
                return error.TriggerBinderNotGround;
            }
        }

        const gop = try self.trigger_by_rule.getOrPut(rule_id);
        if (!gop.found_existing) {
            gop.value_ptr.* = .{};
        }
        try gop.value_ptr.append(self.allocator, pattern);
    }

    /// One trigger-pattern node. Arity comes from the term declaration, so
    /// exactly `term.args.len` child nodes are parsed before the closing
    /// paren — a wrong-arity pattern fails as a syntax error.
    fn parseTriggerNode(
        self: *RewriteRegistry,
        env: *const GlobalEnv,
        rule: *const RuleDecl,
        tokens: *TriggerTokenizer,
    ) anyerror!TriggerPattern {
        const token = tokens.next() orelse
            return error.InvalidTriggerAnnotation;
        if (std.mem.eql(u8, token, "(")) {
            const name = tokens.next() orelse
                return error.InvalidTriggerAnnotation;
            const term_id = env.term_names.get(name) orelse
                return error.UnknownTriggerTerm;
            const term = &env.terms.items[term_id];
            if (!term.available) return error.UnknownTriggerTerm;
            const args = try self.allocator.alloc(
                TriggerPattern,
                term.args.len,
            );
            for (args) |*slot| {
                slot.* = try self.parseTriggerNode(env, rule, tokens);
            }
            const close = tokens.next() orelse
                return error.InvalidTriggerAnnotation;
            if (!std.mem.eql(u8, close, ")")) {
                return error.InvalidTriggerAnnotation;
            }
            return .{ .app = .{ .term_id = term_id, .args = args } };
        }
        if (std.mem.eql(u8, token, ")")) {
            return error.InvalidTriggerAnnotation;
        }
        if (std.mem.eql(u8, token, "_")) return .wildcard;
        const idx = findRuleArgIndex(rule, token) orelse
            return error.UnknownTriggerBinder;
        return .{ .binder = idx };
    }

    /// True when some registered ACUI combiner returns `sort_name` — i.e. a
    /// harvest-time unit default exists for an unnamed binder of that sort.
    fn combinerSortRegistered(
        self: *const RewriteRegistry,
        env: *const GlobalEnv,
        sort_name: []const u8,
    ) bool {
        var it = self.acui_by_head.keyIterator();
        while (it.next()) |head| {
            if (head.* >= env.terms.items.len) continue;
            const term = &env.terms.items[head.*];
            if (std.mem.eql(u8, term.ret_sort_name, sort_name)) return true;
        }
        return false;
    }

    fn processAcui(
        self: *RewriteRegistry,
        env: *const GlobalEnv,
        stmt_name: []const u8,
        iter: *std.mem.TokenIterator(u8, .any),
    ) !void {
        const head_term_id = env.term_names.get(stmt_name) orelse return;

        const assoc_name = iter.next() orelse return;
        const comm_tok = iter.next() orelse return;
        const unit_term_name = iter.next() orelse return;
        const idem_tok = iter.next();

        const comm_name = if (!std.mem.eql(u8, comm_tok, "_"))
            comm_tok
        else
            null;
        const idem_name = if (idem_tok) |tok|
            if (!std.mem.eql(u8, tok, "_")) tok else null
        else
            null;

        try self.acui_by_head.put(head_term_id, .{
            .unit_term_name = unit_term_name,
            .assoc_name = assoc_name,
            .comm_name = comm_name,
            .idem_name = idem_name,
        });
    }

    pub fn getRelationForSort(
        self: *const RewriteRegistry,
        sort_name: []const u8,
    ) ?*const RelationBundle {
        return if (self.relations.getPtr(sort_name)) |ptr| ptr else null;
    }

    pub fn getFallbackRule(
        self: *const RewriteRegistry,
        rule_id: u32,
    ) ?u32 {
        return self.fallbacks.get(rule_id);
    }

    pub fn isAutoForwardRule(
        self: *const RewriteRegistry,
        rule_id: u32,
    ) bool {
        return self.auto_forward_rules.contains(rule_id);
    }

    pub fn triggerRuleCount(self: *const RewriteRegistry) usize {
        return self.trigger_by_rule.count();
    }

    pub fn autoForwardRuleCount(self: *const RewriteRegistry) usize {
        return self.auto_forward_rules.count();
    }

    pub fn isAutoBackwardRule(
        self: *const RewriteRegistry,
        rule_id: u32,
    ) bool {
        return self.auto_backward_rules.contains(rule_id);
    }

    pub fn autoBackwardRuleCount(self: *const RewriteRegistry) usize {
        return self.auto_backward_rules.count();
    }

    /// True when some enrolled backward rule can consume the `@vars` witness
    /// pool: it defers a hypothesis binder as an existential witness
    /// (`rex`-style, premise-only binder) OR carries a bound binder
    /// (`ax_gen`-style `{x}` — a backward generalization premise needs a
    /// concrete variable name, enumerated from the pre-materialized pool).
    /// `@auto eager` implies backward enrollment but rejects witness-deferring
    /// rules, so an eager-only theory whose rules bind no `{x}` has enrolled
    /// rules yet no pool consumer — this predicate (not
    /// `autoBackwardRuleCount`) is the right gate for witness-pool setup.
    pub fn hasWitnessBackwardRules(
        self: *const RewriteRegistry,
        env: *const GlobalEnv,
    ) bool {
        var iter = self.auto_backward_rules.keyIterator();
        while (iter.next()) |rule_id| {
            if (rule_id.* >= env.rules.items.len) continue;
            const rule = &env.rules.items[rule_id.*];
            if (ruleDefersWitness(rule)) return true;
            for (rule.args) |arg| {
                if (arg.bound) return true;
            }
        }
        return false;
    }

    /// Intra-eager-band priority for an `@auto eager` rule (1 = tried
    /// earliest), or null when the rule is not eager. Null-ness is the
    /// "is this rule eager?" predicate.
    pub fn eagerPriority(self: *const RewriteRegistry, rule_id: u32) ?u8 {
        return self.auto_eager_rules.get(rule_id);
    }

    pub fn autoEagerRuleCount(self: *const RewriteRegistry) usize {
        return self.auto_eager_rules.count();
    }

    /// True if `rule_id` is the *transport* rule of some `@relation` bundle
    /// (e.g. `mpbi`: `a ↔ b, a ⊢ b`). A transport rule has a bare-binder
    /// conclusion, so backward it matches every goal — yet it is a
    /// rewrite/congruence tool reached through the relation machinery, never a
    /// hand-applied backward proof step. Backward search therefore screens it
    /// from candidacy on *all* paths (`backward/backtrack.zig`, `apply.zig`); this is a
    /// deliberately different policy from the `@abstract` screen, which is
    /// generation-only, because a transport is useless backward in every mode.
    ///
    /// Keyed on the resolved transport *rule id*, not the source name, so a name
    /// collision can never screen the wrong rule; the id resolves lazily and
    /// caches into the bundle, mirroring `resolveRelation` (an as-yet-undefined
    /// transport name simply isn't screened until it resolves). The cheap
    /// `concl != .binder` early-out keeps the (tiny) relation scan off rules that
    /// cannot be a transport. A plain modus-ponens axiom (`ax_mp`/`mp`) shares
    /// the bare-conclusion shape but is NOT a relation member, so it is never
    /// screened (it stays load-bearing in Hilbert-style proofs).
    pub fn isRelationTransport(
        self: *RewriteRegistry,
        env: *const GlobalEnv,
        rule_id: u32,
    ) bool {
        if (env.rules.items[rule_id].concl != .binder) return false;
        var it = self.relations.valueIterator();
        while (it.next()) |bundle| {
            if (std.mem.eql(u8, bundle.transport_name, "_")) continue;
            if (bundle.transport_id == null) {
                bundle.transport_id = env.getRuleId(bundle.transport_name);
            }
            if (bundle.transport_id) |tid| {
                if (tid == rule_id) return true;
            }
        }
        return false;
    }

    pub fn resolveRelation(
        self: *RewriteRegistry,
        env: *const GlobalEnv,
        sort_name: []const u8,
    ) ?ResolvedRelation {
        const bundle = self.relations.getPtr(sort_name) orelse return null;

        if (bundle.rel_term_id == null) {
            bundle.rel_term_id = env.term_names.get(bundle.rel_term_name);
        }
        if (bundle.refl_id == null) {
            bundle.refl_id = env.getRuleId(bundle.refl_name);
        }
        if (bundle.trans_id == null) {
            bundle.trans_id = env.getRuleId(bundle.trans_name);
        }
        if (bundle.symm_id == null) {
            bundle.symm_id = env.getRuleId(bundle.symm_name);
        }
        const has_transport = !std.mem.eql(u8, bundle.transport_name, "_");
        if (has_transport and bundle.transport_id == null) {
            bundle.transport_id = env.getRuleId(bundle.transport_name);
        }

        const resolved = ResolvedRelation{
            .sort_name = bundle.sort_name,
            .rel_term_id = bundle.rel_term_id orelse return null,
            .refl_id = bundle.refl_id orelse return null,
            .trans_id = bundle.trans_id orelse return null,
            .symm_id = bundle.symm_id orelse return null,
            .transport_id = if (has_transport)
                (bundle.transport_id orelse return null)
            else
                null,
        };
        if (bundle.shape_ok == null) {
            bundle.shape_ok = !ruleHasBoundBinder(env, resolved.refl_id) and
                !ruleHasBoundBinder(env, resolved.trans_id) and
                !ruleHasBoundBinder(env, resolved.symm_id) and
                (resolved.transport_id == null or
                    !ruleHasBoundBinder(env, resolved.transport_id.?));
        }
        if (!bundle.shape_ok.?) return null;
        return resolved;
    }

    pub fn conversionRules(
        self: *const RewriteRegistry,
    ) []const ConversionRule {
        return self.conversions.items;
    }

    pub fn computeRules(
        self: *const RewriteRegistry,
    ) []const ConversionRule {
        return self.computes.items;
    }

    pub fn defConversionRules(
        self: *const RewriteRegistry,
    ) []const DefConversionRule {
        return self.def_conversions.items;
    }

    pub fn defConversionByTerm(
        self: *const RewriteRegistry,
        term_id: u32,
    ) ?DefConversionRule {
        for (self.def_conversions.items) |def_conv| {
            if (def_conv.term_id == term_id) return def_conv;
        }
        return null;
    }

    pub fn hasRewriteRules(self: *const RewriteRegistry) bool {
        return self.rewrites_by_head.count() != 0;
    }

    pub fn getRewriteRules(
        self: *const RewriteRegistry,
        head_term_id: u32,
    ) []const RewriteRule {
        if (self.rewrites_by_head.get(head_term_id)) |list| {
            return list.items;
        }
        return &.{};
    }

    pub fn getAlphaRules(
        self: *const RewriteRegistry,
        head_term_id: u32,
    ) []const AlphaRule {
        if (self.alpha_by_head.get(head_term_id)) |list| {
            return list.items;
        }
        return &.{};
    }

    pub fn getCongruenceRule(
        self: *const RewriteRegistry,
        head_term_id: u32,
    ) ?CongruenceRule {
        return self.congr_by_head.get(head_term_id);
    }

    pub fn hasStructuralCombiner(
        self: *const RewriteRegistry,
        head_term_id: u32,
    ) bool {
        return self.acui_by_head.contains(head_term_id);
    }

    pub fn resolveStructuralCombinerForSort(
        self: *RewriteRegistry,
        env: *const GlobalEnv,
        sort_name: []const u8,
    ) anyerror!?ResolvedStructuralCombiner {
        var found_head: ?u32 = null;
        var it = self.acui_by_head.iterator();
        while (it.next()) |entry| {
            const head_term_id = entry.key_ptr.*;
            if (head_term_id >= env.terms.items.len) continue;
            const term = &env.terms.items[head_term_id];
            if (!std.mem.eql(u8, term.ret_sort_name, sort_name)) continue;
            if (found_head) |existing| {
                if (existing != head_term_id) return null;
                continue;
            }
            found_head = head_term_id;
        }
        return if (found_head) |head_term_id|
            try self.resolveStructuralCombiner(env, head_term_id)
        else
            null;
    }

    pub fn resolveStructuralCombiner(
        self: *RewriteRegistry,
        env: *const GlobalEnv,
        head_term_id: u32,
    ) anyerror!?ResolvedStructuralCombiner {
        const combiner = self.acui_by_head.getPtr(head_term_id) orelse return null;
        const term_decl = if (head_term_id < env.terms.items.len)
            &env.terms.items[head_term_id]
        else
            return null;
        const relation = self.resolveRelation(env, term_decl.ret_sort_name) orelse {
            return null;
        };

        if (combiner.unit_term_id == null) {
            combiner.unit_term_id = env.term_names.get(combiner.unit_term_name);
        }
        if (combiner.assoc_id == null) {
            combiner.assoc_id = env.getRuleId(combiner.assoc_name);
        }
        if (combiner.comm_id == null and combiner.comm_name != null) {
            combiner.comm_id = env.getRuleId(combiner.comm_name.?);
        }
        if (combiner.idem_id == null and combiner.idem_name != null) {
            combiner.idem_id = env.getRuleId(combiner.idem_name.?);
        }
        if (!combiner.left_unit_rule_searched) {
            combiner.left_unit_rule = try findLeftUnitRule(
                env,
                relation.rel_term_id,
                head_term_id,
                combiner.unit_term_id orelse return null,
            );
            combiner.left_unit_rule_searched = true;
        }
        if (!combiner.right_unit_rule_searched) {
            combiner.right_unit_rule = try findRightUnitRule(
                env,
                relation.rel_term_id,
                head_term_id,
                combiner.unit_term_id orelse return null,
            );
            combiner.right_unit_rule_searched = true;
        }

        return .{
            .head_term_id = head_term_id,
            .unit_term_id = combiner.unit_term_id orelse return null,
            .assoc_id = combiner.assoc_id orelse return null,
            .comm_id = combiner.comm_id,
            .idem_id = combiner.idem_id,
            .left_unit_rule_id = if (combiner.left_unit_rule) |rule|
                rule.rule_id
            else
                null,
            .left_unit_rule_reversed = if (combiner.left_unit_rule) |rule|
                rule.reversed
            else
                false,
            .right_unit_rule_id = if (combiner.right_unit_rule) |rule|
                rule.rule_id
            else
                null,
            .right_unit_rule_reversed = if (combiner.right_unit_rule) |rule|
                rule.reversed
            else
                false,
        };
    }
};

fn findLeftUnitRule(
    env: *const GlobalEnv,
    rel_term_id: u32,
    head_term_id: u32,
    unit_term_id: u32,
) !?UnitRule {
    return try findUnitRule(
        env,
        rel_term_id,
        head_term_id,
        unit_term_id,
        isLeftUnitPattern,
    );
}

fn findRightUnitRule(
    env: *const GlobalEnv,
    rel_term_id: u32,
    head_term_id: u32,
    unit_term_id: u32,
) !?UnitRule {
    return try findUnitRule(
        env,
        rel_term_id,
        head_term_id,
        unit_term_id,
        isRightUnitPattern,
    );
}

fn findUnitRule(
    env: *const GlobalEnv,
    rel_term_id: u32,
    head_term_id: u32,
    unit_term_id: u32,
    comptime matches: fn (TemplateExpr, TemplateExpr, u32, u32) bool,
) !?UnitRule {
    var found: ?UnitRule = null;
    for (env.rules.items, 0..) |rule, rule_idx| {
        if (rule.args.len != 1) continue;
        const app = switch (rule.concl) {
            .app => |value| value,
            else => continue,
        };
        if (app.term_id != rel_term_id or app.args.len != 2) continue;

        const direct = matches(
            app.args[0],
            app.args[1],
            head_term_id,
            unit_term_id,
        );
        const reversed = matches(
            app.args[1],
            app.args[0],
            head_term_id,
            unit_term_id,
        );
        if (!direct and !reversed) continue;
        if (direct and reversed) return error.AmbiguousStructuralUnitRule;

        const candidate: UnitRule = .{
            .rule_id = @intCast(rule_idx),
            .reversed = reversed,
        };
        if (found != null) return error.AmbiguousStructuralUnitRule;
        found = candidate;
    }
    return found;
}

fn isLeftUnitPattern(
    lhs: TemplateExpr,
    rhs: TemplateExpr,
    head_term_id: u32,
    unit_term_id: u32,
) bool {
    const lhs_app = switch (lhs) {
        .app => |value| value,
        else => return false,
    };
    if (lhs_app.term_id != head_term_id or lhs_app.args.len != 2) {
        return false;
    }
    const unit_app = switch (lhs_app.args[0]) {
        .app => |value| value,
        else => return false,
    };
    const rhs_binder = switch (rhs) {
        .binder => |value| value,
        else => return false,
    };
    const lhs_rhs_binder = switch (lhs_app.args[1]) {
        .binder => |value| value,
        else => return false,
    };
    return unit_app.term_id == unit_term_id and
        unit_app.args.len == 0 and
        lhs_rhs_binder == rhs_binder;
}

fn isRightUnitPattern(
    lhs: TemplateExpr,
    rhs: TemplateExpr,
    head_term_id: u32,
    unit_term_id: u32,
) bool {
    const lhs_app = switch (lhs) {
        .app => |value| value,
        else => return false,
    };
    if (lhs_app.term_id != head_term_id or lhs_app.args.len != 2) {
        return false;
    }
    const lhs_rhs_binder = switch (lhs_app.args[0]) {
        .binder => |value| value,
        else => return false,
    };
    const unit_app = switch (lhs_app.args[1]) {
        .app => |value| value,
        else => return false,
    };
    const rhs_binder = switch (rhs) {
        .binder => |value| value,
        else => return false,
    };
    return unit_app.term_id == unit_term_id and
        unit_app.args.len == 0 and
        lhs_rhs_binder == rhs_binder;
}

/// Whitespace/paren tokenizer for `@auto trigger` pattern text: `(` and `)`
/// are single-character tokens, everything else splits on whitespace.
const TriggerTokenizer = struct {
    text: []const u8,
    pos: usize = 0,

    fn next(self: *TriggerTokenizer) ?[]const u8 {
        while (self.pos < self.text.len and
            std.ascii.isWhitespace(self.text[self.pos]))
        {
            self.pos += 1;
        }
        if (self.pos >= self.text.len) return null;
        const start = self.pos;
        const c = self.text[start];
        if (c == '(' or c == ')') {
            self.pos += 1;
            return self.text[start..self.pos];
        }
        while (self.pos < self.text.len) : (self.pos += 1) {
            const ch = self.text[self.pos];
            if (std.ascii.isWhitespace(ch) or ch == '(' or ch == ')') break;
        }
        return self.text[start..self.pos];
    }
};

/// Semantic checks for one trigger app node, recording which rule binders
/// the pattern names. Bound term positions hold variables, which a ground
/// seed cannot capture or constrain — only `_` is admitted there. Capture
/// and nested-app sorts must line up with the term's declared argument
/// sorts, and a capture must target a non-bound rule binder (the captured
/// subterm is an arbitrary expression, not a variable).
fn validateTriggerApp(
    env: *const GlobalEnv,
    rule: *const RuleDecl,
    app: TriggerPattern.App,
    named: []bool,
) anyerror!void {
    const term = &env.terms.items[app.term_id];
    for (term.args, app.args) |term_arg, child| {
        switch (child) {
            .wildcard => {},
            .binder => |idx| {
                if (term_arg.bound) return error.TriggerBoundPosition;
                if (rule.args[idx].bound) {
                    return error.TriggerBinderNotGround;
                }
                if (!std.mem.eql(
                    u8,
                    rule.args[idx].sort_name,
                    term_arg.sort_name,
                )) {
                    return error.TriggerSortMismatch;
                }
                named[idx] = true;
            },
            .app => |child_app| {
                if (term_arg.bound) return error.TriggerBoundPosition;
                const child_term = &env.terms.items[child_app.term_id];
                if (!std.mem.eql(
                    u8,
                    child_term.ret_sort_name,
                    term_arg.sort_name,
                )) {
                    return error.TriggerSortMismatch;
                }
                try validateTriggerApp(env, rule, child_app, named);
            },
        }
    }
}

/// One enrolled `@conversion` orientation: `match` is e-matched, `target` is
/// instantiated. The match side must be a term application (a bare-binder
/// match side would match every e-class), and it must bind every binder the
/// target side uses (an egraph rule cannot invent fresh variables).
/// Overflowed binder masks (>= 64 binders) conservatively fail coverage.
fn ruleHasBoundBinder(env: *const GlobalEnv, rule_id: u32) bool {
    if (rule_id >= env.rules.items.len) return false;
    for (env.rules.items[rule_id].args) |arg| {
        if (arg.bound) return true;
    }
    return false;
}

/// Relation-bundle rules (refl/trans/symm/transport) must have no bound
/// binders: extraction cites them on arbitrary terms, and a bound binder
/// would attach a disjointness obligation nothing discharges. Members not
/// yet declared are skipped here — `resolveRelation` re-checks once the
/// whole bundle resolves.
fn validateBundleRuleShapes(
    env: *const GlobalEnv,
    bundle: *const RelationBundle,
) !void {
    const names = [_][]const u8{
        bundle.refl_name,
        bundle.trans_name,
        bundle.symm_name,
        bundle.transport_name,
    };
    for (names) |name| {
        if (std.mem.eql(u8, name, "_")) continue;
        const rule_id = env.getRuleId(name) orelse continue;
        if (ruleHasBoundBinder(env, rule_id)) {
            return error.RelationBundleBoundBinder;
        }
    }
}

/// `@conversion comm` certificate: `rel(t(a, b), t(b, a))` with exactly
/// the two distinct bare binders and nothing else. Returns the head `t`.
fn validateCommShape(
    rule: *const RuleDecl,
    lhs: TemplateExpr,
    rhs: TemplateExpr,
) !u32 {
    if (rule.args.len != 2) return error.ConversionCommRuleShape;
    const left = binaryAppArgs(lhs) orelse return error.ConversionCommRuleShape;
    const a = bareBinder(left.args[0]) orelse return error.ConversionCommRuleShape;
    const b = bareBinder(left.args[1]) orelse return error.ConversionCommRuleShape;
    if (a == b) return error.ConversionCommRuleShape;
    const right = binaryAppArgs(rhs) orelse return error.ConversionCommRuleShape;
    if (right.term_id != left.term_id) return error.ConversionCommRuleShape;
    if (!isBinder(right.args[0], b) or !isBinder(right.args[1], a)) {
        return error.ConversionCommRuleShape;
    }
    return left.term_id;
}

/// `@conversion assoc` certificate: `rel(t(t(a,b), c), t(a, t(b,c)))` in
/// either orientation, three distinct bare binders. Returns the head `t`.
fn validateAssocShape(
    rule: *const RuleDecl,
    lhs: TemplateExpr,
    rhs: TemplateExpr,
) !u32 {
    if (rule.args.len != 3) return error.ConversionAssocRuleShape;
    if (assocHead(lhs, rhs)) |head| return head;
    if (assocHead(rhs, lhs)) |head| return head;
    return error.ConversionAssocRuleShape;
}

/// Match `left = t(t(a,b), c)` against `right = t(a, t(b,c))` for distinct
/// binders a, b, c; null when the pair does not have that shape.
fn assocHead(left: TemplateExpr, right: TemplateExpr) ?u32 {
    const outer_l = binaryAppArgs(left) orelse return null;
    const inner_l = binaryAppArgs(outer_l.args[0]) orelse return null;
    if (inner_l.term_id != outer_l.term_id) return null;
    const a = bareBinder(inner_l.args[0]) orelse return null;
    const b = bareBinder(inner_l.args[1]) orelse return null;
    const c = bareBinder(outer_l.args[1]) orelse return null;
    if (a == b or a == c or b == c) return null;
    const outer_r = binaryAppArgs(right) orelse return null;
    if (outer_r.term_id != outer_l.term_id) return null;
    if (!isBinder(outer_r.args[0], a)) return null;
    const inner_r = binaryAppArgs(outer_r.args[1]) orelse return null;
    if (inner_r.term_id != outer_l.term_id) return null;
    if (!isBinder(inner_r.args[0], b)) return null;
    if (!isBinder(inner_r.args[1], c)) return null;
    return outer_l.term_id;
}

const BinaryApp = struct { term_id: u32, args: []const TemplateExpr };

fn binaryAppArgs(template: TemplateExpr) ?BinaryApp {
    const app = switch (template) {
        .app => |app| app,
        .binder => return null,
    };
    if (app.args.len != 2) return null;
    return .{ .term_id = app.term_id, .args = app.args };
}

fn bareBinder(template: TemplateExpr) ?usize {
    return switch (template) {
        .binder => |idx| idx,
        .app => null,
    };
}

fn validateConversionOrientation(
    match: TemplateExpr,
    target: TemplateExpr,
) !void {
    if (match != .app) return error.ConversionBareMatchSide;
    const match_mask = templateBinderMask(match);
    const target_mask = templateBinderMask(target);
    if (match_mask.overflow or target_mask.overflow) {
        return error.ConversionBinderNotCovered;
    }
    if ((target_mask.mask & ~match_mask.mask) != 0) {
        return error.ConversionBinderNotCovered;
    }
}

fn isBinder(template: TemplateExpr, expected_idx: usize) bool {
    return switch (template) {
        .binder => |idx| idx == expected_idx,
        else => false,
    };
}

fn expectRuleArgCompatible(
    rule: *const RuleDecl,
    binder_idx: usize,
    term_arg: anytype,
    expected_bound: bool,
) !void {
    if (binder_idx >= rule.args.len) return error.InvalidCongruenceAnnotation;
    const rule_arg = rule.args[binder_idx];
    if (rule_arg.bound != expected_bound) {
        return error.InvalidCongruenceAnnotation;
    }
    if (!std.mem.eql(u8, rule_arg.sort_name, term_arg.sort_name)) {
        return error.InvalidCongruenceAnnotation;
    }
}

fn getHeadTermId(template: TemplateExpr) ?u32 {
    return switch (template) {
        .app => |app| app.term_id,
        .binder => null,
    };
}

fn findRuleArgIndex(rule: *const RuleDecl, name: []const u8) ?usize {
    for (rule.arg_names, 0..) |arg_name, idx| {
        if (arg_name) |actual_name| {
            if (std.mem.eql(u8, actual_name, name)) return idx;
        }
    }
    return null;
}
