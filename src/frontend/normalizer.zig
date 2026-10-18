const std = @import("std");
const ArenaAllocator = @import("./arena_allocator.zig").ArenaAllocator;
const ExprId = @import("./expr.zig").ExprId;
const TheoremContext = @import("./expr.zig").TheoremContext;
const GlobalEnv = @import("./env.zig").GlobalEnv;
const RewriteRegistry = @import("./rewrite_registry.zig").RewriteRegistry;
const ResolvedRelation =
    @import("./rewrite_registry.zig").ResolvedRelation;
const ResolvedStructuralCombiner =
    @import("./rewrite_registry.zig").ResolvedStructuralCombiner;
const DiagScratch = @import("./diag_scratch.zig");
const DebugConfig = @import("./debug.zig").DebugConfig;
const DefOps = @import("./def_ops.zig");
const AcuiSupport = @import("./acui_support.zig");
const CheckedLine = @import("./checked_ir.zig").CheckedLine;
const CheckedRef = @import("./checked_ir.zig").CheckedRef;
const Types = @import("./normalizer/types.zig");
const Support = @import("./normalizer/support.zig");
const Core = @import("./normalizer/core.zig");
const CommonTarget = @import("./normalizer/common_target.zig");
const ProofEmit = @import("./normalizer/proof_emit.zig");
const AcuiNormalize = @import("./normalizer/acui/normalize.zig");
const AcuiRearrange = @import("./normalizer/acui/rearrange.zig");

pub const NormalizeResult = Types.NormalizeResult;
pub const CommonTargetResult = Types.CommonTargetResult;

/// The proof-producing normalizer: every step it takes is a checked line
/// appended to `lines`.
pub const Normalizer = Engine(.proofs);

/// The normalizer's normal forms and common targets with no proof sink:
/// where it would emit a step it reports `Support.proof_free_line`, and a
/// commutative bag it sorts in one pass rather than member by member
/// (`normalizeCommutativeBag`), so its steps differ but not where they end.
/// It decides the laws, not whether a proof of them can be stated, so it
/// also runs where the proof-producing normalizer needs a registered
/// relation or `@congr` rule and has none. Its normal forms are the
/// canonical forms inference and search compare, and its common targets
/// decide whether two bindings can meet.
pub const Canonicalizer = Engine(.proof_free);

const Mode = enum { proofs, proof_free };

fn Engine(comptime mode: Mode) type {
    return struct {
        const Self = @This();
        pub const Lines = switch (mode) {
            .proofs => *std.ArrayListUnmanaged(CheckedLine),
            .proof_free => void,
        };

        allocator: std.mem.Allocator,
        theorem: *TheoremContext,
        env: *const GlobalEnv,
        registry: *RewriteRegistry,
        lines: Lines,
        diag_scratch: ?*DiagScratch.Scratch,
        debug: DebugConfig = .none,
        hidden_witness_provider: ?DefOps.HiddenWitnessProvider = null,
        /// Each expression's normal form; null while it is being normalized.
        cache: std.AutoHashMap(ExprId, ?NormalizeResult),
        /// Rewrite steps taken since the budget was last reset. A step past
        /// `step_limit` fails with `RewriteStepLimit`.
        step_count: usize = 0,
        step_limit: usize = 1000,
        /// The `@rewrite` rule of the innermost step whose result is being
        /// normalized, which names a rewrite cycle.
        last_rule_id: ?u32 = null,
        /// ACUI support and its def_ops context, shared by every query this
        /// normalizer makes so their caches stay warm. Created on first use
        /// and heap-allocated, so copying the normalizer stays safe.
        support_ctx: ?*AcuiSupport.Context = null,

        pub fn init(
            allocator: std.mem.Allocator,
            theorem: *TheoremContext,
            registry: *RewriteRegistry,
            env: *const GlobalEnv,
            lines: Lines,
        ) Self {
            return initWithDebugAndScratch(
                allocator,
                theorem,
                registry,
                env,
                lines,
                null,
                .none,
            );
        }

        pub fn initWithScratch(
            allocator: std.mem.Allocator,
            theorem: *TheoremContext,
            registry: *RewriteRegistry,
            env: *const GlobalEnv,
            lines: Lines,
            diag_scratch: ?*DiagScratch.Scratch,
        ) Self {
            return initWithDebugAndScratch(
                allocator,
                theorem,
                registry,
                env,
                lines,
                diag_scratch,
                .none,
            );
        }

        pub fn initWithDebugAndScratch(
            allocator: std.mem.Allocator,
            theorem: *TheoremContext,
            registry: *RewriteRegistry,
            env: *const GlobalEnv,
            lines: Lines,
            diag_scratch: ?*DiagScratch.Scratch,
            debug: DebugConfig,
        ) Self {
            return .{
                .allocator = allocator,
                .theorem = theorem,
                .env = env,
                .registry = registry,
                .lines = lines,
                .diag_scratch = diag_scratch,
                .debug = debug,
                .cache = std.AutoHashMap(ExprId, ?NormalizeResult).init(
                    allocator,
                ),
            };
        }

        pub fn deinit(self: *Self) void {
            self.cache.deinit();
            if (self.support_ctx) |ctx| {
                ctx.deinit();
                self.allocator.destroy(ctx);
                self.support_ctx = null;
            }
        }

        pub fn support(self: *Self) anyerror!*AcuiSupport.Context {
            if (self.support_ctx) |ctx| return ctx;
            const ctx = try self.allocator.create(AcuiSupport.Context);
            ctx.* = AcuiSupport.Context.init(
                self.allocator,
                self.theorem,
                self.env,
                self.registry,
            );
            self.support_ctx = ctx;
            return ctx;
        }

        pub fn defOps(self: *Self) anyerror!*DefOps.Context {
            return (try self.support()).defOps();
        }

        pub fn normalize(
            self: *Self,
            expr_id: ExprId,
        ) anyerror!NormalizeResult {
            return try Core.normalize(self, expr_id);
        }

        /// The normal form of `expr_id`, without its proof.
        pub fn canonicalize(self: *Self, expr_id: ExprId) anyerror!ExprId {
            return (try Core.normalize(self, expr_id)).result_expr;
        }

        /// `canonicalize` with the step budget a fresh engine would have.
        pub fn canonicalizeWithFreshBudget(self: *Self, expr_id: ExprId) anyerror!ExprId {
            self.step_count = 0;
            self.last_rule_id = null;
            return try self.canonicalize(expr_id);
        }

        /// The canonical bag of `acui` at `expr_id`, its members as given.
        pub fn canonicalizeAcui(
            self: *Self,
            expr_id: ExprId,
            acui: ResolvedStructuralCombiner,
        ) anyerror!ExprId {
            return try AcuiNormalize.canonicalizeBag(self, expr_id, acui);
        }

        pub fn resolveRelationForExpr(
            self: *Self,
            expr_id: ExprId,
        ) ?ResolvedRelation {
            return Support.resolveRelationForExpr(self, expr_id);
        }

        /// A proof that `lhs` = `rhs` that moves ACUI members into place,
        /// or null when the two differ by more than that.
        pub fn buildRearrangement(
            self: *Self,
            lhs: ExprId,
            rhs: ExprId,
        ) anyerror!??usize {
            return try AcuiRearrange.buildRearrangement(self, lhs, rhs);
        }

        pub fn buildCommonTarget(
            self: *Self,
            lhs: ExprId,
            rhs: ExprId,
        ) anyerror!?CommonTargetResult {
            return try CommonTarget.buildCommonTarget(self, lhs, rhs);
        }

        pub fn composeTransitivity(
            self: *Self,
            relation: ResolvedRelation,
            original: ExprId,
            mid: ExprId,
            final: ExprId,
            first_proof: ?usize,
            second_proof: ?usize,
        ) anyerror!?usize {
            return try ProofEmit.composeTransitivity(
                self,
                relation,
                original,
                mid,
                final,
                first_proof,
                second_proof,
            );
        }

        pub fn emitTransport(
            self: *Self,
            relation: ResolvedRelation,
            target_expr: ExprId,
            source_expr: ExprId,
            conv_line_idx: usize,
            source_line: CheckedRef,
        ) anyerror!usize {
            return try ProofEmit.emitTransport(
                self,
                relation,
                target_expr,
                source_expr,
                conv_line_idx,
                source_line,
            );
        }

        pub fn emitSymm(
            self: *Self,
            relation: ResolvedRelation,
            a: ExprId,
            b: ExprId,
            proof_line_idx: usize,
        ) anyerror!usize {
            return try ProofEmit.emitSymm(
                self,
                relation,
                a,
                b,
                proof_line_idx,
            );
        }
    };
}

test "canonicalizer rejects rewrite bindings with forbidden deps" {
    var arena = ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();

    var env = GlobalEnv.init(allocator);
    var registry = RewriteRegistry.init(allocator);

    const TemplateExpr = @import("./rules.zig").TemplateExpr;
    const ArgInfo = @import("parse_recovery.zig").ArgInfo;
    const RewriteRule = @import("./rewrite_registry.zig").RewriteRule;
    const arr_term_id: u32 = 0;
    const sb_ty_term_id: u32 = 1;
    try env.term_names.put("arr", arr_term_id);
    try env.term_names.put("sb_ty", sb_ty_term_id);
    try env.terms.append(allocator, .{
        .name = "arr",
        .args = &.{},
        .arg_names = &.{},
        .dummy_args = &.{},
        .dummy_names = &.{},
        .ret_sort_name = "ty",
        .is_def = false,
        .body = null,
    });
    try env.terms.append(allocator, .{
        .name = "sb_ty",
        .args = &.{},
        .arg_names = &.{},
        .dummy_args = &.{},
        .dummy_names = &.{},
        .ret_sort_name = "ty",
        .is_def = false,
        .body = null,
    });

    const lhs: TemplateExpr = .{ .app = .{
        .term_id = sb_ty_term_id,
        .args = try allocator.dupe(TemplateExpr, &.{
            TemplateExpr{ .binder = 0 },
            TemplateExpr{ .binder = 1 },
            TemplateExpr{ .app = .{
                .term_id = arr_term_id,
                .args = try allocator.dupe(TemplateExpr, &.{
                    TemplateExpr{ .binder = 2 },
                    TemplateExpr{ .binder = 3 },
                }),
            } },
        }),
    } };
    const rhs: TemplateExpr = .{ .app = .{
        .term_id = arr_term_id,
        .args = try allocator.dupe(TemplateExpr, &.{
            TemplateExpr{ .binder = 2 },
            TemplateExpr{ .binder = 3 },
        }),
    } };

    const rule_args = try allocator.dupe(ArgInfo, &.{
        ArgInfo{ .sort_name = "tm", .bound = true, .deps = 0 },
        ArgInfo{ .sort_name = "tm", .bound = false, .deps = 1 },
        ArgInfo{ .sort_name = "ty", .bound = false, .deps = 0 },
        ArgInfo{ .sort_name = "ty", .bound = false, .deps = 0 },
    });
    try env.rule_names.put("sb_ty_arr", 0);
    try env.rules.append(allocator, .{
        .name = "sb_ty_arr",
        .args = rule_args,
        .arg_names = &.{},
        .hyps = &.{},
        .concl = lhs,
        .kind = .axiom,
        .is_local = false,
    });

    var rules = std.ArrayListUnmanaged(RewriteRule).empty;
    try rules.append(allocator, .{
        .rule_id = 0,
        .lhs = lhs,
        .rhs = rhs,
        .num_binders = rule_args.len,
        .head_term_id = sb_ty_term_id,
    });
    try registry.rewrites_by_head.put(sb_ty_term_id, rules);

    var theorem = TheoremContext.init(allocator);
    const theorem_args = [_]ArgInfo{
        .{ .sort_name = "tm", .bound = true, .deps = 1 },
        .{ .sort_name = "tm", .bound = false, .deps = 1 },
        .{ .sort_name = "ty", .bound = false, .deps = 1 },
        .{ .sort_name = "ty", .bound = false, .deps = 1 },
    };
    theorem.arg_infos = &theorem_args;
    try theorem.seedBinderCount(theorem_args.len);

    const x = theorem.theorem_vars.items[0];
    const u = theorem.theorem_vars.items[1];
    const a = theorem.theorem_vars.items[2];
    const b = theorem.theorem_vars.items[3];

    const arr_expr = try theorem.interner.internApp(arr_term_id, &.{ a, b });
    const expr = try theorem.interner.internApp(
        sb_ty_term_id,
        &.{ x, u, arr_expr },
    );

    var canonicalizer = Canonicalizer.init(
        allocator,
        &theorem,
        &registry,
        &env,
        {},
    );
    defer canonicalizer.deinit();

    try std.testing.expectEqual(expr, try canonicalizer.canonicalize(expr));
}
