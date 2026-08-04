//! Directed rewrite normalization over symbolic expressions.
//!
//! Last-resort conclusion matching for rule applications whose binders were
//! solved through a hidden-def unfold (task #180). After `beta` matches
//! `Y · g` by opening `Y`, its conclusion's `[x := a] e` side holds symbolic
//! values carrying unmaterialized def dummies — the strict normalizer cannot
//! touch it (not concrete), and the semantic search pays per rewrite step
//! from a small budget. Here the `@rewrite` rules are applied as directed
//! reductions instead, dummies staying in place; the final transparent match
//! of the normal form against the stated line is what forces each dummy's
//! witness (e.g. the line's bound variable).

const std = @import("std");
const ExprId = @import("../../expr.zig").ExprId;
const TemplateExpr = @import("../../rules.zig").TemplateExpr;
const Types = @import("../types.zig");
const MatchState = @import("../match_state.zig");
const TransparentMatch = @import("./transparent_match.zig");
const RewriteApplication = @import("./rewrite_application.zig");
const WitnessState = @import("./witness_state.zig");

const SymbolicExpr = Types.SymbolicExpr;
const MatchSession = MatchState.MatchSession;

/// Rule applications allowed per conclusion match. The reductions this path
/// exists for (substitution ladders under a def unfold) take a few dozen
/// steps; the cap only guards non-terminating rule sets.
const directed_normalize_fuel: usize = 64;

pub const Fuel = struct {
    remaining: usize = directed_normalize_fuel,
    /// Set when the cap was hit while rewrite rules remained to try, so a
    /// failed match may be a fuel artifact rather than a real mismatch.
    /// Surfaced as a `--debug inference` trace by the caller.
    exhausted: bool = false,
};

/// Reduce a symbolic expression bottom-up with the registry's directed
/// `@rewrite` rules, resolving already-solved rule binders through the
/// session. Unmaterialized dummies stay symbolic. Deterministic: at each head
/// the first applicable rule (registry order) is taken; rule application is
/// gated by the dummy-aware dependency validation in `rewrite_application`.
pub fn normalizeSymbolicRewrites(
    self: anytype,
    symbolic: *const SymbolicExpr,
    state: *MatchSession,
    fuel: *Fuel,
) anyerror!*const SymbolicExpr {
    var current = try RewriteApplication.resolveBoundBinderSymbolic(
        self,
        symbolic,
        state,
    );
    outer: while (true) {
        const app = switch (current.*) {
            .app => |app| app,
            .binder, .dummy, .fixed => return current,
        };

        const new_args = try self.shared.scratch().alloc(
            *const SymbolicExpr,
            app.args.len,
        );
        var changed = false;
        for (app.args, 0..) |arg, idx| {
            new_args[idx] = try normalizeSymbolicRewrites(
                self,
                arg,
                state,
                fuel,
            );
            if (new_args[idx] != arg) changed = true;
        }
        if (changed) {
            current = try self.allocSymbolic(.{ .app = .{
                .term_id = app.term_id,
                .args = new_args,
            } });
        }

        const registry = self.shared.registry orelse return current;
        const head = switch (current.*) {
            .app => |value| value.term_id,
            else => return current,
        };
        for (registry.getRewriteRules(head)) |rule| {
            if (fuel.remaining == 0) {
                fuel.exhausted = true;
                return current;
            }
            if (try RewriteApplication.applyRewriteRuleToSymbolic(
                self,
                rule,
                current,
                state,
            )) |next| {
                fuel.remaining -= 1;
                current = try RewriteApplication.resolveBoundBinderSymbolic(
                    self,
                    next,
                    state,
                );
                continue :outer;
            }
        }
        return current;
    }
}

/// Match a rule template against a stated expression, normalizing residual
/// template subtrees with directed rewrites. Left-to-right under matching
/// heads, so binders solved by earlier arguments (e.g. through a hidden-def
/// unfold) are available when a later argument needs reduction to take its
/// stated shape. Inference evidence only — validation still rechecks the
/// application and emits the transport.
///
/// Inert on templates containing an ACUI-enrolled head: the direct matching
/// used here is positional, and committing a naive member split under an
/// ACUI spine would turn the earlier tiers' deliberate no_match (which lets
/// the strategy ladder continue into structural matching and hint flow) into
/// a wrong bound guess that dies as a missing-binder failure.
pub fn matchTemplateRewriteNormalized(
    self: anytype,
    template: TemplateExpr,
    actual: ExprId,
    state: *MatchSession,
    fuel_exhausted: *bool,
) anyerror!bool {
    const registry = self.shared.registry orelse return false;
    if (!registry.hasRewriteRules()) return false;
    if (templateHasAcuiHead(registry, template)) return false;
    var fuel = Fuel{};
    defer if (fuel.exhausted) {
        fuel_exhausted.* = true;
    };
    var snapshot = try WitnessState.saveMatchSnapshot(self, state);
    defer WitnessState.deinitMatchSnapshot(self, &snapshot);
    if (try matchTemplateRewriteNormalizedRec(
        self,
        template,
        actual,
        state,
        &fuel,
    )) {
        return true;
    }
    try WitnessState.restoreMatchSnapshot(self, &snapshot, state);
    return false;
}

fn matchTemplateRewriteNormalizedRec(
    self: anytype,
    template: TemplateExpr,
    actual: ExprId,
    state: *MatchSession,
    fuel: *Fuel,
) anyerror!bool {
    if (try TransparentMatch.tryMatchTemplateStateDirect(
        self,
        template,
        actual,
        state,
    )) {
        return true;
    }
    const app = switch (template) {
        .binder => return false,
        .app => |app| app,
    };

    const actual_node = self.shared.theorem.interner.node(actual);
    if (actual_node.* == .app) {
        const actual_app = actual_node.app;
        if (actual_app.term_id == app.term_id and
            actual_app.args.len == app.args.len)
        {
            var snapshot = try WitnessState.saveMatchSnapshot(self, state);
            defer WitnessState.deinitMatchSnapshot(self, &snapshot);
            var all_matched = true;
            for (app.args, actual_app.args) |tmpl_arg, actual_arg| {
                if (!try matchTemplateRewriteNormalizedRec(
                    self,
                    tmpl_arg,
                    actual_arg,
                    state,
                    fuel,
                )) {
                    all_matched = false;
                    break;
                }
            }
            if (all_matched) return true;
            try WitnessState.restoreMatchSnapshot(self, &snapshot, state);
        }
    }

    const symbolic = try TransparentMatch.symbolicFromTemplate(self, template);
    const normalized = try normalizeSymbolicRewrites(
        self,
        symbolic,
        state,
        fuel,
    );
    if (normalized == symbolic) return false;
    // A rewrite right-hand side may introduce an ACUI head the template gate
    // could not see; the final direct match is positional, so bail rather
    // than commit a member split.
    if (self.shared.registry) |registry| {
        if (symbolicHasAcuiHead(registry, normalized)) return false;
    }
    return try TransparentMatch.tryMatchSymbolicToExprDirect(
        self,
        normalized,
        actual,
        state,
    );
}

fn templateHasAcuiHead(registry: anytype, template: TemplateExpr) bool {
    switch (template) {
        .binder => return false,
        .app => |app| {
            if (registry.hasStructuralCombiner(app.term_id)) return true;
            for (app.args) |arg| {
                if (templateHasAcuiHead(registry, arg)) return true;
            }
            return false;
        },
    }
}

/// Fixed subtrees are opaque here: template binders never reach inside them,
/// so no positional binding can be committed there.
fn symbolicHasAcuiHead(
    registry: anytype,
    symbolic: *const SymbolicExpr,
) bool {
    switch (symbolic.*) {
        .binder, .dummy, .fixed => return false,
        .app => |app| {
            if (registry.hasStructuralCombiner(app.term_id)) return true;
            for (app.args) |arg| {
                if (symbolicHasAcuiHead(registry, arg)) return true;
            }
            return false;
        },
    }
}
