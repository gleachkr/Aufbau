//! Directed rewrite normalization over symbolic expressions.
//!
//! Big-step reduction for the semantic def-eq search (task #181, subsuming
//! the task-#180 conclusion fallback). After `beta` matches `Y · g` by
//! opening `Y`, its conclusion's `[x := a] e` side holds symbolic values
//! carrying unmaterialized def dummies — the strict normalizer cannot touch
//! it (not concrete), and pricing each `@rewrite` reduction as its own
//! semantic step makes a substitution ladder unpayable within the search
//! budget. Here the `@rewrite` rules are applied to a fixpoint as ONE
//! semantic step, dummies staying in place; the search's ordinary direct
//! match of the normal form is what forces each dummy's witness (e.g. the
//! stated line's bound variable).

const std = @import("std");
const ExprId = @import("../../expr.zig").ExprId;
const Types = @import("../types.zig");
const MatchState = @import("../match_state.zig");
const RewriteApplication = @import("./rewrite_application.zig");

const SymbolicExpr = Types.SymbolicExpr;
const MatchSession = MatchState.MatchSession;

/// Rule applications allowed per big-step. The reductions this path exists
/// for (substitution ladders under a def unfold) take a few dozen steps; the
/// cap only guards non-terminating rule sets.
const directed_normalize_fuel: usize = 64;

pub const Fuel = struct {
    remaining: usize = directed_normalize_fuel,
    /// Set when the cap was hit while rewrite rules remained to try, so a
    /// failed match may be a fuel artifact rather than a real mismatch.
    /// Recorded as `MatchSession.rewrite_fuel_exhausted` by the big-step
    /// entry points and surfaced as a `--debug inference` trace upstream.
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
            .binder, .dummy => return current,
            // Nested fixed subtrees (rule-rhs substitution entries, def
            // expansions) can hold rewritable redexes; open and reduce them
            // like `bigStepExpr` does at the root. Keep the original node
            // when nothing fires so no-op passes preserve identity.
            .fixed => |expr_id| {
                const registry = self.shared.registry orelse return current;
                const opened = (try openExprForNormalize(
                    self,
                    registry,
                    expr_id,
                )) orelse return current;
                const fuel_before = fuel.remaining;
                const reduced = try normalizeSymbolicRewrites(
                    self,
                    opened,
                    state,
                    fuel,
                );
                if (fuel.remaining == fuel_before) return current;
                return reduced;
            },
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

/// One semantic-search big-step over a symbolic expression: reduce it to a
/// directed-rewrite fixpoint, priced by the caller as a single step. Returns
/// null when no rule applied anywhere — the step is a no-op and must not be
/// recursed on as progress.
pub fn bigStepSymbolic(
    self: anytype,
    symbolic: *const SymbolicExpr,
    state: *MatchSession,
) anyerror!?*const SymbolicExpr {
    var fuel = Fuel{};
    const next = try normalizeSymbolicRewrites(self, symbolic, state, &fuel);
    if (fuel.exhausted) state.rewrite_fuel_exhausted = true;
    if (fuel.remaining == directed_normalize_fuel) return null;
    return next;
}

/// One semantic-search big-step over a concrete expression. App nodes above
/// a rewritable head are opened into symbolic apps so the bottom-up
/// recursion can reduce nested redexes; subtrees with no rewritable head
/// anywhere stay `.fixed` (nothing in them can reduce, and rule-lhs matching
/// reads through fixed nodes concretely). Returns null when no rule applied.
pub fn bigStepExpr(
    self: anytype,
    expr_id: ExprId,
    state: *MatchSession,
) anyerror!?*const SymbolicExpr {
    const registry = self.shared.registry orelse return null;
    const opened = (try openExprForNormalize(
        self,
        registry,
        expr_id,
    )) orelse return null;
    return try bigStepSymbolic(self, opened, state);
}

/// Convert a concrete expression into the symbolic shape the normalizer can
/// reduce. Returns null when the subtree contains no rewritable head — the
/// caller keeps it `.fixed` (or skips the big-step entirely at the root).
fn openExprForNormalize(
    self: anytype,
    registry: anytype,
    expr_id: ExprId,
) anyerror!?*const SymbolicExpr {
    const node = self.shared.theorem.interner.node(expr_id);
    const app = switch (node.*) {
        .app => |value| value,
        .variable, .placeholder => return null,
    };
    var any_rewritable = registry.getRewriteRules(app.term_id).len != 0;
    const args = try self.shared.scratch().alloc(
        *const SymbolicExpr,
        app.args.len,
    );
    for (app.args, 0..) |arg, idx| {
        if (try openExprForNormalize(self, registry, arg)) |opened| {
            args[idx] = opened;
            any_rewritable = true;
        } else {
            args[idx] = try self.allocSymbolic(.{ .fixed = arg });
        }
    }
    if (!any_rewritable) return null;
    return try self.allocSymbolic(.{ .app = .{
        .term_id = app.term_id,
        .args = args,
    } });
}
