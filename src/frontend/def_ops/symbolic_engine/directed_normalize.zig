//! Directed rewrite normalization over symbolic expressions.
//!
//! An opened def body can hold symbolic values carrying unmaterialized def
//! dummies (after `beta` matches `Y · g` by opening `Y`, its conclusion's
//! `[x := a] e` side does), which the concrete normalizer cannot touch. Here
//! the `@rewrite` rules are applied to a fixpoint with the dummies left in
//! place; the deterministic matcher then compares the normal form directly,
//! and that match is what forces each dummy's witness (e.g. the stated
//! line's bound variable).

const std = @import("std");
const ExprId = @import("../../expr.zig").ExprId;
const Types = @import("../types.zig");
const MatchState = @import("../match_state.zig");
const RewriteApplication = @import("./rewrite_application.zig");

const SymbolicExpr = Types.SymbolicExpr;
const MatchSession = MatchState.MatchSession;

/// Rule applications allowed per normalization. The reductions this path
/// exists for (substitution ladders under a def unfold) take a few dozen
/// steps; the cap only guards non-terminating rule sets.
const directed_normalize_fuel: usize = 64;

pub const Fuel = struct {
    remaining: usize = directed_normalize_fuel,
    /// Set when a rule would fire with no fuel left, so a failed match may
    /// be a fuel artifact rather than a real mismatch.
    /// Recorded as `MatchSession.rewrite_fuel_exhausted` by `bigStepSymbolic`
    /// and `normalForm`, and surfaced as a `--debug inference` trace upstream.
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
            // expansions) can hold rewritable redexes; open and reduce them.
            // Keep the original node when nothing fires so no-op passes
            // preserve identity.
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
            if (try RewriteApplication.applyRewriteRuleToSymbolic(
                self,
                rule,
                current,
                state,
            )) |next| {
                // Out of fuel only when a rule would still fire: a term
                // that reaches its fixpoint on the last unit has a normal
                // form.
                if (fuel.remaining == 0) {
                    fuel.exhausted = true;
                    return current;
                }
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

/// Reduce a symbolic expression to a directed-rewrite fixpoint (or as far as
/// the fuel allows). Returns null when no rule applied anywhere, so the
/// caller keeps its original node.
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

pub const NormalForm = struct {
    expr: *const SymbolicExpr,
    /// A rule fired somewhere: `expr` differs from the input.
    changed: bool,
};

/// `symbolic` at its rewrite normal form. Null when the fuel ran out before
/// a fixpoint: there is no normal form to compare, and comparing the partial
/// reduct again would only reduce it further.
pub fn normalForm(
    self: anytype,
    symbolic: *const SymbolicExpr,
    state: *MatchSession,
) anyerror!?NormalForm {
    var fuel = Fuel{};
    const next = try normalizeSymbolicRewrites(self, symbolic, state, &fuel);
    if (fuel.exhausted) {
        state.rewrite_fuel_exhausted = true;
        return null;
    }
    return .{ .expr = next, .changed = fuel.remaining != directed_normalize_fuel };
}

/// Convert a concrete expression into the symbolic shape the normalizer can
/// reduce: app nodes above a rewritable head are opened into symbolic apps so
/// the bottom-up recursion can reduce nested redexes. Returns null when the
/// subtree contains no rewritable head — the caller keeps it `.fixed`
/// (nothing in it can reduce, and rule-lhs matching reads through fixed
/// nodes concretely).
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
