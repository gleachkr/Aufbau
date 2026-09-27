//! How matching treats a term head: whether it can change under conversion,
//! and which of its arguments equality of two applications forces. Shared by
//! the search prunes (which may only pin or compare forced arguments) and the
//! transparent comparator (which retries a same-head def mismatch by unfolding
//! only when the mismatching argument is not forced).

const GlobalEnv = @import("./env.zig").GlobalEnv;
const RewriteRegistry = @import("./rewrite_registry.zig").RewriteRegistry;
const TemplateExpr = @import("./rules.zig").TemplateExpr;

pub const HeadClass = enum {
    /// A primitive term, or a def without a body (nothing can unfold it):
    /// no conversion changes it, so two applications are equal only when
    /// their arguments are.
    rigid,
    /// A transparent def: it unfolds to its body.
    def,
    /// An `@acui` combiner: rearrangement can reorder, regroup, or (through
    /// the unit and idempotence) drop its arguments.
    acui,
    /// A `@rewrite` head (e.g. a substitution `sb_ty`): it can reduce to a
    /// different head, even when it is also a def or an ACUI combiner.
    rewrite,
    /// A term recovery discarded, or an id outside the environment.
    unavailable,
};

/// The class of `head`. Without a registry no head is ACUI or `@rewrite`.
pub fn classify(
    env: *const GlobalEnv,
    registry: ?*const RewriteRegistry,
    head: u32,
) HeadClass {
    if (!env.hasAvailableTerm(head)) return .unavailable;
    if (registry) |reg| {
        if (reg.rewrites_by_head.contains(head)) return .rewrite;
        if (reg.acui_by_head.contains(head)) return .acui;
    }
    const term = env.terms.items[head];
    return if (term.is_def and term.body != null) .def else .rigid;
}

/// Bound on nested def unfolding; def bodies only reference earlier terms, so
/// this is a defensive cap, not a semantic limit.
const max_depth = 64;

/// Does `h(a) ≡ h(b)` force `a[arg_idx] ≡ b[arg_idx]`? True for a rigid head,
/// and for a transparent def whose body places that parameter at a path of
/// such heads (possibly through nested defs, each checked the same way).
/// False for ACUI / `@rewrite` / unavailable heads, and for a def arg the body
/// drops or only places under a non-determining head (the `const` trap:
/// `const(X, Y) := X` has `const(X, t) ≡ const(X, t')` with `t ≠ t'`).
/// Binder-introducing defs are fine here: their dummies are fresh on both
/// sides and cannot occur in a real argument.
pub fn argDetermined(
    env: *const GlobalEnv,
    registry: ?*const RewriteRegistry,
    head: u32,
    arg_idx: usize,
) bool {
    return argDeterminedAt(env, registry, head, arg_idx, 0);
}

fn argDeterminedAt(
    env: *const GlobalEnv,
    registry: ?*const RewriteRegistry,
    head: u32,
    arg_idx: usize,
    depth: usize,
) bool {
    if (depth >= max_depth) return false;
    switch (classify(env, registry, head)) {
        .acui, .rewrite, .unavailable => return false,
        .rigid => return true,
        .def => {
            const term = env.terms.items[head];
            if (arg_idx >= term.args.len) return false;
            return paramAtDeterminedPath(env, registry, term.body.?, arg_idx, depth + 1);
        },
    }
}

fn paramAtDeterminedPath(
    env: *const GlobalEnv,
    registry: ?*const RewriteRegistry,
    template: TemplateExpr,
    param: usize,
    depth: usize,
) bool {
    switch (template) {
        .binder => |idx| return idx == param,
        .app => |app| {
            for (app.args, 0..) |arg, i| {
                if (paramAtDeterminedPath(env, registry, arg, param, depth) and
                    argDeterminedAt(env, registry, app.term_id, i, depth)) return true;
            }
            return false;
        },
    }
}
