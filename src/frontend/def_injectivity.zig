//! Which arguments of a head are forced by equality of two applications.
//! Shared by the search prunes (which may only pin or compare forced
//! arguments) and the transparent comparator (which retries a same-head def
//! mismatch by unfolding only when the mismatching argument is not forced).

const GlobalEnv = @import("./env.zig").GlobalEnv;
const RewriteRegistry = @import("./rewrite_registry.zig").RewriteRegistry;
const TemplateExpr = @import("./rules.zig").TemplateExpr;

/// Bound on nested def unfolding; def bodies only reference earlier terms, so
/// this is a defensive cap, not a semantic limit.
const max_depth = 64;

/// Does `h(a) ≡ h(b)` force `a[arg_idx] ≡ b[arg_idx]`? True for a rigid
/// primitive head, and for a transparent def whose body places that parameter
/// at a path of such heads (possibly through nested defs, each checked the same
/// way). False for ACUI / `@rewrite` / unavailable heads, and for a def arg the
/// body drops or only places under a non-determining head (the `const` trap:
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
    if (!env.hasAvailableTerm(head)) return false;
    if (registry) |reg| {
        if (reg.acui_by_head.contains(head)) return false;
        // A `@rewrite` head can reduce away, so its args are never forced,
        // even when it is also a def.
        if (reg.rewrites_by_head.contains(head)) return false;
    }
    const term = env.terms.items[head];
    if (!term.is_def) return true;
    const body = term.body orelse return true;
    if (arg_idx >= term.args.len) return false;
    return paramAtDeterminedPath(env, registry, body, arg_idx, depth + 1);
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
