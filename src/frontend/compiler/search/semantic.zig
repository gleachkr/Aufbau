const types = @import("./types.zig");
const ExprId = @import("../../expr.zig").ExprId;
const TheoremContext = @import("../../expr.zig").TheoremContext;
const TemplateExpr = @import("../../rules.zig").TemplateExpr;
const Context = types.Context;
const head_class = @import("../../head_class.zig");
pub const HeadClass = head_class.HeadClass;

/// How conversion can treat `head` (see `head_class.HeadClass`).
pub fn headClass(context: *const Context, head: u32) HeadClass {
    return head_class.classify(context.env, context.registry, head);
}

/// No conversion changes `head`: a primitive term or a bodiless def. Any other
/// head may unfold, rearrange, or reduce, so a template carrying it cannot be
/// matched syntactically (`r : [y/x][q/refl A x] C` against the reduced
/// `refl A x : Id A x x`); such a pair is left to the validator's normalizing
/// matcher.
pub fn isRigidHead(context: *const Context, head: u32) bool {
    return headClass(context, head) == .rigid;
}

/// The rigid head applications of `head` show once def heads are unfolded
/// (`head_class.rigidHead`): one no conversion changes, so the validator's
/// def unfolding and ACUI/`@rewrite` canonicalization preserve it. Null on
/// exactly the heads those could rewrite.
pub fn rigidHead(context: *const Context, head: u32) ?u32 {
    return head_class.rigidHead(context.env, context.registry, head);
}

/// Whether applications of `a` and `b` show distinct rigid heads, which no
/// conversion reconciles (`head_class.rigidHeadsDiffer`).
pub fn rigidHeadsDiffer(context: *const Context, a: u32, b: u32) bool {
    return head_class.rigidHeadsDiffer(context.env, context.registry, a, b);
}

/// Does `h(a) ≡ h(b)` force the args at `arg_idx` equal? A lockstep walk may
/// compare, pin, or descend into only such args. See
/// `head_class.argDetermined`.
pub fn argDetermined(context: *const Context, head: u32, arg_idx: usize) bool {
    return head_class.argDetermined(context.env, context.registry, head, arg_idx);
}
