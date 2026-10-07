pub const HEAP_SIZE = 1 << 16;
pub const UHEAP_SIZE = 1 << 16;
pub const STACK_SIZE = 1 << 16;
pub const USTACK_SIZE = 1 << 16;
pub const ARENA_SIZE = 64 * 1024 * 1024; // 64MB, same as mm0-c

/// MMB dependency masks have exactly 55 bits, so a declaration may bind at
/// most 55 variables (visible bound binders, hidden dummies, and proof-stream
/// Dummy allocations together). A 56th binder's dep bit would shift out of
/// the mask and silently vanish, letting an expression with free variables
/// slip through dependency checking.
pub const MAX_BOUND_VARS = @bitSizeOf(u55);

/// mm0-c's `MAX_SORTS`: the sort table holds at most 128 sorts (a sort index
/// is 7 bits wide in `Arg` and `RetSort`).
pub const MAX_SORTS = 128;

/// Deepest nesting the math parser accepts. Its recursion is bounded by this
/// rather than by the runtime stack, so a deeply nested math string is a
/// parse error instead of a stack overflow. Debug builds spend roughly 2 KB
/// of stack per level; every hand-written theory nests below 64.
pub const MAX_MATH_DEPTH = 1024;
