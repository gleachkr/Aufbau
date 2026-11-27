//! What the compiler's two wasm entries (`wasm.zig`, `lsp_wasm.zig`) share
//! with their JS host: the allocator the host passes buffers through, the
//! locale switch, and pointer conversions.

const std = @import("std");
const mm0 = @import("mm0");

pub const allocator = std.heap.wasm_allocator;

pub export fn alloc(len: u32) u32 {
    if (len == 0) return 0;
    const buf = allocator.alloc(u8, len) catch return 0;
    return @intCast(@intFromPtr(buf.ptr));
}

pub export fn free(ptr: u32, len: u32) void {
    if (ptr == 0 or len == 0) return;
    allocator.free(ptrToSlice(ptr, len));
}

/// Select the diagnostic locale ("en", "de") for everything that follows.
/// Returns 1 on success, 0 for an unknown locale name (the current locale
/// is left unchanged). The embedding JS calls this once after
/// instantiation; there is no environment in browser wasm.
pub export fn set_locale(name_ptr: u32, name_len: u32) u32 {
    const name = ptrToConstSlice(name_ptr, name_len);
    const lang = mm0.parseCompilerLang(name) orelse return 0;
    mm0.setCompilerLang(lang);
    return 1;
}

pub fn ptrToSlice(ptr: u32, len: u32) []u8 {
    return @as([*]u8, @ptrFromInt(ptr))[0..len];
}

pub fn ptrToConstSlice(ptr: u32, len: u32) []const u8 {
    if (ptr == 0 or len == 0) return &.{};
    return @as([*]const u8, @ptrFromInt(ptr))[0..len];
}

pub fn slicePtr(bytes: []const u8) u32 {
    if (bytes.len == 0) return 0;
    return @intCast(@intFromPtr(bytes.ptr));
}
