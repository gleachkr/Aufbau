pub const Sort = packed struct(u8) {
    pure: bool = false,
    strict: bool = false,
    provable: bool = false,
    free: bool = false,
    _padding: u4 = 0,
};
