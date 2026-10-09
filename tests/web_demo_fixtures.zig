//! The one roster of web-demo examples. Each entry ships
//! `tests/proof_cases/{name}.{mm0,auf}` and is listed in the generated
//! `fixtures/manifest.json`, which is what the demo page builds its example
//! picker from, so adding an example is a single edit here. build.zig
//! installs them; the proof-case tests check that each one is a single
//! file, since the demo page reads the text as is and does not join
//! `import`s or `include`s.

pub const Fixture = struct {
    name: []const u8,
    /// Display name in the picker; defaults to `name`.
    label: ?[]const u8 = null,
};

pub const fixtures = [_]Fixture{
    .{ .name = "hilbert" },
    .{ .name = "russell" },
    .{ .name = "tseitin" },
    .{ .name = "robinson" },
    .{ .name = "aristotle" },
    .{ .name = "peirce" },
    .{ .name = "gentzen" },
    .{ .name = "prawitz" },
    .{ .name = "barcan" },
    .{ .name = "prior" },
    .{ .name = "pnueli" },
    .{ .name = "barwise" },
    .{ .name = "loeb" },
    .{ .name = "church" },
    .{ .name = "leibniz" },
    .{ .name = "mac_lane", .label = "mac lane" },
    .{ .name = "martin_lof", .label = "martin-löf" },
    .{ .name = "peano" },
    .{ .name = "euclid" },
    .{ .name = "smullyan" },
    .{ .name = "zermelo" },
    .{ .name = "tait" },
    .{ .name = "pratt" },
    .{ .name = "hoare" },
    .{ .name = "diaconescu" },
    .{ .name = "herbrand" },
    .{ .name = "girard" },
    .{ .name = "reynolds" },
    .{ .name = "cardano" },
    .{ .name = "knaster" },
};
