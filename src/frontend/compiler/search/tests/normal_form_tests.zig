//! Agreement of the two normalizer engines on ACUI bags: inference compares
//! the proof-free `Canonicalizer`'s normal forms, and the checker proves the
//! proof-producing `Normalizer`'s, so a bag on which they differ is a line
//! inference accepts and the checker rejects, or the reverse.

const helpers = @import("./helpers.zig");
const std = helpers.std;
const ExprId = helpers.ExprId;
const TheoremContext = helpers.TheoremContext;
const CheckedLine = helpers.CheckedLine;
const CheckedIr = helpers.CheckedIr;
const fixtureFor = helpers.fixtureFor;
const ContextHarness = helpers.ContextHarness;
const normalizer_mod = @import("../../../normalizer.zig");
const Canonicalizer = normalizer_mod.Canonicalizer;
const Normalizer = normalizer_mod.Normalizer;

const mm0_src =
    \\delimiter $ ( ) $;
    \\provable sort wff;
    \\term bi (a b: wff): wff;
    \\--| @relation wff bi biid bitr bisym mpbi
    \\axiom biid (a: wff): $ bi a a $;
    \\axiom bitr (a b c: wff): $ bi a b $ > $ bi b c $ > $ bi a c $;
    \\axiom bisym (a b: wff): $ bi a b $ > $ bi b a $;
    \\axiom mpbi (a b: wff): $ bi a b $ > $ a $ > $ b $;
    \\
    \\sort ms;
    \\term mnil: ms;
    \\--| @acui ms_assoc ms_comm mnil _
    \\term mjoin (g h: ms): ms;
    \\term mhyp (a: wff): ms;
    \\term ms_eq (g h: ms): wff;
    \\--| @relation ms ms_eq ms_refl ms_trans ms_sym _
    \\axiom ms_refl (g: ms): $ ms_eq g g $;
    \\axiom ms_trans (g h i: ms): $ ms_eq g h $ > $ ms_eq h i $ > $ ms_eq g i $;
    \\axiom ms_sym (g h: ms): $ ms_eq g h $ > $ ms_eq h g $;
    \\axiom ms_assoc (g h i: ms): $ ms_eq (mjoin (mjoin g h) i) (mjoin g (mjoin h i)) $;
    \\axiom ms_comm (g h: ms): $ ms_eq (mjoin g h) (mjoin h g) $;
    \\axiom ms_unit (g: ms): $ ms_eq (mjoin mnil g) g $;
    \\--| @congr
    \\axiom mjoin_congr (g1 g2 h1 h2: ms):
    \\  $ ms_eq g1 g2 $ > $ ms_eq h1 h2 $ > $ ms_eq (mjoin g1 h1) (mjoin g2 h2) $;
    \\def m1 (a: wff): ms = $ mhyp a $;
    \\def m2 (a: wff): ms = $ mhyp a $;
    \\
    \\sort st;
    \\term snil: st;
    \\--| @acui st_assoc st_comm snil st_idem
    \\term sjoin (g h: st): st;
    \\term shyp (a: wff): st;
    \\term st_eq (g h: st): wff;
    \\--| @relation st st_eq st_refl st_trans st_sym _
    \\axiom st_refl (g: st): $ st_eq g g $;
    \\axiom st_trans (g h i: st): $ st_eq g h $ > $ st_eq h i $ > $ st_eq g i $;
    \\axiom st_sym (g h: st): $ st_eq g h $ > $ st_eq h g $;
    \\axiom st_assoc (g h i: st): $ st_eq (sjoin (sjoin g h) i) (sjoin g (sjoin h i)) $;
    \\axiom st_comm (g h: st): $ st_eq (sjoin g h) (sjoin h g) $;
    \\axiom st_idem (g: st): $ st_eq (sjoin g g) g $;
    \\axiom st_unit (g: st): $ st_eq (sjoin snil g) g $;
    \\--| @congr
    \\axiom sjoin_congr (g1 g2 h1 h2: st):
    \\  $ st_eq g1 g2 $ > $ st_eq h1 h2 $ > $ st_eq (sjoin g1 h1) (sjoin g2 h2) $;
    \\def s1 (a: wff): st = $ shyp a $;
    \\def s2 (a: wff): st = $ shyp a $;
    \\
    \\sort du;
    \\term dnil: du;
    \\def demp: du = $ dnil $;
    \\--| @acui du_assoc du_comm demp _
    \\term djoin (g h: du): du;
    \\term dhyp (a: wff): du;
    \\term du_eq (g h: du): wff;
    \\--| @relation du du_eq du_refl du_trans du_sym _
    \\axiom du_refl (g: du): $ du_eq g g $;
    \\axiom du_trans (g h i: du): $ du_eq g h $ > $ du_eq h i $ > $ du_eq g i $;
    \\axiom du_sym (g h: du): $ du_eq g h $ > $ du_eq h g $;
    \\axiom du_assoc (g h i: du): $ du_eq (djoin (djoin g h) i) (djoin g (djoin h i)) $;
    \\axiom du_comm (g h: du): $ du_eq (djoin g h) (djoin h g) $;
    \\axiom du_unit (g: du): $ du_eq (djoin demp g) g $;
    \\--| @congr
    \\axiom djoin_congr (g1 g2 h1 h2: du):
    \\  $ du_eq g1 g2 $ > $ du_eq h1 h2 $ > $ du_eq (djoin g1 h1) (djoin g2 h2) $;
    \\
    \\theorem t (a b: wff): $ a $;
;

/// Every bag of `atoms` with one to four leaves, in every tree shape.
fn allBags(
    allocator: std.mem.Allocator,
    theorem: *TheoremContext,
    join_id: u32,
    atoms: []const ExprId,
) ![]const ExprId {
    var out: std.ArrayListUnmanaged(ExprId) = .empty;
    var leaves: [4]ExprId = undefined;
    for (1..5) |len| {
        var count: usize = 1;
        for (0..len) |_| count *= atoms.len;
        for (0..count) |word| {
            var code = word;
            for (leaves[0..len]) |*leaf| {
                leaf.* = atoms[code % atoms.len];
                code /= atoms.len;
            }
            try appendTrees(allocator, theorem, join_id, leaves[0..len], &out);
        }
    }
    return out.items;
}

fn appendTrees(
    allocator: std.mem.Allocator,
    theorem: *TheoremContext,
    join_id: u32,
    leaves: []const ExprId,
    out: *std.ArrayListUnmanaged(ExprId),
) !void {
    if (leaves.len == 1) return try out.append(allocator, leaves[0]);
    for (1..leaves.len) |cut| {
        var lefts: std.ArrayListUnmanaged(ExprId) = .empty;
        var rights: std.ArrayListUnmanaged(ExprId) = .empty;
        try appendTrees(allocator, theorem, join_id, leaves[0..cut], &lefts);
        try appendTrees(allocator, theorem, join_id, leaves[cut..], &rights);
        for (lefts.items) |lhs| for (rights.items) |rhs| {
            try out.append(
                allocator,
                try theorem.interner.internApp(join_id, &.{ lhs, rhs }),
            );
        };
    }
}

test "proof-free and proof-producing normal forms agree on ACUI bags" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const allocator = arena.allocator();

    var fixture = try fixtureFor(allocator, mm0_src, "t");
    var theorem = TheoremContext.init(allocator);
    defer theorem.deinit();
    try theorem.seedAssertion(fixture.assertion);
    var harness = ContextHarness.init(allocator);
    defer harness.deinit();
    const context = harness.context(&fixture);
    const env = context.env;
    const a = theorem.theorem_vars.items[0];
    const b = theorem.theorem_vars.items[1];

    const Sort = struct {
        join: []const u8,
        atoms: []const []const u8,
        args: []const u8,
    };
    // Per sort: the combiner, then leaves built from it. An atom named
    // with a trailing `*` takes `a`, then `b`, as its argument; one
    // without takes none.
    const sorts = [_]Sort{
        // Non-idempotent: two defs cover `mhyp a`.
        .{ .join = "mjoin", .atoms = &.{ "mhyp", "m1", "m2", "mnil" }, .args = "aaa_" },
        // Idempotent, with the same two covering defs.
        .{ .join = "sjoin", .atoms = &.{ "shyp", "s1", "s2", "snil" }, .args = "aaa_" },
        // A unit that is a definition of another member.
        .{ .join = "djoin", .atoms = &.{ "dhyp", "dnil", "demp", "dhyp" }, .args = "a__b" },
    };
    for (sorts) |sort| {
        const join_id = env.term_names.get(sort.join).?;
        var atoms: [4]ExprId = undefined;
        for (sort.atoms, sort.args, &atoms) |name, arg, *atom| {
            const term_id = env.term_names.get(name).?;
            atom.* = switch (arg) {
                'a' => try theorem.interner.internApp(term_id, &.{a}),
                'b' => try theorem.interner.internApp(term_id, &.{b}),
                else => try theorem.interner.internApp(term_id, &.{}),
            };
        }
        const bags = try allBags(allocator, &theorem, join_id, &atoms);
        for (bags) |bag| {
            var canonicalizer = Canonicalizer.init(
                allocator,
                &theorem,
                context.registry,
                env,
                {},
            );
            defer canonicalizer.deinit();
            var lines: std.ArrayListUnmanaged(CheckedLine) = .empty;
            defer {
                CheckedIr.deinitLines(allocator, lines.items);
                lines.deinit(allocator);
            }
            var normalizer = Normalizer.init(
                allocator,
                &theorem,
                context.registry,
                env,
                &lines,
            );
            defer normalizer.deinit();
            const canonical = try canonicalizer.canonicalize(bag);
            const normal = (try normalizer.normalize(bag)).result_expr;
            if (canonical != normal) {
                std.debug.print("{s}: bag {d} canonical {d} normal {d}\n", .{
                    sort.join,
                    bag,
                    canonical,
                    normal,
                });
                return error.TestUnexpectedResult;
            }
        }
    }
}
