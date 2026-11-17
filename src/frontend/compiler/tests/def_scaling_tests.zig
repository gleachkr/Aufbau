//! Context members that differ only deep inside def encodings (successor
//! numerals in tagged pairs) and meet, once unfolded, at a stuck `@rewrite`
//! head or at an ACUI head. Comparing them pairwise was exponential before the
//! comparison became deterministic (#633); the work now grows with the square
//! of the member count, which the ratio between two sizes pins.

const helpers = @import("./helpers.zig");
const std = helpers.std;
const Compiler = helpers.Compiler;
const FrontendExpr = helpers.FrontendExpr;

const theory_prefix =
    \\delimiter $ ( ) { } [ / ] , | $;
    \\sort fml;
    \\strict provable sort wff;
    \\sort set;
    \\strict sort class;
    \\sort hyps;
    \\term im (p q: fml): fml;
    \\infixr im: $→$ prec 25;
    \\term not (p: fml): fml;
    \\prefix not: $¬$ prec 41;
    \\term and (p q: fml): fml;
    \\infixr and: $∧$ prec 30;
    \\term or (p q: fml): fml;
    \\infixr or: $∨$ prec 28;
    \\term bi (p q: fml): fml;
    \\infixr bi: $↔$ prec 20;
    \\term bot: fml;
    \\prefix bot: $⊥$ prec max;
    \\term all {x: set} (p: fml x): fml;
    \\prefix all: $∀$ prec 41;
    \\term ex {x: set} (p: fml x): fml;
    \\prefix ex: $∃$ prec 41;
    \\term cv (a: set): class;
    \\coercion cv: set > class;
    \\term cab {x: set} (p: fml x): class;
    \\notation cab {x: set} (p: fml x): class = (${$:max) x ($|$:0) p ($}$:0);
    \\term welc (a: set) (A: class): fml;
    \\infixl welc: $∊$ prec 50;
    \\term sb_c {x: set} (t: set x) (A: class x): class;
    \\notation sb_c {x: set} (t: set x) (A: class x): class =
    \\  ($⟦$:41) x ($/$:0) t ($⟧$:0) A;
    \\term isset (A: class): fml;
    \\term hyps_eq (G H: hyps): wff;
    \\term emp: hyps;
    \\--| @acui hyps_assoc hyps_comm emp hyps_idem
    \\term join (G H: hyps): hyps;
    \\infixl join: $,$ prec 5;
    \\term hyp (p: fml): hyps;
    \\coercion hyp: fml > hyps;
    \\term nd (G: hyps) (p: fml): wff;
    \\infixl nd: $⇒$ prec 0;
    \\term ceqt (A B: class): wff;
    \\infixl ceqt: $≐$ prec 1;
    \\--| @relation hyps hyps_eq hyps_refl hyps_trans hyps_sym _
    \\axiom hyps_refl (G: hyps): $ hyps_eq G G $;
    \\axiom hyps_trans (G H K: hyps): $ hyps_eq G H $ > $ hyps_eq H K $ > $ hyps_eq G K $;
    \\axiom hyps_sym (G H: hyps): $ hyps_eq G H $ > $ hyps_eq H G $;
    \\axiom hyps_assoc (G H K: hyps): $ hyps_eq ((G , H) , K) (G , (H , K)) $;
    \\axiom hyps_comm (G H: hyps): $ hyps_eq (G , H) (H , G) $;
    \\axiom hyps_idem (G: hyps): $ hyps_eq (G , G) G $;
    \\axiom hyps_unit (G: hyps): $ hyps_eq (emp , G) G $;
    \\term seq_eq (s t: wff): wff;
    \\infixl seq_eq: $⟚$ prec 1;
    \\term iff (p q: fml): wff;
    \\infixr iff: $⟺$ prec 20;
    \\--| @relation wff seq_eq seq_refl seq_trans seq_sym seq_mp
    \\axiom seq_refl (s: wff): $ s ⟚ s $;
    \\axiom seq_trans (s t u: wff): $ s ⟚ t $ > $ t ⟚ u $ > $ s ⟚ u $;
    \\axiom seq_sym (s t: wff): $ s ⟚ t $ > $ t ⟚ s $;
    \\axiom seq_mp (s t: wff): $ s ⟚ t $ > $ s $ > $ t $;
    \\--| @relation fml iff iff_refl iff_trans iff_sym _
    \\axiom iff_refl (p: fml): $ p ⟺ p $;
    \\axiom iff_trans (p q r: fml): $ p ⟺ q $ > $ q ⟺ r $ > $ p ⟺ r $;
    \\axiom iff_sym (p q: fml): $ p ⟺ q $ > $ q ⟺ p $;
    \\--| @congr
    \\axiom join_congr (G1 G2 H1 H2: hyps):
    \\  $ hyps_eq G1 G2 $ > $ hyps_eq H1 H2 $ > $ hyps_eq (G1 , H1) (G2 , H2) $;
    \\--| @congr
    \\axiom hyp_congr (p q: fml): $ p ⟺ q $ > $ hyps_eq (hyp p) (hyp q) $;
    \\--| @congr
    \\axiom nd_congr (G H: hyps) (p q: fml):
    \\  $ hyps_eq G H $ > $ p ⟺ q $ > $ (G ⇒ p) ⟚ (H ⇒ q) $;
    \\--| @relation class ceqt ceqt_refl ceqt_trans ceqt_sym _
    \\axiom ceqt_refl (A: class): $ A ≐ A $;
    \\axiom ceqt_trans (A B C: class): $ A ≐ B $ > $ B ≐ C $ > $ A ≐ C $;
    \\axiom ceqt_sym (A B: class): $ A ≐ B $ > $ B ≐ A $;
    \\--| @rewrite
    \\axiom sb_c_cv {x: set} (t: set x): $ (⟦ x / t ⟧ x) ≐ t $;
    \\axiom ax (G: hyps) (p: fml): $ G , p ⇒ p $;
    \\def ceq (A B: class) (.z: set): fml = $ ∀ z (z ∊ A ↔ z ∊ B) $;
    \\infixl ceq: $=$ prec 50;
    \\def wcel (A B: class) (.x: set): fml = $ ∃ x (x = A ∧ x ∊ B) $;
    \\infixl wcel: $∈$ prec 50;
    \\def c0 (.x: set): class = $ {x | ⊥} $;
    \\def cpr (A B: class) (.x: set): class = $ {x | x = A ∨ x = B} $;
    \\def csn (A: class): class = $ cpr A A $;
    \\def opair (A B: class): class = $ cpr (csn A) (cpr A B) $;
    \\def cun (A B: class) (.x: set): class = $ {x | x ∊ A ∨ x ∊ B} $;
    \\def suc (A: class): class = $ cun A (csn A) $;
    \\def k0: class = $ c0 $;
    \\--| @acui cu_assoc cu_comm c0 cu_idem
    \\term cu (A B: class): class;
    \\axiom cu_assoc (A B C: class): $ cu (cu A B) C ≐ cu A (cu B C) $;
    \\axiom cu_comm (A B: class): $ cu A B ≐ cu B A $;
    \\axiom cu_idem (A: class): $ cu A A ≐ A $;
    \\axiom cu_unit (A: class): $ cu c0 A ≐ A $;
    \\
;

const Shape = enum {
    /// `rtag_i := ⟦ x / t ⟧ (opair k_i A)`
    rewrite_head,
    /// `atag_i := opair (cu k_i A) A`, `cu` an ACUI union
    acui_head,
};

/// A theory with `n` member defs and the one-line proof of a context
/// `G , m_1 , … , w ∊ L , … , m_n ⇒ w ∊ L` by `ax`.
fn generate(allocator: std.mem.Allocator, shape: Shape, n: usize) !struct { mm0: []u8, auf: []u8 } {
    var mm0: std.ArrayList(u8) = .empty;
    errdefer mm0.deinit(allocator);
    try mm0.appendSlice(allocator, theory_prefix);
    for (1..n + 1) |i| try mm0.print(allocator, "def k{d}: class = $ suc k{d} $;\n", .{ i, i - 1 });
    for (1..n + 1) |i| switch (shape) {
        .rewrite_head => try mm0.print(allocator, "def rtag{d} {{x: set}} (t: set x) (A: class x): class = $ ⟦ x / t ⟧ (opair k{d} A) $;\n", .{ i, i }),
        .acui_head => try mm0.print(allocator, "def atag{d} (A: class): class = $ opair (cu k{d} A) A $;\n", .{ i, i }),
    };
    var line: std.ArrayList(u8) = .empty;
    defer line.deinit(allocator);
    try line.appendSlice(allocator, "G");
    for (1..n + 1) |i| {
        if (i == n / 2 + 1) try line.appendSlice(allocator, " , w ∊ L");
        switch (shape) {
            .rewrite_head => try line.print(allocator, " , rtag{d} x t a ∈ L", .{i}),
            .acui_head => try line.print(allocator, " , atag{d} a ∈ L", .{i}),
        }
    }
    try line.appendSlice(allocator, " ⇒ w ∊ L");
    const params = switch (shape) {
        .rewrite_head => "(G: hyps) (a w t: set) (L: class) {x: set}",
        .acui_head => "(G: hyps) (a w: set) (L: class)",
    };
    try mm0.print(allocator, "theorem t1 {s}: $ {s} $;\n", .{ params, line.items });
    const auf = try std.fmt.allocPrint(allocator, "t1\n---\nl1: $ {s} $ by ax []\n", .{line.items});
    return .{ .mm0 = try mm0.toOwnedSlice(allocator), .auf = auf };
}

/// Interning and symbolic-matching work to compile the generated proof.
fn compileWork(shape: Shape, n: usize) !u64 {
    const allocator = std.testing.allocator;
    const source = try generate(allocator, shape, n);
    defer allocator.free(source.mm0);
    defer allocator.free(source.auf);
    const before = FrontendExpr.work_ticks + FrontendExpr.work_ticks_sym;
    var compiler = Compiler.initWithProof(allocator, source.mm0, source.auf);
    const mmb = try compiler.compileMmb(allocator);
    defer allocator.free(mmb);
    return FrontendExpr.work_ticks + FrontendExpr.work_ticks_sym - before;
}

test "def-encoded context members compare in work quadratic in their count" {
    for ([_]Shape{ .rewrite_head, .acui_head }) |shape| {
        const small = try compileWork(shape, 8);
        const large = try compileWork(shape, 32);
        // Four times the members: quadratic work is at most 16 times the
        // smaller compile's; the exponential comparison was 40 times and
        // more at these sizes.
        std.testing.expect(large < 24 * small) catch |err| {
            std.debug.print("{s}: {d} work at 8 members, {d} at 32\n", .{ @tagName(shape), small, large });
            return err;
        };
    }
}
