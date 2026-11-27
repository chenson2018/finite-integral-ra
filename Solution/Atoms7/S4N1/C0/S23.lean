/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Atoms7.S4N1.C0.Actions

/-! Generated identity-class certificate for the product-row count. -/

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option Elab.async false

@[expose] public section

namespace RACert.S4N1.C0.S23

open RACert RACert.Problem

theorem cover3999 : P.CoversSplit 24 10 3999 0xffffffffffffaaaaffffffffffffaaaaffffffffffffaaaaffffffffffffaaaaffffffffaa00aa00ff00ff00aa00aa00ffffffffaa00aa00ff00ff00aa00aa00ffffffffffffaaaaffffffffffffaaaaffffffffa0a0a0a0ffffffffa0a0a0a0ffffffffaa00aa00ff00ff00aa00aa00cc00cc0080008000cc00cc0080008000 :=
  coversProjected check rows (by decide) (by decide) (xs := [516, 915, 1209, 1217, 1258, 1609]) (ps := [(8, [1217, 1609], [1266]), (14, [1217, 1609], [1266])]) (by decide +kernel)

noncomputable def f3999 (i : ℕ) := rowWeight keep4 twice4 i * P.leaf 24 (4094976 + i)

theorem c3999_0 : rowSum f3999 0 307 = 5506576 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 3999) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover3999 (by decide)
  decide +kernel

theorem c3999_1 : rowSum f3999 307 166 = 11491948 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 3999) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover3999 (by decide)
  decide +kernel

theorem c3999_2 : rowSum f3999 473 294 = 43585160 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 3999) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover3999 (by decide)
  decide +kernel

theorem c3999_3 : rowSum f3999 767 257 = 61982986 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 3999) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover3999 (by decide)
  decide +kernel

theorem sum3999 : rowSum f3999 0 1024 = 122566670 :=
  rowSum_append (F := f3999) (lo := 0) (n := 307) (m := 717) (A := 5506576) (B := 117060094) c3999_0 (rowSum_append (F := f3999) (lo := 307) (n := 166) (m := 551) (A := 11491948) (B := 105568146) c3999_1 (rowSum_append (F := f3999) (lo := 473) (n := 294) (m := 257) (A := 43585160) (B := 61982986) c3999_2 (c3999_3)))

theorem h3999 : P.leaf 34 3999 = 122566670 :=
  leaf_weighted (k := 24) (d := 10) (H := 3999) (keep := keep4) (twice := twice4) rows (by decide) (by decide) bal4 (invRow4 (H := 3999) (by decide) (by decide +kernel)) sum3999

theorem cover4004 : P.CoversSplit 24 10 4004 0x8800000080008000000000000000000088000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000088000000800080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 475, 508, 515, 517, 522, 524, 566, 915, 916, 1202, 1258, 1308]) (by decide +kernel)

theorem c4004_0 : P.sumLeaves 24 4100096 1024 = 225584 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 4004) (lo := 0) (len := 1024) (W := 225584) check rows elimOK (by decide) (by decide) cover4004 (by decide)
  decide +kernel

theorem h4004 : P.leaf 34 4004 = 225584 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 225584)]) (.cons c4004_0 (.nil)) (by decide) (by decide))

theorem cover4005 : P.CoversSplit 24 10 4005 0xcc00cc00c40080000000000000000000cc00cc00c400800000000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00c40080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 475, 515, 522, 566, 915, 916, 1202, 1217, 1308]) (by decide +kernel)

theorem c4005_0 : P.sumLeaves 24 4101120 1024 = 1652812 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 4005) (lo := 0) (len := 1024) (W := 1652812) check rows elimOK (by decide) (by decide) cover4005 (by decide)
  decide +kernel

theorem h4005 : P.leaf 34 4005 = 1652812 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1652812)]) (.cons c4005_0 (.nil)) (by decide) (by decide))

theorem cover4006 : P.CoversSplit 24 10 4006 0xaaaa0000a1a100000000000000000000aaaa00000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000aaaa0000a1a100000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 515, 517, 522, 524, 566, 1202, 1258, 1259, 1308]) (by decide +kernel)

theorem c4006_0 : P.sumLeaves 24 4102144 1024 = 1915714 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 4006) (lo := 0) (len := 1024) (W := 1915714) check rows elimOK (by decide) (by decide) cover4006 (by decide)
  decide +kernel

theorem h4006 : P.leaf 34 4006 = 1915714 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1915714)]) (.cons c4006_0 (.nil)) (by decide) (by decide))

theorem cover4007 : P.CoversSplit 24 10 4007 0xfffffffff4f4a0a00000000000000000fffffffff4f4a0a000000000000000000000000000200020000000000000000000000000002000200000000000000000fffffffff4f4a0a00000000000000000000000000000000000000000000000000000000000200020000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 517, 522, 524, 566, 1202, 1209, 1217, 1258, 1259, 1308]) (by decide +kernel)

theorem c4007_0 : P.sumLeaves 24 4103168 894 = 2598412 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 4007) (lo := 0) (len := 894) (W := 2598412) check rows elimOK (by decide) (by decide) cover4007 (by decide)
  decide +kernel

theorem c4007_1 : P.sumLeaves 24 4104062 130 = 7715648 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 4007) (lo := 894) (len := 130) (W := 7715648) check rows elimOK (by decide) (by decide) cover4007 (by decide)
  decide +kernel

theorem h4007 : P.leaf 34 4007 = 10314060 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(894, 2598412), (130, 7715648)]) (.cons c4007_0 (.cons c4007_1 (.nil))) (by decide) (by decide))

theorem cover4008 : P.CoversSplit 24 10 4008 0x8800000080008000000000000000000088000000000000000000000000000000000000000000000000220000002000000000000000000000002200000000000088000000800080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 508, 515, 517, 522, 565, 915, 1202, 1258, 1308, 1609]) (by decide +kernel)

theorem c4008_0 : P.sumLeaves 24 4104192 448 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 4008) (lo := 0) (len := 448) (W := 0) check rows elimOK (by decide) (by decide) cover4008 (by decide)
  decide +kernel

theorem contract4008_1 : P.leaf 30 64135 = 23450 := by
  exact leaf_contract_factors (k := 30) (b := 19) (H := 64135) (ss := [(6, 1, 466), (26, 1, 472), (27, 1, 473), (29, 1, 473), (2, 1, 474), (3, 1, 524), (14, 1, 923), (18, 1, 923), (19, 1, 965), (15, 1, 930), (16, 1, 1265)]) (ids := [2, 3, 5, 6, 7, 8, 9, 10, 11, 15, 18, 19, 20, 21, 22, 26, 28, 29, 23]) (cs := [1, 1, 2, 3, 1, 4, 5, 6, 7, 8, 9, 10, 1, 1, 1, 11, 1, 1, 12, 13, 14, 15, 16, 20, 1, 1, 17, 1, 18, 19]) (bs := [18, 1]) (W := 23450) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c4008_1 : P.sumLeaves 24 4104640 64 = 23450 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 64135) rows (by decide) (by decide)).symm.trans contract4008_1

theorem c4008_2 : P.sumLeaves 24 4104704 512 = 205266 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 4008) (lo := 512) (len := 512) (W := 205266) check rows elimOK (by decide) (by decide) cover4008 (by decide)
  decide +kernel

theorem h4008 : P.leaf 34 4008 = 228716 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(448, 0), (64, 23450), (512, 205266)]) (.cons c4008_0 (.cons c4008_1 (.cons c4008_2 (.nil)))) (by decide) (by decide))

theorem cover4009 : P.CoversSplit 24 10 4009 0xcc00cc00c40080000000000000000000cc00cc00c400800000000000000000000000000000000000003300000020000000000000000000000033003300200000cc00cc00c40080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 515, 522, 565, 915, 1202, 1217, 1308, 1609]) (ps := [(4, [515], [565])]) (by decide +kernel)

theorem c4009_0 : P.sumLeaves 24 4105216 1024 = 3331363 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 4009) (lo := 0) (len := 1024) (W := 3331363) check rows elimOK (by decide) (by decide) cover4009 (by decide)
  decide +kernel

theorem h4009 : P.leaf 34 4009 = 3331363 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 3331363)]) (.cons c4009_0 (.nil)) (by decide) (by decide))

theorem cover4010 : P.CoversSplit 24 10 4010 0xaaaa0000a1a100000000000000000000aaaa00000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000aaaa0000a1a100000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 515, 517, 522, 565, 916, 1202, 1258, 1259, 1308]) (ps := [(16, [1308], [1258])]) (by decide +kernel)

theorem c4010_0 : P.sumLeaves 24 4106240 1024 = 1576708 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 4010) (lo := 0) (len := 1024) (W := 1576708) check rows elimOK (by decide) (by decide) cover4010 (by decide)
  decide +kernel

theorem h4010 : P.leaf 34 4010 = 1576708 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1576708)]) (.cons c4010_0 (.nil)) (by decide) (by decide))

theorem cover4011 : P.CoversSplit 24 10 4011 0xfffffffff4f4a0a00000000000000000fffffffff4f4a0a000000000000000000000000000200020000000000000000000000000002000200000000000000000fffffffff4f4a0a00000000000000000000000000000000000000000000000000000000000200020000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [515, 522, 565, 916, 1202, 1209, 1217, 1258, 1259, 1308]) (ps := [(16, [615, 1308], [1258])]) (by decide +kernel)

theorem c4011_0 : P.sumLeaves 24 4107264 894 = 5312566 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 4011) (lo := 0) (len := 894) (W := 5312566) check rows elimOK (by decide) (by decide) cover4011 (by decide)
  decide +kernel

theorem c4011_1 : P.sumLeaves 24 4108158 130 = 13566828 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 4011) (lo := 894) (len := 130) (W := 13566828) check rows elimOK (by decide) (by decide) cover4011 (by decide)
  decide +kernel

theorem h4011 : P.leaf 34 4011 = 18879394 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(894, 5312566), (130, 13566828)]) (.cons c4011_0 (.cons c4011_1 (.nil))) (by decide) (by decide))

theorem cover4012 : P.CoversSplit 24 10 4012 0x8800000080008000000000000000000088000000000000000000000000000000000000000000000000220000002000200000000000000000002200000000000088000000800080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 508, 515, 517, 522, 915, 1202, 1258, 1308, 1609]) (by decide +kernel)

theorem c4012_0 : P.sumLeaves 24 4108288 1024 = 1118886 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 4012) (lo := 0) (len := 1024) (W := 1118886) check rows elimOK (by decide) (by decide) cover4012 (by decide)
  decide +kernel

theorem h4012 : P.leaf 34 4012 = 1118886 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1118886)]) (.cons c4012_0 (.nil)) (by decide) (by decide))

theorem cover4013 : P.CoversSplit 24 10 4013 0xcc00cc00c40080000000000000000000cc00cc00c400800000000000000000000000000000000000003300330020002000000000000000000033003300200020cc00cc00c40080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 515, 522, 915, 1202, 1217, 1308, 1609]) (by decide +kernel)

theorem c4013_0 : P.sumLeaves 24 4109312 1024 = 9074589 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 4013) (lo := 0) (len := 1024) (W := 9074589) check rows elimOK (by decide) (by decide) cover4013 (by decide)
  decide +kernel

theorem h4013 : P.leaf 34 4013 = 9074589 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 9074589)]) (.cons c4013_0 (.nil)) (by decide) (by decide))

theorem cover4014 : P.CoversSplit 24 10 4014 0xaaaa0000a1a100000000000000000000aaaa00000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000aaaa0000a1a100000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 515, 517, 522, 1202, 1258, 1259, 1308]) (ps := [(16, [1308], [1258])]) (by decide +kernel)

theorem c4014_0 : P.sumLeaves 24 4110336 1024 = 8091827 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 4014) (lo := 0) (len := 1024) (W := 8091827) check rows elimOK (by decide) (by decide) cover4014 (by decide)
  decide +kernel

theorem h4014 : P.leaf 34 4014 = 8091827 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 8091827)]) (.cons c4014_0 (.nil)) (by decide) (by decide))

theorem cover4015 : P.CoversSplit 24 10 4015 0xfffffffff4f4a0a00000000000000000fffffffff4f4a0a000000000000000000000000000200020000000000000000000000000002000200000000000000000fffffffff4f4a0a00000000000000000000000000000000000000000000000000000000000200020000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [515, 522, 1202, 1209, 1217, 1258, 1259, 1308]) (ps := [(16, [1308], [1258])]) (by decide +kernel)

theorem c4015_0 : P.sumLeaves 24 4111360 894 = 12833540 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 4015) (lo := 0) (len := 894) (W := 12833540) check rows elimOK (by decide) (by decide) cover4015 (by decide)
  decide +kernel

theorem c4015_1 : P.sumLeaves 24 4112254 130 = 30459169 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 4015) (lo := 894) (len := 130) (W := 30459169) check rows elimOK (by decide) (by decide) cover4015 (by decide)
  decide +kernel

theorem h4015 : P.leaf 34 4015 = 43292709 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(894, 12833540), (130, 30459169)]) (.cons c4015_0 (.cons c4015_1 (.nil))) (by decide) (by decide))

theorem cover4022 : P.CoversSplit 24 10 4022 0xfffffffff5f5a0a0fffffffff5f5a0a0aaaaaaaa0000a000aaaaaaaa00000000ffffffffa000a000ff00ff00a000a000aaaaaaaa0000a000aa00aa0000000000fffffffff5f5a0a0fffffffff5f5a0a000000000000000000000000000000000ffffffffa000a000ff00ff00a000a00000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 517, 915, 1202, 1209, 1258, 1308]) (ps := [(5, [475, 524], [517]), (8, [531], [517])]) (by decide +kernel)

theorem c4022_0 : P.sumLeaves 24 4118528 440 = 648960 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 4022) (lo := 0) (len := 440) (W := 648960) check rows elimOK (by decide) (by decide) cover4022 (by decide)
  decide +kernel

theorem c4022_1 : P.sumLeaves 24 4118968 258 = 2086116 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 4022) (lo := 440) (len := 258) (W := 2086116) check rows elimOK (by decide) (by decide) cover4022 (by decide)
  decide +kernel

theorem c4022_2 : P.sumLeaves 24 4119226 234 = 4076119 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 4022) (lo := 698) (len := 234) (W := 4076119) check rows elimOK (by decide) (by decide) cover4022 (by decide)
  decide +kernel

theorem c4022_3 : P.sumLeaves 24 4119460 92 = 9560228 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 4022) (lo := 932) (len := 92) (W := 9560228) check rows elimOK (by decide) (by decide) cover4022 (by decide)
  decide +kernel

theorem h4022 : P.leaf 34 4022 = 16371423 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(440, 648960), (258, 2086116), (234, 4076119), (92, 9560228)]) (.cons c4022_0 (.cons c4022_1 (.cons c4022_2 (.cons c4022_3 (.nil))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(3999, 12), (4004, 24), (4005, 24), (4006, 48), (4007, 48), (4008, 24), (4009, 24), (4010, 48), (4011, 48), (4012, 48), (4013, 48), (4014, 48), (4015, 48), (4022, 24)]

theorem segOK : checkSeg 16 perms 3999 4023 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 3999 4023 516 6518904168 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 6518904168)
    (SegSum.cons (w := 12) h3999 (SegSum.cons (w := 24) h4004 (SegSum.cons (w := 24) h4005 (SegSum.cons (w := 48) h4006 (SegSum.cons (w := 48) h4007 (SegSum.cons (w := 24) h4008 (SegSum.cons (w := 24) h4009 (SegSum.cons (w := 48) h4010 (SegSum.cons (w := 48) h4011 (SegSum.cons (w := 48) h4012 (SegSum.cons (w := 48) h4013 (SegSum.cons (w := 48) h4014 (SegSum.cons (w := 48) h4015 (SegSum.cons (w := 24) h4022 (show SegSum (P.leaf 34) [] 0 from rfl))))))))))))))) (by decide)

end RACert.S4N1.C0.S23
