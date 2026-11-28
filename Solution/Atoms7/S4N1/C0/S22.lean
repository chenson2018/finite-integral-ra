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

namespace RACert.S4N1.C0.S22

open RACert RACert.Problem

theorem cover4004 : P.CoversSplit 24 10 4004 0x8800000080008000000000000000000088000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000088000000800080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 475, 508, 515, 517, 522, 524, 566, 915, 916, 1202, 1258, 1308]) (by decide +kernel)

theorem h4004 : P.leaf 34 4004 = 225584 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 4004) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 4004) (weight := fun _ => 1) (xs := [463, 479, 507, 511, 847, 891, 895, 975, 991, 1019, 1023]) check rows elimOK (by decide) (by decide) cover4004 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover50223 : P.CoversSplit 24 10 50223 0xcc00c800c8000000000000000000000084008000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000080008000800000000000000000000000800080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 517, 522, 529, 572, 858, 860, 865, 872, 1202]) (by decide +kernel)

theorem h50223 : P.leaf 34 50223 = 1652812 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 50223) (keep := keep2) (twice := twice2) rows (by decide) (by decide) bal2 (invRow2 (H := 50223) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 50223) (weight := rowWeight keep2 twice2) (xs := [367, 383, 479, 495, 511, 858, 879, 890, 895, 987, 990, 991, 1003, 1006, 1007, 1018, 1019, 1022, 1023]) check rows elimOK (by decide) (by decide) cover50223 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h4005 : P.leaf 34 4005 = 1652812 :=
  orient5 (v := 50223) (by decide) (by decide +kernel) h50223

theorem cover4006 : P.CoversSplit 24 10 4006 0xaaaa0000a1a100000000000000000000aaaa00000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000aaaa0000a1a100000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 515, 517, 522, 524, 566, 1202, 1258, 1259, 1308]) (by decide +kernel)

theorem c4006_0 : P.sumLeaves 24 4102144 1024 = 1915714 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 4006) (lo := 0) (len := 1024) (W := 1915714) check rows elimOK (by decide) (by decide) cover4006 (by decide)
  decide +kernel

theorem h4006 : P.leaf 34 4006 = 1915714 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1915714)]) (.cons c4006_0 (.nil)) (by decide) (by decide))

theorem cover50239 : P.CoversSplit 24 10 50239 0xff00fa00c8000000ff00fa00c8000000f500f00040000000f500f000400000000000000000000000330032000000000000000000000000003100300000000000f000f000c0000000f000f000c0000000f000f00040000000f000f000400000000000000000000000200020000000000000000000000000002000200000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [517, 529, 572, 573, 858, 860, 867, 872, 915, 1202]) (ps := [(8, [580, 615], [524])]) (by decide +kernel)

theorem c50239_0 : P.sumLeaves 24 51444736 1001 = 6730222 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 50239) (lo := 0) (len := 1001) (W := 6730222) check rows elimOK (by decide) (by decide) cover50239 (by decide)
  decide +kernel

theorem c50239_1 : P.sumLeaves 24 51445737 23 = 3583838 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 50239) (lo := 1001) (len := 23) (W := 3583838) check rows elimOK (by decide) (by decide) cover50239 (by decide)
  decide +kernel

theorem h50239 : P.leaf 34 50239 = 10314060 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1001, 6730222), (23, 3583838)]) (.cons c50239_0 (.cons c50239_1 (.nil))) (by decide) (by decide))

theorem h4007 : P.leaf 34 4007 = 10314060 :=
  orient5 (v := 50239) (by decide) (by decide +kernel) h50239

theorem cover4008 : P.CoversSplit 24 10 4008 0x8800000080008000000000000000000088000000000000000000000000000000000000000000000000220000002000000000000000000000002200000000000088000000800080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 508, 515, 517, 522, 565, 915, 1202, 1258, 1308, 1609]) (by decide +kernel)

theorem h4008 : P.leaf 34 4008 = 228716 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 4008) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 4008) (weight := fun _ => 1) (xs := [463, 479, 507, 511, 561, 565, 661, 689, 693, 891, 895, 975, 991, 1019, 1023]) check rows elimOK (by decide) (by decide) cover4008 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover50255 : P.CoversSplit 24 10 50255 0xcc00c800c80080000000000000000000cc00c800c80080000000000000000000000000000000000000320032003200200000000000000000003200320032002080008000800080000000000000000000800080008000800000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 516, 522, 536, 572, 573, 858, 865, 872, 1202, 1609]) (by decide +kernel)

noncomputable def f50255 (i : ℕ) := rowWeight keep3 twice3 i * P.leaf 24 (51461120 + i)

theorem c50255_0 : rowSum f50255 0 1024 = 3331363 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 50255) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover50255 (by decide)
  decide +kernel

theorem sum50255 : rowSum f50255 0 1024 = 3331363 :=
  c50255_0

theorem h50255 : P.leaf 34 50255 = 3331363 :=
  leaf_weighted (k := 24) (d := 10) (H := 50255) (keep := keep3) (twice := twice3) rows (by decide) (by decide) (bal3) (invRow3 (H := 50255) (by decide) (by decide +kernel)) sum50255

theorem h4009 : P.leaf 34 4009 = 3331363 :=
  orient5 (v := 50255) (by decide) (by decide +kernel) h50255

theorem cover36291 : P.CoversSplit 24 10 36291 0xaa000000aa0000000000000000000000aa0000000000000000000000000000008800000088000000220000002200000088000000000000002200000000000000aa000000aa0000000000000000000000aa0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [466, 515, 516, 522, 858, 865, 1202, 1209, 1258, 1601]) (by decide +kernel)

theorem c36291_0 : P.sumLeaves 24 37161984 1024 = 1576708 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 36291) (lo := 0) (len := 1024) (W := 1576708) check rows elimOK (by decide) (by decide) cover36291 (by decide)
  decide +kernel

theorem h36291 : P.leaf 34 36291 = 1576708 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1576708)]) (.cons c36291_0 (.nil)) (by decide) (by decide))

theorem h4010 : P.leaf 34 4010 = 1576708 :=
  orient25 (v := 36291) (by decide) (by decide +kernel) h36291

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

theorem h4012 : P.leaf 34 4012 = 1118886 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 4012) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 4012) (weight := fun _ => 1) (xs := [463, 479, 507, 511, 561, 565, 645, 661, 689, 693, 891, 895, 975, 991, 1019, 1023]) check rows elimOK (by decide) (by decide) cover4012 (by decide) (by decide) (by decide +kernel)
  decide +kernel

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

theorem cover49839 : P.CoversSplit 24 10 49839 0xfffffffffa005000fffffffffa0050008c8c8c8c080000008c8c8c8c08000000f0c0f0c0f000500030003000300010008080808000000000000000000000000088aa88aa8800000088aa88aa88000000888888880800000088888888080000000080008000000000000000000000000000800080000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 517, 522, 524, 566, 573, 859, 872, 879, 915, 1202, 1601]) (by decide +kernel)

noncomputable def f49839 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (51035136 + i)

theorem c49839_0 : rowSum f49839 0 1015 = 14518307 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 49839) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover49839 (by decide)
  decide +kernel

theorem c49839_1 : rowSum f49839 1015 9 = 1853116 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 49839) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover49839 (by decide)
  decide +kernel

theorem sum49839 : rowSum f49839 0 1024 = 16371423 :=
  rowSum_append (F := f49839) (lo := 0) (n := 1015) (m := 9) (A := 14518307) (B := 1853116) c49839_0 (c49839_1)

theorem h49839 : P.leaf 34 49839 = 16371423 :=
  leaf_weighted (k := 24) (d := 10) (H := 49839) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 49839) (by decide) (by decide +kernel)) sum49839

theorem h4022 : P.leaf 34 4022 = 16371423 :=
  orient24 (v := 49839) (by decide) (by decide +kernel) h49839

theorem cover49855 : P.CoversSplit 24 10 49855 0xfffffffffa005000fffffffffa005000ffffffffc8004000ffffffffc8004000f0c0f0c0f00050003000300030001000f0c0f0c0c00040003000300000000000fffffffffa005000fffffffffa005000ffffffffc8004000ffffffffc8004000a080a080a00000002000200020000000a080a080000000002000200000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [517, 524, 566, 573, 867, 872, 1202, 1308, 1601]) (by decide +kernel)

noncomputable def f49855 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (51051520 + i)

theorem c49855_0 : rowSum f49855 0 462 = 8259054 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 49855) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover49855 (by decide)
  decide +kernel

theorem c49855_1 : rowSum f49855 462 561 = 36559007 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 49855) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover49855 (by decide)
  decide +kernel

theorem c49855_2 : rowSum f49855 1023 1 = 542484 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 49855) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover49855 (by decide)
  decide +kernel

theorem sum49855 : rowSum f49855 0 1024 = 45360545 :=
  rowSum_append (F := f49855) (lo := 0) (n := 462) (m := 562) (A := 8259054) (B := 37101491) c49855_0 (rowSum_append (F := f49855) (lo := 462) (n := 561) (m := 1) (A := 36559007) (B := 542484) c49855_1 (c49855_2))

theorem h49855 : P.leaf 34 49855 = 45360545 :=
  leaf_weighted (k := 24) (d := 10) (H := 49855) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 49855) (by decide) (by decide +kernel)) sum49855

theorem h4023 : P.leaf 34 4023 = 45360545 :=
  orient24 (v := 49855) (by decide) (by decide +kernel) h49855

theorem cover49871 : P.CoversSplit 24 10 49871 0xfffffffffa005000fffffffffa00500088888c8c0000000088888c8c00000000f0c0f0c0f0085000300030003000100080808080000000000000000000000000888888888800000088aa88aa88000000888888880000000088888889000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 516, 522, 536, 573, 859, 879, 915, 1202, 1601]) (by decide +kernel)

noncomputable def f49871 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (51067904 + i)

theorem c49871_0 : rowSum f49871 0 1024 = 29121330 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 49871) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover49871 (by decide)
  decide +kernel

theorem sum49871 : rowSum f49871 0 1024 = 29121330 :=
  c49871_0

theorem h49871 : P.leaf 34 49871 = 29121330 :=
  leaf_weighted (k := 24) (d := 10) (H := 49871) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 49871) (by decide) (by decide +kernel)) sum49871

theorem h4026 : P.leaf 34 4026 = 29121330 :=
  orient24 (v := 49871) (by decide) (by decide +kernel) h49871

theorem cover49887 : P.CoversSplit 24 10 49887 0xfffffffffa005000fffffffffa005000ffffffffc8004000ffffffffc8004000f0c0f0c0f00050003000300030001000f0c0f0c0c00040003000300000000000fffffffffa005000fffffffffa005000ffffffffc8004000ffffffffc8004000a080a080a00000002000200020000000a080a080000000002000200000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [516, 536, 573, 859, 867, 879, 915, 1202, 1601]) (ps := [(8, [615], [1266])]) (by decide +kernel)

noncomputable def f49887 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (51084288 + i)

theorem c49887_0 : rowSum f49887 0 462 = 16302432 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 49887) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover49887 (by decide)
  decide +kernel

theorem c49887_1 : rowSum f49887 462 561 = 64799396 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 49887) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover49887 (by decide)
  decide +kernel

theorem c49887_2 : rowSum f49887 1023 1 = 1077472 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 49887) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover49887 (by decide)
  decide +kernel

theorem sum49887 : rowSum f49887 0 1024 = 82179300 :=
  rowSum_append (F := f49887) (lo := 0) (n := 462) (m := 562) (A := 16302432) (B := 65876868) c49887_0 (rowSum_append (F := f49887) (lo := 462) (n := 561) (m := 1) (A := 64799396) (B := 1077472) c49887_1 (c49887_2))

theorem h49887 : P.leaf 34 49887 = 82179300 :=
  leaf_weighted (k := 24) (d := 10) (H := 49887) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 49887) (by decide) (by decide +kernel)) sum49887

theorem h4027 : P.leaf 34 4027 = 82179300 :=
  orient24 (v := 49887) (by decide) (by decide +kernel) h49887

theorem cover4070 : P.CoversSplit 24 10 4070 0xaaaa0000abab0a0a0000000000000000aaaa0000abab0a0a00220000002300000000000000220002000000000000000000000000002200020000000000000000aaaa0000abab0a0a0000000000000000aaaa0000aaaa0a0a00220000002200000000000000220002000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 515, 522, 524, 566, 915, 1217, 1258, 1609]) (by decide +kernel)

theorem c4070_0 : P.sumLeaves 24 4167680 1009 = 8879824 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 4070) (lo := 0) (len := 1009) (W := 8879824) check rows elimOK (by decide) (by decide) cover4070 (by decide)
  decide +kernel

theorem c4070_1 : P.sumLeaves 24 4168689 15 = 4447488 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 4070) (lo := 1009) (len := 15) (W := 4447488) check rows elimOK (by decide) (by decide) cover4070 (by decide)
  decide +kernel

theorem h4070 : P.leaf 34 4070 = 13327312 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1009, 8879824), (15, 4447488)]) (.cons c4070_0 (.cons c4070_1 (.nil))) (by decide) (by decide))

theorem h4028 : P.leaf 34 4028 = 13327312 :=
  orient4 (v := 4070) (by decide) (by decide +kernel) h4070

theorem cover4029 : P.CoversSplit 24 10 4029 0xff00ff00f500a000ff33ff33f531a020ff00ff00f500a000ff00ff00f500a0000000000000000000330033002000200000000000000000003300330020002000ff00ff00f500a000ff33ff33f531a020000000000000000000000000000000000000000000000000330033002000200000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 517, 915, 1202, 1209, 1217, 1308]) (ps := [(14, [923], [915])]) (by decide +kernel)

theorem c4029_0 : P.sumLeaves 24 4125696 798 = 9685769 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 4029) (lo := 0) (len := 798) (W := 9685769) check rows elimOK (by decide) (by decide) cover4029 (by decide)
  decide +kernel

theorem c4029_1 : P.sumLeaves 24 4126494 220 = 39072851 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 4029) (lo := 798) (len := 220) (W := 39072851) check rows elimOK (by decide) (by decide) cover4029 (by decide)
  decide +kernel

theorem c4029_2 : P.sumLeaves 24 4126714 6 = 11078512 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 4029) (lo := 1018) (len := 6) (W := 11078512) check rows elimOK (by decide) (by decide) cover4029 (by decide)
  decide +kernel

theorem h4029 : P.leaf 34 4029 = 59837132 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(798, 9685769), (220, 39072851), (6, 11078512)]) (.cons c4029_0 (.cons c4029_1 (.cons c4029_2 (.nil)))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(4004, 24), (4005, 24), (4006, 48), (4007, 48), (4008, 24), (4009, 24), (4010, 48), (4011, 48), (4012, 48), (4013, 48), (4014, 48), (4015, 48), (4022, 24), (4023, 24), (4026, 24), (4027, 24), (4028, 48), (4029, 48)]

theorem segOK : checkSeg 16 perms 4004 4030 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 4004 4030 672 12319865640 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 12319865640)
    (SegSum.cons (w := 24) h4004 (SegSum.cons (w := 24) h4005 (SegSum.cons (w := 48) h4006 (SegSum.cons (w := 48) h4007 (SegSum.cons (w := 24) h4008 (SegSum.cons (w := 24) h4009 (SegSum.cons (w := 48) h4010 (SegSum.cons (w := 48) h4011 (SegSum.cons (w := 48) h4012 (SegSum.cons (w := 48) h4013 (SegSum.cons (w := 48) h4014 (SegSum.cons (w := 48) h4015 (SegSum.cons (w := 24) h4022 (SegSum.cons (w := 24) h4023 (SegSum.cons (w := 24) h4026 (SegSum.cons (w := 24) h4027 (SegSum.cons (w := 48) h4028 (SegSum.cons (w := 48) h4029 (show SegSum (P.leaf 34) [] 0 from rfl))))))))))))))))))) (by decide)

end RACert.S4N1.C0.S22
