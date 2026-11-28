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

namespace RACert.S4N1.C0.S46

open RACert RACert.Problem

theorem cover7661 : P.CoversSplit 24 10 7661 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 466, 473, 515, 522, 858, 865, 916, 1209, 1258, 1266]) (by decide +kernel)

theorem h7661 : P.leaf 34 7661 = 2088228 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 7661) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 7661) (weight := fun _ => 1) (xs := [511, 592, 720, 895, 1023]) check rows elimOK (by decide) (by decide) cover7661 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover7662 : P.CoversSplit 24 10 7662 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 465, 466, 515, 522, 858, 865, 1209, 1217, 1258, 1266]) (by decide +kernel)

theorem h7662 : P.leaf 34 7662 = 3697640 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 7662) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 7662) (weight := fun _ => 1) (xs := [208, 511, 592, 720, 895, 1023]) check rows elimOK (by decide) (by decide) cover7662 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover7663 : P.CoversSplit 24 10 7663 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 515, 522, 858, 865, 867, 916, 1209, 1217, 1258, 1266]) (by decide +kernel)

theorem h7663 : P.leaf 34 7663 = 5594693 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 7663) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 7663) (weight := fun _ => 1) (xs := [208, 511, 592, 720, 895, 1023]) check rows elimOK (by decide) (by decide) cover7663 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover19855 : P.CoversSplit 24 10 19855 0xaa000000a0000a000000000000000000aa0000000000000000000000000000008800000080000800220000002000020088000000000000002200000000000000aa000000a0000a000000000000000000aa0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 516, 522, 865, 1202, 1210, 1259, 1601]) (by decide +kernel)

noncomputable def f19855 (i : ℕ) := rowWeight keep5 twice5 i * P.leaf 24 (20331520 + i)

theorem c19855_0 : rowSum f19855 0 1024 = 5905713 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 19855) (keep := keep5) (twice := twice5) check rows elimOK (by decide) (by decide) cover19855 (by decide)
  decide +kernel

theorem sum19855 : rowSum f19855 0 1024 = 5905713 :=
  c19855_0

theorem h19855 : P.leaf 34 19855 = 5905713 :=
  leaf_weighted (k := 24) (d := 10) (H := 19855) (keep := keep5) (twice := twice5) rows (by decide) (by decide) (bal5) (invRow5 (H := 19855) (by decide) (by decide +kernel)) sum19855

theorem h7665 : P.leaf 34 7665 = 5905713 :=
  orient4 (v := 19855) (by decide) (by decide +kernel) h19855

theorem cover51599 : P.CoversSplit 24 10 51599 0xaa000000000000000000000000000000a0000000000000000000000000000000aa000000000000002200000000000000a0000000000000002000000000000000aa000000000000000000000000000000a0000000000000000000000000000000aa000000000000002200000000000000a0000000000000002000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 516, 517, 522, 528, 859, 865, 879]) (by decide +kernel)

theorem h51599 : P.leaf 34 51599 = 8238958 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 51599) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 51599) (weight := fun _ => 1) (xs := [61, 125, 127, 185, 189, 249, 251, 253, 255, 381, 383, 505, 507, 509, 511, 573, 637, 639, 697, 701, 761, 763, 765, 767, 893, 895, 1017, 1019, 1021, 1023]) check rows elimOK (by decide) (by decide) cover51599 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h7666 : P.leaf 34 7666 = 8238958 :=
  orient24 (v := 51599) (by decide) (by decide +kernel) h51599

theorem cover51615 : P.CoversSplit 24 10 51615 0xff00fa00fa000a00ff00fa00fa000a00f500f00055000000f500f00055000000ff00fa00fa000a00ff00fa00fa000a00f500f00045000000f500f00045000000ff00fa00fa000a00ff00fa00fa000a00f500f00050000000f500f00050000000ff00fa00fa000a00ff00fa00fa000a00f400f00040000000f400f00040000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [516, 858, 859, 865, 879, 1202, 1217]) (ps := [(12, [915], [859]), (14, [1609], [859])]) (by decide +kernel)

theorem c51615_0 : P.sumLeaves 24 52853760 425 = 7311495 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 51615) (lo := 0) (len := 425) (W := 7311495) check rows elimOK (by decide) (by decide) cover51615 (by decide)
  decide +kernel

theorem c51615_1 : P.sumLeaves 24 52854185 325 = 20676245 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 51615) (lo := 425) (len := 325) (W := 20676245) check rows elimOK (by decide) (by decide) cover51615 (by decide)
  decide +kernel

theorem c51615_2 : P.sumLeaves 24 52854510 274 = 32233260 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 51615) (lo := 750) (len := 274) (W := 32233260) check rows elimOK (by decide) (by decide) cover51615 (by decide)
  decide +kernel

theorem h51615 : P.leaf 34 51615 = 60221000 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(425, 7311495), (325, 20676245), (274, 32233260)]) (.cons c51615_0 (.cons c51615_1 (.cons c51615_2 (.nil)))) (by decide) (by decide))

theorem h7667 : P.leaf 34 7667 = 60221000 :=
  orient24 (v := 51615) (by decide) (by decide +kernel) h51615

theorem cover19886 : P.CoversSplit 24 10 19886 0xaa000000aa0000000000000000000000aa0000000000000000000000000000008808000088080000888800008888000088080000000000008888000000000000aa000000aa0000000000000000000000aa0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 515, 517, 522, 858, 865, 1202, 1259, 1601]) (by decide +kernel)

theorem c19886_0 : P.sumLeaves 24 20363264 1024 = 3803616 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 19886) (lo := 0) (len := 1024) (W := 3803616) check rows elimOK (by decide) (by decide) cover19886 (by decide)
  decide +kernel

theorem h19886 : P.leaf 34 19886 = 3803616 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 3803616)]) (.cons c19886_0 (.nil)) (by decide) (by decide))

theorem h7668 : P.leaf 34 7668 = 3803616 :=
  orient4 (v := 19886) (by decide) (by decide +kernel) h19886

theorem cover19887 : P.CoversSplit 24 10 19887 0xaa000000aa0000000000000000000000aa0000000000000000000000000000008800000088000000220000002200000088000000000000002200000000000000aa000000aa0000000000000000000000aa0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 517, 522, 858, 865, 1202, 1210, 1259, 1601]) (by decide +kernel)

theorem c19887_0 : P.sumLeaves 24 20364288 1024 = 20315744 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 19887) (lo := 0) (len := 1024) (W := 20315744) check rows elimOK (by decide) (by decide) cover19887 (by decide)
  decide +kernel

theorem h19887 : P.leaf 34 19887 = 20315744 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 20315744)]) (.cons c19887_0 (.nil)) (by decide) (by decide))

theorem h7669 : P.leaf 34 7669 = 20315744 :=
  orient4 (v := 19887) (by decide) (by decide +kernel) h19887

theorem cover7670 : P.CoversSplit 24 10 7670 0xf0f00000f0f50000f0f00000f0f50000f0f00000f0f50000f0f00000f0f50000c0f0000080800000c000000080000000c0f0000080800000c000000080000000f0f00000f0f50000f0f00000f0f50000f0f00000f0f00000f0f00000f0f00000c0f0000080800000c000000080000000c0c0000080800000c000000080000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 858, 865, 866, 908, 1210, 1217, 1258, 1601, 1609]) (by decide +kernel)

theorem c7670_0 : P.sumLeaves 24 7854080 631 = 12518611 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7670) (lo := 0) (len := 631) (W := 12518611) check rows elimOK (by decide) (by decide) cover7670 (by decide)
  decide +kernel

theorem c7670_1 : P.sumLeaves 24 7854711 393 = 45712807 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7670) (lo := 631) (len := 393) (W := 45712807) check rows elimOK (by decide) (by decide) cover7670 (by decide)
  decide +kernel

theorem h7670 : P.leaf 34 7670 = 58231418 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(631, 12518611), (393, 45712807)]) (.cons c7670_0 (.cons c7670_1 (.nil))) (by decide) (by decide))

theorem cover19903 : P.CoversSplit 24 10 19903 0xfffafafafafaa0a0fffafafafafaa0a0fffafafafafaa0a0fffa000000000000ccc8c8c888888080ffc8fac8aa88a080ccc8c8c888888080ffc8000000000000fffafafafafaa0a0fffafafafafaa0a0fffafafafafaa0a0fffa000000000000ccc8c8c888888080ffc8fac8aa88a08000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [517, 858, 865, 1202, 1210, 1251, 1259, 1308, 1601]) (by decide +kernel)

theorem c19903_0 : P.sumLeaves 24 20380672 376 = 14518574 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 19903) (lo := 0) (len := 376) (W := 14518574) check rows elimOK (by decide) (by decide) cover19903 (by decide)
  decide +kernel

theorem c19903_1 : P.sumLeaves 24 20381048 193 = 43174720 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 19903) (lo := 376) (len := 193) (W := 43174720) check rows elimOK (by decide) (by decide) cover19903 (by decide)
  decide +kernel

theorem c19903_2 : P.sumLeaves 24 20381241 285 = 38902531 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 19903) (lo := 569) (len := 285) (W := 38902531) check rows elimOK (by decide) (by decide) cover19903 (by decide)
  decide +kernel

theorem c19903_3 : P.sumLeaves 24 20381526 144 = 85370220 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 19903) (lo := 854) (len := 144) (W := 85370220) check rows elimOK (by decide) (by decide) cover19903 (by decide)
  decide +kernel

theorem c19903_4 : P.sumLeaves 24 20381670 26 = 43667684 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 19903) (lo := 998) (len := 26) (W := 43667684) check rows elimOK (by decide) (by decide) cover19903 (by decide)
  decide +kernel

theorem h19903 : P.leaf 34 19903 = 225633729 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(376, 14518574), (193, 43174720), (285, 38902531), (144, 85370220), (26, 43667684)]) (.cons c19903_0 (.cons c19903_1 (.cons c19903_2 (.cons c19903_3 (.cons c19903_4 (.nil)))))) (by decide) (by decide))

theorem h7671 : P.leaf 34 7671 = 225633729 :=
  orient4 (v := 19903) (by decide) (by decide +kernel) h19903

theorem cover7672 : P.CoversSplit 24 10 7672 0xf0000000f00000000000000000000000f0000000f00000000000000000000000c000000080080000c000000080000000c000000080080000c000000080000000f0000000f00000000000000000000000f0000000f000aa0000000000000000000000000000000000c0c00000808800000000000000000000c0c0000080888888 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 858, 865, 867, 909, 916, 1210, 1601]) (by decide +kernel)

theorem c7672_0 : P.sumLeaves 24 7856128 1024 = 3891760 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7672) (lo := 0) (len := 1024) (W := 3891760) check rows elimOK (by decide) (by decide) cover7672 (by decide)
  decide +kernel

theorem h7672 : P.leaf 34 7672 = 3891760 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 3891760)]) (.cons c7672_0 (.nil)) (by decide) (by decide))

theorem cover7673 : P.CoversSplit 24 10 7673 0xff000000ff0000000000000000000000ff000000ff0000000000000000000000cc030000880000000000000000000000cc030000880000000000000000000000ff000000ff0000000000000000000000ff000000fa00000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 858, 865, 867, 916, 1209, 1210, 1217, 1601]) (by decide +kernel)

theorem c7673_0 : P.sumLeaves 24 7857152 1024 = 18331120 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7673) (lo := 0) (len := 1024) (W := 18331120) check rows elimOK (by decide) (by decide) cover7673 (by decide)
  decide +kernel

theorem h7673 : P.leaf 34 7673 = 18331120 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 18331120)]) (.cons c7673_0 (.nil)) (by decide) (by decide))

theorem cover51663 : P.CoversSplit 24 10 51663 0xff00fa00fa0000000000000000000000a000a000000000000000000000000000ff00fa00fa0000003300320032000000a000a000000000002000200000000000ff00fa00fa0000000000000000000000a000a000000000000000000000000000ff00fa00fa0000003300320032000000a000a000000000002000200000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 516, 522, 858, 859, 865, 879, 1202]) (by decide +kernel)

theorem c51663_0 : P.sumLeaves 24 52902912 877 = 18752222 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 51663) (lo := 0) (len := 877) (W := 18752222) check rows elimOK (by decide) (by decide) cover51663 (by decide)
  decide +kernel

theorem c51663_1 : P.sumLeaves 24 52903789 147 = 12444706 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 51663) (lo := 877) (len := 147) (W := 12444706) check rows elimOK (by decide) (by decide) cover51663 (by decide)
  decide +kernel

theorem h51663 : P.leaf 34 51663 = 31196928 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(877, 18752222), (147, 12444706)]) (.cons c51663_0 (.cons c51663_1 (.nil))) (by decide) (by decide))

theorem h7674 : P.leaf 34 7674 = 31196928 :=
  orient24 (v := 51663) (by decide) (by decide +kernel) h51663

theorem cover51679 : P.CoversSplit 24 10 51679 0xff00fa00fa000000ff00fa00fa000000f500f00055000000f500f00055000000ff00fa00fa000000ff00fa00fa000000f500f00045000000f500f00045000000ff00fa00fa000000ff00fa00fa000000f500f00050000000f500f00050000000ff00fa00fa000000ff00fa00fa000000f400f00000000000f400f00000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [516, 858, 859, 865, 879, 1202, 1217, 1308]) (ps := [(12, [915], [859]), (14, [1609], [859])]) (by decide +kernel)

theorem c51679_0 : P.sumLeaves 24 52919296 442 = 13407186 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 51679) (lo := 0) (len := 442) (W := 13407186) check rows elimOK (by decide) (by decide) cover51679 (by decide)
  decide +kernel

theorem c51679_1 : P.sumLeaves 24 52919738 370 = 33755557 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 51679) (lo := 442) (len := 370) (W := 33755557) check rows elimOK (by decide) (by decide) cover51679 (by decide)
  decide +kernel

theorem c51679_2 : P.sumLeaves 24 52920108 212 = 40475719 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 51679) (lo := 812) (len := 212) (W := 40475719) check rows elimOK (by decide) (by decide) cover51679 (by decide)
  decide +kernel

theorem h51679 : P.leaf 34 51679 = 87638462 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(442, 13407186), (370, 33755557), (212, 40475719)]) (.cons c51679_0 (.cons c51679_1 (.cons c51679_2 (.nil)))) (by decide) (by decide))

theorem h7675 : P.leaf 34 7675 = 87638462 :=
  orient24 (v := 51679) (by decide) (by decide +kernel) h51679

def seg : List (ℕ × ℕ) := [(7661, 48), (7662, 48), (7663, 48), (7665, 24), (7666, 48), (7667, 48), (7668, 48), (7669, 48), (7670, 48), (7671, 48), (7672, 48), (7673, 48), (7674, 48), (7675, 48)]

theorem segOK : checkSeg 16 perms 7661 7676 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 7661 7676 648 25528135320 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 25528135320)
    (SegSum.cons (w := 48) h7661 (SegSum.cons (w := 48) h7662 (SegSum.cons (w := 48) h7663 (SegSum.cons (w := 24) h7665 (SegSum.cons (w := 48) h7666 (SegSum.cons (w := 48) h7667 (SegSum.cons (w := 48) h7668 (SegSum.cons (w := 48) h7669 (SegSum.cons (w := 48) h7670 (SegSum.cons (w := 48) h7671 (SegSum.cons (w := 48) h7672 (SegSum.cons (w := 48) h7673 (SegSum.cons (w := 48) h7674 (SegSum.cons (w := 48) h7675 (show SegSum (P.leaf 34) [] 0 from rfl))))))))))))))) (by decide)

end RACert.S4N1.C0.S46
