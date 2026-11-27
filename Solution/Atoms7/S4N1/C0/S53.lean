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

namespace RACert.S4N1.C0.S53

open RACert RACert.Problem

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

theorem cover7674 : P.CoversSplit 24 10 7674 0xf0f00000f0f50000f0f00000f0f50000f0f00000f0f50000f0f00000f0f50000c0f0000080800000c000000080000000c0f0000080800000c000000080000000f0f00000f0f50000f0f00000f0f50000f0f00000f0f00000f0f00000f0f00000c0f0000080800000c000000080000000c0c0000080800000c000000080000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 858, 865, 867, 909, 1210, 1217, 1258, 1601, 1609]) (by decide +kernel)

theorem c7674_0 : P.sumLeaves 24 7858176 631 = 6938592 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7674) (lo := 0) (len := 631) (W := 6938592) check rows elimOK (by decide) (by decide) cover7674 (by decide)
  decide +kernel

theorem c7674_1 : P.sumLeaves 24 7858807 393 = 24258336 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7674) (lo := 631) (len := 393) (W := 24258336) check rows elimOK (by decide) (by decide) cover7674 (by decide)
  decide +kernel

theorem h7674 : P.leaf 34 7674 = 31196928 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(631, 6938592), (393, 24258336)]) (.cons c7674_0 (.cons c7674_1 (.nil))) (by decide) (by decide))

theorem cover7675 : P.CoversSplit 24 10 7675 0xffff0000fffa0000ffff0000fffa0000ffff0000fffa0000ffff0000fffa0000ccfc000088880000cc00000088000000ccfc000088880000cc00000088000000ffff0000fffa0000ffff0000fffa0000ffff0000fafa0000ffff0000fafa0000ccfc000088880000cc00000088000000cccc000088880000cc00000088000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [858, 865, 867, 916, 1209, 1210, 1217, 1258, 1601, 1609]) (by decide +kernel)

theorem c7675_0 : P.sumLeaves 24 7859200 404 = 7147130 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7675) (lo := 0) (len := 404) (W := 7147130) check rows elimOK (by decide) (by decide) cover7675 (by decide)
  decide +kernel

theorem c7675_1 : P.sumLeaves 24 7859604 362 = 22711106 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7675) (lo := 404) (len := 362) (W := 22711106) check rows elimOK (by decide) (by decide) cover7675 (by decide)
  decide +kernel

theorem c7675_2 : P.sumLeaves 24 7859966 216 = 33797468 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7675) (lo := 766) (len := 216) (W := 33797468) check rows elimOK (by decide) (by decide) cover7675 (by decide)
  decide +kernel

theorem c7675_3 : P.sumLeaves 24 7860182 42 = 23982758 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7675) (lo := 982) (len := 42) (W := 23982758) check rows elimOK (by decide) (by decide) cover7675 (by decide)
  decide +kernel

theorem h7675 : P.leaf 34 7675 = 87638462 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(404, 7147130), (362, 22711106), (216, 33797468), (42, 23982758)]) (.cons c7675_0 (.cons c7675_1 (.cons c7675_2 (.cons c7675_3 (.nil))))) (by decide) (by decide))

theorem cover7676 : P.CoversSplit 24 10 7676 0xf0000000f000aa000000000000000000f0000000f0000a000000000000000000c000000080088808c0c0000080888888c000000080080808c0c0000080880808f0000000f000aa000000000000000000f0000000f0000a0000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 858, 865, 916, 1210, 1601]) (ps := [(11, [879, 909], [858])]) (by decide +kernel)

theorem c7676_0 : P.sumLeaves 24 7860224 1024 = 10966876 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7676) (lo := 0) (len := 1024) (W := 10966876) check rows elimOK (by decide) (by decide) cover7676 (by decide)
  decide +kernel

theorem h7676 : P.leaf 34 7676 = 10966876 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 10966876)]) (.cons c7676_0 (.nil)) (by decide) (by decide))

theorem cover7677 : P.CoversSplit 24 10 7677 0xff00ff00ff00a0000000000000000000ff00ff00ff00a0000000000000000000cc03cc03880080000000000000000000cc03cc03880080000000000000000000ff00ff00ff00a0000000000000000000ff00ff00fa00a00000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 858, 865, 916, 1209, 1210, 1217, 1601]) (by decide +kernel)

theorem c7677_0 : P.sumLeaves 24 7861248 878 = 24540802 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7677) (lo := 0) (len := 878) (W := 24540802) check rows elimOK (by decide) (by decide) cover7677 (by decide)
  decide +kernel

theorem c7677_1 : P.sumLeaves 24 7862126 146 = 31529962 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7677) (lo := 878) (len := 146) (W := 31529962) check rows elimOK (by decide) (by decide) cover7677 (by decide)
  decide +kernel

theorem h7677 : P.leaf 34 7677 = 56070764 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(878, 24540802), (146, 31529962)]) (.cons c7677_0 (.cons c7677_1 (.nil))) (by decide) (by decide))

theorem cover7678 : P.CoversSplit 24 10 7678 0xf0f00000f0f50000f0f00000f0f50000f0f00000f0f50000f0f00000f0f50000c0f0000080800000c000000080000000c0f0000080800000c000000080000000f0f00000f0f50000f0f00000f0f50000f0f00000f0f00000f0f00000f0f00000c0f0000080800000c000000080000000c0c0000080800000c000000080000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 858, 865, 1210, 1217, 1258, 1601, 1609]) (by decide +kernel)

theorem c7678_0 : P.sumLeaves 24 7862272 631 = 28433191 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7678) (lo := 0) (len := 631) (W := 28433191) check rows elimOK (by decide) (by decide) cover7678 (by decide)
  decide +kernel

theorem c7678_1 : P.sumLeaves 24 7862903 393 = 85464140 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7678) (lo := 631) (len := 393) (W := 85464140) check rows elimOK (by decide) (by decide) cover7678 (by decide)
  decide +kernel

theorem h7678 : P.leaf 34 7678 = 113897331 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(631, 28433191), (393, 85464140)]) (.cons c7678_0 (.cons c7678_1 (.nil))) (by decide) (by decide))

theorem cover7679 : P.CoversSplit 24 10 7679 0xfffffffffffaaaaafffffffffffaaaaafffffffffffaaaaafffffffffffaaaaaccfcccfc88888888cccccccc88888888ccfcccfc88888888cccccccc88888888fffffffffffaaaaafffffffffffaaaaafffffffffafaaaaafffffffffafaaaaaccfcccfc88888888cccccccc88888888cccccccc88888888cccccccc88888888 :=
  coversSplit check rows (by decide) (by decide) (xs := [858, 865, 1209, 1210, 1217, 1258, 1601, 1609]) (by decide +kernel)

theorem c7679_0 : P.sumLeaves 24 7863296 250 = 29142642 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7679) (lo := 0) (len := 250) (W := 29142642) check rows elimOK (by decide) (by decide) cover7679 (by decide)
  decide +kernel

theorem c7679_1 : P.sumLeaves 24 7863546 122 = 34287165 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7679) (lo := 250) (len := 122) (W := 34287165) check rows elimOK (by decide) (by decide) cover7679 (by decide)
  decide +kernel

theorem c7679_2 : P.sumLeaves 24 7863668 116 = 55890515 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7679) (lo := 372) (len := 116) (W := 55890515) check rows elimOK (by decide) (by decide) cover7679 (by decide)
  decide +kernel

theorem c7679_3 : P.sumLeaves 24 7863784 210 = 72749363 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7679) (lo := 488) (len := 210) (W := 72749363) check rows elimOK (by decide) (by decide) cover7679 (by decide)
  decide +kernel

theorem c7679_4 : P.sumLeaves 24 7863994 154 = 76623648 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7679) (lo := 698) (len := 154) (W := 76623648) check rows elimOK (by decide) (by decide) cover7679 (by decide)
  decide +kernel

theorem c7679_5 : P.sumLeaves 24 7864148 106 = 105984833 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7679) (lo := 852) (len := 106) (W := 105984833) check rows elimOK (by decide) (by decide) cover7679 (by decide)
  decide +kernel

theorem c7679_6 : P.sumLeaves 24 7864254 66 = 126679048 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7679) (lo := 958) (len := 66) (W := 126679048) check rows elimOK (by decide) (by decide) cover7679 (by decide)
  decide +kernel

theorem h7679 : P.leaf 34 7679 = 501357214 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(250, 29142642), (122, 34287165), (116, 55890515), (210, 72749363), (154, 76623648), (106, 105984833), (66, 126679048)]) (.cons c7679_0 (.cons c7679_1 (.cons c7679_2 (.cons c7679_3 (.cons c7679_4 (.cons c7679_5 (.cons c7679_6 (.nil)))))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(7672, 48), (7673, 48), (7674, 48), (7675, 48), (7676, 48), (7677, 48), (7678, 48), (7679, 48)]

theorem segOK : checkSeg 16 perms 7672 7924 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 7672 7924 384 39520821840 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 39520821840)
    (SegSum.cons (w := 48) h7672 (SegSum.cons (w := 48) h7673 (SegSum.cons (w := 48) h7674 (SegSum.cons (w := 48) h7675 (SegSum.cons (w := 48) h7676 (SegSum.cons (w := 48) h7677 (SegSum.cons (w := 48) h7678 (SegSum.cons (w := 48) h7679 (show SegSum (P.leaf 34) [] 0 from rfl))))))))) (by decide)

end RACert.S4N1.C0.S53
