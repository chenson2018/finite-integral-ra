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

namespace RACert.S4N1.C0.S105

open RACert RACert.Problem

theorem cover28655 : P.CoversSplit 24 10 28655 0xfffffffffafafafafffffffffafafafafffffffffafafafafffffffffafafafaffccffccfac8fac8ccccccccc8c8c8c8ffccffccfac8fac8ccccccccc8c8c8c8fffffffffafafafaffff0000fafa0000fffffffffafafafaffff0000fafa0000ffcc0000fac80000cccc0000c8c80000ffcc0000fac80000cccc0000c8c80000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 522, 1202, 1259, 1264, 1601]) (by decide +kernel)

theorem c28655_0 : P.sumLeaves 24 29342720 318 = 76827947 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28655) (lo := 0) (len := 318) (W := 76827947) check rows elimOK (by decide) (by decide) cover28655 (by decide)
  decide +kernel

theorem c28655_1 : P.sumLeaves 24 29343038 144 = 98817879 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28655) (lo := 318) (len := 144) (W := 98817879) check rows elimOK (by decide) (by decide) cover28655 (by decide)
  decide +kernel

theorem c28655_2 : P.sumLeaves 24 29343182 154 = 119300147 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28655) (lo := 462) (len := 154) (W := 119300147) check rows elimOK (by decide) (by decide) cover28655 (by decide)
  decide +kernel

theorem c28655_3 : P.sumLeaves 24 29343336 161 = 161837311 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28655) (lo := 616) (len := 161) (W := 161837311) check rows elimOK (by decide) (by decide) cover28655 (by decide)
  decide +kernel

theorem c28655_4 : P.sumLeaves 24 29343497 109 = 128934080 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28655) (lo := 777) (len := 109) (W := 128934080) check rows elimOK (by decide) (by decide) cover28655 (by decide)
  decide +kernel

theorem c28655_5 : P.sumLeaves 24 29343606 112 = 219507963 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28655) (lo := 886) (len := 112) (W := 219507963) check rows elimOK (by decide) (by decide) cover28655 (by decide)
  decide +kernel

theorem c28655_6 : P.sumLeaves 24 29343718 26 = 109075038 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28655) (lo := 998) (len := 26) (W := 109075038) check rows elimOK (by decide) (by decide) cover28655 (by decide)
  decide +kernel

theorem h28655 : P.leaf 34 28655 = 914300365 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(318, 76827947), (144, 98817879), (154, 119300147), (161, 161837311), (109, 128934080), (112, 219507963), (26, 109075038)]) (.cons c28655_0 (.cons c28655_1 (.cons c28655_2 (.cons c28655_3 (.cons c28655_4 (.cons c28655_5 (.cons c28655_6 (.nil)))))))) (by decide) (by decide))

theorem cover28670 : P.CoversSplit 24 10 28670 0xfffffffffafafafafffffffffafafafafffffffffafafafafffffffffafafafaffccffccfac8fac8ccccccccc8c8c8c8ffccffccfac8fac8ccccccccc8c8c8c8fffffffffafafafafffffffffafafafafffffffffafafafafffffffffafafafaffccffccfac8fac8ccccccccc8c8c8c8ffccffccfac8fac8ccccccccc8c8c8c8 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 915, 1202, 1259, 1601]) (by decide +kernel)

theorem c28670_0 : P.sumLeaves 24 29358080 190 = 32988844 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28670) (lo := 0) (len := 190) (W := 32988844) check rows elimOK (by decide) (by decide) cover28670 (by decide)
  decide +kernel

theorem c28670_1 : P.sumLeaves 24 29358270 126 = 68453358 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28670) (lo := 190) (len := 126) (W := 68453358) check rows elimOK (by decide) (by decide) cover28670 (by decide)
  decide +kernel

theorem c28670_2 : P.sumLeaves 24 29358396 112 = 100443671 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28670) (lo := 316) (len := 112) (W := 100443671) check rows elimOK (by decide) (by decide) cover28670 (by decide)
  decide +kernel

theorem c28670_3 : P.sumLeaves 24 29358508 134 = 174272501 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28670) (lo := 428) (len := 134) (W := 174272501) check rows elimOK (by decide) (by decide) cover28670 (by decide)
  decide +kernel

theorem c28670_4 : P.sumLeaves 24 29358642 176 = 137441744 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28670) (lo := 562) (len := 176) (W := 137441744) check rows elimOK (by decide) (by decide) cover28670 (by decide)
  decide +kernel

theorem c28670_5 : P.sumLeaves 24 29358818 116 = 158229870 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28670) (lo := 738) (len := 116) (W := 158229870) check rows elimOK (by decide) (by decide) cover28670 (by decide)
  decide +kernel

theorem c28670_6 : P.sumLeaves 24 29358934 107 = 261849336 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28670) (lo := 854) (len := 107) (W := 261849336) check rows elimOK (by decide) (by decide) cover28670 (by decide)
  decide +kernel

theorem c28670_7 : P.sumLeaves 24 29359041 63 = 206737142 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28670) (lo := 961) (len := 63) (W := 206737142) check rows elimOK (by decide) (by decide) cover28670 (by decide)
  decide +kernel

theorem h28670 : P.leaf 34 28670 = 1140416466 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(190, 32988844), (126, 68453358), (112, 100443671), (134, 174272501), (176, 137441744), (116, 158229870), (107, 261849336), (63, 206737142)]) (.cons c28670_0 (.cons c28670_1 (.cons c28670_2 (.cons c28670_3 (.cons c28670_4 (.cons c28670_5 (.cons c28670_6 (.cons c28670_7 (.nil))))))))) (by decide) (by decide))

theorem cover28671 : P.CoversSplit 24 10 28671 0xfffffffffafafafafffffffffafafafafffffffffafafafafffffffffafafafaffccffccfac8fac8ccccccccc8c8c8c8ffccffccfac8fac8ccccccccc8c8c8c8fffffffffafafafafffffffffafafafafffffffffafafafafffffffffafafafaffccffccfac8fac8ccccccccc8c8c8c8ffccffccfac8fac8ccccccccc8c8c8c8 :=
  coversSplit check rows (by decide) (by decide) (xs := [915, 1202, 1210, 1259, 1601]) (by decide +kernel)

theorem c28671_0 : P.sumLeaves 24 29359104 190 = 89603930 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28671) (lo := 0) (len := 190) (W := 89603930) check rows elimOK (by decide) (by decide) cover28671 (by decide)
  decide +kernel

theorem c28671_1 : P.sumLeaves 24 29359294 126 = 134804478 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28671) (lo := 190) (len := 126) (W := 134804478) check rows elimOK (by decide) (by decide) cover28671 (by decide)
  decide +kernel

theorem c28671_2 : P.sumLeaves 24 29359420 112 = 145105171 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28671) (lo := 316) (len := 112) (W := 145105171) check rows elimOK (by decide) (by decide) cover28671 (by decide)
  decide +kernel

theorem c28671_3 : P.sumLeaves 24 29359532 134 = 245659138 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28671) (lo := 428) (len := 134) (W := 245659138) check rows elimOK (by decide) (by decide) cover28671 (by decide)
  decide +kernel

theorem c28671_4 : P.sumLeaves 24 29359666 176 = 243129609 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28671) (lo := 562) (len := 176) (W := 243129609) check rows elimOK (by decide) (by decide) cover28671 (by decide)
  decide +kernel

theorem c28671_5 : P.sumLeaves 24 29359842 116 = 253268209 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28671) (lo := 738) (len := 116) (W := 253268209) check rows elimOK (by decide) (by decide) cover28671 (by decide)
  decide +kernel

theorem c28671_6 : P.sumLeaves 24 29359958 107 = 357242669 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28671) (lo := 854) (len := 107) (W := 357242669) check rows elimOK (by decide) (by decide) cover28671 (by decide)
  decide +kernel

theorem c28671_7 : P.sumLeaves 24 29360065 63 = 277570226 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28671) (lo := 961) (len := 63) (W := 277570226) check rows elimOK (by decide) (by decide) cover28671 (by decide)
  decide +kernel

theorem h28671 : P.leaf 34 28671 = 1746383430 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(190, 89603930), (126, 134804478), (112, 145105171), (134, 245659138), (176, 243129609), (116, 253268209), (107, 357242669), (63, 277570226)]) (.cons c28671_0 (.cons c28671_1 (.cons c28671_2 (.cons c28671_3 (.cons c28671_4 (.cons c28671_5 (.cons c28671_6 (.cons c28671_7 (.nil))))))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(28655, 48), (28670, 24), (28671, 24)]

theorem segOK : checkSeg 16 perms 28655 32228 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 28655 32228 96 113169615024 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 113169615024)
    (SegSum.cons (w := 48) h28655 (SegSum.cons (w := 24) h28670 (SegSum.cons (w := 24) h28671 (show SegSum (P.leaf 34) [] 0 from rfl)))) (by decide)

end RACert.S4N1.C0.S105
