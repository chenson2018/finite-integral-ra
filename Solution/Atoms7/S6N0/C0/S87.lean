/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Atoms7.S6N0.C0.Defs

/-! Generated certificate for the identity on six symmetric diversity atoms. -/

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option Elab.async false

@[expose] public section

namespace RACert.S6N0.C0.S87

open RACert RACert.Problem

theorem cover98297 : P.CoversSplit 26 10 98297 0xf0f0f0f0f0f0f0f0f0f0f0f5f0f0f0f0f0f0f0f0f0f0f0c0f0f0f0f0f0c0f0c00000000000000000000050500000505000000000000000000000505000005040f0f0f0f0f0f0f0f0f0f0f0f5f0f0f0f0f0f0f0f0f000f000f0f0f0f0f000f0000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c98297_0 : P.sumLeaves 26 100656128 478 = 145318368 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98297) (lo := 0) (len := 478) (W := 145318368) check rows elimOK (by decide) (by decide) cover98297 (by decide)
  decide +kernel

theorem c98297_1 : P.sumLeaves 26 100656606 431 = 276486063 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98297) (lo := 478) (len := 431) (W := 276486063) check rows elimOK (by decide) (by decide) cover98297 (by decide)
  decide +kernel

theorem c98297_2 : P.sumLeaves 26 100657037 115 = 449897586 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98297) (lo := 909) (len := 115) (W := 449897586) check rows elimOK (by decide) (by decide) cover98297 (by decide)
  decide +kernel

theorem h98297 : P.leaf 36 98297 = 871702017 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(478, 145318368), (431, 276486063), (115, 449897586)]) (.cons c98297_0 (.cons c98297_1 (.cons c98297_2 (.nil)))) (by decide) (by decide))

theorem cover98299 : P.CoversSplit 26 10 98299 0xf0f0f0f0f0f0f0f0f0f0f0f5f0f0f0f0f0f0f0f0f0f0f0c0f0f0f0f0f0c0f0c00000000000000000000050500000505000000000000000000000505000005040f0f0f0f0f0f0f0f0f0f0f0f5f0f0f0f0f0f0f0f0f000f000f0f0f0f0f000f0000000000000000000000050500000505000000000000000000000505000005000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c98299_0 : P.sumLeaves 26 100658176 452 = 203527056 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98299) (lo := 0) (len := 452) (W := 203527056) check rows elimOK (by decide) (by decide) cover98299 (by decide)
  decide +kernel

theorem c98299_1 : P.sumLeaves 26 100658628 427 = 437473183 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98299) (lo := 452) (len := 427) (W := 437473183) check rows elimOK (by decide) (by decide) cover98299 (by decide)
  decide +kernel

theorem c98299_2 : P.sumLeaves 26 100659055 145 = 733277072 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98299) (lo := 879) (len := 145) (W := 733277072) check rows elimOK (by decide) (by decide) cover98299 (by decide)
  decide +kernel

theorem h98299 : P.leaf 36 98299 = 1374277311 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(452, 203527056), (427, 437473183), (145, 733277072)]) (.cons c98299_0 (.cons c98299_1 (.cons c98299_2 (.nil)))) (by decide) (by decide))

theorem cover98300 : P.CoversSplit 26 10 98300 0xfffffffffffffafafffffffafffffafafffffffffffcfac8fafafafafac8fac8fffffafafffffafafafafafafafafafafffffafafffcfac8fafafafafac8fac8fffffffffffffafafffffffafffffafaffffffffffccfac8fafafafafac8fac80000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [874, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c98300_0 : P.sumLeaves 26 100659200 387 = 114398653 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98300) (lo := 0) (len := 387) (W := 114398653) check rows elimOK (by decide) (by decide) cover98300 (by decide)
  decide +kernel

theorem c98300_1 : P.sumLeaves 26 100659587 104 = 260407985 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98300) (lo := 387) (len := 104) (W := 260407985) check rows elimOK (by decide) (by decide) cover98300 (by decide)
  decide +kernel

theorem c98300_2 : P.sumLeaves 26 100659691 131 = 230505854 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98300) (lo := 491) (len := 131) (W := 230505854) check rows elimOK (by decide) (by decide) cover98300 (by decide)
  decide +kernel

theorem c98300_3 : P.sumLeaves 26 100659822 118 = 256447996 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98300) (lo := 622) (len := 118) (W := 256447996) check rows elimOK (by decide) (by decide) cover98300 (by decide)
  decide +kernel

theorem c98300_4 : P.sumLeaves 26 100659940 129 = 348780362 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98300) (lo := 740) (len := 129) (W := 348780362) check rows elimOK (by decide) (by decide) cover98300 (by decide)
  decide +kernel

theorem c98300_5 : P.sumLeaves 26 100660069 106 = 588064406 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98300) (lo := 869) (len := 106) (W := 588064406) check rows elimOK (by decide) (by decide) cover98300 (by decide)
  decide +kernel

theorem c98300_6 : P.sumLeaves 26 100660175 49 = 475675216 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98300) (lo := 975) (len := 49) (W := 475675216) check rows elimOK (by decide) (by decide) cover98300 (by decide)
  decide +kernel

theorem h98300 : P.leaf 36 98300 = 2274280472 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(387, 114398653), (104, 260407985), (131, 230505854), (118, 256447996), (129, 348780362), (106, 588064406), (49, 475675216)]) (.cons c98300_0 (.cons c98300_1 (.cons c98300_2 (.cons c98300_3 (.cons c98300_4 (.cons c98300_5 (.cons c98300_6 (.nil)))))))) (by decide) (by decide))

theorem cover98301 : P.CoversSplit 26 10 98301 0xfffffffffffffafafffffffafffffafafffffffffffcfac8fafafafafac8fac8fffffafafffffafafafafafafafafafafffffafafffcfac8fafafafafac8fac8fffffffffffffafafffffffafffffafaffffffffffccfac8fafafafafac8fac80000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c98301_0 : P.sumLeaves 26 100660224 387 = 220499446 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98301) (lo := 0) (len := 387) (W := 220499446) check rows elimOK (by decide) (by decide) cover98301 (by decide)
  decide +kernel

theorem c98301_1 : P.sumLeaves 26 100660611 104 = 481966487 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98301) (lo := 387) (len := 104) (W := 481966487) check rows elimOK (by decide) (by decide) cover98301 (by decide)
  decide +kernel

theorem c98301_2 : P.sumLeaves 26 100660715 131 = 392221131 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98301) (lo := 491) (len := 131) (W := 392221131) check rows elimOK (by decide) (by decide) cover98301 (by decide)
  decide +kernel

theorem c98301_3 : P.sumLeaves 26 100660846 118 = 502600926 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98301) (lo := 622) (len := 118) (W := 502600926) check rows elimOK (by decide) (by decide) cover98301 (by decide)
  decide +kernel

theorem c98301_4 : P.sumLeaves 26 100660964 129 = 578575690 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98301) (lo := 740) (len := 129) (W := 578575690) check rows elimOK (by decide) (by decide) cover98301 (by decide)
  decide +kernel

theorem c98301_5 : P.sumLeaves 26 100661093 106 = 984023096 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98301) (lo := 869) (len := 106) (W := 984023096) check rows elimOK (by decide) (by decide) cover98301 (by decide)
  decide +kernel

theorem c98301_6 : P.sumLeaves 26 100661199 49 = 726298394 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98301) (lo := 975) (len := 49) (W := 726298394) check rows elimOK (by decide) (by decide) cover98301 (by decide)
  decide +kernel

theorem h98301 : P.leaf 36 98301 = 3886185170 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(387, 220499446), (104, 481966487), (131, 392221131), (118, 502600926), (129, 578575690), (106, 984023096), (49, 726298394)]) (.cons c98301_0 (.cons c98301_1 (.cons c98301_2 (.cons c98301_3 (.cons c98301_4 (.cons c98301_5 (.cons c98301_6 (.nil)))))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(98297, 720), (98299, 360), (98300, 360), (98301, 720)]

theorem segOK : checkSeg 20 perms 98297 98303 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 98297 98303 2160 4739159576520 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 4739159576520)
    (SegSum.cons (w := 720) h98297 (SegSum.cons (w := 360) h98299 (SegSum.cons (w := 360) h98300 (SegSum.cons (w := 720) h98301 (show SegSum (P.leaf 36) [] 0 from rfl))))) (by decide)

end RACert.S6N0.C0.S87
