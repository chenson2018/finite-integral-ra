/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Atoms7.S6N0.C0.Actions

/-! Generated identity-class certificate for the product-row count. -/

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option Elab.async false

@[expose] public section

namespace RACert.S6N0.C0.S90

open RACert RACert.Problem

theorem cover122871 : P.CoversSplit 26 10 122871 0xfffffffffffffafafffffffffffffafafffffffffffffac8fafafafac8c8c8c8fffffafafffffafafafafafafafafafafffffafafffffac8fafafafac8c8c8c8fffffffffffffafafffffffffffffafaffffffffccccc8c8fafafafac8c8c8c8fffffafafffffafafafafafafafafafafffffafaccccc8c8fafafafac8c8c8c8 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 922, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c122871_0 : P.sumLeaves 26 125819904 153 = 168306711 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122871) (lo := 0) (len := 153) (W := 168306711) check rows elimOK (by decide) (by decide) cover122871 (by decide)
  decide +kernel

theorem c122871_1 : P.sumLeaves 26 125820057 133 = 217649974 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122871) (lo := 153) (len := 133) (W := 217649974) check rows elimOK (by decide) (by decide) cover122871 (by decide)
  decide +kernel

theorem c122871_2 : P.sumLeaves 26 125820190 126 = 496360597 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122871) (lo := 286) (len := 126) (W := 496360597) check rows elimOK (by decide) (by decide) cover122871 (by decide)
  decide +kernel

theorem c122871_3 : P.sumLeaves 26 125820316 103 = 794334826 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122871) (lo := 412) (len := 103) (W := 794334826) check rows elimOK (by decide) (by decide) cover122871 (by decide)
  decide +kernel

theorem c122871_4 : P.sumLeaves 26 125820419 136 = 432181726 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122871) (lo := 515) (len := 136) (W := 432181726) check rows elimOK (by decide) (by decide) cover122871 (by decide)
  decide +kernel

theorem c122871_5 : P.sumLeaves 26 125820555 116 = 637255952 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122871) (lo := 651) (len := 116) (W := 637255952) check rows elimOK (by decide) (by decide) cover122871 (by decide)
  decide +kernel

theorem c122871_6 : P.sumLeaves 26 125820671 133 = 696558290 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122871) (lo := 767) (len := 133) (W := 696558290) check rows elimOK (by decide) (by decide) cover122871 (by decide)
  decide +kernel

theorem c122871_7 : P.sumLeaves 26 125820804 102 = 806861231 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122871) (lo := 900) (len := 102) (W := 806861231) check rows elimOK (by decide) (by decide) cover122871 (by decide)
  decide +kernel

theorem c122871_8 : P.sumLeaves 26 125820906 22 = 339358636 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122871) (lo := 1002) (len := 22) (W := 339358636) check rows elimOK (by decide) (by decide) cover122871 (by decide)
  decide +kernel

theorem h122871 : P.leaf 36 122871 = 4588867943 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(153, 168306711), (133, 217649974), (126, 496360597), (103, 794334826), (136, 432181726), (116, 637255952), (133, 696558290), (102, 806861231), (22, 339358636)]) (.cons c122871_0 (.cons c122871_1 (.cons c122871_2 (.cons c122871_3 (.cons c122871_4 (.cons c122871_5 (.cons c122871_6 (.cons c122871_7 (.cons c122871_8 (.nil)))))))))) (by decide) (by decide))

theorem cover122873 : P.CoversSplit 26 10 122873 0xfffffffffffffafafffffffffffffafafffffffffffffac8fafafafac8c8c8c8fffffafafffffafafafaf0f0fafaf0f0fffffafafffffac8fafaf0f0c8c8c0c0fffffffffffffafafffffffffffffafaffffffffccccc8c8fafafafac8c8c8c8fffffafafffffafafafaf0f0fafaf0f0fffffafaccccc8c8fafaf0f0c8c8c0c0 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 922, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c122873_0 : P.sumLeaves 26 125821952 172 = 42523728 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122873) (lo := 0) (len := 172) (W := 42523728) check rows elimOK (by decide) (by decide) cover122873 (by decide)
  decide +kernel

theorem c122873_1 : P.sumLeaves 26 125822124 133 = 60245060 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122873) (lo := 172) (len := 133) (W := 60245060) check rows elimOK (by decide) (by decide) cover122873 (by decide)
  decide +kernel

theorem c122873_2 : P.sumLeaves 26 125822257 121 = 124184852 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122873) (lo := 305) (len := 121) (W := 124184852) check rows elimOK (by decide) (by decide) cover122873 (by decide)
  decide +kernel

theorem c122873_3 : P.sumLeaves 26 125822378 130 = 253821766 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122873) (lo := 426) (len := 130) (W := 253821766) check rows elimOK (by decide) (by decide) cover122873 (by decide)
  decide +kernel

theorem c122873_4 : P.sumLeaves 26 125822508 131 = 193019556 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122873) (lo := 556) (len := 131) (W := 193019556) check rows elimOK (by decide) (by decide) cover122873 (by decide)
  decide +kernel

theorem c122873_5 : P.sumLeaves 26 125822639 134 = 468043686 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122873) (lo := 687) (len := 134) (W := 468043686) check rows elimOK (by decide) (by decide) cover122873 (by decide)
  decide +kernel

theorem c122873_6 : P.sumLeaves 26 125822773 109 = 239448956 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122873) (lo := 821) (len := 109) (W := 239448956) check rows elimOK (by decide) (by decide) cover122873 (by decide)
  decide +kernel

theorem c122873_7 : P.sumLeaves 26 125822882 94 = 674515372 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122873) (lo := 930) (len := 94) (W := 674515372) check rows elimOK (by decide) (by decide) cover122873 (by decide)
  decide +kernel

theorem h122873 : P.leaf 36 122873 = 2055802976 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(172, 42523728), (133, 60245060), (121, 124184852), (130, 253821766), (131, 193019556), (134, 468043686), (109, 239448956), (94, 674515372)]) (.cons c122873_0 (.cons c122873_1 (.cons c122873_2 (.cons c122873_3 (.cons c122873_4 (.cons c122873_5 (.cons c122873_6 (.cons c122873_7 (.nil))))))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(122871, 360), (122873, 180)]

theorem segOK : checkSeg 20 perms 122871 122874 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 122871 122874 540 2022036995160 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 2022036995160)
    (SegSum.cons (w := 360) h122871 (SegSum.cons (w := 180) h122873 (show SegSum (P.leaf 36) [] 0 from rfl))) (by decide)

end RACert.S6N0.C0.S90
