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

namespace RACert.S6N0.C0.S92

open RACert RACert.Problem

theorem cover122878 : P.CoversSplit 26 10 122878 0xfffffffffffffafafffffffffffffafafffffffffffffac8fafafafac8c8c8c8fffffafafffffafafafafafafafafafafffffafafffffac8fafafafac8c8c8c8fffffffffffffafafffffffffffffafaffffffffccccc8c8fafafafac8c8c8c8fffffafafffffafafafafafafafafafafffffafaccccc8c8fafafafac8c8c8c8 :=
  coversSplit check rows (by decide) (by decide) (xs := [922, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c122878_0 : P.sumLeaves 26 125827072 153 = 162699952 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122878) (lo := 0) (len := 153) (W := 162699952) check rows elimOK (by decide) (by decide) cover122878 (by decide)
  decide +kernel

theorem c122878_1 : P.sumLeaves 26 125827225 133 = 219721246 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122878) (lo := 153) (len := 133) (W := 219721246) check rows elimOK (by decide) (by decide) cover122878 (by decide)
  decide +kernel

theorem c122878_2 : P.sumLeaves 26 125827358 126 = 441242760 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122878) (lo := 286) (len := 126) (W := 441242760) check rows elimOK (by decide) (by decide) cover122878 (by decide)
  decide +kernel

theorem c122878_3 : P.sumLeaves 26 125827484 103 = 981487428 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122878) (lo := 412) (len := 103) (W := 981487428) check rows elimOK (by decide) (by decide) cover122878 (by decide)
  decide +kernel

theorem c122878_4 : P.sumLeaves 26 125827587 136 = 566834161 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122878) (lo := 515) (len := 136) (W := 566834161) check rows elimOK (by decide) (by decide) cover122878 (by decide)
  decide +kernel

theorem c122878_5 : P.sumLeaves 26 125827723 116 = 886830376 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122878) (lo := 651) (len := 116) (W := 886830376) check rows elimOK (by decide) (by decide) cover122878 (by decide)
  decide +kernel

theorem c122878_6 : P.sumLeaves 26 125827839 133 = 746905931 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122878) (lo := 767) (len := 133) (W := 746905931) check rows elimOK (by decide) (by decide) cover122878 (by decide)
  decide +kernel

theorem c122878_7 : P.sumLeaves 26 125827972 102 = 861831461 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122878) (lo := 900) (len := 102) (W := 861831461) check rows elimOK (by decide) (by decide) cover122878 (by decide)
  decide +kernel

theorem c122878_8 : P.sumLeaves 26 125828074 22 = 466631946 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122878) (lo := 1002) (len := 22) (W := 466631946) check rows elimOK (by decide) (by decide) cover122878 (by decide)
  decide +kernel

theorem h122878 : P.leaf 36 122878 = 5334185261 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(153, 162699952), (133, 219721246), (126, 441242760), (103, 981487428), (136, 566834161), (116, 886830376), (133, 746905931), (102, 861831461), (22, 466631946)]) (.cons c122878_0 (.cons c122878_1 (.cons c122878_2 (.cons c122878_3 (.cons c122878_4 (.cons c122878_5 (.cons c122878_6 (.cons c122878_7 (.cons c122878_8 (.nil)))))))))) (by decide) (by decide))

theorem cover122879 : P.CoversSplit 26 10 122879 0xfffffffffffffafafffffffffffffafafffffffffffffac8fafafafac8c8c8c8fffffafafffffafafafafafafafafafafffffafafffffac8fafafafac8c8c8c8fffffffffffffafafffffffffffffafaffffffffccccc8c8fafafafac8c8c8c8fffffafafffffafafafafafafafafafafffffafaccccc8c8fafafafac8c8c8c8 :=
  coversSplit check rows (by decide) (by decide) (xs := [922, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c122879_0 : P.sumLeaves 26 125828096 153 = 684486149 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122879) (lo := 0) (len := 153) (W := 684486149) check rows elimOK (by decide) (by decide) cover122879 (by decide)
  decide +kernel

theorem c122879_1 : P.sumLeaves 26 125828249 133 = 814150123 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122879) (lo := 153) (len := 133) (W := 814150123) check rows elimOK (by decide) (by decide) cover122879 (by decide)
  decide +kernel

theorem c122879_2 : P.sumLeaves 26 125828382 126 = 960762719 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122879) (lo := 286) (len := 126) (W := 960762719) check rows elimOK (by decide) (by decide) cover122879 (by decide)
  decide +kernel

theorem c122879_3 : P.sumLeaves 26 125828508 103 = 1345261390 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122879) (lo := 412) (len := 103) (W := 1345261390) check rows elimOK (by decide) (by decide) cover122879 (by decide)
  decide +kernel

theorem c122879_4 : P.sumLeaves 26 125828611 136 = 1101882379 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122879) (lo := 515) (len := 136) (W := 1101882379) check rows elimOK (by decide) (by decide) cover122879 (by decide)
  decide +kernel

theorem c122879_5 : P.sumLeaves 26 125828747 116 = 1420429795 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122879) (lo := 651) (len := 116) (W := 1420429795) check rows elimOK (by decide) (by decide) cover122879 (by decide)
  decide +kernel

theorem c122879_6 : P.sumLeaves 26 125828863 133 = 1319224668 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122879) (lo := 767) (len := 133) (W := 1319224668) check rows elimOK (by decide) (by decide) cover122879 (by decide)
  decide +kernel

theorem c122879_7 : P.sumLeaves 26 125828996 102 = 1444956296 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122879) (lo := 900) (len := 102) (W := 1444956296) check rows elimOK (by decide) (by decide) cover122879 (by decide)
  decide +kernel

theorem c122879_8 : P.sumLeaves 26 125829098 22 = 523887866 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122879) (lo := 1002) (len := 22) (W := 523887866) check rows elimOK (by decide) (by decide) cover122879 (by decide)
  decide +kernel

theorem h122879 : P.leaf 36 122879 = 9615041385 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(153, 684486149), (133, 814150123), (126, 960762719), (103, 1345261390), (136, 1101882379), (116, 1420429795), (133, 1319224668), (102, 1444956296), (22, 523887866)]) (.cons c122879_0 (.cons c122879_1 (.cons c122879_2 (.cons c122879_3 (.cons c122879_4 (.cons c122879_5 (.cons c122879_6 (.cons c122879_7 (.cons c122879_8 (.nil)))))))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(122878, 360), (122879, 360)]

theorem segOK : checkSeg 20 perms 122878 131056 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 122878 131056 720 5381721592560 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 5381721592560)
    (SegSum.cons (w := 360) h122878 (SegSum.cons (w := 360) h122879 (show SegSum (P.leaf 36) [] 0 from rfl))) (by decide)

end RACert.S6N0.C0.S92
