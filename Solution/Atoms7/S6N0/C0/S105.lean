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

namespace RACert.S6N0.C0.S105

open RACert RACert.Problem

theorem cover243559 : P.CoversSplit 26 10 243559 0xfffffffffffffffffffffffffffffafaffffffffffffccccffffaaaaff008800fffffffffffffffffafaaaaafafaaaaaffffffffffffccccfafaaaaafa008800fffffffffffffffffffffffffffffafaffffffffcc00cc00ffffaaaacc008800fffffffffffffffffafaaaaafafaaaaaffffffffcc00cc00fafaaaaac8008800 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 579, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c243559_0 : P.sumLeaves 26 249404416 181 = 31961837 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243559) (lo := 0) (len := 181) (W := 31961837) check rows elimOK (by decide) (by decide) cover243559 (by decide)
  decide +kernel

theorem c243559_1 : P.sumLeaves 26 249404597 132 = 72507738 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243559) (lo := 181) (len := 132) (W := 72507738) check rows elimOK (by decide) (by decide) cover243559 (by decide)
  decide +kernel

theorem c243559_2 : P.sumLeaves 26 249404729 124 = 160243445 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243559) (lo := 313) (len := 124) (W := 160243445) check rows elimOK (by decide) (by decide) cover243559 (by decide)
  decide +kernel

theorem c243559_3 : P.sumLeaves 26 249404853 130 = 271710924 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243559) (lo := 437) (len := 130) (W := 271710924) check rows elimOK (by decide) (by decide) cover243559 (by decide)
  decide +kernel

theorem c243559_4 : P.sumLeaves 26 249404983 128 = 123825826 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243559) (lo := 567) (len := 128) (W := 123825826) check rows elimOK (by decide) (by decide) cover243559 (by decide)
  decide +kernel

theorem c243559_5 : P.sumLeaves 26 249405111 128 = 204801159 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243559) (lo := 695) (len := 128) (W := 204801159) check rows elimOK (by decide) (by decide) cover243559 (by decide)
  decide +kernel

theorem c243559_6 : P.sumLeaves 26 249405239 108 = 204361170 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243559) (lo := 823) (len := 108) (W := 204361170) check rows elimOK (by decide) (by decide) cover243559 (by decide)
  decide +kernel

theorem c243559_7 : P.sumLeaves 26 249405347 93 = 361659896 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243559) (lo := 931) (len := 93) (W := 361659896) check rows elimOK (by decide) (by decide) cover243559 (by decide)
  decide +kernel

theorem h243559 : P.leaf 36 243559 = 1431071995 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(181, 31961837), (132, 72507738), (124, 160243445), (130, 271710924), (128, 123825826), (128, 204801159), (108, 204361170), (93, 361659896)]) (.cons c243559_0 (.cons c243559_1 (.cons c243559_2 (.cons c243559_3 (.cons c243559_4 (.cons c243559_5 (.cons c243559_6 (.cons c243559_7 (.nil))))))))) (by decide) (by decide))

theorem cover243566 : P.CoversSplit 26 10 243566 0xfffffffffffffffffffffffffffffafaffffffffffffccccffffaaaaff008800fffffffffffffffffafaa0a0fafaa0a0ffffffffffffccccfafaa0a0fa008000fffffffffffffffffffffffffffffafaffffffffcc00cc00ffffaaaacc008800fffffffffffffffffafaa0a0fafaa0a0ffffffffcc00cc00fafaa0a0c8008000 :=
  coversSplit check rows (by decide) (by decide) (xs := [579, 873, 930, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c243566_0 : P.sumLeaves 26 249411584 196 = 32729447 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243566) (lo := 0) (len := 196) (W := 32729447) check rows elimOK (by decide) (by decide) cover243566 (by decide)
  decide +kernel

theorem c243566_1 : P.sumLeaves 26 249411780 154 = 63147671 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243566) (lo := 196) (len := 154) (W := 63147671) check rows elimOK (by decide) (by decide) cover243566 (by decide)
  decide +kernel

theorem c243566_2 : P.sumLeaves 26 249411934 100 = 92955138 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243566) (lo := 350) (len := 100) (W := 92955138) check rows elimOK (by decide) (by decide) cover243566 (by decide)
  decide +kernel

theorem c243566_3 : P.sumLeaves 26 249412034 145 = 150204578 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243566) (lo := 450) (len := 145) (W := 150204578) check rows elimOK (by decide) (by decide) cover243566 (by decide)
  decide +kernel

theorem c243566_4 : P.sumLeaves 26 249412179 128 = 146553691 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243566) (lo := 595) (len := 128) (W := 146553691) check rows elimOK (by decide) (by decide) cover243566 (by decide)
  decide +kernel

theorem c243566_5 : P.sumLeaves 26 249412307 134 = 228491299 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243566) (lo := 723) (len := 134) (W := 228491299) check rows elimOK (by decide) (by decide) cover243566 (by decide)
  decide +kernel

theorem c243566_6 : P.sumLeaves 26 249412441 100 = 192257208 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243566) (lo := 857) (len := 100) (W := 192257208) check rows elimOK (by decide) (by decide) cover243566 (by decide)
  decide +kernel

theorem c243566_7 : P.sumLeaves 26 249412541 67 = 302797327 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243566) (lo := 957) (len := 67) (W := 302797327) check rows elimOK (by decide) (by decide) cover243566 (by decide)
  decide +kernel

theorem h243566 : P.leaf 36 243566 = 1209136359 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(196, 32729447), (154, 63147671), (100, 92955138), (145, 150204578), (128, 146553691), (134, 228491299), (100, 192257208), (67, 302797327)]) (.cons c243566_0 (.cons c243566_1 (.cons c243566_2 (.cons c243566_3 (.cons c243566_4 (.cons c243566_5 (.cons c243566_6 (.cons c243566_7 (.nil))))))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(243559, 240), (243566, 720)]

theorem segOK : checkSeg 20 perms 243559 243567 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 243559 243567 960 1214035457280 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 1214035457280)
    (SegSum.cons (w := 240) h243559 (SegSum.cons (w := 720) h243566 (show SegSum (P.leaf 36) [] 0 from rfl))) (by decide)

end RACert.S6N0.C0.S105
