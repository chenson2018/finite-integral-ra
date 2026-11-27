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

namespace RACert.S6N0.C0.S123

open RACert RACert.Problem

theorem cover243558 : P.CoversSplit 26 10 243558 0xfffffffffffffffffffffffffffffafaffffffffffffccccffffaaaaff008800fffffffffffffffffafaa0a0fafaa0a0ffffffffffffccccfafaa0a0fa008000fffffffffffffffffffffffffffffafaffccffcccc00cc00ffccaa88cc008800fffffffffffffffffafaa0a0fafaa0a0ffccffcccc00cc00fac8a080c8008000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 579, 873, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c243558_0 : P.sumLeaves 26 249403392 208 = 8052962 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243558) (lo := 0) (len := 208) (W := 8052962) check rows elimOK (by decide) (by decide) cover243558 (by decide)
  decide +kernel

theorem c243558_1 : P.sumLeaves 26 249403600 168 = 31087922 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243558) (lo := 208) (len := 168) (W := 31087922) check rows elimOK (by decide) (by decide) cover243558 (by decide)
  decide +kernel

theorem c243558_2 : P.sumLeaves 26 249403768 100 = 48284170 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243558) (lo := 376) (len := 100) (W := 48284170) check rows elimOK (by decide) (by decide) cover243558 (by decide)
  decide +kernel

theorem c243558_3 : P.sumLeaves 26 249403868 145 = 79321269 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243558) (lo := 476) (len := 145) (W := 79321269) check rows elimOK (by decide) (by decide) cover243558 (by decide)
  decide +kernel

theorem c243558_4 : P.sumLeaves 26 249404013 128 = 81655679 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243558) (lo := 621) (len := 128) (W := 81655679) check rows elimOK (by decide) (by decide) cover243558 (by decide)
  decide +kernel

theorem c243558_5 : P.sumLeaves 26 249404141 134 = 101381704 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243558) (lo := 749) (len := 134) (W := 101381704) check rows elimOK (by decide) (by decide) cover243558 (by decide)
  decide +kernel

theorem c243558_6 : P.sumLeaves 26 249404275 100 = 100397662 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243558) (lo := 883) (len := 100) (W := 100397662) check rows elimOK (by decide) (by decide) cover243558 (by decide)
  decide +kernel

theorem c243558_7 : P.sumLeaves 26 249404375 41 = 117116828 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243558) (lo := 983) (len := 41) (W := 117116828) check rows elimOK (by decide) (by decide) cover243558 (by decide)
  decide +kernel

theorem h243558 : P.leaf 36 243558 = 567298196 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(208, 8052962), (168, 31087922), (100, 48284170), (145, 79321269), (128, 81655679), (134, 101381704), (100, 100397662), (41, 117116828)]) (.cons c243558_0 (.cons c243558_1 (.cons c243558_2 (.cons c243558_3 (.cons c243558_4 (.cons c243558_5 (.cons c243558_6 (.cons c243558_7 (.nil))))))))) (by decide) (by decide))

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

def seg : List (ℕ × ℕ) := [(243558, 120), (243559, 240)]

theorem segOK : checkSeg 20 perms 243558 243566 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 243558 243566 360 411533062320 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 411533062320)
    (SegSum.cons (w := 120) h243558 (SegSum.cons (w := 240) h243559 (show SegSum (P.leaf 36) [] 0 from rfl))) (by decide)

end RACert.S6N0.C0.S123
