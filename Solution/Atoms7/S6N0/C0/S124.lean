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

namespace RACert.S6N0.C0.S124

open RACert RACert.Problem

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

theorem cover243567 : P.CoversSplit 26 10 243567 0xfffffffffffffffffffffffffffffafaffffffffffffccccffffaaaaff008800fffffffffffffffffafaaaaafafaaaaaffffffffffffccccfafaaaaafa008800fffffffffffffffffffffffffffffafaffffffffcc00cc00ffffaaaacc008800fffffffffffffffffafaaaaafafaaaaaffffffffcc00cc00fafaaaaac8008800 :=
  coversSplit check rows (by decide) (by decide) (xs := [579, 930, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c243567_0 : P.sumLeaves 26 249412608 181 = 125942810 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243567) (lo := 0) (len := 181) (W := 125942810) check rows elimOK (by decide) (by decide) cover243567 (by decide)
  decide +kernel

theorem c243567_1 : P.sumLeaves 26 249412789 132 = 222983540 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243567) (lo := 181) (len := 132) (W := 222983540) check rows elimOK (by decide) (by decide) cover243567 (by decide)
  decide +kernel

theorem c243567_2 : P.sumLeaves 26 249412921 124 = 268013353 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243567) (lo := 313) (len := 124) (W := 268013353) check rows elimOK (by decide) (by decide) cover243567 (by decide)
  decide +kernel

theorem c243567_3 : P.sumLeaves 26 249413045 130 = 430502825 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243567) (lo := 437) (len := 130) (W := 430502825) check rows elimOK (by decide) (by decide) cover243567 (by decide)
  decide +kernel

theorem c243567_4 : P.sumLeaves 26 249413175 128 = 276779957 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243567) (lo := 567) (len := 128) (W := 276779957) check rows elimOK (by decide) (by decide) cover243567 (by decide)
  decide +kernel

theorem c243567_5 : P.sumLeaves 26 249413303 128 = 429192328 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243567) (lo := 695) (len := 128) (W := 429192328) check rows elimOK (by decide) (by decide) cover243567 (by decide)
  decide +kernel

theorem c243567_6 : P.sumLeaves 26 249413431 108 = 350902468 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243567) (lo := 823) (len := 108) (W := 350902468) check rows elimOK (by decide) (by decide) cover243567 (by decide)
  decide +kernel

theorem c243567_7 : P.sumLeaves 26 249413539 93 = 605384599 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243567) (lo := 931) (len := 93) (W := 605384599) check rows elimOK (by decide) (by decide) cover243567 (by decide)
  decide +kernel

theorem h243567 : P.leaf 36 243567 = 2709701880 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(181, 125942810), (132, 222983540), (124, 268013353), (130, 430502825), (128, 276779957), (128, 429192328), (108, 350902468), (93, 605384599)]) (.cons c243567_0 (.cons c243567_1 (.cons c243567_2 (.cons c243567_3 (.cons c243567_4 (.cons c243567_5 (.cons c243567_6 (.cons c243567_7 (.nil))))))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(243566, 720), (243567, 720)]

theorem segOK : checkSeg 20 perms 243566 243579 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 243566 243579 1440 2821563532080 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 2821563532080)
    (SegSum.cons (w := 720) h243566 (SegSum.cons (w := 720) h243567 (show SegSum (P.leaf 36) [] 0 from rfl))) (by decide)

end RACert.S6N0.C0.S124
