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

namespace RACert.S6N0.C0.S106

open RACert RACert.Problem

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

theorem cover243579 : P.CoversSplit 26 10 243579 0xfffffffffffffffffffffffffffffafaffffffffffffccccffffaaaaff008800ffffffffffffffffffffaaaaffffaaaaffffffffffffccccffffaaaaff008800fffffffffffffffffffffffffffffafaffffffffcc00cc00ffffaaaacc008800ffffffffffffffffffffaaaaffffaaaaffffffffcc00cc00ffffaaaacc008800 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 930, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c243579_0 : P.sumLeaves 26 249424896 165 = 48806298 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243579) (lo := 0) (len := 165) (W := 48806298) check rows elimOK (by decide) (by decide) cover243579 (by decide)
  decide +kernel

theorem c243579_1 : P.sumLeaves 26 249425061 132 = 106899648 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243579) (lo := 165) (len := 132) (W := 106899648) check rows elimOK (by decide) (by decide) cover243579 (by decide)
  decide +kernel

theorem c243579_2 : P.sumLeaves 26 249425193 127 = 173226641 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243579) (lo := 297) (len := 127) (W := 173226641) check rows elimOK (by decide) (by decide) cover243579 (by decide)
  decide +kernel

theorem c243579_3 : P.sumLeaves 26 249425320 118 = 342382488 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243579) (lo := 424) (len := 118) (W := 342382488) check rows elimOK (by decide) (by decide) cover243579 (by decide)
  decide +kernel

theorem c243579_4 : P.sumLeaves 26 249425438 120 = 242193014 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243579) (lo := 542) (len := 120) (W := 242193014) check rows elimOK (by decide) (by decide) cover243579 (by decide)
  decide +kernel

theorem c243579_5 : P.sumLeaves 26 249425558 104 = 453307858 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243579) (lo := 662) (len := 104) (W := 453307858) check rows elimOK (by decide) (by decide) cover243579 (by decide)
  decide +kernel

theorem c243579_6 : P.sumLeaves 26 249425662 136 = 319917591 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243579) (lo := 766) (len := 136) (W := 319917591) check rows elimOK (by decide) (by decide) cover243579 (by decide)
  decide +kernel

theorem c243579_7 : P.sumLeaves 26 249425798 98 = 497298454 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243579) (lo := 902) (len := 98) (W := 497298454) check rows elimOK (by decide) (by decide) cover243579 (by decide)
  decide +kernel

theorem c243579_8 : P.sumLeaves 26 249425896 24 = 216188016 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243579) (lo := 1000) (len := 24) (W := 216188016) check rows elimOK (by decide) (by decide) cover243579 (by decide)
  decide +kernel

theorem h243579 : P.leaf 36 243579 = 2400220008 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(165, 48806298), (132, 106899648), (127, 173226641), (118, 342382488), (120, 242193014), (104, 453307858), (136, 319917591), (98, 497298454), (24, 216188016)]) (.cons c243579_0 (.cons c243579_1 (.cons c243579_2 (.cons c243579_3 (.cons c243579_4 (.cons c243579_5 (.cons c243579_6 (.cons c243579_7 (.cons c243579_8 (.nil)))))))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(243567, 720), (243579, 360)]

theorem segOK : checkSeg 20 perms 243567 243582 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 243567 243582 1080 2815064556480 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 2815064556480)
    (SegSum.cons (w := 720) h243567 (SegSum.cons (w := 360) h243579 (show SegSum (P.leaf 36) [] 0 from rfl))) (by decide)

end RACert.S6N0.C0.S106
