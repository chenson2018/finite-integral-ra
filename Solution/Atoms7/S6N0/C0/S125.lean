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

namespace RACert.S6N0.C0.S125

open RACert RACert.Problem

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

theorem cover243582 : P.CoversSplit 26 10 243582 0xfffffffffffffffffffffffffffffafaffffffffffffccccffffaaaaff008800ffffffffffffffffffffa0a0ffffa0a0ffffffffffffccccffffa0a0ff008000fffffffffffffffffffffffffffffafaffffffffcc00cc00ffffaaaacc008800ffffffffffffffffffffa0a0ffffa0a0ffffffffcc00cc00ffffa0a0cc008000 :=
  coversSplit check rows (by decide) (by decide) (xs := [579, 873, 930, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c243582_0 : P.sumLeaves 26 249427968 183 = 71232388 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243582) (lo := 0) (len := 183) (W := 71232388) check rows elimOK (by decide) (by decide) cover243582 (by decide)
  decide +kernel

theorem c243582_1 : P.sumLeaves 26 249428151 130 = 120260187 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243582) (lo := 183) (len := 130) (W := 120260187) check rows elimOK (by decide) (by decide) cover243582 (by decide)
  decide +kernel

theorem c243582_2 : P.sumLeaves 26 249428281 124 = 226506087 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243582) (lo := 313) (len := 124) (W := 226506087) check rows elimOK (by decide) (by decide) cover243582 (by decide)
  decide +kernel

theorem c243582_3 : P.sumLeaves 26 249428405 131 = 362502211 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243582) (lo := 437) (len := 131) (W := 362502211) check rows elimOK (by decide) (by decide) cover243582 (by decide)
  decide +kernel

theorem c243582_4 : P.sumLeaves 26 249428536 128 = 324877203 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243582) (lo := 568) (len := 128) (W := 324877203) check rows elimOK (by decide) (by decide) cover243582 (by decide)
  decide +kernel

theorem c243582_5 : P.sumLeaves 26 249428664 126 = 511335596 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243582) (lo := 696) (len := 126) (W := 511335596) check rows elimOK (by decide) (by decide) cover243582 (by decide)
  decide +kernel

theorem c243582_6 : P.sumLeaves 26 249428790 108 = 443001322 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243582) (lo := 822) (len := 108) (W := 443001322) check rows elimOK (by decide) (by decide) cover243582 (by decide)
  decide +kernel

theorem c243582_7 : P.sumLeaves 26 249428898 94 = 704040341 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243582) (lo := 930) (len := 94) (W := 704040341) check rows elimOK (by decide) (by decide) cover243582 (by decide)
  decide +kernel

theorem h243582 : P.leaf 36 243582 = 2763755335 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(183, 71232388), (130, 120260187), (124, 226506087), (131, 362502211), (128, 324877203), (126, 511335596), (108, 443001322), (94, 704040341)]) (.cons c243582_0 (.cons c243582_1 (.cons c243582_2 (.cons c243582_3 (.cons c243582_4 (.cons c243582_5 (.cons c243582_6 (.cons c243582_7 (.nil))))))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(243579, 360), (243582, 720)]

theorem segOK : checkSeg 20 perms 243579 243583 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 243579 243583 1080 2853983044080 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 2853983044080)
    (SegSum.cons (w := 360) h243579 (SegSum.cons (w := 720) h243582 (show SegSum (P.leaf 36) [] 0 from rfl))) (by decide)

end RACert.S6N0.C0.S125
