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

namespace RACert.S6N0.C0.S107

open RACert RACert.Problem

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

theorem cover243583 : P.CoversSplit 26 10 243583 0xfffffffffffffffffffffffffffffafaffffffffffffccccffffaaaaff008800ffffffffffffffffffffaaaaffffaaaaffffffffffffccccffffaaaaff008800fffffffffffffffffffffffffffffafaffffffffcc00cc00ffffaaaacc008800ffffffffffffffffffffaaaaffffaaaaffffffffcc00cc00ffffaaaacc008800 :=
  coversSplit check rows (by decide) (by decide) (xs := [579, 930, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c243583_0 : P.sumLeaves 26 249428992 165 = 259517749 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243583) (lo := 0) (len := 165) (W := 259517749) check rows elimOK (by decide) (by decide) cover243583 (by decide)
  decide +kernel

theorem c243583_1 : P.sumLeaves 26 249429157 132 = 388682611 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243583) (lo := 165) (len := 132) (W := 388682611) check rows elimOK (by decide) (by decide) cover243583 (by decide)
  decide +kernel

theorem c243583_2 : P.sumLeaves 26 249429289 127 = 538473219 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243583) (lo := 297) (len := 127) (W := 538473219) check rows elimOK (by decide) (by decide) cover243583 (by decide)
  decide +kernel

theorem c243583_3 : P.sumLeaves 26 249429416 118 = 781621998 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243583) (lo := 424) (len := 118) (W := 781621998) check rows elimOK (by decide) (by decide) cover243583 (by decide)
  decide +kernel

theorem c243583_4 : P.sumLeaves 26 249429534 120 = 534163287 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243583) (lo := 542) (len := 120) (W := 534163287) check rows elimOK (by decide) (by decide) cover243583 (by decide)
  decide +kernel

theorem c243583_5 : P.sumLeaves 26 249429654 104 = 738781330 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243583) (lo := 662) (len := 104) (W := 738781330) check rows elimOK (by decide) (by decide) cover243583 (by decide)
  decide +kernel

theorem c243583_6 : P.sumLeaves 26 249429758 136 = 730461001 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243583) (lo := 766) (len := 136) (W := 730461001) check rows elimOK (by decide) (by decide) cover243583 (by decide)
  decide +kernel

theorem c243583_7 : P.sumLeaves 26 249429894 98 = 859964285 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243583) (lo := 902) (len := 98) (W := 859964285) check rows elimOK (by decide) (by decide) cover243583 (by decide)
  decide +kernel

theorem c243583_8 : P.sumLeaves 26 249429992 24 = 334577398 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243583) (lo := 1000) (len := 24) (W := 334577398) check rows elimOK (by decide) (by decide) cover243583 (by decide)
  decide +kernel

theorem h243583 : P.leaf 36 243583 = 5166242878 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(165, 259517749), (132, 388682611), (127, 538473219), (118, 781621998), (120, 534163287), (104, 738781330), (136, 730461001), (98, 859964285), (24, 334577398)]) (.cons c243583_0 (.cons c243583_1 (.cons c243583_2 (.cons c243583_3 (.cons c243583_4 (.cons c243583_5 (.cons c243583_6 (.cons c243583_7 (.cons c243583_8 (.nil)))))))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(243582, 720), (243583, 720)]

theorem segOK : checkSeg 20 perms 243582 243683 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 243582 243683 1440 5709598713360 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 5709598713360)
    (SegSum.cons (w := 720) h243582 (SegSum.cons (w := 720) h243583 (show SegSum (P.leaf 36) [] 0 from rfl))) (by decide)

end RACert.S6N0.C0.S107
