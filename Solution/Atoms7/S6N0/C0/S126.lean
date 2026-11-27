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

namespace RACert.S6N0.C0.S126

open RACert RACert.Problem

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

theorem cover243683 : P.CoversSplit 26 10 243683 0xfffffffffffffffffffffafafffffafaffffffffffccccccffffaaaaffcc8888ffffffffffffffffffffaaaaffffaaaaffffffffffccccccffffaaaaffcc8888fffffffffffffffffffffafafffffafaffffffffccccccccffffaaaacccc8888ffffffffffffffffffffaaaaffffaaaaffffffffccccccccffffaaaacccc8888 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 1322, 1658]) (by decide +kernel)

theorem c243683_0 : P.sumLeaves 26 249531392 148 = 7783236 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243683) (lo := 0) (len := 148) (W := 7783236) check rows elimOK (by decide) (by decide) cover243683 (by decide)
  decide +kernel

theorem c243683_1 : P.sumLeaves 26 249531540 104 = 25004700 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243683) (lo := 148) (len := 104) (W := 25004700) check rows elimOK (by decide) (by decide) cover243683 (by decide)
  decide +kernel

theorem c243683_2 : P.sumLeaves 26 249531644 144 = 71882762 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243683) (lo := 252) (len := 144) (W := 71882762) check rows elimOK (by decide) (by decide) cover243683 (by decide)
  decide +kernel

theorem c243683_3 : P.sumLeaves 26 249531788 100 = 210795658 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243683) (lo := 396) (len := 100) (W := 210795658) check rows elimOK (by decide) (by decide) cover243683 (by decide)
  decide +kernel

theorem c243683_4 : P.sumLeaves 26 249531888 132 = 134144380 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243683) (lo := 496) (len := 132) (W := 134144380) check rows elimOK (by decide) (by decide) cover243683 (by decide)
  decide +kernel

theorem c243683_5 : P.sumLeaves 26 249532020 112 = 200272180 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243683) (lo := 628) (len := 112) (W := 200272180) check rows elimOK (by decide) (by decide) cover243683 (by decide)
  decide +kernel

theorem c243683_6 : P.sumLeaves 26 249532132 132 = 171188952 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243683) (lo := 740) (len := 132) (W := 171188952) check rows elimOK (by decide) (by decide) cover243683 (by decide)
  decide +kernel

theorem c243683_7 : P.sumLeaves 26 249532264 104 = 281883056 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243683) (lo := 872) (len := 104) (W := 281883056) check rows elimOK (by decide) (by decide) cover243683 (by decide)
  decide +kernel

theorem c243683_8 : P.sumLeaves 26 249532368 48 = 239302064 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243683) (lo := 976) (len := 48) (W := 239302064) check rows elimOK (by decide) (by decide) cover243683 (by decide)
  decide +kernel

theorem h243683 : P.leaf 36 243683 = 1342256988 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(148, 7783236), (104, 25004700), (144, 71882762), (100, 210795658), (132, 134144380), (112, 200272180), (132, 171188952), (104, 281883056), (48, 239302064)]) (.cons c243683_0 (.cons c243683_1 (.cons c243683_2 (.cons c243683_3 (.cons c243683_4 (.cons c243683_5 (.cons c243683_6 (.cons c243683_7 (.cons c243683_8 (.nil)))))))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(243583, 720), (243683, 120)]

theorem segOK : checkSeg 20 perms 243583 243687 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 243583 243687 840 3880765710720 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 3880765710720)
    (SegSum.cons (w := 720) h243583 (SegSum.cons (w := 120) h243683 (show SegSum (P.leaf 36) [] 0 from rfl))) (by decide)

end RACert.S6N0.C0.S126
