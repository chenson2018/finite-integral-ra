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

namespace RACert.S6N0.C0.S41

open RACert RACert.Problem

theorem cover65527 : P.CoversSplit 26 10 65527 0xfffffffffffffac8fffffafafffffac8ffffffffffccfac8fac8fac8fac8fac8fffffafafffffac8fafafafafafafac8fffffafaffccfac8fac8fac8fac8fac8ffffffffffccfac8fffffafaffccfac8ffccffccffccfac8fac8fac8fac8fac8fffffafaffccfac8fafafafafac8fac8ffccfac8ffccfac8fac8fac8fac8fac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 1265, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c65527_0 : P.sumLeaves 26 67099648 161 = 260641312 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 65527) (lo := 0) (len := 161) (W := 260641312) check rows elimOK (by decide) (by decide) cover65527 (by decide)
  decide +kernel

theorem c65527_1 : P.sumLeaves 26 67099809 139 = 284414216 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 65527) (lo := 161) (len := 139) (W := 284414216) check rows elimOK (by decide) (by decide) cover65527 (by decide)
  decide +kernel

theorem c65527_2 : P.sumLeaves 26 67099948 137 = 515587192 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 65527) (lo := 300) (len := 137) (W := 515587192) check rows elimOK (by decide) (by decide) cover65527 (by decide)
  decide +kernel

theorem c65527_3 : P.sumLeaves 26 67100085 135 = 658854280 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 65527) (lo := 437) (len := 135) (W := 658854280) check rows elimOK (by decide) (by decide) cover65527 (by decide)
  decide +kernel

theorem c65527_4 : P.sumLeaves 26 67100220 130 = 453088796 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 65527) (lo := 572) (len := 130) (W := 453088796) check rows elimOK (by decide) (by decide) cover65527 (by decide)
  decide +kernel

theorem c65527_5 : P.sumLeaves 26 67100350 142 = 608441012 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 65527) (lo := 702) (len := 142) (W := 608441012) check rows elimOK (by decide) (by decide) cover65527 (by decide)
  decide +kernel

theorem c65527_6 : P.sumLeaves 26 67100492 111 = 589905424 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 65527) (lo := 844) (len := 111) (W := 589905424) check rows elimOK (by decide) (by decide) cover65527 (by decide)
  decide +kernel

theorem c65527_7 : P.sumLeaves 26 67100603 69 = 588894432 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 65527) (lo := 955) (len := 69) (W := 588894432) check rows elimOK (by decide) (by decide) cover65527 (by decide)
  decide +kernel

theorem h65527 : P.leaf 36 65527 = 3959826664 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(161, 260641312), (139, 284414216), (137, 515587192), (135, 658854280), (130, 453088796), (142, 608441012), (111, 589905424), (69, 588894432)]) (.cons c65527_0 (.cons c65527_1 (.cons c65527_2 (.cons c65527_3 (.cons c65527_4 (.cons c65527_5 (.cons c65527_6 (.cons c65527_7 (.nil))))))))) (by decide) (by decide))

theorem cover65535 : P.CoversSplit 26 10 65535 0xfffffffffffffac8fffffafafffffac8ffffffffffccfac8fac8fac8fac8fac8fffffafafffffac8fafafafafafafac8fffffafaffccfac8fac8fac8fac8fac8ffffffffffccfac8fffffafaffccfac8ffccffccffccfac8fac8fac8fac8fac8fffffafaffccfac8fafafafafac8fac8ffccfac8ffccfac8fac8fac8fac8fac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [1265, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c65535_0 : P.sumLeaves 26 67107840 161 = 1075499064 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 65535) (lo := 0) (len := 161) (W := 1075499064) check rows elimOK (by decide) (by decide) cover65535 (by decide)
  decide +kernel

theorem c65535_1 : P.sumLeaves 26 67108001 139 = 1101758662 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 65535) (lo := 161) (len := 139) (W := 1101758662) check rows elimOK (by decide) (by decide) cover65535 (by decide)
  decide +kernel

theorem c65535_2 : P.sumLeaves 26 67108140 137 = 1337340408 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 65535) (lo := 300) (len := 137) (W := 1337340408) check rows elimOK (by decide) (by decide) cover65535 (by decide)
  decide +kernel

theorem c65535_3 : P.sumLeaves 26 67108277 135 = 1501651550 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 65535) (lo := 437) (len := 135) (W := 1501651550) check rows elimOK (by decide) (by decide) cover65535 (by decide)
  decide +kernel

theorem c65535_4 : P.sumLeaves 26 67108412 130 = 1330704214 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 65535) (lo := 572) (len := 130) (W := 1330704214) check rows elimOK (by decide) (by decide) cover65535 (by decide)
  decide +kernel

theorem c65535_5 : P.sumLeaves 26 67108542 142 = 1618354674 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 65535) (lo := 702) (len := 142) (W := 1618354674) check rows elimOK (by decide) (by decide) cover65535 (by decide)
  decide +kernel

theorem c65535_6 : P.sumLeaves 26 67108684 111 = 1401247800 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 65535) (lo := 844) (len := 111) (W := 1401247800) check rows elimOK (by decide) (by decide) cover65535 (by decide)
  decide +kernel

theorem c65535_7 : P.sumLeaves 26 67108795 69 = 1170338820 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 65535) (lo := 955) (len := 69) (W := 1170338820) check rows elimOK (by decide) (by decide) cover65535 (by decide)
  decide +kernel

theorem h65535 : P.leaf 36 65535 = 10536895192 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(161, 1075499064), (139, 1101758662), (137, 1337340408), (135, 1501651550), (130, 1330704214), (142, 1618354674), (111, 1401247800), (69, 1170338820)]) (.cons c65535_0 (.cons c65535_1 (.cons c65535_2 (.cons c65535_3 (.cons c65535_4 (.cons c65535_5 (.cons c65535_6 (.cons c65535_7 (.nil))))))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(65527, 60), (65535, 15)]

theorem segOK : checkSeg 20 perms 65527 76983 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 65527 76983 75 395643027720 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 395643027720)
    (SegSum.cons (w := 60) h65527 (SegSum.cons (w := 15) h65535 (show SegSum (P.leaf 36) [] 0 from rfl))) (by decide)

end RACert.S6N0.C0.S41
