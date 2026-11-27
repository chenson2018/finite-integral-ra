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

namespace RACert.S6N0.C0.S115

open RACert RACert.Problem

theorem cover245742 : P.CoversSplit 26 10 245742 0xfffffffffffffffffffffffffffffafaffffffffffffffccffffaaaaffccaa88ffffffffffffffffffffaaaaffffaaaaffffffffffffffccffffaaaaffccaa88fffffffffffffffffffffffffffffafaffffffffffccffccffffaaaaffccaa88ffffffffffffffffffffaaaaffffaaaaffffffffffccffccffffaaaaffccaa88 :=
  coversSplit check rows (by decide) (by decide) (xs := [930, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c245742_0 : P.sumLeaves 26 251639808 126 = 63182872 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245742) (lo := 0) (len := 126) (W := 63182872) check rows elimOK (by decide) (by decide) cover245742 (by decide)
  decide +kernel

theorem c245742_1 : P.sumLeaves 26 251639934 112 = 147978944 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245742) (lo := 126) (len := 112) (W := 147978944) check rows elimOK (by decide) (by decide) cover245742 (by decide)
  decide +kernel

theorem c245742_2 : P.sumLeaves 26 251640046 126 = 237588693 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245742) (lo := 238) (len := 126) (W := 237588693) check rows elimOK (by decide) (by decide) cover245742 (by decide)
  decide +kernel

theorem c245742_3 : P.sumLeaves 26 251640172 100 = 622120388 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245742) (lo := 364) (len := 100) (W := 622120388) check rows elimOK (by decide) (by decide) cover245742 (by decide)
  decide +kernel

theorem c245742_4 : P.sumLeaves 26 251640272 122 = 644442363 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245742) (lo := 464) (len := 122) (W := 644442363) check rows elimOK (by decide) (by decide) cover245742 (by decide)
  decide +kernel

theorem c245742_5 : P.sumLeaves 26 251640394 112 = 496812591 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245742) (lo := 586) (len := 112) (W := 496812591) check rows elimOK (by decide) (by decide) cover245742 (by decide)
  decide +kernel

theorem c245742_6 : P.sumLeaves 26 251640506 118 = 793645778 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245742) (lo := 698) (len := 118) (W := 793645778) check rows elimOK (by decide) (by decide) cover245742 (by decide)
  decide +kernel

theorem c245742_7 : P.sumLeaves 26 251640624 104 = 617385144 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245742) (lo := 816) (len := 104) (W := 617385144) check rows elimOK (by decide) (by decide) cover245742 (by decide)
  decide +kernel

theorem c245742_8 : P.sumLeaves 26 251640728 96 = 1336199860 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245742) (lo := 920) (len := 96) (W := 1336199860) check rows elimOK (by decide) (by decide) cover245742 (by decide)
  decide +kernel

theorem c245742_9 : P.sumLeaves 26 251640824 8 = 186018332 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245742) (lo := 1016) (len := 8) (W := 186018332) check rows elimOK (by decide) (by decide) cover245742 (by decide)
  decide +kernel

theorem h245742 : P.leaf 36 245742 = 5145374965 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(126, 63182872), (112, 147978944), (126, 237588693), (100, 622120388), (122, 644442363), (112, 496812591), (118, 793645778), (104, 617385144), (96, 1336199860), (8, 186018332)]) (.cons c245742_0 (.cons c245742_1 (.cons c245742_2 (.cons c245742_3 (.cons c245742_4 (.cons c245742_5 (.cons c245742_6 (.cons c245742_7 (.cons c245742_8 (.cons c245742_9 (.nil))))))))))) (by decide) (by decide))

theorem cover245743 : P.CoversSplit 26 10 245743 0xfffffffffffffffffffffffffffffafaffffffffffffffccffffaaaaffccaa88ffffffffffffffffffffaaaaffffaaaaffffffffffffffccffffaaaaffccaa88fffffffffffffffffffffffffffffafaffffffffffccffccffffaaaaffccaa88ffffffffffffffffffffaaaaffffaaaaffffffffffccffccffffaaaaffccaa88 :=
  coversSplit check rows (by decide) (by decide) (xs := [930, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c245743_0 : P.sumLeaves 26 251640832 126 = 232365049 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245743) (lo := 0) (len := 126) (W := 232365049) check rows elimOK (by decide) (by decide) cover245743 (by decide)
  decide +kernel

theorem c245743_1 : P.sumLeaves 26 251640958 112 = 579948579 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245743) (lo := 126) (len := 112) (W := 579948579) check rows elimOK (by decide) (by decide) cover245743 (by decide)
  decide +kernel

theorem c245743_2 : P.sumLeaves 26 251641070 126 = 506727966 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245743) (lo := 238) (len := 126) (W := 506727966) check rows elimOK (by decide) (by decide) cover245743 (by decide)
  decide +kernel

theorem c245743_3 : P.sumLeaves 26 251641196 100 = 1103971611 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245743) (lo := 364) (len := 100) (W := 1103971611) check rows elimOK (by decide) (by decide) cover245743 (by decide)
  decide +kernel

theorem c245743_4 : P.sumLeaves 26 251641296 122 = 1007315292 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245743) (lo := 464) (len := 122) (W := 1007315292) check rows elimOK (by decide) (by decide) cover245743 (by decide)
  decide +kernel

theorem c245743_5 : P.sumLeaves 26 251641418 112 = 840297549 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245743) (lo := 586) (len := 112) (W := 840297549) check rows elimOK (by decide) (by decide) cover245743 (by decide)
  decide +kernel

theorem c245743_6 : P.sumLeaves 26 251641530 118 = 1232403305 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245743) (lo := 698) (len := 118) (W := 1232403305) check rows elimOK (by decide) (by decide) cover245743 (by decide)
  decide +kernel

theorem c245743_7 : P.sumLeaves 26 251641648 104 = 920830211 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245743) (lo := 816) (len := 104) (W := 920830211) check rows elimOK (by decide) (by decide) cover245743 (by decide)
  decide +kernel

theorem c245743_8 : P.sumLeaves 26 251641752 96 = 2056548874 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245743) (lo := 920) (len := 96) (W := 2056548874) check rows elimOK (by decide) (by decide) cover245743 (by decide)
  decide +kernel

theorem c245743_9 : P.sumLeaves 26 251641848 8 = 216189220 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245743) (lo := 1016) (len := 8) (W := 216189220) check rows elimOK (by decide) (by decide) cover245743 (by decide)
  decide +kernel

theorem h245743 : P.leaf 36 245743 = 8696597656 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(126, 232365049), (112, 579948579), (126, 506727966), (100, 1103971611), (122, 1007315292), (112, 840297549), (118, 1232403305), (104, 920830211), (96, 2056548874), (8, 216189220)]) (.cons c245743_0 (.cons c245743_1 (.cons c245743_2 (.cons c245743_3 (.cons c245743_4 (.cons c245743_5 (.cons c245743_6 (.cons c245743_7 (.cons c245743_8 (.cons c245743_9 (.nil))))))))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(245742, 720), (245743, 720)]

theorem segOK : checkSeg 20 perms 245742 245758 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 245742 245758 1440 9966220287120 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 9966220287120)
    (SegSum.cons (w := 720) h245742 (SegSum.cons (w := 720) h245743 (show SegSum (P.leaf 36) [] 0 from rfl))) (by decide)

end RACert.S6N0.C0.S115
