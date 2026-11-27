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

namespace RACert.S6N0.C0.S118

open RACert RACert.Problem

theorem cover241643 : P.CoversSplit 26 10 241643 0xffffffffffffffffffffffffffffaaaaffffffffffffffccffffaaaaffccaa88ffffffffffffffffffffaaaaffffaaaaffffffffffffffccffffaaaaffccaa88ffffffffffffffffffffffffffffaaaaffffffffffccffccffffaaaaffccaa88ffffffffffffffffffffaaaaffffaaaaffffffffffccffccffffaaaaffccaa88 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 881, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c241643_0 : P.sumLeaves 26 247442432 126 = 40156640 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241643) (lo := 0) (len := 126) (W := 40156640) check rows elimOK (by decide) (by decide) cover241643 (by decide)
  decide +kernel

theorem c241643_1 : P.sumLeaves 26 247442558 112 = 84678579 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241643) (lo := 126) (len := 112) (W := 84678579) check rows elimOK (by decide) (by decide) cover241643 (by decide)
  decide +kernel

theorem c241643_2 : P.sumLeaves 26 247442670 126 = 145701054 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241643) (lo := 238) (len := 126) (W := 145701054) check rows elimOK (by decide) (by decide) cover241643 (by decide)
  decide +kernel

theorem c241643_3 : P.sumLeaves 26 247442796 104 = 326170952 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241643) (lo := 364) (len := 104) (W := 326170952) check rows elimOK (by decide) (by decide) cover241643 (by decide)
  decide +kernel

theorem c241643_4 : P.sumLeaves 26 247442900 122 = 374951328 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241643) (lo := 468) (len := 122) (W := 374951328) check rows elimOK (by decide) (by decide) cover241643 (by decide)
  decide +kernel

theorem c241643_5 : P.sumLeaves 26 247443022 112 = 365077761 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241643) (lo := 590) (len := 112) (W := 365077761) check rows elimOK (by decide) (by decide) cover241643 (by decide)
  decide +kernel

theorem c241643_6 : P.sumLeaves 26 247443134 118 = 499736443 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241643) (lo := 702) (len := 118) (W := 499736443) check rows elimOK (by decide) (by decide) cover241643 (by decide)
  decide +kernel

theorem c241643_7 : P.sumLeaves 26 247443252 108 = 392535837 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241643) (lo := 820) (len := 108) (W := 392535837) check rows elimOK (by decide) (by decide) cover241643 (by decide)
  decide +kernel

theorem c241643_8 : P.sumLeaves 26 247443360 96 = 929014826 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241643) (lo := 928) (len := 96) (W := 929014826) check rows elimOK (by decide) (by decide) cover241643 (by decide)
  decide +kernel

theorem h241643 : P.leaf 36 241643 = 3158023420 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(126, 40156640), (112, 84678579), (126, 145701054), (104, 326170952), (122, 374951328), (112, 365077761), (118, 499736443), (108, 392535837), (96, 929014826)]) (.cons c241643_0 (.cons c241643_1 (.cons c241643_2 (.cons c241643_3 (.cons c241643_4 (.cons c241643_5 (.cons c241643_6 (.cons c241643_7 (.cons c241643_8 (.nil)))))))))) (by decide) (by decide))

theorem cover241647 : P.CoversSplit 26 10 241647 0xffffffffffffffffffffffffffffaaaaffffffffffffffccffffaaaaffccaa88ffffffffffffffffffffaaaaffffaaaaffffffffffffffccffffaaaaffccaa88ffffffffffffffffffffffffffffaaaaffffffffffccffccffffaaaaffccaa88ffffffffffffffffffffaaaaffffaaaaffffffffffccffccffffaaaaffccaa88 :=
  coversSplit check rows (by decide) (by decide) (xs := [881, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c241647_0 : P.sumLeaves 26 247446528 126 = 152425414 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241647) (lo := 0) (len := 126) (W := 152425414) check rows elimOK (by decide) (by decide) cover241647 (by decide)
  decide +kernel

theorem c241647_1 : P.sumLeaves 26 247446654 112 = 318489718 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241647) (lo := 126) (len := 112) (W := 318489718) check rows elimOK (by decide) (by decide) cover241647 (by decide)
  decide +kernel

theorem c241647_2 : P.sumLeaves 26 247446766 126 = 354081395 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241647) (lo := 238) (len := 126) (W := 354081395) check rows elimOK (by decide) (by decide) cover241647 (by decide)
  decide +kernel

theorem c241647_3 : P.sumLeaves 26 247446892 104 = 644871443 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241647) (lo := 364) (len := 104) (W := 644871443) check rows elimOK (by decide) (by decide) cover241647 (by decide)
  decide +kernel

theorem c241647_4 : P.sumLeaves 26 247446996 122 = 696896111 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241647) (lo := 468) (len := 122) (W := 696896111) check rows elimOK (by decide) (by decide) cover241647 (by decide)
  decide +kernel

theorem c241647_5 : P.sumLeaves 26 247447118 112 = 519120851 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241647) (lo := 590) (len := 112) (W := 519120851) check rows elimOK (by decide) (by decide) cover241647 (by decide)
  decide +kernel

theorem c241647_6 : P.sumLeaves 26 247447230 118 = 700823067 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241647) (lo := 702) (len := 118) (W := 700823067) check rows elimOK (by decide) (by decide) cover241647 (by decide)
  decide +kernel

theorem c241647_7 : P.sumLeaves 26 247447348 108 = 536981623 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241647) (lo := 820) (len := 108) (W := 536981623) check rows elimOK (by decide) (by decide) cover241647 (by decide)
  decide +kernel

theorem c241647_8 : P.sumLeaves 26 247447456 96 = 1296913594 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241647) (lo := 928) (len := 96) (W := 1296913594) check rows elimOK (by decide) (by decide) cover241647 (by decide)
  decide +kernel

theorem h241647 : P.leaf 36 241647 = 5220603216 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(126, 152425414), (112, 318489718), (126, 354081395), (104, 644871443), (122, 696896111), (112, 519120851), (118, 700823067), (108, 536981623), (96, 1296913594)]) (.cons c241647_0 (.cons c241647_1 (.cons c241647_2 (.cons c241647_3 (.cons c241647_4 (.cons c241647_5 (.cons c241647_6 (.cons c241647_7 (.cons c241647_8 (.nil)))))))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(241643, 90), (241647, 180)]

theorem segOK : checkSeg 20 perms 241643 241663 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 241643 241663 270 1223930686680 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 1223930686680)
    (SegSum.cons (w := 90) h241643 (SegSum.cons (w := 180) h241647 (show SegSum (P.leaf 36) [] 0 from rfl))) (by decide)

end RACert.S6N0.C0.S118
