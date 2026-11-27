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

namespace RACert.S6N0.C0.S95

open RACert RACert.Problem

theorem cover120829 : P.CoversSplit 26 10 120829 0xfffffffffffffafafffffffffffffafaffffffffffffc8c8fafafafac8c8c8c8fffffafafffffafafafaf0f0fafaf0f0fffffafaffffc8c8fafaf0f0c8c8c0c0fffffffffffffafafffffffffffffafaffffffffccccc8c8fafafafac8c8c8c8fffffafafffffafafafaf0f0fafaf0f0fffffafaccccc8c8fafaf0f0c8c8c0c0 :=
  coversSplit check rows (by decide) (by decide) (xs := [873, 922, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c120829_0 : P.sumLeaves 26 123728896 172 = 110508156 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120829) (lo := 0) (len := 172) (W := 110508156) check rows elimOK (by decide) (by decide) cover120829 (by decide)
  decide +kernel

theorem c120829_1 : P.sumLeaves 26 123729068 133 = 137121143 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120829) (lo := 172) (len := 133) (W := 137121143) check rows elimOK (by decide) (by decide) cover120829 (by decide)
  decide +kernel

theorem c120829_2 : P.sumLeaves 26 123729201 121 = 197908173 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120829) (lo := 305) (len := 121) (W := 197908173) check rows elimOK (by decide) (by decide) cover120829 (by decide)
  decide +kernel

theorem c120829_3 : P.sumLeaves 26 123729322 130 = 333519382 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120829) (lo := 426) (len := 130) (W := 333519382) check rows elimOK (by decide) (by decide) cover120829 (by decide)
  decide +kernel

theorem c120829_4 : P.sumLeaves 26 123729452 136 = 287431618 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120829) (lo := 556) (len := 136) (W := 287431618) check rows elimOK (by decide) (by decide) cover120829 (by decide)
  decide +kernel

theorem c120829_5 : P.sumLeaves 26 123729588 133 = 534768772 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120829) (lo := 692) (len := 133) (W := 534768772) check rows elimOK (by decide) (by decide) cover120829 (by decide)
  decide +kernel

theorem c120829_6 : P.sumLeaves 26 123729721 111 = 348930606 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120829) (lo := 825) (len := 111) (W := 348930606) check rows elimOK (by decide) (by decide) cover120829 (by decide)
  decide +kernel

theorem c120829_7 : P.sumLeaves 26 123729832 88 = 666811838 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120829) (lo := 936) (len := 88) (W := 666811838) check rows elimOK (by decide) (by decide) cover120829 (by decide)
  decide +kernel

theorem h120829 : P.leaf 36 120829 = 2616999688 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(172, 110508156), (133, 137121143), (121, 197908173), (130, 333519382), (136, 287431618), (133, 534768772), (111, 348930606), (88, 666811838)]) (.cons c120829_0 (.cons c120829_1 (.cons c120829_2 (.cons c120829_3 (.cons c120829_4 (.cons c120829_5 (.cons c120829_6 (.cons c120829_7 (.nil))))))))) (by decide) (by decide))

theorem cover120831 : P.CoversSplit 26 10 120831 0xfffffffffffffafafffffffffffffafaffffffffffffc8c8fafafafac8c8c8c8fffffafafffffafafafafafafafafafafffffafaffffc8c8fafafafac8c8c8c8fffffffffffffafafffffffffffffafaffffffffccccc8c8fafafafac8c8c8c8fffffafafffffafafafafafafafafafafffffafaccccc8c8fafafafac8c8c8c8 :=
  coversSplit check rows (by decide) (by decide) (xs := [873, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c120831_0 : P.sumLeaves 26 123730944 153 = 480076080 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120831) (lo := 0) (len := 153) (W := 480076080) check rows elimOK (by decide) (by decide) cover120831 (by decide)
  decide +kernel

theorem c120831_1 : P.sumLeaves 26 123731097 133 = 577666758 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120831) (lo := 153) (len := 133) (W := 577666758) check rows elimOK (by decide) (by decide) cover120831 (by decide)
  decide +kernel

theorem c120831_2 : P.sumLeaves 26 123731230 126 = 677919860 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120831) (lo := 286) (len := 126) (W := 677919860) check rows elimOK (by decide) (by decide) cover120831 (by decide)
  decide +kernel

theorem c120831_3 : P.sumLeaves 26 123731356 103 = 930470887 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120831) (lo := 412) (len := 103) (W := 930470887) check rows elimOK (by decide) (by decide) cover120831 (by decide)
  decide +kernel

theorem c120831_4 : P.sumLeaves 26 123731459 139 = 790684090 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120831) (lo := 515) (len := 139) (W := 790684090) check rows elimOK (by decide) (by decide) cover120831 (by decide)
  decide +kernel

theorem c120831_5 : P.sumLeaves 26 123731598 121 = 1107419591 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120831) (lo := 654) (len := 121) (W := 1107419591) check rows elimOK (by decide) (by decide) cover120831 (by decide)
  decide +kernel

theorem c120831_6 : P.sumLeaves 26 123731719 133 = 931406597 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120831) (lo := 775) (len := 133) (W := 931406597) check rows elimOK (by decide) (by decide) cover120831 (by decide)
  decide +kernel

theorem c120831_7 : P.sumLeaves 26 123731852 100 = 1115514072 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120831) (lo := 908) (len := 100) (W := 1115514072) check rows elimOK (by decide) (by decide) cover120831 (by decide)
  decide +kernel

theorem c120831_8 : P.sumLeaves 26 123731952 16 = 301208328 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120831) (lo := 1008) (len := 16) (W := 301208328) check rows elimOK (by decide) (by decide) cover120831 (by decide)
  decide +kernel

theorem h120831 : P.leaf 36 120831 = 6912366263 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(153, 480076080), (133, 577666758), (126, 677919860), (103, 930470887), (139, 790684090), (121, 1107419591), (133, 931406597), (100, 1115514072), (16, 301208328)]) (.cons c120831_0 (.cons c120831_1 (.cons c120831_2 (.cons c120831_3 (.cons c120831_4 (.cons c120831_5 (.cons c120831_6 (.cons c120831_7 (.cons c120831_8 (.nil)))))))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(120829, 720), (120831, 360)]

theorem segOK : checkSeg 20 perms 120829 122742 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 120829 122742 1080 4372691630040 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 4372691630040)
    (SegSum.cons (w := 720) h120829 (SegSum.cons (w := 360) h120831 (show SegSum (P.leaf 36) [] 0 from rfl))) (by decide)

end RACert.S6N0.C0.S95
