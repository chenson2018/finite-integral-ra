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

namespace RACert.S6N0.C0.S94

open RACert RACert.Problem

theorem cover120823 : P.CoversSplit 26 10 120823 0xfffffffffffffafafffffffffffffafaffffffffffffc8c8fafafafac8c8c8c8fffffafafffffafafafafafafafafafafffffafaffffc8c8fafafafac8c8c8c8fffffffffffffafafffffffffffffafaffffffffccccc8c8fafafafac8c8c8c8fffffafafffffafafafafafafafafafafffffafaccccc8c8fafafafac8c8c8c8 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 873, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c120823_0 : P.sumLeaves 26 123722752 153 = 112435020 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120823) (lo := 0) (len := 153) (W := 112435020) check rows elimOK (by decide) (by decide) cover120823 (by decide)
  decide +kernel

theorem c120823_1 : P.sumLeaves 26 123722905 133 = 153478956 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120823) (lo := 153) (len := 133) (W := 153478956) check rows elimOK (by decide) (by decide) cover120823 (by decide)
  decide +kernel

theorem c120823_2 : P.sumLeaves 26 123723038 126 = 314144661 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120823) (lo := 286) (len := 126) (W := 314144661) check rows elimOK (by decide) (by decide) cover120823 (by decide)
  decide +kernel

theorem c120823_3 : P.sumLeaves 26 123723164 103 = 502455980 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120823) (lo := 412) (len := 103) (W := 502455980) check rows elimOK (by decide) (by decide) cover120823 (by decide)
  decide +kernel

theorem c120823_4 : P.sumLeaves 26 123723267 139 = 299698117 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120823) (lo := 515) (len := 139) (W := 299698117) check rows elimOK (by decide) (by decide) cover120823 (by decide)
  decide +kernel

theorem c120823_5 : P.sumLeaves 26 123723406 121 = 482416863 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120823) (lo := 654) (len := 121) (W := 482416863) check rows elimOK (by decide) (by decide) cover120823 (by decide)
  decide +kernel

theorem c120823_6 : P.sumLeaves 26 123723527 133 = 435003166 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120823) (lo := 775) (len := 133) (W := 435003166) check rows elimOK (by decide) (by decide) cover120823 (by decide)
  decide +kernel

theorem c120823_7 : P.sumLeaves 26 123723660 100 = 577658038 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120823) (lo := 908) (len := 100) (W := 577658038) check rows elimOK (by decide) (by decide) cover120823 (by decide)
  decide +kernel

theorem c120823_8 : P.sumLeaves 26 123723760 16 = 163857692 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120823) (lo := 1008) (len := 16) (W := 163857692) check rows elimOK (by decide) (by decide) cover120823 (by decide)
  decide +kernel

theorem h120823 : P.leaf 36 120823 = 3041148493 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(153, 112435020), (133, 153478956), (126, 314144661), (103, 502455980), (139, 299698117), (121, 482416863), (133, 435003166), (100, 577658038), (16, 163857692)]) (.cons c120823_0 (.cons c120823_1 (.cons c120823_2 (.cons c120823_3 (.cons c120823_4 (.cons c120823_5 (.cons c120823_6 (.cons c120823_7 (.cons c120823_8 (.nil)))))))))) (by decide) (by decide))

theorem cover120827 : P.CoversSplit 26 10 120827 0xf0f00000f0f000000000000000000000f0f00000f0f000000000000000000000f0f00000f0f000000000505000005050f0f00000f0f000000000505000004040f0f00000f0f000000000000000000000f0f00000c0c000000000000000000000f0f00000f0f000000000505000005050f0f00000c0c000000000505000004040 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 873, 922, 1273, 1322]) (by decide +kernel)

theorem c120827_0 : P.sumLeaves 26 123726848 676 = 236254225 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120827) (lo := 0) (len := 676) (W := 236254225) check rows elimOK (by decide) (by decide) cover120827 (by decide)
  decide +kernel

theorem c120827_1 : P.sumLeaves 26 123727524 348 = 410647114 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120827) (lo := 676) (len := 348) (W := 410647114) check rows elimOK (by decide) (by decide) cover120827 (by decide)
  decide +kernel

theorem h120827 : P.leaf 36 120827 = 646901339 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(676, 236254225), (348, 410647114)]) (.cons c120827_0 (.cons c120827_1 (.nil))) (by decide) (by decide))

theorem cover120828 : P.CoversSplit 26 10 120828 0xfffffffffffffafafffffffffffffafaffffffffffffc8c8fafafafac8c8c8c8fffffafafffffafafafaf0f0fafaf0f0fffffafaffffc8c8fafaf0f0c8c8c0c0fffffffffffffafafffffffffffffafaffffffffccccc8c8fafafafac8c8c8c8fffffafafffffafafafaf0f0fafaf0f0fffffafaccccc8c8fafaf0f0c8c8c0c0 :=
  coversSplit check rows (by decide) (by decide) (xs := [873, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c120828_0 : P.sumLeaves 26 123727872 172 = 20512756 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120828) (lo := 0) (len := 172) (W := 20512756) check rows elimOK (by decide) (by decide) cover120828 (by decide)
  decide +kernel

theorem c120828_1 : P.sumLeaves 26 123728044 133 = 28312739 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120828) (lo := 172) (len := 133) (W := 28312739) check rows elimOK (by decide) (by decide) cover120828 (by decide)
  decide +kernel

theorem c120828_2 : P.sumLeaves 26 123728177 121 = 54670911 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120828) (lo := 305) (len := 121) (W := 54670911) check rows elimOK (by decide) (by decide) cover120828 (by decide)
  decide +kernel

theorem c120828_3 : P.sumLeaves 26 123728298 130 = 99822664 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120828) (lo := 426) (len := 130) (W := 99822664) check rows elimOK (by decide) (by decide) cover120828 (by decide)
  decide +kernel

theorem c120828_4 : P.sumLeaves 26 123728428 136 = 107918384 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120828) (lo := 556) (len := 136) (W := 107918384) check rows elimOK (by decide) (by decide) cover120828 (by decide)
  decide +kernel

theorem c120828_5 : P.sumLeaves 26 123728564 133 = 225091961 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120828) (lo := 692) (len := 133) (W := 225091961) check rows elimOK (by decide) (by decide) cover120828 (by decide)
  decide +kernel

theorem c120828_6 : P.sumLeaves 26 123728697 111 = 149884833 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120828) (lo := 825) (len := 111) (W := 149884833) check rows elimOK (by decide) (by decide) cover120828 (by decide)
  decide +kernel

theorem c120828_7 : P.sumLeaves 26 123728808 88 = 316078649 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120828) (lo := 936) (len := 88) (W := 316078649) check rows elimOK (by decide) (by decide) cover120828 (by decide)
  decide +kernel

theorem h120828 : P.leaf 36 120828 = 1002292897 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(172, 20512756), (133, 28312739), (121, 54670911), (130, 99822664), (136, 107918384), (133, 225091961), (111, 149884833), (88, 316078649)]) (.cons c120828_0 (.cons c120828_1 (.cons c120828_2 (.cons c120828_3 (.cons c120828_4 (.cons c120828_5 (.cons c120828_6 (.cons c120828_7 (.nil))))))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(120823, 360), (120827, 360), (120828, 360)]

theorem segOK : checkSeg 20 perms 120823 120829 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 120823 120829 1080 1688523382440 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 1688523382440)
    (SegSum.cons (w := 360) h120823 (SegSum.cons (w := 360) h120827 (SegSum.cons (w := 360) h120828 (show SegSum (P.leaf 36) [] 0 from rfl)))) (by decide)

end RACert.S6N0.C0.S94
