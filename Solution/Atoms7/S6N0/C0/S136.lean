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

namespace RACert.S6N0.C0.S136

open RACert RACert.Problem

theorem cover245738 : P.CoversSplit 26 10 245738 0xfffffffffffffffffffffffffffffafaffffffffffffffccffffaaaaffccaa88fffffffffffffffffafaaaaafafaaaaaffffffffffffffccfafaaaaafac8aa88fffffffffffffffffffffffffffffafaffffffffffccffccffffaaaaffccaa88fffffffffffffffffafaaaaafafaaaaaffffffffffccffccfafaaaaafac8aa88 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 930, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c245738_0 : P.sumLeaves 26 251635712 139 = 16189024 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245738) (lo := 0) (len := 139) (W := 16189024) check rows elimOK (by decide) (by decide) cover245738 (by decide)
  decide +kernel

theorem c245738_1 : P.sumLeaves 26 251635851 114 = 39393780 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245738) (lo := 139) (len := 114) (W := 39393780) check rows elimOK (by decide) (by decide) cover245738 (by decide)
  decide +kernel

theorem c245738_2 : P.sumLeaves 26 251635965 126 = 123218786 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245738) (lo := 253) (len := 126) (W := 123218786) check rows elimOK (by decide) (by decide) cover245738 (by decide)
  decide +kernel

theorem c245738_3 : P.sumLeaves 26 251636091 100 = 324177964 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245738) (lo := 379) (len := 100) (W := 324177964) check rows elimOK (by decide) (by decide) cover245738 (by decide)
  decide +kernel

theorem c245738_4 : P.sumLeaves 26 251636191 129 = 314881170 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245738) (lo := 479) (len := 129) (W := 314881170) check rows elimOK (by decide) (by decide) cover245738 (by decide)
  decide +kernel

theorem c245738_5 : P.sumLeaves 26 251636320 120 = 424469842 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245738) (lo := 608) (len := 120) (W := 424469842) check rows elimOK (by decide) (by decide) cover245738 (by decide)
  decide +kernel

theorem c245738_6 : P.sumLeaves 26 251636440 122 = 484411504 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245738) (lo := 728) (len := 122) (W := 484411504) check rows elimOK (by decide) (by decide) cover245738 (by decide)
  decide +kernel

theorem c245738_7 : P.sumLeaves 26 251636562 100 = 544230314 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245738) (lo := 850) (len := 100) (W := 544230314) check rows elimOK (by decide) (by decide) cover245738 (by decide)
  decide +kernel

theorem c245738_8 : P.sumLeaves 26 251636662 74 = 801002456 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245738) (lo := 950) (len := 74) (W := 801002456) check rows elimOK (by decide) (by decide) cover245738 (by decide)
  decide +kernel

theorem h245738 : P.leaf 36 245738 = 3071974840 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(139, 16189024), (114, 39393780), (126, 123218786), (100, 324177964), (129, 314881170), (120, 424469842), (122, 484411504), (100, 544230314), (74, 801002456)]) (.cons c245738_0 (.cons c245738_1 (.cons c245738_2 (.cons c245738_3 (.cons c245738_4 (.cons c245738_5 (.cons c245738_6 (.cons c245738_7 (.cons c245738_8 (.nil)))))))))) (by decide) (by decide))

theorem cover245739 : P.CoversSplit 26 10 245739 0xfffffffffffffffffffffffffffffafaffffffffffffffccffffaaaaffccaa88ffffffffffffffffffffaaaaffffaaaaffffffffffffffccffffaaaaffccaa88fffffffffffffffffffffffffffffafaffffffffffccffccffffaaaaffccaa88ffffffffffffffffffffaaaaffffaaaaffffffffffccffccffffaaaaffccaa88 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 930, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c245739_0 : P.sumLeaves 26 251636736 126 = 61342882 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245739) (lo := 0) (len := 126) (W := 61342882) check rows elimOK (by decide) (by decide) cover245739 (by decide)
  decide +kernel

theorem c245739_1 : P.sumLeaves 26 251636862 112 = 159178048 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245739) (lo := 126) (len := 112) (W := 159178048) check rows elimOK (by decide) (by decide) cover245739 (by decide)
  decide +kernel

theorem c245739_2 : P.sumLeaves 26 251636974 126 = 218955084 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245739) (lo := 238) (len := 126) (W := 218955084) check rows elimOK (by decide) (by decide) cover245739 (by decide)
  decide +kernel

theorem c245739_3 : P.sumLeaves 26 251637100 100 = 584533776 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245739) (lo := 364) (len := 100) (W := 584533776) check rows elimOK (by decide) (by decide) cover245739 (by decide)
  decide +kernel

theorem c245739_4 : P.sumLeaves 26 251637200 122 = 579629018 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245739) (lo := 464) (len := 122) (W := 579629018) check rows elimOK (by decide) (by decide) cover245739 (by decide)
  decide +kernel

theorem c245739_5 : P.sumLeaves 26 251637322 112 = 707577390 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245739) (lo := 586) (len := 112) (W := 707577390) check rows elimOK (by decide) (by decide) cover245739 (by decide)
  decide +kernel

theorem c245739_6 : P.sumLeaves 26 251637434 118 = 1091666116 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245739) (lo := 698) (len := 118) (W := 1091666116) check rows elimOK (by decide) (by decide) cover245739 (by decide)
  decide +kernel

theorem c245739_7 : P.sumLeaves 26 251637552 104 = 801888838 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245739) (lo := 816) (len := 104) (W := 801888838) check rows elimOK (by decide) (by decide) cover245739 (by decide)
  decide +kernel

theorem c245739_8 : P.sumLeaves 26 251637656 96 = 1848609882 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245739) (lo := 920) (len := 96) (W := 1848609882) check rows elimOK (by decide) (by decide) cover245739 (by decide)
  decide +kernel

theorem c245739_9 : P.sumLeaves 26 251637752 8 = 194614256 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245739) (lo := 1016) (len := 8) (W := 194614256) check rows elimOK (by decide) (by decide) cover245739 (by decide)
  decide +kernel

theorem h245739 : P.leaf 36 245739 = 6247995290 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(126, 61342882), (112, 159178048), (126, 218955084), (100, 584533776), (122, 579629018), (112, 707577390), (118, 1091666116), (104, 801888838), (96, 1848609882), (8, 194614256)]) (.cons c245739_0 (.cons c245739_1 (.cons c245739_2 (.cons c245739_3 (.cons c245739_4 (.cons c245739_5 (.cons c245739_6 (.cons c245739_7 (.cons c245739_8 (.cons c245739_9 (.nil))))))))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(245738, 180), (245739, 360)]

theorem segOK : checkSeg 20 perms 245738 245742 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 245738 245742 540 2802233775600 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 2802233775600)
    (SegSum.cons (w := 180) h245738 (SegSum.cons (w := 360) h245739 (show SegSum (P.leaf 36) [] 0 from rfl))) (by decide)

end RACert.S6N0.C0.S136
