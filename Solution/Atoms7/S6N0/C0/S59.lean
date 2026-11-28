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

namespace RACert.S6N0.C0.S59

open RACert RACert.Problem

theorem cover90077 : P.CoversSplit 26 10 90077 0xffff0000fffc0504ffff0000fffc0500ffff0000fffc0500fafa0000c8c80000050505050504050400000000000000000505050505040500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 922, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c90077_0 : P.sumLeaves 26 92238848 947 = 183832405 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90077) (lo := 0) (len := 947) (W := 183832405) check rows elimOK (by decide) (by decide) cover90077 (by decide)
  decide +kernel

theorem c90077_1 : P.sumLeaves 26 92239795 77 = 272257236 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90077) (lo := 947) (len := 77) (W := 272257236) check rows elimOK (by decide) (by decide) cover90077 (by decide)
  decide +kernel

theorem h90077 : P.leaf 36 90077 = 456089641 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(947, 183832405), (77, 272257236)]) (.cons c90077_0 (.cons c90077_1 (.nil))) (by decide) (by decide))

theorem cover90078 : P.CoversSplit 26 10 90078 0xffff0000fffc0504ffff0000fffc0500ffff0000fffc0500fafa0000c8c800000505050505040504000000000000000005050505050405000000000000000000ffff0000ffcc0504ffff0000ffcc0500ffff0000cc000400fafa0000c80000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 874, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c90078_0 : P.sumLeaves 26 92239872 511 = 146528874 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90078) (lo := 0) (len := 511) (W := 146528874) check rows elimOK (by decide) (by decide) cover90078 (by decide)
  decide +kernel

theorem c90078_1 : P.sumLeaves 26 92240383 435 = 182328926 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90078) (lo := 511) (len := 435) (W := 182328926) check rows elimOK (by decide) (by decide) cover90078 (by decide)
  decide +kernel

theorem c90078_2 : P.sumLeaves 26 92240818 78 = 220497952 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90078) (lo := 946) (len := 78) (W := 220497952) check rows elimOK (by decide) (by decide) cover90078 (by decide)
  decide +kernel

theorem h90078 : P.leaf 36 90078 = 549355752 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(511, 146528874), (435, 182328926), (78, 220497952)]) (.cons c90078_0 (.cons c90078_1 (.cons c90078_2 (.nil)))) (by decide) (by decide))

theorem cover90079 : P.CoversSplit 26 10 90079 0xffff0000fffc0504ffff0000fffc0500ffff0000fffc0500fafa0000c8c800000505050505040504000000000000000005050505050405000000000000000000ffff0000ffcc0504ffff0000ffcc0500ffff0000cc000400fafa0000c80000000505050505040504000000000000000005050505040004000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c90079_0 : P.sumLeaves 26 92240896 471 = 156307198 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90079) (lo := 0) (len := 471) (W := 156307198) check rows elimOK (by decide) (by decide) cover90079 (by decide)
  decide +kernel

theorem c90079_1 : P.sumLeaves 26 92241367 419 = 333125531 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90079) (lo := 471) (len := 419) (W := 333125531) check rows elimOK (by decide) (by decide) cover90079 (by decide)
  decide +kernel

theorem c90079_2 : P.sumLeaves 26 92241786 134 = 508326490 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90079) (lo := 890) (len := 134) (W := 508326490) check rows elimOK (by decide) (by decide) cover90079 (by decide)
  decide +kernel

theorem h90079 : P.leaf 36 90079 = 997759219 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(471, 156307198), (419, 333125531), (134, 508326490)]) (.cons c90079_0 (.cons c90079_1 (.cons c90079_2 (.nil)))) (by decide) (by decide))

theorem cover90092 : P.CoversSplit 26 10 90092 0xfffffffffffcfaf8fffffffafffcfaf8fffffffffffcfac8fafafafac8c8c8c8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [874, 922, 923, 972, 979, 1266, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f90092 (i : ℕ) := rowWeight keep4 twice4 i * P.leaf 26 (92254208 + i)

theorem c90092_0 : rowSum f90092 0 990 = 200571067 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 90092) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover90092 (by decide)
  decide +kernel

theorem c90092_1 : rowSum f90092 990 34 = 109414388 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 90092) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover90092 (by decide)
  decide +kernel

theorem sum90092 : rowSum f90092 0 1024 = 309985455 :=
  rowSum_append (F := f90092) (lo := 0) (n := 990) (m := 34) (A := 200571067) (B := 109414388) c90092_0 (c90092_1)

theorem h90092 : P.leaf 36 90092 = 309985455 :=
  leaf_weighted (k := 26) (d := 10) (H := 90092) (keep := keep4) (twice := twice4) rows (by decide) (by decide) (bal4) (invRow4 (H := 90092) (by decide) (by decide +kernel)) sum90092

theorem cover90093 : P.CoversSplit 26 10 90093 0xfffffffffffcfaf8fffffffafffcfaf8fffffffffffcfac8fafafafac8c8c8c8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [922, 923, 972, 979, 1266, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f90093 (i : ℕ) := rowWeight keep4 twice4 i * P.leaf 26 (92255232 + i)

theorem c90093_0 : rowSum f90093 0 990 = 484760557 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 90093) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover90093 (by decide)
  decide +kernel

theorem c90093_1 : rowSum f90093 990 34 = 162575144 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 90093) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover90093 (by decide)
  decide +kernel

theorem sum90093 : rowSum f90093 0 1024 = 647335701 :=
  rowSum_append (F := f90093) (lo := 0) (n := 990) (m := 34) (A := 484760557) (B := 162575144) c90093_0 (c90093_1)

theorem h90093 : P.leaf 36 90093 = 647335701 :=
  leaf_weighted (k := 26) (d := 10) (H := 90093) (keep := keep4) (twice := twice4) rows (by decide) (by decide) (bal4) (invRow4 (H := 90093) (by decide) (by decide +kernel)) sum90093

theorem cover90094 : P.CoversSplit 26 10 90094 0xfffffffffffcfaf8fffffffafffcfaf8fffffffffffcfac8fafafafac8c8c8c80000000000000000000000000000000000000000000000000000000000000000ffffffffffccfac8fffffffaffccfac8ffffffffcc00c800fafafafac800c8000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [874, 922, 972, 979, 1266, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c90094_0 : P.sumLeaves 26 92256256 424 = 81109778 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90094) (lo := 0) (len := 424) (W := 81109778) check rows elimOK (by decide) (by decide) cover90094 (by decide)
  decide +kernel

theorem c90094_1 : P.sumLeaves 26 92256680 387 = 192387560 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90094) (lo := 424) (len := 387) (W := 192387560) check rows elimOK (by decide) (by decide) cover90094 (by decide)
  decide +kernel

theorem c90094_2 : P.sumLeaves 26 92257067 116 = 210938550 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90094) (lo := 811) (len := 116) (W := 210938550) check rows elimOK (by decide) (by decide) cover90094 (by decide)
  decide +kernel

theorem c90094_3 : P.sumLeaves 26 92257183 97 = 391892392 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90094) (lo := 927) (len := 97) (W := 391892392) check rows elimOK (by decide) (by decide) cover90094 (by decide)
  decide +kernel

theorem h90094 : P.leaf 36 90094 = 876328280 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(424, 81109778), (387, 192387560), (116, 210938550), (97, 391892392)]) (.cons c90094_0 (.cons c90094_1 (.cons c90094_2 (.cons c90094_3 (.nil))))) (by decide) (by decide))

theorem cover90095 : P.CoversSplit 26 10 90095 0xfffffffffffcfaf8fffffffafffcfaf8fffffffffffcfac8fafafafac8c8c8c80000000000000000000000000000000000000000000000000000000000000000ffffffffffccfac8fffffffaffccfac8ffffffffcc00c800fafafafac800c8000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [922, 972, 979, 1266, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c90095_0 : P.sumLeaves 26 92257280 424 = 225496962 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90095) (lo := 0) (len := 424) (W := 225496962) check rows elimOK (by decide) (by decide) cover90095 (by decide)
  decide +kernel

theorem c90095_1 : P.sumLeaves 26 92257704 387 = 346914580 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90095) (lo := 424) (len := 387) (W := 346914580) check rows elimOK (by decide) (by decide) cover90095 (by decide)
  decide +kernel

theorem c90095_2 : P.sumLeaves 26 92258091 116 = 505824282 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90095) (lo := 811) (len := 116) (W := 505824282) check rows elimOK (by decide) (by decide) cover90095 (by decide)
  decide +kernel

theorem c90095_3 : P.sumLeaves 26 92258207 97 = 647564493 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90095) (lo := 927) (len := 97) (W := 647564493) check rows elimOK (by decide) (by decide) cover90095 (by decide)
  decide +kernel

theorem h90095 : P.leaf 36 90095 = 1725800317 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(424, 225496962), (387, 346914580), (116, 505824282), (97, 647564493)]) (.cons c90095_0 (.cons c90095_1 (.cons c90095_2 (.cons c90095_3 (.nil))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(90077, 720), (90078, 720), (90079, 720), (90092, 360), (90093, 360), (90094, 720), (90095, 720)]

theorem segOK : checkSeg 20 perms 90077 90110 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 90077 90110 4320 3660475526640 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 3660475526640)
    (SegSum.cons (w := 720) h90077 (SegSum.cons (w := 720) h90078 (SegSum.cons (w := 720) h90079 (SegSum.cons (w := 360) h90092 (SegSum.cons (w := 360) h90093 (SegSum.cons (w := 720) h90094 (SegSum.cons (w := 720) h90095 (show SegSum (P.leaf 36) [] 0 from rfl)))))))) (by decide)

end RACert.S6N0.C0.S59
