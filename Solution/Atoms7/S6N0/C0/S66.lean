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

namespace RACert.S6N0.C0.S66

open RACert RACert.Problem

theorem cover90079 : P.CoversSplit 26 10 90079 0xffff0000fffc0504ffff0000fffc0500ffff0000fffc0500fafa0000c8c800000505050505040504000000000000000005050505050405000000000000000000ffff0000ffcc0504ffff0000ffcc0500ffff0000cc000400fafa0000c80000000505050505040504000000000000000005050505040004000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c90079_0 : P.sumLeaves 26 92240896 192 = 123684 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90079) (lo := 0) (len := 192) (W := 123684) check rows elimOK (by decide) (by decide) cover90079 (by decide)
  decide +kernel

theorem contract90079_1 : P.leaf 32 1441267 = 194704 := by
  exact leaf_contract_factors (k := 32) (b := 20) (H := 1441267) (ss := [(22, 1, 433), (2, 1, 482), (3, 1, 531), (4, 1, 580), (5, 1, 629), (6, 1, 636), (7, 1, 825), (8, 1, 1217), (28, 0, 1315), (30, 0, 1315), (9, 1, 1609), (21, 1, 1658)]) (ids := [8, 9, 10, 13, 14, 15, 16, 17, 18, 21, 23, 24, 25, 27, 29, 30, 31, 11, 12, 22]) (cs := [1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 19, 20, 5, 6, 7, 8, 9, 10, 1, 1, 11, 21, 12, 13, 14, 0, 15, 0, 16, 17, 18]) (bs := [17, 3]) (W := 194704) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c90079_1 : P.sumLeaves 26 92241088 64 = 194704 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1441267) rows (by decide) (by decide)).symm.trans contract90079_1

theorem c90079_2 : P.sumLeaves 26 92241152 255 = 235590950 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90079) (lo := 256) (len := 255) (W := 235590950) check rows elimOK (by decide) (by decide) cover90079 (by decide)
  decide +kernel

theorem c90079_3 : P.sumLeaves 26 92241407 435 = 385175936 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90079) (lo := 511) (len := 435) (W := 385175936) check rows elimOK (by decide) (by decide) cover90079 (by decide)
  decide +kernel

theorem c90079_4 : P.sumLeaves 26 92241842 78 = 376673945 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90079) (lo := 946) (len := 78) (W := 376673945) check rows elimOK (by decide) (by decide) cover90079 (by decide)
  decide +kernel

theorem h90079 : P.leaf 36 90079 = 997759219 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(192, 123684), (64, 194704), (255, 235590950), (435, 385175936), (78, 376673945)]) (.cons c90079_0 (.cons c90079_1 (.cons c90079_2 (.cons c90079_3 (.cons c90079_4 (.nil)))))) (by decide) (by decide))

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
  leaf_weighted (k := 26) (d := 10) (H := 90092) (keep := keep4) (twice := twice4) rows (by decide) (by decide) bal4 (invRow4 (H := 90092) (by decide) (by decide +kernel)) sum90092

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
  leaf_weighted (k := 26) (d := 10) (H := 90093) (keep := keep4) (twice := twice4) rows (by decide) (by decide) bal4 (invRow4 (H := 90093) (by decide) (by decide +kernel)) sum90093

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

theorem cover90110 : P.CoversSplit 26 10 90110 0xfffffffffffcfaf8fffffffafffcfaf8fffffffffffcfac8fafafafac8c8c8c8fffffafafffcfaf8fafafafafaf8faf8fffffafafffcfac8fafafafac8c8c8c8ffffffffffccfac8fffffffaffccfac8ffffffffccccc8c8fafafafac8c8c8c80000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [874, 922, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f90110 (i : ℕ) := rowWeight keep4 twice4 i * P.leaf 26 (92272640 + i)

theorem c90110_0 : rowSum f90110 0 409 = 389948472 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 90110) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover90110 (by decide)
  decide +kernel

theorem c90110_1 : rowSum f90110 409 381 = 807684308 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 90110) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover90110 (by decide)
  decide +kernel

theorem c90110_2 : rowSum f90110 790 215 = 1032471574 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 90110) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover90110 (by decide)
  decide +kernel

theorem c90110_3 : rowSum f90110 1005 19 = 169497152 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 90110) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover90110 (by decide)
  decide +kernel

theorem sum90110 : rowSum f90110 0 1024 = 2399601506 :=
  rowSum_append (F := f90110) (lo := 0) (n := 409) (m := 615) (A := 389948472) (B := 2009653034) c90110_0 (rowSum_append (F := f90110) (lo := 409) (n := 381) (m := 234) (A := 807684308) (B := 1201968726) c90110_1 (rowSum_append (F := f90110) (lo := 790) (n := 215) (m := 19) (A := 1032471574) (B := 169497152) c90110_2 (c90110_3)))

theorem h90110 : P.leaf 36 90110 = 2399601506 :=
  leaf_weighted (k := 26) (d := 10) (H := 90110) (keep := keep4) (twice := twice4) rows (by decide) (by decide) bal4 (invRow4 (H := 90110) (by decide) (by decide +kernel)) sum90110

def seg : List (ℕ × ℕ) := [(90079, 720), (90092, 360), (90093, 360), (90094, 720), (90095, 720), (90110, 360)]

theorem segOK : checkSeg 20 perms 90079 90111 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 90079 90111 3240 3800411385840 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 3800411385840)
    (SegSum.cons (w := 720) h90079 (SegSum.cons (w := 360) h90092 (SegSum.cons (w := 360) h90093 (SegSum.cons (w := 720) h90094 (SegSum.cons (w := 720) h90095 (SegSum.cons (w := 360) h90110 (show SegSum (P.leaf 36) [] 0 from rfl))))))) (by decide)

end RACert.S6N0.C0.S66
