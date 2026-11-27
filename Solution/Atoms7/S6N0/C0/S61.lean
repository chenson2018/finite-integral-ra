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

namespace RACert.S6N0.C0.S61

open RACert RACert.Problem

theorem cover89055 : P.CoversSplit 26 10 89055 0xffff0000fffc0504ffff0000fffc0500ffff0000fffc0500fafa0000c8c800000505050505040504000000000000000005050505050405000000000000000000ffff0000ffcc0504ffff0000ffcc0500ffff0000cc000400fafa0000c80000000505050505040504000000000000000005050505040004000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 922, 972, 979, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c89055_0 : P.sumLeaves 26 91192320 192 = 45600 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89055) (lo := 0) (len := 192) (W := 45600) check rows elimOK (by decide) (by decide) cover89055 (by decide)
  decide +kernel

theorem contract89055_1 : P.leaf 32 1424883 = 78160 := by
  exact leaf_contract_factors (k := 32) (b := 19) (H := 1424883) (ss := [(22, 1, 433), (2, 1, 482), (3, 1, 531), (4, 1, 580), (5, 1, 629), (6, 1, 636), (7, 1, 825), (8, 1, 1217), (28, 0, 1315), (30, 0, 1315), (15, 1, 922), (9, 1, 1609), (21, 1, 1658)]) (ids := [8, 9, 10, 12, 14, 15, 16, 17, 18, 21, 24, 25, 27, 29, 30, 31, 11, 22, 23]) (cs := [1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 18, 5, 1, 6, 7, 8, 9, 10, 1, 1, 11, 19, 20, 12, 13, 0, 14, 0, 15, 16, 17]) (bs := [16, 3]) (W := 78160) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c89055_1 : P.sumLeaves 26 91192512 64 = 78160 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1424883) rows (by decide) (by decide)).symm.trans contract89055_1

theorem c89055_2 : P.sumLeaves 26 91192576 255 = 161594568 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89055) (lo := 256) (len := 255) (W := 161594568) check rows elimOK (by decide) (by decide) cover89055 (by decide)
  decide +kernel

theorem c89055_3 : P.sumLeaves 26 91192831 435 = 258456442 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89055) (lo := 511) (len := 435) (W := 258456442) check rows elimOK (by decide) (by decide) cover89055 (by decide)
  decide +kernel

theorem c89055_4 : P.sumLeaves 26 91193266 78 = 265332076 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89055) (lo := 946) (len := 78) (W := 265332076) check rows elimOK (by decide) (by decide) cover89055 (by decide)
  decide +kernel

theorem h89055 : P.leaf 36 89055 = 685506846 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(192, 45600), (64, 78160), (255, 161594568), (435, 258456442), (78, 265332076)]) (.cons c89055_0 (.cons c89055_1 (.cons c89055_2 (.cons c89055_3 (.cons c89055_4 (.nil)))))) (by decide) (by decide))

theorem cover89069 : P.CoversSplit 26 10 89069 0xfffffffffffcfaf8fffffffafffcfaf8fffffffffffcfac8fafafafac8c8c8c8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [922, 923, 972, 979, 1266, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f89069 (i : ℕ) := rowWeight keep4 twice4 i * P.leaf 26 (91206656 + i)

theorem c89069_0 : rowSum f89069 0 990 = 10704058 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 89069) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover89069 (by decide)
  decide +kernel

theorem c89069_1 : rowSum f89069 990 34 = 2210784 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 89069) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover89069 (by decide)
  decide +kernel

theorem sum89069 : rowSum f89069 0 1024 = 12914842 :=
  rowSum_append (F := f89069) (lo := 0) (n := 990) (m := 34) (A := 10704058) (B := 2210784) c89069_0 (c89069_1)

theorem h89069 : P.leaf 36 89069 = 12914842 :=
  leaf_weighted (k := 26) (d := 10) (H := 89069) (keep := keep4) (twice := twice4) rows (by decide) (by decide) bal4 (invRow4 (H := 89069) (by decide) (by decide +kernel)) sum89069

theorem cover89070 : P.CoversSplit 26 10 89070 0xfffffffffffcfaf8fffffffafffcfaf8fffffffffffcfac8fafafafac8c8c8c80000000000000000000000000000000000000000000000000000000000000000ffffffffffccfac8fffffffaffccfac8ffffffff00000000fafafafa000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [874, 922, 972, 979, 1266, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c89070_0 : P.sumLeaves 26 91207680 437 = 2966312 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89070) (lo := 0) (len := 437) (W := 2966312) check rows elimOK (by decide) (by decide) cover89070 (by decide)
  decide +kernel

theorem c89070_1 : P.sumLeaves 26 91208117 391 = 7965314 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89070) (lo := 437) (len := 391) (W := 7965314) check rows elimOK (by decide) (by decide) cover89070 (by decide)
  decide +kernel

theorem c89070_2 : P.sumLeaves 26 91208508 114 = 11275284 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89070) (lo := 828) (len := 114) (W := 11275284) check rows elimOK (by decide) (by decide) cover89070 (by decide)
  decide +kernel

theorem c89070_3 : P.sumLeaves 26 91208622 82 = 21833200 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89070) (lo := 942) (len := 82) (W := 21833200) check rows elimOK (by decide) (by decide) cover89070 (by decide)
  decide +kernel

theorem h89070 : P.leaf 36 89070 = 44040110 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(437, 2966312), (391, 7965314), (114, 11275284), (82, 21833200)]) (.cons c89070_0 (.cons c89070_1 (.cons c89070_2 (.cons c89070_3 (.nil))))) (by decide) (by decide))

theorem cover89071 : P.CoversSplit 26 10 89071 0xfffffffffffcfaf8fffffffafffcfaf8fffffffffffcfac8fafafafac8c8c8c80000000000000000000000000000000000000000000000000000000000000000ffffffffffccfac8fffffffaffccfac8ffffffff00000000fafafafa000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [922, 972, 979, 1266, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c89071_0 : P.sumLeaves 26 91208704 437 = 13092254 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89071) (lo := 0) (len := 437) (W := 13092254) check rows elimOK (by decide) (by decide) cover89071 (by decide)
  decide +kernel

theorem c89071_1 : P.sumLeaves 26 91209141 391 = 22321634 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89071) (lo := 437) (len := 391) (W := 22321634) check rows elimOK (by decide) (by decide) cover89071 (by decide)
  decide +kernel

theorem c89071_2 : P.sumLeaves 26 91209532 114 = 40833004 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89071) (lo := 828) (len := 114) (W := 40833004) check rows elimOK (by decide) (by decide) cover89071 (by decide)
  decide +kernel

theorem c89071_3 : P.sumLeaves 26 91209646 82 = 45303436 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89071) (lo := 942) (len := 82) (W := 45303436) check rows elimOK (by decide) (by decide) cover89071 (by decide)
  decide +kernel

theorem h89071 : P.leaf 36 89071 = 121550328 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(437, 13092254), (391, 22321634), (114, 40833004), (82, 45303436)]) (.cons c89071_0 (.cons c89071_1 (.cons c89071_2 (.cons c89071_3 (.nil))))) (by decide) (by decide))

theorem cover89086 : P.CoversSplit 26 10 89086 0xfffffffffffcfaf8fffffffafffcfaf8fffffffffffcfac8fafafafac8c8c8c8fffffafafffcfaf8fafafafafaf8faf8fffffafafffcfac8fafafafac8c8c8c8ffffffffffccfac8fffffffaffccfac8ffffffffccccc8c8fafafafac8c8c8c80000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [874, 922, 972, 979, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f89086 (i : ℕ) := rowWeight keep4 twice4 i * P.leaf 26 (91224064 + i)

theorem c89086_0 : rowSum f89086 0 409 = 167064086 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 89086) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover89086 (by decide)
  decide +kernel

theorem c89086_1 : rowSum f89086 409 381 = 416470902 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 89086) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover89086 (by decide)
  decide +kernel

theorem c89086_2 : rowSum f89086 790 215 = 508868275 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 89086) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover89086 (by decide)
  decide +kernel

theorem c89086_3 : rowSum f89086 1005 19 = 107892396 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 89086) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover89086 (by decide)
  decide +kernel

theorem sum89086 : rowSum f89086 0 1024 = 1200295659 :=
  rowSum_append (F := f89086) (lo := 0) (n := 409) (m := 615) (A := 167064086) (B := 1033231573) c89086_0 (rowSum_append (F := f89086) (lo := 409) (n := 381) (m := 234) (A := 416470902) (B := 616760671) c89086_1 (rowSum_append (F := f89086) (lo := 790) (n := 215) (m := 19) (A := 508868275) (B := 107892396) c89086_2 (c89086_3)))

theorem h89086 : P.leaf 36 89086 = 1200295659 :=
  leaf_weighted (k := 26) (d := 10) (H := 89086) (keep := keep4) (twice := twice4) rows (by decide) (by decide) bal4 (invRow4 (H := 89086) (by decide) (by decide +kernel)) sum89086

theorem cover89087 : P.CoversSplit 26 10 89087 0xfffffffffffcfaf8fffffffafffcfaf8fffffffffffcfac8fafafafac8c8c8c8fffffafafffcfaf8fafafafafaf8faf8fffffafafffcfac8fafafafac8c8c8c8ffffffffffccfac8fffffffaffccfac8ffffffffccccc8c8fafafafac8c8c8c8fffffafaffccfac8fafafafafac8fac8fffffafaccccc8c8fafafafac8c8c8c8 :=
  coversSplit check rows (by decide) (by decide) (xs := [922, 972, 979, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f89087 (i : ℕ) := rowWeight keep4 twice4 i * P.leaf 26 (91225088 + i)

theorem c89087_0 : rowSum f89087 0 271 = 47635573 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 89087) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover89087 (by decide)
  decide +kernel

theorem c89087_1 : rowSum f89087 271 143 = 797405664 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 89087) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover89087 (by decide)
  decide +kernel

theorem c89087_2 : rowSum f89087 414 390 = 1113020000 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 89087) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover89087 (by decide)
  decide +kernel

theorem c89087_3 : rowSum f89087 804 219 = 1642824257 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 89087) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover89087 (by decide)
  decide +kernel

theorem c89087_4 : rowSum f89087 1023 1 = 18749528 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 89087) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover89087 (by decide)
  decide +kernel

theorem sum89087 : rowSum f89087 0 1024 = 3619635022 :=
  rowSum_append (F := f89087) (lo := 0) (n := 271) (m := 753) (A := 47635573) (B := 3571999449) c89087_0 (rowSum_append (F := f89087) (lo := 271) (n := 143) (m := 610) (A := 797405664) (B := 2774593785) c89087_1 (rowSum_append (F := f89087) (lo := 414) (n := 390) (m := 220) (A := 1113020000) (B := 1661573785) c89087_2 (rowSum_append (F := f89087) (lo := 804) (n := 219) (m := 1) (A := 1642824257) (B := 18749528) c89087_3 (c89087_4))))

theorem h89087 : P.leaf 36 89087 = 3619635022 :=
  leaf_weighted (k := 26) (d := 10) (H := 89087) (keep := keep4) (twice := twice4) rows (by decide) (by decide) bal4 (invRow4 (H := 89087) (by decide) (by decide +kernel)) sum89087

def seg : List (ℕ × ℕ) := [(89055, 720), (89069, 360), (89070, 720), (89071, 720), (89086, 360), (89087, 360)]

theorem segOK : checkSeg 20 perms 89055 89559 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 89055 89559 3240 2352614432760 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 2352614432760)
    (SegSum.cons (w := 720) h89055 (SegSum.cons (w := 360) h89069 (SegSum.cons (w := 720) h89070 (SegSum.cons (w := 720) h89071 (SegSum.cons (w := 360) h89086 (SegSum.cons (w := 360) h89087 (show SegSum (P.leaf 36) [] 0 from rfl))))))) (by decide)

end RACert.S6N0.C0.S61
