/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Atoms7.S4N1.C0.Actions

/-! Generated identity-class certificate for the product-row count. -/

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option Elab.async false

@[expose] public section

namespace RACert.S4N1.C0.S21

open RACert RACert.Problem

theorem cover3789 : P.CoversSplit 24 10 3789 0xcc00cc00c4000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 515, 522, 536, 573, 915, 1202, 1210, 1217, 1651]) (ps := [(14, [929], [1266])]) (by decide +kernel)

theorem h3789 : P.leaf 34 3789 = 605096 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 3789) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 3789) (weight := fun _ => 1) (xs := [986, 990, 991, 1002, 1003, 1006, 1007, 1018, 1019, 1022, 1023]) check rows elimOK (by decide) (by decide) cover3789 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3790 : P.CoversSplit 24 10 3790 0xaa000000a10000000000000000000000aa000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 515, 516, 522, 536, 916, 921, 1202, 1258]) (by decide +kernel)

theorem h3790 : P.leaf 34 3790 = 957728 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 3790) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 3790) (weight := fun _ => 1) (xs := [889, 891, 893, 895, 984, 989, 991, 1017, 1019, 1021, 1023]) check rows elimOK (by decide) (by decide) cover3790 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover34943 : P.CoversSplit 24 10 34943 0xcc00c800c8000000cc00c800c8000000cc00c800c8000000cc00c800c8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [572, 573, 578, 858, 859, 866, 915, 1202, 1209]) (by decide +kernel)

theorem c34943_0 : P.sumLeaves 24 35781632 1024 = 7870452 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 34943) (lo := 0) (len := 1024) (W := 7870452) check rows elimOK (by decide) (by decide) cover34943 (by decide)
  decide +kernel

theorem h34943 : P.leaf 34 34943 = 7870452 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 7870452)]) (.cons c34943_0 (.nil)) (by decide) (by decide))

theorem h3791 : P.leaf 34 3791 = 7870452 :=
  orient5 (v := 34943) (by decide) (by decide +kernel) h34943

theorem cover35422 : P.CoversSplit 24 10 35422 0xcc00cc00c8000000cc00cc00c8000000cc00cc0000000000cc000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00c80000000000000000000000cc00cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 516, 523, 536, 572, 573, 578, 879, 915, 1202, 1217, 1251, 1258, 1308]) (by decide +kernel)

def k35422 : ℕ := 0x8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cefffffffffffffffff8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef
def t35422 : ℕ := 0x8ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce000000000000000008ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce

noncomputable def f35422 (i : ℕ) := rowWeight k35422 t35422 i * P.leaf 24 (36272128 + i)

theorem c35422_0 : rowSum f35422 0 320 = 0 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 35422) (keep := k35422) (twice := t35422) check rows elimOK (by decide) (by decide) cover35422 (by decide)
  decide +kernel

theorem contract35422_1 : P.leaf 30 566757 = 0 := by
  exact leaf_contract_zero (ss := [(27, 1, 578), (29, 1, 915), (8, 0, 1272), (10, 1, 467), (20, 1, 531), (21, 0, 537), (14, 1, 580)]) (q := 586) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c35422_1 : rowSum f35422 320 64 = 0 :=
  (rowSum_unit_block (P := P) (keep := k35422) (twice := t35422) (by decide +kernel)).trans ((leaf_eq_inner (k := 24) (d := 6) (H := 566757) rows (by decide) (by decide)).symm.trans contract35422_1)

theorem c35422_2 : rowSum f35422 384 640 = 2113282 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 35422) (keep := k35422) (twice := t35422) check rows elimOK (by decide) (by decide) cover35422 (by decide)
  decide +kernel

theorem sum35422 : rowSum f35422 0 1024 = 2113282 :=
  rowSum_append (F := f35422) (lo := 0) (n := 320) (m := 704) (A := 0) (B := 2113282) c35422_0 (rowSum_append (F := f35422) (lo := 320) (n := 64) (m := 640) (A := 0) (B := 2113282) c35422_1 (c35422_2))

theorem h35422 : P.leaf 34 35422 = 2113282 :=
  leaf_weighted (k := 24) (d := 10) (H := 35422) (keep := k35422) (twice := t35422) rows (by decide) (by decide) (balancedRows_of_check (by decide +kernel)) (invRow2 (H := 35422) (by decide) (by decide +kernel)) sum35422

theorem h3802 : P.leaf 34 3802 = 2113282 :=
  orient5 (v := 35422) (by decide) (by decide +kernel) h35422

theorem cover35423 : P.CoversSplit 24 10 35423 0xcc00cc00c8000000cc00cc00c8000000cc00cc0000000000cc000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00c80000000000000000000000cc00cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [516, 523, 536, 572, 573, 578, 879, 915, 1202, 1217, 1251, 1258, 1308]) (by decide +kernel)

def k35423 : ℕ := 0x8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cefffffffffffffffff8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef
def t35423 : ℕ := 0x8ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce000000000000000008ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce

noncomputable def f35423 (i : ℕ) := rowWeight k35423 t35423 i * P.leaf 24 (36273152 + i)

theorem c35423_0 : rowSum f35423 0 320 = 0 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 35423) (keep := k35423) (twice := t35423) check rows elimOK (by decide) (by decide) cover35423 (by decide)
  decide +kernel

theorem contract35423_1 : P.leaf 30 566773 = 0 := by
  exact leaf_contract_zero (ss := [(27, 1, 578), (29, 1, 915), (8, 0, 1272), (14, 0, 537), (5, 1, 433), (20, 1, 531), (21, 0, 537)]) (q := 580) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c35423_1 : rowSum f35423 320 64 = 0 :=
  (rowSum_unit_block (P := P) (keep := k35423) (twice := t35423) (by decide +kernel)).trans ((leaf_eq_inner (k := 24) (d := 6) (H := 566773) rows (by decide) (by decide)).symm.trans contract35423_1)

theorem c35423_2 : rowSum f35423 384 640 = 5345450 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 35423) (keep := k35423) (twice := t35423) check rows elimOK (by decide) (by decide) cover35423 (by decide)
  decide +kernel

theorem sum35423 : rowSum f35423 0 1024 = 5345450 :=
  rowSum_append (F := f35423) (lo := 0) (n := 320) (m := 704) (A := 0) (B := 5345450) c35423_0 (rowSum_append (F := f35423) (lo := 320) (n := 64) (m := 640) (A := 0) (B := 5345450) c35423_1 (c35423_2))

theorem h35423 : P.leaf 34 35423 = 5345450 :=
  leaf_weighted (k := 24) (d := 10) (H := 35423) (keep := k35423) (twice := t35423) rows (by decide) (by decide) (balancedRows_of_check (by decide +kernel)) (invRow2 (H := 35423) (by decide) (by decide +kernel)) sum35423

theorem h3803 : P.leaf 34 3803 = 5345450 :=
  orient5 (v := 35423) (by decide) (by decide +kernel) h35423

theorem cover3818 : P.CoversSplit 24 10 3818 0xaa000000ab0000000000000000000000aa000000ab0000000000000000000000000000000000000000000000000000000000000000000000000000000000000088000000880000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 515, 522, 523, 565, 573, 916, 921, 1210, 1258, 1308]) (by decide +kernel)

theorem h3818 : P.leaf 34 3818 = 2034148 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 3818) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 3818) (weight := fun _ => 1) (xs := [475, 479, 507, 511, 856, 857, 859, 861, 863, 889, 891, 893, 895, 984, 985, 987, 989, 991, 1017, 1019, 1021, 1023]) check rows elimOK (by decide) (by decide) cover3818 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h3804 : P.leaf 34 3804 = 2034148 :=
  orient4 (v := 3818) (by decide) (by decide +kernel) h3818

theorem cover3805 : P.CoversSplit 24 10 3805 0xff00ff00f50000000000000000000000ff00ff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00c40000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 516, 536, 573, 915, 1202, 1209, 1210, 1259, 1264]) (ps := [(14, [929], [1266])]) (by decide +kernel)

theorem c3805_0 : P.sumLeaves 24 3896320 1024 = 7301744 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3805) (lo := 0) (len := 1024) (W := 7301744) check rows elimOK (by decide) (by decide) cover3805 (by decide)
  decide +kernel

theorem h3805 : P.leaf 34 3805 = 7301744 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 7301744)]) (.cons c3805_0 (.nil)) (by decide) (by decide))

theorem cover3806 : P.CoversSplit 24 10 3806 0xff00ff00f50000000000000000000000aa00af000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00c40000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 516, 536, 573, 916, 921, 1202, 1209, 1210, 1259]) (ps := [(14, [965], [1266])]) (by decide +kernel)

theorem c3806_0 : P.sumLeaves 24 3897344 1024 = 8827608 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3806) (lo := 0) (len := 1024) (W := 8827608) check rows elimOK (by decide) (by decide) cover3806 (by decide)
  decide +kernel

theorem h3806 : P.leaf 34 3806 = 8827608 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 8827608)]) (.cons c3806_0 (.nil)) (by decide) (by decide))

theorem cover3807 : P.CoversSplit 24 10 3807 0xff00ff00f50000000000000000000000ff00ff00f500000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00c40000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [516, 536, 573, 916, 921, 1202, 1209, 1210, 1217, 1259]) (ps := [(14, [965], [1266])]) (by decide +kernel)

theorem c3807_0 : P.sumLeaves 24 3898368 1024 = 13769352 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3807) (lo := 0) (len := 1024) (W := 13769352) check rows elimOK (by decide) (by decide) cover3807 (by decide)
  decide +kernel

theorem h3807 : P.leaf 34 3807 = 13769352 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 13769352)]) (.cons c3807_0 (.nil)) (by decide) (by decide))

theorem cover3820 : P.CoversSplit 24 10 3820 0x8800000088000000000000000000000088000000880000000000000000000000000000000000000000000000000000000000000000000000000000000000000088000000880000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 508, 515, 522, 573, 915, 1210, 1258, 1308, 1651]) (by decide +kernel)

theorem h3820 : P.leaf 34 3820 = 648904 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 3820) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 3820) (weight := fun _ => 1) (xs := [475, 479, 507, 511, 859, 863, 891, 895, 987, 991, 1019, 1023]) check rows elimOK (by decide) (by decide) cover3820 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover35951 : P.CoversSplit 24 10 35951 0xcc00c800c80000000000000000000000cc0000000000c80000000000000000000000000000000000000000000000000000000000000000000000000000000000cc00c800c80000000000000000000000cc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [515, 522, 572, 858, 865, 1202, 1209, 1258, 1308, 1651]) (ps := [(19, [529], [1209])]) (by decide +kernel)

theorem h35951 : P.leaf 34 35951 = 3341336 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 35951) (keep := keep2) (twice := twice2) rows (by decide) (by decide) bal2 (invRow2 (H := 35951) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 35951) (weight := rowWeight keep2 twice2) (xs := [378, 379, 382, 383, 475, 478, 479, 491, 494, 495, 506, 507, 510, 511, 843, 846, 847, 890, 891, 894, 895, 987, 990, 991, 1003, 1006, 1007, 1018, 1019, 1022, 1023]) check rows elimOK (by decide) (by decide) cover35951 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h3821 : P.leaf 34 3821 = 3341336 :=
  orient5 (v := 35951) (by decide) (by decide +kernel) h35951

theorem cover3822 : P.CoversSplit 24 10 3822 0xaa000000ab0000000000000000000000aa000000ab0000000000000000000000000000000000000000000000000000000000000000000000000000000000000088000000880000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 515, 522, 573, 916, 921, 1210, 1258, 1308]) (by decide +kernel)

theorem h3822 : P.leaf 34 3822 = 5677396 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 3822) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 3822) (weight := fun _ => 1) (xs := [475, 479, 507, 511, 856, 857, 859, 861, 863, 889, 891, 893, 895, 984, 985, 987, 989, 991, 1017, 1019, 1021, 1023]) check rows elimOK (by decide) (by decide) cover3822 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover35967 : P.CoversSplit 24 10 35967 0xcc00c800c8000000cc00c800c8000000cc00c800c8000000cc00c800c80000000000000000000000000000000000000000000000000000000000000000000000cc00c800c80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [572, 573, 578, 858, 915, 1202, 1209, 1258, 1308]) (ps := [(8, [622], [1272])]) (by decide +kernel)

theorem c35967_0 : P.sumLeaves 24 36830208 1024 = 13838986 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 35967) (lo := 0) (len := 1024) (W := 13838986) check rows elimOK (by decide) (by decide) cover35967 (by decide)
  decide +kernel

theorem h35967 : P.leaf 34 35967 = 13838986 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 13838986)]) (.cons c35967_0 (.nil)) (by decide) (by decide))

theorem h3823 : P.leaf 34 3823 = 13838986 :=
  orient5 (v := 35967) (by decide) (by decide +kernel) h35967

theorem cover36478 : P.CoversSplit 24 10 36478 0xcc00cc00c8000000cc00cc00c8000000cc00cc00c8000000cc00cc00c80000000000000000000000000000000000000000000000000000000000000000000000cc00cc00c80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 572, 573, 578, 915, 1202, 1209, 1258, 1308]) (ps := [(8, [622], [1272])]) (by decide +kernel)

noncomputable def f36478 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 24 (37353472 + i)

theorem c36478_0 : rowSum f36478 0 1024 = 23702292 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 36478) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover36478 (by decide)
  decide +kernel

theorem sum36478 : rowSum f36478 0 1024 = 23702292 :=
  c36478_0

theorem h36478 : P.leaf 34 36478 = 23702292 :=
  leaf_weighted (k := 24) (d := 10) (H := 36478) (keep := keep2) (twice := twice2) rows (by decide) (by decide) (bal2) (invRow2 (H := 36478) (by decide) (by decide +kernel)) sum36478

theorem h3838 : P.leaf 34 3838 = 23702292 :=
  orient5 (v := 36478) (by decide) (by decide +kernel) h36478

theorem cover36479 : P.CoversSplit 24 10 36479 0xcc00cc00c8000000cc00cc00c8000000cc00cc00c8000000cc00cc00c80000000000000000000000000000000000000000000000000000000000000000000000cc00cc00c80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [572, 573, 578, 915, 1202, 1209, 1258, 1308]) (ps := [(8, [622], [1272])]) (by decide +kernel)

noncomputable def f36479 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 24 (37354496 + i)

theorem c36479_0 : rowSum f36479 0 1024 = 23702292 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 36479) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover36479 (by decide)
  decide +kernel

theorem sum36479 : rowSum f36479 0 1024 = 23702292 :=
  c36479_0

theorem h36479 : P.leaf 34 36479 = 23702292 :=
  leaf_weighted (k := 24) (d := 10) (H := 36479) (keep := keep2) (twice := twice2) rows (by decide) (by decide) (bal2) (invRow2 (H := 36479) (by decide) (by decide +kernel)) sum36479

theorem h3839 : P.leaf 34 3839 = 23702292 :=
  orient5 (v := 36479) (by decide) (by decide +kernel) h36479

theorem cover49695 : P.CoversSplit 24 10 49695 0xffffffffc800c800ffffffffc800c800ffffffffc800c800ffffffffc800c800a080a08080008000a080a08080008000a080a08080008000a080a08080008000ffffffffc800c800ffffffffc800c800ffffffffc800c800ffffffffc800c800a080a08080008000a080a08080008000a080a08080008000a080a08080008000 :=
  coversSplit check rows (by decide) (by decide) (xs := [516, 523, 529, 572, 866, 872]) (by decide +kernel)

noncomputable def f49695 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (50887680 + i)

theorem c49695_0 : rowSum f49695 0 439 = 816350 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 49695) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover49695 (by decide)
  decide +kernel

theorem c49695_1 : rowSum f49695 439 582 = 7880752 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 49695) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover49695 (by decide)
  decide +kernel

theorem c49695_2 : rowSum f49695 1021 3 = 389760 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 49695) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover49695 (by decide)
  decide +kernel

theorem sum49695 : rowSum f49695 0 1024 = 9086862 :=
  rowSum_append (F := f49695) (lo := 0) (n := 439) (m := 585) (A := 816350) (B := 8270512) c49695_0 (rowSum_append (F := f49695) (lo := 439) (n := 582) (m := 3) (A := 7880752) (B := 389760) c49695_1 (c49695_2))

theorem h49695 : P.leaf 34 49695 = 9086862 :=
  leaf_weighted (k := 24) (d := 10) (H := 49695) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 49695) (by decide) (by decide +kernel)) sum49695

theorem h3987 : P.leaf 34 3987 = 9086862 :=
  orient5 (v := 49695) (by decide) (by decide +kernel) h49695

theorem cover19843 : P.CoversSplit 24 10 19843 0xaa000000a0000a000000000000000000aa0000000000000000000000000000008800000080000800220000002000000088000000000000002200000000000000aa000000a0000a000000000000000000aa0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [466, 515, 516, 522, 865, 1202, 1210, 1259, 1601]) (by decide +kernel)

noncomputable def f19843 (i : ℕ) := rowWeight keep5 twice5 i * P.leaf 24 (20319232 + i)

theorem c19843_0 : rowSum f19843 0 1024 = 340224 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 19843) (keep := keep5) (twice := twice5) check rows elimOK (by decide) (by decide) cover19843 (by decide)
  decide +kernel

theorem sum19843 : rowSum f19843 0 1024 = 340224 :=
  c19843_0

theorem h19843 : P.leaf 34 19843 = 340224 :=
  leaf_weighted (k := 24) (d := 10) (H := 19843) (keep := keep5) (twice := twice5) rows (by decide) (by decide) (bal5) (invRow5 (H := 19843) (by decide) (by decide +kernel)) sum19843

theorem h3988 : P.leaf 34 3988 = 340224 :=
  orient32 (v := 19843) (by decide) (by decide +kernel) h19843

theorem cover49711 : P.CoversSplit 24 10 49711 0xccccc8c8c8004000ccccc8c8c80040008c8c8888080000008c8c888808000000000000000000000000c000c0000000000000000000000000008000800000000088888888880000008888888888000000888888880800000088888888080000000000000000000000008000800000000000000000000000000080008000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 517, 522, 524, 529, 572, 859, 872, 879, 1202]) (by decide +kernel)

theorem c49711_0 : P.sumLeaves 24 50904064 1006 = 3708290 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 49711) (lo := 0) (len := 1006) (W := 3708290) check rows elimOK (by decide) (by decide) cover49711 (by decide)
  decide +kernel

theorem c49711_1 : P.sumLeaves 24 50905070 18 = 1632060 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 49711) (lo := 1006) (len := 18) (W := 1632060) check rows elimOK (by decide) (by decide) cover49711 (by decide)
  decide +kernel

theorem h49711 : P.leaf 34 49711 = 5340350 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1006, 3708290), (18, 1632060)]) (.cons c49711_0 (.cons c49711_1 (.nil))) (by decide) (by decide))

theorem h3989 : P.leaf 34 3989 = 5340350 :=
  orient5 (v := 49711) (by decide) (by decide +kernel) h49711

theorem cover20371 : P.CoversSplit 24 10 20371 0xfffffffff0f0aaaafffffffff0f0aaaafffffffff0f0aaaafffffffff0f0aaaacccccccc80008800ff00ff00a000aa00cccccccc80008800ff00ff00a000aa00fffffffff0f0aaaafffffffff0f0aaaa00000000000000000000000000000000cccccccc80008800ff00ff00a000aa0000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [516, 915, 1202, 1210, 1259, 1308, 1601]) (ps := [(8, [615], [1266])]) (by decide +kernel)

noncomputable def f20371 (i : ℕ) := rowWeight keep5 twice5 i * P.leaf 24 (20859904 + i)

theorem c20371_0 : rowSum f20371 0 463 = 4031704 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 20371) (keep := keep5) (twice := twice5) check rows elimOK (by decide) (by decide) cover20371 (by decide)
  decide +kernel

theorem c20371_1 : rowSum f20371 463 488 = 10853272 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 20371) (keep := keep5) (twice := twice5) check rows elimOK (by decide) (by decide) cover20371 (by decide)
  decide +kernel

theorem c20371_2 : rowSum f20371 951 73 = 8145880 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 20371) (keep := keep5) (twice := twice5) check rows elimOK (by decide) (by decide) cover20371 (by decide)
  decide +kernel

theorem sum20371 : rowSum f20371 0 1024 = 23030856 :=
  rowSum_append (F := f20371) (lo := 0) (n := 463) (m := 561) (A := 4031704) (B := 18999152) c20371_0 (rowSum_append (F := f20371) (lo := 463) (n := 488) (m := 73) (A := 10853272) (B := 8145880) c20371_1 (c20371_2))

theorem h20371 : P.leaf 34 20371 = 23030856 :=
  leaf_weighted (k := 24) (d := 10) (H := 20371) (keep := keep5) (twice := twice5) rows (by decide) (by decide) (bal5) (invRow5 (H := 20371) (by decide) (by decide +kernel)) sum20371

theorem h3991 : P.leaf 34 3991 = 23030856 :=
  orient32 (v := 20371) (by decide) (by decide +kernel) h20371

theorem cover3996 : P.CoversSplit 24 10 3996 0xaa00af0000000a00aa22af2200000a02aa00af0000000a00aa00af0000000a000000000000000000220023000000020000000000000000002200230000000200aa00aa0000000a00aa22aa2200000a02000000000000000000000000000000000000000000000000220022000000020000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 508, 516, 915]) (ps := [(8, [531], [516, 1266]), (14, [923], [915])]) (by decide +kernel)

noncomputable def f3996 (i : ℕ) := rowWeight keep4 twice4 i * P.leaf 24 (4091904 + i)

theorem c3996_0 : rowSum f3996 0 1024 = 1939458 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 3996) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover3996 (by decide)
  decide +kernel

theorem sum3996 : rowSum f3996 0 1024 = 1939458 :=
  c3996_0

theorem h3996 : P.leaf 34 3996 = 1939458 :=
  leaf_weighted (k := 24) (d := 10) (H := 3996) (keep := keep4) (twice := twice4) rows (by decide) (by decide) (bal4) (invRow4 (H := 3996) (by decide) (by decide +kernel)) sum3996

theorem cover3997 : P.CoversSplit 24 10 3997 0xff00ff00ff00aa00ff33ff33ff33aa22ff00ff00ff00aa00ff00ff00ff00aa000000000000000000330033002200220000000000000000003300330022002200ff00ff00ff00aa00ff33ff33ff33aa22000000000000000000000000000000000000000000000000330033002200220000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 516, 915, 1209, 1217]) (ps := [(8, [1217], [1266]), (14, [923], [915, 1266])]) (by decide +kernel)

theorem c3997_0 : P.sumLeaves 24 4092928 665 = 4496138 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3997) (lo := 0) (len := 665) (W := 4496138) check rows elimOK (by decide) (by decide) cover3997 (by decide)
  decide +kernel

theorem c3997_1 : P.sumLeaves 24 4093593 279 = 7500979 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3997) (lo := 665) (len := 279) (W := 7500979) check rows elimOK (by decide) (by decide) cover3997 (by decide)
  decide +kernel

theorem c3997_2 : P.sumLeaves 24 4093872 80 = 23714829 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3997) (lo := 944) (len := 80) (W := 23714829) check rows elimOK (by decide) (by decide) cover3997 (by decide)
  decide +kernel

theorem h3997 : P.leaf 34 3997 = 35711946 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(665, 4496138), (279, 7500979), (80, 23714829)]) (.cons c3997_0 (.cons c3997_1 (.cons c3997_2 (.nil)))) (by decide) (by decide))

theorem cover3999 : P.CoversSplit 24 10 3999 0xffffffffffffaaaaffffffffffffaaaaffffffffffffaaaaffffffffffffaaaaffffffffaa00aa00ff00ff00aa00aa00ffffffffaa00aa00ff00ff00aa00aa00ffffffffffffaaaaffffffffffffaaaaffffffffa0a0a0a0ffffffffa0a0a0a0ffffffffaa00aa00ff00ff00aa00aa00cc00cc0080008000cc00cc0080008000 :=
  coversProjected check rows (by decide) (by decide) (xs := [516, 915, 1209, 1217, 1258, 1609]) (ps := [(8, [1217, 1609], [1266]), (14, [1217, 1609], [1266])]) (by decide +kernel)

def k3999 : ℕ := 0x8aef000000000000ffff8aef0000000000000000000000000000000000000000ffffffff8aef0000ffffffffffff8aef00000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def t3999 : ℕ := 0x8ae000000000000ffff08ae0000000000000000000000000000000000000000ffffffff08ae0000ffffffffffff08ae00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000

noncomputable def f3999 (i : ℕ) := rowWeight k3999 t3999 i * P.leaf 24 (4094976 + i)

theorem contract3999_0 : P.leaf 30 63984 = 0 := by
  exact leaf_contract_zero (ss := [(3, 1, 523), (29, 1, 1258), (8, 0, 1266), (14, 1, 531), (5, 1, 580), (11, 1, 923)]) (q := 1266) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c3999_0 : rowSum f3999 0 64 = 0 :=
  (rowSum_unit_block (P := P) (keep := k3999) (twice := t3999) (by decide +kernel)).trans ((leaf_eq_inner (k := 24) (d := 6) (H := 63984) rows (by decide) (by decide)).symm.trans contract3999_0)

theorem contract3999_1 : P.leaf 30 63985 = 0 := by
  exact leaf_contract_zero (ss := [(3, 1, 523), (8, 0, 1266), (14, 1, 531), (5, 1, 580), (11, 1, 923)]) (q := 1266) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c3999_1 : rowSum f3999 64 64 = 0 :=
  (rowSum_unit_block (P := P) (keep := k3999) (twice := t3999) (by decide +kernel)).trans ((leaf_eq_inner (k := 24) (d := 6) (H := 63985) rows (by decide) (by decide)).symm.trans contract3999_1)

theorem c3999_2 : rowSum f3999 128 128 = 5506576 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 3999) (keep := k3999) (twice := t3999) check rows elimOK (by decide) (by decide) cover3999 (by decide)
  decide +kernel

theorem contract3999_3 : P.leaf 30 63988 = 0 := by
  exact leaf_contract_zero (ss := [(8, 0, 1266), (14, 1, 531), (11, 1, 923)]) (q := 1266) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c3999_3 : rowSum f3999 256 64 = 0 :=
  (rowSum_unit_block (P := P) (keep := k3999) (twice := t3999) (by decide +kernel)).trans ((leaf_eq_inner (k := 24) (d := 6) (H := 63988) rows (by decide) (by decide)).symm.trans contract3999_3)

theorem contract3999_4 : P.leaf 30 63989 = 0 := by
  exact leaf_contract_zero (ss := [(8, 0, 1266), (14, 1, 531), (11, 1, 923)]) (q := 1266) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c3999_4 : rowSum f3999 320 64 = 0 :=
  (rowSum_unit_block (P := P) (keep := k3999) (twice := t3999) (by decide +kernel)).trans ((leaf_eq_inner (k := 24) (d := 6) (H := 63989) rows (by decide) (by decide)).symm.trans contract3999_4)

theorem c3999_5 : rowSum f3999 384 112 = 17372716 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 3999) (keep := k3999) (twice := t3999) check rows elimOK (by decide) (by decide) cover3999 (by decide)
  decide +kernel

theorem c3999_6 : rowSum f3999 496 460 = 66160354 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 3999) (keep := k3999) (twice := t3999) check rows elimOK (by decide) (by decide) cover3999 (by decide)
  decide +kernel

theorem c3999_7 : rowSum f3999 956 68 = 33527024 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 3999) (keep := k3999) (twice := t3999) check rows elimOK (by decide) (by decide) cover3999 (by decide)
  decide +kernel

theorem sum3999 : rowSum f3999 0 1024 = 122566670 :=
  rowSum_append (F := f3999) (lo := 0) (n := 64) (m := 960) (A := 0) (B := 122566670) c3999_0 (rowSum_append (F := f3999) (lo := 64) (n := 64) (m := 896) (A := 0) (B := 122566670) c3999_1 (rowSum_append (F := f3999) (lo := 128) (n := 128) (m := 768) (A := 5506576) (B := 117060094) c3999_2 (rowSum_append (F := f3999) (lo := 256) (n := 64) (m := 704) (A := 0) (B := 117060094) c3999_3 (rowSum_append (F := f3999) (lo := 320) (n := 64) (m := 640) (A := 0) (B := 117060094) c3999_4 (rowSum_append (F := f3999) (lo := 384) (n := 112) (m := 528) (A := 17372716) (B := 99687378) c3999_5 (rowSum_append (F := f3999) (lo := 496) (n := 460) (m := 68) (A := 66160354) (B := 33527024) c3999_6 (c3999_7)))))))

theorem h3999 : P.leaf 34 3999 = 122566670 :=
  leaf_weighted (k := 24) (d := 10) (H := 3999) (keep := k3999) (twice := t3999) rows (by decide) (by decide) (balancedRows_of_check (by decide +kernel)) (invRow4 (H := 3999) (by decide) (by decide +kernel)) sum3999

def seg : List (ℕ × ℕ) := [(3789, 48), (3790, 48), (3791, 48), (3802, 24), (3803, 24), (3804, 48), (3805, 48), (3806, 48), (3807, 48), (3820, 24), (3821, 24), (3822, 48), (3823, 48), (3838, 24), (3839, 24), (3987, 3), (3988, 24), (3989, 48), (3991, 24), (3996, 12), (3997, 24), (3999, 12)]

theorem segOK : checkSeg 16 perms 3789 4004 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 3789 4004 723 7530509370 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 7530509370)
    (SegSum.cons (w := 48) h3789 (SegSum.cons (w := 48) h3790 (SegSum.cons (w := 48) h3791 (SegSum.cons (w := 24) h3802 (SegSum.cons (w := 24) h3803 (SegSum.cons (w := 48) h3804 (SegSum.cons (w := 48) h3805 (SegSum.cons (w := 48) h3806 (SegSum.cons (w := 48) h3807 (SegSum.cons (w := 24) h3820 (SegSum.cons (w := 24) h3821 (SegSum.cons (w := 48) h3822 (SegSum.cons (w := 48) h3823 (SegSum.cons (w := 24) h3838 (SegSum.cons (w := 24) h3839 (SegSum.cons (w := 3) h3987 (SegSum.cons (w := 24) h3988 (SegSum.cons (w := 48) h3989 (SegSum.cons (w := 24) h3991 (SegSum.cons (w := 12) h3996 (SegSum.cons (w := 24) h3997 (SegSum.cons (w := 12) h3999 (show SegSum (P.leaf 34) [] 0 from rfl))))))))))))))))))))))) (by decide)

end RACert.S4N1.C0.S21
