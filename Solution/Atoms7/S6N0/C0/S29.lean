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

namespace RACert.S6N0.C0.S29

open RACert RACert.Problem

theorem cover14305 : P.CoversSplit 26 10 14305 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h14305 : P.leaf 36 14305 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 14305) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 14305) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover14305 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover14307 : P.CoversSplit 26 10 14307 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h14307 : P.leaf 36 14307 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 14307) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 14307) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover14307 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover14308 : P.CoversSplit 26 10 14308 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h14308 : P.leaf 36 14308 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 14308) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 14308) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover14308 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover14309 : P.CoversSplit 26 10 14309 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h14309 : P.leaf 36 14309 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 14309) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 14309) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover14309 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover14310 : P.CoversSplit 26 10 14310 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h14310 : P.leaf 36 14310 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 14310) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 14310) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover14310 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover14311 : P.CoversSplit 26 10 14311 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h14311 : P.leaf 36 14311 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 14311) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 14311) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover14311 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover14316 : P.CoversSplit 26 10 14316 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h14316 : P.leaf 36 14316 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 14316) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 14316) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover14316 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover14317 : P.CoversSplit 26 10 14317 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h14317 : P.leaf 36 14317 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 14317) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 14317) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover14317 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover14319 : P.CoversSplit 26 10 14319 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h14319 : P.leaf 36 14319 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 14319) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 14319) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover14319 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover80300 : P.CoversSplit 26 10 80300 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 531, 538, 629, 636, 930, 972, 979, 1273, 1315, 1658]) (by decide +kernel)

theorem h80300 : P.leaf 36 80300 = 50176 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 80300) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 80300) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover80300 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h14320 : P.leaf 36 14320 = 50176 :=
  orient348 (v := 80300) (by decide) (by decide +kernel) h80300

theorem cover272735 : P.CoversSplit 26 10 272735 0xaa00aa00aa00aa00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 629, 636, 929, 979, 1265, 1273, 1308, 1658]) (by decide +kernel)

theorem h272735 : P.leaf 36 272735 = 1536784 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 272735) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 272735) (weight := fun _ => 1) (xs := [969, 971, 973, 975, 985, 987, 989, 991, 1001, 1003, 1005, 1007, 1017, 1019, 1021, 1023]) check rows elimOK (by decide) (by decide) cover272735 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h14321 : P.leaf 36 14321 = 1536784 :=
  orient86 (v := 272735) (by decide) (by decide +kernel) h272735

theorem cover14323 : P.CoversSplit 26 10 14323 0xf0000000f0000000f0000000f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 873, 930, 972, 979, 1322, 1658]) (by decide +kernel)

theorem h14323 : P.leaf 36 14323 = 6860096 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 14323) (keep := keep2) (twice := twice2) rows (by decide) (by decide) bal2 (invRow2 (H := 14323) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 14323) (weight := rowWeight keep2 twice2) (xs := [924, 925, 926, 927, 956, 957, 958, 959, 988, 989, 990, 991, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover14323 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover100827 : P.CoversSplit 26 10 100827 0xa0a0a0a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 629, 636, 881, 930, 965, 1266, 1322, 1658]) (by decide +kernel)

theorem h100827 : P.leaf 36 100827 = 1087824 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 100827) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 100827) (weight := fun _ => 1) (xs := [997, 999, 1005, 1007, 1013, 1015, 1021, 1023]) check rows elimOK (by decide) (by decide) cover100827 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h14324 : P.leaf 36 14324 = 1087824 :=
  orient84 (v := 100827) (by decide) (by decide +kernel) h100827

theorem cover100831 : P.CoversSplit 26 10 100831 0xffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 629, 636, 881, 922, 930, 1266, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h100831 : P.leaf 36 100831 = 7812712 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 100831) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 100831) (weight := fun _ => 1) (xs := [992, 993, 994, 995, 996, 997, 998, 999, 1000, 1001, 1002, 1003, 1004, 1005, 1006, 1007, 1008, 1009, 1010, 1011, 1012, 1013, 1014, 1015, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover100831 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h14325 : P.leaf 36 14325 = 7812712 :=
  orient84 (v := 100831) (by decide) (by decide +kernel) h100831

theorem cover100859 : P.CoversSplit 26 10 100859 0xaaaaaaaa00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 629, 636, 881, 922, 930, 965, 1266, 1322, 1658]) (by decide +kernel)

theorem h100859 : P.leaf 36 100859 = 13142184 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 100859) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 100859) (weight := fun _ => 1) (xs := [993, 995, 997, 999, 1001, 1003, 1005, 1007, 1009, 1011, 1013, 1015, 1017, 1019, 1021, 1023]) check rows elimOK (by decide) (by decide) cover100859 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h14326 : P.leaf 36 14326 = 13142184 :=
  orient84 (v := 100859) (by decide) (by decide +kernel) h100859

theorem cover100863 : P.CoversSplit 26 10 100863 0xffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [629, 636, 881, 922, 930, 1266, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h100863 : P.leaf 36 100863 = 61616798 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 100863) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 100863) (weight := fun _ => 1) (xs := [992, 993, 994, 995, 996, 997, 998, 999, 1000, 1001, 1002, 1003, 1004, 1005, 1006, 1007, 1008, 1009, 1010, 1011, 1012, 1013, 1014, 1015, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover100863 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h14327 : P.leaf 36 14327 = 61616798 :=
  orient84 (v := 100863) (by decide) (by decide +kernel) h100863

theorem cover46067 : P.CoversSplit 26 10 46067 0xf0000000f0000000f0000000f000000000000000000000000000000000000000f5005000f5004000a0000000a000000000000000000000000000000000000000f0300000c0000000f0300000c000000030000000000000002000000000000000f5315010c4004000a02000008000000031001000000000002000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 873, 930, 1265, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f46067 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 26 (47172608 + i)

theorem c46067_0 : rowSum f46067 0 1024 = 28424993 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 46067) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover46067 (by decide)
  decide +kernel

theorem sum46067 : rowSum f46067 0 1024 = 28424993 :=
  c46067_0

theorem h46067 : P.leaf 36 46067 = 28424993 :=
  leaf_weighted (k := 26) (d := 10) (H := 46067) (keep := keep2) (twice := twice2) rows (by decide) (by decide) (bal2) (invRow2 (H := 46067) (by decide) (by decide +kernel)) sum46067

theorem h14332 : P.leaf 36 14332 = 28424993 :=
  orient80 (v := 46067) (by decide) (by decide +kernel) h46067

theorem cover36859 : P.CoversSplit 26 10 36859 0xf0f0f5f5f0f0a080000050500000000000000000000000000000000000000000f0f0a0a0f0f0a080000000000000000000000000000000000000000000000000f0f0f5f5f0c0a080000050500000000000000000000000000000000000000000f0f0a0a0f0c0a080000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 881, 922, 929, 1265, 1315, 1322]) (by decide +kernel)

theorem c36859_0 : P.sumLeaves 26 37743616 998 = 131004064 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 36859) (lo := 0) (len := 998) (W := 131004064) check rows elimOK (by decide) (by decide) cover36859 (by decide)
  decide +kernel

theorem c36859_1 : P.sumLeaves 26 37744614 26 = 51430344 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 36859) (lo := 998) (len := 26) (W := 51430344) check rows elimOK (by decide) (by decide) cover36859 (by decide)
  decide +kernel

theorem h36859 : P.leaf 36 36859 = 182434408 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(998, 131004064), (26, 51430344)]) (.cons c36859_0 (.cons c36859_1 (.nil))) (by decide) (by decide))

theorem h14333 : P.leaf 36 14333 = 182434408 :=
  orient6 (v := 36859) (by decide) (by decide +kernel) h36859

theorem cover46079 : P.CoversSplit 26 10 46079 0xffffffffffffc8c8ffffaaaaffff8888ffffffffccccc8c8aa88aa8888888888fffffafaffffc8c8aaaaaaaaaaaa8888fffffafaccccc8c8aa88aa8888888888ffffffffccccc8c8ffffaaaacccc8888ffccffccccccc8c8aa88aa8888888888fffffafaccccc8c8aaaaaaaa88888888ffccfac8ccccc8c8aa88aa8888888888 :=
  coversSplit check rows (by decide) (by decide) (xs := [873, 930, 1265, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f46079 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 26 (47184896 + i)

theorem c46079_0 : rowSum f46079 0 346 = 326461580 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 46079) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover46079 (by decide)
  decide +kernel

theorem c46079_1 : rowSum f46079 346 152 = 522109140 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 46079) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover46079 (by decide)
  decide +kernel

theorem c46079_2 : rowSum f46079 498 514 = 573931042 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 46079) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover46079 (by decide)
  decide +kernel

theorem c46079_3 : rowSum f46079 1012 12 = 77818424 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 46079) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover46079 (by decide)
  decide +kernel

theorem sum46079 : rowSum f46079 0 1024 = 1500320186 :=
  rowSum_append (F := f46079) (lo := 0) (n := 346) (m := 678) (A := 326461580) (B := 1173858606) c46079_0 (rowSum_append (F := f46079) (lo := 346) (n := 152) (m := 526) (A := 522109140) (B := 651749466) c46079_1 (rowSum_append (F := f46079) (lo := 498) (n := 514) (m := 12) (A := 573931042) (B := 77818424) c46079_2 (c46079_3)))

theorem h46079 : P.leaf 36 46079 = 1500320186 :=
  leaf_weighted (k := 26) (d := 10) (H := 46079) (keep := keep2) (twice := twice2) rows (by decide) (by decide) (bal2) (invRow2 (H := 46079) (by decide) (by decide +kernel)) sum46079

theorem h14335 : P.leaf 36 14335 = 1500320186 :=
  orient80 (v := 46079) (by decide) (by decide +kernel) h46079

theorem cover15606 : P.CoversSplit 26 10 15606 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h15606 : P.leaf 36 15606 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 15606) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 15606) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover15606 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover15607 : P.CoversSplit 26 10 15607 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h15607 : P.leaf 36 15607 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 15607) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 15607) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover15607 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover15608 : P.CoversSplit 26 10 15608 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h15608 : P.leaf 36 15608 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 15608) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 15608) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover15608 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover15609 : P.CoversSplit 26 10 15609 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h15609 : P.leaf 36 15609 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 15609) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 15609) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover15609 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover15610 : P.CoversSplit 26 10 15610 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h15610 : P.leaf 36 15610 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 15610) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 15610) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover15610 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover15611 : P.CoversSplit 26 10 15611 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h15611 : P.leaf 36 15611 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 15611) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 15611) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover15611 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover15614 : P.CoversSplit 26 10 15614 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h15614 : P.leaf 36 15614 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 15614) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 15614) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover15614 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover15615 : P.CoversSplit 26 10 15615 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h15615 : P.leaf 36 15615 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 15615) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 15615) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover15615 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover15732 : P.CoversSplit 26 10 15732 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h15732 : P.leaf 36 15732 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 15732) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 15732) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover15732 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover15733 : P.CoversSplit 26 10 15733 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h15733 : P.leaf 36 15733 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 15733) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 15733) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover15733 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover15734 : P.CoversSplit 26 10 15734 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h15734 : P.leaf 36 15734 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 15734) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 15734) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover15734 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover15735 : P.CoversSplit 26 10 15735 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h15735 : P.leaf 36 15735 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 15735) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 15735) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover15735 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover15740 : P.CoversSplit 26 10 15740 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h15740 : P.leaf 36 15740 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 15740) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 15740) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover15740 (by decide) (by decide) (by decide +kernel)
  decide +kernel

def seg : List (ℕ × ℕ) := [(14305, 720), (14307, 360), (14308, 720), (14309, 720), (14310, 720), (14311, 720), (14316, 360), (14317, 720), (14319, 360), (14320, 360), (14321, 720), (14323, 360), (14324, 720), (14325, 720), (14326, 720), (14327, 720), (14332, 360), (14333, 720), (14335, 360), (15606, 180), (15607, 180), (15608, 180), (15609, 180), (15610, 360), (15611, 360), (15614, 180), (15615, 180), (15732, 720), (15733, 720), (15734, 720), (15735, 720), (15740, 360)]

theorem segOK : checkSeg 20 perms 14305 15741 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 14305 15741 16200 745530073560 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 745530073560)
    (SegSum.cons (w := 720) h14305 (SegSum.cons (w := 360) h14307 (SegSum.cons (w := 720) h14308 (SegSum.cons (w := 720) h14309 (SegSum.cons (w := 720) h14310 (SegSum.cons (w := 720) h14311 (SegSum.cons (w := 360) h14316 (SegSum.cons (w := 720) h14317 (SegSum.cons (w := 360) h14319 (SegSum.cons (w := 360) h14320 (SegSum.cons (w := 720) h14321 (SegSum.cons (w := 360) h14323 (SegSum.cons (w := 720) h14324 (SegSum.cons (w := 720) h14325 (SegSum.cons (w := 720) h14326 (SegSum.cons (w := 720) h14327 (SegSum.cons (w := 360) h14332 (SegSum.cons (w := 720) h14333 (SegSum.cons (w := 360) h14335 (SegSum.cons (w := 180) h15606 (SegSum.cons (w := 180) h15607 (SegSum.cons (w := 180) h15608 (SegSum.cons (w := 180) h15609 (SegSum.cons (w := 360) h15610 (SegSum.cons (w := 360) h15611 (SegSum.cons (w := 180) h15614 (SegSum.cons (w := 180) h15615 (SegSum.cons (w := 720) h15732 (SegSum.cons (w := 720) h15733 (SegSum.cons (w := 720) h15734 (SegSum.cons (w := 720) h15735 (SegSum.cons (w := 360) h15740 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S29
