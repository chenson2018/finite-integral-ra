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

namespace RACert.S6N0.C0.S60

open RACert RACert.Problem

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
  leaf_weighted (k := 26) (d := 10) (H := 90110) (keep := keep4) (twice := twice4) rows (by decide) (by decide) (bal4) (invRow4 (H := 90110) (by decide) (by decide +kernel)) sum90110

theorem cover832511 : P.CoversSplit 26 10 832511 0xffffffffffffffffffffaaaaffffaaaaffffffffccccccccffffaaaacccc8888fffffafafffffafaffffaaaaffffaaaafffffafaccccc8c8ffffaaaacccc8888ffffffffffffffffffffaaaaffffaaaaffccffccccccccccffccaa88cccc8888fffffafafffffafaffffaaaaffffaaaaffccfac8ccccc8c8ffccaa88cccc8888 :=
  coversSplit check rows (by decide) (by decide) (xs := [873, 930, 1265, 1273]) (by decide +kernel)

noncomputable def f832511 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 26 (852491264 + i)

theorem c832511_0 : rowSum f832511 0 275 = 973604611 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 832511) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover832511 (by decide)
  decide +kernel

theorem c832511_1 : rowSum f832511 275 156 = 1140371444 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 832511) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover832511 (by decide)
  decide +kernel

theorem c832511_2 : rowSum f832511 431 378 = 1295384512 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 832511) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover832511 (by decide)
  decide +kernel

theorem c832511_3 : rowSum f832511 809 215 = 1210793136 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 832511) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover832511 (by decide)
  decide +kernel

theorem sum832511 : rowSum f832511 0 1024 = 4620153703 :=
  rowSum_append (F := f832511) (lo := 0) (n := 275) (m := 749) (A := 973604611) (B := 3646549092) c832511_0 (rowSum_append (F := f832511) (lo := 275) (n := 156) (m := 593) (A := 1140371444) (B := 2506177648) c832511_1 (rowSum_append (F := f832511) (lo := 431) (n := 378) (m := 215) (A := 1295384512) (B := 1210793136) c832511_2 (c832511_3)))

theorem h832511 : P.leaf 36 832511 = 4620153703 :=
  leaf_weighted (k := 26) (d := 10) (H := 832511) (keep := keep2) (twice := twice2) rows (by decide) (by decide) (bal2) (invRow2 (H := 832511) (by decide) (by decide +kernel)) sum832511

theorem h90111 : P.leaf 36 90111 = 4620153703 :=
  orient324 (v := 832511) (by decide) (by decide +kernel) h832511

theorem cover96741 : P.CoversSplit 26 10 96741 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 482, 489, 629, 636, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h96741 : P.leaf 36 96741 = 1235616 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 96741) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 96741) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover96741 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover96743 : P.CoversSplit 26 10 96743 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 482, 489, 629, 636, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h96743 : P.leaf 36 96743 = 1717468 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 96743) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 96743) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover96743 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover96745 : P.CoversSplit 26 10 96745 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 481, 482, 629, 636, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h96745 : P.leaf 36 96745 = 1399204 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 96745) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 96745) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover96745 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover96747 : P.CoversSplit 26 10 96747 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 481, 482, 629, 636, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h96747 : P.leaf 36 96747 = 1710352 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 96747) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 96747) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover96747 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover96749 : P.CoversSplit 26 10 96749 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 972, 979, 1266, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h96749 : P.leaf 36 96749 = 1794144 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 96749) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 96749) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover96749 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover96751 : P.CoversSplit 26 10 96751 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 972, 979, 1266, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h96751 : P.leaf 36 96751 = 2107682 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 96751) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 96751) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover96751 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover96757 : P.CoversSplit 26 10 96757 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 482, 489, 629, 636, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h96757 : P.leaf 36 96757 = 6546270 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 96757) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 96757) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover96757 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover96759 : P.CoversSplit 26 10 96759 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 482, 489, 629, 636, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h96759 : P.leaf 36 96759 = 8200480 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 96759) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 96759) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover96759 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover96761 : P.CoversSplit 26 10 96761 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 481, 482, 629, 636, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h96761 : P.leaf 36 96761 = 5301592 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 96761) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 96761) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover96761 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover96763 : P.CoversSplit 26 10 96763 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 481, 482, 629, 636, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h96763 : P.leaf 36 96763 = 6937056 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 96763) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 96763) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover96763 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover96764 : P.CoversSplit 26 10 96764 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 972, 979, 1266, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h96764 : P.leaf 36 96764 = 10978546 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 96764) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 96764) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover96764 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover96765 : P.CoversSplit 26 10 96765 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 972, 979, 1266, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h96765 : P.leaf 36 96765 = 11423406 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 96765) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 96765) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover96765 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover96767 : P.CoversSplit 26 10 96767 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 972, 979, 1266, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h96767 : P.leaf 36 96767 = 12935986 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 96767) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 96767) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover96767 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover96979 : P.CoversSplit 26 10 96979 0xc0000000c0000000c0000000c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 587, 972, 979, 1315, 1322]) (by decide +kernel)

theorem h96979 : P.leaf 36 96979 = 9987208 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 96979) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 96979) (weight := fun _ => 1) (xs := [926, 927, 958, 959, 990, 991, 1022, 1023]) check rows elimOK (by decide) (by decide) cover96979 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover96982 : P.CoversSplit 26 10 96982 0xcc000000cc000400cc000000cc00040000000000000000000000000000000000040004000400040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 587, 874, 972, 979, 1315, 1658]) (by decide +kernel)

theorem h96982 : P.leaf 36 96982 = 26401458 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 96982) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 96982) (weight := fun _ => 1) (xs := [714, 730, 746, 762, 906, 922, 923, 926, 927, 954, 955, 958, 959, 970, 986, 987, 990, 991, 1018, 1019, 1022, 1023]) check rows elimOK (by decide) (by decide) cover96982 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover96983 : P.CoversSplit 26 10 96983 0xcc000000cc000400cc000000cc00040000000000000000000000000000000000040004000400040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 587, 972, 979, 1315, 1658]) (by decide +kernel)

theorem h96983 : P.leaf 36 96983 = 58337348 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 96983) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 96983) (weight := fun _ => 1) (xs := [714, 730, 746, 762, 906, 922, 923, 926, 927, 954, 955, 958, 959, 970, 986, 987, 990, 991, 1018, 1019, 1022, 1023]) check rows elimOK (by decide) (by decide) cover96983 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover309043 : P.CoversSplit 26 10 309043 0xaa00000000000000000000000000000000000000000000000000000000000000aa00050000000000000000000000000000000000000000000000000000000000aa00000000220000000000000000000000000000000000000000000000000000aa00050000220001000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 579, 930, 1265, 1273]) (by decide +kernel)

theorem h309043 : P.leaf 36 309043 = 14193792 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 309043) (keep := keep8) (twice := twice8) rows (by decide) (by decide) bal8 (invRow8 (H := 309043) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 309043) (weight := rowWeight keep8 twice8) (xs := [192, 209, 213, 232, 234, 249, 251, 253, 255, 465, 469, 505, 507, 509, 511, 744, 746, 761, 763, 765, 767, 1017, 1019, 1021, 1023]) check rows elimOK (by decide) (by decide) cover309043 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h96985 : P.leaf 36 96985 = 14193792 :=
  orient6 (v := 309043) (by decide) (by decide +kernel) h309043

theorem cover96986 : P.CoversSplit 26 10 96986 0xf0f00000f0f00000f0f00000f0f0000500000000000000000000000000300000000000000000000000000000000000000000000000000000000000000000000000000000003000000000000000300001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 587, 874, 972, 979, 1273, 1315, 1665]) (by decide +kernel)

theorem c96986_0 : P.sumLeaves 26 99313664 1024 = 30506700 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 96986) (lo := 0) (len := 1024) (W := 30506700) check rows elimOK (by decide) (by decide) cover96986 (by decide)
  decide +kernel

theorem h96986 : P.leaf 36 96986 = 30506700 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 30506700)]) (.cons c96986_0 (.nil)) (by decide) (by decide))

theorem cover96987 : P.CoversSplit 26 10 96987 0xf0f00000f0f00000f0f00000f0f0000500000000000000000000000000300000000000000000000000000000000000000000000000000000000000000000000000000000003000000000000000300001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 587, 972, 979, 1273, 1315, 1665]) (by decide +kernel)

theorem c96987_0 : P.sumLeaves 26 99314688 1024 = 66319708 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 96987) (lo := 0) (len := 1024) (W := 66319708) check rows elimOK (by decide) (by decide) cover96987 (by decide)
  decide +kernel

theorem h96987 : P.leaf 36 96987 = 66319708 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 66319708)]) (.cons c96987_0 (.nil)) (by decide) (by decide))

theorem cover309054 : P.CoversSplit 26 10 309054 0xffff050500330001050505050001000100330001003300010000000000000000ffff050500330001000000000000000000330001003300010000000000000000ffff050500330001050505050001000100000000000000000000000000000000ffff050500330001000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [538, 579, 873, 1265, 1273, 1658, 1665]) (by decide +kernel)

noncomputable def f309054 (i : ℕ) := rowWeight keep8 twice8 i * P.leaf 26 (316471296 + i)

theorem c309054_0 : rowSum f309054 0 1024 = 126016732 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 309054) (keep := keep8) (twice := twice8) check rows elimOK (by decide) (by decide) cover309054 (by decide)
  decide +kernel

theorem sum309054 : rowSum f309054 0 1024 = 126016732 :=
  c309054_0

theorem h309054 : P.leaf 36 309054 = 126016732 :=
  leaf_weighted (k := 26) (d := 10) (H := 309054) (keep := keep8) (twice := twice8) rows (by decide) (by decide) (bal8) (invRow8 (H := 309054) (by decide) (by decide +kernel)) sum309054

theorem h96990 : P.leaf 36 96990 = 126016732 :=
  orient6 (v := 309054) (by decide) (by decide +kernel) h309054

theorem cover309055 : P.CoversSplit 26 10 309055 0xffff050500330001050505050001000100330001003300010000000000000000ffff050500330001000000000000000000330001003300010000000000000000ffff050500330001050505050001000100000000000000000000000000000000ffff050500330001000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [538, 579, 1265, 1273, 1658, 1665]) (by decide +kernel)

noncomputable def f309055 (i : ℕ) := rowWeight keep8 twice8 i * P.leaf 26 (316472320 + i)

theorem c309055_0 : rowSum f309055 0 1024 = 268020242 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 309055) (keep := keep8) (twice := twice8) check rows elimOK (by decide) (by decide) cover309055 (by decide)
  decide +kernel

theorem sum309055 : rowSum f309055 0 1024 = 268020242 :=
  c309055_0

theorem h309055 : P.leaf 36 309055 = 268020242 :=
  leaf_weighted (k := 26) (d := 10) (H := 309055) (keep := keep8) (twice := twice8) rows (by decide) (by decide) (bal8) (invRow8 (H := 309055) (by decide) (by decide +kernel)) sum309055

theorem h96991 : P.leaf 36 96991 = 268020242 :=
  orient6 (v := 309055) (by decide) (by decide +kernel) h309055

theorem cover369979 : P.CoversSplit 26 10 369979 0x8080808000000000808080800000000000000000000000000000000000000000808080800000000080808888000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 579, 636, 958, 1273, 1658, 1665]) (by decide +kernel)

theorem h369979 : P.leaf 36 369979 = 4934022 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 369979) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 369979) (weight := fun _ => 1) (xs := [675, 679, 683, 687, 695, 703, 743, 751, 759, 767, 935, 943, 951, 959, 999, 1007, 1015, 1023]) check rows elimOK (by decide) (by decide) cover369979 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h97010 : P.leaf 36 97010 = 4934022 :=
  orient84 (v := 369979) (by decide) (by decide +kernel) h369979

theorem cover97011 : P.CoversSplit 26 10 97011 0xc000c000c000c000c000c000c000c0000000000000000000000000000000000000000000000000000000c0000000c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 587, 972, 979, 1658, 1665]) (by decide +kernel)

theorem h97011 : P.leaf 36 97011 = 27724310 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 97011) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 97011) (weight := fun _ => 1) (xs := [654, 655, 686, 687, 910, 911, 926, 927, 942, 943, 958, 959, 974, 975, 990, 991, 1006, 1007, 1022, 1023]) check rows elimOK (by decide) (by decide) cover97011 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover112115 : P.CoversSplit 26 10 112115 0x8800000088000000880000008800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 629, 636, 930, 1315, 1322]) (by decide +kernel)

theorem h112115 : P.leaf 36 112115 = 20508396 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 112115) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 112115) (weight := fun _ => 1) (xs := [923, 927, 955, 959, 987, 991, 1019, 1023]) check rows elimOK (by decide) (by decide) cover112115 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h97013 : P.leaf 36 97013 = 20508396 :=
  orient4 (v := 112115) (by decide) (by decide +kernel) h112115

theorem cover112118 : P.CoversSplit 26 10 112118 0xcc000000cc000400cc000000cc00040000000000000000000000000000000000040004000400040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 531, 629, 636, 873, 930, 1315, 1658]) (by decide +kernel)

theorem h112118 : P.leaf 36 112118 = 59565504 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 112118) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 112118) (weight := fun _ => 1) (xs := [714, 730, 746, 762, 906, 922, 923, 926, 927, 954, 955, 958, 959, 970, 986, 987, 990, 991, 1018, 1019, 1022, 1023]) check rows elimOK (by decide) (by decide) cover112118 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h97014 : P.leaf 36 97014 = 59565504 :=
  orient4 (v := 112118) (by decide) (by decide +kernel) h112118

theorem cover112119 : P.CoversSplit 26 10 112119 0xcc000000cc000400cc000000cc00040000000000000000000000000000000000040004000400040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 629, 636, 930, 1315, 1658]) (by decide +kernel)

theorem h112119 : P.leaf 36 112119 = 117788882 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 112119) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 112119) (weight := fun _ => 1) (xs := [714, 730, 746, 762, 906, 922, 923, 926, 927, 954, 955, 958, 959, 970, 986, 987, 990, 991, 1018, 1019, 1022, 1023]) check rows elimOK (by decide) (by decide) cover112119 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h97015 : P.leaf 36 97015 = 117788882 :=
  orient4 (v := 112119) (by decide) (by decide +kernel) h112119

theorem cover112120 : P.CoversSplit 26 10 112120 0xaaaa0000aaaa0000aaaa0000aaaa010100000000000000000000000000220000000000000000000000000000000000000000000000000000000000000000000000000000002200000000000000220001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 531, 629, 636, 873, 930, 1315, 1665]) (by decide +kernel)

theorem c112120_0 : P.sumLeaves 26 114810880 1024 = 4957294 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 112120) (lo := 0) (len := 1024) (W := 4957294) check rows elimOK (by decide) (by decide) cover112120 (by decide)
  decide +kernel

theorem h112120 : P.leaf 36 112120 = 4957294 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 4957294)]) (.cons c112120_0 (.nil)) (by decide) (by decide))

theorem h97016 : P.leaf 36 97016 = 4957294 :=
  orient4 (v := 112120) (by decide) (by decide +kernel) h112120

theorem cover112121 : P.CoversSplit 26 10 112121 0xaaaa0000aaaa0000aaaa0000aaaa010100000000000000000000000000220000000000000000000000000000000000000000000000000000000000000000000000000000002200000000000000220001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 580, 629, 636, 930, 1315, 1665]) (by decide +kernel)

theorem c112121_0 : P.sumLeaves 26 114811904 1024 = 43897578 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 112121) (lo := 0) (len := 1024) (W := 43897578) check rows elimOK (by decide) (by decide) cover112121 (by decide)
  decide +kernel

theorem h112121 : P.leaf 36 112121 = 43897578 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 43897578)]) (.cons c112121_0 (.nil)) (by decide) (by decide))

theorem h97017 : P.leaf 36 97017 = 43897578 :=
  orient4 (v := 112121) (by decide) (by decide +kernel) h112121

theorem cover97018 : P.CoversSplit 26 10 97018 0xf0f0f0f0f0f0f0f0f0f0f0f5f0f0f0f000000000000000000000000000300000000000000000000000005050000050500000000000000000000000000000000000000000003000300000000000300030000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 587, 874, 972, 979, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c97018_0 : P.sumLeaves 26 99346432 1024 = 100717536 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97018) (lo := 0) (len := 1024) (W := 100717536) check rows elimOK (by decide) (by decide) cover97018 (by decide)
  decide +kernel

theorem h97018 : P.leaf 36 97018 = 100717536 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 100717536)]) (.cons c97018_0 (.nil)) (by decide) (by decide))

theorem cover97019 : P.CoversSplit 26 10 97019 0xf0f0f0f0f0f0f0f0f0f0f0f5f0f0f0f000000000000000000000000000300000000000000000000000005050000050500000000000000000000000000000000000000000003000300000000000300030000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 587, 972, 979, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c97019_0 : P.sumLeaves 26 99347456 1024 = 212234684 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97019) (lo := 0) (len := 1024) (W := 212234684) check rows elimOK (by decide) (by decide) cover97019 (by decide)
  decide +kernel

theorem h97019 : P.leaf 36 97019 = 212234684 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 212234684)]) (.cons c97019_0 (.nil)) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(90110, 360), (90111, 360), (96741, 360), (96743, 180), (96745, 360), (96747, 180), (96749, 360), (96751, 180), (96757, 360), (96759, 360), (96761, 360), (96763, 360), (96764, 360), (96765, 720), (96767, 360), (96979, 720), (96982, 360), (96983, 360), (96985, 360), (96986, 720), (96987, 720), (96990, 360), (96991, 360), (97010, 720), (97011, 720), (97013, 720), (97014, 720), (97015, 720), (97016, 720), (97017, 720), (97018, 720), (97019, 720)]

theorem segOK : checkSeg 20 perms 90110 97020 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 90110 97020 15660 3237102677520 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 3237102677520)
    (SegSum.cons (w := 360) h90110 (SegSum.cons (w := 360) h90111 (SegSum.cons (w := 360) h96741 (SegSum.cons (w := 180) h96743 (SegSum.cons (w := 360) h96745 (SegSum.cons (w := 180) h96747 (SegSum.cons (w := 360) h96749 (SegSum.cons (w := 180) h96751 (SegSum.cons (w := 360) h96757 (SegSum.cons (w := 360) h96759 (SegSum.cons (w := 360) h96761 (SegSum.cons (w := 360) h96763 (SegSum.cons (w := 360) h96764 (SegSum.cons (w := 720) h96765 (SegSum.cons (w := 360) h96767 (SegSum.cons (w := 720) h96979 (SegSum.cons (w := 360) h96982 (SegSum.cons (w := 360) h96983 (SegSum.cons (w := 360) h96985 (SegSum.cons (w := 720) h96986 (SegSum.cons (w := 720) h96987 (SegSum.cons (w := 360) h96990 (SegSum.cons (w := 360) h96991 (SegSum.cons (w := 720) h97010 (SegSum.cons (w := 720) h97011 (SegSum.cons (w := 720) h97013 (SegSum.cons (w := 720) h97014 (SegSum.cons (w := 720) h97015 (SegSum.cons (w := 720) h97016 (SegSum.cons (w := 720) h97017 (SegSum.cons (w := 720) h97018 (SegSum.cons (w := 720) h97019 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S60
