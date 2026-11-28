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

namespace RACert.S4N1.C0.S25

open RACert RACert.Problem

theorem cover5323 : P.CoversSplit 24 10 5323 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem h5323 : P.leaf 34 5323 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5323) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5323) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover5323 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover5324 : P.CoversSplit 24 10 5324 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem h5324 : P.leaf 34 5324 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5324) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5324) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover5324 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h5325 : P.leaf 34 5325 = 0 := by
  exact leaf_contract_zero (ss := [(30, 1, 466), (11, 1, 472), (4, 1, 508), (32, 1, 523), (3, 1, 417), (18, 1, 524), (35, 33, 536), (17, 1, 565), (33, 0, 867), (27, 1, 573), (26, 1, 515), (34, 1, 573), (29, 1, 865), (28, 1, 858), (16, 1, 872), (31, 1, 1209)]) (q := 1272) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem cover5326 : P.CoversSplit 24 10 5326 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem h5326 : P.leaf 34 5326 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5326) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5326) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover5326 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover5327 : P.CoversSplit 24 10 5327 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem h5327 : P.leaf 34 5327 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5327) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5327) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover5327 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h5329 : P.leaf 34 5329 = 0 := by
  exact leaf_contract_zero (ss := [(2, 1, 453), (5, 1, 453), (8, 0, 475), (6, 1, 478), (12, 1, 460), (11, 1, 459), (14, 0, 487), (33, 1, 482)]) (q := 488) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem cover5330 : P.CoversSplit 24 10 5330 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem h5330 : P.leaf 34 5330 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5330) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5330) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover5330 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover5331 : P.CoversSplit 24 10 5331 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem h5331 : P.leaf 34 5331 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5331) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5331) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover5331 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover5332 : P.CoversSplit 24 10 5332 0xa000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 508, 516, 536, 573, 858, 865, 867, 909, 1202, 1210, 1251, 1259, 1264]) (by decide +kernel)

theorem h5332 : P.leaf 34 5332 = 8992 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5332) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5332) (weight := fun _ => 1) (xs := [1021, 1023]) check rows elimOK (by decide) (by decide) cover5332 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover5333 : P.CoversSplit 24 10 5333 0xff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 516, 536, 573, 858, 860, 865, 866, 867, 909, 916, 1202, 1210, 1251, 1259]) (by decide +kernel)

theorem h5333 : P.leaf 34 5333 = 140640 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5333) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5333) (weight := fun _ => 1) (xs := [1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover5333 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover5334 : P.CoversSplit 24 10 5334 0xa0a00000000000000000000000000000a0a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 516, 536, 573, 858, 865, 867, 916, 1202, 1209, 1210, 1251, 1259, 1264]) (by decide +kernel)

theorem h5334 : P.leaf 34 5334 = 220848 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5334) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5334) (weight := fun _ => 1) (xs := [885, 887, 893, 895, 1013, 1015, 1021, 1023]) check rows elimOK (by decide) (by decide) cover5334 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover5335 : P.CoversSplit 24 10 5335 0xffff0000000000000000000000000000ffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [516, 536, 573, 858, 860, 865, 866, 867, 916, 1202, 1210, 1217, 1251, 1259, 1264]) (by decide +kernel)

theorem h5335 : P.leaf 34 5335 = 3389176 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5335) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5335) (weight := fun _ => 1) (xs := [880, 881, 882, 883, 884, 885, 886, 887, 888, 889, 890, 891, 892, 893, 894, 895, 1008, 1009, 1010, 1011, 1012, 1013, 1014, 1015, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover5335 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h5336 : P.leaf 34 5336 = 0 := by
  exact leaf_contract_zero (ss := [(2, 1, 466), (29, 1, 472), (15, 1, 486), (35, 14, 487), (28, 1, 508), (14, 8, 509), (8, 0, 867), (18, 11, 475), (20, 1, 482), (21, 0, 488), (27, 1, 573), (34, 1, 573), (33, 0, 580), (7, 6, 467), (31, 1, 536), (26, 1, 465), (12, 1, 608), (5, 1, 411), (4, 1, 410), (9, 1, 678), (30, 1, 858), (32, 1, 865), (16, 10, 872)]) (q := 1272) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem h5337 : P.leaf 34 5337 = 0 := by
  exact leaf_contract_zero (ss := [(35, 14, 487), (14, 0, 867), (16, 1, 872), (33, 0, 909), (34, 31, 536), (8, 0, 874), (18, 11, 475), (20, 1, 482), (21, 0, 488), (12, 5, 509), (29, 15, 558), (5, 1, 608), (31, 1, 622), (10, 1, 811), (15, 1, 865), (2, 1, 411), (27, 1, 573), (9, 1, 678), (32, 1, 865), (13, 1, 971), (30, 1, 1251), (11, 1, 1265), (6, 1, 460), (7, 1, 628)]) (q := 1272) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem cover5338 : P.CoversSplit 24 10 5338 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem h5338 : P.leaf 34 5338 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5338) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5338) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover5338 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover5339 : P.CoversSplit 24 10 5339 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem h5339 : P.leaf 34 5339 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5339) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5339) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover5339 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover5340 : P.CoversSplit 24 10 5340 0xa000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 508, 516, 536, 573, 858, 865, 867, 909, 1202, 1210, 1251, 1258, 1259, 1264]) (by decide +kernel)

theorem h5340 : P.leaf 34 5340 = 70736 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5340) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5340) (weight := fun _ => 1) (xs := [1021, 1023]) check rows elimOK (by decide) (by decide) cover5340 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover5341 : P.CoversSplit 24 10 5341 0xff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 516, 536, 573, 858, 860, 865, 867, 909, 916, 1202, 1210, 1251, 1258, 1259]) (by decide +kernel)

theorem h5341 : P.leaf 34 5341 = 709856 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5341) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5341) (weight := fun _ => 1) (xs := [1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover5341 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover5342 : P.CoversSplit 24 10 5342 0xa0a00000000000000000000000000000a0a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 516, 536, 573, 858, 865, 867, 916, 1202, 1209, 1210, 1251, 1258, 1259, 1264]) (by decide +kernel)

theorem h5342 : P.leaf 34 5342 = 808232 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5342) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5342) (weight := fun _ => 1) (xs := [885, 887, 893, 895, 1013, 1015, 1021, 1023]) check rows elimOK (by decide) (by decide) cover5342 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover5343 : P.CoversSplit 24 10 5343 0xffff0000000000000000000000000000ffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [516, 536, 573, 858, 860, 865, 867, 916, 1202, 1210, 1217, 1251, 1258, 1259, 1264]) (by decide +kernel)

theorem h5343 : P.leaf 34 5343 = 5505428 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5343) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5343) (weight := fun _ => 1) (xs := [880, 881, 882, 883, 884, 885, 886, 887, 888, 889, 890, 891, 892, 893, 894, 895, 1008, 1009, 1010, 1011, 1012, 1013, 1014, 1015, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover5343 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover5344 : P.CoversSplit 24 10 5344 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem h5344 : P.leaf 34 5344 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5344) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5344) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover5344 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h5345 : P.leaf 34 5345 = 0 := by
  exact leaf_contract_zero (ss := [(30, 1, 466), (8, 0, 475), (6, 1, 478), (12, 1, 478), (11, 1, 459), (14, 0, 487), (33, 1, 482)]) (q := 488) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem cover5346 : P.CoversSplit 24 10 5346 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem h5346 : P.leaf 34 5346 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5346) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5346) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover5346 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover5347 : P.CoversSplit 24 10 5347 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem h5347 : P.leaf 34 5347 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5347) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5347) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover5347 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover5348 : P.CoversSplit 24 10 5348 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem h5348 : P.leaf 34 5348 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5348) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5348) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover5348 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h5349 : P.leaf 34 5349 = 0 := by
  exact leaf_contract_zero (ss := [(30, 1, 466), (35, 8, 475), (4, 1, 508), (18, 1, 487), (8, 0, 867), (21, 0, 580), (20, 1, 586), (34, 5, 622), (16, 1, 872), (33, 0, 909), (6, 1, 482), (11, 1, 459), (14, 1, 482), (9, 1, 559)]) (q := 629) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem cover5350 : P.CoversSplit 24 10 5350 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem h5350 : P.leaf 34 5350 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5350) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5350) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover5350 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover5351 : P.CoversSplit 24 10 5351 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem h5351 : P.leaf 34 5351 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5351) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5351) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover5351 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover5352 : P.CoversSplit 24 10 5352 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem h5352 : P.leaf 34 5352 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5352) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5352) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover5352 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h5353 : P.leaf 34 5353 = 0 := by
  exact leaf_contract_zero (ss := [(30, 1, 466), (35, 14, 487), (4, 1, 508), (14, 0, 867), (18, 1, 524), (16, 1, 872), (33, 0, 909), (8, 0, 874), (5, 1, 433), (2, 1, 410), (11, 1, 475), (6, 1, 460), (12, 1, 460), (20, 1, 482), (21, 0, 488), (29, 15, 558), (34, 1, 622), (27, 1, 522), (26, 1, 515), (32, 1, 522), (7, 1, 628), (10, 1, 811), (15, 1, 865), (9, 1, 678), (28, 1, 858), (13, 1, 971), (31, 1, 1209)]) (q := 1272) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem cover5354 : P.CoversSplit 24 10 5354 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem h5354 : P.leaf 34 5354 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5354) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5354) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover5354 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover5355 : P.CoversSplit 24 10 5355 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem h5355 : P.leaf 34 5355 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5355) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5355) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover5355 (by decide) (by decide) (by decide +kernel)
  decide +kernel

def seg : List (ℕ × ℕ) := [(5323, 48), (5324, 48), (5325, 48), (5326, 48), (5327, 48), (5329, 24), (5330, 48), (5331, 48), (5332, 48), (5333, 48), (5334, 48), (5335, 48), (5336, 48), (5337, 48), (5338, 48), (5339, 48), (5340, 48), (5341, 48), (5342, 48), (5343, 48), (5344, 24), (5345, 48), (5346, 48), (5347, 48), (5348, 48), (5349, 48), (5350, 48), (5351, 48), (5352, 48), (5353, 48), (5354, 48), (5355, 48)]

theorem segOK : checkSeg 16 perms 5323 5356 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 5323 5356 1488 520987584 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 520987584)
    (SegSum.cons (w := 48) h5323 (SegSum.cons (w := 48) h5324 (SegSum.cons (w := 48) h5325 (SegSum.cons (w := 48) h5326 (SegSum.cons (w := 48) h5327 (SegSum.cons (w := 24) h5329 (SegSum.cons (w := 48) h5330 (SegSum.cons (w := 48) h5331 (SegSum.cons (w := 48) h5332 (SegSum.cons (w := 48) h5333 (SegSum.cons (w := 48) h5334 (SegSum.cons (w := 48) h5335 (SegSum.cons (w := 48) h5336 (SegSum.cons (w := 48) h5337 (SegSum.cons (w := 48) h5338 (SegSum.cons (w := 48) h5339 (SegSum.cons (w := 48) h5340 (SegSum.cons (w := 48) h5341 (SegSum.cons (w := 48) h5342 (SegSum.cons (w := 48) h5343 (SegSum.cons (w := 24) h5344 (SegSum.cons (w := 48) h5345 (SegSum.cons (w := 48) h5346 (SegSum.cons (w := 48) h5347 (SegSum.cons (w := 48) h5348 (SegSum.cons (w := 48) h5349 (SegSum.cons (w := 48) h5350 (SegSum.cons (w := 48) h5351 (SegSum.cons (w := 48) h5352 (SegSum.cons (w := 48) h5353 (SegSum.cons (w := 48) h5354 (SegSum.cons (w := 48) h5355 (show SegSum (P.leaf 34) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S4N1.C0.S25
