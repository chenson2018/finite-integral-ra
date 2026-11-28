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

namespace RACert.S4N1.C0.S26

open RACert RACert.Problem

theorem cover5356 : P.CoversSplit 24 10 5356 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem h5356 : P.leaf 34 5356 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5356) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5356) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover5356 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h5357 : P.leaf 34 5357 = 0 := by
  exact leaf_contract_zero (ss := [(30, 1, 466), (4, 1, 508), (35, 0, 867), (18, 1, 487), (16, 1, 872), (33, 0, 909), (11, 1, 879)]) (q := 1272) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem cover5358 : P.CoversSplit 24 10 5358 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem h5358 : P.leaf 34 5358 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5358) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5358) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover5358 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover5359 : P.CoversSplit 24 10 5359 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem h5359 : P.leaf 34 5359 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5359) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5359) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover5359 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h5361 : P.leaf 34 5361 = 0 := by
  exact leaf_contract_zero (ss := [(8, 0, 475), (6, 1, 478), (12, 1, 478), (11, 1, 459), (14, 0, 487), (33, 1, 482)]) (q := 488) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem cover5362 : P.CoversSplit 24 10 5362 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem h5362 : P.leaf 34 5362 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5362) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5362) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover5362 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover5363 : P.CoversSplit 24 10 5363 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem h5363 : P.leaf 34 5363 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5363) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5363) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover5363 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover5364 : P.CoversSplit 24 10 5364 0xf0000000a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 508, 573, 858, 860, 865, 867, 909, 1202, 1210, 1259]) (by decide +kernel)

theorem h5364 : P.leaf 34 5364 = 40392 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5364) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5364) (weight := fun _ => 1) (xs := [989, 991, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover5364 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover18607 : P.CoversSplit 24 10 18607 0xaa000000aa0000000000000000000000aa000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 517, 522, 573, 865, 879, 916, 921, 1202, 1210]) (by decide +kernel)

theorem h18607 : P.leaf 34 18607 = 323584 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 18607) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 18607) (weight := fun _ => 1) (xs := [889, 891, 893, 895, 985, 987, 989, 991, 1017, 1019, 1021, 1023]) check rows elimOK (by decide) (by decide) cover18607 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h5365 : P.leaf 34 5365 = 323584 :=
  orient4 (v := 18607) (by decide) (by decide +kernel) h18607

theorem cover18622 : P.CoversSplit 24 10 18622 0xa000a000a0000000a000a000a0000000a000a00000000000a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 517, 573, 859, 865, 866, 879, 916, 921, 1202, 1210, 1251]) (by decide +kernel)

theorem h18622 : P.leaf 34 18622 = 904560 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 18622) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 18622) (weight := fun _ => 1) (xs := [829, 831, 877, 879, 893, 895, 925, 927, 941, 943, 957, 959, 989, 991, 1005, 1007, 1021, 1023]) check rows elimOK (by decide) (by decide) cover18622 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h5366 : P.leaf 34 5366 = 904560 :=
  orient4 (v := 18622) (by decide) (by decide +kernel) h18622

theorem cover18623 : P.CoversSplit 24 10 18623 0xff00fa00aa000000ff00fa00aa000000ff00fa0000000000ff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [517, 573, 858, 865, 879, 916, 921, 1202, 1210, 1217, 1251]) (by decide +kernel)

theorem c18623_0 : P.sumLeaves 24 19069952 1024 = 10175096 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 18623) (lo := 0) (len := 1024) (W := 10175096) check rows elimOK (by decide) (by decide) cover18623 (by decide)
  decide +kernel

theorem h18623 : P.leaf 34 18623 = 10175096 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 10175096)]) (.cons c18623_0 (.nil)) (by decide) (by decide))

theorem h5367 : P.leaf 34 5367 = 10175096 :=
  orient4 (v := 18623) (by decide) (by decide +kernel) h18623

theorem h5368 : P.leaf 34 5368 = 0 := by
  exact leaf_contract_zero (ss := [(2, 1, 466), (35, 14, 487), (28, 1, 508), (14, 0, 867), (15, 1, 486), (16, 10, 872), (33, 0, 909), (21, 0, 874), (18, 11, 879), (20, 1, 880), (12, 1, 951), (31, 1, 860), (30, 1, 858), (34, 1, 965), (29, 1, 865), (27, 1, 573), (32, 1, 865), (8, 0, 972), (5, 1, 411), (4, 1, 410), (9, 1, 678)]) (q := 1272) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem h5369 : P.leaf 34 5369 = 0 := by
  exact leaf_contract_zero (ss := [(35, 14, 487), (14, 0, 867), (16, 1, 872), (33, 0, 909), (8, 0, 874), (5, 1, 433), (18, 11, 475), (20, 1, 482), (21, 0, 488), (29, 15, 558), (12, 1, 608), (34, 1, 622), (7, 1, 628), (6, 1, 460), (10, 1, 811), (15, 1, 865), (27, 1, 573), (9, 1, 678), (32, 1, 865), (13, 1, 971), (31, 1, 1217), (11, 1, 1265)]) (q := 1272) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem cover5370 : P.CoversSplit 24 10 5370 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem h5370 : P.leaf 34 5370 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5370) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5370) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover5370 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover5371 : P.CoversSplit 24 10 5371 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem h5371 : P.leaf 34 5371 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5371) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5371) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover5371 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover5372 : P.CoversSplit 24 10 5372 0xf0000000a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 508, 573, 858, 860, 865, 867, 909, 1202, 1210, 1258, 1259]) (by decide +kernel)

theorem h5372 : P.leaf 34 5372 = 309192 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5372) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5372) (weight := fun _ => 1) (xs := [989, 991, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover5372 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover5373 : P.CoversSplit 24 10 5373 0xff00ff00aa000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 573, 858, 860, 865, 867, 909, 916, 1202, 1210, 1258, 1259]) (by decide +kernel)

theorem h5373 : P.leaf 34 5373 = 1862640 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5373) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5373) (weight := fun _ => 1) (xs := [985, 987, 989, 991, 1000, 1001, 1002, 1003, 1004, 1005, 1006, 1007, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover5373 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover5374 : P.CoversSplit 24 10 5374 0xf0f00000a0a000000000000000000000f0f00000000500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 573, 858, 860, 865, 867, 916, 1202, 1210, 1258, 1259, 1264]) (by decide +kernel)

theorem h5374 : P.leaf 34 5374 = 4238222 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5374) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5374) (weight := fun _ => 1) (xs := [848, 850, 884, 885, 886, 887, 892, 893, 894, 895, 981, 983, 989, 991, 1012, 1013, 1014, 1015, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover5374 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover18687 : P.CoversSplit 24 10 18687 0xff00fa00aa000000ff00fa00aa000000ff00fa00aa000000ff00fa00aa000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [573, 858, 859, 865, 879, 915, 916, 921, 1202, 1210]) (by decide +kernel)

theorem c18687_0 : P.sumLeaves 24 19135488 1024 = 20566456 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 18687) (lo := 0) (len := 1024) (W := 20566456) check rows elimOK (by decide) (by decide) cover18687 (by decide)
  decide +kernel

theorem h18687 : P.leaf 34 18687 = 20566456 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 20566456)]) (.cons c18687_0 (.nil)) (by decide) (by decide))

theorem h5375 : P.leaf 34 5375 = 20566456 :=
  orient4 (v := 18687) (by decide) (by decide +kernel) h18687

theorem cover9504 : P.CoversSplit 24 10 9504 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 515, 517, 522, 524, 529, 565, 572, 858, 865, 1202, 1258, 1259, 1266]) (by decide +kernel)

theorem h9504 : P.leaf 34 9504 = 352 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 9504) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 9504) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover9504 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h5440 : P.leaf 34 5440 = 352 :=
  orient32 (v := 9504) (by decide) (by decide +kernel) h9504

theorem cover5441 : P.CoversSplit 24 10 5441 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [523]) (by decide +kernel)

theorem h5441 : P.leaf 34 5441 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5441) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5441) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover5441 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover5443 : P.CoversSplit 24 10 5443 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [523]) (by decide +kernel)

theorem h5443 : P.leaf 34 5443 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5443) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5443) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover5443 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover5444 : P.CoversSplit 24 10 5444 0x800000000000040000000000000000000000000000000000000000000000000000000000000100010020000000010000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 465, 473, 515, 516, 522, 523, 565, 572, 858, 860, 865, 916]) (by decide +kernel)

theorem h5444 : P.leaf 34 5444 = 2184 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 5444) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 5444) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5444) (weight := rowWeight keep0 twice0) (xs := [16, 53, 64, 80, 330, 383]) check rows elimOK (by decide) (by decide) cover5444 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover5445 : P.CoversSplit 24 10 5445 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [523]) (by decide +kernel)

theorem h5445 : P.leaf 34 5445 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5445) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5445) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover5445 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover5447 : P.CoversSplit 24 10 5447 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [523]) (by decide +kernel)

theorem h5447 : P.leaf 34 5447 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5447) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5447) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover5447 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover5448 : P.CoversSplit 24 10 5448 0x800000000000040000000000000000000000000000000000000000000000000000000000000100010020000000010000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 465, 473, 515, 516, 522, 523, 565, 858, 865, 1202, 1209, 1258, 1259]) (by decide +kernel)

theorem h5448 : P.leaf 34 5448 = 2232 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 5448) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 5448) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5448) (weight := rowWeight keep0 twice0) (xs := [16, 53, 64, 80, 330, 383]) check rows elimOK (by decide) (by decide) cover5448 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover5449 : P.CoversSplit 24 10 5449 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [523]) (by decide +kernel)

theorem h5449 : P.leaf 34 5449 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5449) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5449) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover5449 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover5451 : P.CoversSplit 24 10 5451 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [523]) (by decide +kernel)

theorem h5451 : P.leaf 34 5451 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5451) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5451) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover5451 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover5452 : P.CoversSplit 24 10 5452 0x800000000000040000000000000000000000000000000000000000000000000000000000000100010020000000010000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 465, 473, 515, 516, 522, 523, 565, 572, 858, 860, 865, 916]) (by decide +kernel)

theorem h5452 : P.leaf 34 5452 = 17856 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 5452) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 5452) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5452) (weight := rowWeight keep0 twice0) (xs := [16, 53, 64, 80, 330, 383]) check rows elimOK (by decide) (by decide) cover5452 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover5453 : P.CoversSplit 24 10 5453 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [523]) (by decide +kernel)

theorem h5453 : P.leaf 34 5453 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5453) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5453) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover5453 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover5455 : P.CoversSplit 24 10 5455 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [523]) (by decide +kernel)

theorem h5455 : P.leaf 34 5455 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5455) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5455) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover5455 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h5456 : P.leaf 34 5456 = 0 := by
  exact leaf_contract_zero (ss := [(28, 2, 466), (7, 6, 467), (29, 2, 472), (6, 1, 479), (15, 2, 486), (14, 8, 509), (8, 1, 482), (2, 1, 468), (26, 1, 465), (27, 1, 473), (35, 0, 867), (34, 5, 523), (16, 10, 872), (33, 0, 909), (31, 5, 565), (18, 11, 879), (5, 1, 1210), (3, 1, 409), (4, 1, 410), (10, 1, 458), (11, 1, 459), (12, 1, 460), (17, 1, 537), (19, 1, 586), (30, 1, 858), (32, 1, 865)]) (q := 1266) check rows (by decide) (by decide +kernel) (by decide +kernel)

def seg : List (ℕ × ℕ) := [(5356, 48), (5357, 48), (5358, 48), (5359, 48), (5361, 24), (5362, 48), (5363, 48), (5364, 48), (5365, 48), (5366, 48), (5367, 48), (5368, 48), (5369, 48), (5370, 48), (5371, 48), (5372, 48), (5373, 48), (5374, 48), (5375, 48), (5440, 12), (5441, 24), (5443, 12), (5444, 12), (5445, 24), (5447, 12), (5448, 12), (5449, 24), (5451, 12), (5452, 12), (5453, 24), (5455, 12), (5456, 24)]

theorem segOK : checkSeg 16 perms 5356 5457 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 5356 5457 1104 1844438304 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 1844438304)
    (SegSum.cons (w := 48) h5356 (SegSum.cons (w := 48) h5357 (SegSum.cons (w := 48) h5358 (SegSum.cons (w := 48) h5359 (SegSum.cons (w := 24) h5361 (SegSum.cons (w := 48) h5362 (SegSum.cons (w := 48) h5363 (SegSum.cons (w := 48) h5364 (SegSum.cons (w := 48) h5365 (SegSum.cons (w := 48) h5366 (SegSum.cons (w := 48) h5367 (SegSum.cons (w := 48) h5368 (SegSum.cons (w := 48) h5369 (SegSum.cons (w := 48) h5370 (SegSum.cons (w := 48) h5371 (SegSum.cons (w := 48) h5372 (SegSum.cons (w := 48) h5373 (SegSum.cons (w := 48) h5374 (SegSum.cons (w := 48) h5375 (SegSum.cons (w := 12) h5440 (SegSum.cons (w := 24) h5441 (SegSum.cons (w := 12) h5443 (SegSum.cons (w := 12) h5444 (SegSum.cons (w := 24) h5445 (SegSum.cons (w := 12) h5447 (SegSum.cons (w := 12) h5448 (SegSum.cons (w := 24) h5449 (SegSum.cons (w := 12) h5451 (SegSum.cons (w := 12) h5452 (SegSum.cons (w := 24) h5453 (SegSum.cons (w := 12) h5455 (SegSum.cons (w := 24) h5456 (show SegSum (P.leaf 34) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S4N1.C0.S26
