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

namespace RACert.S4N1.C0.S35

open RACert RACert.Problem

theorem cover17583 : P.CoversSplit 24 10 17583 0xa0000000a00000000000000000000000a0000000000005000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [515, 517, 522, 573, 858, 865, 916, 921]) (ps := [(14, [908, 965], [867])]) (by decide +kernel)

theorem h17583 : P.leaf 34 17583 = 165132 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 17583) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 17583) (weight := fun _ => 1) (xs := [840, 842, 893, 895, 989, 991, 1021, 1023]) check rows elimOK (by decide) (by decide) cover17583 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h6389 : P.leaf 34 6389 = 165132 :=
  orient4 (v := 17583) (by decide) (by decide +kernel) h17583

theorem cover6390 : P.CoversSplit 24 10 6390 0xf0f00000a0a500000000000000000000f0f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 573, 858, 859, 865, 866, 879, 1202, 1210, 1259]) (by decide +kernel)

theorem h6390 : P.leaf 34 6390 = 1036068 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 6390) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 6390) (weight := fun _ => 1) (xs := [884, 885, 886, 887, 892, 893, 894, 895, 976, 978, 981, 983, 989, 991, 1012, 1013, 1014, 1015, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover6390 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover17599 : P.CoversSplit 24 10 17599 0xff00fa00fa000000ff00fa00fa000000f500f00000000000f500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [517, 573, 858, 860, 865, 867, 872, 916, 921, 1202, 1217, 1251]) (by decide +kernel)

theorem c17599_0 : P.sumLeaves 24 18021376 1024 = 8969224 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 17599) (lo := 0) (len := 1024) (W := 8969224) check rows elimOK (by decide) (by decide) cover17599 (by decide)
  decide +kernel

theorem h17599 : P.leaf 34 17599 = 8969224 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 8969224)]) (.cons c17599_0 (.nil)) (by decide) (by decide))

theorem h6391 : P.leaf 34 6391 = 8969224 :=
  orient4 (v := 17599) (by decide) (by decide +kernel) h17599

theorem cover6392 : P.CoversSplit 24 10 6392 0xf0000000a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 487, 858, 859, 865, 879, 909, 916, 1202, 1210, 1259, 1264]) (by decide +kernel)

theorem h6392 : P.leaf 34 6392 = 87768 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 6392) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 6392) (weight := fun _ => 1) (xs := [989, 991, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover6392 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover6393 : P.CoversSplit 24 10 6393 0xff000000af000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 487, 858, 865, 879, 909, 1202, 1209, 1210, 1259, 1264]) (by decide +kernel)

theorem h6393 : P.leaf 34 6393 = 793910 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 6393) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 6393) (weight := fun _ => 1) (xs := [984, 985, 986, 987, 989, 991, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover6393 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover17630 : P.CoversSplit 24 10 17630 0xa0000000a0000000a0000000a0000000a000000000000500a000000000000500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 516, 536, 573, 858, 865, 867, 916, 921, 1202]) (by decide +kernel)

theorem h17630 : P.leaf 34 17630 = 889110 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 17630) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 17630) (weight := fun _ => 1) (xs := [776, 778, 829, 831, 840, 842, 893, 895, 925, 927, 957, 959, 989, 991, 1021, 1023]) check rows elimOK (by decide) (by decide) cover17630 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h6394 : P.leaf 34 6394 = 889110 :=
  orient4 (v := 17630) (by decide) (by decide +kernel) h17630

theorem cover6395 : P.CoversSplit 24 10 6395 0xffff0000afaa00000000000000000000ffff0000afaa00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [487, 573, 858, 865, 879, 909, 916, 1202, 1209, 1210, 1259, 1264]) (by decide +kernel)

theorem c6395_0 : P.sumLeaves 24 6548480 1024 = 7402392 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6395) (lo := 0) (len := 1024) (W := 7402392) check rows elimOK (by decide) (by decide) cover6395 (by decide)
  decide +kernel

theorem h6395 : P.leaf 34 6395 = 7402392 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 7402392)]) (.cons c6395_0 (.nil)) (by decide) (by decide))

theorem cover6396 : P.CoversSplit 24 10 6396 0xf0000000a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 573, 858, 859, 865, 879, 916, 1202, 1210, 1259, 1264, 1308]) (by decide +kernel)

theorem h6396 : P.leaf 34 6396 = 289850 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 6396) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 6396) (weight := fun _ => 1) (xs := [989, 991, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover6396 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover17647 : P.CoversSplit 24 10 17647 0xf0005500f00000000000000000000000f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [515, 522, 573, 858, 860, 865, 916, 921, 1202, 1210]) (ps := [(14, [908, 965], [867])]) (by decide +kernel)

theorem h17647 : P.leaf 34 17647 = 1388372 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 17647) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 17647) (weight := fun _ => 1) (xs := [892, 893, 894, 895, 988, 989, 990, 991, 1000, 1002, 1004, 1006, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover17647 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h6397 : P.leaf 34 6397 = 1388372 :=
  orient4 (v := 17647) (by decide) (by decide +kernel) h17647

theorem cover6398 : P.CoversSplit 24 10 6398 0xf0f00000a0a500000000000000000000f0f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 573, 858, 859, 865, 879, 1202, 1210, 1259, 1264]) (by decide +kernel)

theorem h6398 : P.leaf 34 6398 = 2941200 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 6398) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 6398) (weight := fun _ => 1) (xs := [884, 885, 886, 887, 892, 893, 894, 895, 976, 978, 981, 983, 989, 991, 1012, 1013, 1014, 1015, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover6398 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover17663 : P.CoversSplit 24 10 17663 0xff00fa00fa000000ff00fa00fa000000ff00fa00fa000000ff00fa00fa000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [573, 858, 860, 865, 867, 916, 921, 1202, 1210]) (by decide +kernel)

theorem c17663_0 : P.sumLeaves 24 18086912 1024 = 24646665 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 17663) (lo := 0) (len := 1024) (W := 24646665) check rows elimOK (by decide) (by decide) cover17663 (by decide)
  decide +kernel

theorem h17663 : P.leaf 34 17663 = 24646665 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 24646665)]) (.cons c17663_0 (.nil)) (by decide) (by decide))

theorem h6399 : P.leaf 34 6399 = 24646665 :=
  orient4 (v := 17663) (by decide) (by decide +kernel) h17663

theorem cover6432 : P.CoversSplit 24 10 6432 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem h6432 : P.leaf 34 6432 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 6432) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 6432) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover6432 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover9424 : P.CoversSplit 24 10 9424 0x9000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [508, 516, 536, 573, 858, 860, 865, 867, 872, 908, 1202, 1209, 1210, 1259]) (ps := [(6, [479, 487], [465, 473])]) (by decide +kernel)

theorem h9424 : P.leaf 34 9424 = 1360 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 9424) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 9424) (weight := fun _ => 1) (xs := [383, 1020, 1023]) check rows elimOK (by decide) (by decide) cover9424 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h6433 : P.leaf 34 6433 = 1360 :=
  orient32 (v := 9424) (by decide) (by decide +kernel) h9424

theorem cover6435 : P.CoversSplit 24 10 6435 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 515, 517, 522, 523, 524, 566, 858, 865, 1209, 1217, 1258, 1266, 1609]) (by decide +kernel)

theorem h6435 : P.leaf 34 6435 = 88300 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 6435) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 6435) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 6435) (weight := rowWeight keep1 twice1) (xs := [511, 720, 895, 1023]) check rows elimOK (by decide) (by decide) cover6435 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover6436 : P.CoversSplit 24 10 6436 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem h6436 : P.leaf 34 6436 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 6436) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 6436) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover6436 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover6437 : P.CoversSplit 24 10 6437 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000002000000001000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [466, 473, 515, 522, 524, 529, 572, 858, 865, 1202, 1209, 1258]) (by decide +kernel)

theorem h6437 : P.leaf 34 6437 = 10432 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 6437) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 6437) (weight := fun _ => 1) (xs := [144, 181, 511, 1023]) check rows elimOK (by decide) (by decide) cover6437 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover6438 : P.CoversSplit 24 10 6438 0x8000000000000000000000000000000080000000000004000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 466, 515, 517, 522, 529, 565, 858, 865, 1209, 1258, 1259]) (by decide +kernel)

theorem h6438 : P.leaf 34 6438 = 10978 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 6438) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 6438) (weight := fun _ => 1) (xs := [576, 842, 895, 1023]) check rows elimOK (by decide) (by decide) cover6438 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover6439 : P.CoversSplit 24 10 6439 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 515, 517, 522, 523, 524, 566, 858, 865, 1209, 1217, 1258, 1266, 1609]) (by decide +kernel)

theorem h6439 : P.leaf 34 6439 = 264758 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 6439) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 6439) (weight := fun _ => 1) (xs := [511, 720, 895, 1023]) check rows elimOK (by decide) (by decide) cover6439 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover6444 : P.CoversSplit 24 10 6444 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem h6444 : P.leaf 34 6444 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 6444) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 6444) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover6444 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover6445 : P.CoversSplit 24 10 6445 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000002000000001000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [466, 473, 515, 522, 524, 529, 572, 858, 865, 1202, 1209, 1258]) (by decide +kernel)

theorem h6445 : P.leaf 34 6445 = 78780 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 6445) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 6445) (weight := fun _ => 1) (xs := [144, 181, 511, 1023]) check rows elimOK (by decide) (by decide) cover6445 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover6447 : P.CoversSplit 24 10 6447 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 515, 517, 522, 523, 524, 566, 858, 865, 1209, 1217, 1258, 1266, 1609]) (by decide +kernel)

theorem h6447 : P.leaf 34 6447 = 671819 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 6447) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 6447) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 6447) (weight := rowWeight keep1 twice1) (xs := [511, 720, 895, 1023]) check rows elimOK (by decide) (by decide) cover6447 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover17671 : P.CoversSplit 24 10 17671 0x8000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 516, 517, 522, 528, 529, 572, 858, 865, 872, 915]) (by decide +kernel)

theorem h17671 : P.leaf 34 17671 = 21120 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 17671) (keep := keep5) (twice := twice5) rows (by decide) (by decide) bal5 (invRow5 (H := 17671) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 17671) (weight := rowWeight keep5 twice5) (xs := [383, 511, 895, 1023]) check rows elimOK (by decide) (by decide) cover17671 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h6449 : P.leaf 34 6449 = 21120 :=
  orient4 (v := 17671) (by decide) (by decide +kernel) h17671

theorem cover6451 : P.CoversSplit 24 10 6451 0xffff0000000000000000000000000000ffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffff0000000000000000000000000000ffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [517, 572, 858, 859, 865, 866, 867, 908, 1202, 1209, 1210, 1258]) (by decide +kernel)

noncomputable def f6451 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (6605824 + i)

theorem c6451_0 : rowSum f6451 0 1024 = 1523532 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 6451) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover6451 (by decide)
  decide +kernel

theorem sum6451 : rowSum f6451 0 1024 = 1523532 :=
  c6451_0

theorem h6451 : P.leaf 34 6451 = 1523532 :=
  leaf_weighted (k := 24) (d := 10) (H := 6451) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 6451) (by decide) (by decide +kernel)) sum6451

theorem cover6452 : P.CoversSplit 24 10 6452 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 508, 517, 529, 572, 858, 859, 865, 866, 879, 916, 1202, 1209, 1210, 1258]) (by decide +kernel)

theorem h6452 : P.leaf 34 6452 = 9080 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 6452) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 6452) (weight := fun _ => 1) (xs := [383, 1023]) check rows elimOK (by decide) (by decide) cover6452 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover17703 : P.CoversSplit 24 10 17703 0x8000000080000000000000000000000080000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000080000000800000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 517, 522, 529, 572, 858, 860, 865, 872, 915, 916]) (by decide +kernel)

theorem h17703 : P.leaf 34 17703 = 164992 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 17703) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 17703) (weight := fun _ => 1) (xs := [383, 479, 511, 842, 895, 991, 1023]) check rows elimOK (by decide) (by decide) cover17703 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h6453 : P.leaf 34 6453 = 164992 :=
  orient4 (v := 17703) (by decide) (by decide +kernel) h17703

theorem cover6454 : P.CoversSplit 24 10 6454 0xa0a00000000000000000000000000000a0a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 517, 529, 572, 858, 865, 866, 879, 1202, 1209, 1210, 1258]) (by decide +kernel)

theorem h6454 : P.leaf 34 6454 = 138676 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 6454) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 6454) (weight := fun _ => 1) (xs := [885, 887, 893, 895, 1013, 1015, 1021, 1023]) check rows elimOK (by decide) (by decide) cover6454 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover6455 : P.CoversSplit 24 10 6455 0xffff0000000000000000000000000000ffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffff0000000000000000000000000000ffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [517, 572, 858, 859, 865, 866, 908, 1202, 1209, 1210, 1251, 1258]) (by decide +kernel)

theorem c6455_0 : P.sumLeaves 24 6609920 1024 = 3947048 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6455) (lo := 0) (len := 1024) (W := 3947048) check rows elimOK (by decide) (by decide) cover6455 (by decide)
  decide +kernel

theorem h6455 : P.leaf 34 6455 = 3947048 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 3947048)]) (.cons c6455_0 (.nil)) (by decide) (by decide))

theorem cover6460 : P.CoversSplit 24 10 6460 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 508, 517, 529, 572, 858, 859, 865, 879, 916, 1202, 1209, 1210, 1258]) (by decide +kernel)

theorem h6460 : P.leaf 34 6460 = 109448 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 6460) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 6460) (weight := fun _ => 1) (xs := [383, 1023]) check rows elimOK (by decide) (by decide) cover6460 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover6461 : P.CoversSplit 24 10 6461 0xcc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 517, 529, 572, 858, 865, 879, 1202, 1209, 1210, 1251, 1258, 1259]) (by decide +kernel)

theorem h6461 : P.leaf 34 6461 = 946520 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 6461) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 6461) (weight := fun _ => 1) (xs := [506, 507, 510, 511, 1018, 1019, 1022, 1023]) check rows elimOK (by decide) (by decide) cover6461 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover6463 : P.CoversSplit 24 10 6463 0xffff0000000000000000000000000000ffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffff0000000000000000000000000000ffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [517, 572, 858, 865, 1202, 1209, 1210, 1251, 1258, 1264]) (by decide +kernel)

noncomputable def f6463 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (6618112 + i)

theorem c6463_0 : rowSum f6463 0 1024 = 10226272 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 6463) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover6463 (by decide)
  decide +kernel

theorem sum6463 : rowSum f6463 0 1024 = 10226272 :=
  c6463_0

theorem h6463 : P.leaf 34 6463 = 10226272 :=
  leaf_weighted (k := 24) (d := 10) (H := 6463) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 6463) (by decide) (by decide +kernel)) sum6463

theorem cover6496 : P.CoversSplit 24 10 6496 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem h6496 : P.leaf 34 6496 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 6496) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 6496) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover6496 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover17677 : P.CoversSplit 24 10 17677 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 515, 516, 517, 522, 528, 529, 572, 858, 860, 865, 872, 915]) (ps := [(8, [615], [565])]) (by decide +kernel)

theorem h17677 : P.leaf 34 17677 = 4700 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 17677) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 17677) (weight := fun _ => 1) (xs := [177, 511, 1023]) check rows elimOK (by decide) (by decide) cover17677 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h6497 : P.leaf 34 6497 = 4700 :=
  orient4 (v := 17677) (by decide) (by decide +kernel) h17677

def seg : List (ℕ × ℕ) := [(6389, 48), (6390, 48), (6391, 48), (6392, 48), (6393, 48), (6394, 48), (6395, 48), (6396, 48), (6397, 48), (6398, 48), (6399, 48), (6432, 6), (6433, 24), (6435, 12), (6436, 24), (6437, 24), (6438, 24), (6439, 24), (6444, 12), (6445, 24), (6447, 12), (6449, 24), (6451, 24), (6452, 48), (6453, 48), (6454, 48), (6455, 48), (6460, 24), (6461, 48), (6463, 24), (6496, 24), (6497, 48)]

theorem segOK : checkSeg 16 perms 6389 6498 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 6389 6498 1122 2886435684 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 2886435684)
    (SegSum.cons (w := 48) h6389 (SegSum.cons (w := 48) h6390 (SegSum.cons (w := 48) h6391 (SegSum.cons (w := 48) h6392 (SegSum.cons (w := 48) h6393 (SegSum.cons (w := 48) h6394 (SegSum.cons (w := 48) h6395 (SegSum.cons (w := 48) h6396 (SegSum.cons (w := 48) h6397 (SegSum.cons (w := 48) h6398 (SegSum.cons (w := 48) h6399 (SegSum.cons (w := 6) h6432 (SegSum.cons (w := 24) h6433 (SegSum.cons (w := 12) h6435 (SegSum.cons (w := 24) h6436 (SegSum.cons (w := 24) h6437 (SegSum.cons (w := 24) h6438 (SegSum.cons (w := 24) h6439 (SegSum.cons (w := 12) h6444 (SegSum.cons (w := 24) h6445 (SegSum.cons (w := 12) h6447 (SegSum.cons (w := 24) h6449 (SegSum.cons (w := 24) h6451 (SegSum.cons (w := 48) h6452 (SegSum.cons (w := 48) h6453 (SegSum.cons (w := 48) h6454 (SegSum.cons (w := 48) h6455 (SegSum.cons (w := 24) h6460 (SegSum.cons (w := 48) h6461 (SegSum.cons (w := 24) h6463 (SegSum.cons (w := 24) h6496 (SegSum.cons (w := 48) h6497 (show SegSum (P.leaf 34) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S4N1.C0.S35
