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

namespace RACert.S4N1.C0.S36

open RACert RACert.Problem

theorem cover6498 : P.CoversSplit 24 10 6498 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 465, 466, 515, 522, 523, 565, 858, 859, 865, 879, 1209, 1258]) (by decide +kernel)

theorem h6498 : P.leaf 34 6498 = 7680 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 6498) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 6498) (weight := fun _ => 1) (xs := [720, 895, 1023]) check rows elimOK (by decide) (by decide) cover6498 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover6499 : P.CoversSplit 24 10 6499 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 515, 522, 523, 572, 858, 865, 1209, 1217, 1258, 1266, 1609]) (by decide +kernel)

theorem h6499 : P.leaf 34 6499 = 220029 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 6499) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 6499) (weight := fun _ => 1) (xs := [511, 592, 720, 895, 1023]) check rows elimOK (by decide) (by decide) cover6499 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover6500 : P.CoversSplit 24 10 6500 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem h6500 : P.leaf 34 6500 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 6500) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 6500) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover6500 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover6501 : P.CoversSplit 24 10 6501 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000002000000001000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 466, 473, 515, 522, 572, 858, 865, 879, 1202, 1209, 1210, 1258]) (by decide +kernel)

theorem h6501 : P.leaf 34 6501 = 42568 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 6501) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 6501) (weight := fun _ => 1) (xs := [144, 181, 511, 1023]) check rows elimOK (by decide) (by decide) cover6501 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover6502 : P.CoversSplit 24 10 6502 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 465, 466, 515, 522, 523, 565, 858, 859, 865, 879, 1209, 1258]) (by decide +kernel)

theorem h6502 : P.leaf 34 6502 = 150344 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 6502) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 6502) (weight := fun _ => 1) (xs := [720, 895, 1023]) check rows elimOK (by decide) (by decide) cover6502 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover6503 : P.CoversSplit 24 10 6503 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 515, 522, 523, 572, 858, 865, 1209, 1217, 1258, 1266, 1609]) (by decide +kernel)

theorem h6503 : P.leaf 34 6503 = 729952 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 6503) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 6503) (weight := fun _ => 1) (xs := [511, 592, 720, 895, 1023]) check rows elimOK (by decide) (by decide) cover6503 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover6504 : P.CoversSplit 24 10 6504 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem h6504 : P.leaf 34 6504 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 6504) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 6504) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover6504 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover6505 : P.CoversSplit 24 10 6505 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000002000000001000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 466, 473, 515, 522, 572, 858, 865, 879, 1202, 1209, 1210, 1258]) (by decide +kernel)

theorem h6505 : P.leaf 34 6505 = 29814 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 6505) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 6505) (weight := fun _ => 1) (xs := [144, 181, 511, 1023]) check rows elimOK (by decide) (by decide) cover6505 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover6506 : P.CoversSplit 24 10 6506 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 465, 466, 515, 522, 523, 565, 858, 859, 865, 879, 1209, 1258]) (by decide +kernel)

theorem h6506 : P.leaf 34 6506 = 40888 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 6506) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 6506) (weight := fun _ => 1) (xs := [720, 895, 1023]) check rows elimOK (by decide) (by decide) cover6506 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover6507 : P.CoversSplit 24 10 6507 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 515, 522, 523, 572, 858, 865, 1209, 1217, 1258, 1266, 1609]) (by decide +kernel)

theorem h6507 : P.leaf 34 6507 = 419724 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 6507) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 6507) (weight := fun _ => 1) (xs := [511, 592, 720, 895, 1023]) check rows elimOK (by decide) (by decide) cover6507 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover6508 : P.CoversSplit 24 10 6508 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem h6508 : P.leaf 34 6508 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 6508) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 6508) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover6508 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover6509 : P.CoversSplit 24 10 6509 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000002000000001000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 466, 473, 515, 522, 572, 858, 865, 879, 1202, 1209, 1210, 1258]) (by decide +kernel)

theorem h6509 : P.leaf 34 6509 = 216196 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 6509) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 6509) (weight := fun _ => 1) (xs := [144, 181, 511, 1023]) check rows elimOK (by decide) (by decide) cover6509 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover6510 : P.CoversSplit 24 10 6510 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 465, 466, 515, 522, 523, 565, 858, 859, 865, 879, 1209, 1258]) (by decide +kernel)

theorem h6510 : P.leaf 34 6510 = 284434 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 6510) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 6510) (weight := fun _ => 1) (xs := [720, 895, 1023]) check rows elimOK (by decide) (by decide) cover6510 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover6511 : P.CoversSplit 24 10 6511 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 515, 522, 523, 572, 858, 865, 1209, 1217, 1258, 1266, 1609]) (by decide +kernel)

theorem h6511 : P.leaf 34 6511 = 1335620 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 6511) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 6511) (weight := fun _ => 1) (xs := [511, 592, 720, 895, 1023]) check rows elimOK (by decide) (by decide) cover6511 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover17679 : P.CoversSplit 24 10 17679 0x8000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 516, 517, 522, 528, 529, 572, 858, 865, 872, 915]) (by decide +kernel)

theorem h17679 : P.leaf 34 17679 = 74016 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 17679) (keep := keep5) (twice := twice5) rows (by decide) (by decide) bal5 (invRow5 (H := 17679) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 17679) (weight := rowWeight keep5 twice5) (xs := [383, 511, 895, 1023]) check rows elimOK (by decide) (by decide) cover17679 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h6513 : P.leaf 34 6513 = 74016 :=
  orient4 (v := 17679) (by decide) (by decide +kernel) h17679

theorem cover17694 : P.CoversSplit 24 10 17694 0xa000000000000000a000000000000000a000000000000000a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 516, 517, 528, 572, 858, 865, 867, 872, 915, 921]) (by decide +kernel)

theorem h17694 : P.leaf 34 17694 = 158144 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 17694) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 17694) (weight := fun _ => 1) (xs := [829, 831, 893, 895, 957, 959, 1021, 1023]) check rows elimOK (by decide) (by decide) cover17694 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h6514 : P.leaf 34 6514 = 158144 :=
  orient4 (v := 17694) (by decide) (by decide +kernel) h17694

theorem cover17695 : P.CoversSplit 24 10 17695 0xff00fa00f0000a00ff00fa00f0000a00f500000000000000f5000000000000000000000000000000000000000000000000000000000000000000000000000000f000f000f0000000f0000000f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [516, 529, 572, 858, 860, 872, 909, 915, 921, 1202, 1210, 1264]) (ps := [(8, [615], [1266])]) (by decide +kernel)

theorem c17695_0 : P.sumLeaves 24 18119680 1024 = 4025932 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 17695) (lo := 0) (len := 1024) (W := 4025932) check rows elimOK (by decide) (by decide) cover17695 (by decide)
  decide +kernel

theorem h17695 : P.leaf 34 17695 = 4025932 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 4025932)]) (.cons c17695_0 (.nil)) (by decide) (by decide))

theorem h6515 : P.leaf 34 6515 = 4025932 :=
  orient4 (v := 17695) (by decide) (by decide +kernel) h17695

theorem cover17710 : P.CoversSplit 24 10 17710 0x8000000080000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 515, 517, 522, 529, 572, 858, 860, 865, 872, 915, 921]) (ps := [(14, [965], [867])]) (by decide +kernel)

theorem h17710 : P.leaf 34 17710 = 52736 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 17710) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 17710) (weight := fun _ => 1) (xs := [895, 991, 1023]) check rows elimOK (by decide) (by decide) cover17710 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h6516 : P.leaf 34 6516 = 52736 :=
  orient4 (v := 17710) (by decide) (by decide +kernel) h17710

theorem cover17711 : P.CoversSplit 24 10 17711 0x8000000080000000000000000000000080000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000080000000800000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 517, 522, 529, 572, 858, 860, 865, 872, 915, 916]) (by decide +kernel)

theorem h17711 : P.leaf 34 17711 = 669472 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 17711) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 17711) (weight := fun _ => 1) (xs := [383, 479, 511, 842, 895, 991, 1023]) check rows elimOK (by decide) (by decide) cover17711 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h6517 : P.leaf 34 6517 = 669472 :=
  orient4 (v := 17711) (by decide) (by decide +kernel) h17711

theorem cover6518 : P.CoversSplit 24 10 6518 0xf0f00000a0a500000000000000000000f0f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 572, 858, 859, 865, 866, 879, 1202, 1258, 1259]) (by decide +kernel)

theorem h6518 : P.leaf 34 6518 = 1513312 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 6518) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 6518) (weight := fun _ => 1) (xs := [884, 885, 886, 887, 892, 893, 894, 895, 976, 978, 981, 983, 989, 991, 1012, 1013, 1014, 1015, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover6518 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover17727 : P.CoversSplit 24 10 17727 0xff00fa00fa000000ff00fa00fa000000f500f00000000000f5000000000000000000000000000000000000000000000000000000000000000000000000000000f000f000f0000000f0000000f0000000f000f00000000000f0000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [517, 529, 572, 858, 860, 865, 872, 909, 915, 921, 1202, 1217, 1251, 1264, 1308]) (by decide +kernel)

theorem c17727_0 : P.sumLeaves 24 18152448 1024 = 18106750 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 17727) (lo := 0) (len := 1024) (W := 18106750) check rows elimOK (by decide) (by decide) cover17727 (by decide)
  decide +kernel

theorem h17727 : P.leaf 34 17727 = 18106750 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 18106750)]) (.cons c17727_0 (.nil)) (by decide) (by decide))

theorem h6519 : P.leaf 34 6519 = 18106750 :=
  orient4 (v := 17727) (by decide) (by decide +kernel) h17727

theorem cover6520 : P.CoversSplit 24 10 6520 0xc000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 508, 572, 858, 859, 865, 879, 909, 916, 1202, 1258, 1259, 1308]) (by decide +kernel)

theorem h6520 : P.leaf 34 6520 = 30400 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 6520) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 6520) (weight := fun _ => 1) (xs := [991, 1022, 1023]) check rows elimOK (by decide) (by decide) cover6520 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover17743 : P.CoversSplit 24 10 17743 0xc0000400c00000000000000000000000c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c0000000c00000000000000000000000c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [515, 516, 522, 572, 858, 865, 872, 915, 916, 1202, 1210]) (ps := [(11, [879], [858])]) (by decide +kernel)

theorem h17743 : P.leaf 34 17743 = 245772 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 17743) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 17743) (weight := fun _ => 1) (xs := [382, 383, 478, 479, 510, 511, 894, 895, 990, 991, 1002, 1022, 1023]) check rows elimOK (by decide) (by decide) cover17743 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h6521 : P.leaf 34 6521 = 245772 :=
  orient4 (v := 17743) (by decide) (by decide +kernel) h17743

theorem cover17758 : P.CoversSplit 24 10 17758 0xa0000000a0000000a0000000a0000000a000000000000500a000000000000500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 516, 572, 858, 865, 867, 915, 921, 1202]) (by decide +kernel)

theorem h17758 : P.leaf 34 17758 = 563730 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 17758) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 17758) (weight := fun _ => 1) (xs := [776, 778, 829, 831, 840, 842, 893, 895, 925, 927, 957, 959, 989, 991, 1021, 1023]) check rows elimOK (by decide) (by decide) cover17758 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h6522 : P.leaf 34 6522 = 563730 :=
  orient4 (v := 17758) (by decide) (by decide +kernel) h17758

theorem cover6523 : P.CoversSplit 24 10 6523 0xffff0000afaa00000000000000000000ffff0000afaa000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffff0000afaa00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [572, 858, 865, 867, 916, 1202, 1209, 1217, 1258, 1259, 1264, 1308]) (by decide +kernel)

theorem c6523_0 : P.sumLeaves 24 6679552 1024 = 8470106 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6523) (lo := 0) (len := 1024) (W := 8470106) check rows elimOK (by decide) (by decide) cover6523 (by decide)
  decide +kernel

theorem h6523 : P.leaf 34 6523 = 8470106 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 8470106)]) (.cons c6523_0 (.nil)) (by decide) (by decide))

theorem cover6524 : P.CoversSplit 24 10 6524 0xc000000080008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 508, 572, 858, 859, 865, 879, 916, 1202, 1258, 1259, 1308]) (by decide +kernel)

theorem h6524 : P.leaf 34 6524 = 271340 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 6524) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 6524) (weight := fun _ => 1) (xs := [975, 991, 1022, 1023]) check rows elimOK (by decide) (by decide) cover6524 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover17775 : P.CoversSplit 24 10 17775 0xc0004400c00000000000000000000000c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c0004000c00000000000000000000000c00040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 522, 572, 858, 860, 865, 872, 915, 916, 1202, 1210]) (by decide +kernel)

theorem h17775 : P.leaf 34 17775 = 2200460 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 17775) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 17775) (weight := fun _ => 1) (xs := [366, 382, 383, 478, 479, 494, 510, 511, 894, 895, 990, 991, 1002, 1006, 1022, 1023]) check rows elimOK (by decide) (by decide) cover17775 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h6525 : P.leaf 34 6525 = 2200460 :=
  orient4 (v := 17775) (by decide) (by decide +kernel) h17775

theorem cover6526 : P.CoversSplit 24 10 6526 0xf0f00000a0a500000000000000000000f0f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 572, 858, 859, 865, 879, 1202, 1258, 1259, 1264]) (by decide +kernel)

theorem h6526 : P.leaf 34 6526 = 3347258 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 6526) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 6526) (weight := fun _ => 1) (xs := [884, 885, 886, 887, 892, 893, 894, 895, 976, 978, 981, 983, 989, 991, 1012, 1013, 1014, 1015, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover6526 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover17791 : P.CoversSplit 24 10 17791 0xff00fa00fa00aa00ff00fa00fa00aa00ff00fa00fa00aa00ff00fa00fa00aa000000000000000000000000000000000000000000000000000000000000000000f000f000f000a000f0000000f0000000f000f00000000000f0000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [572, 858, 860, 865, 872, 915, 921, 1202, 1264, 1308]) (by decide +kernel)

theorem c17791_0 : P.sumLeaves 24 18217984 942 = 22492734 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 17791) (lo := 0) (len := 942) (W := 22492734) check rows elimOK (by decide) (by decide) cover17791 (by decide)
  decide +kernel

theorem c17791_1 : P.sumLeaves 24 18218926 82 = 22249086 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 17791) (lo := 942) (len := 82) (W := 22249086) check rows elimOK (by decide) (by decide) cover17791 (by decide)
  decide +kernel

theorem h17791 : P.leaf 34 17791 = 44741820 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(942, 22492734), (82, 22249086)]) (.cons c17791_0 (.cons c17791_1 (.nil))) (by decide) (by decide))

theorem h6527 : P.leaf 34 6527 = 44741820 :=
  orient4 (v := 17791) (by decide) (by decide +kernel) h17791

theorem cover6624 : P.CoversSplit 24 10 6624 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem h6624 : P.leaf 34 6624 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 6624) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 6624) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover6624 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover6625 : P.CoversSplit 24 10 6625 0x8000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 466, 473, 515, 522, 858, 865, 879, 916, 1209, 1258]) (by decide +kernel)

theorem h6625 : P.leaf 34 6625 = 42024 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 6625) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 6625) (weight := fun _ => 1) (xs := [511, 720, 1023]) check rows elimOK (by decide) (by decide) cover6625 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover6627 : P.CoversSplit 24 10 6627 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 515, 522, 858, 859, 865, 866, 1209, 1217, 1258, 1266]) (by decide +kernel)

theorem h6627 : P.leaf 34 6627 = 816324 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 6627) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 6627) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 6627) (weight := rowWeight keep1 twice1) (xs := [208, 511, 592, 720, 895, 1023]) check rows elimOK (by decide) (by decide) cover6627 (by decide) (by decide) (by decide +kernel)
  decide +kernel

def seg : List (ℕ × ℕ) := [(6498, 48), (6499, 48), (6500, 48), (6501, 48), (6502, 48), (6503, 48), (6504, 48), (6505, 48), (6506, 48), (6507, 48), (6508, 48), (6509, 48), (6510, 48), (6511, 48), (6513, 24), (6514, 48), (6515, 48), (6516, 48), (6517, 48), (6518, 48), (6519, 48), (6520, 48), (6521, 48), (6522, 48), (6523, 48), (6524, 48), (6525, 48), (6526, 48), (6527, 48), (6624, 24), (6625, 48), (6627, 24)]

theorem segOK : checkSeg 16 perms 6498 6628 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 6498 6628 1464 4241360400 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 4241360400)
    (SegSum.cons (w := 48) h6498 (SegSum.cons (w := 48) h6499 (SegSum.cons (w := 48) h6500 (SegSum.cons (w := 48) h6501 (SegSum.cons (w := 48) h6502 (SegSum.cons (w := 48) h6503 (SegSum.cons (w := 48) h6504 (SegSum.cons (w := 48) h6505 (SegSum.cons (w := 48) h6506 (SegSum.cons (w := 48) h6507 (SegSum.cons (w := 48) h6508 (SegSum.cons (w := 48) h6509 (SegSum.cons (w := 48) h6510 (SegSum.cons (w := 48) h6511 (SegSum.cons (w := 24) h6513 (SegSum.cons (w := 48) h6514 (SegSum.cons (w := 48) h6515 (SegSum.cons (w := 48) h6516 (SegSum.cons (w := 48) h6517 (SegSum.cons (w := 48) h6518 (SegSum.cons (w := 48) h6519 (SegSum.cons (w := 48) h6520 (SegSum.cons (w := 48) h6521 (SegSum.cons (w := 48) h6522 (SegSum.cons (w := 48) h6523 (SegSum.cons (w := 48) h6524 (SegSum.cons (w := 48) h6525 (SegSum.cons (w := 48) h6526 (SegSum.cons (w := 48) h6527 (SegSum.cons (w := 24) h6624 (SegSum.cons (w := 48) h6625 (SegSum.cons (w := 24) h6627 (show SegSum (P.leaf 34) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S4N1.C0.S36
