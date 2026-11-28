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

namespace RACert.S4N1.C0.S44

open RACert RACert.Problem

theorem cover7585 : P.CoversSplit 24 10 7585 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 466, 473, 515, 522, 524, 566, 858, 865, 916, 1209, 1258, 1266]) (by decide +kernel)

theorem h7585 : P.leaf 34 7585 = 40456 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 7585) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 7585) (weight := fun _ => 1) (xs := [511, 592, 720, 895, 1023]) check rows elimOK (by decide) (by decide) cover7585 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover7587 : P.CoversSplit 24 10 7587 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 515, 517, 522, 524, 566, 858, 865, 1209, 1217, 1258, 1266]) (by decide +kernel)

theorem h7587 : P.leaf 34 7587 = 411694 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 7587) (keep := keep4) (twice := twice4) rows (by decide) (by decide) bal4 (invRow4 (H := 7587) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 7587) (weight := rowWeight keep4 twice4) (xs := [208, 511, 592, 720, 895, 1023]) check rows elimOK (by decide) (by decide) cover7587 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover7588 : P.CoversSplit 24 10 7588 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem h7588 : P.leaf 34 7588 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 7588) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 7588) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover7588 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover7589 : P.CoversSplit 24 10 7589 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 466, 473, 515, 522, 524, 566, 858, 865, 916, 1209, 1258, 1266]) (by decide +kernel)

theorem h7589 : P.leaf 34 7589 = 194376 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 7589) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 7589) (weight := fun _ => 1) (xs := [511, 592, 720, 895, 1023]) check rows elimOK (by decide) (by decide) cover7589 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover7590 : P.CoversSplit 24 10 7590 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 465, 466, 515, 517, 522, 858, 865, 1209, 1258, 1266]) (by decide +kernel)

theorem h7590 : P.leaf 34 7590 = 579234 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 7590) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 7590) (weight := fun _ => 1) (xs := [208, 511, 720, 895, 1023]) check rows elimOK (by decide) (by decide) cover7590 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover7591 : P.CoversSplit 24 10 7591 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 515, 517, 522, 524, 566, 858, 865, 1209, 1217, 1258, 1266]) (by decide +kernel)

theorem h7591 : P.leaf 34 7591 = 1022068 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 7591) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 7591) (weight := fun _ => 1) (xs := [208, 511, 592, 720, 895, 1023]) check rows elimOK (by decide) (by decide) cover7591 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover7596 : P.CoversSplit 24 10 7596 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem h7596 : P.leaf 34 7596 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 7596) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 7596) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover7596 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover7597 : P.CoversSplit 24 10 7597 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 466, 473, 515, 522, 524, 566, 858, 865, 916, 1209, 1258, 1266]) (by decide +kernel)

theorem h7597 : P.leaf 34 7597 = 1047866 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 7597) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 7597) (weight := fun _ => 1) (xs := [511, 592, 720, 895, 1023]) check rows elimOK (by decide) (by decide) cover7597 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover7599 : P.CoversSplit 24 10 7599 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 515, 517, 522, 524, 566, 858, 865, 1209, 1217, 1258, 1266]) (by decide +kernel)

theorem h7599 : P.leaf 34 7599 = 1934426 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 7599) (keep := keep4) (twice := twice4) rows (by decide) (by decide) bal4 (invRow4 (H := 7599) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 7599) (weight := rowWeight keep4 twice4) (xs := [208, 511, 592, 720, 895, 1023]) check rows elimOK (by decide) (by decide) cover7599 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover19847 : P.CoversSplit 24 10 19847 0xaa000000a0000a000000000000000000aa0000000000000000000000000000008800000080000800220000002000000088000000000000002200000000000000aa000000a0000a000000000000000000aa0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [466, 515, 516, 522, 865, 1202, 1210, 1259, 1601]) (by decide +kernel)

noncomputable def f19847 (i : ℕ) := rowWeight keep5 twice5 i * P.leaf 24 (20323328 + i)

theorem c19847_0 : rowSum f19847 0 1024 = 957904 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 19847) (keep := keep5) (twice := twice5) check rows elimOK (by decide) (by decide) cover19847 (by decide)
  decide +kernel

theorem sum19847 : rowSum f19847 0 1024 = 957904 :=
  c19847_0

theorem h19847 : P.leaf 34 19847 = 957904 :=
  leaf_weighted (k := 24) (d := 10) (H := 19847) (keep := keep5) (twice := twice5) rows (by decide) (by decide) (bal5) (invRow5 (H := 19847) (by decide) (by decide +kernel)) sum19847

theorem h7601 : P.leaf 34 7601 = 957904 :=
  orient4 (v := 19847) (by decide) (by decide +kernel) h19847

theorem cover51343 : P.CoversSplit 24 10 51343 0xaa00000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 516, 517, 522, 528, 536, 573, 859, 865, 879, 915, 916, 921]) (by decide +kernel)

theorem h51343 : P.leaf 34 51343 = 969564 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 51343) (keep := keep5) (twice := twice5) rows (by decide) (by decide) bal5 (invRow5 (H := 51343) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 51343) (weight := rowWeight keep5 twice5) (xs := [383, 511, 895, 1017, 1019, 1021, 1023]) check rows elimOK (by decide) (by decide) cover51343 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h7602 : P.leaf 34 7602 = 969564 :=
  orient24 (v := 51343) (by decide) (by decide +kernel) h51343

theorem cover51359 : P.CoversSplit 24 10 51359 0xff00fa00fa000a00ff00fa00fa000a00f500f00040000000f500f000400000000000000000000000000000000000000000000000000000000000000000000000f000f000f0000000f000f000f0000000f000f00040000000f000f000400000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [516, 517, 536, 573, 858, 859, 879, 908, 916, 921, 1202]) (by decide +kernel)

theorem c51359_0 : P.sumLeaves 24 52591616 1004 = 8417816 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 51359) (lo := 0) (len := 1004) (W := 8417816) check rows elimOK (by decide) (by decide) cover51359 (by decide)
  decide +kernel

theorem c51359_1 : P.sumLeaves 24 52592620 20 = 4127970 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 51359) (lo := 1004) (len := 20) (W := 4127970) check rows elimOK (by decide) (by decide) cover51359 (by decide)
  decide +kernel

theorem h51359 : P.leaf 34 51359 = 12545786 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1004, 8417816), (20, 4127970)]) (.cons c51359_0 (.cons c51359_1 (.nil))) (by decide) (by decide))

theorem h7603 : P.leaf 34 7603 = 12545786 :=
  orient24 (v := 51359) (by decide) (by decide +kernel) h51359

theorem cover7604 : P.CoversSplit 24 10 7604 0xf0000000000000000000000000000000a0000000000000000000000000000000c000000000000000c00000000000000080000000000000008000000000000000f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 508, 517, 858, 865, 866, 916, 1202, 1209, 1308, 1601]) (by decide +kernel)

theorem h7604 : P.leaf 34 7604 = 659320 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 7604) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 7604) (weight := fun _ => 1) (xs := [508, 509, 510, 511, 575, 639, 702, 703, 766, 767, 893, 895, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover7604 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover7605 : P.CoversSplit 24 10 7605 0xff000000000000000000000000000000ff000000000000000000000000000000cc030000000000000000000000000000cc030000000000000000000000000000ff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 517, 858, 865, 866, 916, 1202, 1209, 1210, 1251, 1308, 1601]) (by decide +kernel)

theorem c7605_0 : P.sumLeaves 24 7787520 1024 = 2925394 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7605) (lo := 0) (len := 1024) (W := 2925394) check rows elimOK (by decide) (by decide) cover7605 (by decide)
  decide +kernel

theorem h7605 : P.leaf 34 7605 = 2925394 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 2925394)]) (.cons c7605_0 (.nil)) (by decide) (by decide))

theorem cover36777 : P.CoversSplit 24 10 36777 0xcc00cc00c0008000cc00cc00c0008000cc00cc00c0008000cc00cc00c00080000000000000000000000000000000000000000000000000000000000000000000cc00cc00c00080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 515, 522, 915, 921, 1202, 1258, 1308]) (ps := [(14, [923], [1272])]) (by decide +kernel)

theorem c36777_0 : P.sumLeaves 24 37659648 1024 = 8697500 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 36777) (lo := 0) (len := 1024) (W := 8697500) check rows elimOK (by decide) (by decide) cover36777 (by decide)
  decide +kernel

theorem h36777 : P.leaf 34 36777 = 8697500 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 8697500)]) (.cons c36777_0 (.nil)) (by decide) (by decide))

theorem h7606 : P.leaf 34 7606 = 8697500 :=
  orient25 (v := 36777) (by decide) (by decide +kernel) h36777

theorem cover36793 : P.CoversSplit 24 10 36793 0xff00ff00f000a000ff00ff00f000a000ff00ff00f000a000ff00ff00f000a0000000000000000000000000000000000000000000000000000000000000000000ff00ff00f000a000ff00ff00f000a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 517, 915, 921, 1202, 1209, 1308]) (ps := [(14, [923], [1272])]) (by decide +kernel)

theorem c36793_0 : P.sumLeaves 24 37676032 938 = 13643362 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 36793) (lo := 0) (len := 938) (W := 13643362) check rows elimOK (by decide) (by decide) cover36793 (by decide)
  decide +kernel

theorem c36793_1 : P.sumLeaves 24 37676970 86 = 19027991 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 36793) (lo := 938) (len := 86) (W := 19027991) check rows elimOK (by decide) (by decide) cover36793 (by decide)
  decide +kernel

theorem h36793 : P.leaf 34 36793 = 32671353 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(938, 13643362), (86, 19027991)]) (.cons c36793_0 (.cons c36793_1 (.nil))) (by decide) (by decide))

theorem h7607 : P.leaf 34 7607 = 32671353 :=
  orient25 (v := 36793) (by decide) (by decide +kernel) h36793

theorem cover7608 : P.CoversSplit 24 10 7608 0xf0000000000000000000000000000000a0000000000000000000000000000000c000000000000000c00000000000000080000000000000008000000000000000f0000000000000000000000000000000000000000000000000000000000000000000000000000000c00000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 508, 517, 858, 865, 867, 909, 916, 1202, 1209, 1308, 1601]) (by decide +kernel)

theorem h7608 : P.leaf 34 7608 = 637680 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 7608) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 7608) (weight := fun _ => 1) (xs := [190, 191, 508, 509, 510, 511, 575, 639, 702, 703, 766, 767, 893, 895, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover7608 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover7609 : P.CoversSplit 24 10 7609 0xff000000000000000000000000000000ff000000000000000000000000000000cc030000000000000000000000000000cc030000000000000000000000000000ff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 517, 858, 865, 867, 916, 1202, 1209, 1210, 1308, 1601]) (by decide +kernel)

theorem c7609_0 : P.sumLeaves 24 7791616 1024 = 7229070 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7609) (lo := 0) (len := 1024) (W := 7229070) check rows elimOK (by decide) (by decide) cover7609 (by decide)
  decide +kernel

theorem h7609 : P.leaf 34 7609 = 7229070 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 7229070)]) (.cons c7609_0 (.nil)) (by decide) (by decide))

theorem cover51407 : P.CoversSplit 24 10 51407 0xff00fa00fa000000000000000000000080008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080008000800000000000000000000000800080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 516, 522, 536, 573, 858, 859, 865, 879, 916, 921, 1202]) (by decide +kernel)

theorem h51407 : P.leaf 34 51407 = 5528476 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 51407) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 51407) (weight := fun _ => 1) (xs := [367, 383, 479, 495, 511, 879, 895, 985, 987, 988, 989, 990, 991, 1001, 1003, 1004, 1005, 1006, 1007, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover51407 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h7610 : P.leaf 34 7610 = 5528476 :=
  orient24 (v := 51407) (by decide) (by decide +kernel) h51407

theorem cover51423 : P.CoversSplit 24 10 51423 0xff00fa00fa000000ff00fa00fa000000f500f00044000000f500f000440000000000000000000000000000000000000000000000000000000000000000000000f000f000f0000000f000f000f0000000f000f00040000000f000f000400000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [516, 536, 573, 858, 859, 865, 879, 908, 916, 921, 1202]) (by decide +kernel)

theorem c51423_0 : P.sumLeaves 24 52657152 1006 = 22886366 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 51423) (lo := 0) (len := 1006) (W := 22886366) check rows elimOK (by decide) (by decide) cover51423 (by decide)
  decide +kernel

theorem c51423_1 : P.sumLeaves 24 52658158 18 = 6640182 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 51423) (lo := 1006) (len := 18) (W := 6640182) check rows elimOK (by decide) (by decide) cover51423 (by decide)
  decide +kernel

theorem h51423 : P.leaf 34 51423 = 29526548 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1006, 22886366), (18, 6640182)]) (.cons c51423_0 (.cons c51423_1 (.nil))) (by decide) (by decide))

theorem h7611 : P.leaf 34 7611 = 29526548 :=
  orient24 (v := 51423) (by decide) (by decide +kernel) h51423

theorem cover7612 : P.CoversSplit 24 10 7612 0xf0000000000000000000000000000000a0000000000000000000000000000000c000000000000000c00000000000000080000000000000008000000000000000f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 508, 517, 858, 865, 916, 1202, 1209, 1308, 1601]) (by decide +kernel)

theorem h7612 : P.leaf 34 7612 = 2557588 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 7612) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 7612) (weight := fun _ => 1) (xs := [508, 509, 510, 511, 575, 639, 702, 703, 766, 767, 893, 895, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover7612 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover7613 : P.CoversSplit 24 10 7613 0xff000000000000000000000000000000ff000000000000000000000000000000cc030000000000000000000000000000cc030000000000000000000000000000ff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 517, 858, 865, 916, 1202, 1209, 1210, 1251, 1308, 1601]) (by decide +kernel)

theorem c7613_0 : P.sumLeaves 24 7795712 1024 = 14700672 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7613) (lo := 0) (len := 1024) (W := 14700672) check rows elimOK (by decide) (by decide) cover7613 (by decide)
  decide +kernel

theorem h7613 : P.leaf 34 7613 = 14700672 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 14700672)]) (.cons c7613_0 (.nil)) (by decide) (by decide))

theorem cover7614 : P.CoversSplit 24 10 7614 0xf0f0000000000000f0f0000000000000a0a0000000000000a0a0000000000000c0f0000000000000c00000000000000080a00000000000008000000000000000f0f0000000000000f0f000000000000000000000000000000000000000000000c0f0000000000000c00000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 517, 858, 865, 1209, 1308, 1601]) (by decide +kernel)

theorem c7614_0 : P.sumLeaves 24 7796736 1024 = 19055250 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7614) (lo := 0) (len := 1024) (W := 19055250) check rows elimOK (by decide) (by decide) cover7614 (by decide)
  decide +kernel

theorem h7614 : P.leaf 34 7614 = 19055250 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 19055250)]) (.cons c7614_0 (.nil)) (by decide) (by decide))

theorem cover7615 : P.CoversSplit 24 10 7615 0xffff000000000000ffff000000000000ffff000000000000ffff000000000000ccfc000000000000cc00000000000000ccfc000000000000cc00000000000000ffff000000000000ffff00000000000000000000000000000000000000000000ccfc000000000000cc0000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [517, 858, 865, 1202, 1209, 1210, 1251, 1258, 1308, 1601]) (by decide +kernel)

theorem c7615_0 : P.sumLeaves 24 7797760 886 = 26503458 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7615) (lo := 0) (len := 886) (W := 26503458) check rows elimOK (by decide) (by decide) cover7615 (by decide)
  decide +kernel

theorem c7615_1 : P.sumLeaves 24 7798646 138 = 39677952 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7615) (lo := 886) (len := 138) (W := 39677952) check rows elimOK (by decide) (by decide) cover7615 (by decide)
  decide +kernel

theorem h7615 : P.leaf 34 7615 = 66181410 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(886, 26503458), (138, 39677952)]) (.cons c7615_0 (.cons c7615_1 (.nil))) (by decide) (by decide))

theorem cover7616 : P.CoversSplit 24 10 7616 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem h7616 : P.leaf 34 7616 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 7616) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 7616) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover7616 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover7617 : P.CoversSplit 24 10 7617 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 466, 473, 515, 522, 523, 858, 865, 916, 1209, 1258, 1272]) (by decide +kernel)

theorem h7617 : P.leaf 34 7617 = 50248 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 7617) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 7617) (weight := fun _ => 1) (xs := [511, 592, 720, 895, 1023]) check rows elimOK (by decide) (by decide) cover7617 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover7619 : P.CoversSplit 24 10 7619 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 515, 516, 522, 523, 858, 865, 1209, 1217, 1258, 1272]) (by decide +kernel)

theorem h7619 : P.leaf 34 7619 = 490484 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 7619) (keep := keep5) (twice := twice5) rows (by decide) (by decide) bal5 (invRow5 (H := 7619) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 7619) (weight := rowWeight keep5 twice5) (xs := [208, 511, 592, 720, 895, 1023]) check rows elimOK (by decide) (by decide) cover7619 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover7620 : P.CoversSplit 24 10 7620 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem h7620 : P.leaf 34 7620 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 7620) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 7620) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover7620 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover7621 : P.CoversSplit 24 10 7621 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 466, 473, 515, 522, 523, 858, 865, 916, 1209, 1258, 1272]) (by decide +kernel)

theorem h7621 : P.leaf 34 7621 = 552556 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 7621) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 7621) (weight := fun _ => 1) (xs := [511, 592, 720, 895, 1023]) check rows elimOK (by decide) (by decide) cover7621 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover7623 : P.CoversSplit 24 10 7623 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 515, 516, 522, 523, 858, 865, 1209, 1217, 1258, 1272]) (by decide +kernel)

theorem h7623 : P.leaf 34 7623 = 2079224 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 7623) (keep := keep5) (twice := twice5) rows (by decide) (by decide) bal5 (invRow5 (H := 7623) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 7623) (weight := rowWeight keep5 twice5) (xs := [208, 511, 592, 720, 895, 1023]) check rows elimOK (by decide) (by decide) cover7623 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover7624 : P.CoversSplit 24 10 7624 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem h7624 : P.leaf 34 7624 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 7624) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 7624) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover7624 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover7625 : P.CoversSplit 24 10 7625 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 466, 473, 515, 522, 523, 858, 865, 916, 1209, 1258, 1272]) (by decide +kernel)

theorem h7625 : P.leaf 34 7625 = 286307 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 7625) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 7625) (weight := fun _ => 1) (xs := [511, 592, 720, 895, 1023]) check rows elimOK (by decide) (by decide) cover7625 (by decide) (by decide) (by decide +kernel)
  decide +kernel

def seg : List (ℕ × ℕ) := [(7585, 48), (7587, 24), (7588, 48), (7589, 48), (7590, 48), (7591, 48), (7596, 24), (7597, 48), (7599, 24), (7601, 24), (7602, 24), (7603, 48), (7604, 48), (7605, 48), (7606, 48), (7607, 48), (7608, 48), (7609, 48), (7610, 48), (7611, 48), (7612, 48), (7613, 48), (7614, 48), (7615, 48), (7616, 12), (7617, 48), (7619, 24), (7620, 24), (7621, 48), (7623, 24), (7624, 24), (7625, 48)]

theorem segOK : checkSeg 16 perms 7585 7627 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 7585 7627 1284 10085318688 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 10085318688)
    (SegSum.cons (w := 48) h7585 (SegSum.cons (w := 24) h7587 (SegSum.cons (w := 48) h7588 (SegSum.cons (w := 48) h7589 (SegSum.cons (w := 48) h7590 (SegSum.cons (w := 48) h7591 (SegSum.cons (w := 24) h7596 (SegSum.cons (w := 48) h7597 (SegSum.cons (w := 24) h7599 (SegSum.cons (w := 24) h7601 (SegSum.cons (w := 24) h7602 (SegSum.cons (w := 48) h7603 (SegSum.cons (w := 48) h7604 (SegSum.cons (w := 48) h7605 (SegSum.cons (w := 48) h7606 (SegSum.cons (w := 48) h7607 (SegSum.cons (w := 48) h7608 (SegSum.cons (w := 48) h7609 (SegSum.cons (w := 48) h7610 (SegSum.cons (w := 48) h7611 (SegSum.cons (w := 48) h7612 (SegSum.cons (w := 48) h7613 (SegSum.cons (w := 48) h7614 (SegSum.cons (w := 48) h7615 (SegSum.cons (w := 12) h7616 (SegSum.cons (w := 48) h7617 (SegSum.cons (w := 24) h7619 (SegSum.cons (w := 24) h7620 (SegSum.cons (w := 48) h7621 (SegSum.cons (w := 24) h7623 (SegSum.cons (w := 24) h7624 (SegSum.cons (w := 48) h7625 (show SegSum (P.leaf 34) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S4N1.C0.S44
