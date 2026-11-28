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

namespace RACert.S4N1.C0.S43

open RACert RACert.Problem

theorem cover19663 : P.CoversSplit 24 10 19663 0xff00fa00f00000000000000000000000ff0000000000f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 522, 536, 858, 865, 916, 921, 1202, 1210]) (by decide +kernel)

theorem h19663 : P.leaf 34 19663 = 4904080 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 19663) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 19663) (weight := fun _ => 1) (xs := [844, 845, 846, 847, 888, 889, 890, 891, 892, 893, 894, 895, 988, 989, 990, 991, 1001, 1003, 1004, 1005, 1006, 1007, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover19663 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h7417 : P.leaf 34 7417 = 4904080 :=
  orient4 (v := 19663) (by decide) (by decide +kernel) h19663

theorem cover7418 : P.CoversSplit 24 10 7418 0xf0f00000f0f500000000000000000000f0f00000f0f5000000000000000000000000000000000000000000000000000000000000000000000000000000000000c0000000c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 487, 573, 858, 865, 867, 909, 916, 1210, 1217, 1259, 1264, 1308]) (by decide +kernel)

theorem c7418_0 : P.sumLeaves 24 7596032 1024 = 5653182 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7418) (lo := 0) (len := 1024) (W := 5653182) check rows elimOK (by decide) (by decide) cover7418 (by decide)
  decide +kernel

theorem h7418 : P.leaf 34 7418 = 5653182 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 5653182)]) (.cons c7418_0 (.nil)) (by decide) (by decide))

theorem cover7419 : P.CoversSplit 24 10 7419 0xffff0000fffa00000000000000000000ffff0000fffa000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000cc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [487, 573, 858, 865, 867, 909, 916, 1209, 1210, 1217, 1259, 1264, 1308]) (by decide +kernel)

theorem c7419_0 : P.sumLeaves 24 7597056 1024 = 14649606 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7419) (lo := 0) (len := 1024) (W := 14649606) check rows elimOK (by decide) (by decide) cover7419 (by decide)
  decide +kernel

theorem h7419 : P.leaf 34 7419 = 14649606 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 14649606)]) (.cons c7419_0 (.nil)) (by decide) (by decide))

theorem cover7420 : P.CoversSplit 24 10 7420 0xf0000000f00000000000000000000000f0000000f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c0000000c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 573, 858, 865, 916, 1210, 1259, 1308]) (by decide +kernel)

theorem h7420 : P.leaf 34 7420 = 1834988 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 7420) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 7420) (weight := fun _ => 1) (xs := [478, 479, 510, 511, 860, 861, 862, 863, 892, 893, 894, 895, 988, 989, 990, 991, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover7420 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover19695 : P.CoversSplit 24 10 19695 0xff00fa00fa0000000000000000000000ff0000000000fa0000000000000000000000000000000000000000000000000000000000000000000000000000000000cc00c800c80000000000000000000000cc0000000000c80000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [515, 522, 573, 858, 865, 916, 921, 1202, 1210]) (ps := [(18, [536], [1210])]) (by decide +kernel)

theorem c19695_0 : P.sumLeaves 24 20167680 320 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 19695) (lo := 0) (len := 320) (W := 0) check rows elimOK (by decide) (by decide) cover19695 (by decide)
  decide +kernel

theorem contract19695_1 : P.leaf 30 315125 = 0 := by
  exact leaf_contract_zero (ss := [(18, 1, 536), (27, 1, 573), (29, 1, 865), (13, 1, 922), (14, 1, 965), (8, 1, 580), (21, 0, 1266), (20, 1, 1272)]) (q := 1658) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c19695_1 : P.sumLeaves 24 20168000 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 315125) rows (by decide) (by decide)).symm.trans contract19695_1

theorem c19695_2 : P.sumLeaves 24 20168064 640 = 8607402 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 19695) (lo := 384) (len := 640) (W := 8607402) check rows elimOK (by decide) (by decide) cover19695 (by decide)
  decide +kernel

theorem h19695 : P.leaf 34 19695 = 8607402 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(320, 0), (64, 0), (640, 8607402)]) (.cons c19695_0 (.cons c19695_1 (.cons c19695_2 (.nil)))) (by decide) (by decide))

theorem h7421 : P.leaf 34 7421 = 8607402 :=
  orient4 (v := 19695) (by decide) (by decide +kernel) h19695

theorem cover7422 : P.CoversSplit 24 10 7422 0xf0f00000f0f500000000000000000000f0f00000f0f5000000000000000000000000000000000000000000000000000000000000000000000000000000000000c0000000c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 573, 858, 865, 916, 1210, 1217, 1259, 1264, 1308]) (by decide +kernel)

theorem c7422_0 : P.sumLeaves 24 7600128 1024 = 15938906 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7422) (lo := 0) (len := 1024) (W := 15938906) check rows elimOK (by decide) (by decide) cover7422 (by decide)
  decide +kernel

theorem h7422 : P.leaf 34 7422 = 15938906 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 15938906)]) (.cons c7422_0 (.nil)) (by decide) (by decide))

theorem cover19711 : P.CoversSplit 24 10 19711 0xff00fa00fa000000ff00fa00fa000000ff00fa00fa000000ff00fa00fa0000000000000000000000000000000000000000000000000000000000000000000000cc00c800c80000000000000000000000cc00c800c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [573, 858, 865, 916, 921, 1202, 1210, 1259]) (ps := [(8, [1217], [1266])]) (by decide +kernel)

theorem c19711_0 : P.sumLeaves 24 20184064 320 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 19711) (lo := 0) (len := 320) (W := 0) check rows elimOK (by decide) (by decide) cover19711 (by decide)
  decide +kernel

theorem contract19711_1 : P.leaf 30 315381 = 0 := by
  exact leaf_contract_zero (ss := [(27, 1, 573), (18, 1, 867), (29, 1, 916), (13, 1, 922), (14, 1, 965), (8, 1, 580)]) (q := 1266) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c19711_1 : P.sumLeaves 24 20184384 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 315381) rows (by decide) (by decide)).symm.trans contract19711_1

theorem c19711_2 : P.sumLeaves 24 20184448 640 = 37687143 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 19711) (lo := 384) (len := 640) (W := 37687143) check rows elimOK (by decide) (by decide) cover19711 (by decide)
  decide +kernel

theorem h19711 : P.leaf 34 19711 = 37687143 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(320, 0), (64, 0), (640, 37687143)]) (.cons c19711_0 (.cons c19711_1 (.cons c19711_2 (.nil)))) (by decide) (by decide))

theorem h7423 : P.leaf 34 7423 = 37687143 :=
  orient4 (v := 19711) (by decide) (by decide +kernel) h19711

theorem cover7524 : P.CoversSplit 24 10 7524 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem h7524 : P.leaf 34 7524 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 7524) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 7524) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover7524 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover7525 : P.CoversSplit 24 10 7525 0x8000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000002000000001000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 466, 473, 515, 522, 572, 858, 865, 1209, 1210, 1217, 1258, 1266]) (by decide +kernel)

theorem h7525 : P.leaf 34 7525 = 289650 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 7525) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 7525) (weight := fun _ => 1) (xs := [144, 181, 511, 895, 1023]) check rows elimOK (by decide) (by decide) cover7525 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover7526 : P.CoversSplit 24 10 7526 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 465, 466, 515, 522, 523, 565, 858, 865, 1209, 1217, 1258, 1266, 1609]) (by decide +kernel)

theorem h7526 : P.leaf 34 7526 = 1642208 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 7526) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 7526) (weight := fun _ => 1) (xs := [511, 592, 720, 895, 1023]) check rows elimOK (by decide) (by decide) cover7526 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover7527 : P.CoversSplit 24 10 7527 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 515, 522, 523, 572, 858, 865, 1209, 1217, 1258, 1266, 1609]) (by decide +kernel)

theorem h7527 : P.leaf 34 7527 = 2586416 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 7527) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 7527) (weight := fun _ => 1) (xs := [511, 592, 720, 895, 1023]) check rows elimOK (by decide) (by decide) cover7527 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover7528 : P.CoversSplit 24 10 7528 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem h7528 : P.leaf 34 7528 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 7528) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 7528) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover7528 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover7529 : P.CoversSplit 24 10 7529 0x8000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000002000000001000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 466, 473, 515, 522, 572, 858, 865, 1209, 1210, 1217, 1258, 1266]) (by decide +kernel)

theorem h7529 : P.leaf 34 7529 = 125174 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 7529) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 7529) (weight := fun _ => 1) (xs := [144, 181, 511, 895, 1023]) check rows elimOK (by decide) (by decide) cover7529 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover7530 : P.CoversSplit 24 10 7530 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 465, 466, 515, 522, 523, 565, 858, 865, 1209, 1217, 1258, 1266, 1609]) (by decide +kernel)

theorem h7530 : P.leaf 34 7530 = 401071 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 7530) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 7530) (weight := fun _ => 1) (xs := [511, 592, 720, 895, 1023]) check rows elimOK (by decide) (by decide) cover7530 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover7531 : P.CoversSplit 24 10 7531 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 515, 522, 523, 572, 858, 865, 1209, 1217, 1258, 1266, 1609]) (by decide +kernel)

theorem h7531 : P.leaf 34 7531 = 749619 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 7531) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 7531) (weight := fun _ => 1) (xs := [511, 592, 720, 895, 1023]) check rows elimOK (by decide) (by decide) cover7531 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover7532 : P.CoversSplit 24 10 7532 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem h7532 : P.leaf 34 7532 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 7532) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 7532) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover7532 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover7533 : P.CoversSplit 24 10 7533 0x8000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000002000000001000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 466, 473, 515, 522, 572, 858, 865, 1209, 1210, 1217, 1258, 1266]) (by decide +kernel)

theorem h7533 : P.leaf 34 7533 = 947610 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 7533) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 7533) (weight := fun _ => 1) (xs := [144, 181, 511, 895, 1023]) check rows elimOK (by decide) (by decide) cover7533 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover7534 : P.CoversSplit 24 10 7534 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 465, 466, 515, 522, 523, 565, 858, 865, 1209, 1217, 1258, 1266, 1609]) (by decide +kernel)

theorem h7534 : P.leaf 34 7534 = 2076219 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 7534) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 7534) (weight := fun _ => 1) (xs := [511, 592, 720, 895, 1023]) check rows elimOK (by decide) (by decide) cover7534 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover7535 : P.CoversSplit 24 10 7535 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 515, 522, 523, 572, 858, 865, 1209, 1217, 1258, 1266, 1609]) (by decide +kernel)

theorem h7535 : P.leaf 34 7535 = 2786828 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 7535) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 7535) (weight := fun _ => 1) (xs := [511, 592, 720, 895, 1023]) check rows elimOK (by decide) (by decide) cover7535 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover19758 : P.CoversSplit 24 10 19758 0x8800000088000000000000000000000088000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000088000000880000000000000000000000880000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 515, 517, 522, 529, 572, 858, 865, 915, 916, 921, 1202]) (by decide +kernel)

theorem h19758 : P.leaf 34 19758 = 887552 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 19758) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 19758) (weight := fun _ => 1) (xs := [379, 383, 475, 479, 507, 511, 891, 895, 987, 991, 1019, 1023]) check rows elimOK (by decide) (by decide) cover19758 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h7540 : P.leaf 34 7540 = 887552 :=
  orient4 (v := 19758) (by decide) (by decide +kernel) h19758

theorem cover19759 : P.CoversSplit 24 10 19759 0x8800000088000000000000000000000088000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000088000000880000000000000000000000880000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 517, 522, 529, 572, 858, 865, 915, 916, 1202, 1210]) (by decide +kernel)

theorem h19759 : P.leaf 34 19759 = 6595138 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 19759) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 19759) (weight := fun _ => 1) (xs := [379, 383, 475, 479, 507, 511, 891, 895, 987, 991, 1019, 1023]) check rows elimOK (by decide) (by decide) cover19759 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h7541 : P.leaf 34 7541 = 6595138 :=
  orient4 (v := 19759) (by decide) (by decide +kernel) h19759

theorem cover7542 : P.CoversSplit 24 10 7542 0xf0f00000f0f500000000000000000000f0f00000f0f5000000000000000000000000000000000000000000000000000000000000000000000000000000000000f0f00000f0f500000000000000000000f0f00000f0f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 572, 858, 865, 866, 908, 1210, 1217, 1258, 1259, 1264]) (by decide +kernel)

theorem c7542_0 : P.sumLeaves 24 7723008 1024 = 22410038 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7542) (lo := 0) (len := 1024) (W := 22410038) check rows elimOK (by decide) (by decide) cover7542 (by decide)
  decide +kernel

theorem h7542 : P.leaf 34 7542 = 22410038 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 22410038)]) (.cons c7542_0 (.nil)) (by decide) (by decide))

theorem cover19775 : P.CoversSplit 24 10 19775 0xff00fa00fa00a000ff00fa00fa00a000ff00fa00fa00a000ff000000000000000000000000000000000000000000000000000000000000000000000000000000ff00fa00fa00a000ff000000fa000000ff00fa0000000000ff000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [517, 529, 572, 858, 865, 915, 921, 1202, 1210, 1251, 1264, 1308]) (by decide +kernel)

theorem c19775_0 : P.sumLeaves 24 20249600 937 = 35201078 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 19775) (lo := 0) (len := 937) (W := 35201078) check rows elimOK (by decide) (by decide) cover19775 (by decide)
  decide +kernel

theorem c19775_1 : P.sumLeaves 24 20250537 87 = 41313418 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 19775) (lo := 937) (len := 87) (W := 41313418) check rows elimOK (by decide) (by decide) cover19775 (by decide)
  decide +kernel

theorem h19775 : P.leaf 34 19775 = 76514496 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(937, 35201078), (87, 41313418)]) (.cons c19775_0 (.cons c19775_1 (.nil))) (by decide) (by decide))

theorem h7543 : P.leaf 34 7543 = 76514496 :=
  orient4 (v := 19775) (by decide) (by decide +kernel) h19775

theorem cover20300 : P.CoversSplit 24 10 20300 0x8800880080008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000088008800800080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 472, 473, 516, 522, 565, 572, 915, 916, 921, 1202]) (by decide +kernel)

theorem h20300 : P.leaf 34 20300 = 470220 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 20300) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 20300) (weight := fun _ => 1) (xs := [463, 479, 491, 495, 507, 511, 975, 991, 1003, 1007, 1019, 1023]) check rows elimOK (by decide) (by decide) cover20300 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h7544 : P.leaf 34 7544 = 470220 :=
  orient5 (v := 20300) (by decide) (by decide +kernel) h20300

theorem cover20301 : P.CoversSplit 24 10 20301 0xcc00cc00c0008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000088008800800080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 515, 516, 522, 523, 565, 572, 915, 916, 1202]) (by decide +kernel)

theorem h20301 : P.leaf 34 20301 = 1682058 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 20301) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 20301) (weight := fun _ => 1) (xs := [463, 479, 491, 495, 507, 511, 975, 990, 991, 1002, 1003, 1006, 1007, 1018, 1019, 1022, 1023]) check rows elimOK (by decide) (by decide) cover20301 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h7545 : P.leaf 34 7545 = 1682058 :=
  orient5 (v := 20301) (by decide) (by decide +kernel) h20301

theorem cover7546 : P.CoversSplit 24 10 7546 0xf0f00000f0f500000000000000000000f0f00000f0f5000000000000000000000000000000000000000000000000000000000000000000000000000000000000f0f00000f0f500000000000000000000f0f00000f0f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 572, 858, 865, 867, 909, 1210, 1217, 1258, 1259, 1264]) (by decide +kernel)

theorem c7546_0 : P.sumLeaves 24 7727104 1024 = 6823068 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7546) (lo := 0) (len := 1024) (W := 6823068) check rows elimOK (by decide) (by decide) cover7546 (by decide)
  decide +kernel

theorem h7546 : P.leaf 34 7546 = 6823068 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 6823068)]) (.cons c7546_0 (.nil)) (by decide) (by decide))

theorem cover19807 : P.CoversSplit 24 10 19807 0xff00fa00f000a000ff00fa00f000a000ff00000000005000ff000000000050000000000000000000000000000000000000000000000000000000000000000000ff00fa00f000a000ff000000f0000000ff00500000000000ff000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [516, 572, 858, 915, 921, 1202, 1210, 1264, 1308]) (by decide +kernel)

theorem c19807_0 : P.sumLeaves 24 20282368 256 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 19807) (lo := 0) (len := 256) (W := 0) check rows elimOK (by decide) (by decide) cover19807 (by decide)
  decide +kernel

theorem contract19807_1 : P.leaf 30 316916 = 0 := by
  exact leaf_contract_zero (ss := [(11, 1, 879), (29, 1, 921), (30, 1, 1264), (31, 1, 1210), (8, 0, 1266), (5, 1, 565), (14, 0, 586), (20, 1, 531), (21, 1, 537)]) (q := 586) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c19807_1 : P.sumLeaves 24 20282624 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 316916) rows (by decide) (by decide)).symm.trans contract19807_1

theorem contract19807_2 : P.leaf 30 316917 = 0 := by
  exact leaf_contract_zero (ss := [(11, 1, 879), (29, 1, 915), (8, 0, 1266), (5, 1, 565), (14, 0, 586), (20, 1, 531), (21, 1, 537)]) (q := 586) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c19807_2 : P.sumLeaves 24 20282688 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 316917) rows (by decide) (by decide)).symm.trans contract19807_2

theorem c19807_3 : P.sumLeaves 24 20282752 640 = 21535341 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 19807) (lo := 384) (len := 640) (W := 21535341) check rows elimOK (by decide) (by decide) cover19807 (by decide)
  decide +kernel

theorem h19807 : P.leaf 34 19807 = 21535341 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(256, 0), (64, 0), (64, 0), (640, 21535341)]) (.cons c19807_0 (.cons c19807_1 (.cons c19807_2 (.cons c19807_3 (.nil))))) (by decide) (by decide))

theorem h7547 : P.leaf 34 7547 = 21535341 :=
  orient4 (v := 19807) (by decide) (by decide +kernel) h19807

theorem cover7548 : P.CoversSplit 24 10 7548 0xc0000000c00080000000000000000000c0000000c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c0000000c00080000000000000000000c0000000c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 572, 858, 865, 916, 1209, 1210, 1258, 1259]) (ps := [(11, [879, 909], [858])]) (by decide +kernel)

theorem h7548 : P.leaf 34 7548 = 3032032 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 7548) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 7548) (weight := fun _ => 1) (xs := [350, 351, 382, 383, 463, 478, 479, 510, 511, 862, 863, 894, 895, 975, 990, 991, 1022, 1023]) check rows elimOK (by decide) (by decide) cover7548 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover19823 : P.CoversSplit 24 10 19823 0xcc00c800c80088000000000000000000cc0000000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000cc00c800c80088000000000000000000cc0040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 522, 572, 858, 865, 915, 916, 1202, 1210, 1308]) (by decide +kernel)

theorem c19823_0 : P.sumLeaves 24 20298752 1024 = 15770124 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 19823) (lo := 0) (len := 1024) (W := 15770124) check rows elimOK (by decide) (by decide) cover19823 (by decide)
  decide +kernel

theorem h19823 : P.leaf 34 19823 = 15770124 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 15770124)]) (.cons c19823_0 (.nil)) (by decide) (by decide))

theorem h7549 : P.leaf 34 7549 = 15770124 :=
  orient4 (v := 19823) (by decide) (by decide +kernel) h19823

theorem cover7550 : P.CoversSplit 24 10 7550 0xf0f00000f0f500000000000000000000f0f00000f0f5000000000000000000000000000000000000000000000000000000000000000000000000000000000000f0f00000f0f500000000000000000000f0f00000f0f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 572, 858, 865, 1210, 1217, 1258, 1259, 1264]) (by decide +kernel)

theorem c7550_0 : P.sumLeaves 24 7731200 1024 = 35434226 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7550) (lo := 0) (len := 1024) (W := 35434226) check rows elimOK (by decide) (by decide) cover7550 (by decide)
  decide +kernel

theorem h7550 : P.leaf 34 7550 = 35434226 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 35434226)]) (.cons c7550_0 (.nil)) (by decide) (by decide))

theorem cover19839 : P.CoversSplit 24 10 19839 0xff00fa00fa00aa00ff00fa00fa00aa00ff00fa00fa00aa00ff00fa00fa00aa000000000000000000000000000000000000000000000000000000000000000000ff00fa00fa00aa00ff000000fa000000ff00fa0000000000ff000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [572, 858, 865, 915, 921, 1202, 1210, 1264, 1308]) (by decide +kernel)

theorem c19839_0 : P.sumLeaves 24 20315136 876 = 34195158 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 19839) (lo := 0) (len := 876) (W := 34195158) check rows elimOK (by decide) (by decide) cover19839 (by decide)
  decide +kernel

theorem c19839_1 : P.sumLeaves 24 20316012 148 = 75929408 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 19839) (lo := 876) (len := 148) (W := 75929408) check rows elimOK (by decide) (by decide) cover19839 (by decide)
  decide +kernel

theorem h19839 : P.leaf 34 19839 = 110124566 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(876, 34195158), (148, 75929408)]) (.cons c19839_0 (.cons c19839_1 (.nil))) (by decide) (by decide))

theorem h7551 : P.leaf 34 7551 = 110124566 :=
  orient4 (v := 19839) (by decide) (by decide +kernel) h19839

theorem cover7584 : P.CoversSplit 24 10 7584 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem h7584 : P.leaf 34 7584 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 7584) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 7584) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover7584 (by decide) (by decide) (by decide +kernel)
  decide +kernel

def seg : List (ℕ × ℕ) := [(7417, 48), (7418, 48), (7419, 48), (7420, 48), (7421, 48), (7422, 48), (7423, 48), (7524, 24), (7525, 24), (7526, 24), (7527, 24), (7528, 24), (7529, 24), (7530, 24), (7531, 24), (7532, 24), (7533, 24), (7534, 24), (7535, 24), (7540, 48), (7541, 48), (7542, 48), (7543, 48), (7544, 48), (7545, 48), (7546, 48), (7547, 48), (7548, 48), (7549, 48), (7550, 48), (7551, 48), (7584, 12)]

theorem segOK : checkSeg 16 perms 7417 7585 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 7417 7585 1212 19025115048 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 19025115048)
    (SegSum.cons (w := 48) h7417 (SegSum.cons (w := 48) h7418 (SegSum.cons (w := 48) h7419 (SegSum.cons (w := 48) h7420 (SegSum.cons (w := 48) h7421 (SegSum.cons (w := 48) h7422 (SegSum.cons (w := 48) h7423 (SegSum.cons (w := 24) h7524 (SegSum.cons (w := 24) h7525 (SegSum.cons (w := 24) h7526 (SegSum.cons (w := 24) h7527 (SegSum.cons (w := 24) h7528 (SegSum.cons (w := 24) h7529 (SegSum.cons (w := 24) h7530 (SegSum.cons (w := 24) h7531 (SegSum.cons (w := 24) h7532 (SegSum.cons (w := 24) h7533 (SegSum.cons (w := 24) h7534 (SegSum.cons (w := 24) h7535 (SegSum.cons (w := 48) h7540 (SegSum.cons (w := 48) h7541 (SegSum.cons (w := 48) h7542 (SegSum.cons (w := 48) h7543 (SegSum.cons (w := 48) h7544 (SegSum.cons (w := 48) h7545 (SegSum.cons (w := 48) h7546 (SegSum.cons (w := 48) h7547 (SegSum.cons (w := 48) h7548 (SegSum.cons (w := 48) h7549 (SegSum.cons (w := 48) h7550 (SegSum.cons (w := 48) h7551 (SegSum.cons (w := 12) h7584 (show SegSum (P.leaf 34) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S4N1.C0.S43
