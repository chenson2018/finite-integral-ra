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

namespace RACert.S6N0.C0.S47

open RACert RACert.Problem

theorem cover298467 : P.CoversSplit 26 10 298467 0x8000800080008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 488, 489, 636, 922, 929, 1658, 1665]) (by decide +kernel)

theorem h298467 : P.leaf 36 298467 = 538752 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 298467) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 298467) (weight := fun _ => 1) (xs := [975, 991, 1007, 1023]) check rows elimOK (by decide) (by decide) cover298467 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h79673 : P.leaf 36 79673 = 538752 :=
  orient6 (v := 298467) (by decide) (by decide +kernel) h298467

theorem cover79674 : P.CoversSplit 26 10 79674 0xa0a0a0a000000000000000000000000000000000000000000000000000000000000000000000000000005050000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 579, 873, 874, 972, 1273, 1658]) (by decide +kernel)

theorem h79674 : P.leaf 36 79674 = 1174048 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 79674) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 79674) (weight := fun _ => 1) (xs := [676, 678, 684, 686, 997, 999, 1005, 1007, 1013, 1015, 1021, 1023]) check rows elimOK (by decide) (by decide) cover79674 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover79675 : P.CoversSplit 26 10 79675 0xa0a0a0a000000000000000000000000000000000000000000000000000000000000000000000000000005050000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 579, 972, 979, 1273, 1322, 1658]) (by decide +kernel)

theorem h79675 : P.leaf 36 79675 = 4008272 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 79675) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 79675) (weight := fun _ => 1) (xs := [676, 678, 684, 686, 997, 999, 1005, 1007, 1013, 1015, 1021, 1023]) check rows elimOK (by decide) (by decide) cover79675 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover101866 : P.CoversSplit 26 10 101866 0xaaaaaaaa00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 531, 629, 636, 881, 922, 930, 965, 1322, 1658]) (by decide +kernel)

theorem h101866 : P.leaf 36 101866 = 2403192 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 101866) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 101866) (weight := fun _ => 1) (xs := [993, 995, 997, 999, 1001, 1003, 1005, 1007, 1009, 1011, 1013, 1015, 1017, 1019, 1021, 1023]) check rows elimOK (by decide) (by decide) cover101866 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h79676 : P.leaf 36 79676 = 2403192 :=
  orient72 (v := 101866) (by decide) (by decide +kernel) h101866

theorem cover80699 : P.CoversSplit 26 10 80699 0xf0f0f0f500000000000000000000000000000000000000000000000000000000000000000000000000005050000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [481, 538, 930, 972, 979, 1273, 1315, 1322, 1658]) (ps := [(21, [929], [1658])]) (by decide +kernel)

theorem h80699 : P.leaf 36 80699 = 6476448 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 80699) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 80699) (weight := fun _ => 1) (xs := [676, 678, 684, 686, 992, 994, 996, 997, 998, 999, 1004, 1005, 1006, 1007, 1012, 1013, 1014, 1015, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover80699 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h79677 : P.leaf 36 79677 = 6476448 :=
  orient4 (v := 80699) (by decide) (by decide +kernel) h80699

theorem cover101867 : P.CoversSplit 26 10 101867 0xaaaaaaaa00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 629, 636, 922, 930, 965, 1322, 1658]) (by decide +kernel)

theorem h101867 : P.leaf 36 101867 = 8615360 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 101867) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 101867) (weight := fun _ => 1) (xs := [993, 995, 997, 999, 1001, 1003, 1005, 1007, 1009, 1011, 1013, 1015, 1017, 1019, 1021, 1023]) check rows elimOK (by decide) (by decide) cover101867 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h79678 : P.leaf 36 79678 = 8615360 :=
  orient72 (v := 101867) (by decide) (by decide +kernel) h101867

theorem cover101871 : P.CoversSplit 26 10 101871 0xffffffff00000000000000000000000000000000000000000000000000000000555500000000000055550000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [629, 636, 922, 930, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c101871_0 : P.sumLeaves 26 104315904 1024 = 24553540 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 101871) (lo := 0) (len := 1024) (W := 24553540) check rows elimOK (by decide) (by decide) cover101871 (by decide)
  decide +kernel

theorem h101871 : P.leaf 36 101871 = 24553540 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 24553540)]) (.cons c101871_0 (.nil)) (by decide) (by decide))

theorem h79679 : P.leaf 36 79679 = 24553540 :=
  orient72 (v := 101871) (by decide) (by decide +kernel) h101871

theorem cover298387 : P.CoversSplit 26 10 298387 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 482, 488, 489, 530, 538, 629, 636, 922, 929]) (by decide +kernel)

theorem h298387 : P.leaf 36 298387 = 109568 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 298387) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 298387) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover298387 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h79689 : P.leaf 36 79689 = 109568 :=
  orient6 (v := 298387) (by decide) (by decide +kernel) h298387

theorem cover298391 : P.CoversSplit 26 10 298391 0x8800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 531, 537, 538, 636, 923, 930, 1265, 1658]) (by decide +kernel)

theorem h298391 : P.leaf 36 298391 = 532608 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 298391) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 298391) (weight := fun _ => 1) (xs := [1019, 1023]) check rows elimOK (by decide) (by decide) cover298391 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h79691 : P.leaf 36 79691 = 532608 :=
  orient6 (v := 298391) (by decide) (by decide +kernel) h298391

theorem cover298394 : P.CoversSplit 26 10 298394 0x8080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [468, 481, 530, 538, 615, 629, 636, 922, 929, 1665]) (by decide +kernel)

theorem h298394 : P.leaf 36 298394 = 214416 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 298394) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 298394) (weight := fun _ => 1) (xs := [1015, 1023]) check rows elimOK (by decide) (by decide) cover298394 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h79692 : P.leaf 36 79692 = 214416 :=
  orient6 (v := 298394) (by decide) (by decide +kernel) h298394

theorem cover298395 : P.CoversSplit 26 10 298395 0x8080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 537, 538, 629, 636, 922, 929, 1665]) (by decide +kernel)

theorem h298395 : P.leaf 36 298395 = 943008 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 298395) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 298395) (weight := fun _ => 1) (xs := [1015, 1023]) check rows elimOK (by decide) (by decide) cover298395 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h79693 : P.leaf 36 79693 = 943008 :=
  orient6 (v := 298395) (by decide) (by decide +kernel) h298395

theorem cover298398 : P.CoversSplit 26 10 298398 0x8888000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 538, 615, 636, 881, 930, 1265, 1272, 1658, 1665]) (by decide +kernel)

theorem h298398 : P.leaf 36 298398 = 575624 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 298398) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 298398) (weight := fun _ => 1) (xs := [1011, 1015, 1019, 1023]) check rows elimOK (by decide) (by decide) cover298398 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h79694 : P.leaf 36 79694 = 575624 :=
  orient6 (v := 298398) (by decide) (by decide +kernel) h298398

theorem cover298399 : P.CoversSplit 26 10 298399 0x8888000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 537, 538, 636, 930, 1265, 1272, 1658, 1665]) (by decide +kernel)

theorem h298399 : P.leaf 36 298399 = 2753120 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 298399) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 298399) (weight := fun _ => 1) (xs := [1011, 1015, 1019, 1023]) check rows elimOK (by decide) (by decide) cover298399 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h79695 : P.leaf 36 79695 = 2753120 :=
  orient6 (v := 298399) (by decide) (by decide +kernel) h298399

theorem cover276919 : P.CoversSplit 26 10 276919 0xcc00cc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 538, 629, 636, 929, 930, 972, 979, 1265, 1658]) (by decide +kernel)

theorem h276919 : P.leaf 36 276919 = 4098208 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 276919) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 276919) (weight := fun _ => 1) (xs := [1002, 1003, 1006, 1007, 1018, 1019, 1022, 1023]) check rows elimOK (by decide) (by decide) cover276919 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h79707 : P.leaf 36 79707 = 4098208 :=
  orient74 (v := 276919) (by decide) (by decide +kernel) h276919

theorem cover298426 : P.CoversSplit 26 10 298426 0xc0c0c4c400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [468, 481, 538, 629, 922, 929, 1265, 1266, 1658, 1665]) (ps := [(21, [867], [1658])]) (by decide +kernel)

theorem h298426 : P.leaf 36 298426 = 4259076 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 298426) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 298426) (weight := fun _ => 1) (xs := [994, 998, 999, 1002, 1006, 1007, 1014, 1015, 1022, 1023]) check rows elimOK (by decide) (by decide) cover298426 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h79708 : P.leaf 36 79708 = 4259076 :=
  orient6 (v := 298426) (by decide) (by decide +kernel) h298426

theorem cover276926 : P.CoversSplit 26 10 276926 0xccccccc800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [482, 538, 629, 636, 867, 923, 972, 1265, 1273, 1658]) (by decide +kernel)

theorem h276926 : P.leaf 36 276926 = 10082304 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 276926) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 276926) (weight := fun _ => 1) (xs := [995, 998, 999, 1002, 1003, 1006, 1007, 1010, 1011, 1014, 1015, 1018, 1019, 1022, 1023]) check rows elimOK (by decide) (by decide) cover276926 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h79709 : P.leaf 36 79709 = 10082304 :=
  orient74 (v := 276926) (by decide) (by decide +kernel) h276926

theorem cover276923 : P.CoversSplit 26 10 276923 0xccccccc800000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 629, 636, 923, 972, 979, 1265, 1273, 1658, 1665]) (by decide +kernel)

theorem h276923 : P.leaf 36 276923 = 9591805 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 276923) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 276923) (weight := fun _ => 1) (xs := [788, 995, 998, 999, 1002, 1003, 1006, 1007, 1010, 1011, 1014, 1015, 1018, 1019, 1022, 1023]) check rows elimOK (by decide) (by decide) cover276923 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h79710 : P.leaf 36 79710 = 9591805 :=
  orient74 (v := 276923) (by decide) (by decide +kernel) h276923

theorem cover276927 : P.CoversSplit 26 10 276927 0xccccccc800000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [538, 629, 636, 923, 972, 979, 1265, 1273, 1658, 1665]) (by decide +kernel)

theorem h276927 : P.leaf 36 276927 = 25977142 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 276927) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 276927) (weight := fun _ => 1) (xs := [788, 995, 998, 999, 1002, 1003, 1006, 1007, 1010, 1011, 1014, 1015, 1018, 1019, 1022, 1023]) check rows elimOK (by decide) (by decide) cover276927 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h79711 : P.leaf 36 79711 = 25977142 :=
  orient74 (v := 276927) (by decide) (by decide +kernel) h276927

theorem cover298458 : P.CoversSplit 26 10 298458 0xa0a00000a0a00000000000000000000000000000000000000000000000000000000000000000000000000505000005050000000000000000000000000000000020200000202000000000000000000000000000000000000000000000000000000000000000000000000001010000010100000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 629, 636, 881, 922, 929, 1665]) (by decide +kernel)

theorem h298458 : P.leaf 36 298458 = 6345677 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 298458) (keep := keep3) (twice := twice3) rows (by decide) (by decide) bal3 (invRow3 (H := 298458) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 298458) (weight := rowWeight keep3 twice3) (xs := [128, 136, 160, 168, 469, 477, 501, 509, 640, 642, 648, 650, 672, 674, 680, 682, 981, 983, 989, 991, 1013, 1015, 1021, 1023]) check rows elimOK (by decide) (by decide) cover298458 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h79724 : P.leaf 36 79724 = 6345677 :=
  orient6 (v := 298458) (by decide) (by decide +kernel) h298458

theorem cover298459 : P.CoversSplit 26 10 298459 0xa0a00000a0a00000000000000000000000000000000000000000000000000000000000000000000000000505000005050000000000000000000000000000000020200000202000000000000000000000000000000000000000000000000000000000000000000000000001010000010100000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 629, 636, 922, 929, 1665]) (by decide +kernel)

theorem h298459 : P.leaf 36 298459 = 16437708 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 298459) (keep := keep3) (twice := twice3) rows (by decide) (by decide) bal3 (invRow3 (H := 298459) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 298459) (weight := rowWeight keep3 twice3) (xs := [128, 136, 160, 168, 469, 477, 501, 509, 640, 642, 648, 650, 672, 674, 680, 682, 981, 983, 989, 991, 1013, 1015, 1021, 1023]) check rows elimOK (by decide) (by decide) cover298459 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h79725 : P.leaf 36 79725 = 16437708 :=
  orient6 (v := 298459) (by decide) (by decide +kernel) h298459

theorem cover298462 : P.CoversSplit 26 10 298462 0xffff0505ffff0504000000000000000000000000000000000000000000000000000000000000000005050000050500000000000000000000000000000000000033330101333301000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [530, 629, 636, 881, 922, 930, 1265, 1272, 1658, 1665]) (ps := [(19, [1273], [1265]), (20, [866], [1665]), (21, [867], [1658])]) (by decide +kernel)

theorem c298462_0 : P.sumLeaves 26 305625088 1024 = 31995870 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 298462) (lo := 0) (len := 1024) (W := 31995870) check rows elimOK (by decide) (by decide) cover298462 (by decide)
  decide +kernel

theorem h298462 : P.leaf 36 298462 = 31995870 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 31995870)]) (.cons c298462_0 (.nil)) (by decide) (by decide))

theorem h79726 : P.leaf 36 79726 = 31995870 :=
  orient6 (v := 298462) (by decide) (by decide +kernel) h298462

theorem cover298463 : P.CoversSplit 26 10 298463 0xffff0505ffff0504000000000000000000000000000000000000000000000000555505055555050405050000050500000000000000000000000000000000000033330101333301000000000000000000000000000000000000000000000000001111010111110100010100000101000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [530, 629, 636, 922, 930, 1265, 1272, 1658, 1665]) (ps := [(19, [1273], [1265])]) (by decide +kernel)

theorem c298463_0 : P.sumLeaves 26 305626112 1016 = 59929714 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 298463) (lo := 0) (len := 1016) (W := 59929714) check rows elimOK (by decide) (by decide) cover298463 (by decide)
  decide +kernel

theorem c298463_1 : P.sumLeaves 26 305627128 8 = 30695600 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 298463) (lo := 1016) (len := 8) (W := 30695600) check rows elimOK (by decide) (by decide) cover298463 (by decide)
  decide +kernel

theorem h298463 : P.leaf 36 298463 = 90625314 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1016, 59929714), (8, 30695600)]) (.cons c298463_0 (.cons c298463_1 (.nil))) (by decide) (by decide))

theorem h79727 : P.leaf 36 79727 = 90625314 :=
  orient6 (v := 298463) (by decide) (by decide +kernel) h298463

theorem cover80766 : P.CoversSplit 26 10 80766 0xfffffffafffffafa0000000000000000000000000000000000000000000000005555505055555050555550505555505000000000000000000000000000000000fffffffafffffafa0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [579, 867, 874, 972, 1315, 1658]) (by decide +kernel)

noncomputable def f80766 (i : ℕ) := rowWeight keep3 twice3 i * P.leaf 26 (82704384 + i)

theorem c80766_0 : rowSum f80766 0 1020 = 109296533 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 80766) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover80766 (by decide)
  decide +kernel

theorem c80766_1 : rowSum f80766 1020 4 = 13275504 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 80766) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover80766 (by decide)
  decide +kernel

theorem sum80766 : rowSum f80766 0 1024 = 122572037 :=
  rowSum_append (F := f80766) (lo := 0) (n := 1020) (m := 4) (A := 109296533) (B := 13275504) c80766_0 (c80766_1)

theorem h80766 : P.leaf 36 80766 = 122572037 :=
  leaf_weighted (k := 26) (d := 10) (H := 80766) (keep := keep3) (twice := twice3) rows (by decide) (by decide) (bal3) (invRow3 (H := 80766) (by decide) (by decide +kernel)) sum80766

theorem h79742 : P.leaf 36 79742 = 122572037 :=
  orient4 (v := 80766) (by decide) (by decide +kernel) h80766

theorem cover298495 : P.CoversSplit 26 10 298495 0xffffffffffffffff000000000000000000000000000000001111101011001000555555555555555555555050555550500000000000000000111110101100100033333333333333330000000000000000333333333300330011111010110010001111111111111111111110101111101011111111110011001111101011001000 :=
  coversSplit check rows (by decide) (by decide) (xs := [629, 636, 922, 930, 1658, 1665]) (by decide +kernel)

noncomputable def f298495 (i : ℕ) := rowWeight keep3 twice3 i * P.leaf 26 (305658880 + i)

theorem c298495_0 : rowSum f298495 0 726 = 65860928 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 298495) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover298495 (by decide)
  decide +kernel

theorem c298495_1 : rowSum f298495 726 298 = 263888576 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 298495) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover298495 (by decide)
  decide +kernel

theorem sum298495 : rowSum f298495 0 1024 = 329749504 :=
  rowSum_append (F := f298495) (lo := 0) (n := 726) (m := 298) (A := 65860928) (B := 263888576) c298495_0 (c298495_1)

theorem h298495 : P.leaf 36 298495 = 329749504 :=
  leaf_weighted (k := 26) (d := 10) (H := 298495) (keep := keep3) (twice := twice3) rows (by decide) (by decide) (bal3) (invRow3 (H := 298495) (by decide) (by decide +kernel)) sum298495

theorem h79743 : P.leaf 36 79743 = 329749504 :=
  orient6 (v := 298495) (by decide) (by decide +kernel) h298495

theorem cover79753 : P.CoversSplit 26 10 79753 0xf0f0000000000000f0f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 538, 566, 923, 972, 979, 1273, 1315, 1322]) (by decide +kernel)

theorem h79753 : P.leaf 36 79753 = 262144 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 79753) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 79753) (weight := fun _ => 1) (xs := [948, 949, 950, 951, 956, 957, 958, 959, 1012, 1013, 1014, 1015, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover79753 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover79755 : P.CoversSplit 26 10 79755 0xf0f0000000000000f0f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 538, 615, 972, 979, 1266, 1273, 1315, 1322]) (by decide +kernel)

theorem h79755 : P.leaf 36 79755 = 1404928 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 79755) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 79755) (weight := fun _ => 1) (xs := [948, 949, 950, 951, 956, 957, 958, 959, 1012, 1013, 1014, 1015, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover79755 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover80779 : P.CoversSplit 26 10 80779 0xf0f0000000000000f0f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [481, 530, 538, 615, 930, 972, 1266, 1273, 1315, 1322, 1658]) (ps := [(16, [867], [1273])]) (by decide +kernel)

theorem h80779 : P.leaf 36 80779 = 1592448 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 80779) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 80779) (weight := fun _ => 1) (xs := [948, 949, 950, 951, 956, 957, 958, 959, 1012, 1013, 1014, 1015, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover80779 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h79757 : P.leaf 36 79757 = 1592448 :=
  orient4 (v := 80779) (by decide) (by decide +kernel) h80779

theorem cover101727 : P.CoversSplit 26 10 101727 0xaaaaaaaa00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000088008800000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 579, 636, 930, 965, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h101727 : P.leaf 36 101727 = 5241760 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 101727) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 101727) (weight := fun _ => 1) (xs := [323, 327, 339, 343, 993, 995, 997, 999, 1001, 1003, 1005, 1007, 1009, 1011, 1013, 1015, 1017, 1019, 1021, 1023]) check rows elimOK (by decide) (by decide) cover101727 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h79759 : P.leaf 36 79759 = 5241760 :=
  orient72 (v := 101727) (by decide) (by decide +kernel) h101727

theorem cover79765 : P.CoversSplit 26 10 79765 0xcc00000000000000cc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 538, 923, 930, 972, 979, 1315, 1658, 1665]) (by decide +kernel)

theorem h79765 : P.leaf 36 79765 = 778832 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 79765) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 79765) (weight := fun _ => 1) (xs := [954, 955, 958, 959, 1018, 1019, 1022, 1023]) check rows elimOK (by decide) (by decide) cover79765 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover101751 : P.CoversSplit 26 10 101751 0xcc00cc0000000000000000000000000000000000000000000000000000000000440000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 579, 629, 636, 881, 922, 930, 965, 1273, 1315, 1658]) (by decide +kernel)

theorem h101751 : P.leaf 36 101751 = 3419288 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 101751) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 101751) (weight := fun _ => 1) (xs := [762, 766, 1002, 1003, 1006, 1007, 1018, 1019, 1022, 1023]) check rows elimOK (by decide) (by decide) cover101751 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h79767 : P.leaf 36 79767 = 3419288 :=
  orient72 (v := 101751) (by decide) (by decide +kernel) h101751

theorem cover101754 : P.CoversSplit 26 10 101754 0xaaaaaaaa00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 531, 629, 636, 881, 922, 930, 965, 1322, 1658]) (by decide +kernel)

theorem h101754 : P.leaf 36 101754 = 2222272 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 101754) (keep := keep12) (twice := twice12) rows (by decide) (by decide) bal12 (invRow12 (H := 101754) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 101754) (weight := rowWeight keep12 twice12) (xs := [993, 995, 997, 999, 1001, 1003, 1005, 1007, 1009, 1011, 1013, 1015, 1017, 1019, 1021, 1023]) check rows elimOK (by decide) (by decide) cover101754 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h79772 : P.leaf 36 79772 = 2222272 :=
  orient72 (v := 101754) (by decide) (by decide +kernel) h101754

theorem cover79773 : P.CoversSplit 26 10 79773 0xffff000000000000ffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 538, 923, 930, 972, 979, 1273, 1315, 1322]) (by decide +kernel)

theorem h79773 : P.leaf 36 79773 = 8117756 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 79773) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 79773) (weight := fun _ => 1) (xs := [944, 945, 946, 947, 948, 949, 950, 951, 952, 953, 954, 955, 956, 957, 958, 959, 1008, 1009, 1010, 1011, 1012, 1013, 1014, 1015, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover79773 (by decide) (by decide) (by decide +kernel)
  decide +kernel

def seg : List (ℕ × ℕ) := [(79673, 720), (79674, 720), (79675, 720), (79676, 720), (79677, 720), (79678, 720), (79679, 720), (79689, 180), (79691, 720), (79692, 360), (79693, 720), (79694, 720), (79695, 720), (79707, 360), (79708, 720), (79709, 720), (79710, 720), (79711, 720), (79724, 360), (79725, 360), (79726, 720), (79727, 720), (79742, 360), (79743, 360), (79753, 240), (79755, 240), (79757, 720), (79759, 720), (79765, 720), (79767, 720), (79772, 360), (79773, 720)]

theorem segOK : checkSeg 20 perms 79673 79774 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 79673 79774 19020 349674163680 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 349674163680)
    (SegSum.cons (w := 720) h79673 (SegSum.cons (w := 720) h79674 (SegSum.cons (w := 720) h79675 (SegSum.cons (w := 720) h79676 (SegSum.cons (w := 720) h79677 (SegSum.cons (w := 720) h79678 (SegSum.cons (w := 720) h79679 (SegSum.cons (w := 180) h79689 (SegSum.cons (w := 720) h79691 (SegSum.cons (w := 360) h79692 (SegSum.cons (w := 720) h79693 (SegSum.cons (w := 720) h79694 (SegSum.cons (w := 720) h79695 (SegSum.cons (w := 360) h79707 (SegSum.cons (w := 720) h79708 (SegSum.cons (w := 720) h79709 (SegSum.cons (w := 720) h79710 (SegSum.cons (w := 720) h79711 (SegSum.cons (w := 360) h79724 (SegSum.cons (w := 360) h79725 (SegSum.cons (w := 720) h79726 (SegSum.cons (w := 720) h79727 (SegSum.cons (w := 360) h79742 (SegSum.cons (w := 360) h79743 (SegSum.cons (w := 240) h79753 (SegSum.cons (w := 240) h79755 (SegSum.cons (w := 720) h79757 (SegSum.cons (w := 720) h79759 (SegSum.cons (w := 720) h79765 (SegSum.cons (w := 720) h79767 (SegSum.cons (w := 360) h79772 (SegSum.cons (w := 720) h79773 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S47
