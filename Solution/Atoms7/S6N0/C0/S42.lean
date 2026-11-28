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

namespace RACert.S6N0.C0.S42

open RACert RACert.Problem

theorem cover530558 : P.CoversSplit 26 10 530558 0x8000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [579, 587, 622, 629, 636, 874, 922, 930, 1265, 1273]) (by decide +kernel)

theorem h530558 : P.leaf 36 530558 = 181900 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 530558) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 530558) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 530558) (weight := rowWeight keep0 twice0) (xs := [256, 320, 384, 448, 512, 576, 640, 704, 768, 832, 896, 960, 1023]) check rows elimOK (by decide) (by decide) cover530558 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h78646 : P.leaf 36 78646 = 181900 :=
  orient324 (v := 530558) (by decide) (by decide +kernel) h530558

theorem cover99815 : P.CoversSplit 26 10 99815 0xcc00000000000000000000000000000000000000000000000000000000000000440000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 629, 636, 873, 881, 930, 958, 965, 1273, 1315]) (by decide +kernel)

theorem h99815 : P.leaf 36 99815 = 814304 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 99815) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 99815) (weight := fun _ => 1) (xs := [762, 766, 1018, 1019, 1022, 1023]) check rows elimOK (by decide) (by decide) cover99815 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h78647 : P.leaf 36 78647 = 814304 :=
  orient72 (v := 99815) (by decide) (by decide +kernel) h99815

theorem cover274841 : P.CoversSplit 26 10 274841 0x8080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 538, 615, 629, 636, 872, 873, 923, 930, 1265, 1273]) (by decide +kernel)

theorem h274841 : P.leaf 36 274841 = 7168 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 274841) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 274841) (weight := fun _ => 1) (xs := [1015, 1023]) check rows elimOK (by decide) (by decide) cover274841 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h78648 : P.leaf 36 78648 = 7168 :=
  orient86 (v := 274841) (by decide) (by decide +kernel) h274841

theorem cover274845 : P.CoversSplit 26 10 274845 0x8080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 538, 615, 629, 636, 872, 873, 923, 930, 1265, 1273]) (by decide +kernel)

theorem h274845 : P.leaf 36 274845 = 78464 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 274845) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 274845) (weight := fun _ => 1) (xs := [1015, 1023]) check rows elimOK (by decide) (by decide) cover274845 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h78649 : P.leaf 36 78649 = 78464 :=
  orient86 (v := 274845) (by decide) (by decide +kernel) h274845

theorem cover274873 : P.CoversSplit 26 10 274873 0xc0c0000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 629, 636, 872, 873, 923, 930, 1273, 1658, 1665]) (by decide +kernel)

theorem h274873 : P.leaf 36 274873 = 118120 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 274873) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 274873) (weight := fun _ => 1) (xs := [788, 1014, 1015, 1022, 1023]) check rows elimOK (by decide) (by decide) cover274873 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h78650 : P.leaf 36 78650 = 118120 :=
  orient86 (v := 274873) (by decide) (by decide +kernel) h274873

theorem cover274877 : P.CoversSplit 26 10 274877 0xc0c0000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [538, 629, 636, 872, 923, 930, 972, 1273, 1658, 1665]) (by decide +kernel)

theorem h274877 : P.leaf 36 274877 = 529272 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 274877) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 274877) (weight := fun _ => 1) (xs := [788, 1014, 1015, 1022, 1023]) check rows elimOK (by decide) (by decide) cover274877 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h78651 : P.leaf 36 78651 = 529272 :=
  orient86 (v := 274877) (by decide) (by decide +kernel) h274877

theorem cover99819 : P.CoversSplit 26 10 99819 0xa0a0000000000000000000000000000000000000000000000000000000000000000000000000000000000505000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 629, 636, 873, 881, 922, 958, 965, 1322]) (by decide +kernel)

theorem h99819 : P.leaf 36 99819 = 994626 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 99819) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 99819) (weight := fun _ => 1) (xs := [672, 674, 680, 682, 1013, 1015, 1021, 1023]) check rows elimOK (by decide) (by decide) cover99819 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h78654 : P.leaf 36 78654 = 994626 :=
  orient72 (v := 99819) (by decide) (by decide +kernel) h99819

theorem cover100327 : P.CoversSplit 26 10 100327 0xff00000000000000000000000000000000000000333300000000000000000000ff00000000000000000000000000000000000000333300000000000000000000ff00000000000000000000000000000000000000000000000000000000000000ff00000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 873, 874, 881, 923, 930, 1322]) (by decide +kernel)

theorem c100327_0 : P.sumLeaves 26 102734848 1024 = 5653362 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 100327) (lo := 0) (len := 1024) (W := 5653362) check rows elimOK (by decide) (by decide) cover100327 (by decide)
  decide +kernel

theorem h100327 : P.leaf 36 100327 = 5653362 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 5653362)]) (.cons c100327_0 (.nil)) (by decide) (by decide))

theorem h78655 : P.leaf 36 78655 = 5653362 :=
  orient84 (v := 100327) (by decide) (by decide +kernel) h100327

theorem cover296339 : P.CoversSplit 26 10 296339 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 482, 488, 489, 530, 538, 629, 636, 922, 929]) (by decide +kernel)

theorem h296339 : P.leaf 36 296339 = 6848 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 296339) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 296339) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover296339 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h78665 : P.leaf 36 78665 = 6848 :=
  orient6 (v := 296339) (by decide) (by decide +kernel) h296339

theorem cover274839 : P.CoversSplit 26 10 274839 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 538, 615, 629, 636, 872, 873, 929, 930, 1265]) (by decide +kernel)

theorem h274839 : P.leaf 36 274839 = 52976 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 274839) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 274839) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover274839 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h78667 : P.leaf 36 78667 = 52976 :=
  orient74 (v := 274839) (by decide) (by decide +kernel) h274839

theorem cover274843 : P.CoversSplit 26 10 274843 0x8080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 538, 615, 629, 636, 872, 873, 923, 979, 1265, 1273]) (by decide +kernel)

theorem h274843 : P.leaf 36 274843 = 68480 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 274843) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 274843) (weight := fun _ => 1) (xs := [1015, 1023]) check rows elimOK (by decide) (by decide) cover274843 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h78670 : P.leaf 36 78670 = 68480 :=
  orient74 (v := 274843) (by decide) (by decide +kernel) h274843

theorem cover274847 : P.CoversSplit 26 10 274847 0x8080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 538, 615, 629, 636, 872, 873, 923, 1265, 1273]) (by decide +kernel)

theorem h274847 : P.leaf 36 274847 = 765392 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 274847) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 274847) (weight := fun _ => 1) (xs := [1015, 1023]) check rows elimOK (by decide) (by decide) cover274847 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h78671 : P.leaf 36 78671 = 765392 :=
  orient74 (v := 274847) (by decide) (by decide +kernel) h274847

theorem cover274871 : P.CoversSplit 26 10 274871 0xc000c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 538, 629, 636, 873, 929, 930, 972, 979, 1265, 1658]) (by decide +kernel)

theorem h274871 : P.leaf 36 274871 = 707328 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 274871) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 274871) (weight := fun _ => 1) (xs := [1006, 1007, 1022, 1023]) check rows elimOK (by decide) (by decide) cover274871 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h78683 : P.leaf 36 78683 = 707328 :=
  orient74 (v := 274871) (by decide) (by decide +kernel) h274871

theorem cover296378 : P.CoversSplit 26 10 296378 0x8080808000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [468, 479, 481, 538, 922, 929, 1266, 1658, 1665]) (by decide +kernel)

theorem h296378 : P.leaf 36 296378 = 90752 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 296378) (keep := keep4) (twice := twice4) rows (by decide) (by decide) bal4 (invRow4 (H := 296378) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 296378) (weight := rowWeight keep4 twice4) (xs := [999, 1007, 1015, 1023]) check rows elimOK (by decide) (by decide) cover296378 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h78684 : P.leaf 36 78684 = 90752 :=
  orient6 (v := 296378) (by decide) (by decide +kernel) h296378

theorem cover296379 : P.CoversSplit 26 10 296379 0x8080808000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 629, 636, 922, 929, 1266, 1658, 1665]) (by decide +kernel)

theorem h296379 : P.leaf 36 296379 = 550016 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 296379) (keep := keep4) (twice := twice4) rows (by decide) (by decide) bal4 (invRow4 (H := 296379) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 296379) (weight := rowWeight keep4 twice4) (xs := [999, 1007, 1015, 1023]) check rows elimOK (by decide) (by decide) cover296379 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h78685 : P.leaf 36 78685 = 550016 :=
  orient6 (v := 296379) (by decide) (by decide +kernel) h296379

theorem cover274875 : P.CoversSplit 26 10 274875 0xc0c0000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 629, 636, 873, 923, 979, 1273, 1658, 1665]) (by decide +kernel)

theorem h274875 : P.leaf 36 274875 = 559646 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 274875) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 274875) (weight := fun _ => 1) (xs := [788, 1014, 1015, 1022, 1023]) check rows elimOK (by decide) (by decide) cover274875 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h78686 : P.leaf 36 78686 = 559646 :=
  orient74 (v := 274875) (by decide) (by decide +kernel) h274875

theorem cover274879 : P.CoversSplit 26 10 274879 0xc0c0c0c400000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [538, 629, 636, 873, 923, 972, 979, 1265, 1273, 1658, 1665]) (by decide +kernel)

theorem h274879 : P.leaf 36 274879 = 10205170 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 274879) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 274879) (weight := fun _ => 1) (xs := [788, 994, 998, 999, 1006, 1007, 1014, 1015, 1022, 1023]) check rows elimOK (by decide) (by decide) cover274879 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h78687 : P.leaf 36 78687 = 10205170 :=
  orient74 (v := 274879) (by decide) (by decide +kernel) h274879

theorem cover530942 : P.CoversSplit 26 10 530942 0xf000000000000001f000000000000000f000000000000000f000000000000000000005000000000100000000000000000000050000000000000000000000000000000000003000010000000000300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [629, 636, 874, 922, 930, 972, 979, 1265, 1273, 1315, 1322]) (by decide +kernel)

theorem h530942 : P.leaf 36 530942 = 5499460 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 530942) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 530942) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 530942) (weight := rowWeight keep0 twice0) (xs := [404, 405, 448, 468, 469, 616, 618, 704, 744, 746, 828, 829, 830, 831, 892, 893, 894, 895, 956, 957, 958, 959, 960, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover530942 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h78718 : P.leaf 36 78718 = 5499460 :=
  orient324 (v := 530942) (by decide) (by decide +kernel) h530942

theorem cover296447 : P.CoversSplit 26 10 296447 0xffffffffffffffff000000000000000000000000000000001111101011001000555555555555555555555050555550500000000000000000111110101100100033333333333333330000000000000000333333333300330011111010110010001111111111111111111110101111101011111111110011001111101011001000 :=
  coversSplit check rows (by decide) (by decide) (xs := [629, 636, 873, 881, 1658, 1665]) (by decide +kernel)

noncomputable def f296447 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 26 (303561728 + i)

theorem c296447_0 : rowSum f296447 0 816 = 39105872 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 296447) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover296447 (by decide)
  decide +kernel

theorem c296447_1 : rowSum f296447 816 208 = 149562676 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 296447) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover296447 (by decide)
  decide +kernel

theorem sum296447 : rowSum f296447 0 1024 = 188668548 :=
  rowSum_append (F := f296447) (lo := 0) (n := 816) (m := 208) (A := 39105872) (B := 149562676) c296447_0 (c296447_1)

theorem h296447 : P.leaf 36 296447 = 188668548 :=
  leaf_weighted (k := 26) (d := 10) (H := 296447) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 296447) (by decide) (by decide +kernel)) sum296447

theorem h78719 : P.leaf 36 78719 = 188668548 :=
  orient6 (v := 296447) (by decide) (by decide +kernel) h296447

theorem cover99671 : P.CoversSplit 26 10 99671 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 579, 629, 636, 873, 881, 930, 1273, 1315]) (by decide +kernel)

theorem h99671 : P.leaf 36 99671 = 83888 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 99671) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 99671) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover99671 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h78727 : P.leaf 36 78727 = 83888 :=
  orient72 (v := 99671) (by decide) (by decide +kernel) h99671

theorem cover531091 : P.CoversSplit 26 10 531091 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 482, 488, 489, 530, 537, 922, 930, 972, 979]) (by decide +kernel)

theorem h531091 : P.leaf 36 531091 = 16384 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 531091) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 531091) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover531091 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h78729 : P.leaf 36 78729 = 16384 :=
  orient324 (v := 531091) (by decide) (by decide +kernel) h531091

theorem cover531095 : P.CoversSplit 26 10 531095 0xc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [489, 530, 531, 538, 587, 922, 923, 929, 930, 979, 1265, 1315]) (ps := [(16, [867], [1265])]) (by decide +kernel)

theorem h531095 : P.leaf 36 531095 = 89600 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 531095) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 531095) (weight := fun _ => 1) (xs := [1022, 1023]) check rows elimOK (by decide) (by decide) cover531095 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h78731 : P.leaf 36 78731 = 89600 :=
  orient324 (v := 531095) (by decide) (by decide +kernel) h531095

theorem cover80293 : P.CoversSplit 26 10 80293 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000200000000001000010000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 482, 489, 538, 629, 636, 930, 972, 979, 1315, 1658]) (by decide +kernel)

theorem h80293 : P.leaf 36 80293 = 56606 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 80293) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 80293) (weight := fun _ => 1) (xs := [256, 276, 321, 341, 1023]) check rows elimOK (by decide) (by decide) cover80293 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h78734 : P.leaf 36 78734 = 56606 :=
  orient325 (v := 80293) (by decide) (by decide +kernel) h80293

theorem cover99679 : P.CoversSplit 26 10 99679 0xa0a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000a080000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 579, 629, 636, 873, 881, 1315, 1322, 1665]) (by decide +kernel)

theorem h99679 : P.leaf 36 99679 = 966304 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 99679) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 99679) (weight := fun _ => 1) (xs := [343, 349, 351, 1013, 1015, 1021, 1023]) check rows elimOK (by decide) (by decide) cover99679 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h78735 : P.leaf 36 78735 = 966304 :=
  orient72 (v := 99679) (by decide) (by decide +kernel) h99679

theorem cover99698 : P.CoversSplit 26 10 99698 0x8000000000000000000000000000000000000000000000000000000000001111000000000000000000000000000000000000000000000000000000000000101000000000000000000000000000000000000000000000000000000000000011000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 531, 579, 608, 629, 636, 873, 881, 922, 930, 1273]) (by decide +kernel)

theorem h99698 : P.leaf 36 99698 = 35168 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 99698) (keep := keep12) (twice := twice12) rows (by decide) (by decide) bal12 (invRow12 (H := 99698) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 99698) (weight := rowWeight keep12 twice12) (xs := [264, 268, 516, 524, 768, 772, 776, 780, 1023]) check rows elimOK (by decide) (by decide) cover99698 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h78740 : P.leaf 36 78740 = 35168 :=
  orient72 (v := 99698) (by decide) (by decide +kernel) h99698

theorem cover99702 : P.CoversSplit 26 10 99702 0xc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [489, 531, 579, 629, 636, 873, 881, 922, 930, 958, 1273, 1315]) (ps := [(18, [1266], [1315])]) (by decide +kernel)

theorem h99702 : P.leaf 36 99702 = 50256 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 99702) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 99702) (weight := fun _ => 1) (xs := [1022, 1023]) check rows elimOK (by decide) (by decide) cover99702 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h78741 : P.leaf 36 78741 = 50256 :=
  orient72 (v := 99702) (by decide) (by decide +kernel) h99702

theorem cover99699 : P.CoversSplit 26 10 99699 0x8000000000000000000000000000000000000000000000000000000000001111000000000000000000000000000000000000000000000000000000000000101000000000000000000000000000000000000000000000000000000000000011000000000000000000000000000000000000000000000000000000000000001000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 579, 608, 629, 636, 873, 881, 922, 930, 1273]) (by decide +kernel)

theorem h99699 : P.leaf 36 99699 = 172902 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 99699) (keep := keep12) (twice := twice12) rows (by decide) (by decide) bal12 (invRow12 (H := 99699) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 99699) (weight := rowWeight keep12 twice12) (xs := [12, 264, 268, 516, 524, 768, 772, 776, 780, 1023]) check rows elimOK (by decide) (by decide) cover99699 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h78742 : P.leaf 36 78742 = 172902 :=
  orient72 (v := 99699) (by decide) (by decide +kernel) h99699

theorem cover99703 : P.CoversSplit 26 10 99703 0xc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [489, 579, 629, 636, 873, 881, 922, 930, 958, 1273, 1315]) (ps := [(18, [1266], [1315])]) (by decide +kernel)

theorem h99703 : P.leaf 36 99703 = 453508 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 99703) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 99703) (weight := fun _ => 1) (xs := [1022, 1023]) check rows elimOK (by decide) (by decide) cover99703 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h78743 : P.leaf 36 78743 = 453508 :=
  orient72 (v := 99703) (by decide) (by decide +kernel) h99703

theorem cover100181 : P.CoversSplit 26 10 100181 0xa0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [489, 530, 559, 579, 873, 874, 881, 930, 1315, 1322]) (ps := [(11, [474], [930])]) (by decide +kernel)

theorem h100181 : P.leaf 36 100181 = 108256 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 100181) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 100181) (weight := fun _ => 1) (xs := [509, 511, 1021, 1023]) check rows elimOK (by decide) (by decide) cover100181 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h78745 : P.leaf 36 78745 = 108256 :=
  orient84 (v := 100181) (by decide) (by decide +kernel) h100181

theorem cover274933 : P.CoversSplit 26 10 274933 0xf0000000f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [489, 629, 636, 872, 929, 930, 972, 979, 1273, 1658, 1665]) (ps := [(15, [559], [930])]) (by decide +kernel)

theorem h274933 : P.leaf 36 274933 = 352640 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 274933) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 274933) (weight := fun _ => 1) (xs := [988, 989, 990, 991, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover274933 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h78747 : P.leaf 36 78747 = 352640 :=
  orient86 (v := 274933) (by decide) (by decide +kernel) h274933

theorem cover530619 : P.CoversSplit 26 10 530619 0xc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [481, 538, 587, 629, 636, 874, 922, 930, 965, 972, 1265, 1273, 1308]) (ps := [(11, [879], [922])]) (by decide +kernel)

theorem h530619 : P.leaf 36 530619 = 125312 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 530619) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 530619) (weight := fun _ => 1) (xs := [1022, 1023]) check rows elimOK (by decide) (by decide) cover530619 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h78748 : P.leaf 36 78748 = 125312 :=
  orient324 (v := 530619) (by decide) (by decide +kernel) h530619

theorem cover531131 : P.CoversSplit 26 10 531131 0xf030000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [481, 538, 922, 929, 930, 972, 979, 1265, 1266, 1272, 1322]) (ps := [(11, [879], [922, 930]), (16, [866], [1273])]) (by decide +kernel)

theorem h531131 : P.leaf 36 531131 = 418416 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 531131) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 531131) (weight := fun _ => 1) (xs := [500, 501, 1012, 1013, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover531131 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h78749 : P.leaf 36 78749 = 418416 :=
  orient324 (v := 531131) (by decide) (by decide +kernel) h531131

def seg : List (ℕ × ℕ) := [(78646, 180), (78647, 180), (78648, 360), (78649, 360), (78650, 720), (78651, 720), (78654, 360), (78655, 360), (78665, 90), (78667, 720), (78670, 360), (78671, 360), (78683, 360), (78684, 360), (78685, 360), (78686, 720), (78687, 720), (78718, 180), (78719, 180), (78727, 360), (78729, 360), (78731, 720), (78734, 360), (78735, 360), (78740, 120), (78741, 360), (78742, 360), (78743, 720), (78745, 720), (78747, 720), (78748, 720), (78749, 720)]

theorem segOK : checkSeg 20 perms 78646 78750 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 78646 78750 14250 48197988240 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 48197988240)
    (SegSum.cons (w := 180) h78646 (SegSum.cons (w := 180) h78647 (SegSum.cons (w := 360) h78648 (SegSum.cons (w := 360) h78649 (SegSum.cons (w := 720) h78650 (SegSum.cons (w := 720) h78651 (SegSum.cons (w := 360) h78654 (SegSum.cons (w := 360) h78655 (SegSum.cons (w := 90) h78665 (SegSum.cons (w := 720) h78667 (SegSum.cons (w := 360) h78670 (SegSum.cons (w := 360) h78671 (SegSum.cons (w := 360) h78683 (SegSum.cons (w := 360) h78684 (SegSum.cons (w := 360) h78685 (SegSum.cons (w := 720) h78686 (SegSum.cons (w := 720) h78687 (SegSum.cons (w := 180) h78718 (SegSum.cons (w := 180) h78719 (SegSum.cons (w := 360) h78727 (SegSum.cons (w := 360) h78729 (SegSum.cons (w := 720) h78731 (SegSum.cons (w := 360) h78734 (SegSum.cons (w := 360) h78735 (SegSum.cons (w := 120) h78740 (SegSum.cons (w := 360) h78741 (SegSum.cons (w := 360) h78742 (SegSum.cons (w := 720) h78743 (SegSum.cons (w := 720) h78745 (SegSum.cons (w := 720) h78747 (SegSum.cons (w := 720) h78748 (SegSum.cons (w := 720) h78749 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S42
