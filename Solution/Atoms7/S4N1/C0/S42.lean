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

namespace RACert.S4N1.C0.S42

open RACert RACert.Problem

theorem cover6630 : P.CoversSplit 24 10 6630 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 465, 466, 515, 522, 858, 859, 865, 879, 1209, 1258]) (by decide +kernel)

theorem c6630_0 : P.sumLeaves 24 6789120 1024 = 269344 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6630) (lo := 0) (len := 1024) (W := 269344) check rows elimOK (by decide) (by decide) cover6630 (by decide)
  decide +kernel

theorem h6630 : P.leaf 34 6630 = 269344 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 269344)]) (.cons c6630_0 (.nil)) (by decide) (by decide))

theorem cover6631 : P.CoversSplit 24 10 6631 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 515, 522, 858, 859, 865, 866, 1209, 1217, 1258, 1266]) (by decide +kernel)

theorem c6631_0 : P.sumLeaves 24 6790144 1024 = 1556670 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6631) (lo := 0) (len := 1024) (W := 1556670) check rows elimOK (by decide) (by decide) cover6631 (by decide)
  decide +kernel

theorem h6631 : P.leaf 34 6631 = 1556670 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1556670)]) (.cons c6631_0 (.nil)) (by decide) (by decide))

theorem cover6636 : P.CoversSplit 24 10 6636 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem c6636_0 : P.sumLeaves 24 6795264 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6636) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover6636 (by decide)
  decide +kernel

theorem h6636 : P.leaf 34 6636 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c6636_0 (.nil)) (by decide) (by decide))

theorem cover6637 : P.CoversSplit 24 10 6637 0x8000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 466, 473, 515, 522, 858, 865, 879, 916, 1209, 1258]) (by decide +kernel)

theorem c6637_0 : P.sumLeaves 24 6796288 1024 = 517668 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6637) (lo := 0) (len := 1024) (W := 517668) check rows elimOK (by decide) (by decide) cover6637 (by decide)
  decide +kernel

theorem h6637 : P.leaf 34 6637 = 517668 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 517668)]) (.cons c6637_0 (.nil)) (by decide) (by decide))

theorem cover6639 : P.CoversSplit 24 10 6639 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 515, 522, 858, 859, 865, 866, 1209, 1217, 1258, 1266]) (by decide +kernel)

noncomputable def f6639 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (6798336 + i)

theorem c6639_0 : rowSum f6639 0 1024 = 4277968 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 6639) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover6639 (by decide)
  decide +kernel

theorem sum6639 : rowSum f6639 0 1024 = 4277968 :=
  c6639_0

theorem h6639 : P.leaf 34 6639 = 4277968 :=
  leaf_weighted (k := 24) (d := 10) (H := 6639) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 6639) (by decide) (by decide +kernel)) sum6639

theorem cover6640 : P.CoversSplit 24 10 6640 0xf0000000a0000000000000000000000000000000000000000000000000000000c00000008008000000000000000000000000000000000000000000000000000000000000000000000000000000000000f00000000000aa000000000000000000000000000000000000000000000000000000000000000000c0c0000000008888 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 858, 859, 865, 866, 879, 909, 916, 1202, 1259, 1601]) (by decide +kernel)

theorem contract6640_0 : P.leaf 30 106240 = 12 := by
  exact leaf_contract_factors (k := 30) (b := 5) (H := 106240) (ss := [(2, 1, 466), (10, 0, 866), (11, 0, 458), (12, 0, 458), (6, 0, 809), (26, 1, 465), (27, 1, 473), (7, 1, 481), (8, 1, 482), (9, 1, 489), (14, 0, 810), (28, 13, 852), (30, 18, 867), (19, 16, 872), (31, 20, 874), (21, 0, 880), (29, 15, 901), (17, 0, 908), (18, 0, 909), (22, 1, 417), (5, 3, 524), (20, 0, 858), (4, 3, 536), (24, 16, 860), (25, 16, 915)]) (ids := [1, 14, 11, 13, 21]) (cs := [1, 2, 2, 2, 0, 1, 1, 1, 0, 0, 0, 4, 0, 5, 3, 0, 0, 3, 0, 0, 1, 6, 3, 3, 1, 1, 4, 5, 0, 0]) (bs := [2, 3]) (W := 12) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c6640_0 : P.sumLeaves 24 6799360 64 = 12 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 106240) rows (by decide) (by decide)).symm.trans contract6640_0

theorem c6640_1 : P.sumLeaves 24 6799424 256 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6640) (lo := 64) (len := 256) (W := 0) check rows elimOK (by decide) (by decide) cover6640 (by decide)
  decide +kernel

theorem contract6640_2 : P.leaf 30 106245 = 7680 := by
  exact leaf_contract_factors (k := 30) (b := 15) (H := 106245) (ss := [(2, 1, 466), (29, 1, 865), (10, 1, 866), (3, 1, 409), (5, 1, 411), (4, 1, 410), (6, 1, 459), (11, 1, 459), (12, 1, 460), (30, 18, 867), (17, 1, 908), (18, 1, 909), (28, 1, 858), (31, 1, 859), (8, 1, 1266)]) (ids := [5, 7, 11, 12, 13, 14, 17, 18, 19, 20, 24, 25, 21, 22, 23]) (cs := [1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 4, 5, 6, 7, 1, 1, 8, 9, 10, 11, 14, 15, 16, 12, 13, 1, 1, 1, 1]) (bs := [12, 3]) (W := 7680) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c6640_2 : P.sumLeaves 24 6799680 64 = 7680 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 106245) rows (by decide) (by decide)).symm.trans contract6640_2

theorem c6640_3 : P.sumLeaves 24 6799744 640 = 33736 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6640) (lo := 384) (len := 640) (W := 33736) check rows elimOK (by decide) (by decide) cover6640 (by decide)
  decide +kernel

theorem h6640 : P.leaf 34 6640 = 41428 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(64, 12), (256, 0), (64, 7680), (640, 33736)]) (.cons c6640_0 (.cons c6640_1 (.cons c6640_2 (.cons c6640_3 (.nil))))) (by decide) (by decide))

theorem cover6641 : P.CoversSplit 24 10 6641 0xff000000af000000000000000000000000000000000000000000000000000000cc03000088000000000000000000000000000000000000000000000000000000ff000000af0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 858, 865, 866, 867, 879, 916, 1202, 1209, 1259, 1601]) (by decide +kernel)

theorem c6641_0 : P.sumLeaves 24 6800384 1024 = 687700 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6641) (lo := 0) (len := 1024) (W := 687700) check rows elimOK (by decide) (by decide) cover6641 (by decide)
  decide +kernel

theorem h6641 : P.leaf 34 6641 = 687700 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 687700)]) (.cons c6641_0 (.nil)) (by decide) (by decide))

theorem cover6643 : P.CoversSplit 24 10 6643 0xffff0000afaa00000000000000000000ffff0000afaa00000000000000000000ccfc0000888800000000000000000000ccfc0000888800000000000000000000ffff0000afaa00000000000000000000ffff0000aaaa00000000000000000000ccfc0000888800000000000000000000cccc0000888800000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [858, 859, 865, 866, 867, 1202, 1209, 1217, 1258, 1259, 1601, 1609]) (by decide +kernel)

noncomputable def f6643 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (6802432 + i)

theorem c6643_0 : rowSum f6643 0 1024 = 15939899 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 6643) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover6643 (by decide)
  decide +kernel

theorem sum6643 : rowSum f6643 0 1024 = 15939899 :=
  c6643_0

theorem h6643 : P.leaf 34 6643 = 15939899 :=
  leaf_weighted (k := 24) (d := 10) (H := 6643) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 6643) (by decide) (by decide +kernel)) sum6643

theorem cover6644 : P.CoversSplit 24 10 6644 0xf0000000a000a000000000000000000000000000000000000000000000000000c00000008008800000000000000000000000000000000000000000000000000000000000000000000000000000000000f000000000000a0000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 858, 859, 865, 866, 879, 916, 1202, 1259, 1601]) (ps := [(11, [909], [858])]) (by decide +kernel)

theorem c6644_0 : P.sumLeaves 24 6803456 1024 = 303976 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6644) (lo := 0) (len := 1024) (W := 303976) check rows elimOK (by decide) (by decide) cover6644 (by decide)
  decide +kernel

theorem h6644 : P.leaf 34 6644 = 303976 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 303976)]) (.cons c6644_0 (.nil)) (by decide) (by decide))

theorem cover6645 : P.CoversSplit 24 10 6645 0xff00ff00af00a000000000000000000000000000000000000000000000000000cc03cc0388008000000000000000000000000000000000000000000000000000ff00ff00af00a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 858, 865, 866, 879, 916, 1202, 1209, 1259, 1601]) (by decide +kernel)

theorem c6645_0 : P.sumLeaves 24 6804480 1024 = 2522020 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6645) (lo := 0) (len := 1024) (W := 2522020) check rows elimOK (by decide) (by decide) cover6645 (by decide)
  decide +kernel

theorem h6645 : P.leaf 34 6645 = 2522020 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 2522020)]) (.cons c6645_0 (.nil)) (by decide) (by decide))

theorem cover6646 : P.CoversSplit 24 10 6646 0xf0f00000a0a500000000000000000000f0f00000000000000000000000000000c0f00000808000000000000000000000c0f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 858, 859, 865, 866, 879, 1202, 1258, 1259, 1601]) (by decide +kernel)

theorem c6646_0 : P.sumLeaves 24 6805504 1024 = 3032736 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6646) (lo := 0) (len := 1024) (W := 3032736) check rows elimOK (by decide) (by decide) cover6646 (by decide)
  decide +kernel

theorem h6646 : P.leaf 34 6646 = 3032736 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 3032736)]) (.cons c6646_0 (.nil)) (by decide) (by decide))

theorem cover6647 : P.CoversSplit 24 10 6647 0xffffffffafaaa0a00000000000000000ffffffffafaaa0a00000000000000000ccfcccfc888880800000000000000000ccfcccfc888880800000000000000000ffffffffafaaa0a00000000000000000ffffffffaaaaa0a00000000000000000ccfcccfc888880800000000000000000cccccccc888880800000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [858, 859, 865, 866, 1202, 1209, 1217, 1258, 1259, 1601, 1609]) (by decide +kernel)

theorem c6647_0 : P.sumLeaves 24 6806528 465 = 4419377 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6647) (lo := 0) (len := 465) (W := 4419377) check rows elimOK (by decide) (by decide) cover6647 (by decide)
  decide +kernel

theorem c6647_1 : P.sumLeaves 24 6806993 380 = 16975260 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6647) (lo := 465) (len := 380) (W := 16975260) check rows elimOK (by decide) (by decide) cover6647 (by decide)
  decide +kernel

theorem c6647_2 : P.sumLeaves 24 6807373 179 = 30036588 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6647) (lo := 845) (len := 179) (W := 30036588) check rows elimOK (by decide) (by decide) cover6647 (by decide)
  decide +kernel

theorem h6647 : P.leaf 34 6647 = 51431225 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(465, 4419377), (380, 16975260), (179, 30036588)]) (.cons c6647_0 (.cons c6647_1 (.cons c6647_2 (.nil)))) (by decide) (by decide))

theorem cover6652 : P.CoversSplit 24 10 6652 0xf0000000a000aa00000000000000000000000000000000000000000000000000c000000080088808c0c00000808888880000000000000000000000000000000000000000000000000000000000000000f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 858, 859, 865, 879, 916, 1202, 1259, 1601]) (by decide +kernel)

noncomputable def f6652 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (6811648 + i)

theorem c6652_0 : rowSum f6652 0 1024 = 1237453 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 6652) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover6652 (by decide)
  decide +kernel

theorem sum6652 : rowSum f6652 0 1024 = 1237453 :=
  c6652_0

theorem h6652 : P.leaf 34 6652 = 1237453 :=
  leaf_weighted (k := 24) (d := 10) (H := 6652) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 6652) (by decide) (by decide +kernel)) sum6652

theorem cover6653 : P.CoversSplit 24 10 6653 0xff00ff00af00a000000000000000000000000000000000000000000000000000cc03cc0388008000000000000000000000000000000000000000000000000000ff00ff00af00a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 858, 865, 879, 916, 1202, 1209, 1259, 1601]) (by decide +kernel)

theorem c6653_0 : P.sumLeaves 24 6812672 1024 = 8912021 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6653) (lo := 0) (len := 1024) (W := 8912021) check rows elimOK (by decide) (by decide) cover6653 (by decide)
  decide +kernel

theorem h6653 : P.leaf 34 6653 = 8912021 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 8912021)]) (.cons c6653_0 (.nil)) (by decide) (by decide))

theorem cover6655 : P.CoversSplit 24 10 6655 0xffffffffafaaaaaaffffffffafaaaaaaffffffffafaaaaaaffffffffafaaaaaaccfcccfc88888888cccccccc88888888ccfcccfc88888888cccccccc88888888ffffffffafaaaaaaffffffffafaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaccfcccfc88888888cccccccc88888888cccccccc88888888cccccccc88888888 :=
  coversSplit check rows (by decide) (by decide) (xs := [858, 865, 1202, 1209, 1217, 1258, 1259, 1601, 1609]) (by decide +kernel)

noncomputable def f6655 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (6814720 + i)

theorem c6655_0 : rowSum f6655 0 291 = 51933378 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 6655) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover6655 (by decide)
  decide +kernel

theorem c6655_1 : rowSum f6655 291 181 = 71069718 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 6655) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover6655 (by decide)
  decide +kernel

theorem c6655_2 : rowSum f6655 472 474 = 157954578 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 6655) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover6655 (by decide)
  decide +kernel

theorem c6655_3 : rowSum f6655 946 78 = 85330614 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 6655) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover6655 (by decide)
  decide +kernel

theorem sum6655 : rowSum f6655 0 1024 = 366288288 :=
  rowSum_append (F := f6655) (lo := 0) (n := 291) (m := 733) (A := 51933378) (B := 314354910) c6655_0 (rowSum_append (F := f6655) (lo := 291) (n := 181) (m := 552) (A := 71069718) (B := 243285192) c6655_1 (rowSum_append (F := f6655) (lo := 472) (n := 474) (m := 78) (A := 157954578) (B := 85330614) c6655_2 (c6655_3)))

theorem h6655 : P.leaf 34 6655 = 366288288 :=
  leaf_weighted (k := 24) (d := 10) (H := 6655) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 6655) (by decide) (by decide +kernel)) sum6655

theorem cover6868 : P.CoversSplit 24 10 6868 0xffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 475, 479, 573, 859, 1202, 1210, 1259, 1264]) (by decide +kernel)

noncomputable def f6868 (i : ℕ) := rowWeight keep5 twice5 i * P.leaf 24 (7032832 + i)

theorem c6868_0 : rowSum f6868 0 1024 = 95136 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 6868) (keep := keep5) (twice := twice5) check rows elimOK (by decide) (by decide) cover6868 (by decide)
  decide +kernel

theorem sum6868 : rowSum f6868 0 1024 = 95136 :=
  c6868_0

theorem h6868 : P.leaf 34 6868 = 95136 :=
  leaf_weighted (k := 24) (d := 10) (H := 6868) (keep := keep5) (twice := twice5) rows (by decide) (by decide) bal5 (invRow5 (H := 6868) (by decide) (by decide +kernel)) sum6868

theorem cover6869 : P.CoversSplit 24 10 6869 0xffff0000000000000000000000000000a0a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 475, 479, 516, 573, 859, 1202, 1209, 1210, 1259, 1264]) (by decide +kernel)

theorem c6869_0 : P.sumLeaves 24 7033856 832 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6869) (lo := 0) (len := 832) (W := 0) check rows elimOK (by decide) (by decide) cover6869 (by decide)
  decide +kernel

theorem contract6869_1 : P.leaf 30 109917 = 35968 := by
  exact leaf_contract_factors (k := 30) (b := 18) (H := 109917) (ss := [(31, 1, 479), (18, 1, 487), (8, 1, 537), (26, 1, 516), (17, 1, 537), (14, 1, 880), (28, 1, 859), (30, 1, 1210), (16, 1, 1265), (19, 1, 1273), (21, 1, 1315), (20, 1, 1364)]) (ids := [0, 1, 2, 3, 4, 5, 7, 8, 9, 10, 11, 13, 20, 21, 25, 27, 22, 23]) (cs := [2, 3, 4, 5, 6, 7, 1, 8, 9, 10, 11, 12, 1, 13, 1, 1, 1, 1, 1, 1, 14, 15, 18, 19, 1, 16, 1, 17, 1, 1]) (bs := [16, 2]) (W := 35968) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c6869_1 : P.sumLeaves 24 7034688 64 = 35968 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 109917) rows (by decide) (by decide)).symm.trans contract6869_1

theorem c6869_2 : P.sumLeaves 24 7034752 128 = 1217776 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6869) (lo := 896) (len := 128) (W := 1217776) check rows elimOK (by decide) (by decide) cover6869 (by decide)
  decide +kernel

theorem h6869 : P.leaf 34 6869 = 1253744 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(832, 0), (64, 35968), (128, 1217776)]) (.cons c6869_0 (.cons c6869_1 (.cons c6869_2 (.nil)))) (by decide) (by decide))

theorem cover6871 : P.CoversSplit 24 10 6871 0xffff0000000000000000000000000000a0a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [475, 479, 516, 573, 859, 916, 1202, 1209, 1210, 1251, 1259, 1264]) (by decide +kernel)

noncomputable def f6871 (i : ℕ) := rowWeight keep5 twice5 i * P.leaf 24 (7035904 + i)

theorem c6871_0 : rowSum f6871 0 1024 = 3198704 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 6871) (keep := keep5) (twice := twice5) check rows elimOK (by decide) (by decide) cover6871 (by decide)
  decide +kernel

theorem sum6871 : rowSum f6871 0 1024 = 3198704 :=
  c6871_0

theorem h6871 : P.leaf 34 6871 = 3198704 :=
  leaf_weighted (k := 24) (d := 10) (H := 6871) (keep := keep5) (twice := twice5) rows (by decide) (by decide) bal5 (invRow5 (H := 6871) (by decide) (by decide +kernel)) sum6871

theorem cover6876 : P.CoversSplit 24 10 6876 0xffff0000000000000000000000000000a0a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 516, 536, 573, 859, 916, 1202, 1210, 1251, 1259, 1264]) (by decide +kernel)

noncomputable def f6876 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (7041024 + i)

theorem c6876_0 : rowSum f6876 0 1024 = 1391496 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 6876) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover6876 (by decide)
  decide +kernel

theorem sum6876 : rowSum f6876 0 1024 = 1391496 :=
  c6876_0

theorem h6876 : P.leaf 34 6876 = 1391496 :=
  leaf_weighted (k := 24) (d := 10) (H := 6876) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 6876) (by decide) (by decide +kernel)) sum6876

theorem cover6877 : P.CoversSplit 24 10 6877 0xffff0000000000000000000000000000a0a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 516, 536, 573, 859, 916, 1202, 1209, 1210, 1251, 1259, 1264]) (by decide +kernel)

noncomputable def f6877 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 24 (7042048 + i)

theorem c6877_0 : rowSum f6877 0 1024 = 3259280 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 6877) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover6877 (by decide)
  decide +kernel

theorem sum6877 : rowSum f6877 0 1024 = 3259280 :=
  c6877_0

theorem h6877 : P.leaf 34 6877 = 3259280 :=
  leaf_weighted (k := 24) (d := 10) (H := 6877) (keep := keep2) (twice := twice2) rows (by decide) (by decide) bal2 (invRow2 (H := 6877) (by decide) (by decide +kernel)) sum6877

theorem cover6879 : P.CoversSplit 24 10 6879 0xffff0000000000000000000000000000a0a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [516, 536, 573, 859, 916, 1202, 1209, 1210, 1251, 1259, 1264]) (by decide +kernel)

noncomputable def f6879 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (7044096 + i)

theorem c6879_0 : rowSum f6879 0 1024 = 5371140 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 6879) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover6879 (by decide)
  decide +kernel

theorem sum6879 : rowSum f6879 0 1024 = 5371140 :=
  c6879_0

theorem h6879 : P.leaf 34 6879 = 5371140 :=
  leaf_weighted (k := 24) (d := 10) (H := 6879) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 6879) (by decide) (by decide +kernel)) sum6879

theorem cover6884 : P.CoversSplit 24 10 6884 0x8888000000000000000000000000000080800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 475, 515, 522, 524, 573, 859, 1202, 1210, 1251, 1259]) (by decide +kernel)

theorem c6884_0 : P.sumLeaves 24 7049216 1024 = 148416 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6884) (lo := 0) (len := 1024) (W := 148416) check rows elimOK (by decide) (by decide) cover6884 (by decide)
  decide +kernel

theorem h6884 : P.leaf 34 6884 = 148416 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 148416)]) (.cons c6884_0 (.nil)) (by decide) (by decide))

theorem cover6885 : P.CoversSplit 24 10 6885 0xcccc0000000000000000000000000000cccc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 475, 515, 522, 524, 879, 1202, 1209, 1210, 1251, 1259]) (by decide +kernel)

theorem c6885_0 : P.sumLeaves 24 7050240 1024 = 1418528 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6885) (lo := 0) (len := 1024) (W := 1418528) check rows elimOK (by decide) (by decide) cover6885 (by decide)
  decide +kernel

theorem h6885 : P.leaf 34 6885 = 1418528 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1418528)]) (.cons c6885_0 (.nil)) (by decide) (by decide))

theorem cover6886 : P.CoversSplit 24 10 6886 0xaaaa0000000000000000000000000000a0a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000088000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 475, 515, 522, 524, 566, 573, 859, 916, 1210, 1251, 1259, 1264, 1308]) (by decide +kernel)

theorem c6886_0 : P.sumLeaves 24 7051264 1024 = 817000 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6886) (lo := 0) (len := 1024) (W := 817000) check rows elimOK (by decide) (by decide) cover6886 (by decide)
  decide +kernel

theorem h6886 : P.leaf 34 6886 = 817000 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 817000)]) (.cons c6886_0 (.nil)) (by decide) (by decide))

theorem cover6887 : P.CoversSplit 24 10 6887 0xffff0000000000000000000000000000ffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [475, 515, 522, 524, 566, 573, 916, 1202, 1209, 1210, 1251, 1259, 1264, 1308]) (by decide +kernel)

theorem c6887_0 : P.sumLeaves 24 7052288 448 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6887) (lo := 0) (len := 448) (W := 0) check rows elimOK (by decide) (by decide) cover6887 (by decide)
  decide +kernel

theorem contract6887_1 : P.leaf 30 110199 = 112928 := by
  exact leaf_contract_factors (k := 30) (b := 20) (H := 110199) (ss := [(30, 18, 524), (18, 1, 536), (27, 1, 573), (29, 1, 916), (14, 1, 923), (8, 1, 580), (31, 1, 1210), (16, 1, 1265), (20, 1, 1657), (21, 1, 1658)]) (ids := [0, 1, 2, 3, 4, 7, 8, 9, 10, 11, 13, 15, 17, 20, 21, 24, 26, 5, 22, 23]) (cs := [2, 3, 4, 5, 6, 19, 1, 7, 8, 9, 10, 11, 1, 12, 1, 13, 1, 14, 1, 1, 15, 16, 20, 21, 17, 1, 18, 1, 1, 1]) (bs := [17, 3]) (W := 112928) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c6887_1 : P.sumLeaves 24 7052736 64 = 112928 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 110199) rows (by decide) (by decide)).symm.trans contract6887_1

theorem c6887_2 : P.sumLeaves 24 7052800 512 = 4766296 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6887) (lo := 512) (len := 512) (W := 4766296) check rows elimOK (by decide) (by decide) cover6887 (by decide)
  decide +kernel

theorem h6887 : P.leaf 34 6887 = 4879224 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(448, 0), (64, 112928), (512, 4766296)]) (.cons c6887_0 (.cons c6887_1 (.cons c6887_2 (.nil)))) (by decide) (by decide))

theorem cover6888 : P.CoversSplit 24 10 6888 0x8888000000000000000000000000000080800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 515, 522, 523, 573, 859, 879, 916, 1202, 1210, 1251, 1259, 1264, 1308]) (ps := [(14, [923], [487])]) (by decide +kernel)

theorem c6888_0 : P.sumLeaves 24 7053312 1024 = 64336 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6888) (lo := 0) (len := 1024) (W := 64336) check rows elimOK (by decide) (by decide) cover6888 (by decide)
  decide +kernel

theorem h6888 : P.leaf 34 6888 = 64336 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 64336)]) (.cons c6888_0 (.nil)) (by decide) (by decide))

theorem cover6889 : P.CoversSplit 24 10 6889 0xcccc0000000000000000000000000000cccc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 515, 522, 523, 573, 879, 916, 1202, 1209, 1210, 1251, 1259, 1308]) (ps := [(14, [923], [487])]) (by decide +kernel)

theorem c6889_0 : P.sumLeaves 24 7054336 1024 = 565576 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6889) (lo := 0) (len := 1024) (W := 565576) check rows elimOK (by decide) (by decide) cover6889 (by decide)
  decide +kernel

theorem h6889 : P.leaf 34 6889 = 565576 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 565576)]) (.cons c6889_0 (.nil)) (by decide) (by decide))

theorem cover6890 : P.CoversSplit 24 10 6890 0xaaaa0000000000000000000000000000a0a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000088000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 515, 522, 523, 573, 859, 879, 916, 1210, 1251, 1259, 1264, 1308]) (by decide +kernel)

theorem c6890_0 : P.sumLeaves 24 7055360 1024 = 1433408 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6890) (lo := 0) (len := 1024) (W := 1433408) check rows elimOK (by decide) (by decide) cover6890 (by decide)
  decide +kernel

theorem h6890 : P.leaf 34 6890 = 1433408 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1433408)]) (.cons c6890_0 (.nil)) (by decide) (by decide))

theorem cover6891 : P.CoversSplit 24 10 6891 0xffff0000000000000000000000000000ffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 522, 523, 573, 879, 916, 1202, 1209, 1210, 1251, 1259, 1264, 1308]) (by decide +kernel)

theorem c6891_0 : P.sumLeaves 24 7056384 448 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6891) (lo := 0) (len := 448) (W := 0) check rows elimOK (by decide) (by decide) cover6891 (by decide)
  decide +kernel

theorem contract6891_1 : P.leaf 30 110263 = 173568 := by
  exact leaf_contract_factors (k := 30) (b := 20) (H := 110263) (ss := [(18, 1, 524), (27, 1, 573), (29, 1, 916), (14, 1, 923), (8, 1, 580), (30, 1, 1251), (31, 1, 1210), (16, 1, 1265), (20, 1, 1657), (21, 1, 1658)]) (ids := [0, 1, 2, 3, 4, 7, 8, 9, 10, 11, 13, 15, 17, 20, 21, 24, 26, 5, 22, 23]) (cs := [2, 3, 4, 5, 6, 19, 1, 7, 8, 9, 10, 11, 1, 12, 1, 13, 1, 14, 1, 1, 15, 16, 20, 21, 17, 1, 18, 1, 1, 1]) (bs := [17, 3]) (W := 173568) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c6891_1 : P.sumLeaves 24 7056832 64 = 173568 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 110263) rows (by decide) (by decide)).symm.trans contract6891_1

theorem c6891_2 : P.sumLeaves 24 7056896 512 = 6938114 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6891) (lo := 512) (len := 512) (W := 6938114) check rows elimOK (by decide) (by decide) cover6891 (by decide)
  decide +kernel

theorem h6891 : P.leaf 34 6891 = 7111682 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(448, 0), (64, 173568), (512, 6938114)]) (.cons c6891_0 (.cons c6891_1 (.cons c6891_2 (.nil)))) (by decide) (by decide))

theorem cover6892 : P.CoversSplit 24 10 6892 0x8888000000000000000000000000000080800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000088000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 515, 522, 573, 859, 879, 916, 1202, 1210, 1251, 1259, 1264, 1308]) (by decide +kernel)

theorem c6892_0 : P.sumLeaves 24 7057408 1024 = 591656 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6892) (lo := 0) (len := 1024) (W := 591656) check rows elimOK (by decide) (by decide) cover6892 (by decide)
  decide +kernel

theorem h6892 : P.leaf 34 6892 = 591656 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 591656)]) (.cons c6892_0 (.nil)) (by decide) (by decide))

theorem cover6893 : P.CoversSplit 24 10 6893 0xcccc0000000000000000000000000000cccc00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 515, 522, 573, 879, 916, 1202, 1209, 1210, 1251, 1259, 1308]) (by decide +kernel)

theorem c6893_0 : P.sumLeaves 24 7058432 448 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6893) (lo := 0) (len := 448) (W := 0) check rows elimOK (by decide) (by decide) cover6893 (by decide)
  decide +kernel

theorem contract6893_1 : P.leaf 30 110295 = 162560 := by
  exact leaf_contract_factors (k := 30) (b := 20) (H := 110295) (ss := [(18, 1, 475), (27, 1, 522), (29, 1, 916), (14, 1, 923), (30, 1, 1251), (31, 1, 1210), (16, 1, 1265), (20, 1, 1657), (21, 1, 1658), (8, 1, 580)]) (ids := [0, 1, 2, 3, 4, 7, 8, 9, 10, 11, 13, 15, 17, 20, 21, 24, 26, 5, 22, 23]) (cs := [2, 3, 4, 5, 6, 19, 1, 7, 8, 9, 10, 11, 1, 12, 1, 13, 1, 14, 1, 1, 15, 16, 20, 21, 17, 1, 18, 1, 1, 1]) (bs := [17, 3]) (W := 162560) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c6893_1 : P.sumLeaves 24 7058880 64 = 162560 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 110295) rows (by decide) (by decide)).symm.trans contract6893_1

theorem c6893_2 : P.sumLeaves 24 7058944 512 = 3335840 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6893) (lo := 512) (len := 512) (W := 3335840) check rows elimOK (by decide) (by decide) cover6893 (by decide)
  decide +kernel

theorem h6893 : P.leaf 34 6893 = 3498400 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(448, 0), (64, 162560), (512, 3335840)]) (.cons c6893_0 (.cons c6893_1 (.cons c6893_2 (.nil)))) (by decide) (by decide))

theorem cover6894 : P.CoversSplit 24 10 6894 0xaaaa0000000000000000000000000000a0a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000088000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 515, 522, 573, 859, 879, 916, 1210, 1251, 1259, 1264, 1308]) (by decide +kernel)

theorem c6894_0 : P.sumLeaves 24 7059456 1024 = 3433432 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6894) (lo := 0) (len := 1024) (W := 3433432) check rows elimOK (by decide) (by decide) cover6894 (by decide)
  decide +kernel

theorem h6894 : P.leaf 34 6894 = 3433432 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 3433432)]) (.cons c6894_0 (.nil)) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(6630, 48), (6631, 48), (6636, 24), (6637, 48), (6639, 24), (6640, 24), (6641, 48), (6643, 24), (6644, 48), (6645, 48), (6646, 48), (6647, 48), (6652, 24), (6653, 48), (6655, 24), (6868, 24), (6869, 48), (6871, 24), (6876, 12), (6877, 24), (6879, 12), (6884, 48), (6885, 48), (6886, 48), (6887, 48), (6888, 48), (6889, 48), (6890, 48), (6891, 48), (6892, 48), (6893, 48), (6894, 48)]

theorem segOK : checkSeg 16 perms 6630 6895 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 6630 6895 1248 14078807952 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 14078807952)
    (SegSum.cons (w := 48) h6630 (SegSum.cons (w := 48) h6631 (SegSum.cons (w := 24) h6636 (SegSum.cons (w := 48) h6637 (SegSum.cons (w := 24) h6639 (SegSum.cons (w := 24) h6640 (SegSum.cons (w := 48) h6641 (SegSum.cons (w := 24) h6643 (SegSum.cons (w := 48) h6644 (SegSum.cons (w := 48) h6645 (SegSum.cons (w := 48) h6646 (SegSum.cons (w := 48) h6647 (SegSum.cons (w := 24) h6652 (SegSum.cons (w := 48) h6653 (SegSum.cons (w := 24) h6655 (SegSum.cons (w := 24) h6868 (SegSum.cons (w := 48) h6869 (SegSum.cons (w := 24) h6871 (SegSum.cons (w := 12) h6876 (SegSum.cons (w := 24) h6877 (SegSum.cons (w := 12) h6879 (SegSum.cons (w := 48) h6884 (SegSum.cons (w := 48) h6885 (SegSum.cons (w := 48) h6886 (SegSum.cons (w := 48) h6887 (SegSum.cons (w := 48) h6888 (SegSum.cons (w := 48) h6889 (SegSum.cons (w := 48) h6890 (SegSum.cons (w := 48) h6891 (SegSum.cons (w := 48) h6892 (SegSum.cons (w := 48) h6893 (SegSum.cons (w := 48) h6894 (show SegSum (P.leaf 34) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S4N1.C0.S42
