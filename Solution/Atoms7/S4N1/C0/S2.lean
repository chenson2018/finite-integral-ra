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

namespace RACert.S4N1.C0.S2

open RACert RACert.Problem

theorem cover236 : P.CoversSplit 24 10 236 0x8000000000000000000000000000000080000000000000000000000000000000000000001001000020000000100000000000000010010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 465, 473, 515, 522, 524, 566, 573, 858, 859, 865, 915, 1217, 1272, 1651]) (by decide +kernel)

theorem c236_0 : P.sumLeaves 24 241664 1024 = 39256 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 236) (lo := 0) (len := 1024) (W := 39256) check rows elimOK (by decide) (by decide) cover236 (by decide)
  decide +kernel

theorem h236 : P.leaf 34 236 = 39256 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 39256)]) (.cons c236_0 (.nil)) (by decide) (by decide))

theorem cover237 : P.CoversSplit 24 10 237 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [866]) (by decide +kernel)

theorem c237_0 : P.sumLeaves 24 242688 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 237) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover237 (by decide)
  decide +kernel

theorem h237 : P.leaf 34 237 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c237_0 (.nil)) (by decide) (by decide))

theorem cover238 : P.CoversSplit 24 10 238 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [872]) (by decide +kernel)

theorem c238_0 : P.sumLeaves 24 243712 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 238) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover238 (by decide)
  decide +kernel

theorem h238 : P.leaf 34 238 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c238_0 (.nil)) (by decide) (by decide))

theorem cover239 : P.CoversSplit 24 10 239 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [866]) (by decide +kernel)

theorem c239_0 : P.sumLeaves 24 244736 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 239) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover239 (by decide)
  decide +kernel

theorem h239 : P.leaf 34 239 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c239_0 (.nil)) (by decide) (by decide))

theorem cover254 : P.CoversSplit 24 10 254 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [866]) (by decide +kernel)

theorem c254_0 : P.sumLeaves 24 260096 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 254) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover254 (by decide)
  decide +kernel

theorem h254 : P.leaf 34 254 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c254_0 (.nil)) (by decide) (by decide))

theorem cover255 : P.CoversSplit 24 10 255 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem c255_0 : P.sumLeaves 24 261120 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 255) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover255 (by decide)
  decide +kernel

theorem h255 : P.leaf 34 255 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c255_0 (.nil)) (by decide) (by decide))

theorem cover492 : P.CoversSplit 24 10 492 0x8000000000004400000000000000000080000000000040000000000000000000000000001001110120200000101100000000000010011000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000010010000200000001000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 465, 473, 515, 522, 858, 859, 865, 915, 1217, 1266, 1609]) (by decide +kernel)

noncomputable def f492 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (503808 + i)

theorem c492_0 : rowSum f492 0 1024 = 197208 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 492) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover492 (by decide)
  decide +kernel

theorem sum492 : rowSum f492 0 1024 = 197208 :=
  c492_0

theorem h492 : P.leaf 34 492 = 197208 :=
  leaf_weighted (k := 24) (d := 10) (H := 492) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 492) (by decide) (by decide +kernel)) sum492

theorem cover493 : P.CoversSplit 24 10 493 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [866]) (by decide +kernel)

theorem c493_0 : P.sumLeaves 24 504832 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 493) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover493 (by decide)
  decide +kernel

theorem h493 : P.leaf 34 493 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c493_0 (.nil)) (by decide) (by decide))

theorem cover495 : P.CoversSplit 24 10 495 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [866]) (by decide +kernel)

theorem c495_0 : P.sumLeaves 24 506880 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 495) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover495 (by decide)
  decide +kernel

theorem h495 : P.leaf 34 495 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c495_0 (.nil)) (by decide) (by decide))

theorem cover511 : P.CoversSplit 24 10 511 0xfff8faf8faf8aaa8ffc8fac8fac8aa88fff8faf8faf8aaa8ffc8fac8fac8aa88ffc8fac888888888ccc8c8c888888888ffc8fac888888888ccc8c8c888888888fff8faf8faf8aaa8ffc8fac8fac8aa88fff8faf8faf8aaa8ffc8fac8fac8aa88ffc8fac888888888ccc8c8c888888888ffc8fac888888888ccc8c8c888888888 :=
  coversSplit check rows (by decide) (by decide) (xs := [858, 859, 865, 915, 1209, 1258]) (by decide +kernel)

noncomputable def f511 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (523264 + i)

theorem c511_0 : rowSum f511 0 301 = 15374244 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 511) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover511 (by decide)
  decide +kernel

theorem c511_1 : rowSum f511 301 209 = 41317056 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 511) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover511 (by decide)
  decide +kernel

theorem c511_2 : rowSum f511 510 514 = 53932314 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 511) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover511 (by decide)
  decide +kernel

theorem sum511 : rowSum f511 0 1024 = 110623614 :=
  rowSum_append (F := f511) (lo := 0) (n := 301) (m := 723) (A := 15374244) (B := 95249370) c511_0 (rowSum_append (F := f511) (lo := 301) (n := 209) (m := 514) (A := 41317056) (B := 53932314) c511_1 (c511_2))

theorem h511 : P.leaf 34 511 = 110623614 :=
  leaf_weighted (k := 24) (d := 10) (H := 511) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 511) (by decide) (by decide +kernel)) sum511

theorem cover531 : P.CoversSplit 24 10 531 0xffff00000000000000000000000000008000000000000000000000000000000000000000ffffffff00000000ffffffff0000000000000505000000000000050580000000000000000000000000000000ffffffff00000000ffffffff000000000000000000000000000000000033003300000000ffffffff00000000ffffffff :=
  coversProjected check rows (by decide) (by decide) (xs := [529, 1209, 1217, 1258, 1609]) (ps := [(8, [531, 580], [516, 572, 1217, 1609]), (14, [874, 923], [859, 915, 1217, 1609]), (16, [531], [1258]), (18, [580], [1210])]) (by decide +kernel)

theorem contract531_0 : P.leaf 30 8496 = 27909 := by
  exact leaf_contract_factors (k := 30) (b := 17) (H := 8496) (ss := [(31, 5, 467), (5, 0, 474), (12, 0, 479), (16, 1, 1216), (7, 1, 579), (18, 1, 579), (13, 1, 873), (17, 1, 1224), (9, 1, 587), (19, 1, 587), (15, 1, 881), (8, 0, 1266), (14, 0, 531)]) (ids := [0, 1, 2, 4, 8, 9, 20, 21, 22, 23, 24, 25, 26, 27, 28, 18, 19]) (cs := [2, 3, 4, 0, 5, 1, 0, 1, 6, 7, 0, 1, 0, 1, 1, 1, 1, 1, 17, 18, 8, 9, 10, 11, 12, 13, 14, 15, 16, 0]) (bs := [15, 2]) (W := 27909) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c531_0 : P.sumLeaves 24 543744 64 = 27909 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 8496) rows (by decide) (by decide)).symm.trans contract531_0

theorem contract531_1 : P.leaf 30 8497 = 42306 := by
  exact leaf_contract_factors (k := 30) (b := 17) (H := 8497) (ss := [(31, 5, 467), (5, 0, 474), (12, 0, 479), (16, 1, 1216), (7, 1, 579), (18, 1, 579), (13, 1, 873), (17, 1, 1224), (9, 1, 587), (19, 1, 587), (15, 1, 881), (8, 0, 1266), (14, 0, 531)]) (ids := [0, 1, 2, 4, 8, 9, 20, 21, 22, 23, 24, 25, 26, 27, 28, 18, 19]) (cs := [2, 3, 4, 0, 5, 1, 0, 1, 6, 7, 0, 1, 0, 1, 1, 1, 1, 1, 17, 18, 8, 9, 10, 11, 12, 13, 14, 15, 16, 0]) (bs := [15, 2]) (W := 42306) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c531_1 : P.sumLeaves 24 543808 64 = 42306 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 8497) rows (by decide) (by decide)).symm.trans contract531_1

theorem contract531_2 : P.leaf 30 8498 = 4221 := by
  apply (leaf_contract (k := 30) (b := 17) (H := 8498) (ss := [(31, 5, 467), (5, 0, 474), (12, 0, 479), (8, 1, 580), (18, 1, 580), (19, 1, 586), (9, 7, 601), (14, 1, 923), (15, 13, 951), (17, 16, 1301), (27, 0, 1609), (29, 0, 1609), (25, 1, 473)]) (ids := [0, 1, 2, 4, 5, 8, 9, 11, 14, 18, 19, 20, 21, 22, 24, 26, 28]) (cs := [2, 3, 4, 0, 5, 6, 1, 6, 7, 8, 0, 9, 1, 9, 10, 10, 1, 1, 11, 12, 13, 14, 15, 1, 16, 0, 17, 0, 18, 0]) check rows (by decide) (by decide +kernel) (by decide +kernel)).trans
  decide +kernel

theorem c531_2 : P.sumLeaves 24 543872 64 = 4221 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 8498) rows (by decide) (by decide)).symm.trans contract531_2

theorem c531_3 : P.sumLeaves 24 543936 64 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 531) (lo := 192) (len := 64) (W := 0) check rows elimOK (by decide) (by decide) cover531 (by decide)
  decide +kernel

theorem contract531_4 : P.leaf 30 8500 = 27909 := by
  exact leaf_contract_factors (k := 30) (b := 17) (H := 8500) (ss := [(31, 5, 467), (5, 1, 474), (12, 1, 479), (16, 0, 1258), (13, 0, 530), (18, 0, 530), (14, 0, 531), (7, 0, 873), (8, 0, 874), (17, 0, 1259), (15, 0, 538), (19, 0, 489), (9, 0, 881)]) (ids := [0, 1, 2, 4, 8, 9, 20, 21, 22, 23, 24, 25, 26, 27, 28, 18, 19]) (cs := [2, 3, 4, 1, 5, 0, 0, 0, 6, 7, 1, 0, 0, 0, 0, 0, 0, 0, 17, 18, 8, 9, 10, 11, 12, 13, 14, 15, 16, 1]) (bs := [15, 2]) (W := 27909) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c531_4 : P.sumLeaves 24 544000 64 = 27909 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 8500) rows (by decide) (by decide)).symm.trans contract531_4

theorem c531_5 : P.sumLeaves 24 544064 192 = 42372 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 531) (lo := 320) (len := 192) (W := 42372) check rows elimOK (by decide) (by decide) cover531 (by decide)
  decide +kernel

theorem contract531_6 : P.leaf 30 8504 = 1581 := by
  apply (leaf_contract (k := 30) (b := 16) (H := 8504) (ss := [(31, 5, 467), (5, 0, 474), (12, 0, 479), (8, 1, 531), (16, 1, 531), (17, 1, 537), (9, 7, 601), (14, 1, 874), (15, 13, 951), (26, 0, 1217), (28, 0, 1217), (30, 0, 1217), (24, 1, 465), (19, 18, 1651)]) (ids := [0, 1, 2, 4, 5, 8, 9, 11, 16, 18, 19, 20, 21, 23, 25, 27]) (cs := [2, 3, 4, 0, 5, 6, 1, 6, 7, 8, 0, 9, 1, 9, 1, 1, 10, 10, 11, 12, 13, 14, 1, 15, 0, 16, 0, 17, 0, 0]) check rows (by decide) (by decide +kernel) (by decide +kernel)).trans
  decide +kernel

theorem c531_6 : P.sumLeaves 24 544256 64 = 1581 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 8504) rows (by decide) (by decide)).symm.trans contract531_6

theorem contract531_7 : P.leaf 30 8505 = 2640 := by
  apply (leaf_contract (k := 30) (b := 16) (H := 8505) (ss := [(31, 5, 467), (5, 0, 474), (12, 0, 479), (8, 1, 531), (16, 1, 531), (17, 1, 537), (9, 7, 601), (14, 1, 874), (15, 13, 951), (26, 0, 1217), (28, 0, 1217), (30, 0, 1217), (24, 1, 465), (19, 18, 1651)]) (ids := [0, 1, 2, 4, 5, 8, 9, 11, 16, 18, 19, 20, 21, 23, 25, 27]) (cs := [2, 3, 4, 0, 5, 6, 1, 6, 7, 8, 0, 9, 1, 9, 1, 1, 10, 10, 11, 12, 13, 14, 1, 15, 0, 16, 0, 17, 0, 0]) check rows (by decide) (by decide +kernel) (by decide +kernel)).trans
  decide +kernel

theorem c531_7 : P.sumLeaves 24 544320 64 = 2640 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 8505) rows (by decide) (by decide)).symm.trans contract531_7

theorem c531_8 : P.sumLeaves 24 544384 384 = 79201 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 531) (lo := 640) (len := 384) (W := 79201) check rows elimOK (by decide) (by decide) cover531 (by decide)
  decide +kernel

theorem h531 : P.leaf 34 531 = 228139 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(64, 27909), (64, 42306), (64, 4221), (64, 0), (64, 27909), (192, 42372), (64, 1581), (64, 2640), (384, 79201)]) (.cons c531_0 (.cons c531_1 (.cons c531_2 (.cons c531_3 (.cons c531_4 (.cons c531_5 (.cons c531_6 (.cons c531_7 (.cons c531_8 (.nil)))))))))) (by decide) (by decide))

theorem h532 : P.leaf 34 532 = 37 := by
  apply (leaf_contract (k := 34) (b := 18) (H := 532) (ss := [(17, 10, 467), (33, 0, 468), (19, 11, 474), (35, 0, 475), (16, 3, 486), (18, 4, 487), (10, 3, 509), (34, 1, 523), (5, 1, 524), (31, 1, 529), (11, 4, 558), (12, 1, 866), (8, 0, 1266), (14, 0, 1266), (21, 0, 482), (20, 1, 433)]) (ids := [0, 1, 2, 4, 5, 7, 11, 13, 20, 21, 22, 23, 24, 25, 26, 27, 28, 30]) (cs := [2, 3, 4, 1, 5, 6, 0, 7, 3, 4, 1, 8, 0, 9, 3, 3, 4, 4, 1, 0, 10, 11, 12, 13, 14, 15, 16, 17, 18, 1, 19, 0, 1, 0]) check rows (by decide) (by decide +kernel) (by decide +kernel)).trans
  decide +kernel

theorem cover533 : P.CoversSplit 24 10 533 0x80000000000000000000000000000000842184210000000084218421000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 475, 516, 523, 529, 572, 860, 916, 1258]) (ps := [(8, [580], [516, 572]), (18, [580], [1210])]) (by decide +kernel)

theorem c533_0 : P.sumLeaves 24 545792 256 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 533) (lo := 0) (len := 256) (W := 0) check rows elimOK (by decide) (by decide) cover533 (by decide)
  decide +kernel

theorem contract533_1 : P.leaf 30 8532 = 20 := by
  apply (leaf_contract (k := 30) (b := 11) (H := 8532) (ss := [(31, 5, 468), (5, 1, 418), (19, 11, 474), (12, 1, 479), (18, 4, 487), (3, 1, 502), (11, 4, 558), (10, 1, 852), (16, 0, 1258), (4, 0, 530), (7, 0, 530), (13, 0, 530), (20, 1, 481), (8, 0, 531), (14, 0, 531), (21, 0, 482), (17, 0, 587), (9, 0, 538), (15, 0, 538)]) (ids := [0, 4, 20, 21, 22, 23, 24, 25, 26, 27, 28]) (cs := [2, 1, 0, 1, 3, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 4, 5, 6, 7, 8, 9, 10, 11, 12, 1]) check rows (by decide) (by decide +kernel) (by decide +kernel)).trans
  decide +kernel

theorem c533_1 : P.sumLeaves 24 546048 64 = 20 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 8532) rows (by decide) (by decide)).symm.trans contract533_1

theorem contract533_2 : P.leaf 30 8533 = 41 := by
  apply (leaf_contract (k := 30) (b := 18) (H := 8533) (ss := [(31, 5, 468), (5, 1, 418), (19, 11, 474), (12, 1, 479), (18, 4, 487), (3, 1, 502), (11, 4, 558), (10, 1, 852), (8, 0, 1266), (14, 0, 531), (21, 0, 482), (20, 1, 433)]) (ids := [0, 2, 4, 5, 7, 11, 13, 14, 15, 20, 21, 22, 23, 24, 25, 26, 27, 28]) (cs := [2, 1, 3, 1, 4, 5, 0, 6, 1, 3, 1, 7, 0, 8, 9, 10, 3, 3, 1, 0, 11, 12, 13, 14, 15, 16, 17, 18, 19, 1]) check rows (by decide) (by decide +kernel) (by decide +kernel)).trans
  decide +kernel

theorem c533_2 : P.sumLeaves 24 546112 64 = 41 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 8533) rows (by decide) (by decide)).symm.trans contract533_2

theorem c533_3 : P.sumLeaves 24 546176 640 = 128 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 533) (lo := 384) (len := 640) (W := 128) check rows elimOK (by decide) (by decide) cover533 (by decide)
  decide +kernel

theorem h533 : P.leaf 34 533 = 189 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(256, 0), (64, 20), (64, 41), (640, 128)]) (.cons c533_0 (.cons c533_1 (.cons c533_2 (.cons c533_3 (.nil))))) (by decide) (by decide))

theorem cover535 : P.CoversSplit 24 10 535 0x8421000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000842184210000000084218421000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [516, 523, 529, 572, 860, 916, 1209, 1258]) (ps := [(8, [531, 580], [516, 572]), (16, [531], [1258]), (18, [580], [1210])]) (by decide +kernel)

noncomputable def f535 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (547840 + i)

theorem c535_0 : rowSum f535 0 1024 = 2373 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 535) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover535 (by decide)
  decide +kernel

theorem sum535 : rowSum f535 0 1024 = 2373 :=
  c535_0

theorem h535 : P.leaf 34 535 = 2373 :=
  leaf_weighted (k := 24) (d := 10) (H := 535) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 535) (by decide) (by decide +kernel)) sum535

theorem cover540 : P.CoversSplit 24 10 540 0x8421000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000842184210000000084218421000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 508, 516, 523, 529, 572, 859, 915, 1209, 1258]) (ps := [(8, [531, 580], [516, 572]), (16, [531], [1258]), (18, [580], [1210])]) (by decide +kernel)

theorem c540_0 : P.sumLeaves 24 552960 256 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 540) (lo := 0) (len := 256) (W := 0) check rows elimOK (by decide) (by decide) cover540 (by decide)
  decide +kernel

theorem contract540_1 : P.leaf 30 8644 = 100 := by
  exact leaf_contract_factors (k := 30) (b := 11) (H := 8644) (ss := [(17, 10, 467), (16, 10, 468), (19, 11, 474), (18, 11, 475), (10, 3, 479), (11, 4, 480), (31, 1, 529), (3, 0, 1258), (4, 0, 409), (30, 25, 522), (7, 0, 1265), (13, 0, 1265), (8, 0, 1266), (14, 0, 628), (5, 1, 433), (20, 1, 481), (12, 1, 825), (9, 0, 1273), (15, 0, 636)]) (ids := [0, 4, 20, 21, 22, 23, 24, 25, 26, 27, 19]) (cs := [2, 0, 0, 1, 3, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 12, 4, 5, 6, 7, 8, 9, 10, 11, 7, 1]) (bs := [10, 1]) (W := 100) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c540_1 : P.sumLeaves 24 553216 64 = 100 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 8644) rows (by decide) (by decide)).symm.trans contract540_1

theorem c540_2 : P.sumLeaves 24 553280 640 = 276 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 540) (lo := 320) (len := 640) (W := 276) check rows elimOK (by decide) (by decide) cover540 (by decide)
  decide +kernel

theorem contract540_3 : P.leaf 30 8655 = 1536 := by
  exact leaf_contract_factors (k := 30) (b := 20) (H := 8655) (ss := [(10, 1, 467), (6, 1, 459), (11, 1, 459), (3, 1, 479), (2, 1, 410), (4, 1, 410), (5, 1, 425), (31, 1, 529), (12, 1, 810), (30, 1, 1209)]) (ids := [5, 6, 7, 11, 12, 13, 14, 15, 16, 17, 18, 19, 22, 23, 24, 25, 26, 27, 20, 21]) (cs := [1, 1, 1, 1, 1, 2, 3, 4, 1, 1, 1, 5, 6, 7, 8, 9, 10, 11, 12, 13, 20, 21, 14, 15, 16, 17, 18, 19, 1, 1]) (bs := [18, 2]) (W := 1536) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c540_3 : P.sumLeaves 24 553920 64 = 1536 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 8655) rows (by decide) (by decide)).symm.trans contract540_3

theorem h540 : P.leaf 34 540 = 1912 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(256, 0), (64, 100), (640, 276), (64, 1536)]) (.cons c540_0 (.cons c540_1 (.cons c540_2 (.cons c540_3 (.nil))))) (by decide) (by decide))

theorem cover541 : P.CoversSplit 24 10 541 0x8421000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000842184210000000084218421000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 516, 523, 529, 572, 859, 915, 1209, 1258]) (ps := [(8, [531, 580], [516, 572]), (16, [531], [1258]), (18, [580], [1210])]) (by decide +kernel)

theorem c541_0 : P.sumLeaves 24 553984 256 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 541) (lo := 0) (len := 256) (W := 0) check rows elimOK (by decide) (by decide) cover541 (by decide)
  decide +kernel

theorem contract541_1 : P.leaf 30 8660 = 180 := by
  exact leaf_contract_factors (k := 30) (b := 12) (H := 8660) (ss := [(19, 11, 474), (18, 11, 475), (11, 4, 480), (31, 1, 529), (16, 0, 1258), (3, 1, 419), (4, 0, 530), (10, 1, 459), (7, 0, 530), (13, 0, 530), (8, 0, 531), (14, 0, 531), (5, 1, 433), (20, 1, 481), (17, 0, 587), (9, 0, 538), (15, 0, 538), (12, 1, 825)]) (ids := [0, 4, 20, 21, 22, 23, 24, 25, 26, 27, 28, 19]) (cs := [2, 1, 0, 1, 3, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 13, 4, 5, 6, 7, 8, 9, 10, 11, 12, 1]) (bs := [11, 1]) (W := 180) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c541_1 : P.sumLeaves 24 554240 64 = 180 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 8660) rows (by decide) (by decide)).symm.trans contract541_1

theorem c541_2 : P.sumLeaves 24 554304 704 = 26358 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 541) (lo := 320) (len := 704) (W := 26358) check rows elimOK (by decide) (by decide) cover541 (by decide)
  decide +kernel

theorem h541 : P.leaf 34 541 = 26538 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(256, 0), (64, 180), (704, 26358)]) (.cons c541_0 (.cons c541_1 (.cons c541_2 (.nil)))) (by decide) (by decide))

theorem cover543 : P.CoversSplit 24 10 543 0x8421000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000842184210000000084218421000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [516, 523, 529, 572, 859, 915, 1209, 1258]) (ps := [(8, [531, 580], [516, 572]), (16, [531], [1258]), (18, [580], [1210])]) (by decide +kernel)

noncomputable def f543 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (556032 + i)

theorem c543_0 : rowSum f543 0 1024 = 91254 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 543) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover543 (by decide)
  decide +kernel

theorem sum543 : rowSum f543 0 1024 = 91254 :=
  c543_0

theorem h543 : P.leaf 34 543 = 91254 :=
  leaf_weighted (k := 24) (d := 10) (H := 543) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 543) (by decide) (by decide +kernel)) sum543

theorem h548 : P.leaf 34 548 = 0 := by
  exact leaf_contract_zero (ss := [(27, 6, 466), (33, 0, 468), (26, 6, 472), (19, 1, 474), (35, 0, 475), (13, 2, 479), (18, 4, 487), (14, 0, 510), (16, 3, 486), (4, 1, 558), (34, 12, 866), (31, 12, 872), (2, 1, 873), (5, 1, 404), (3, 1, 417), (12, 1, 951), (6, 1, 458), (10, 1, 458), (11, 1, 459), (28, 1, 465), (29, 1, 473), (30, 1, 515), (32, 1, 522), (7, 1, 579), (9, 1, 587), (15, 1, 930)]) (q := 958) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem h549 : P.leaf 34 549 = 192 := by
  exact leaf_contract_factors (k := 34) (b := 10) (H := 549) (ss := [(19, 1, 474), (35, 0, 475), (18, 4, 487), (4, 1, 558), (10, 1, 852), (12, 1, 852), (5, 1, 510), (11, 1, 817), (34, 1, 866), (27, 1, 473), (29, 1, 473), (2, 1, 410), (3, 1, 417), (32, 1, 522), (7, 1, 579), (9, 1, 587), (28, 1, 871), (31, 1, 860), (13, 1, 922), (15, 1, 930), (30, 1, 1209), (16, 1, 1265), (17, 1, 1273), (20, 1, 1657)]) (ids := [4, 6, 12, 19, 24, 31, 20, 21, 22, 23]) (cs := [1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 5, 8, 9, 10, 11, 6, 1, 1, 1, 1, 1, 1, 7, 1, 0]) (bs := [6, 4]) (W := 192) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem h550 : P.leaf 34 550 = 0 := by
  exact leaf_contract_zero (ss := [(33, 0, 468), (13, 2, 479), (14, 0, 510), (16, 3, 486), (19, 1, 523), (35, 0, 524), (34, 5, 475), (5, 1, 425), (12, 1, 480), (18, 4, 536), (4, 1, 551), (11, 1, 817), (31, 1, 872), (26, 1, 465), (28, 1, 465), (30, 1, 515), (2, 1, 873), (3, 1, 417), (7, 1, 579), (27, 1, 572), (9, 1, 587), (6, 1, 461), (10, 1, 810), (29, 1, 915), (8, 0, 923), (21, 0, 482), (20, 1, 433), (15, 1, 930)]) (q := 958) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem cover551 : P.CoversSplit 24 10 551 0xc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [515, 517, 522, 524, 572, 859, 860, 871, 872, 916, 1258, 1259]) (ps := [(14, [958], [915, 1266]), (18, [923], [1210])]) (by decide +kernel)

theorem c551_0 : P.sumLeaves 24 564224 1024 = 512 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 551) (lo := 0) (len := 1024) (W := 512) check rows elimOK (by decide) (by decide) cover551 (by decide)
  decide +kernel

theorem h551 : P.leaf 34 551 = 512 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 512)]) (.cons c551_0 (.nil)) (by decide) (by decide))

theorem cover552 : P.CoversSplit 24 10 552 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [558]) (by decide +kernel)

theorem c552_0 : P.sumLeaves 24 565248 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 552) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover552 (by decide)
  decide +kernel

theorem h552 : P.leaf 34 552 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c552_0 (.nil)) (by decide) (by decide))

theorem cover553 : P.CoversSplit 24 10 553 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [558]) (by decide +kernel)

theorem c553_0 : P.sumLeaves 24 566272 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 553) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover553 (by decide)
  decide +kernel

theorem h553 : P.leaf 34 553 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c553_0 (.nil)) (by decide) (by decide))

theorem cover554 : P.CoversSplit 24 10 554 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [566]) (by decide +kernel)

theorem c554_0 : P.sumLeaves 24 567296 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 554) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover554 (by decide)
  decide +kernel

theorem h554 : P.leaf 34 554 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c554_0 (.nil)) (by decide) (by decide))

theorem cover555 : P.CoversSplit 24 10 555 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [566]) (by decide +kernel)

theorem c555_0 : P.sumLeaves 24 568320 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 555) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover555 (by decide)
  decide +kernel

theorem h555 : P.leaf 34 555 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c555_0 (.nil)) (by decide) (by decide))

theorem cover556 : P.CoversSplit 24 10 556 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [566]) (by decide +kernel)

theorem c556_0 : P.sumLeaves 24 569344 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 556) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover556 (by decide)
  decide +kernel

theorem h556 : P.leaf 34 556 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c556_0 (.nil)) (by decide) (by decide))

theorem cover557 : P.CoversSplit 24 10 557 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [566]) (by decide +kernel)

theorem c557_0 : P.sumLeaves 24 570368 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 557) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover557 (by decide)
  decide +kernel

theorem h557 : P.leaf 34 557 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c557_0 (.nil)) (by decide) (by decide))

theorem cover558 : P.CoversSplit 24 10 558 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [566]) (by decide +kernel)

theorem c558_0 : P.sumLeaves 24 571392 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 558) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover558 (by decide)
  decide +kernel

theorem h558 : P.leaf 34 558 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c558_0 (.nil)) (by decide) (by decide))

theorem cover559 : P.CoversSplit 24 10 559 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [566]) (by decide +kernel)

theorem c559_0 : P.sumLeaves 24 572416 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 559) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover559 (by decide)
  decide +kernel

theorem h559 : P.leaf 34 559 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c559_0 (.nil)) (by decide) (by decide))

theorem h566 : P.leaf 34 566 = 0 := by
  exact leaf_contract_zero (ss := [(33, 0, 468), (13, 2, 479), (14, 0, 510), (16, 3, 486), (4, 1, 551), (5, 1, 551), (12, 1, 559), (31, 1, 566), (34, 1, 866), (35, 0, 874), (11, 1, 901), (8, 0, 923), (21, 0, 482), (20, 1, 433)]) (q := 958) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem cover567 : P.CoversSplit 24 10 567 0xc0000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [517, 529, 572, 859, 860, 867, 871, 916, 1209, 1251, 1258, 1259]) (ps := [(8, [531], [517, 572]), (14, [958], [915, 1266])]) (by decide +kernel)

theorem c567_0 : P.sumLeaves 24 580608 1024 = 10304 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 567) (lo := 0) (len := 1024) (W := 10304) check rows elimOK (by decide) (by decide) cover567 (by decide)
  decide +kernel

theorem h567 : P.leaf 34 567 = 10304 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 10304)]) (.cons c567_0 (.nil)) (by decide) (by decide))

theorem cover570 : P.CoversSplit 24 10 570 0xc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 467, 474, 517, 529, 572, 573, 859, 866, 915, 1209, 1251, 1258, 1259]) (ps := [(8, [531], [517, 572]), (14, [874, 880], [486])]) (by decide +kernel)

theorem c570_0 : P.sumLeaves 24 583680 1024 = 13296 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 570) (lo := 0) (len := 1024) (W := 13296) check rows elimOK (by decide) (by decide) cover570 (by decide)
  decide +kernel

theorem h570 : P.leaf 34 570 = 13296 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 13296)]) (.cons c570_0 (.nil)) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(236, 24), (237, 24), (238, 48), (239, 48), (254, 24), (255, 24), (492, 4), (493, 12), (495, 12), (511, 4), (531, 1), (532, 12), (533, 24), (535, 12), (540, 6), (541, 12), (543, 6), (548, 24), (549, 24), (550, 48), (551, 48), (552, 24), (553, 24), (554, 48), (555, 48), (556, 48), (557, 48), (558, 48), (559, 48), (566, 24), (567, 24), (570, 24)]

theorem segOK : checkSeg 16 perms 236 571 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 236 571 849 445960063 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 445960063)
    (SegSum.cons (w := 24) h236 (SegSum.cons (w := 24) h237 (SegSum.cons (w := 48) h238 (SegSum.cons (w := 48) h239 (SegSum.cons (w := 24) h254 (SegSum.cons (w := 24) h255 (SegSum.cons (w := 4) h492 (SegSum.cons (w := 12) h493 (SegSum.cons (w := 12) h495 (SegSum.cons (w := 4) h511 (SegSum.cons (w := 1) h531 (SegSum.cons (w := 12) h532 (SegSum.cons (w := 24) h533 (SegSum.cons (w := 12) h535 (SegSum.cons (w := 6) h540 (SegSum.cons (w := 12) h541 (SegSum.cons (w := 6) h543 (SegSum.cons (w := 24) h548 (SegSum.cons (w := 24) h549 (SegSum.cons (w := 48) h550 (SegSum.cons (w := 48) h551 (SegSum.cons (w := 24) h552 (SegSum.cons (w := 24) h553 (SegSum.cons (w := 48) h554 (SegSum.cons (w := 48) h555 (SegSum.cons (w := 48) h556 (SegSum.cons (w := 48) h557 (SegSum.cons (w := 48) h558 (SegSum.cons (w := 48) h559 (SegSum.cons (w := 24) h566 (SegSum.cons (w := 24) h567 (SegSum.cons (w := 24) h570 (show SegSum (P.leaf 34) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S4N1.C0.S2
