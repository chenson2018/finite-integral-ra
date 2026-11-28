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

namespace RACert.S4N1.C0.S3

open RACert RACert.Problem

theorem cover723 : P.CoversSplit 24 10 723 0xf0000000000000000000000000000000a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c0000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [467, 475, 516, 573, 871, 921, 1210, 1251, 1259, 1264]) (by decide +kernel)

theorem h723 : P.leaf 34 723 = 29224 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 723) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 723) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 723) (weight := rowWeight keep1 twice1) (xs := [383, 510, 511, 893, 895, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover723 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h571 : P.leaf 34 571 = 29224 :=
  orient24 (v := 723) (by decide) (by decide +kernel) h723

theorem cover614 : P.CoversSplit 24 10 614 0x8000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 468, 475, 515, 522, 524, 572, 860, 872, 916, 1217, 1258]) (ps := [(14, [874, 880], [915, 1266])]) (by decide +kernel)

theorem h614 : P.leaf 34 614 = 5456 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 614) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 614) (weight := fun _ => 1) (xs := [511, 895, 1023]) check rows elimOK (by decide) (by decide) cover614 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h572 : P.leaf 34 572 = 5456 :=
  orient4 (v := 614) (by decide) (by decide +kernel) h614

theorem cover573 : P.CoversSplit 24 10 573 0xc0000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 517, 524, 529, 572, 860, 866, 871, 915, 1209, 1251, 1258, 1259]) (ps := [(8, [531], [572]), (14, [958], [915, 1266])]) (by decide +kernel)

theorem h573 : P.leaf 34 573 = 70528 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 573) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 573) (weight := fun _ => 1) (xs := [510, 511, 895, 1022, 1023]) check rows elimOK (by decide) (by decide) cover573 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover574 : P.CoversSplit 24 10 574 0xc4000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 517, 524, 529, 572, 859, 866, 915, 1209, 1251, 1258, 1259]) (ps := [(8, [531], [517, 572]), (14, [880], [859, 915, 1266])]) (by decide +kernel)

theorem h574 : P.leaf 34 574 = 87312 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 574) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 574) (weight := fun _ => 1) (xs := [510, 511, 895, 1018, 1022, 1023]) check rows elimOK (by decide) (by decide) cover574 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover575 : P.CoversSplit 24 10 575 0xc0000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [517, 524, 529, 572, 860, 866, 871, 915, 1209, 1251, 1258, 1259]) (ps := [(8, [531], [572]), (14, [958], [915, 1266])]) (by decide +kernel)

theorem h575 : P.leaf 34 575 = 252056 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 575) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 575) (weight := fun _ => 1) (xs := [510, 511, 895, 1022, 1023]) check rows elimOK (by decide) (by decide) cover575 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover620 : P.CoversSplit 24 10 620 0x8000000000000000000000000000000080000000000000000000000000000000000000000000000000000000001100110000000000000000000000000011001080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000011001100000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 508, 522, 572, 859, 872, 1209, 1217]) (ps := [(4, [558], [515]), (14, [874], [1266])]) (by decide +kernel)

theorem h620 : P.leaf 34 620 = 13211 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 620) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 620) (weight := fun _ => 1) (xs := [128, 132, 144, 148, 511, 516, 528, 532, 640, 644, 656, 660, 895, 1023]) check rows elimOK (by decide) (by decide) cover620 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3171 : P.CoversSplit 24 10 3171 0x8000000000000000000000000000000080000000000000000000000000000000000000000000000000210000002100000000000000000000002100000021000080000000000000000000000000000000800000000000000000000000000000000000000000000000002100000021000000000000000000000021000000200000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 515, 522, 523, 565, 572, 858, 865, 1209, 1217]) (by decide +kernel)

theorem h3171 : P.leaf 34 3171 = 110121 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 3171) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 3171) (weight := fun _ => 1) (xs := [21, 48, 53, 144, 149, 176, 181, 383, 511, 528, 533, 560, 565, 656, 661, 688, 693, 895, 1023]) check rows elimOK (by decide) (by decide) cover3171 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h621 : P.leaf 34 621 = 110121 :=
  orient5 (v := 3171) (by decide) (by decide +kernel) h3171

theorem cover622 : P.CoversSplit 24 10 622 0x8000000000000400000000000000000080000000000000000020000000000000000000000000000000000000000000000000000000000000000000000000000080000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 515, 522, 572, 859, 872, 915, 1217, 1258]) (ps := [(14, [874], [915, 1266])]) (by decide +kernel)

theorem h622 : P.leaf 34 622 = 86220 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 622) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 622) (weight := fun _ => 1) (xs := [458, 511, 821, 895, 970, 1023]) check rows elimOK (by decide) (by decide) cover622 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover623 : P.CoversSplit 24 10 623 0xcc0000000000c8000000000000000000cc0000000000c80000320000000000200000000000000000000000000000000000000000000000000000000000000000cc0000000000c8000000000000000000cc0000000000880000320000000000200000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [515, 522, 572, 859, 872, 915, 1209, 1258]) (ps := [(8, [1217], [572]), (14, [1217], [915, 1266]), (18, [524], [1210])]) (by decide +kernel)

theorem c623_0 : P.sumLeaves 24 637952 320 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 623) (lo := 0) (len := 320) (W := 0) check rows elimOK (by decide) (by decide) cover623 (by decide)
  decide +kernel

theorem contract623_1 : P.leaf 30 9973 = 0 := by
  exact leaf_contract_zero (ss := [(19, 1, 523), (18, 1, 524), (4, 1, 529), (27, 1, 572), (7, 1, 579), (9, 1, 587), (12, 1, 866), (29, 1, 915), (13, 1, 922), (15, 1, 930), (16, 1, 1265), (14, 0, 1266), (8, 1, 874)]) (q := 923) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c623_1 : P.sumLeaves 24 638272 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 9973) rows (by decide) (by decide)).symm.trans contract623_1

theorem c623_2 : P.sumLeaves 24 638336 640 = 960144 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 623) (lo := 384) (len := 640) (W := 960144) check rows elimOK (by decide) (by decide) cover623 (by decide)
  decide +kernel

theorem h623 : P.leaf 34 623 = 960144 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(320, 0), (64, 0), (640, 960144)]) (.cons c623_0 (.cons c623_1 (.cons c623_2 (.nil)))) (by decide) (by decide))

theorem cover638 : P.CoversSplit 24 10 638 0xc400c400440000000000000000000000c400c4004400000000310031001100000000000000000000000000000000000000000000000000000000000000000000c000c000440000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 572, 859, 866, 915, 1209, 1217, 1258]) (ps := [(14, [874], [859, 915, 1266])]) (by decide +kernel)

theorem h638 : P.leaf 34 638 = 902400 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 638) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 638) (weight := fun _ => 1) (xs := [474, 478, 494, 495, 510, 511, 784, 788, 800, 804, 805, 816, 820, 821, 858, 862, 874, 878, 879, 890, 894, 895, 986, 990, 1002, 1006, 1007, 1018, 1022, 1023]) check rows elimOK (by decide) (by decide) cover638 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3699 : P.CoversSplit 24 10 3699 0xcc00cc00cc0000000000000000000000cc00cc00cc00000000330033003300000000000000000000000000000000000000000000000000000000000000000000cc00cc00cc0000000000000000000000cc00cc008000000000330033002000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [474, 572, 915, 1209, 1217, 1258]) (ps := [(8, [1217], [572, 1266]), (14, [1217], [915, 1266])]) (by decide +kernel)

def k3699 : ℕ := 0x8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cefffffffffffffffffffffffffffffffff8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef
def t3699 : ℕ := 0x8ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce0000000000000000000000000000000008ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce

noncomputable def f3699 (i : ℕ) := rowWeight k3699 t3699 i * P.leaf 24 (3787776 + i)

theorem c3699_0 : rowSum f3699 0 256 = 0 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 3699) (keep := k3699) (twice := t3699) check rows elimOK (by decide) (by decide) cover3699 (by decide)
  decide +kernel

theorem contract3699_1 : P.leaf 30 59188 = 0 := by
  exact leaf_contract_zero (ss := [(16, 0, 1258), (27, 0, 1258), (7, 0, 572), (8, 0, 572), (6, 1, 482), (14, 1, 482), (9, 0, 573), (13, 0, 579), (18, 1, 481)]) (q := 580) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c3699_1 : rowSum f3699 256 64 = 0 :=
  (rowSum_unit_block (P := P) (keep := k3699) (twice := t3699) (by decide +kernel)).trans ((leaf_eq_inner (k := 24) (d := 6) (H := 59188) rows (by decide) (by decide)).symm.trans contract3699_1)

theorem contract3699_2 : P.leaf 30 59189 = 0 := by
  exact leaf_contract_zero (ss := [(27, 1, 572), (29, 1, 915), (8, 0, 1266), (6, 1, 482), (14, 1, 482)]) (q := 580) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c3699_2 : rowSum f3699 320 64 = 0 :=
  (rowSum_unit_block (P := P) (keep := k3699) (twice := t3699) (by decide +kernel)).trans ((leaf_eq_inner (k := 24) (d := 6) (H := 59189) rows (by decide) (by decide)).symm.trans contract3699_2)

theorem c3699_3 : rowSum f3699 384 640 = 3691076 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 3699) (keep := k3699) (twice := t3699) check rows elimOK (by decide) (by decide) cover3699 (by decide)
  decide +kernel

theorem sum3699 : rowSum f3699 0 1024 = 3691076 :=
  rowSum_append (F := f3699) (lo := 0) (n := 256) (m := 768) (A := 0) (B := 3691076) c3699_0 (rowSum_append (F := f3699) (lo := 256) (n := 64) (m := 704) (A := 0) (B := 3691076) c3699_1 (rowSum_append (F := f3699) (lo := 320) (n := 64) (m := 640) (A := 0) (B := 3691076) c3699_2 (c3699_3)))

theorem h3699 : P.leaf 34 3699 = 3691076 :=
  leaf_weighted (k := 24) (d := 10) (H := 3699) (keep := k3699) (twice := t3699) rows (by decide) (by decide) (balancedRows_of_check (by decide +kernel)) (invRow2 (H := 3699) (by decide) (by decide +kernel)) sum3699

theorem h639 : P.leaf 34 639 = 3691076 :=
  orient5 (v := 3699) (by decide) (by decide +kernel) h3699

theorem h676 : P.leaf 34 676 = 0 := by
  exact leaf_contract_zero (ss := [(27, 6, 466), (33, 0, 468), (26, 6, 472), (35, 0, 475), (13, 2, 479), (14, 0, 510), (16, 3, 486), (18, 4, 487), (34, 12, 866), (31, 12, 872), (12, 1, 951), (6, 1, 458), (10, 1, 458), (11, 1, 459), (28, 1, 465), (29, 1, 473), (30, 1, 515), (32, 1, 522)]) (q := 958) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem h677 : P.leaf 34 677 = 0 := by
  exact leaf_contract_zero (ss := [(35, 0, 475), (13, 2, 480), (16, 3, 529), (14, 0, 559), (18, 4, 487), (12, 5, 510), (33, 0, 566), (31, 5, 468), (5, 1, 811), (10, 1, 852), (34, 1, 867), (27, 1, 473), (29, 1, 473), (32, 1, 522), (28, 1, 871), (8, 0, 874), (21, 0, 482), (20, 1, 433)]) (q := 958) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem h679 : P.leaf 34 679 = 0 := by
  exact leaf_contract_zero (ss := [(35, 0, 524), (34, 5, 475), (16, 3, 529), (33, 0, 566), (31, 5, 468), (18, 4, 536), (10, 1, 852), (12, 1, 852), (5, 1, 510), (28, 1, 871), (11, 1, 901), (29, 1, 921), (3, 1, 958), (13, 1, 873), (4, 1, 922), (14, 1, 958), (8, 1, 531), (26, 1, 517), (27, 1, 573), (17, 1, 880), (19, 1, 929), (30, 1, 1209), (32, 1, 1258)]) (q := 1266) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem cover708 : P.CoversSplit 24 10 708 0x8000000000000000000000000000000000000000000000000000000000000000000000001010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 468, 473, 475, 508, 515, 516, 522, 536, 566, 573, 860, 872]) (by decide +kernel)

theorem h708 : P.leaf 34 708 = 2880 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 708) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 708) (weight := fun _ => 1) (xs := [724, 732, 1023]) check rows elimOK (by decide) (by decide) cover708 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h680 : P.leaf 34 680 = 2880 :=
  orient4 (v := 708) (by decide) (by decide +kernel) h708

theorem cover681 : P.CoversSplit 24 10 681 0xc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 515, 517, 522, 524, 566, 573, 871, 879, 1209]) (by decide +kernel)

theorem h681 : P.leaf 34 681 = 9024 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 681) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 681) (weight := fun _ => 1) (xs := [1022, 1023]) check rows elimOK (by decide) (by decide) cover681 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover683 : P.CoversSplit 24 10 683 0xf000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 517, 522, 524, 566, 573, 871, 879, 921, 1209, 1258]) (by decide +kernel)

theorem h683 : P.leaf 34 683 = 40416 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 683) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 683) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 683) (weight := rowWeight keep0 twice0) (xs := [1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover683 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover684 : P.CoversSplit 24 10 684 0x8000000000000000000000000000000000000000000000000000000000000000000000001000100000000000100010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 508, 515, 517, 522, 524, 566, 573, 859, 872]) (by decide +kernel)

theorem h684 : P.leaf 34 684 = 16912 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 684) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 684) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 684) (weight := rowWeight keep0 twice0) (xs := [652, 668, 716, 732, 1023]) check rows elimOK (by decide) (by decide) cover684 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover685 : P.CoversSplit 24 10 685 0xc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 515, 517, 522, 524, 566, 573, 860, 871, 879, 1209]) (by decide +kernel)

theorem h685 : P.leaf 34 685 = 94336 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 685) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 685) (weight := fun _ => 1) (xs := [1022, 1023]) check rows elimOK (by decide) (by decide) cover685 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover687 : P.CoversSplit 24 10 687 0xf000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 517, 522, 524, 566, 573, 860, 871, 879, 916, 921, 1209, 1258]) (by decide +kernel)

theorem h687 : P.leaf 34 687 = 395888 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 687) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 687) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 687) (weight := rowWeight keep0 twice0) (xs := [1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover687 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover695 : P.CoversSplit 24 10 695 0xf0000000000000000000000000000000a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [517, 573, 859, 860, 867, 871, 916, 921, 1209, 1251, 1259, 1264, 1308]) (ps := [(8, [531, 580], [517, 573])]) (by decide +kernel)

theorem h695 : P.leaf 34 695 = 51440 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 695) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 695) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 695) (weight := rowWeight keep0 twice0) (xs := [510, 511, 893, 895, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover695 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover710 : P.CoversSplit 24 10 710 0xa000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 468, 475, 515, 516, 522, 536, 573, 860, 872, 879, 916, 921, 1258]) (ps := [(14, [874], [479])]) (by decide +kernel)

theorem h710 : P.leaf 34 710 = 7184 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 710) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 710) (weight := fun _ => 1) (xs := [1021, 1023]) check rows elimOK (by decide) (by decide) cover710 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h696 : P.leaf 34 696 = 7184 :=
  orient4 (v := 710) (by decide) (by decide +kernel) h710

theorem cover711 : P.CoversSplit 24 10 711 0xf000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [475, 515, 516, 522, 536, 566, 573, 860, 871, 879, 916, 921, 1209, 1258]) (ps := [(14, [965], [1266])]) (by decide +kernel)

theorem h711 : P.leaf 34 711 = 40832 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 711) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 711) (weight := fun _ => 1) (xs := [1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover711 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h697 : P.leaf 34 697 = 40832 :=
  orient4 (v := 711) (by decide) (by decide +kernel) h711

theorem cover699 : P.CoversSplit 24 10 699 0xf0000000000000000000000000000000a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [517, 524, 566, 573, 871, 879, 921, 1209, 1251, 1259, 1264, 1308]) (by decide +kernel)

theorem h699 : P.leaf 34 699 = 87104 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 699) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 699) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 699) (weight := rowWeight keep0 twice0) (xs := [510, 511, 893, 895, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover699 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover742 : P.CoversSplit 24 10 742 0xa0000000000000000000000000000000a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 468, 475, 515, 522, 524, 573, 860, 872, 916, 921, 1217, 1258, 1308]) (ps := [(16, [958], [1258])]) (by decide +kernel)

theorem h742 : P.leaf 34 742 = 49152 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 742) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 742) (weight := fun _ => 1) (xs := [511, 893, 895, 1021, 1023]) check rows elimOK (by decide) (by decide) cover742 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h700 : P.leaf 34 700 = 49152 :=
  orient4 (v := 742) (by decide) (by decide +kernel) h742

theorem cover701 : P.CoversSplit 24 10 701 0xf0300000000000000000000000000000a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 517, 524, 566, 573, 860, 867, 871, 915, 1209, 1251, 1259, 1264, 1308]) (ps := [(8, [580], [573]), (14, [874], [915])]) (by decide +kernel)

theorem h701 : P.leaf 34 701 = 286976 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 701) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 701) (weight := fun _ => 1) (xs := [510, 511, 893, 895, 1012, 1013, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover701 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover703 : P.CoversSplit 24 10 703 0xf0000000000000000000000000000000a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [517, 524, 566, 573, 860, 867, 871, 916, 921, 1209, 1251, 1259, 1264, 1308]) (by decide +kernel)

theorem h703 : P.leaf 34 703 = 922928 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 703) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 703) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 703) (weight := rowWeight keep0 twice0) (xs := [510, 511, 893, 895, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover703 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover716 : P.CoversSplit 24 10 716 0x8000000000000000000000000000000000000000000000000000000000000000000000001111101000000000110010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 508, 515, 516, 522, 536, 573, 859, 872, 1301]) (ps := [(14, [874], [1266])]) (by decide +kernel)

theorem h716 : P.leaf 34 716 = 53236 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 716) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 716) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 716) (weight := rowWeight keep1 twice1) (xs := [652, 664, 668, 708, 716, 720, 724, 728, 732, 1023]) check rows elimOK (by decide) (by decide) cover716 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover717 : P.CoversSplit 24 10 717 0xc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 515, 516, 522, 536, 573, 859, 860, 871, 879, 1209]) (ps := [(14, [929], [1266])]) (by decide +kernel)

theorem h717 : P.leaf 34 717 = 74368 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 717) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 717) (weight := fun _ => 1) (xs := [1022, 1023]) check rows elimOK (by decide) (by decide) cover717 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover719 : P.CoversSplit 24 10 719 0xf000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [515, 516, 522, 536, 573, 859, 860, 871, 879, 916, 921, 1209, 1258]) (ps := [(14, [958], [1266])]) (by decide +kernel)

theorem h719 : P.leaf 34 719 = 447288 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 719) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 719) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 719) (weight := rowWeight keep1 twice1) (xs := [1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover719 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover732 : P.CoversSplit 24 10 732 0xf4210000000000000000000000000000a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 508, 516, 536, 573, 859, 866, 872, 915, 1210, 1251, 1259, 1264]) (ps := [(14, [874, 880], [859, 915, 1266])]) (by decide +kernel)

theorem h732 : P.leaf 34 732 = 62140 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 732) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 732) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 732) (weight := rowWeight keep1 twice1) (xs := [510, 511, 893, 895, 1008, 1013, 1018, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover732 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover733 : P.CoversSplit 24 10 733 0xf0300000000000000000000000000000a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 516, 536, 573, 859, 860, 867, 871, 915, 1210, 1251, 1259, 1264]) (ps := [(14, [880, 929], [915, 1266])]) (by decide +kernel)

theorem h733 : P.leaf 34 733 = 313392 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 733) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 733) (weight := fun _ => 1) (xs := [510, 511, 893, 895, 1012, 1013, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover733 (by decide) (by decide) (by decide +kernel)
  decide +kernel

def seg : List (ℕ × ℕ) := [(571, 24), (572, 48), (573, 48), (574, 48), (575, 48), (620, 12), (621, 12), (622, 24), (623, 24), (638, 12), (639, 12), (676, 8), (677, 24), (679, 24), (680, 24), (681, 48), (683, 24), (684, 24), (685, 48), (687, 24), (695, 8), (696, 24), (697, 48), (699, 24), (700, 24), (701, 48), (703, 24), (716, 24), (717, 48), (719, 24), (732, 24), (733, 48)]

theorem segOK : checkSeg 16 perms 571 735 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 571 735 928 192115840 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 192115840)
    (SegSum.cons (w := 24) h571 (SegSum.cons (w := 48) h572 (SegSum.cons (w := 48) h573 (SegSum.cons (w := 48) h574 (SegSum.cons (w := 48) h575 (SegSum.cons (w := 12) h620 (SegSum.cons (w := 12) h621 (SegSum.cons (w := 24) h622 (SegSum.cons (w := 24) h623 (SegSum.cons (w := 12) h638 (SegSum.cons (w := 12) h639 (SegSum.cons (w := 8) h676 (SegSum.cons (w := 24) h677 (SegSum.cons (w := 24) h679 (SegSum.cons (w := 24) h680 (SegSum.cons (w := 48) h681 (SegSum.cons (w := 24) h683 (SegSum.cons (w := 24) h684 (SegSum.cons (w := 48) h685 (SegSum.cons (w := 24) h687 (SegSum.cons (w := 8) h695 (SegSum.cons (w := 24) h696 (SegSum.cons (w := 48) h697 (SegSum.cons (w := 24) h699 (SegSum.cons (w := 24) h700 (SegSum.cons (w := 48) h701 (SegSum.cons (w := 24) h703 (SegSum.cons (w := 24) h716 (SegSum.cons (w := 48) h717 (SegSum.cons (w := 24) h719 (SegSum.cons (w := 24) h732 (SegSum.cons (w := 48) h733 (show SegSum (P.leaf 34) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S4N1.C0.S3
