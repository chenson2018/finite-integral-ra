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

namespace RACert.S4N1.C0.S0

open RACert RACert.Problem

theorem cover0 : P.CoversSplit 24 10 0 0x900900000000dd0d0000000000000000900900000000dd0db0bb000000000000000000009009dd0db0bb0000b0bb0000000000000000dd0db0bb0000000000009009dd0d0000dd0d00000000000000009009dd0d0000dd0db0bb0000000000000000000000000000b0bb0000b0bb0000000000009009dd0db0bb0000b0bb0000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 522, 858, 865, 1208, 1209, 1217, 1258, 1609]) (by decide +kernel)

noncomputable def f0 (i : ℕ) := rowWeight keep4 twice4 i * P.leaf 24 (0 + i)

theorem c0_0 : rowSum f0 0 1023 = 102258 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 0) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover0 (by decide)
  decide +kernel

theorem c0_1 : rowSum f0 1023 1 = 2368 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 0) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover0 (by decide)
  decide +kernel

theorem sum0 : rowSum f0 0 1024 = 104626 :=
  rowSum_append (F := f0) (lo := 0) (n := 1023) (m := 1) (A := 102258) (B := 2368) c0_0 (c0_1)

theorem h0 : P.leaf 34 0 = 104626 :=
  leaf_weighted (k := 24) (d := 10) (H := 0) (keep := keep4) (twice := twice4) rows (by decide) (by decide) (bal4) (invRow4 (H := 0) (by decide) (by decide +kernel)) sum0

theorem cover1 : P.CoversSplit 24 10 1 0x800000000000cc000000000000000000800000000000cc000033000000000000000000008000cc000033000000330000000000000000cc0000330000000000008000cc000000cc0000000000000000008000cc000000cc00003300000000000000000000000000000033000000330000000000008000cc000033000000330000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 515, 522, 858, 865, 1208, 1209, 1217, 1258, 1609]) (by decide +kernel)

noncomputable def f1 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 24 (1024 + i)

theorem c1_0 : rowSum f1 0 1024 = 26960 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 1) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover1 (by decide)
  decide +kernel

theorem sum1 : rowSum f1 0 1024 = 26960 :=
  c1_0

theorem h1 : P.leaf 34 1 = 26960 :=
  leaf_weighted (k := 24) (d := 10) (H := 1) (keep := keep2) (twice := twice2) rows (by decide) (by decide) (bal2) (invRow2 (H := 1) (by decide) (by decide +kernel)) sum1

theorem cover3 : P.CoversSplit 24 10 3 0x8001000000000000000000000000000080010000000000000021000000000000000000008001040100000000002100000000000000000401000000000000000080010401000000000000000000000000800104010000000000210000000000000000000000000000000000000021000000000000800104010000000000210000 :=
  coversProjected check rows (by decide) (by decide) (xs := [417, 515, 522, 858, 865, 1209, 1217, 1258, 1609]) (ps := [(5, [467, 474], [467, 474])]) (by decide +kernel)

theorem h3 : P.leaf 34 3 = 6592 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 3) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 3) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 3) (weight := rowWeight keep0 twice0) (xs := [16, 21, 64, 74, 80, 95, 144, 149, 304, 309, 352, 362, 368, 383, 480, 490, 496, 511, 576, 586, 656, 661, 704, 714, 720, 735, 816, 821, 880, 895, 1008, 1023]) check rows elimOK (by decide) (by decide) cover3 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover4 : P.CoversSplit 24 10 4 0x800080000000040080000000000000000000000000000000000000000000000000000000000100010020000000010000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 468, 473, 475, 515, 516, 522, 572, 858, 860, 865, 916, 1208]) (by decide +kernel)

theorem h4 : P.leaf 34 4 = 11344 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 4) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 4) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 4) (weight := rowWeight keep0 twice0) (xs := [16, 53, 64, 80, 319, 330, 367, 383]) check rows elimOK (by decide) (by decide) cover4 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover33 : P.CoversSplit 24 10 33 0x8000c0000000000000000000000000008000c0000000000000000000000000000000000000000000003000000000000000000000000000000030000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 515, 517, 522, 524, 572, 858, 859, 865, 871, 1208]) (by decide +kernel)

theorem h33 : P.leaf 34 33 = 4372 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 33) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 33) (weight := fun _ => 1) (xs := [52, 53, 180, 181, 366, 367, 383, 494, 495, 511]) check rows elimOK (by decide) (by decide) cover33 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h5 : P.leaf 34 5 = 4372 :=
  orient4 (v := 33) (by decide) (by decide +kernel) h33

theorem cover16912 : P.CoversSplit 24 10 16912 0x8000800000000000800080000000000080000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000080008000000000000000000000000000800080000000000080008000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 508, 517, 528, 536, 578, 871, 921, 1210, 1259]) (by decide +kernel)

theorem h16912 : P.leaf 34 16912 = 4486 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 16912) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 16912) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 16912) (weight := rowWeight keep1 twice1) (xs := [303, 319, 367, 383, 495, 511, 831, 895, 943, 959, 1007, 1023]) check rows elimOK (by decide) (by decide) cover16912 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h7 : P.leaf 34 7 = 4486 :=
  orient32 (v := 16912) (by decide) (by decide +kernel) h16912

theorem cover12 : P.CoversSplit 24 10 12 0x8000000000000400000000000000000080000000000004008000000000000000000000000001000100200000000100000000000000000001002000000000000080008000000004000000000000000000800080000000040080000000000000000000000000000000002000000001000000000000000100010020000000010000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 515, 516, 522, 572, 858, 859, 865, 915, 1208, 1209, 1217, 1258, 1609]) (by decide +kernel)

theorem h12 : P.leaf 34 12 = 97192 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 12) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 12) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 12) (weight := rowWeight keep0 twice0) (xs := [16, 53, 64, 80, 144, 181, 319, 330, 367, 383, 458, 495, 511, 565, 576, 656, 693, 704, 720, 831, 842, 895, 970, 1023]) check rows elimOK (by decide) (by decide) cover12 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover13 : P.CoversSplit 24 10 13 0x8000000000000000000000000000000080000000000000000000000000000000000000000000000000210000000100000000000000000000002100000000000080008400000004000000000000000000800084000000040000000000000000000000000000000000002100000001000000000000000000000021000000010000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 515, 516, 522, 572, 858, 859, 865, 1208, 1209, 1217]) (ps := [(4, [480], [466])]) (by decide +kernel)

theorem h13 : P.leaf 34 13 = 55956 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 13) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 13) (weight := fun _ => 1) (xs := [16, 48, 53, 144, 176, 181, 330, 362, 367, 383, 458, 490, 495, 511, 560, 565, 656, 688, 693, 895, 1023]) check rows elimOK (by decide) (by decide) cover13 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover15 : P.CoversSplit 24 10 15 0x8001000000000401000000000000000080010000000004010021000000000000000000000001000100210000000100000000000000000001002100000000000080010401000004010000000000000000800104010000040100210000000000000000000000000000002100000001000000000000000100010021000000010000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 515, 516, 522, 572, 858, 865, 1209, 1217, 1258, 1609]) (by decide +kernel)

noncomputable def f15 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (15360 + i)

theorem c15_0 : rowSum f15 0 1024 = 62928 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 15) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover15 (by decide)
  decide +kernel

theorem sum15 : rowSum f15 0 1024 = 62928 :=
  c15_0

theorem h15 : P.leaf 34 15 = 62928 :=
  leaf_weighted (k := 24) (d := 10) (H := 15) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 15) (by decide) (by decide +kernel)) sum15

theorem cover19 : P.CoversSplit 24 10 19 0xfff800000000000000000000000000008888000000000000000000000000000000000000fff8faf800000000ffc8fac80000000000005050000000000000504088880000000000000000000000000000fff8faf800000000ffc8fac8000000000000000000000000000000003300320000000000fff8faf800000000ffc8fac8 :=
  coversProjected check rows (by decide) (by decide) (xs := [529, 858, 865, 1209, 1217, 1258, 1609]) (ps := [(8, [531, 580], [516, 572, 1217, 1609]), (16, [531], [1258]), (18, [580], [1210])]) (by decide +kernel)

noncomputable def f19 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (19456 + i)

theorem c19_0 : rowSum f19 0 1024 = 75171 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 19) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover19 (by decide)
  decide +kernel

theorem sum19 : rowSum f19 0 1024 = 75171 :=
  c19_0

theorem h19 : P.leaf 34 19 = 75171 :=
  leaf_weighted (k := 24) (d := 10) (H := 19) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 19) (by decide) (by decide +kernel)) sum19

theorem cover20 : P.CoversSplit 24 10 20 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem h20 : P.leaf 34 20 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 20) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 20) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover20 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover21 : P.CoversSplit 24 10 21 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem h21 : P.leaf 34 21 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 21) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 21) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover21 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover23 : P.CoversSplit 24 10 23 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem h23 : P.leaf 34 23 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 23) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 23) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover23 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover28 : P.CoversSplit 24 10 28 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [866]) (by decide +kernel)

theorem h28 : P.leaf 34 28 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 28) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 28) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover28 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover29 : P.CoversSplit 24 10 29 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [866]) (by decide +kernel)

theorem h29 : P.leaf 34 29 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 29) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 29) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover29 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover31 : P.CoversSplit 24 10 31 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [866]) (by decide +kernel)

theorem h31 : P.leaf 34 31 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 31) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 31) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover31 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h36 : P.leaf 34 36 = 0 := by
  exact leaf_contract_zero (ss := [(33, 0, 468), (19, 11, 474), (35, 0, 475), (13, 2, 479), (18, 4, 487), (14, 0, 510), (16, 3, 486), (30, 11, 523), (11, 4, 558), (12, 1, 951), (6, 1, 458), (10, 1, 458)]) (q := 958) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem cover37 : P.CoversSplit 24 10 37 0x8000c0000000000000000000000000008000c0000000000000000000000000000000000000000000003000000000000000000000000000000030000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 475, 515, 517, 522, 572, 858, 859, 860, 865, 871, 1208]) (by decide +kernel)

theorem h37 : P.leaf 34 37 = 15440 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 37) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 37) (weight := fun _ => 1) (xs := [52, 53, 180, 181, 366, 367, 383, 494, 495, 511]) check rows elimOK (by decide) (by decide) cover37 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover38 : P.CoversSplit 24 10 38 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [879]) (by decide +kernel)

theorem h38 : P.leaf 34 38 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 38) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 38) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover38 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover39 : P.CoversSplit 24 10 39 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [879]) (by decide +kernel)

theorem h39 : P.leaf 34 39 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 39) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 39) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover39 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover192 : P.CoversSplit 24 10 192 0x8008000000000000000000000000000000000000000000000000000000000000000000001001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 516, 522, 523, 536, 566, 573, 858, 865, 1202, 1208, 1258, 1272]) (by decide +kernel)

theorem h192 : P.leaf 34 192 = 2536 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 192) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 192) (weight := fun _ => 1) (xs := [720, 732, 1011, 1023]) check rows elimOK (by decide) (by decide) cover192 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h40 : P.leaf 34 40 = 2536 :=
  orient24 (v := 192) (by decide) (by decide +kernel) h192

theorem cover41 : P.CoversSplit 24 10 41 0x8000c000000000000000000000000000800080000000000000000000000000000000000000000000003000000000000000000000000000000020000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 474, 515, 517, 522, 572, 858, 859, 865, 871, 1208]) (by decide +kernel)

theorem h41 : P.leaf 34 41 = 24800 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 41) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 41) (weight := fun _ => 1) (xs := [53, 180, 181, 367, 383, 494, 495, 511]) check rows elimOK (by decide) (by decide) cover41 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover42 : P.CoversSplit 24 10 42 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [879]) (by decide +kernel)

theorem h42 : P.leaf 34 42 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 42) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 42) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover42 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover43 : P.CoversSplit 24 10 43 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [879]) (by decide +kernel)

theorem h43 : P.leaf 34 43 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 43) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 43) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover43 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover44 : P.CoversSplit 24 10 44 0x80008000000040000000000000000000800080000000000000000000000000000000000000000000002000000010000000000000000000000020000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 515, 517, 522, 524, 572, 858, 859, 915, 1208, 1301]) (by decide +kernel)

theorem h44 : P.leaf 34 44 = 14376 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 44) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 44) (weight := fun _ => 1) (xs := [53, 148, 181, 367, 383, 462, 495, 511]) check rows elimOK (by decide) (by decide) cover44 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover45 : P.CoversSplit 24 10 45 0x8000c000000000000000000000000000800080000000000000000000000000000000000000000000003000000000000000000000000000000020000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 515, 517, 522, 524, 572, 858, 859, 860, 865, 871, 1208]) (by decide +kernel)

theorem h45 : P.leaf 34 45 = 148024 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 45) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 45) (weight := fun _ => 1) (xs := [53, 180, 181, 367, 383, 494, 495, 511]) check rows elimOK (by decide) (by decide) cover45 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover46 : P.CoversSplit 24 10 46 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [879]) (by decide +kernel)

theorem h46 : P.leaf 34 46 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 46) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 46) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover46 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover47 : P.CoversSplit 24 10 47 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [879]) (by decide +kernel)

theorem h47 : P.leaf 34 47 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 47) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 47) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover47 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover54 : P.CoversSplit 24 10 54 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem h54 : P.leaf 34 54 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 54) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 54) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover54 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover55 : P.CoversSplit 24 10 55 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem h55 : P.leaf 34 55 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 55) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 55) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover55 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover58 : P.CoversSplit 24 10 58 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [866]) (by decide +kernel)

theorem h58 : P.leaf 34 58 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 58) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 58) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover58 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover59 : P.CoversSplit 24 10 59 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [866]) (by decide +kernel)

theorem h59 : P.leaf 34 59 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 59) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 59) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover59 (by decide) (by decide) (by decide +kernel)
  decide +kernel

def seg : List (ℕ × ℕ) := [(0, 1), (1, 4), (3, 6), (4, 12), (5, 24), (7, 12), (12, 6), (13, 12), (15, 6), (19, 4), (20, 24), (21, 48), (23, 24), (28, 12), (29, 24), (31, 12), (36, 24), (37, 24), (38, 48), (39, 48), (40, 24), (41, 24), (42, 48), (43, 48), (44, 48), (45, 48), (46, 48), (47, 48), (54, 24), (55, 24), (58, 24), (59, 24)]

theorem segOK : checkSeg 16 perms 0 60 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 0 60 807 11301606 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 11301606)
    (SegSum.cons (w := 1) h0 (SegSum.cons (w := 4) h1 (SegSum.cons (w := 6) h3 (SegSum.cons (w := 12) h4 (SegSum.cons (w := 24) h5 (SegSum.cons (w := 12) h7 (SegSum.cons (w := 6) h12 (SegSum.cons (w := 12) h13 (SegSum.cons (w := 6) h15 (SegSum.cons (w := 4) h19 (SegSum.cons (w := 24) h20 (SegSum.cons (w := 48) h21 (SegSum.cons (w := 24) h23 (SegSum.cons (w := 12) h28 (SegSum.cons (w := 24) h29 (SegSum.cons (w := 12) h31 (SegSum.cons (w := 24) h36 (SegSum.cons (w := 24) h37 (SegSum.cons (w := 48) h38 (SegSum.cons (w := 48) h39 (SegSum.cons (w := 24) h40 (SegSum.cons (w := 24) h41 (SegSum.cons (w := 48) h42 (SegSum.cons (w := 48) h43 (SegSum.cons (w := 48) h44 (SegSum.cons (w := 48) h45 (SegSum.cons (w := 48) h46 (SegSum.cons (w := 48) h47 (SegSum.cons (w := 24) h54 (SegSum.cons (w := 24) h55 (SegSum.cons (w := 24) h58 (SegSum.cons (w := 24) h59 (show SegSum (P.leaf 34) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S4N1.C0.S0
