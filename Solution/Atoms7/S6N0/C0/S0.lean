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

namespace RACert.S6N0.C0.S0

open RACert RACert.Problem

theorem cover0 : P.CoversSplit 26 10 0 0x9009000000009009000000000000000000000000000000009009000000009009dd0ddd0d0000dd0ddd0ddd0d0000dd0d0000000000000000dd0ddd0d0000dd0db0bb0000b0bbb0bb0000000000000000b0bb0000b0bbb0bbb0bb0000b0bbb0bb0000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [629, 636, 972, 979, 1315, 1322, 1658, 1665, 2008]) (by decide +kernel)

noncomputable def f0 (i : ℕ) := rowWeight keep10 twice10 i * P.leaf 26 (0 + i)

theorem c0_0 : rowSum f0 0 1024 = 299712 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 0) (keep := keep10) (twice := twice10) check rows elimOK (by decide) (by decide) cover0 (by decide)
  decide +kernel

theorem sum0 : rowSum f0 0 1024 = 299712 :=
  c0_0

theorem h0 : P.leaf 36 0 = 299712 :=
  leaf_weighted (k := 26) (d := 10) (H := 0) (keep := keep10) (twice := twice10) rows (by decide) (by decide) (bal10) (invRow10 (H := 0) (by decide) (by decide +kernel)) sum0

theorem cover1 : P.CoversSplit 26 10 1 0x8000000000000001000000000000000000000000000000008000000000000001800004000000000180000400000000010000000000000000800004000000000180000000002000010000000000000000800000000020000180000000002000010000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 530, 538, 629, 636, 873, 881, 1658, 1665, 2008]) (by decide +kernel)

theorem h1 : P.leaf 36 1 = 68864 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 1) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 1) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 1) (weight := rowWeight keep0 twice0) (xs := [256, 277, 319, 320, 341, 383, 448, 469, 511, 512, 554, 575, 640, 682, 703, 704, 746, 767, 768, 831, 960, 1023]) check rows elimOK (by decide) (by decide) cover1 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3 : P.CoversSplit 26 10 3 0x8000000000000000000000000000000000000000000000000000000000000001800000000000000000000400000000000000000000000000000000000000000180000000000000000000000000000000000000000020000000000000000000010000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 530, 538, 579, 587, 629, 636, 873, 881, 2008]) (by decide +kernel)

theorem h3 : P.leaf 36 3 = 18112 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 3) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 3) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3) (weight := rowWeight keep0 twice0) (xs := [256, 341, 511, 512, 682, 767, 768, 1023]) check rows elimOK (by decide) (by decide) cover3 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover7 : P.CoversSplit 26 10 7 0x8000000000000000000000000000000000000000000000000000000000000000840004000000000004000400000000000000000000000000000000000000000000000000000000000000000000000000000000000021000100000000000100010000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 538, 579, 587, 629, 636, 873, 881, 2008]) (by decide +kernel)

theorem h7 : P.leaf 36 7 = 15168 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 7) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 7) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 7) (weight := rowWeight keep1 twice1) (xs := [256, 272, 320, 336, 341, 682, 698, 746, 762, 767, 1023]) check rows elimOK (by decide) (by decide) cover7 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover15 : P.CoversSplit 26 10 15 0x8001000000000001000000000000000000000000000000000001000000000001040104010000000104010401000000010000000000000000000100010000000100210000002100010000000000000000002100000021000100010000000100010000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 538, 579, 587, 629, 636, 873, 881, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h15 : P.leaf 36 15 = 38800 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 15) (keep := keep2) (twice := twice2) rows (by decide) (by decide) bal2 (invRow2 (H := 15) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 15) (weight := rowWeight keep2 twice2) (xs := [256, 272, 304, 320, 336, 341, 368, 373, 448, 464, 469, 496, 501, 512, 544, 560, 640, 672, 682, 688, 698, 704, 736, 746, 752, 762, 768, 816, 960, 1008, 1023]) check rows elimOK (by decide) (by decide) cover15 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover19 : P.CoversSplit 26 10 19 0x8000000000000000000000000000000000000000000000000000000000000001800000000000000000000400000000000000000000000000000000000000000180000000000000000000000000000000000000000020000000000000000000010000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 530, 538, 579, 587, 629, 636, 873, 881, 2008]) (by decide +kernel)

theorem h19 : P.leaf 36 19 = 261344 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 19) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 19) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 19) (weight := rowWeight keep0 twice0) (xs := [256, 341, 511, 512, 682, 767, 768, 1023]) check rows elimOK (by decide) (by decide) cover19 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover20 : P.CoversSplit 26 10 20 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [866]) (by decide +kernel)

theorem h20 : P.leaf 36 20 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 20) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 20) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover20 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover21 : P.CoversSplit 26 10 21 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [866]) (by decide +kernel)

theorem h21 : P.leaf 36 21 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 21) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 21) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover21 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover23 : P.CoversSplit 26 10 23 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [866]) (by decide +kernel)

theorem h23 : P.leaf 36 23 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 23) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 23) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover23 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover28 : P.CoversSplit 26 10 28 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [866]) (by decide +kernel)

theorem h28 : P.leaf 36 28 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 28) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 28) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover28 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover29 : P.CoversSplit 26 10 29 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [866]) (by decide +kernel)

theorem h29 : P.leaf 36 29 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 29) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 29) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover29 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover31 : P.CoversSplit 26 10 31 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [866]) (by decide +kernel)

theorem h31 : P.leaf 36 31 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 31) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 31) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover31 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover54 : P.CoversSplit 26 10 54 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [866]) (by decide +kernel)

theorem h54 : P.leaf 36 54 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 54) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 54) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover54 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover55 : P.CoversSplit 26 10 55 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [866]) (by decide +kernel)

theorem h55 : P.leaf 36 55 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 55) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 55) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover55 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover58 : P.CoversSplit 26 10 58 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem h58 : P.leaf 36 58 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 58) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 58) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover58 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover59 : P.CoversSplit 26 10 59 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem h59 : P.leaf 36 59 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 59) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 59) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover59 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover62 : P.CoversSplit 26 10 62 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [866]) (by decide +kernel)

theorem h62 : P.leaf 36 62 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 62) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 62) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover62 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover63 : P.CoversSplit 26 10 63 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [866]) (by decide +kernel)

theorem h63 : P.leaf 36 63 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 63) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 63) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover63 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover126 : P.CoversSplit 26 10 126 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [866]) (by decide +kernel)

theorem h126 : P.leaf 36 126 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 126) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 126) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover126 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover127 : P.CoversSplit 26 10 127 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [866]) (by decide +kernel)

theorem h127 : P.leaf 36 127 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 127) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 127) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover127 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover183 : P.CoversSplit 26 10 183 0x8000000000000000000000000000000000000000000000000000000000000000cc00c80000000000c8008800000000000000000000000000000000000000000000000000000000000000000000000000000000000033003200000000003200220000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 538, 587, 629, 636, 873, 881, 922, 972, 1265, 1315, 1658, 2008]) (by decide +kernel)

theorem h183 : P.leaf 36 183 = 2889796 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 183) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 183) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 183) (weight := rowWeight keep1 twice1) (xs := [257, 261, 273, 276, 277, 321, 324, 325, 336, 337, 340, 341, 683, 687, 699, 702, 703, 747, 750, 751, 762, 763, 766, 767, 1023]) check rows elimOK (by decide) (by decide) cover183 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover184 : P.CoversSplit 26 10 184 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem h184 : P.leaf 36 184 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 184) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 184) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover184 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover185 : P.CoversSplit 26 10 185 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [866]) (by decide +kernel)

theorem h185 : P.leaf 36 185 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 185) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 185) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover185 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover187 : P.CoversSplit 26 10 187 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [866]) (by decide +kernel)

theorem h187 : P.leaf 36 187 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 187) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 187) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover187 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover191 : P.CoversSplit 26 10 191 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem h191 : P.leaf 36 191 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 191) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 191) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover191 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover207 : P.CoversSplit 26 10 207 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [866]) (by decide +kernel)

theorem h207 : P.leaf 36 207 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 207) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 207) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover207 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover220 : P.CoversSplit 26 10 220 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [866]) (by decide +kernel)

theorem h220 : P.leaf 36 220 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 220) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 220) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover220 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover221 : P.CoversSplit 26 10 221 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem h221 : P.leaf 36 221 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 221) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 221) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover221 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover223 : P.CoversSplit 26 10 223 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem h223 : P.leaf 36 223 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 223) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 223) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover223 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover254 : P.CoversSplit 26 10 254 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [866]) (by decide +kernel)

theorem h254 : P.leaf 36 254 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 254) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 254) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover254 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover255 : P.CoversSplit 26 10 255 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem h255 : P.leaf 36 255 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 255) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 255) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover255 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover495 : P.CoversSplit 26 10 495 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [866]) (by decide +kernel)

theorem h495 : P.leaf 36 495 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 495) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 495) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover495 (by decide) (by decide) (by decide +kernel)
  decide +kernel

def seg : List (ℕ × ℕ) := [(0, 1), (1, 20), (3, 90), (7, 60), (15, 15), (19, 60), (20, 90), (21, 360), (23, 360), (28, 180), (29, 360), (31, 180), (54, 90), (55, 180), (58, 360), (59, 360), (62, 360), (63, 360), (126, 60), (127, 60), (183, 30), (184, 60), (185, 360), (187, 360), (191, 120), (207, 90), (220, 72), (221, 360), (223, 360), (254, 180), (255, 180), (495, 90)]

theorem segOK : checkSeg 20 perms 0 511 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 0 511 5868 107173672 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 107173672)
    (SegSum.cons (w := 1) h0 (SegSum.cons (w := 20) h1 (SegSum.cons (w := 90) h3 (SegSum.cons (w := 60) h7 (SegSum.cons (w := 15) h15 (SegSum.cons (w := 60) h19 (SegSum.cons (w := 90) h20 (SegSum.cons (w := 360) h21 (SegSum.cons (w := 360) h23 (SegSum.cons (w := 180) h28 (SegSum.cons (w := 360) h29 (SegSum.cons (w := 180) h31 (SegSum.cons (w := 90) h54 (SegSum.cons (w := 180) h55 (SegSum.cons (w := 360) h58 (SegSum.cons (w := 360) h59 (SegSum.cons (w := 360) h62 (SegSum.cons (w := 360) h63 (SegSum.cons (w := 60) h126 (SegSum.cons (w := 60) h127 (SegSum.cons (w := 30) h183 (SegSum.cons (w := 60) h184 (SegSum.cons (w := 360) h185 (SegSum.cons (w := 360) h187 (SegSum.cons (w := 120) h191 (SegSum.cons (w := 90) h207 (SegSum.cons (w := 72) h220 (SegSum.cons (w := 360) h221 (SegSum.cons (w := 360) h223 (SegSum.cons (w := 180) h254 (SegSum.cons (w := 180) h255 (SegSum.cons (w := 90) h495 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S0
