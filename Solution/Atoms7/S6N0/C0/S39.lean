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

namespace RACert.S6N0.C0.S39

open RACert RACert.Problem

theorem cover77167 : P.CoversSplit 26 10 77167 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 579, 580, 629, 636, 874, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h77167 : P.leaf 36 77167 = 287230 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 77167) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 77167) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover77167 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover77182 : P.CoversSplit 26 10 77182 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 579, 580, 629, 636, 874, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h77182 : P.leaf 36 77182 = 371608 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 77182) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 77182) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover77182 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover77183 : P.CoversSplit 26 10 77183 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 579, 580, 629, 636, 874, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h77183 : P.leaf 36 77183 = 1827836 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 77183) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 77183) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover77183 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover77292 : P.CoversSplit 26 10 77292 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 874, 881, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h77292 : P.leaf 36 77292 = 125498 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 77292) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 77292) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover77292 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover77293 : P.CoversSplit 26 10 77293 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 874, 881, 930, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h77293 : P.leaf 36 77293 = 315830 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 77293) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 77293) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover77293 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover77295 : P.CoversSplit 26 10 77295 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 874, 881, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h77295 : P.leaf 36 77295 = 1234078 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 77295) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 77295) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover77295 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover77311 : P.CoversSplit 26 10 77311 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 874, 881, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h77311 : P.leaf 36 77311 = 6888880 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 77311) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 77311) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover77311 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover301458 : P.CoversSplit 26 10 301458 0x8000000000000000000000000000000000000000000000001111111111111111000000000000000000000000000000000000000000000000111111111111111100000000000000000000000000000000000000000000000011111111111111110000000000000000000000000000000000000000000000001111111111111111 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 530, 538, 608, 629, 636, 922, 930]) (by decide +kernel)

noncomputable def f301458 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 26 (308692992 + i)

theorem c301458_0 : rowSum f301458 0 1024 = 2077333 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 301458) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover301458 (by decide)
  decide +kernel

theorem sum301458 : rowSum f301458 0 1024 = 2077333 :=
  c301458_0

theorem h301458 : P.leaf 36 301458 = 2077333 :=
  leaf_weighted (k := 26) (d := 10) (H := 301458) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 301458) (by decide) (by decide +kernel)) sum301458

theorem h77640 : P.leaf 36 77640 = 2077333 :=
  orient6 (v := 301458) (by decide) (by decide +kernel) h301458

theorem cover301459 : P.CoversSplit 26 10 301459 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 482, 488, 489, 530, 538, 629, 636, 922, 930]) (by decide +kernel)

theorem h301459 : P.leaf 36 301459 = 91136 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 301459) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 301459) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover301459 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h77641 : P.leaf 36 77641 = 91136 :=
  orient6 (v := 301459) (by decide) (by decide +kernel) h301459

theorem cover301494 : P.CoversSplit 26 10 301494 0xcc00cc0000000000000000000000000000000000000000000000000000000000440044000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [468, 489, 538, 629, 636, 866, 930, 1658]) (by decide +kernel)

theorem h301494 : P.leaf 36 301494 = 853040 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 301494) (keep := keep3) (twice := twice3) rows (by decide) (by decide) bal3 (invRow3 (H := 301494) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 301494) (weight := rowWeight keep3 twice3) (xs := [746, 750, 762, 766, 1002, 1003, 1006, 1007, 1018, 1019, 1022, 1023]) check rows elimOK (by decide) (by decide) cover301494 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h77643 : P.leaf 36 77643 = 853040 :=
  orient86 (v := 301494) (by decide) (by decide +kernel) h301494

theorem cover301471 : P.CoversSplit 26 10 301471 0xffff555533331111000000000000000000000000000000001000100010001000555555551111111100000000000000000000000000000000100010001000100033331111333311110000000000000000000000000000000010001000100010001111111111111111000000000000000000000000000000001000100010001000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 538, 629, 636, 922, 930, 1265, 1273, 1308, 1658, 1665]) (by decide +kernel)

noncomputable def f301471 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 26 (308706304 + i)

theorem c301471_0 : rowSum f301471 0 1024 = 9424673 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 301471) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover301471 (by decide)
  decide +kernel

theorem sum301471 : rowSum f301471 0 1024 = 9424673 :=
  c301471_0

theorem h301471 : P.leaf 36 301471 = 9424673 :=
  leaf_weighted (k := 26) (d := 10) (H := 301471) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 301471) (by decide) (by decide +kernel)) sum301471

theorem h77647 : P.leaf 36 77647 = 9424673 :=
  orient6 (v := 301471) (by decide) (by decide +kernel) h301471

theorem cover301495 : P.CoversSplit 26 10 301495 0xcc00cc0000000000000000000000000000000000000000000000000000000000440044000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000033003300000000000000000000000000000000000000000000000000000000001100110000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 538, 629, 636, 922, 930, 965, 1658]) (by decide +kernel)

theorem h301495 : P.leaf 36 301495 = 3847491 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 301495) (keep := keep3) (twice := twice3) rows (by decide) (by decide) bal3 (invRow3 (H := 301495) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 301495) (weight := rowWeight keep3 twice3) (xs := [64, 68, 80, 84, 320, 321, 324, 325, 336, 337, 340, 341, 746, 750, 762, 766, 1002, 1003, 1006, 1007, 1018, 1019, 1022, 1023]) check rows elimOK (by decide) (by decide) cover301495 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h77659 : P.leaf 36 77659 = 3847491 :=
  orient6 (v := 301495) (by decide) (by decide +kernel) h301495

theorem cover301971 : P.CoversSplit 26 10 301971 0xf420440020200000000000000000000000000000000000000000000000000000f420440020200000000000000000000000000000000000000000000000000000f420440020200000000000000000000000000000000000000000000000000000f420440020200000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 482, 488, 489, 531, 537, 922, 923, 929, 930, 1265, 1273]) (by decide +kernel)

noncomputable def f301971 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 26 (309218304 + i)

theorem c301971_0 : rowSum f301971 0 1024 = 1450384 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 301971) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover301971 (by decide)
  decide +kernel

theorem sum301971 : rowSum f301971 0 1024 = 1450384 :=
  c301971_0

theorem h301971 : P.leaf 36 301971 = 1450384 :=
  leaf_weighted (k := 26) (d := 10) (H := 301971) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 301971) (by decide) (by decide +kernel)) sum301971

theorem h77660 : P.leaf 36 77660 = 1450384 :=
  orient80 (v := 301971) (by decide) (by decide +kernel) h301971

theorem cover301499 : P.CoversSplit 26 10 301499 0xf5f4f5f431302020000000000000000000000000000000000000000000000000555455541110000000000000000000000000000000000000000000000000000031303130313020200000000000000000000000000000000000000000000000001110111011100000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [481, 538, 629, 636, 922, 930, 965, 1265, 1273, 1308, 1658, 1665]) (ps := [(15, [930], [922]), (19, [1265], [1273])]) (by decide +kernel)

noncomputable def f301499 (i : ℕ) := rowWeight keep4 twice4 i * P.leaf 26 (308734976 + i)

theorem c301499_0 : rowSum f301499 0 1024 = 6474244 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 301499) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover301499 (by decide)
  decide +kernel

theorem sum301499 : rowSum f301499 0 1024 = 6474244 :=
  c301499_0

theorem h301499 : P.leaf 36 301499 = 6474244 :=
  leaf_weighted (k := 26) (d := 10) (H := 301499) (keep := keep4) (twice := twice4) rows (by decide) (by decide) (bal4) (invRow4 (H := 301499) (by decide) (by decide +kernel)) sum301499

theorem h77661 : P.leaf 36 77661 = 6474244 :=
  orient6 (v := 301499) (by decide) (by decide +kernel) h301499

theorem cover301983 : P.CoversSplit 26 10 301983 0xffff555533331111000000000000000000000000000000000000000000000000ffff555533331111000000000000000000000000000000000000000000000000ffff555533331111000000000000000000000000000000000000000000000000ffff555533331111000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 538, 922, 930, 1265, 1266, 1272, 1273]) (by decide +kernel)

noncomputable def f301983 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 26 (309230592 + i)

theorem c301983_0 : rowSum f301983 0 1024 = 27826364 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 301983) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover301983 (by decide)
  decide +kernel

theorem sum301983 : rowSum f301983 0 1024 = 27826364 :=
  c301983_0

theorem h301983 : P.leaf 36 301983 = 27826364 :=
  leaf_weighted (k := 26) (d := 10) (H := 301983) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 301983) (by decide) (by decide +kernel)) sum301983

theorem h77663 : P.leaf 36 77663 = 27826364 :=
  orient80 (v := 301983) (by decide) (by decide +kernel) h301983

theorem cover302011 : P.CoversSplit 26 10 302011 0xf5f4f5f431302020000000000000000000000000000000000000000000000000f5f4f5f431302020000000000000000000000000000000000000000000000000f5f4f5f431302020000000000000000000000000000000000000000000000000f5f4f5f431302020000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [481, 538, 922, 929, 1265, 1266, 1273]) (ps := [(15, [930], [922]), (19, [1265], [1273])]) (by decide +kernel)

noncomputable def f302011 (i : ℕ) := rowWeight keep4 twice4 i * P.leaf 26 (309259264 + i)

theorem c302011_0 : rowSum f302011 0 1024 = 28892568 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 302011) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover302011 (by decide)
  decide +kernel

theorem sum302011 : rowSum f302011 0 1024 = 28892568 :=
  c302011_0

theorem h302011 : P.leaf 36 302011 = 28892568 :=
  leaf_weighted (k := 26) (d := 10) (H := 302011) (keep := keep4) (twice := twice4) rows (by decide) (by decide) (bal4) (invRow4 (H := 302011) (by decide) (by decide +kernel)) sum302011

theorem h77694 : P.leaf 36 77694 = 28892568 :=
  orient74 (v := 302011) (by decide) (by decide +kernel) h302011

theorem cover301567 : P.CoversSplit 26 10 301567 0xffffffffffffffff000000000000000000000000000000001000000000000000555555555555555550500000505000000000000000000000100000000000000033333333333333330000000000000000330033000000000010000000000000001111111111111111101000001010000011001100000000001000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [629, 636, 922, 930, 1265, 1273, 1658, 1665]) (by decide +kernel)

noncomputable def f301567 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 26 (308804608 + i)

theorem c301567_0 : rowSum f301567 0 1024 = 115213726 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 301567) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover301567 (by decide)
  decide +kernel

theorem sum301567 : rowSum f301567 0 1024 = 115213726 :=
  c301567_0

theorem h301567 : P.leaf 36 301567 = 115213726 :=
  leaf_weighted (k := 26) (d := 10) (H := 301567) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 301567) (by decide) (by decide +kernel)) sum301567

theorem h77695 : P.leaf 36 77695 = 115213726 :=
  orient6 (v := 301567) (by decide) (by decide +kernel) h301567

theorem cover302079 : P.CoversSplit 26 10 302079 0xfffffffffffffffffafaaaaafafaaaaaffccffcccccccccc8888888888888888ffffffffffffffffaaaaaaaaaaaaaaaaffccffcccccccccc8888888888888888fffffffffffffffffafaaaaafafaaaaacccccccccccccccc8888888888888888ffffffffffffffffaaaaaaaaaaaaaaaacccccccccccccccc8888888888888888 :=
  coversSplit check rows (by decide) (by decide) (xs := [922, 930, 1265, 1273, 1658, 1665]) (by decide +kernel)

noncomputable def f302079 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 26 (309328896 + i)

theorem c302079_0 : rowSum f302079 0 326 = 386144692 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 302079) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover302079 (by decide)
  decide +kernel

theorem c302079_1 : rowSum f302079 326 148 = 472632524 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 302079) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover302079 (by decide)
  decide +kernel

theorem c302079_2 : rowSum f302079 474 499 = 564922122 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 302079) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover302079 (by decide)
  decide +kernel

theorem c302079_3 : rowSum f302079 973 51 = 231644008 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 302079) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover302079 (by decide)
  decide +kernel

theorem sum302079 : rowSum f302079 0 1024 = 1655343346 :=
  rowSum_append (F := f302079) (lo := 0) (n := 326) (m := 698) (A := 386144692) (B := 1269198654) c302079_0 (rowSum_append (F := f302079) (lo := 326) (n := 148) (m := 550) (A := 472632524) (B := 796566130) c302079_1 (rowSum_append (F := f302079) (lo := 474) (n := 499) (m := 51) (A := 564922122) (B := 231644008) c302079_2 (c302079_3)))

theorem h302079 : P.leaf 36 302079 = 1655343346 :=
  leaf_weighted (k := 26) (d := 10) (H := 302079) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 302079) (by decide) (by decide +kernel)) sum302079

theorem h77823 : P.leaf 36 77823 = 1655343346 :=
  orient6 (v := 302079) (by decide) (by decide +kernel) h302079

theorem cover78030 : P.CoversSplit 26 10 78030 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 536, 537, 580, 587, 629, 930, 972, 1273, 1315, 1658]) (by decide +kernel)

theorem h78030 : P.leaf 36 78030 = 1024 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 78030) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 78030) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover78030 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover78031 : P.CoversSplit 26 10 78031 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 536, 537, 580, 587, 629, 930, 972, 1273, 1315, 1658]) (by decide +kernel)

theorem h78031 : P.leaf 36 78031 = 7296 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 78031) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 78031) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover78031 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover78044 : P.CoversSplit 26 10 78044 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 479, 487, 537, 580, 587, 629, 930, 972, 1273, 1658]) (by decide +kernel)

theorem h78044 : P.leaf 36 78044 = 4096 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 78044) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 78044) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover78044 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover78045 : P.CoversSplit 26 10 78045 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 487, 530, 537, 580, 587, 629, 930, 972, 1273, 1315, 1658]) (by decide +kernel)

theorem h78045 : P.leaf 36 78045 = 13824 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 78045) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 78045) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover78045 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover78046 : P.CoversSplit 26 10 78046 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 537, 580, 587, 629, 930, 972, 1273, 1315, 1658]) (by decide +kernel)

theorem h78046 : P.leaf 36 78046 = 6912 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 78046) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 78046) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover78046 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover78047 : P.CoversSplit 26 10 78047 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 537, 580, 587, 629, 930, 972, 1273, 1315, 1658]) (by decide +kernel)

theorem h78047 : P.leaf 36 78047 = 45888 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 78047) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 78047) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover78047 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover78078 : P.CoversSplit 26 10 78078 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 580, 587, 629, 636, 867, 930, 972, 1273, 1315, 1658]) (by decide +kernel)

theorem h78078 : P.leaf 36 78078 = 20936 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 78078) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 78078) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover78078 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover78079 : P.CoversSplit 26 10 78079 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 580, 587, 629, 636, 867, 930, 972, 1273, 1315, 1658]) (by decide +kernel)

theorem h78079 : P.leaf 36 78079 = 242240 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 78079) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 78079) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover78079 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover78355 : P.CoversSplit 26 10 78355 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030000000000000000000000000000000000000000000000000000000000000002 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 530, 538, 579, 587, 608, 873, 930, 972, 979]) (by decide +kernel)

theorem h78355 : P.leaf 36 78355 = 676 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 78355) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 78355) (weight := fun _ => 1) (xs := [1, 256, 257, 1023]) check rows elimOK (by decide) (by decide) cover78355 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h78117 : P.leaf 36 78117 = 676 :=
  orient4 (v := 78355) (by decide) (by decide +kernel) h78355

theorem cover78119 : P.CoversSplit 26 10 78119 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000200000000001000010000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [482, 489, 538, 629, 636, 930, 972, 1315, 1658]) (by decide +kernel)

theorem h78119 : P.leaf 36 78119 = 5803 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 78119) (keep := keep9) (twice := twice9) rows (by decide) (by decide) bal9 (invRow9 (H := 78119) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 78119) (weight := rowWeight keep9 twice9) (xs := [256, 276, 321, 341, 1023]) check rows elimOK (by decide) (by decide) cover78119 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover78121 : P.CoversSplit 26 10 78121 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [474, 481, 482, 531, 636, 979, 1273, 1315, 1658]) (by decide +kernel)

theorem h78121 : P.leaf 36 78121 = 256 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 78121) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 78121) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover78121 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover78123 : P.CoversSplit 26 10 78123 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 482, 531, 636, 979, 1273, 1315, 1658]) (by decide +kernel)

theorem h78123 : P.leaf 36 78123 = 832 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 78123) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 78123) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover78123 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover78125 : P.CoversSplit 26 10 78125 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 531, 538, 580, 629, 636, 972, 979, 1273, 1315, 1658]) (by decide +kernel)

theorem h78125 : P.leaf 36 78125 = 1024 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 78125) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 78125) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover78125 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover78127 : P.CoversSplit 26 10 78127 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 531, 538, 580, 629, 636, 972, 979, 1273, 1315, 1658]) (by decide +kernel)

theorem h78127 : P.leaf 36 78127 = 14560 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 78127) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 78127) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover78127 (by decide) (by decide) (by decide +kernel)
  decide +kernel

def seg : List (ℕ × ℕ) := [(77167, 720), (77182, 360), (77183, 360), (77292, 120), (77293, 360), (77295, 360), (77311, 120), (77640, 15), (77641, 180), (77643, 360), (77647, 120), (77659, 120), (77660, 90), (77661, 360), (77663, 360), (77694, 90), (77695, 180), (77823, 30), (78030, 180), (78031, 180), (78044, 360), (78045, 360), (78046, 720), (78047, 720), (78078, 180), (78079, 180), (78117, 360), (78119, 360), (78121, 720), (78123, 360), (78125, 720), (78127, 360)]

theorem segOK : checkSeg 20 perms 77167 78134 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 77167 78134 10065 89925603495 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 89925603495)
    (SegSum.cons (w := 720) h77167 (SegSum.cons (w := 360) h77182 (SegSum.cons (w := 360) h77183 (SegSum.cons (w := 120) h77292 (SegSum.cons (w := 360) h77293 (SegSum.cons (w := 360) h77295 (SegSum.cons (w := 120) h77311 (SegSum.cons (w := 15) h77640 (SegSum.cons (w := 180) h77641 (SegSum.cons (w := 360) h77643 (SegSum.cons (w := 120) h77647 (SegSum.cons (w := 120) h77659 (SegSum.cons (w := 90) h77660 (SegSum.cons (w := 360) h77661 (SegSum.cons (w := 360) h77663 (SegSum.cons (w := 90) h77694 (SegSum.cons (w := 180) h77695 (SegSum.cons (w := 30) h77823 (SegSum.cons (w := 180) h78030 (SegSum.cons (w := 180) h78031 (SegSum.cons (w := 360) h78044 (SegSum.cons (w := 360) h78045 (SegSum.cons (w := 720) h78046 (SegSum.cons (w := 720) h78047 (SegSum.cons (w := 180) h78078 (SegSum.cons (w := 180) h78079 (SegSum.cons (w := 360) h78117 (SegSum.cons (w := 360) h78119 (SegSum.cons (w := 720) h78121 (SegSum.cons (w := 360) h78123 (SegSum.cons (w := 720) h78125 (SegSum.cons (w := 360) h78127 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S39
