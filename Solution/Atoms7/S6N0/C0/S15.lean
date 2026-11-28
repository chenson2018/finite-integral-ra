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

namespace RACert.S6N0.C0.S15

open RACert RACert.Problem

theorem cover8093 : P.CoversSplit 26 10 8093 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem h8093 : P.leaf 36 8093 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 8093) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 8093) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover8093 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover8094 : P.CoversSplit 26 10 8094 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h8094 : P.leaf 36 8094 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 8094) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 8094) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover8094 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover8095 : P.CoversSplit 26 10 8095 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h8095 : P.leaf 36 8095 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 8095) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 8095) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover8095 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover8118 : P.CoversSplit 26 10 8118 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem h8118 : P.leaf 36 8118 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 8118) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 8118) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover8118 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover8119 : P.CoversSplit 26 10 8119 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem h8119 : P.leaf 36 8119 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 8119) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 8119) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover8119 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover8122 : P.CoversSplit 26 10 8122 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [929]) (by decide +kernel)

theorem h8122 : P.leaf 36 8122 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 8122) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 8122) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover8122 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover8123 : P.CoversSplit 26 10 8123 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [929]) (by decide +kernel)

theorem h8123 : P.leaf 36 8123 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 8123) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 8123) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover8123 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover8126 : P.CoversSplit 26 10 8126 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h8126 : P.leaf 36 8126 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 8126) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 8126) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover8126 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover8127 : P.CoversSplit 26 10 8127 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h8127 : P.leaf 36 8127 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 8127) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 8127) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover8127 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover8190 : P.CoversSplit 26 10 8190 0xfffffffafffcfac8fffffafafffcfac8fffffffaffccfac88888888888888888fffffafafffcfac8aaaaaaaaaaa8aa88fffffafaffccfac88888888888888888fffffffaffccfac8fffffafaffccfac8ccccccc8ccccc8c888888888888888880000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [874, 922, 930, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f8190 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 26 (8386560 + i)

theorem c8190_0 : rowSum f8190 0 455 = 131484200 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 8190) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover8190 (by decide)
  decide +kernel

theorem c8190_1 : rowSum f8190 455 427 = 226356600 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 8190) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover8190 (by decide)
  decide +kernel

theorem c8190_2 : rowSum f8190 882 142 = 181935724 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 8190) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover8190 (by decide)
  decide +kernel

theorem sum8190 : rowSum f8190 0 1024 = 539776524 :=
  rowSum_append (F := f8190) (lo := 0) (n := 455) (m := 569) (A := 131484200) (B := 408292324) c8190_0 (rowSum_append (F := f8190) (lo := 455) (n := 427) (m := 142) (A := 226356600) (B := 181935724) c8190_1 (c8190_2))

theorem h8190 : P.leaf 36 8190 = 539776524 :=
  leaf_weighted (k := 26) (d := 10) (H := 8190) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 8190) (by decide) (by decide +kernel)) sum8190

theorem cover820223 : P.CoversSplit 26 10 820223 0xfffffafaffccfac8fafaaaaafac8aa88ffccfac8ccccc8c8fac8aa88c8c88888fffffafaffccfac8fafaaaaafac8aa88ffccfac8ccccc8c8fac8aa88c8c88888fffffafaffccfac8fafaaaaafac8aa88ffccfac8ccccc8c8fac8aa88c8c88888fffffafaffccfac8fafaaaaafac8aa88ffccfac8ccccc8c8fac8aa88c8c88888 :=
  coversSplit check rows (by decide) (by decide) (xs := [873, 881, 922, 930, 1265, 1273]) (by decide +kernel)

noncomputable def f820223 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 26 (839908352 + i)

theorem c820223_0 : rowSum f820223 0 311 = 427326665 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 820223) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover820223 (by decide)
  decide +kernel

theorem c820223_1 : rowSum f820223 311 167 = 474364176 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 820223) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover820223 (by decide)
  decide +kernel

theorem c820223_2 : rowSum f820223 478 512 = 523639440 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 820223) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover820223 (by decide)
  decide +kernel

theorem c820223_3 : rowSum f820223 990 34 = 78674912 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 820223) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover820223 (by decide)
  decide +kernel

theorem sum820223 : rowSum f820223 0 1024 = 1504005193 :=
  rowSum_append (F := f820223) (lo := 0) (n := 311) (m := 713) (A := 427326665) (B := 1076678528) c820223_0 (rowSum_append (F := f820223) (lo := 311) (n := 167) (m := 546) (A := 474364176) (B := 602314352) c820223_1 (rowSum_append (F := f820223) (lo := 478) (n := 512) (m := 34) (A := 523639440) (B := 78674912) c820223_2 (c820223_3)))

theorem h820223 : P.leaf 36 820223 = 1504005193 :=
  leaf_weighted (k := 26) (d := 10) (H := 820223) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 820223) (by decide) (by decide +kernel)) sum820223

theorem h8191 : P.leaf 36 8191 = 1504005193 :=
  orient324 (v := 820223) (by decide) (by decide +kernel) h820223

theorem cover11443 : P.CoversSplit 26 10 11443 0x8000000000000000000000000000000000000000000000000000000000000000cc00cc0000000000cc00c800000000000000000000000000000000000000000000000000000000000000000000000000000000000033003300000000003300320000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 538, 587, 629, 636, 881, 972, 1315, 1658, 2008]) (by decide +kernel)

theorem h11443 : P.leaf 36 11443 = 15481888 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 11443) (keep := keep9) (twice := twice9) rows (by decide) (by decide) bal9 (invRow9 (H := 11443) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 11443) (weight := rowWeight keep9 twice9) (xs := [257, 260, 261, 272, 273, 276, 277, 320, 321, 324, 325, 336, 337, 340, 341, 683, 686, 687, 698, 699, 702, 703, 746, 747, 750, 751, 762, 763, 766, 767, 1023]) check rows elimOK (by decide) (by decide) cover11443 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover11447 : P.CoversSplit 26 10 11447 0x8000000000000000000000000000000000000000000000000000000000000000cc00cc0000000000cc00c800000000000000000000000000000000000000000000000000000000000000000000000000000000000033003300000000003300320000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 538, 587, 629, 636, 881, 972, 1265, 1315, 1658, 2008]) (by decide +kernel)

theorem h11447 : P.leaf 36 11447 = 33668760 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 11447) (keep := keep9) (twice := twice9) rows (by decide) (by decide) bal9 (invRow9 (H := 11447) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 11447) (weight := rowWeight keep9 twice9) (xs := [257, 260, 261, 272, 273, 276, 277, 320, 321, 324, 325, 336, 337, 340, 341, 683, 686, 687, 698, 699, 702, 703, 746, 747, 750, 751, 762, 763, 766, 767, 1023]) check rows elimOK (by decide) (by decide) cover11447 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover76307 : P.CoversSplit 26 10 76307 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030000000000000000000000000000000000000000000000000000000000000003 :=
  coversProjected check rows (by decide) (by decide) (xs := [481, 489, 530, 538, 579, 587, 608, 881, 979]) (ps := [(13, [510], [972])]) (by decide +kernel)

theorem h76307 : P.leaf 36 76307 = 6575 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 76307) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 76307) (weight := fun _ => 1) (xs := [0, 1, 256, 257, 1023]) check rows elimOK (by decide) (by decide) cover76307 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h11448 : P.leaf 36 11448 = 6575 :=
  orient84 (v := 76307) (by decide) (by decide +kernel) h76307

theorem cover11452 : P.CoversSplit 26 10 11452 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000021002100000000002100200000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 531, 538, 587, 629, 636, 881, 972, 979, 1265, 1315, 1658]) (by decide +kernel)

theorem h11452 : P.leaf 36 11452 = 9812 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 11452) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 11452) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 11452) (weight := rowWeight keep1 twice1) (xs := [261, 272, 277, 320, 325, 336, 341, 1023]) check rows elimOK (by decide) (by decide) cover11452 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h11449 : P.leaf 36 11449 = 9812 :=
  orient72 (v := 11452) (by decide) (by decide +kernel) h11452

theorem cover11451 : P.CoversSplit 26 10 11451 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000021002100000000002100200000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 531, 538, 587, 629, 636, 881, 972, 1265, 1315, 1658]) (by decide +kernel)

theorem h11451 : P.leaf 36 11451 = 18106 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 11451) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 11451) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 11451) (weight := rowWeight keep1 twice1) (xs := [261, 272, 277, 320, 325, 336, 341, 1023]) check rows elimOK (by decide) (by decide) cover11451 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover11455 : P.CoversSplit 26 10 11455 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000021002100000000002100200000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 531, 538, 587, 629, 636, 881, 972, 1265, 1315, 1658]) (by decide +kernel)

theorem h11455 : P.leaf 36 11455 = 42574 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 11455) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 11455) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 11455) (weight := rowWeight keep1 twice1) (xs := [261, 272, 277, 320, 325, 336, 341, 1023]) check rows elimOK (by decide) (by decide) cover11455 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover11458 : P.CoversSplit 26 10 11458 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [482]) (by decide +kernel)

theorem h11458 : P.leaf 36 11458 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 11458) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 11458) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover11458 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover11459 : P.CoversSplit 26 10 11459 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [482]) (by decide +kernel)

theorem h11459 : P.leaf 36 11459 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 11459) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 11459) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover11459 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover11462 : P.CoversSplit 26 10 11462 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h11462 : P.leaf 36 11462 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 11462) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 11462) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover11462 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover11463 : P.CoversSplit 26 10 11463 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h11463 : P.leaf 36 11463 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 11463) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 11463) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover11463 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover11464 : P.CoversSplit 26 10 11464 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h11464 : P.leaf 36 11464 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 11464) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 11464) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover11464 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover11465 : P.CoversSplit 26 10 11465 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h11465 : P.leaf 36 11465 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 11465) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 11465) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover11465 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover11466 : P.CoversSplit 26 10 11466 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h11466 : P.leaf 36 11466 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 11466) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 11466) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover11466 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover11467 : P.CoversSplit 26 10 11467 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h11467 : P.leaf 36 11467 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 11467) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 11467) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover11467 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover11470 : P.CoversSplit 26 10 11470 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h11470 : P.leaf 36 11470 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 11470) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 11470) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover11470 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover11471 : P.CoversSplit 26 10 11471 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h11471 : P.leaf 36 11471 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 11471) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 11471) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover11471 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover11475 : P.CoversSplit 26 10 11475 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [482]) (by decide +kernel)

theorem h11475 : P.leaf 36 11475 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 11475) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 11475) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover11475 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover11476 : P.CoversSplit 26 10 11476 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [475]) (by decide +kernel)

theorem h11476 : P.leaf 36 11476 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 11476) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 11476) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover11476 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover11477 : P.CoversSplit 26 10 11477 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [475]) (by decide +kernel)

theorem h11477 : P.leaf 36 11477 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 11477) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 11477) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover11477 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover11478 : P.CoversSplit 26 10 11478 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h11478 : P.leaf 36 11478 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 11478) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 11478) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover11478 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover11479 : P.CoversSplit 26 10 11479 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h11479 : P.leaf 36 11479 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 11479) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 11479) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover11479 (by decide) (by decide) (by decide +kernel)
  decide +kernel

def seg : List (ℕ × ℕ) := [(8093, 360), (8094, 360), (8095, 360), (8118, 180), (8119, 180), (8122, 360), (8123, 360), (8126, 360), (8127, 360), (8190, 60), (8191, 60), (11443, 90), (11447, 60), (11448, 60), (11449, 180), (11451, 180), (11455, 60), (11458, 360), (11459, 720), (11462, 360), (11463, 360), (11464, 360), (11465, 360), (11466, 720), (11467, 720), (11470, 360), (11471, 360), (11475, 360), (11476, 360), (11477, 720), (11478, 720), (11479, 720)]

theorem segOK : checkSeg 20 perms 8093 11480 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 8093 11480 11190 126048372720 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 126048372720)
    (SegSum.cons (w := 360) h8093 (SegSum.cons (w := 360) h8094 (SegSum.cons (w := 360) h8095 (SegSum.cons (w := 180) h8118 (SegSum.cons (w := 180) h8119 (SegSum.cons (w := 360) h8122 (SegSum.cons (w := 360) h8123 (SegSum.cons (w := 360) h8126 (SegSum.cons (w := 360) h8127 (SegSum.cons (w := 60) h8190 (SegSum.cons (w := 60) h8191 (SegSum.cons (w := 90) h11443 (SegSum.cons (w := 60) h11447 (SegSum.cons (w := 60) h11448 (SegSum.cons (w := 180) h11449 (SegSum.cons (w := 180) h11451 (SegSum.cons (w := 60) h11455 (SegSum.cons (w := 360) h11458 (SegSum.cons (w := 720) h11459 (SegSum.cons (w := 360) h11462 (SegSum.cons (w := 360) h11463 (SegSum.cons (w := 360) h11464 (SegSum.cons (w := 360) h11465 (SegSum.cons (w := 720) h11466 (SegSum.cons (w := 720) h11467 (SegSum.cons (w := 360) h11470 (SegSum.cons (w := 360) h11471 (SegSum.cons (w := 360) h11475 (SegSum.cons (w := 360) h11476 (SegSum.cons (w := 720) h11477 (SegSum.cons (w := 720) h11478 (SegSum.cons (w := 720) h11479 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S15
