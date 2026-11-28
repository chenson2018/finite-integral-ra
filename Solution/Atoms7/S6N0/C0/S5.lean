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

namespace RACert.S6N0.C0.S5

open RACert RACert.Problem

theorem cover1790 : P.CoversSplit 26 10 1790 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [874]) (by decide +kernel)

theorem h1790 : P.leaf 36 1790 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 1790) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 1790) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1790 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1791 : P.CoversSplit 26 10 1791 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [929]) (by decide +kernel)

theorem h1791 : P.leaf 36 1791 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 1791) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 1791) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1791 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover2028 : P.CoversSplit 26 10 2028 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [874]) (by decide +kernel)

theorem h2028 : P.leaf 36 2028 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 2028) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 2028) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover2028 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover2029 : P.CoversSplit 26 10 2029 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem h2029 : P.leaf 36 2029 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 2029) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 2029) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover2029 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover2031 : P.CoversSplit 26 10 2031 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h2031 : P.leaf 36 2031 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 2031) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 2031) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover2031 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover2047 : P.CoversSplit 26 10 2047 0xfff8fff8fff88888fff8faf8fff88888fff8fff8ffc888888888888888888888faf8aaa8faf88888aaa8aaa8aaa88888faf8aaa8fac888888888888888888888ffc8ffc8ccc88888ffc8fac8ccc88888ccc8ccc8ccc888888888888888888888fac8aa88c8c88888aa88aa8888888888c8c88888c8c888888888888888888888 :=
  coversSplit check rows (by decide) (by decide) (xs := [873, 881, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f2047 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 26 (2096128 + i)

theorem c2047_0 : rowSum f2047 0 415 = 83526264 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 2047) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover2047 (by decide)
  decide +kernel

theorem c2047_1 : rowSum f2047 415 472 = 192290008 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 2047) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover2047 (by decide)
  decide +kernel

theorem c2047_2 : rowSum f2047 887 137 = 111264048 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 2047) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover2047 (by decide)
  decide +kernel

theorem sum2047 : rowSum f2047 0 1024 = 387080320 :=
  rowSum_append (F := f2047) (lo := 0) (n := 415) (m := 609) (A := 83526264) (B := 303554056) c2047_0 (rowSum_append (F := f2047) (lo := 415) (n := 472) (m := 137) (A := 192290008) (B := 111264048) c2047_1 (c2047_2))

theorem h2047 : P.leaf 36 2047 = 387080320 :=
  leaf_weighted (k := 26) (d := 10) (H := 2047) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 2047) (by decide) (by decide +kernel)) sum2047

theorem cover3126 : P.CoversSplit 26 10 3126 0x8000000000000000000000000000000000000000000000000000000000000000800004000000000000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000020000100000000000000010000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 538, 579, 587, 629, 636, 922, 930, 1265, 2008]) (by decide +kernel)

theorem h3126 : P.leaf 36 3126 = 173712 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3126) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3126) (weight := fun _ => 1) (xs := [256, 320, 341, 682, 746, 767, 1023]) check rows elimOK (by decide) (by decide) cover3126 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3127 : P.CoversSplit 26 10 3127 0x8000000000000000000000000000000000000000000000000000000000000000800004000000000000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000020000100000000000000010000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 538, 579, 587, 629, 636, 881, 922, 1265, 2008]) (by decide +kernel)

theorem h3127 : P.leaf 36 3127 = 255600 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3127) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3127) (weight := fun _ => 1) (xs := [256, 320, 341, 682, 746, 767, 1023]) check rows elimOK (by decide) (by decide) cover3127 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3132 : P.CoversSplit 26 10 3132 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000100000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 474, 531, 538, 579, 587, 629, 636, 881, 922, 972, 979, 1265]) (by decide +kernel)

theorem h3132 : P.leaf 36 3132 = 916 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3132) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3132) (weight := fun _ => 1) (xs := [320, 341, 1023]) check rows elimOK (by decide) (by decide) cover3132 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h3130 : P.leaf 36 3130 = 916 :=
  orient4 (v := 3132) (by decide) (by decide +kernel) h3132

theorem cover3133 : P.CoversSplit 26 10 3133 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000100000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 474, 531, 538, 579, 587, 629, 636, 881, 922, 972, 1265]) (by decide +kernel)

theorem h3133 : P.leaf 36 3133 = 4116 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3133) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3133) (weight := fun _ => 1) (xs := [320, 341, 1023]) check rows elimOK (by decide) (by decide) cover3133 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h3131 : P.leaf 36 3131 = 4116 :=
  orient4 (v := 3133) (by decide) (by decide +kernel) h3133

theorem cover3134 : P.CoversSplit 26 10 3134 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000100000000000000010000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 531, 538, 579, 587, 629, 636, 881, 922, 930, 1265]) (by decide +kernel)

theorem h3134 : P.leaf 36 3134 = 3664 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3134) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3134) (weight := fun _ => 1) (xs := [256, 320, 341, 1023]) check rows elimOK (by decide) (by decide) cover3134 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3135 : P.CoversSplit 26 10 3135 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000100000000000000010000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 531, 538, 579, 587, 629, 636, 881, 922, 1265]) (by decide +kernel)

theorem h3135 : P.leaf 36 3135 = 10188 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3135) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3135) (weight := fun _ => 1) (xs := [256, 320, 341, 1023]) check rows elimOK (by decide) (by decide) cover3135 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3164 : P.CoversSplit 26 10 3164 0x8000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 475, 480, 531, 579, 587, 629, 636, 880, 922, 930, 972, 979, 1265, 1273]) (by decide +kernel)

theorem h3164 : P.leaf 36 3164 = 1088 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3164) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3164) (weight := fun _ => 1) (xs := [960, 1023]) check rows elimOK (by decide) (by decide) cover3164 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3165 : P.CoversSplit 26 10 3165 0x8000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 475, 480, 531, 579, 587, 629, 636, 880, 922, 930, 972, 979, 1265, 1273]) (by decide +kernel)

theorem h3165 : P.leaf 36 3165 = 16864 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3165) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3165) (weight := fun _ => 1) (xs := [960, 1023]) check rows elimOK (by decide) (by decide) cover3165 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3166 : P.CoversSplit 26 10 3166 0x8000000000000001000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 579, 587, 629, 636, 880, 922, 930, 1265, 1273, 1658, 1665]) (by decide +kernel)

theorem h3166 : P.leaf 36 3166 = 5392 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3166) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3166) (weight := fun _ => 1) (xs := [768, 960, 1023]) check rows elimOK (by decide) (by decide) cover3166 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3167 : P.CoversSplit 26 10 3167 0x8000000000000001000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 579, 587, 629, 636, 880, 922, 930, 1265, 1273, 1658, 1665]) (by decide +kernel)

theorem h3167 : P.leaf 36 3167 = 53232 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3167) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3167) (weight := fun _ => 1) (xs := [768, 960, 1023]) check rows elimOK (by decide) (by decide) cover3167 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover6270 : P.CoversSplit 26 10 6270 0x8000000000000001000000000000000000000000000000000000000000000000000004000000000100000000000000000000000000000000000000000000000000000000002000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 579, 587, 629, 636, 866, 867, 922, 930, 1265, 1273]) (by decide +kernel)

theorem h6270 : P.leaf 36 6270 = 37560 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 6270) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 6270) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 6270) (weight := rowWeight keep0 twice0) (xs := [448, 469, 704, 746, 960, 1023]) check rows elimOK (by decide) (by decide) cover6270 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h3198 : P.leaf 36 3198 = 37560 :=
  orient6 (v := 6270) (by decide) (by decide +kernel) h6270

theorem cover6271 : P.CoversSplit 26 10 6271 0x8000000000000001000000000000000000000000000000000000000000000000000004000000000100000000000000000000000000000000000000000000000000000000002000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 579, 587, 629, 636, 866, 867, 922, 930, 1265, 1273]) (by decide +kernel)

theorem h6271 : P.leaf 36 6271 = 153824 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 6271) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 6271) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 6271) (weight := rowWeight keep0 twice0) (xs := [448, 469, 704, 746, 960, 1023]) check rows elimOK (by decide) (by decide) cover6271 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h3199 : P.leaf 36 3199 = 153824 :=
  orient6 (v := 6271) (by decide) (by decide +kernel) h6271

theorem cover3219 : P.CoversSplit 26 10 3219 0x8000000000000000000000000000000000000000000000000000000000000000800000000000000000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000020000000000000000000010000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 530, 538, 587, 629, 636, 881, 922, 2008]) (by decide +kernel)

theorem h3219 : P.leaf 36 3219 = 518776 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3219) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3219) (weight := fun _ => 1) (xs := [256, 341, 682, 767, 1023]) check rows elimOK (by decide) (by decide) cover3219 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3220 : P.CoversSplit 26 10 3220 0x8000000000000000000000000000000000000000000000000000000000000000cc0004000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000033000100000000000100000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 538, 587, 629, 636, 922, 972, 979, 1265, 2008]) (by decide +kernel)

theorem h3220 : P.leaf 36 3220 = 53416 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 3220) (keep := keep9) (twice := twice9) rows (by decide) (by decide) bal9 (invRow9 (H := 3220) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3220) (weight := rowWeight keep9 twice9) (xs := [272, 320, 336, 337, 340, 341, 698, 746, 762, 763, 766, 767, 1023]) check rows elimOK (by decide) (by decide) cover3220 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3221 : P.CoversSplit 26 10 3221 0x8000000000000000000000000000000000000000000000000000000000000000cc0004000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000033000100000000000100000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 538, 587, 629, 636, 881, 922, 972, 1265, 2008]) (by decide +kernel)

theorem h3221 : P.leaf 36 3221 = 905548 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3221) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3221) (weight := fun _ => 1) (xs := [272, 320, 336, 337, 340, 341, 698, 746, 762, 763, 766, 767, 1023]) check rows elimOK (by decide) (by decide) cover3221 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3223 : P.CoversSplit 26 10 3223 0x8000000000000000000000000000000000000000000000000000000000000000cc0004000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000033000100000000000100000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 538, 587, 629, 636, 881, 972, 1265, 2008]) (by decide +kernel)

theorem h3223 : P.leaf 36 3223 = 3523760 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 3223) (keep := keep9) (twice := twice9) rows (by decide) (by decide) bal9 (invRow9 (H := 3223) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3223) (weight := rowWeight keep9 twice9) (xs := [272, 320, 336, 337, 340, 341, 698, 746, 762, 763, 766, 767, 1023]) check rows elimOK (by decide) (by decide) cover3223 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3224 : P.CoversSplit 26 10 3224 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [531]) (by decide +kernel)

theorem h3224 : P.leaf 36 3224 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3224) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3224) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3224 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3225 : P.CoversSplit 26 10 3225 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [531]) (by decide +kernel)

theorem h3225 : P.leaf 36 3225 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3225) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3225) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3225 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3227 : P.CoversSplit 26 10 3227 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [531]) (by decide +kernel)

theorem h3227 : P.leaf 36 3227 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3227) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3227) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3227 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3228 : P.CoversSplit 26 10 3228 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [531]) (by decide +kernel)

theorem h3228 : P.leaf 36 3228 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3228) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3228) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3228 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3229 : P.CoversSplit 26 10 3229 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [531]) (by decide +kernel)

theorem h3229 : P.leaf 36 3229 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3229) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3229) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3229 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3231 : P.CoversSplit 26 10 3231 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [531]) (by decide +kernel)

theorem h3231 : P.leaf 36 3231 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3231) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3231) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3231 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover75939 : P.CoversSplit 26 10 75939 0x8000000000000000000000000000000000000000000000000000000000000000cc00cc0000000000cc00c800000000000000000000000000000000000000000000000000000000000000000000000000000000000033003300000000003300320000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 538, 587, 629, 636, 881, 972, 1315, 1658, 2008]) (by decide +kernel)

theorem h75939 : P.leaf 36 75939 = 6821088 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 75939) (keep := keep9) (twice := twice9) rows (by decide) (by decide) bal9 (invRow9 (H := 75939) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 75939) (weight := rowWeight keep9 twice9) (xs := [257, 260, 261, 272, 273, 276, 277, 320, 321, 324, 325, 336, 337, 340, 341, 683, 686, 687, 698, 699, 702, 703, 746, 747, 750, 751, 762, 763, 766, 767, 1023]) check rows elimOK (by decide) (by decide) cover75939 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h3254 : P.leaf 36 3254 = 6821088 :=
  orient85 (v := 75939) (by decide) (by decide +kernel) h75939

theorem cover10423 : P.CoversSplit 26 10 10423 0x8000000000000000000000000000000000000000000000000000000000000000cc00cc0000000000cc008800000000000000000000000000000000000000000000000000000000000000000000000000000000000033003300000000003300220000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 538, 587, 629, 636, 881, 972, 1265, 1315, 1658, 2008]) (by decide +kernel)

theorem h10423 : P.leaf 36 10423 = 16517420 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 10423) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 10423) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 10423) (weight := rowWeight keep1 twice1) (xs := [257, 261, 272, 273, 276, 277, 320, 321, 324, 325, 336, 337, 340, 341, 683, 687, 698, 699, 702, 703, 746, 747, 750, 751, 762, 763, 766, 767, 1023]) check rows elimOK (by decide) (by decide) cover10423 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h3255 : P.leaf 36 3255 = 16517420 :=
  orient72 (v := 10423) (by decide) (by decide +kernel) h10423

theorem cover3256 : P.CoversSplit 26 10 3256 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem h3256 : P.leaf 36 3256 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3256) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3256) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3256 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3257 : P.CoversSplit 26 10 3257 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem h3257 : P.leaf 36 3257 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 3257) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 3257) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3257 (by decide) (by decide) (by decide +kernel)
  decide +kernel

def seg : List (ℕ × ℕ) := [(1790, 360), (1791, 360), (2028, 60), (2029, 180), (2031, 180), (2047, 60), (3126, 60), (3127, 60), (3130, 360), (3131, 360), (3134, 180), (3135, 180), (3164, 120), (3165, 120), (3166, 360), (3167, 360), (3198, 180), (3199, 180), (3219, 90), (3220, 72), (3221, 360), (3223, 360), (3224, 360), (3225, 720), (3227, 360), (3228, 360), (3229, 720), (3231, 360), (3254, 180), (3255, 180), (3256, 360), (3257, 360)]

theorem segOK : checkSeg 20 perms 1790 3258 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 1790 3258 8562 29158608912 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 29158608912)
    (SegSum.cons (w := 360) h1790 (SegSum.cons (w := 360) h1791 (SegSum.cons (w := 60) h2028 (SegSum.cons (w := 180) h2029 (SegSum.cons (w := 180) h2031 (SegSum.cons (w := 60) h2047 (SegSum.cons (w := 60) h3126 (SegSum.cons (w := 60) h3127 (SegSum.cons (w := 360) h3130 (SegSum.cons (w := 360) h3131 (SegSum.cons (w := 180) h3134 (SegSum.cons (w := 180) h3135 (SegSum.cons (w := 120) h3164 (SegSum.cons (w := 120) h3165 (SegSum.cons (w := 360) h3166 (SegSum.cons (w := 360) h3167 (SegSum.cons (w := 180) h3198 (SegSum.cons (w := 180) h3199 (SegSum.cons (w := 90) h3219 (SegSum.cons (w := 72) h3220 (SegSum.cons (w := 360) h3221 (SegSum.cons (w := 360) h3223 (SegSum.cons (w := 360) h3224 (SegSum.cons (w := 720) h3225 (SegSum.cons (w := 360) h3227 (SegSum.cons (w := 360) h3228 (SegSum.cons (w := 720) h3229 (SegSum.cons (w := 360) h3231 (SegSum.cons (w := 180) h3254 (SegSum.cons (w := 180) h3255 (SegSum.cons (w := 360) h3256 (SegSum.cons (w := 360) h3257 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S5
