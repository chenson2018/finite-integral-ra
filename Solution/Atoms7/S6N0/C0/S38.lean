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

namespace RACert.S6N0.C0.S38

open RACert RACert.Problem

theorem cover76983 : P.CoversSplit 26 10 76983 0x8000000000000000000000000000000000000000000000000000000000000000cc00cc0000000000cc00cc00000000000000000000000000000000000000000000000000000000000000000000000000000000000033003300000000003300330000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 538, 587, 629, 636, 881, 972, 1315, 1658, 2008]) (by decide +kernel)

noncomputable def f76983 (i : ℕ) := rowWeight keep9 twice9 i * P.leaf 26 (78830592 + i)

theorem c76983_0 : rowSum f76983 0 1024 = 52390304 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 76983) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover76983 (by decide)
  decide +kernel

theorem sum76983 : rowSum f76983 0 1024 = 52390304 :=
  c76983_0

theorem h76983 : P.leaf 36 76983 = 52390304 :=
  leaf_weighted (k := 26) (d := 10) (H := 76983) (keep := keep9) (twice := twice9) rows (by decide) (by decide) (bal9) (invRow9 (H := 76983) (by decide) (by decide +kernel)) sum76983

theorem cover77331 : P.CoversSplit 26 10 77331 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030000000000000000000000000000000000000000000000000000000000000003 :=
  coversProjected check rows (by decide) (by decide) (xs := [481, 489, 530, 538, 579, 587, 608, 881, 979]) (ps := [(13, [510], [972])]) (by decide +kernel)

theorem h77331 : P.leaf 36 77331 = 23983 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 77331) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 77331) (weight := fun _ => 1) (xs := [0, 1, 256, 257, 1023]) check rows elimOK (by decide) (by decide) cover77331 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h76984 : P.leaf 36 76984 = 23983 :=
  orient84 (v := 77331) (by decide) (by decide +kernel) h77331

theorem cover76988 : P.CoversSplit 26 10 76988 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000021002100000000002100210000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 531, 538, 587, 629, 636, 881, 972, 979, 1315, 1658]) (by decide +kernel)

theorem h76988 : P.leaf 36 76988 = 30223 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 76988) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 76988) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 76988) (weight := rowWeight keep1 twice1) (xs := [256, 261, 272, 277, 320, 325, 336, 341, 1023]) check rows elimOK (by decide) (by decide) cover76988 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h76985 : P.leaf 36 76985 = 30223 :=
  orient72 (v := 76988) (by decide) (by decide +kernel) h76988

theorem cover76987 : P.CoversSplit 26 10 76987 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000021002100000000002100210000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 531, 538, 587, 629, 636, 881, 972, 1315, 1658]) (by decide +kernel)

theorem h76987 : P.leaf 36 76987 = 43049 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 76987) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 76987) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 76987) (weight := rowWeight keep1 twice1) (xs := [256, 261, 272, 277, 320, 325, 336, 341, 1023]) check rows elimOK (by decide) (by decide) cover76987 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover76991 : P.CoversSplit 26 10 76991 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000021002100000000002100210000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 531, 538, 587, 629, 636, 881, 972, 1315, 1658]) (by decide +kernel)

theorem h76991 : P.leaf 36 76991 = 65523 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 76991) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 76991) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 76991) (weight := rowWeight keep1 twice1) (xs := [256, 261, 272, 277, 320, 325, 336, 341, 1023]) check rows elimOK (by decide) (by decide) cover76991 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover77000 : P.CoversSplit 26 10 77000 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [475, 481, 482, 530, 580, 587, 629, 930, 972, 1273, 1315, 1658]) (by decide +kernel)

theorem h77000 : P.leaf 36 77000 = 64 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 77000) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 77000) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover77000 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover77001 : P.CoversSplit 26 10 77001 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [475, 481, 482, 580, 587, 629, 930, 972, 1273, 1315, 1658]) (by decide +kernel)

theorem h77001 : P.leaf 36 77001 = 1024 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 77001) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 77001) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover77001 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover77002 : P.CoversSplit 26 10 77002 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 482, 524, 530, 580, 587, 629, 930, 972, 1273, 1315, 1658]) (by decide +kernel)

theorem h77002 : P.leaf 36 77002 = 512 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 77002) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 77002) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover77002 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover77003 : P.CoversSplit 26 10 77003 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 482, 524, 530, 580, 587, 629, 930, 972, 1273, 1315, 1658]) (by decide +kernel)

theorem h77003 : P.leaf 36 77003 = 4096 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 77003) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 77003) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover77003 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover77006 : P.CoversSplit 26 10 77006 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 524, 530, 531, 580, 587, 629, 930, 972, 1273, 1315, 1658]) (by decide +kernel)

theorem h77006 : P.leaf 36 77006 = 2352 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 77006) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 77006) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover77006 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover77007 : P.CoversSplit 26 10 77007 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 524, 530, 531, 580, 587, 629, 930, 972, 1273, 1315, 1658]) (by decide +kernel)

theorem h77007 : P.leaf 36 77007 = 25952 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 77007) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 77007) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover77007 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover77018 : P.CoversSplit 26 10 77018 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 482, 530, 580, 587, 629, 930, 972, 1273, 1315, 1658]) (by decide +kernel)

theorem h77018 : P.leaf 36 77018 = 8192 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 77018) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 77018) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover77018 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover77019 : P.CoversSplit 26 10 77019 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 482, 580, 587, 629, 930, 972, 1273, 1315, 1658]) (by decide +kernel)

theorem h77019 : P.leaf 36 77019 = 32768 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 77019) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 77019) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover77019 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover77020 : P.CoversSplit 26 10 77020 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 475, 530, 531, 580, 587, 629, 930, 972, 1273, 1315, 1658]) (by decide +kernel)

theorem h77020 : P.leaf 36 77020 = 6656 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 77020) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 77020) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover77020 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover77021 : P.CoversSplit 26 10 77021 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 475, 530, 531, 580, 587, 629, 930, 972, 1273, 1315, 1658]) (by decide +kernel)

theorem h77021 : P.leaf 36 77021 = 24064 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 77021) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 77021) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover77021 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover77022 : P.CoversSplit 26 10 77022 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 580, 587, 629, 930, 972, 1273, 1315, 1658]) (by decide +kernel)

theorem h77022 : P.leaf 36 77022 = 21504 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 77022) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 77022) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover77022 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover77023 : P.CoversSplit 26 10 77023 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 580, 587, 629, 930, 972, 1273, 1315, 1658]) (by decide +kernel)

theorem h77023 : P.leaf 36 77023 = 88256 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 77023) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 77023) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover77023 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover77054 : P.CoversSplit 26 10 77054 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 580, 587, 629, 636, 881, 930, 972, 1273, 1315, 1658]) (by decide +kernel)

theorem h77054 : P.leaf 36 77054 = 66376 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 77054) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 77054) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover77054 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover77055 : P.CoversSplit 26 10 77055 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 580, 587, 629, 636, 881, 930, 972, 1273, 1315, 1658]) (by decide +kernel)

theorem h77055 : P.leaf 36 77055 = 264640 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 77055) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 77055) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover77055 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover77128 : P.CoversSplit 26 10 77128 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000500000000000000000000000000000000000000000500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 482, 530, 579, 629, 636, 972, 979, 1322, 1665]) (by decide +kernel)

theorem h77128 : P.leaf 36 77128 = 23983 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 77128) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 77128) (weight := fun _ => 1) (xs := [512, 514, 680, 682, 1023]) check rows elimOK (by decide) (by decide) cover77128 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover77129 : P.CoversSplit 26 10 77129 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [474, 481, 482, 530, 579, 629, 636, 972, 979, 1322, 1665]) (by decide +kernel)

theorem h77129 : P.leaf 36 77129 = 1024 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 77129) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 77129) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover77129 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover77131 : P.CoversSplit 26 10 77131 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 482, 523, 530, 579, 629, 636, 972, 979, 1322, 1665]) (by decide +kernel)

theorem h77131 : P.leaf 36 77131 = 8192 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 77131) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 77131) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover77131 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover301443 : P.CoversSplit 26 10 301443 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 482, 488, 489, 530, 538, 629, 636, 922, 930]) (by decide +kernel)

theorem h301443 : P.leaf 36 301443 = 848 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 301443) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 301443) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover301443 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h77132 : P.leaf 36 77132 = 848 :=
  orient80 (v := 301443) (by decide) (by decide +kernel) h301443

theorem cover77133 : P.CoversSplit 26 10 77133 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 579, 629, 636, 880, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h77133 : P.leaf 36 77133 = 9656 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 77133) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 77133) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover77133 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover77135 : P.CoversSplit 26 10 77135 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 579, 629, 636, 880, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h77135 : P.leaf 36 77135 = 101656 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 77135) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 77135) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover77135 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover77147 : P.CoversSplit 26 10 77147 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000500000000000000000000000000000000000000000500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 482, 530, 579, 629, 636, 972, 979, 1322, 1665]) (by decide +kernel)

theorem h77147 : P.leaf 36 77147 = 68768 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 77147) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 77147) (weight := fun _ => 1) (xs := [512, 514, 680, 682, 1023]) check rows elimOK (by decide) (by decide) cover77147 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover77148 : P.CoversSplit 26 10 77148 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 629, 636, 880, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h77148 : P.leaf 36 77148 = 13120 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 77148) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 77148) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover77148 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover77149 : P.CoversSplit 26 10 77149 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 579, 629, 636, 880, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h77149 : P.leaf 36 77149 = 96184 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 77149) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 77149) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover77149 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover77151 : P.CoversSplit 26 10 77151 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 629, 636, 880, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h77151 : P.leaf 36 77151 = 630212 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 77151) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 77151) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover77151 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover77164 : P.CoversSplit 26 10 77164 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 579, 580, 629, 636, 874, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h77164 : P.leaf 36 77164 = 6784 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 77164) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 77164) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover77164 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover77165 : P.CoversSplit 26 10 77165 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 579, 580, 629, 636, 874, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h77165 : P.leaf 36 77165 = 34712 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 77165) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 77165) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover77165 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover77166 : P.CoversSplit 26 10 77166 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 579, 580, 629, 636, 874, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h77166 : P.leaf 36 77166 = 75888 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 77166) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 77166) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover77166 (by decide) (by decide) (by decide +kernel)
  decide +kernel

def seg : List (ℕ × ℕ) := [(76983, 6), (76984, 60), (76985, 180), (76987, 180), (76991, 60), (77000, 180), (77001, 180), (77002, 720), (77003, 720), (77006, 360), (77007, 360), (77018, 360), (77019, 360), (77020, 360), (77021, 360), (77022, 720), (77023, 720), (77054, 180), (77055, 180), (77128, 60), (77129, 360), (77131, 360), (77132, 360), (77133, 720), (77135, 360), (77147, 120), (77148, 360), (77149, 720), (77151, 360), (77164, 360), (77165, 360), (77166, 720)]

theorem segOK : checkSeg 20 perms 76983 77167 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 76983 77167 11466 938311644 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 938311644)
    (SegSum.cons (w := 6) h76983 (SegSum.cons (w := 60) h76984 (SegSum.cons (w := 180) h76985 (SegSum.cons (w := 180) h76987 (SegSum.cons (w := 60) h76991 (SegSum.cons (w := 180) h77000 (SegSum.cons (w := 180) h77001 (SegSum.cons (w := 720) h77002 (SegSum.cons (w := 720) h77003 (SegSum.cons (w := 360) h77006 (SegSum.cons (w := 360) h77007 (SegSum.cons (w := 360) h77018 (SegSum.cons (w := 360) h77019 (SegSum.cons (w := 360) h77020 (SegSum.cons (w := 360) h77021 (SegSum.cons (w := 720) h77022 (SegSum.cons (w := 720) h77023 (SegSum.cons (w := 180) h77054 (SegSum.cons (w := 180) h77055 (SegSum.cons (w := 60) h77128 (SegSum.cons (w := 360) h77129 (SegSum.cons (w := 360) h77131 (SegSum.cons (w := 360) h77132 (SegSum.cons (w := 720) h77133 (SegSum.cons (w := 360) h77135 (SegSum.cons (w := 120) h77147 (SegSum.cons (w := 360) h77148 (SegSum.cons (w := 720) h77149 (SegSum.cons (w := 360) h77151 (SegSum.cons (w := 360) h77164 (SegSum.cons (w := 360) h77165 (SegSum.cons (w := 720) h77166 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S38
