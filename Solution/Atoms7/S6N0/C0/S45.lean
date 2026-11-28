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

namespace RACert.S6N0.C0.S45

open RACert RACert.Problem

theorem cover79341 : P.CoversSplit 26 10 79341 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 873, 874, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h79341 : P.leaf 36 79341 = 1280980 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 79341) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 79341) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover79341 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover79342 : P.CoversSplit 26 10 79342 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 873, 874, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h79342 : P.leaf 36 79342 = 2153662 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 79342) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 79342) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover79342 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover79343 : P.CoversSplit 26 10 79343 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 873, 874, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h79343 : P.leaf 36 79343 = 2861806 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 79343) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 79343) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover79343 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover79358 : P.CoversSplit 26 10 79358 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 873, 874, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h79358 : P.leaf 36 79358 = 5471645 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 79358) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 79358) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover79358 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover79359 : P.CoversSplit 26 10 79359 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 873, 874, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h79359 : P.leaf 36 79359 = 8222582 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 79359) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 79359) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover79359 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover79451 : P.CoversSplit 26 10 79451 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 579, 587, 622, 873, 930, 972, 1273, 1665]) (by decide +kernel)

theorem h79451 : P.leaf 36 79451 = 28280 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 79451) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 79451) (weight := fun _ => 1) (xs := [469, 1023]) check rows elimOK (by decide) (by decide) cover79451 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover80238 : P.CoversSplit 26 10 80238 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 579, 580, 629, 636, 879, 923, 972, 979, 1315, 1322, 1658]) (by decide +kernel)

theorem h80238 : P.leaf 36 80238 = 198336 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 80238) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 80238) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover80238 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h79454 : P.leaf 36 79454 = 198336 :=
  orient4 (v := 80238) (by decide) (by decide +kernel) h80238

theorem cover80239 : P.CoversSplit 26 10 80239 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 579, 580, 629, 636, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h80239 : P.leaf 36 80239 = 212668 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 80239) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 80239) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover80239 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h79455 : P.leaf 36 79455 = 212668 :=
  orient4 (v := 80239) (by decide) (by decide +kernel) h80239

theorem cover80254 : P.CoversSplit 26 10 80254 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 579, 580, 629, 636, 867, 923, 972, 979, 1315, 1322, 1658]) (by decide +kernel)

theorem h80254 : P.leaf 36 80254 = 1927200 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 80254) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 80254) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover80254 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h79486 : P.leaf 36 79486 = 1927200 :=
  orient4 (v := 80254) (by decide) (by decide +kernel) h80254

theorem cover80255 : P.CoversSplit 26 10 80255 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 579, 580, 629, 636, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h80255 : P.leaf 36 80255 = 2340579 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 80255) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 80255) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover80255 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h79487 : P.leaf 36 79487 = 2340579 :=
  orient4 (v := 80255) (by decide) (by decide +kernel) h80255

theorem cover80295 : P.CoversSplit 26 10 80295 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000200000000001000010000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 482, 489, 538, 629, 636, 930, 972, 1315, 1658]) (by decide +kernel)

theorem h80295 : P.leaf 36 80295 = 196496 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 80295) (keep := keep9) (twice := twice9) rows (by decide) (by decide) bal9 (invRow9 (H := 80295) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 80295) (weight := rowWeight keep9 twice9) (xs := [256, 276, 321, 341, 1023]) check rows elimOK (by decide) (by decide) cover80295 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h79511 : P.leaf 36 79511 = 196496 :=
  orient4 (v := 80295) (by decide) (by decide +kernel) h80295

theorem cover80297 : P.CoversSplit 26 10 80297 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 481, 482, 531, 629, 636, 972, 979, 1273, 1315, 1658]) (by decide +kernel)

theorem h80297 : P.leaf 36 80297 = 79360 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 80297) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 80297) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover80297 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h79513 : P.leaf 36 79513 = 79360 :=
  orient4 (v := 80297) (by decide) (by decide +kernel) h80297

theorem cover80301 : P.CoversSplit 26 10 80301 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 531, 538, 629, 636, 930, 972, 979, 1273, 1315, 1658]) (by decide +kernel)

theorem h80301 : P.leaf 36 80301 = 144000 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 80301) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 80301) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover80301 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h79515 : P.leaf 36 79515 = 144000 :=
  orient4 (v := 80301) (by decide) (by decide +kernel) h80301

theorem cover80299 : P.CoversSplit 26 10 80299 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 481, 482, 531, 629, 636, 972, 979, 1273, 1315, 1658]) (by decide +kernel)

theorem h80299 : P.leaf 36 80299 = 317232 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 80299) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 80299) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover80299 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h79517 : P.leaf 36 79517 = 317232 :=
  orient4 (v := 80299) (by decide) (by decide +kernel) h80299

theorem cover80303 : P.CoversSplit 26 10 80303 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 531, 538, 629, 636, 972, 979, 1273, 1315, 1658]) (by decide +kernel)

theorem h80303 : P.leaf 36 80303 = 375232 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 80303) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 80303) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover80303 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h79519 : P.leaf 36 79519 = 375232 :=
  orient4 (v := 80303) (by decide) (by decide +kernel) h80303

theorem cover80310 : P.CoversSplit 26 10 80310 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000200000000001000010000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 482, 489, 538, 629, 636, 930, 972, 1315, 1658]) (by decide +kernel)

theorem h80310 : P.leaf 36 80310 = 217244 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 80310) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 80310) (weight := fun _ => 1) (xs := [256, 276, 321, 341, 1023]) check rows elimOK (by decide) (by decide) cover80310 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h79542 : P.leaf 36 79542 = 217244 :=
  orient4 (v := 80310) (by decide) (by decide +kernel) h80310

theorem cover80311 : P.CoversSplit 26 10 80311 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000200000000001000010000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 482, 489, 538, 629, 636, 930, 972, 1315, 1658]) (by decide +kernel)

theorem h80311 : P.leaf 36 80311 = 777408 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 80311) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 80311) (weight := fun _ => 1) (xs := [256, 276, 321, 341, 1023]) check rows elimOK (by decide) (by decide) cover80311 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h79543 : P.leaf 36 79543 = 777408 :=
  orient4 (v := 80311) (by decide) (by decide +kernel) h80311

theorem cover80312 : P.CoversSplit 26 10 80312 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 481, 482, 531, 629, 636, 867, 972, 979, 1273, 1315, 1658]) (by decide +kernel)

theorem h80312 : P.leaf 36 80312 = 10752 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 80312) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 80312) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover80312 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h79544 : P.leaf 36 79544 = 10752 :=
  orient4 (v := 80312) (by decide) (by decide +kernel) h80312

theorem cover80313 : P.CoversSplit 26 10 80313 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 481, 482, 531, 629, 636, 972, 979, 1273, 1315, 1658]) (by decide +kernel)

theorem h80313 : P.leaf 36 80313 = 216480 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 80313) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 80313) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover80313 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h79545 : P.leaf 36 79545 = 216480 :=
  orient4 (v := 80313) (by decide) (by decide +kernel) h80313

theorem cover80316 : P.CoversSplit 26 10 80316 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 531, 538, 629, 636, 867, 972, 979, 1273, 1315, 1658]) (by decide +kernel)

theorem h80316 : P.leaf 36 80316 = 222112 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 80316) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 80316) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover80316 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h79546 : P.leaf 36 79546 = 222112 :=
  orient4 (v := 80316) (by decide) (by decide +kernel) h80316

theorem cover80317 : P.CoversSplit 26 10 80317 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 531, 538, 629, 636, 930, 972, 979, 1273, 1315, 1658]) (by decide +kernel)

theorem h80317 : P.leaf 36 80317 = 468904 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 80317) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 80317) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover80317 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h79547 : P.leaf 36 79547 = 468904 :=
  orient4 (v := 80317) (by decide) (by decide +kernel) h80317

theorem cover80314 : P.CoversSplit 26 10 80314 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 481, 482, 531, 629, 636, 867, 972, 979, 1273, 1315, 1658]) (by decide +kernel)

theorem h80314 : P.leaf 36 80314 = 427552 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 80314) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 80314) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover80314 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h79548 : P.leaf 36 79548 = 427552 :=
  orient4 (v := 80314) (by decide) (by decide +kernel) h80314

theorem cover80315 : P.CoversSplit 26 10 80315 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 481, 482, 531, 629, 636, 972, 979, 1273, 1315, 1658]) (by decide +kernel)

theorem h80315 : P.leaf 36 80315 = 906736 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 80315) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 80315) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover80315 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h79549 : P.leaf 36 79549 = 906736 :=
  orient4 (v := 80315) (by decide) (by decide +kernel) h80315

theorem cover80318 : P.CoversSplit 26 10 80318 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 531, 538, 629, 636, 867, 972, 979, 1273, 1315, 1658]) (by decide +kernel)

theorem h80318 : P.leaf 36 80318 = 694000 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 80318) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 80318) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover80318 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h79550 : P.leaf 36 79550 = 694000 :=
  orient4 (v := 80318) (by decide) (by decide +kernel) h80318

theorem cover80319 : P.CoversSplit 26 10 80319 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 531, 538, 629, 636, 972, 979, 1273, 1315, 1658]) (by decide +kernel)

theorem h80319 : P.leaf 36 80319 = 1278776 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 80319) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 80319) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover80319 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h79551 : P.leaf 36 79551 = 1278776 :=
  orient4 (v := 80319) (by decide) (by decide +kernel) h80319

theorem cover80329 : P.CoversSplit 26 10 80329 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 481, 482, 629, 636, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h80329 : P.leaf 36 80329 = 13056 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 80329) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 80329) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover80329 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h79561 : P.leaf 36 79561 = 13056 :=
  orient4 (v := 80329) (by decide) (by decide +kernel) h80329

theorem cover80333 : P.CoversSplit 26 10 80333 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 629, 636, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h80333 : P.leaf 36 80333 = 146112 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 80333) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 80333) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover80333 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h79563 : P.leaf 36 79563 = 146112 :=
  orient4 (v := 80333) (by decide) (by decide +kernel) h80333

theorem cover80330 : P.CoversSplit 26 10 80330 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 467, 482, 629, 636, 879, 923, 972, 979, 1315, 1322, 1658]) (by decide +kernel)

theorem h80330 : P.leaf 36 80330 = 83328 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 80330) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 80330) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover80330 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h79564 : P.leaf 36 79564 = 83328 :=
  orient4 (v := 80330) (by decide) (by decide +kernel) h80330

theorem cover80331 : P.CoversSplit 26 10 80331 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 481, 482, 530, 629, 636, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h80331 : P.leaf 36 80331 = 156336 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 80331) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 80331) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover80331 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h79565 : P.leaf 36 79565 = 156336 :=
  orient4 (v := 80331) (by decide) (by decide +kernel) h80331

theorem cover80334 : P.CoversSplit 26 10 80334 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 629, 636, 879, 923, 972, 979, 1315, 1322, 1658]) (by decide +kernel)

theorem h80334 : P.leaf 36 80334 = 111904 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 80334) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 80334) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover80334 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h79566 : P.leaf 36 79566 = 111904 :=
  orient4 (v := 80334) (by decide) (by decide +kernel) h80334

theorem cover80335 : P.CoversSplit 26 10 80335 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 629, 636, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h80335 : P.leaf 36 80335 = 405808 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 80335) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 80335) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover80335 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h79567 : P.leaf 36 79567 = 405808 :=
  orient4 (v := 80335) (by decide) (by decide +kernel) h80335

theorem cover80365 : P.CoversSplit 26 10 80365 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 923, 930, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h80365 : P.leaf 36 80365 = 314144 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 80365) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 80365) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover80365 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h79579 : P.leaf 36 79579 = 314144 :=
  orient4 (v := 80365) (by decide) (by decide +kernel) h80365

def seg : List (ℕ × ℕ) := [(79341, 360), (79342, 720), (79343, 720), (79358, 360), (79359, 360), (79451, 360), (79454, 720), (79455, 720), (79486, 360), (79487, 360), (79511, 360), (79513, 720), (79515, 720), (79517, 360), (79519, 360), (79542, 180), (79543, 360), (79544, 720), (79545, 720), (79546, 720), (79547, 720), (79548, 720), (79549, 720), (79550, 720), (79551, 720), (79561, 360), (79563, 720), (79564, 360), (79565, 720), (79566, 720), (79567, 720), (79579, 360)]

theorem segOK : checkSeg 20 perms 79341 79580 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 79341 79580 17820 15425061120 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 15425061120)
    (SegSum.cons (w := 360) h79341 (SegSum.cons (w := 720) h79342 (SegSum.cons (w := 720) h79343 (SegSum.cons (w := 360) h79358 (SegSum.cons (w := 360) h79359 (SegSum.cons (w := 360) h79451 (SegSum.cons (w := 720) h79454 (SegSum.cons (w := 720) h79455 (SegSum.cons (w := 360) h79486 (SegSum.cons (w := 360) h79487 (SegSum.cons (w := 360) h79511 (SegSum.cons (w := 720) h79513 (SegSum.cons (w := 720) h79515 (SegSum.cons (w := 360) h79517 (SegSum.cons (w := 360) h79519 (SegSum.cons (w := 180) h79542 (SegSum.cons (w := 360) h79543 (SegSum.cons (w := 720) h79544 (SegSum.cons (w := 720) h79545 (SegSum.cons (w := 720) h79546 (SegSum.cons (w := 720) h79547 (SegSum.cons (w := 720) h79548 (SegSum.cons (w := 720) h79549 (SegSum.cons (w := 720) h79550 (SegSum.cons (w := 720) h79551 (SegSum.cons (w := 360) h79561 (SegSum.cons (w := 720) h79563 (SegSum.cons (w := 360) h79564 (SegSum.cons (w := 720) h79565 (SegSum.cons (w := 720) h79566 (SegSum.cons (w := 720) h79567 (SegSum.cons (w := 360) h79579 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S45
