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

namespace RACert.S6N0.C0.S44

open RACert RACert.Problem

theorem cover79165 : P.CoversSplit 26 10 79165 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 531, 538, 580, 629, 636, 972, 979, 1273, 1315, 1658]) (by decide +kernel)

theorem h79165 : P.leaf 36 79165 = 238852 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 79165) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 79165) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover79165 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover79167 : P.CoversSplit 26 10 79167 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 531, 538, 580, 629, 636, 972, 979, 1273, 1315, 1658]) (by decide +kernel)

theorem h79167 : P.leaf 36 79167 = 770884 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 79167) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 79167) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover79167 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover79196 : P.CoversSplit 26 10 79196 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 479, 530, 531, 629, 636, 972, 979, 1322, 1658, 1665]) (by decide +kernel)

theorem h79196 : P.leaf 36 79196 = 81920 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 79196) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 79196) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover79196 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover79197 : P.CoversSplit 26 10 79197 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 579, 629, 636, 923, 972, 979, 1322, 1658, 1665]) (by decide +kernel)

theorem h79197 : P.leaf 36 79197 = 260608 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 79197) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 79197) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover79197 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover79198 : P.CoversSplit 26 10 79198 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 579, 629, 636, 873, 972, 979, 1322, 1658, 1665]) (by decide +kernel)

theorem h79198 : P.leaf 36 79198 = 231552 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 79198) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 79198) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover79198 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover79199 : P.CoversSplit 26 10 79199 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 579, 629, 636, 923, 972, 979, 1322, 1658, 1665]) (by decide +kernel)

theorem h79199 : P.leaf 36 79199 = 853504 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 79199) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 79199) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover79199 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover79212 : P.CoversSplit 26 10 79212 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 579, 580, 629, 636, 873, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h79212 : P.leaf 36 79212 = 124056 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 79212) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 79212) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover79212 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover79213 : P.CoversSplit 26 10 79213 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 579, 580, 629, 636, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h79213 : P.leaf 36 79213 = 153132 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 79213) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 79213) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover79213 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover79214 : P.CoversSplit 26 10 79214 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 579, 580, 629, 636, 873, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h79214 : P.leaf 36 79214 = 559542 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 79214) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 79214) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover79214 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover79215 : P.CoversSplit 26 10 79215 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 579, 580, 629, 636, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h79215 : P.leaf 36 79215 = 775504 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 79215) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 79215) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover79215 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover79230 : P.CoversSplit 26 10 79230 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 579, 580, 629, 636, 873, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h79230 : P.leaf 36 79230 = 1942709 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 79230) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 79230) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover79230 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover79231 : P.CoversSplit 26 10 79231 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 579, 580, 629, 636, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h79231 : P.leaf 36 79231 = 2958212 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 79231) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 79231) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover79231 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover79269 : P.CoversSplit 26 10 79269 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000200000000001000010000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 482, 489, 538, 629, 636, 930, 972, 979, 1315, 1658]) (by decide +kernel)

theorem h79269 : P.leaf 36 79269 = 68444 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 79269) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 79269) (weight := fun _ => 1) (xs := [256, 276, 321, 341, 1023]) check rows elimOK (by decide) (by decide) cover79269 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover79271 : P.CoversSplit 26 10 79271 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000200000000001000010000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 482, 489, 538, 629, 636, 930, 972, 1315, 1658]) (by decide +kernel)

theorem h79271 : P.leaf 36 79271 = 231996 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 79271) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 79271) (weight := fun _ => 1) (xs := [256, 276, 321, 341, 1023]) check rows elimOK (by decide) (by decide) cover79271 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover79276 : P.CoversSplit 26 10 79276 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 531, 538, 566, 629, 636, 972, 979, 1273, 1315, 1658]) (by decide +kernel)

theorem h79276 : P.leaf 36 79276 = 39664 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 79276) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 79276) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover79276 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover79277 : P.CoversSplit 26 10 79277 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 531, 538, 566, 629, 636, 972, 979, 1273, 1315, 1658]) (by decide +kernel)

theorem h79277 : P.leaf 36 79277 = 249636 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 79277) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 79277) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover79277 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover79278 : P.CoversSplit 26 10 79278 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 531, 538, 629, 636, 874, 972, 979, 1273, 1315, 1658]) (by decide +kernel)

theorem h79278 : P.leaf 36 79278 = 75048 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 79278) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 79278) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover79278 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover79279 : P.CoversSplit 26 10 79279 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 531, 538, 629, 636, 874, 972, 979, 1273, 1315, 1658]) (by decide +kernel)

theorem h79279 : P.leaf 36 79279 = 473696 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 79279) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 79279) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover79279 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover79287 : P.CoversSplit 26 10 79287 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000200000000001000010000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 482, 489, 538, 629, 636, 930, 972, 1315, 1658]) (by decide +kernel)

theorem h79287 : P.leaf 36 79287 = 914628 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 79287) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 79287) (weight := fun _ => 1) (xs := [256, 276, 321, 341, 1023]) check rows elimOK (by decide) (by decide) cover79287 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover79292 : P.CoversSplit 26 10 79292 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 531, 538, 629, 636, 874, 972, 979, 1273, 1315, 1658]) (by decide +kernel)

theorem h79292 : P.leaf 36 79292 = 320956 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 79292) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 79292) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover79292 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover79293 : P.CoversSplit 26 10 79293 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 531, 538, 629, 636, 874, 972, 979, 1273, 1315, 1658]) (by decide +kernel)

theorem h79293 : P.leaf 36 79293 = 943900 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 79293) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 79293) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover79293 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover79294 : P.CoversSplit 26 10 79294 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 531, 538, 629, 636, 874, 972, 979, 1273, 1315, 1658]) (by decide +kernel)

theorem h79294 : P.leaf 36 79294 = 605376 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 79294) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 79294) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover79294 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover79295 : P.CoversSplit 26 10 79295 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 531, 538, 629, 636, 874, 972, 979, 1273, 1315, 1658]) (by decide +kernel)

theorem h79295 : P.leaf 36 79295 = 1988188 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 79295) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 79295) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover79295 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover79308 : P.CoversSplit 26 10 79308 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 467, 531, 629, 636, 972, 979, 1322, 1658, 1665]) (by decide +kernel)

theorem h79308 : P.leaf 36 79308 = 53960 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 79308) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 79308) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover79308 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover79309 : P.CoversSplit 26 10 79309 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 629, 636, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h79309 : P.leaf 36 79309 = 230856 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 79309) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 79309) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover79309 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover79310 : P.CoversSplit 26 10 79310 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 629, 636, 873, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h79310 : P.leaf 36 79310 = 95864 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 79310) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 79310) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover79310 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover79311 : P.CoversSplit 26 10 79311 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 629, 636, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h79311 : P.leaf 36 79311 = 440632 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 79311) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 79311) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover79311 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover79324 : P.CoversSplit 26 10 79324 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 467, 531, 629, 636, 972, 979, 1322, 1658, 1665]) (by decide +kernel)

theorem h79324 : P.leaf 36 79324 = 670560 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 79324) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 79324) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover79324 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover79325 : P.CoversSplit 26 10 79325 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 629, 636, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h79325 : P.leaf 36 79325 = 1085992 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 79325) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 79325) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover79325 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover79326 : P.CoversSplit 26 10 79326 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 629, 636, 873, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h79326 : P.leaf 36 79326 = 1148064 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 79326) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 79326) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover79326 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover79327 : P.CoversSplit 26 10 79327 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 629, 636, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h79327 : P.leaf 36 79327 = 2050886 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 79327) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 79327) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover79327 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover79340 : P.CoversSplit 26 10 79340 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 873, 874, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h79340 : P.leaf 36 79340 = 1098268 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 79340) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 79340) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover79340 (by decide) (by decide) (by decide +kernel)
  decide +kernel

def seg : List (ℕ × ℕ) := [(79165, 720), (79167, 360), (79196, 720), (79197, 720), (79198, 720), (79199, 720), (79212, 360), (79213, 360), (79214, 720), (79215, 720), (79230, 360), (79231, 360), (79269, 180), (79271, 360), (79276, 720), (79277, 720), (79278, 720), (79279, 720), (79287, 180), (79292, 720), (79293, 720), (79294, 720), (79295, 720), (79308, 720), (79309, 720), (79310, 720), (79311, 720), (79324, 720), (79325, 720), (79326, 720), (79327, 720), (79340, 360)]

theorem segOK : checkSeg 20 perms 79165 79341 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 79165 79341 19440 12499312680 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 12499312680)
    (SegSum.cons (w := 720) h79165 (SegSum.cons (w := 360) h79167 (SegSum.cons (w := 720) h79196 (SegSum.cons (w := 720) h79197 (SegSum.cons (w := 720) h79198 (SegSum.cons (w := 720) h79199 (SegSum.cons (w := 360) h79212 (SegSum.cons (w := 360) h79213 (SegSum.cons (w := 720) h79214 (SegSum.cons (w := 720) h79215 (SegSum.cons (w := 360) h79230 (SegSum.cons (w := 360) h79231 (SegSum.cons (w := 180) h79269 (SegSum.cons (w := 360) h79271 (SegSum.cons (w := 720) h79276 (SegSum.cons (w := 720) h79277 (SegSum.cons (w := 720) h79278 (SegSum.cons (w := 720) h79279 (SegSum.cons (w := 180) h79287 (SegSum.cons (w := 720) h79292 (SegSum.cons (w := 720) h79293 (SegSum.cons (w := 720) h79294 (SegSum.cons (w := 720) h79295 (SegSum.cons (w := 720) h79308 (SegSum.cons (w := 720) h79309 (SegSum.cons (w := 720) h79310 (SegSum.cons (w := 720) h79311 (SegSum.cons (w := 720) h79324 (SegSum.cons (w := 720) h79325 (SegSum.cons (w := 720) h79326 (SegSum.cons (w := 720) h79327 (SegSum.cons (w := 360) h79340 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S44
