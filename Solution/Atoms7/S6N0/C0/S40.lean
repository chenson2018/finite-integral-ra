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

namespace RACert.S6N0.C0.S40

open RACert RACert.Problem

theorem cover78134 : P.CoversSplit 26 10 78134 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000200000000001000010000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [482, 489, 538, 629, 636, 930, 972, 1315, 1658]) (by decide +kernel)

theorem h78134 : P.leaf 36 78134 = 5476 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 78134) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 78134) (weight := fun _ => 1) (xs := [256, 276, 321, 341, 1023]) check rows elimOK (by decide) (by decide) cover78134 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover78135 : P.CoversSplit 26 10 78135 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000200000000001000010000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [482, 489, 538, 629, 636, 930, 972, 1315, 1658]) (by decide +kernel)

theorem h78135 : P.leaf 36 78135 = 46543 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 78135) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 78135) (weight := fun _ => 1) (xs := [256, 276, 321, 341, 1023]) check rows elimOK (by decide) (by decide) cover78135 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover78137 : P.CoversSplit 26 10 78137 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [474, 481, 482, 531, 636, 979, 1273, 1315, 1658]) (by decide +kernel)

theorem h78137 : P.leaf 36 78137 = 4096 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 78137) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 78137) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover78137 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover78139 : P.CoversSplit 26 10 78139 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 482, 531, 636, 979, 1273, 1315, 1658]) (by decide +kernel)

theorem h78139 : P.leaf 36 78139 = 28672 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 78139) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 78139) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover78139 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover78140 : P.CoversSplit 26 10 78140 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 531, 538, 580, 629, 636, 867, 972, 979, 1273, 1315, 1658]) (by decide +kernel)

theorem h78140 : P.leaf 36 78140 = 3184 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 78140) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 78140) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover78140 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover78141 : P.CoversSplit 26 10 78141 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 531, 538, 580, 629, 636, 972, 979, 1273, 1315, 1658]) (by decide +kernel)

theorem h78141 : P.leaf 36 78141 = 11632 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 78141) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 78141) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover78141 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover78142 : P.CoversSplit 26 10 78142 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 531, 538, 580, 629, 636, 867, 972, 979, 1273, 1315, 1658]) (by decide +kernel)

theorem h78142 : P.leaf 36 78142 = 28132 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 78142) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 78142) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover78142 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover78143 : P.CoversSplit 26 10 78143 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 531, 538, 580, 629, 636, 972, 979, 1273, 1315, 1658]) (by decide +kernel)

theorem h78143 : P.leaf 36 78143 = 137364 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 78143) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 78143) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover78143 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover78157 : P.CoversSplit 26 10 78157 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 523, 530, 531, 629, 636, 923, 972, 979, 1322, 1658, 1665]) (by decide +kernel)

theorem h78157 : P.leaf 36 78157 = 1344 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 78157) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 78157) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover78157 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover78158 : P.CoversSplit 26 10 78158 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 579, 629, 636, 873, 879, 972, 979, 1322, 1658]) (by decide +kernel)

theorem h78158 : P.leaf 36 78158 = 3584 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 78158) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 78158) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover78158 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover78159 : P.CoversSplit 26 10 78159 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 523, 530, 531, 629, 636, 923, 972, 979, 1322, 1658, 1665]) (by decide +kernel)

theorem h78159 : P.leaf 36 78159 = 18976 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 78159) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 78159) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover78159 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover78172 : P.CoversSplit 26 10 78172 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 479, 530, 531, 629, 636, 867, 972, 979, 1322, 1658]) (by decide +kernel)

theorem h78172 : P.leaf 36 78172 = 2048 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 78172) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 78172) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover78172 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover78173 : P.CoversSplit 26 10 78173 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 579, 629, 636, 923, 972, 979, 1322, 1658, 1665]) (by decide +kernel)

theorem h78173 : P.leaf 36 78173 = 10544 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 78173) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 78173) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover78173 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover78174 : P.CoversSplit 26 10 78174 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 579, 629, 636, 867, 873, 972, 979, 1322, 1658]) (by decide +kernel)

theorem h78174 : P.leaf 36 78174 = 28672 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 78174) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 78174) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover78174 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover78175 : P.CoversSplit 26 10 78175 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 579, 629, 636, 923, 972, 979, 1322, 1658, 1665]) (by decide +kernel)

theorem h78175 : P.leaf 36 78175 = 246112 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 78175) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 78175) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover78175 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover78189 : P.CoversSplit 26 10 78189 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 579, 580, 629, 636, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h78189 : P.leaf 36 78189 = 8192 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 78189) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 78189) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover78189 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover78190 : P.CoversSplit 26 10 78190 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 579, 580, 629, 636, 873, 879, 972, 979, 1315, 1322, 1658]) (by decide +kernel)

theorem h78190 : P.leaf 36 78190 = 14008 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 78190) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 78190) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover78190 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover78191 : P.CoversSplit 26 10 78191 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 579, 580, 629, 636, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h78191 : P.leaf 36 78191 = 117242 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 78191) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 78191) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover78191 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover78206 : P.CoversSplit 26 10 78206 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 579, 580, 629, 636, 867, 873, 972, 979, 1315, 1322, 1658]) (by decide +kernel)

theorem h78206 : P.leaf 36 78206 = 134384 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 78206) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 78206) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover78206 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover78207 : P.CoversSplit 26 10 78207 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 579, 580, 629, 636, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem h78207 : P.leaf 36 78207 = 1760787 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 78207) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 78207) (weight := fun _ => 1) (xs := [768, 1023]) check rows elimOK (by decide) (by decide) cover78207 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover78245 : P.CoversSplit 26 10 78245 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000000000000001000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [433, 482, 489, 538, 629, 636, 930, 972, 979, 1315, 1658]) (ps := [(15, [872], [559])]) (by decide +kernel)

theorem h78245 : P.leaf 36 78245 = 5020 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 78245) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 78245) (weight := fun _ => 1) (xs := [276, 341, 1023]) check rows elimOK (by decide) (by decide) cover78245 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover99539 : P.CoversSplit 26 10 99539 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000110000000000000000000000000000000000000000000000000000000000000010 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 530, 587, 608, 629, 636, 873, 881, 922]) (by decide +kernel)

theorem h99539 : P.leaf 36 99539 = 5252 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 99539) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 99539) (weight := fun _ => 1) (xs := [4, 256, 260, 1023]) check rows elimOK (by decide) (by decide) cover99539 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h78246 : P.leaf 36 78246 = 5252 :=
  orient72 (v := 99539) (by decide) (by decide +kernel) h99539

theorem cover78247 : P.CoversSplit 26 10 78247 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000200000000001000010000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 482, 489, 538, 629, 636, 930, 972, 1315, 1658]) (by decide +kernel)

theorem h78247 : P.leaf 36 78247 = 32924 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 78247) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 78247) (weight := fun _ => 1) (xs := [256, 276, 321, 341, 1023]) check rows elimOK (by decide) (by decide) cover78247 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover78249 : P.CoversSplit 26 10 78249 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 481, 482, 531, 629, 636, 972, 979, 1273, 1315, 1658]) (by decide +kernel)

theorem h78249 : P.leaf 36 78249 = 5120 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 78249) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 78249) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover78249 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover78251 : P.CoversSplit 26 10 78251 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 481, 482, 531, 629, 636, 972, 979, 1273, 1315, 1658]) (by decide +kernel)

theorem h78251 : P.leaf 36 78251 = 14368 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 78251) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 78251) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover78251 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover78253 : P.CoversSplit 26 10 78253 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 531, 538, 629, 636, 874, 972, 979, 1273, 1315, 1658]) (by decide +kernel)

theorem h78253 : P.leaf 36 78253 = 10240 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 78253) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 78253) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover78253 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover78254 : P.CoversSplit 26 10 78254 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 531, 538, 629, 636, 874, 972, 979, 1273, 1315, 1658]) (by decide +kernel)

theorem h78254 : P.leaf 36 78254 = 13952 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 78254) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 78254) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover78254 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover78255 : P.CoversSplit 26 10 78255 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 531, 538, 629, 636, 874, 972, 979, 1273, 1315, 1658]) (by decide +kernel)

theorem h78255 : P.leaf 36 78255 = 69488 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 78255) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 78255) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover78255 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover78262 : P.CoversSplit 26 10 78262 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000200000000001000010000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 482, 489, 538, 629, 636, 930, 972, 1315, 1658]) (by decide +kernel)

theorem h78262 : P.leaf 36 78262 = 19391 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 78262) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 78262) (weight := fun _ => 1) (xs := [256, 276, 321, 341, 1023]) check rows elimOK (by decide) (by decide) cover78262 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover78263 : P.CoversSplit 26 10 78263 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000200000000001000010000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 482, 489, 538, 629, 636, 930, 972, 1315, 1658]) (by decide +kernel)

theorem h78263 : P.leaf 36 78263 = 161699 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 78263) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 78263) (weight := fun _ => 1) (xs := [256, 276, 321, 341, 1023]) check rows elimOK (by decide) (by decide) cover78263 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover78265 : P.CoversSplit 26 10 78265 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 481, 482, 531, 629, 636, 972, 979, 1273, 1315, 1658]) (by decide +kernel)

theorem h78265 : P.leaf 36 78265 = 24128 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 78265) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 78265) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover78265 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover78267 : P.CoversSplit 26 10 78267 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 481, 482, 531, 629, 636, 972, 979, 1273, 1315, 1658]) (by decide +kernel)

theorem h78267 : P.leaf 36 78267 = 78016 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 78267) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 78267) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover78267 (by decide) (by decide) (by decide +kernel)
  decide +kernel

def seg : List (ℕ × ℕ) := [(78134, 180), (78135, 360), (78137, 720), (78139, 720), (78140, 720), (78141, 720), (78142, 720), (78143, 720), (78157, 720), (78158, 720), (78159, 720), (78172, 720), (78173, 720), (78174, 720), (78175, 720), (78189, 360), (78190, 720), (78191, 720), (78206, 360), (78207, 360), (78245, 360), (78246, 360), (78247, 720), (78249, 720), (78251, 720), (78253, 720), (78254, 720), (78255, 720), (78262, 180), (78263, 360), (78265, 720), (78267, 720)]

theorem segOK : checkSeg 20 perms 78134 78268 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 78134 78268 19440 1419120900 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 1419120900)
    (SegSum.cons (w := 180) h78134 (SegSum.cons (w := 360) h78135 (SegSum.cons (w := 720) h78137 (SegSum.cons (w := 720) h78139 (SegSum.cons (w := 720) h78140 (SegSum.cons (w := 720) h78141 (SegSum.cons (w := 720) h78142 (SegSum.cons (w := 720) h78143 (SegSum.cons (w := 720) h78157 (SegSum.cons (w := 720) h78158 (SegSum.cons (w := 720) h78159 (SegSum.cons (w := 720) h78172 (SegSum.cons (w := 720) h78173 (SegSum.cons (w := 720) h78174 (SegSum.cons (w := 720) h78175 (SegSum.cons (w := 360) h78189 (SegSum.cons (w := 720) h78190 (SegSum.cons (w := 720) h78191 (SegSum.cons (w := 360) h78206 (SegSum.cons (w := 360) h78207 (SegSum.cons (w := 360) h78245 (SegSum.cons (w := 360) h78246 (SegSum.cons (w := 720) h78247 (SegSum.cons (w := 720) h78249 (SegSum.cons (w := 720) h78251 (SegSum.cons (w := 720) h78253 (SegSum.cons (w := 720) h78254 (SegSum.cons (w := 720) h78255 (SegSum.cons (w := 180) h78262 (SegSum.cons (w := 360) h78263 (SegSum.cons (w := 720) h78265 (SegSum.cons (w := 720) h78267 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S40
