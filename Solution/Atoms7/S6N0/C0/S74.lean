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

namespace RACert.S6N0.C0.S74

open RACert RACert.Problem

theorem cover98115 : P.CoversSplit 26 10 98115 0xa0000000a00000000000000000000000a0000000a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 523, 530, 579, 608, 972, 979, 1266]) (by decide +kernel)

noncomputable def f98115 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 26 (100469760 + i)

theorem c98115_0 : rowSum f98115 0 1024 = 10602376 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 98115) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover98115 (by decide)
  decide +kernel

theorem sum98115 : rowSum f98115 0 1024 = 10602376 :=
  c98115_0

theorem h98115 : P.leaf 36 98115 = 10602376 :=
  leaf_weighted (k := 26) (d := 10) (H := 98115) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 98115) (by decide) (by decide +kernel)) sum98115

theorem cover98117 : P.CoversSplit 26 10 98117 0xff000000ff0005000000000000000000ff000000ff0305000500000005000500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003300010000000000010001000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 579, 923, 972, 979, 1266, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c98117_0 : P.sumLeaves 26 100471808 1024 = 9149809 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98117) (lo := 0) (len := 1024) (W := 9149809) check rows elimOK (by decide) (by decide) cover98117 (by decide)
  decide +kernel

theorem h98117 : P.leaf 36 98117 = 9149809 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 9149809)]) (.cons c98117_0 (.nil)) (by decide) (by decide))

theorem cover98119 : P.CoversSplit 26 10 98119 0xff000000ff0005000000000000000000ff000000ff0305000500000005000500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003300010000000000010001000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 579, 972, 979, 1266, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f98119 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 26 (100473856 + i)

theorem c98119_0 : rowSum f98119 0 1024 = 128653387 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 98119) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover98119 (by decide)
  decide +kernel

theorem sum98119 : rowSum f98119 0 1024 = 128653387 :=
  c98119_0

theorem h98119 : P.leaf 36 98119 = 128653387 :=
  leaf_weighted (k := 26) (d := 10) (H := 98119) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 98119) (by decide) (by decide +kernel)) sum98119

theorem cover98123 : P.CoversSplit 26 10 98123 0xa0a00000a0a000000000000000000000a0a00000a0a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000a0a00000a0a000000000000000000000a0a00000a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 523, 530, 579, 972, 979]) (by decide +kernel)

noncomputable def f98123 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 26 (100477952 + i)

theorem c98123_0 : rowSum f98123 0 1024 = 63690598 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 98123) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover98123 (by decide)
  decide +kernel

theorem sum98123 : rowSum f98123 0 1024 = 63690598 :=
  c98123_0

theorem h98123 : P.leaf 36 98123 = 63690598 :=
  leaf_weighted (k := 26) (d := 10) (H := 98123) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 98123) (by decide) (by decide +kernel)) sum98123

theorem cover98125 : P.CoversSplit 26 10 98125 0xffff0000ffff05050000000000000000ffff0000fffc050005050000050005000000000000000000000000000000000000000000000000000000000000000000ffff0000ffff05050000000000000000ffff0000ff00050005050000050005000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 579, 923, 972, 979, 1266, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c98125_0 : P.sumLeaves 26 100480000 882 = 19856339 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98125) (lo := 0) (len := 882) (W := 19856339) check rows elimOK (by decide) (by decide) cover98125 (by decide)
  decide +kernel

theorem c98125_1 : P.sumLeaves 26 100480882 142 = 47932580 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98125) (lo := 882) (len := 142) (W := 47932580) check rows elimOK (by decide) (by decide) cover98125 (by decide)
  decide +kernel

theorem h98125 : P.leaf 36 98125 = 67788919 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(882, 19856339), (142, 47932580)]) (.cons c98125_0 (.cons c98125_1 (.nil))) (by decide) (by decide))

theorem cover98127 : P.CoversSplit 26 10 98127 0xffff0000ffff05050000000000000000ffff0000fffc050005050000050005000000000000000000000000000000000000000000000000000000000000000000ffff0000ffff05050000000000000000ffff0000ff00050005050000050005000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 579, 972, 979, 1266, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f98127 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 26 (100482048 + i)

theorem c98127_0 : rowSum f98127 0 1018 = 418887045 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 98127) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover98127 (by decide)
  decide +kernel

theorem c98127_1 : rowSum f98127 1018 6 = 63515156 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 98127) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover98127 (by decide)
  decide +kernel

theorem sum98127 : rowSum f98127 0 1024 = 482402201 :=
  rowSum_append (F := f98127) (lo := 0) (n := 1018) (m := 6) (A := 418887045) (B := 63515156) c98127_0 (c98127_1)

theorem h98127 : P.leaf 36 98127 = 482402201 :=
  leaf_weighted (k := 26) (d := 10) (H := 98127) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 98127) (by decide) (by decide +kernel)) sum98127

theorem cover98131 : P.CoversSplit 26 10 98131 0xa0000000a00000000000000000000000a0000000a0000000000000000000000000000000000000000000050000000500000000000000000000000500000005000000000000000000000000000000000000000000a000000000000000000000000000000000000000000000000000000000000000000000000000000000000500 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 530, 579, 608, 972, 979, 1315]) (by decide +kernel)

noncomputable def f98131 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 26 (100486144 + i)

theorem c98131_0 : rowSum f98131 0 1024 = 21536061 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 98131) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover98131 (by decide)
  decide +kernel

theorem sum98131 : rowSum f98131 0 1024 = 21536061 :=
  c98131_0

theorem h98131 : P.leaf 36 98131 = 21536061 :=
  leaf_weighted (k := 26) (d := 10) (H := 98131) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 98131) (by decide) (by decide +kernel)) sum98131

theorem cover98132 : P.CoversSplit 26 10 98132 0xff000000ff0005000000000000000000ff000000ff0305000500000005000500050005000500050005000000050000000500050005010500050000000500000000000000000000000000000000000000000000003300010000000000010001000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 874, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f98132 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 26 (100487168 + i)

theorem c98132_0 : rowSum f98132 0 1024 = 6525173 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 98132) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover98132 (by decide)
  decide +kernel

theorem sum98132 : rowSum f98132 0 1024 = 6525173 :=
  c98132_0

theorem h98132 : P.leaf 36 98132 = 6525173 :=
  leaf_weighted (k := 26) (d := 10) (H := 98132) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 98132) (by decide) (by decide +kernel)) sum98132

theorem cover98133 : P.CoversSplit 26 10 98133 0xff000000ff0005000000000000000000ff000000ff0305000500000005000500050005000500050005000000050000000500050005010500050000000500000000000000000000000000000000000000000000003300010000000000010001000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 579, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c98133_0 : P.sumLeaves 26 100488192 1024 = 96277938 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98133) (lo := 0) (len := 1024) (W := 96277938) check rows elimOK (by decide) (by decide) cover98133 (by decide)
  decide +kernel

theorem h98133 : P.leaf 36 98133 = 96277938 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 96277938)]) (.cons c98133_0 (.nil)) (by decide) (by decide))

theorem cover98135 : P.CoversSplit 26 10 98135 0xff000000ff0005000000000000000000ff000000ff0305000500000005000500050005000500050005000000050000000500050005010500050000000500000000000000000000000000000000000000000000003300010000000000010001000000000000000000000000000000000000000000010001000000000001000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f98135 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 26 (100490240 + i)

theorem c98135_0 : rowSum f98135 0 1024 = 201376273 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 98135) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover98135 (by decide)
  decide +kernel

theorem sum98135 : rowSum f98135 0 1024 = 201376273 :=
  c98135_0

theorem h98135 : P.leaf 36 98135 = 201376273 :=
  leaf_weighted (k := 26) (d := 10) (H := 98135) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 98135) (by decide) (by decide +kernel)) sum98135

theorem cover98137 : P.CoversSplit 26 10 98137 0xa0a00000a0a000000000000000000000a0a00000a0a0000000000000000000000000000000000000000005050000050500000000000000000000050500000500a0a00000a0a000000000000000000000a0a00000a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 579, 923, 972, 979]) (by decide +kernel)

theorem c98137_0 : P.sumLeaves 26 100492288 1024 = 49044523 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98137) (lo := 0) (len := 1024) (W := 49044523) check rows elimOK (by decide) (by decide) cover98137 (by decide)
  decide +kernel

theorem h98137 : P.leaf 36 98137 = 49044523 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 49044523)]) (.cons c98137_0 (.nil)) (by decide) (by decide))

theorem cover98139 : P.CoversSplit 26 10 98139 0xa0a00000a0a000000000000000000000a0a00000a0a0000000000000000000000000000000000000000005050000050500000000000000000000050500000500a0a00000a0a000000000000000000000a0a00000a000000000000000000000000000000000000000000005050000050500000000000000000000050500000500 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 579, 972, 979]) (by decide +kernel)

noncomputable def f98139 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 26 (100494336 + i)

theorem c98139_0 : rowSum f98139 0 1024 = 109142691 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 98139) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover98139 (by decide)
  decide +kernel

theorem sum98139 : rowSum f98139 0 1024 = 109142691 :=
  c98139_0

theorem h98139 : P.leaf 36 98139 = 109142691 :=
  leaf_weighted (k := 26) (d := 10) (H := 98139) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 98139) (by decide) (by decide +kernel)) sum98139

theorem cover98140 : P.CoversSplit 26 10 98140 0xffff0000ffff05050000000000000000ffff0000fffc050005050000050005000505050505050505050500000505000005050505050405000505000005000000ffff0000ffff05050000000000000000ffff0000ff00050005050000050005000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 874, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f98140 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 26 (100495360 + i)

theorem c98140_0 : rowSum f98140 0 881 = 52327418 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 98140) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover98140 (by decide)
  decide +kernel

theorem c98140_1 : rowSum f98140 881 143 = 129439630 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 98140) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover98140 (by decide)
  decide +kernel

theorem sum98140 : rowSum f98140 0 1024 = 181767048 :=
  rowSum_append (F := f98140) (lo := 0) (n := 881) (m := 143) (A := 52327418) (B := 129439630) c98140_0 (c98140_1)

theorem h98140 : P.leaf 36 98140 = 181767048 :=
  leaf_weighted (k := 26) (d := 10) (H := 98140) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 98140) (by decide) (by decide +kernel)) sum98140

theorem cover98141 : P.CoversSplit 26 10 98141 0xffff0000ffff05050000000000000000ffff0000fffc050005050000050005000505050505050505050500000505000005050505050405000505000005000000ffff0000ffff05050000000000000000ffff0000ff00050005050000050005000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 579, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c98141_0 : P.sumLeaves 26 100496384 698 = 59395946 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98141) (lo := 0) (len := 698) (W := 59395946) check rows elimOK (by decide) (by decide) cover98141 (by decide)
  decide +kernel

theorem c98141_1 : P.sumLeaves 26 100497082 326 = 303724557 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98141) (lo := 698) (len := 326) (W := 303724557) check rows elimOK (by decide) (by decide) cover98141 (by decide)
  decide +kernel

theorem h98141 : P.leaf 36 98141 = 363120503 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(698, 59395946), (326, 303724557)]) (.cons c98141_0 (.cons c98141_1 (.nil))) (by decide) (by decide))

theorem cover98143 : P.CoversSplit 26 10 98143 0xffff0000ffff05050000000000000000ffff0000fffc050005050000050005000505050505050505050500000505000005050505050405000505000005000000ffff0000ffff05050000000000000000ffff0000ff00050005050000050005000505050505050505050500000505000005050505050005000505000005000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f98143 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 26 (100498432 + i)

theorem c98143_0 : rowSum f98143 0 762 = 106983018 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 98143) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover98143 (by decide)
  decide +kernel

theorem c98143_1 : rowSum f98143 762 262 = 588975126 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 98143) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover98143 (by decide)
  decide +kernel

theorem sum98143 : rowSum f98143 0 1024 = 695958144 :=
  rowSum_append (F := f98143) (lo := 0) (n := 762) (m := 262) (A := 106983018) (B := 588975126) c98143_0 (c98143_1)

theorem h98143 : P.leaf 36 98143 = 695958144 :=
  leaf_weighted (k := 26) (d := 10) (H := 98143) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 98143) (by decide) (by decide +kernel)) sum98143

theorem cover98147 : P.CoversSplit 26 10 98147 0xf000f000f000f0000000000000000000f000f000f000f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000f000f00000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 579, 972, 979, 1266, 1273, 1658]) (by decide +kernel)

theorem c98147_0 : P.sumLeaves 26 100502528 320 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98147) (lo := 0) (len := 320) (W := 0) check rows elimOK (by decide) (by decide) cover98147 (by decide)
  decide +kernel

theorem contract98147_1 : P.leaf 32 1570357 = 434432 := by
  exact leaf_contract_factors (k := 32) (b := 21) (H := 1570357) (ss := [(2, 1, 482), (4, 1, 580), (5, 1, 586), (30, 1, 972), (33, 0, 979), (31, 1, 1273), (12, 0, 979), (9, 1, 480), (7, 1, 825), (18, 1, 880), (21, 1, 929)]) (ids := [1, 4, 6, 8, 9, 11, 12, 14, 15, 17, 18, 21, 22, 23, 25, 26, 27, 13, 20, 24, 30]) (cs := [1, 2, 1, 1, 3, 1, 4, 1, 5, 6, 0, 7, 8, 19, 9, 10, 1, 11, 12, 1, 20, 13, 14, 15, 21, 16, 17, 18, 1, 1, 22, 0]) (bs := [17, 4]) (W := 434432) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c98147_1 : P.sumLeaves 26 100502848 64 = 434432 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1570357) rows (by decide) (by decide)).symm.trans contract98147_1

theorem c98147_2 : P.sumLeaves 26 100502912 640 = 49504840 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98147) (lo := 384) (len := 640) (W := 49504840) check rows elimOK (by decide) (by decide) cover98147 (by decide)
  decide +kernel

theorem h98147 : P.leaf 36 98147 = 49939272 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(320, 0), (64, 434432), (640, 49504840)]) (.cons c98147_0 (.cons c98147_1 (.cons c98147_2 (.nil)))) (by decide) (by decide))

theorem cover98149 : P.CoversSplit 26 10 98149 0xff00ff00ff00fa000000000000000000ff00ff00ff03fa000500050005000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003300320000000000010000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 579, 923, 972, 979, 1266, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c98149_0 : P.sumLeaves 26 100504576 1024 = 23335469 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98149) (lo := 0) (len := 1024) (W := 23335469) check rows elimOK (by decide) (by decide) cover98149 (by decide)
  decide +kernel

theorem h98149 : P.leaf 36 98149 = 23335469 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 23335469)]) (.cons c98149_0 (.nil)) (by decide) (by decide))

theorem cover98150 : P.CoversSplit 26 10 98150 0xff00ff00ff00fa000000000000000000ff00ff00ff03fa000500050005000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003300320000000000010000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 579, 874, 972, 979, 1266, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c98150_0 : P.sumLeaves 26 100505600 1024 = 185607689 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98150) (lo := 0) (len := 1024) (W := 185607689) check rows elimOK (by decide) (by decide) cover98150 (by decide)
  decide +kernel

theorem h98150 : P.leaf 36 98150 = 185607689 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 185607689)]) (.cons c98150_0 (.nil)) (by decide) (by decide))

theorem cover98151 : P.CoversSplit 26 10 98151 0xff00ff00ff00fa000000000000000000ff00ff00ff03fa000500050005000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003300320000000000010000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 579, 972, 979, 1266, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c98151_0 : P.sumLeaves 26 100506624 1024 = 362491499 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98151) (lo := 0) (len := 1024) (W := 362491499) check rows elimOK (by decide) (by decide) cover98151 (by decide)
  decide +kernel

theorem h98151 : P.leaf 36 98151 = 362491499 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 362491499)]) (.cons c98151_0 (.nil)) (by decide) (by decide))

theorem cover98153 : P.CoversSplit 26 10 98153 0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0c000000005000000000000000000000000000000000000000000000000000000000000000000000000f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f000f00000000005000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 579, 923, 972, 979, 1315, 1322, 1658]) (by decide +kernel)

theorem c98153_0 : P.sumLeaves 26 100508672 974 = 14253260 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98153) (lo := 0) (len := 974) (W := 14253260) check rows elimOK (by decide) (by decide) cover98153 (by decide)
  decide +kernel

theorem c98153_1 : P.sumLeaves 26 100509646 50 = 19092796 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98153) (lo := 974) (len := 50) (W := 19092796) check rows elimOK (by decide) (by decide) cover98153 (by decide)
  decide +kernel

theorem h98153 : P.leaf 36 98153 = 33346056 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(974, 14253260), (50, 19092796)]) (.cons c98153_0 (.cons c98153_1 (.nil))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(98115, 180), (98117, 360), (98119, 360), (98123, 180), (98125, 360), (98127, 360), (98131, 360), (98132, 360), (98133, 720), (98135, 360), (98137, 360), (98139, 360), (98140, 360), (98141, 720), (98143, 360), (98147, 720), (98149, 720), (98150, 720), (98151, 720), (98153, 360)]

theorem segOK : checkSeg 20 perms 98115 98154 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 98115 98154 9000 1506737344320 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 1506737344320)
    (SegSum.cons (w := 180) h98115 (SegSum.cons (w := 360) h98117 (SegSum.cons (w := 360) h98119 (SegSum.cons (w := 180) h98123 (SegSum.cons (w := 360) h98125 (SegSum.cons (w := 360) h98127 (SegSum.cons (w := 360) h98131 (SegSum.cons (w := 360) h98132 (SegSum.cons (w := 720) h98133 (SegSum.cons (w := 360) h98135 (SegSum.cons (w := 360) h98137 (SegSum.cons (w := 360) h98139 (SegSum.cons (w := 360) h98140 (SegSum.cons (w := 720) h98141 (SegSum.cons (w := 360) h98143 (SegSum.cons (w := 720) h98147 (SegSum.cons (w := 720) h98149 (SegSum.cons (w := 720) h98150 (SegSum.cons (w := 720) h98151 (SegSum.cons (w := 360) h98153 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S74
