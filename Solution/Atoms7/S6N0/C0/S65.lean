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

namespace RACert.S6N0.C0.S65

open RACert RACert.Problem

theorem cover98042 : P.CoversSplit 26 10 98042 0xf0f0f0f0f0f0f0f0f0f0f0f5f0f0f0f000000000000000000000000000300000000000000000000000005050000050500000000000000000000000000000000000000000003000300000000000300030000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 587, 874, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c98042_0 : P.sumLeaves 26 100395008 1024 = 289384086 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98042) (lo := 0) (len := 1024) (W := 289384086) check rows elimOK (by decide) (by decide) cover98042 (by decide)
  decide +kernel

theorem h98042 : P.leaf 36 98042 = 289384086 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 289384086)]) (.cons c98042_0 (.nil)) (by decide) (by decide))

theorem cover98043 : P.CoversSplit 26 10 98043 0xf0f0f0f0f0f0f0f0f0f0f0f5f0f0f0f000000000000000000000000000300000000000000000000000005050000050500000000000000000000000000000000000000000003000300000000000300030000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 587, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c98043_0 : P.sumLeaves 26 100396032 1024 = 479892306 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98043) (lo := 0) (len := 1024) (W := 479892306) check rows elimOK (by decide) (by decide) cover98043 (by decide)
  decide +kernel

theorem h98043 : P.leaf 36 98043 = 479892306 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 479892306)]) (.cons c98043_0 (.nil)) (by decide) (by decide))

theorem cover114619 : P.CoversSplit 26 10 114619 0xffffffff00000000ffffffff0000000000000000000000000000000000000000fffff0f000000000aaaaa0a00000000000000000000000000000000000000000ffffffff00330030ffffffff0033003000330033000000000022002200000000fffff0f000330030aaaaa0a00022002000330030000000000022002000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 1273, 1315, 1658]) (by decide +kernel)

noncomputable def f114619 (i : ℕ) := rowWeight keep9 twice9 i * P.leaf 26 (117369856 + i)

theorem c114619_0 : rowSum f114619 0 762 = 484317694 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 114619) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover114619 (by decide)
  decide +kernel

theorem c114619_1 : rowSum f114619 762 262 = 498302996 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 114619) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover114619 (by decide)
  decide +kernel

theorem sum114619 : rowSum f114619 0 1024 = 982620690 :=
  rowSum_append (F := f114619) (lo := 0) (n := 762) (m := 262) (A := 484317694) (B := 498302996) c114619_0 (c114619_1)

theorem h114619 : P.leaf 36 114619 = 982620690 :=
  leaf_weighted (k := 26) (d := 10) (H := 114619) (keep := keep9) (twice := twice9) rows (by decide) (by decide) (bal9) (invRow9 (H := 114619) (by decide) (by decide +kernel)) sum114619

theorem h98046 : P.leaf 36 98046 = 982620690 :=
  orient72 (v := 114619) (by decide) (by decide +kernel) h114619

theorem cover114623 : P.CoversSplit 26 10 114623 0xffffffff00000000ffffffff0000000000000000000000000000000000000000fffff0f000000000aaaaa0a00000000000000000000000000000000000000000ffffffff00330030ffffffff0033003000330033000000000022002200000000fffff0f000330030aaaaa0a00022002000330030000000000022002000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [538, 1273, 1315, 1658]) (by decide +kernel)

noncomputable def f114623 (i : ℕ) := rowWeight keep9 twice9 i * P.leaf 26 (117373952 + i)

theorem c114623_0 : rowSum f114623 0 762 = 814643754 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 114623) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover114623 (by decide)
  decide +kernel

theorem c114623_1 : rowSum f114623 762 262 = 567092904 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 114623) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover114623 (by decide)
  decide +kernel

theorem sum114623 : rowSum f114623 0 1024 = 1381736658 :=
  rowSum_append (F := f114623) (lo := 0) (n := 762) (m := 262) (A := 814643754) (B := 567092904) c114623_0 (c114623_1)

theorem h114623 : P.leaf 36 114623 = 1381736658 :=
  leaf_weighted (k := 26) (d := 10) (H := 114623) (keep := keep9) (twice := twice9) rows (by decide) (by decide) (bal9) (invRow9 (H := 114623) (by decide) (by decide +kernel)) sum114623

theorem h98047 : P.leaf 36 98047 = 1381736658 :=
  orient72 (v := 114623) (by decide) (by decide +kernel) h114623

theorem cover98115 : P.CoversSplit 26 10 98115 0xa0000000a00000000000000000000000a0000000a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 523, 530, 579, 608, 972, 979, 1266]) (by decide +kernel)

theorem h98115 : P.leaf 36 98115 = 10602376 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 98115) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 98115) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 98115) (weight := rowWeight keep1 twice1) (xs := [349, 351, 861, 863, 893, 895, 989, 991, 1021, 1023]) check rows elimOK (by decide) (by decide) cover98115 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover310681 : P.CoversSplit 26 10 310681 0xaaaa000000220000aaaa0a0a002200020000000000000000000000000000000000000000000000000a0a0a0a000200020000000000000000000000000000000000220000002200000022000200220002000000000000000000000000000000000000000000000000000200020002000200000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 537, 538, 629, 636, 930, 1272, 1273, 1665]) (by decide +kernel)

noncomputable def f310681 (i : ℕ) := rowWeight keep16 twice16 i * P.leaf 26 (318137344 + i)

theorem c310681_0 : rowSum f310681 0 1024 = 9149809 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 310681) (keep := keep16) (twice := twice16) check rows elimOK (by decide) (by decide) cover310681 (by decide)
  decide +kernel

theorem sum310681 : rowSum f310681 0 1024 = 9149809 :=
  c310681_0

theorem h310681 : P.leaf 36 310681 = 9149809 :=
  leaf_weighted (k := 26) (d := 10) (H := 310681) (keep := keep16) (twice := twice16) rows (by decide) (by decide) (bal16) (invRow16 (H := 310681) (by decide) (by decide +kernel)) sum310681

theorem h98117 : P.leaf 36 98117 = 9149809 :=
  orient6 (v := 310681) (by decide) (by decide +kernel) h310681

theorem cover98119 : P.CoversSplit 26 10 98119 0xff000000ff0005000000000000000000ff000000ff0305000500000005000500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003300010000000000010001000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 579, 972, 979, 1266, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f98119 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 26 (100473856 + i)

theorem c98119_0 : rowSum f98119 0 1024 = 128653387 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 98119) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover98119 (by decide)
  decide +kernel

theorem sum98119 : rowSum f98119 0 1024 = 128653387 :=
  c98119_0

theorem h98119 : P.leaf 36 98119 = 128653387 :=
  leaf_weighted (k := 26) (d := 10) (H := 98119) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 98119) (by decide) (by decide +kernel)) sum98119

theorem cover375222 : P.CoversSplit 26 10 375222 0xcc00cc0000000000cc00cc000000000000000000000000000000000000000000cc00cc000000000088008800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [468, 489, 538, 629, 636, 867]) (by decide +kernel)

theorem h375222 : P.leaf 36 375222 = 63690598 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 375222) (keep := keep17) (twice := twice17) rows (by decide) (by decide) bal17 (invRow17 (H := 375222) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 375222) (weight := rowWeight keep17 twice17) (xs := [683, 687, 699, 703, 746, 747, 750, 751, 762, 763, 766, 767, 938, 939, 942, 943, 954, 955, 958, 959, 1002, 1003, 1006, 1007, 1018, 1019, 1022, 1023]) check rows elimOK (by decide) (by decide) cover375222 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h98123 : P.leaf 36 98123 = 63690598 :=
  orient86 (v := 375222) (by decide) (by decide +kernel) h375222

theorem cover310683 : P.CoversSplit 26 10 310683 0xaaaa000000220000aaaa0a0a002200020000000000000000000000000000000000000000000000000a0a0a0a000200020000000000000000000000000000000000220000002200000022000200220002000000000000000000000000000000000000000000000000000200020002000200000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 537, 538, 629, 636, 1272, 1273, 1665]) (by decide +kernel)

noncomputable def f310683 (i : ℕ) := rowWeight keep16 twice16 i * P.leaf 26 (318139392 + i)

theorem c310683_0 : rowSum f310683 0 1024 = 67788919 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 310683) (keep := keep16) (twice := twice16) check rows elimOK (by decide) (by decide) cover310683 (by decide)
  decide +kernel

theorem sum310683 : rowSum f310683 0 1024 = 67788919 :=
  c310683_0

theorem h310683 : P.leaf 36 310683 = 67788919 :=
  leaf_weighted (k := 26) (d := 10) (H := 310683) (keep := keep16) (twice := twice16) rows (by decide) (by decide) (bal16) (invRow16 (H := 310683) (by decide) (by decide +kernel)) sum310683

theorem h98125 : P.leaf 36 98125 = 67788919 :=
  orient6 (v := 310683) (by decide) (by decide +kernel) h310683

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
  leaf_weighted (k := 26) (d := 10) (H := 98127) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 98127) (by decide) (by decide +kernel)) sum98127

theorem cover604287 : P.CoversSplit 26 10 604287 0x8800880000000000880088000000000000000000000000000000000000000000000008000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000022002200000000002200220000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [579, 587, 622, 629, 636, 874, 930, 979, 1273]) (by decide +kernel)

theorem h604287 : P.leaf 36 604287 = 21536061 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 604287) (keep := keep3) (twice := twice3) rows (by decide) (by decide) bal3 (invRow3 (H := 604287) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 604287) (weight := rowWeight keep3 twice3) (xs := [257, 261, 273, 277, 321, 325, 337, 341, 683, 747, 939, 943, 955, 959, 1003, 1007, 1019, 1023]) check rows elimOK (by decide) (by decide) cover604287 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h98131 : P.leaf 36 98131 = 21536061 :=
  orient87 (v := 604287) (by decide) (by decide +kernel) h604287

theorem cover356813 : P.CoversSplit 26 10 356813 0xa0a0a0a0a0a0a0a0a0a0a0a1a0a0a0a100000000000000000000000000200020000000000000000000000000000000000000000000000000000000000000000000000000002000200000000000200021000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 580, 629, 636, 972, 1273, 1665]) (by decide +kernel)

noncomputable def f356813 (i : ℕ) := rowWeight keep7 twice7 i * P.leaf 26 (365376512 + i)

theorem c356813_0 : rowSum f356813 0 1024 = 6525173 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 356813) (keep := keep7) (twice := twice7) check rows elimOK (by decide) (by decide) cover356813 (by decide)
  decide +kernel

theorem sum356813 : rowSum f356813 0 1024 = 6525173 :=
  c356813_0

theorem h356813 : P.leaf 36 356813 = 6525173 :=
  leaf_weighted (k := 26) (d := 10) (H := 356813) (keep := keep7) (twice := twice7) rows (by decide) (by decide) (bal7) (invRow7 (H := 356813) (by decide) (by decide +kernel)) sum356813

theorem h98132 : P.leaf 36 98132 = 6525173 :=
  orient348 (v := 356813) (by decide) (by decide +kernel) h356813

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
  leaf_weighted (k := 26) (d := 10) (H := 98135) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 98135) (by decide) (by decide +kernel)) sum98135

theorem cover310707 : P.CoversSplit 26 10 310707 0xcc00cc0000000000cc00c8000000000000000000000000000000000000000000cc00cc000000000088008800000000000000000000000000000000000000000000000000000000000000000000000000000000000033003300000000002200220000000000000000000000000000000000000000003300330000000000220022 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 538, 629, 636, 930]) (by decide +kernel)

noncomputable def f310707 (i : ℕ) := rowWeight keep17 twice17 i * P.leaf 26 (318163968 + i)

theorem c310707_0 : rowSum f310707 0 1024 = 49044523 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 310707) (keep := keep17) (twice := twice17) check rows elimOK (by decide) (by decide) cover310707 (by decide)
  decide +kernel

theorem sum310707 : rowSum f310707 0 1024 = 49044523 :=
  c310707_0

theorem h310707 : P.leaf 36 310707 = 49044523 :=
  leaf_weighted (k := 26) (d := 10) (H := 310707) (keep := keep17) (twice := twice17) rows (by decide) (by decide) (bal17) (invRow17 (H := 310707) (by decide) (by decide +kernel)) sum310707

theorem h98137 : P.leaf 36 98137 = 49044523 :=
  orient6 (v := 310707) (by decide) (by decide +kernel) h310707

theorem cover604415 : P.CoversSplit 26 10 604415 0xcc00cc0000000000cc00cc000000000000000000000000000000000000000000cc00c80000000000cc00c800000000000000000000000000000000000000000000000000000000000000000000000000000000000033003200000000003300320000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [587, 629, 636, 874, 930, 1273]) (by decide +kernel)

noncomputable def f604415 (i : ℕ) := rowWeight keep3 twice3 i * P.leaf 26 (618920960 + i)

theorem c604415_0 : rowSum f604415 0 1024 = 109142691 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 604415) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover604415 (by decide)
  decide +kernel

theorem sum604415 : rowSum f604415 0 1024 = 109142691 :=
  c604415_0

theorem h604415 : P.leaf 36 604415 = 109142691 :=
  leaf_weighted (k := 26) (d := 10) (H := 604415) (keep := keep3) (twice := twice3) rows (by decide) (by decide) (bal3) (invRow3 (H := 604415) (by decide) (by decide +kernel)) sum604415

theorem h98139 : P.leaf 36 98139 = 109142691 :=
  orient87 (v := 604415) (by decide) (by decide +kernel) h604415

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
  leaf_weighted (k := 26) (d := 10) (H := 98140) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 98140) (by decide) (by decide +kernel)) sum98140

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
  leaf_weighted (k := 26) (d := 10) (H := 98143) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 98143) (by decide) (by decide +kernel)) sum98143

theorem cover98147 : P.CoversSplit 26 10 98147 0xf000f000f000f0000000000000000000f000f000f000f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000f000f00000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 579, 972, 979, 1266, 1273, 1658]) (by decide +kernel)

theorem c98147_0 : P.sumLeaves 26 100502528 1024 = 49939272 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98147) (lo := 0) (len := 1024) (W := 49939272) check rows elimOK (by decide) (by decide) cover98147 (by decide)
  decide +kernel

theorem h98147 : P.leaf 36 98147 = 49939272 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 49939272)]) (.cons c98147_0 (.nil)) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(98042, 720), (98043, 720), (98046, 360), (98047, 360), (98115, 180), (98117, 360), (98119, 360), (98123, 180), (98125, 360), (98127, 360), (98131, 360), (98132, 360), (98133, 720), (98135, 360), (98137, 360), (98139, 360), (98140, 360), (98141, 720), (98143, 360), (98147, 720)]

theorem segOK : checkSeg 20 perms 98042 98149 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 98042 98149 8640 2488347458640 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 2488347458640)
    (SegSum.cons (w := 720) h98042 (SegSum.cons (w := 720) h98043 (SegSum.cons (w := 360) h98046 (SegSum.cons (w := 360) h98047 (SegSum.cons (w := 180) h98115 (SegSum.cons (w := 360) h98117 (SegSum.cons (w := 360) h98119 (SegSum.cons (w := 180) h98123 (SegSum.cons (w := 360) h98125 (SegSum.cons (w := 360) h98127 (SegSum.cons (w := 360) h98131 (SegSum.cons (w := 360) h98132 (SegSum.cons (w := 720) h98133 (SegSum.cons (w := 360) h98135 (SegSum.cons (w := 360) h98137 (SegSum.cons (w := 360) h98139 (SegSum.cons (w := 360) h98140 (SegSum.cons (w := 720) h98141 (SegSum.cons (w := 360) h98143 (SegSum.cons (w := 720) h98147 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S65
