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

namespace RACert.S6N0.C0.S36

open RACert RACert.Problem

theorem cover31729 : P.CoversSplit 26 10 31729 0xf000f000f000f000f000a000f000a000f000f000c000c000f000a000c000800800000000000000000000aa000000aa0000000000000000000000aa00000088080000000000000000000000000000000000000000c0c0c0c000000000c0c080880000000000000000000000000000000000000000000000000000000000008888 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 972, 979, 1265, 1273]) (by decide +kernel)

noncomputable def f31729 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 26 (32490496 + i)

theorem c31729_0 : rowSum f31729 0 1024 = 8014232 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 31729) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover31729 (by decide)
  decide +kernel

theorem sum31729 : rowSum f31729 0 1024 = 8014232 :=
  c31729_0

theorem h31729 : P.leaf 36 31729 = 8014232 :=
  leaf_weighted (k := 26) (d := 10) (H := 31729) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 31729) (by decide) (by decide +kernel)) sum31729

theorem cover31731 : P.CoversSplit 26 10 31731 0xf000f000f000f000f000a000f000a000f000f000c000c000f000a000c000800800000000000000000000aa000000aa0000000000000000000000aa00000088080000000000000000000000000000000000000000c0c0c0c000000000c0c080880000000000000000000000000000000000000000000000000000000000008888 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 972, 979, 1265, 1273]) (by decide +kernel)

noncomputable def f31731 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 26 (32492544 + i)

theorem c31731_0 : rowSum f31731 0 1024 = 65602384 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 31731) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover31731 (by decide)
  decide +kernel

theorem sum31731 : rowSum f31731 0 1024 = 65602384 :=
  c31731_0

theorem h31731 : P.leaf 36 31731 = 65602384 :=
  leaf_weighted (k := 26) (d := 10) (H := 31731) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 31731) (by decide) (by decide +kernel)) sum31731

theorem cover31733 : P.CoversSplit 26 10 31733 0xff00ff00ff00fa00ff00aa00ff00aa00ff00ff00cc00c800fa00aa00c8008800ff00fa00ff00fa00fa00a000fa00a000ff00fa00cc00c800fa00a000c800800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 929, 972, 979, 1265, 1273, 1315, 1658]) (by decide +kernel)

theorem c31733_0 : P.sumLeaves 26 32494592 859 = 30721768 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 31733) (lo := 0) (len := 859) (W := 30721768) check rows elimOK (by decide) (by decide) cover31733 (by decide)
  decide +kernel

theorem c31733_1 : P.sumLeaves 26 32495451 165 = 52474432 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 31733) (lo := 859) (len := 165) (W := 52474432) check rows elimOK (by decide) (by decide) cover31733 (by decide)
  decide +kernel

theorem h31733 : P.leaf 36 31733 = 83196200 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(859, 30721768), (165, 52474432)]) (.cons c31733_0 (.cons c31733_1 (.nil))) (by decide) (by decide))

theorem cover31735 : P.CoversSplit 26 10 31735 0xff00ff00ff00fa00ff00aa00ff00aa00ff00ff00cc00c800fa00aa00c8008800ff00fa00ff00fa00fa00a000fa00a000ff00fa00cc00c800fa00a000c800800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 972, 979, 1265, 1273, 1315, 1658]) (by decide +kernel)

noncomputable def f31735 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 26 (32496640 + i)

theorem c31735_0 : rowSum f31735 0 1019 = 395601896 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 31735) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover31735 (by decide)
  decide +kernel

theorem c31735_1 : rowSum f31735 1019 5 = 30569200 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 31735) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover31735 (by decide)
  decide +kernel

theorem sum31735 : rowSum f31735 0 1024 = 426171096 :=
  rowSum_append (F := f31735) (lo := 0) (n := 1019) (m := 5) (A := 395601896) (B := 30569200) c31735_0 (c31735_1)

theorem h31735 : P.leaf 36 31735 = 426171096 :=
  leaf_weighted (k := 26) (d := 10) (H := 31735) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 31735) (by decide) (by decide +kernel)) sum31735

theorem cover31743 : P.CoversSplit 26 10 31743 0xfffffffffffffac8ffffaaaaffffaa88ffffffffccccc8c8fac8aa88c8c88888fffffafafffffac8fafaaaaafafaaa88fffffafaccccc8c8fac8aa88c8c88888ffffffffffccfac8ffffaaaaffccaa88ffccffccccccc8c8fac8aa88c8c88888fffffafaffccfac8fafaaaaafac8aa88ffccfac8ccccc8c8fac8aa88c8c88888 :=
  coversSplit check rows (by decide) (by decide) (xs := [972, 979, 1265, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f31743 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 26 (32504832 + i)

theorem c31743_0 : rowSum f31743 0 311 = 167924874 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 31743) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover31743 (by decide)
  decide +kernel

theorem c31743_1 : rowSum f31743 311 155 = 753086646 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 31743) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover31743 (by decide)
  decide +kernel

theorem c31743_2 : rowSum f31743 466 421 = 1027758464 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 31743) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover31743 (by decide)
  decide +kernel

theorem c31743_3 : rowSum f31743 887 137 = 627275036 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 31743) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover31743 (by decide)
  decide +kernel

theorem sum31743 : rowSum f31743 0 1024 = 2576045020 :=
  rowSum_append (F := f31743) (lo := 0) (n := 311) (m := 713) (A := 167924874) (B := 2408120146) c31743_0 (rowSum_append (F := f31743) (lo := 311) (n := 155) (m := 558) (A := 753086646) (B := 1655033500) c31743_1 (rowSum_append (F := f31743) (lo := 466) (n := 421) (m := 137) (A := 1027758464) (B := 627275036) c31743_2 (c31743_3)))

theorem h31743 : P.leaf 36 31743 = 2576045020 :=
  leaf_weighted (k := 26) (d := 10) (H := 31743) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 31743) (by decide) (by decide +kernel)) sum31743

theorem cover32243 : P.CoversSplit 26 10 32243 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [482]) (by decide +kernel)

theorem c32243_0 : P.sumLeaves 26 33016832 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 32243) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover32243 (by decide)
  decide +kernel

theorem h32243 : P.leaf 36 32243 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c32243_0 (.nil)) (by decide) (by decide))

theorem cover32244 : P.CoversSplit 26 10 32244 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c32244_0 : P.sumLeaves 26 33017856 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 32244) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover32244 (by decide)
  decide +kernel

theorem h32244 : P.leaf 36 32244 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c32244_0 (.nil)) (by decide) (by decide))

theorem cover32245 : P.CoversSplit 26 10 32245 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c32245_0 : P.sumLeaves 26 33018880 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 32245) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover32245 (by decide)
  decide +kernel

theorem h32245 : P.leaf 36 32245 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c32245_0 (.nil)) (by decide) (by decide))

theorem cover32247 : P.CoversSplit 26 10 32247 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c32247_0 : P.sumLeaves 26 33020928 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 32247) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover32247 (by decide)
  decide +kernel

theorem h32247 : P.leaf 36 32247 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c32247_0 (.nil)) (by decide) (by decide))

theorem cover32252 : P.CoversSplit 26 10 32252 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c32252_0 : P.sumLeaves 26 33026048 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 32252) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover32252 (by decide)
  decide +kernel

theorem h32252 : P.leaf 36 32252 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c32252_0 (.nil)) (by decide) (by decide))

theorem cover32253 : P.CoversSplit 26 10 32253 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c32253_0 : P.sumLeaves 26 33027072 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 32253) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover32253 (by decide)
  decide +kernel

theorem h32253 : P.leaf 36 32253 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c32253_0 (.nil)) (by decide) (by decide))

theorem cover32255 : P.CoversSplit 26 10 32255 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c32255_0 : P.sumLeaves 26 33029120 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 32255) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover32255 (by decide)
  decide +kernel

theorem h32255 : P.leaf 36 32255 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c32255_0 (.nil)) (by decide) (by decide))

theorem cover32496 : P.CoversSplit 26 10 32496 0xc000c000c000c000c000c000c000c0000000000000000000000000000000000000000000000000000000c0000000c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 587, 972, 979, 1658, 1665]) (by decide +kernel)

theorem c32496_0 : P.sumLeaves 26 33275904 640 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 32496) (lo := 0) (len := 640) (W := 0) check rows elimOK (by decide) (by decide) cover32496 (by decide)
  decide +kernel

theorem contract32496_1 : P.leaf 32 519946 = 0 := by
  exact leaf_contract_zero (ss := [(7, 1, 475), (2, 1, 482), (6, 4, 580), (4, 1, 586), (3, 1, 409), (5, 1, 411), (10, 1, 458), (11, 1, 459), (12, 1, 460), (13, 1, 461), (29, 1, 587), (30, 0, 972), (28, 1, 481), (32, 0, 972), (26, 1, 873), (31, 1, 979)]) (q := 1658) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c32496_1 : P.sumLeaves 26 33276544 64 = 0 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 519946) rows (by decide) (by decide)).symm.trans contract32496_1

theorem c32496_2 : P.sumLeaves 26 33276608 192 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 32496) (lo := 704) (len := 192) (W := 0) check rows elimOK (by decide) (by decide) cover32496 (by decide)
  decide +kernel

theorem contract32496_3 : P.leaf 32 519950 = 62336 := by
  exact leaf_contract_factors (k := 32) (b := 19) (H := 519950) (ss := [(7, 1, 475), (2, 1, 482), (6, 1, 580), (3, 1, 409), (4, 1, 410), (5, 1, 411), (10, 1, 458), (11, 1, 459), (12, 1, 460), (13, 1, 461), (29, 1, 587), (31, 1, 979), (30, 1, 972)]) (ids := [6, 7, 12, 13, 14, 15, 16, 17, 18, 19, 22, 23, 24, 26, 30, 31, 20, 21, 25]) (cs := [1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 4, 5, 6, 7, 8, 9, 10, 11, 18, 19, 12, 13, 14, 20, 15, 1, 1, 1, 16, 17]) (bs := [16, 3]) (W := 62336) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c32496_3 : P.sumLeaves 26 33276800 64 = 62336 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 519950) rows (by decide) (by decide)).symm.trans contract32496_3

theorem c32496_4 : P.sumLeaves 26 33276864 64 = 71744 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 32496) (lo := 960) (len := 64) (W := 71744) check rows elimOK (by decide) (by decide) cover32496 (by decide)
  decide +kernel

theorem h32496 : P.leaf 36 32496 = 134080 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(640, 0), (64, 0), (192, 0), (64, 62336), (64, 71744)]) (.cons c32496_0 (.cons c32496_1 (.cons c32496_2 (.cons c32496_3 (.cons c32496_4 (.nil)))))) (by decide) (by decide))

theorem cover32497 : P.CoversSplit 26 10 32497 0xc000c000c000c000c000c000c000c0000000000000000000000000000000000000000000000000000000c0000000c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 587, 972, 979, 1658, 1665]) (by decide +kernel)

theorem c32497_0 : P.sumLeaves 26 33276928 640 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 32497) (lo := 0) (len := 640) (W := 0) check rows elimOK (by decide) (by decide) cover32497 (by decide)
  decide +kernel

theorem contract32497_1 : P.leaf 32 519962 = 77680 := by
  exact leaf_contract_factors (k := 32) (b := 19) (H := 519962) (ss := [(7, 1, 475), (2, 1, 482), (6, 4, 580), (4, 1, 586), (29, 1, 587), (32, 0, 972), (31, 1, 979), (30, 1, 1658), (13, 0, 972), (17, 1, 874), (20, 1, 923), (9, 1, 573), (21, 1, 573)]) (ids := [1, 3, 6, 8, 9, 10, 12, 13, 14, 16, 17, 21, 22, 24, 26, 31, 20, 23, 25]) (cs := [1, 2, 1, 3, 1, 1, 4, 1, 5, 6, 7, 0, 8, 9, 10, 1, 11, 12, 1, 1, 18, 13, 14, 19, 15, 20, 16, 1, 1, 1, 0, 17]) (bs := [16, 3]) (W := 77680) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c32497_1 : P.sumLeaves 26 33277568 64 = 77680 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 519962) rows (by decide) (by decide)).symm.trans contract32497_1

theorem c32497_2 : P.sumLeaves 26 33277632 320 = 4176400 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 32497) (lo := 704) (len := 320) (W := 4176400) check rows elimOK (by decide) (by decide) cover32497 (by decide)
  decide +kernel

theorem h32497 : P.leaf 36 32497 = 4254080 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(640, 0), (64, 77680), (320, 4176400)]) (.cons c32497_0 (.cons c32497_1 (.cons c32497_2 (.nil)))) (by decide) (by decide))

theorem cover32498 : P.CoversSplit 26 10 32498 0xc000c000c000c000c000c000c000c0000000000000000000000000000000000000000000000000000000c0000000c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 587, 972, 979, 1658, 1665]) (by decide +kernel)

theorem c32498_0 : P.sumLeaves 26 33277952 1024 = 9554000 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 32498) (lo := 0) (len := 1024) (W := 9554000) check rows elimOK (by decide) (by decide) cover32498 (by decide)
  decide +kernel

theorem h32498 : P.leaf 36 32498 = 9554000 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 9554000)]) (.cons c32498_0 (.nil)) (by decide) (by decide))

theorem cover32499 : P.CoversSplit 26 10 32499 0xc000c000c000c000c000c000c000c0000000000000000000000000000000000000000000000000000000c0000000c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 587, 972, 979, 1658, 1665]) (by decide +kernel)

theorem c32499_0 : P.sumLeaves 26 33278976 1024 = 23784464 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 32499) (lo := 0) (len := 1024) (W := 23784464) check rows elimOK (by decide) (by decide) cover32499 (by decide)
  decide +kernel

theorem h32499 : P.leaf 36 32499 = 23784464 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 23784464)]) (.cons c32499_0 (.nil)) (by decide) (by decide))

theorem cover32502 : P.CoversSplit 26 10 32502 0xcc00cc00cc00c800cc00c800cc00c80000000000000000000000000000000000cc00c800cc00c800c000c000c000c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 587, 880, 972, 979, 1265, 1315, 1658]) (by decide +kernel)

theorem c32502_0 : P.sumLeaves 26 33282048 1024 = 61133808 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 32502) (lo := 0) (len := 1024) (W := 61133808) check rows elimOK (by decide) (by decide) cover32502 (by decide)
  decide +kernel

theorem h32502 : P.leaf 36 32502 = 61133808 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 61133808)]) (.cons c32502_0 (.nil)) (by decide) (by decide))

theorem cover32503 : P.CoversSplit 26 10 32503 0xcc00cc00cc00c800cc00c800cc00c80000000000000000000000000000000000cc00c800cc00c800c000c000c000c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 587, 972, 979, 1265, 1315, 1658]) (by decide +kernel)

theorem c32503_0 : P.sumLeaves 26 33283072 1024 = 124748000 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 32503) (lo := 0) (len := 1024) (W := 124748000) check rows elimOK (by decide) (by decide) cover32503 (by decide)
  decide +kernel

theorem h32503 : P.leaf 36 32503 = 124748000 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 124748000)]) (.cons c32503_0 (.nil)) (by decide) (by decide))

theorem cover32504 : P.CoversSplit 26 10 32504 0xf0f0f0f0f0f0f0c0f0f0f0f0f0f0f0c000000000000000000030003000000000000000000000000000005050000050400000000000000000000000100000000000300030000000000030003000000000003000300000000000300030000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 587, 874, 972, 979, 1265, 1273, 1322, 1665]) (by decide +kernel)

theorem c32504_0 : P.sumLeaves 26 33284096 1024 = 7238172 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 32504) (lo := 0) (len := 1024) (W := 7238172) check rows elimOK (by decide) (by decide) cover32504 (by decide)
  decide +kernel

theorem h32504 : P.leaf 36 32504 = 7238172 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 7238172)]) (.cons c32504_0 (.nil)) (by decide) (by decide))

theorem cover32505 : P.CoversSplit 26 10 32505 0xf0f0f0f0f0f0f0c0f0f0f0f0f0f0f0c000000000000000000030003000000000000000000000000000005050000050400000000000000000000000100000000000300030000000000030003000000000003000300000000000300030000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 587, 923, 972, 979, 1265, 1273, 1322, 1665]) (by decide +kernel)

theorem c32505_0 : P.sumLeaves 26 33285120 1024 = 59119112 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 32505) (lo := 0) (len := 1024) (W := 59119112) check rows elimOK (by decide) (by decide) cover32505 (by decide)
  decide +kernel

theorem h32505 : P.leaf 36 32505 = 59119112 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 59119112)]) (.cons c32505_0 (.nil)) (by decide) (by decide))

theorem cover32506 : P.CoversSplit 26 10 32506 0xf0f0f0f0f0f0f0c0f0f0f0f0f0f0f0c000000000000000000030003000000000000000000000000000005050000050400000000000000000000000100000000000300030000000000030003000000000003000300000000000300030000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 587, 874, 972, 979, 1265, 1273, 1322, 1665]) (by decide +kernel)

theorem c32506_0 : P.sumLeaves 26 33286144 1024 = 124874332 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 32506) (lo := 0) (len := 1024) (W := 124874332) check rows elimOK (by decide) (by decide) cover32506 (by decide)
  decide +kernel

theorem h32506 : P.leaf 36 32506 = 124874332 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 124874332)]) (.cons c32506_0 (.nil)) (by decide) (by decide))

theorem cover32507 : P.CoversSplit 26 10 32507 0xf0f0f0f0f0f0f0c0f0f0f0f0f0f0f0c000000000000000000030003000000000000000000000000000005050000050400000000000000000000000100000000000300030000000000030003000000000003000300000000000300030000000000000000000000000000000100000000000000000000000000000001000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 587, 972, 979, 1265, 1273, 1322, 1665]) (by decide +kernel)

theorem c32507_0 : P.sumLeaves 26 33287168 1024 = 260108342 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 32507) (lo := 0) (len := 1024) (W := 260108342) check rows elimOK (by decide) (by decide) cover32507 (by decide)
  decide +kernel

theorem h32507 : P.leaf 36 32507 = 260108342 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 260108342)]) (.cons c32507_0 (.nil)) (by decide) (by decide))

theorem cover32510 : P.CoversSplit 26 10 32510 0xfffffffffffffac8fffffafafffffac800000000000000000030003000000000fffffafafffffac8f0f0f0f0f0f0f0c00000000000000000003000300000000000330033000000000033003200000000003300330000000000300030000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [587, 874, 972, 979, 1265, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c32510_0 : P.sumLeaves 26 33290240 750 = 66019384 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 32510) (lo := 0) (len := 750) (W := 66019384) check rows elimOK (by decide) (by decide) cover32510 (by decide)
  decide +kernel

theorem c32510_1 : P.sumLeaves 26 33290990 238 = 246695902 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 32510) (lo := 750) (len := 238) (W := 246695902) check rows elimOK (by decide) (by decide) cover32510 (by decide)
  decide +kernel

theorem c32510_2 : P.sumLeaves 26 33291228 36 = 178590026 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 32510) (lo := 988) (len := 36) (W := 178590026) check rows elimOK (by decide) (by decide) cover32510 (by decide)
  decide +kernel

theorem h32510 : P.leaf 36 32510 = 491305312 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(750, 66019384), (238, 246695902), (36, 178590026)]) (.cons c32510_0 (.cons c32510_1 (.cons c32510_2 (.nil)))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(31729, 360), (31731, 180), (31733, 360), (31735, 360), (31743, 90), (32243, 45), (32244, 180), (32245, 360), (32247, 180), (32252, 90), (32253, 180), (32255, 90), (32496, 360), (32497, 360), (32498, 720), (32499, 720), (32502, 360), (32503, 360), (32504, 360), (32505, 360), (32506, 720), (32507, 720), (32510, 360)]

theorem segOK : checkSeg 20 perms 31729 32511 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 31729 32511 7875 1000356773400 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 1000356773400)
    (SegSum.cons (w := 360) h31729 (SegSum.cons (w := 180) h31731 (SegSum.cons (w := 360) h31733 (SegSum.cons (w := 360) h31735 (SegSum.cons (w := 90) h31743 (SegSum.cons (w := 45) h32243 (SegSum.cons (w := 180) h32244 (SegSum.cons (w := 360) h32245 (SegSum.cons (w := 180) h32247 (SegSum.cons (w := 90) h32252 (SegSum.cons (w := 180) h32253 (SegSum.cons (w := 90) h32255 (SegSum.cons (w := 360) h32496 (SegSum.cons (w := 360) h32497 (SegSum.cons (w := 720) h32498 (SegSum.cons (w := 720) h32499 (SegSum.cons (w := 360) h32502 (SegSum.cons (w := 360) h32503 (SegSum.cons (w := 360) h32504 (SegSum.cons (w := 360) h32505 (SegSum.cons (w := 720) h32506 (SegSum.cons (w := 720) h32507 (SegSum.cons (w := 360) h32510 (show SegSum (P.leaf 36) [] 0 from rfl)))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S36
