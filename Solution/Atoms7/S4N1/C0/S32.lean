/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Atoms7.S4N1.C0.Actions

/-! Generated identity-class certificate for the product-row count. -/

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option Elab.async false

@[expose] public section

namespace RACert.S4N1.C0.S32

open RACert RACert.Problem

theorem cover5629 : P.CoversSplit 24 10 5629 0xff00ff00aa00a000000000000000000000000000000000000000000000000000cc00cc0088008000000000000000000000000000000000000000000000000000ff00ff00aa00a0000000000000000000000000000000000000000000000000000003000300000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 858, 860, 865, 909, 916, 1202, 1258, 1601]) (by decide +kernel)

theorem c5629_0 : P.sumLeaves 24 5764096 1024 = 12565871 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5629) (lo := 0) (len := 1024) (W := 12565871) check rows elimOK (by decide) (by decide) cover5629 (by decide)
  decide +kernel

theorem h5629 : P.leaf 34 5629 = 12565871 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 12565871)]) (.cons c5629_0 (.nil)) (by decide) (by decide))

theorem cover5631 : P.CoversSplit 24 10 5631 0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaacccccccc88888888cccccccc88888888cccccccc88888888cccccccc88888888ffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaacccccccc88888888cccccccc88888888cccccccc88888888cccccccc88888888 :=
  coversSplit check rows (by decide) (by decide) (xs := [858, 860, 865, 916, 1202, 1258, 1601]) (by decide +kernel)

noncomputable def f5631 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (5766144 + i)

theorem c5631_0 : rowSum f5631 0 295 = 45829736 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 5631) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover5631 (by decide)
  decide +kernel

theorem c5631_1 : rowSum f5631 295 187 = 67492009 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 5631) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover5631 (by decide)
  decide +kernel

theorem c5631_2 : rowSum f5631 482 476 = 143413960 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 5631) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover5631 (by decide)
  decide +kernel

theorem c5631_3 : rowSum f5631 958 66 = 36921880 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 5631) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover5631 (by decide)
  decide +kernel

theorem sum5631 : rowSum f5631 0 1024 = 293657585 :=
  rowSum_append (F := f5631) (lo := 0) (n := 295) (m := 729) (A := 45829736) (B := 247827849) c5631_0 (rowSum_append (F := f5631) (lo := 295) (n := 187) (m := 542) (A := 67492009) (B := 180335840) c5631_1 (rowSum_append (F := f5631) (lo := 482) (n := 476) (m := 66) (A := 143413960) (B := 36921880) c5631_2 (c5631_3)))

theorem h5631 : P.leaf 34 5631 = 293657585 :=
  leaf_weighted (k := 24) (d := 10) (H := 5631) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 5631) (by decide) (by decide +kernel)) sum5631

theorem cover5811 : P.CoversSplit 24 10 5811 0xffff0000000000000000000000000000a0a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [517, 573, 860, 916, 1202, 1209, 1210, 1251, 1258, 1259, 1264, 1308]) (ps := [(8, [531, 580], [517, 573]), (14, [874, 923], [860, 916])]) (by decide +kernel)

noncomputable def f5811 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (5950464 + i)

theorem c5811_0 : rowSum f5811 0 1024 = 229440 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 5811) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover5811 (by decide)
  decide +kernel

theorem sum5811 : rowSum f5811 0 1024 = 229440 :=
  c5811_0

theorem h5811 : P.leaf 34 5811 = 229440 :=
  leaf_weighted (k := 24) (d := 10) (H := 5811) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 5811) (by decide) (by decide +kernel)) sum5811

theorem cover5812 : P.CoversSplit 24 10 5812 0xfca9000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 508, 517, 573, 860, 867, 909, 916, 1202, 1209, 1251, 1258, 1259, 1264, 1308]) (ps := [(8, [468, 475], [468, 475])]) (by decide +kernel)

noncomputable def f5812 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (5951488 + i)

theorem c5812_0 : rowSum f5812 0 1024 = 73376 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 5812) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover5812 (by decide)
  decide +kernel

theorem sum5812 : rowSum f5812 0 1024 = 73376 :=
  c5812_0

theorem h5812 : P.leaf 34 5812 = 73376 :=
  leaf_weighted (k := 24) (d := 10) (H := 5812) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 5812) (by decide) (by decide +kernel)) sum5812

theorem cover5813 : P.CoversSplit 24 10 5813 0xffff0000000000000000000000000000a0a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 517, 573, 860, 867, 909, 916, 1202, 1209, 1251, 1258, 1259, 1264, 1308]) (ps := [(8, [475, 580], [475, 517])]) (by decide +kernel)

theorem c5813_0 : P.sumLeaves 24 5952512 832 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5813) (lo := 0) (len := 832) (W := 0) check rows elimOK (by decide) (by decide) cover5813 (by decide)
  decide +kernel

theorem contract5813_1 : P.leaf 30 93021 = 30464 := by
  exact leaf_contract_factors (k := 30) (b := 17) (H := 93021) (ss := [(8, 1, 475), (31, 1, 468), (26, 1, 517), (5, 1, 524), (16, 1, 531), (9, 1, 559), (28, 1, 860), (14, 1, 874), (18, 1, 487), (30, 1, 1209), (17, 1, 1266), (20, 1, 1314), (21, 1, 1315)]) (ids := [0, 1, 2, 4, 8, 9, 10, 11, 13, 17, 20, 21, 25, 27, 5, 22, 23]) (cs := [2, 3, 4, 1, 5, 16, 1, 1, 6, 7, 8, 9, 1, 10, 1, 1, 1, 11, 1, 1, 12, 13, 17, 18, 1, 14, 1, 15, 1, 1]) (bs := [14, 3]) (W := 30464) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c5813_1 : P.sumLeaves 24 5953344 64 = 30464 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 93021) rows (by decide) (by decide)).symm.trans contract5813_1

theorem c5813_2 : P.sumLeaves 24 5953408 128 = 575328 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5813) (lo := 896) (len := 128) (W := 575328) check rows elimOK (by decide) (by decide) cover5813 (by decide)
  decide +kernel

theorem h5813 : P.leaf 34 5813 = 605792 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(832, 0), (64, 30464), (128, 575328)]) (.cons c5813_0 (.cons c5813_1 (.cons c5813_2 (.nil)))) (by decide) (by decide))

theorem cover5815 : P.CoversSplit 24 10 5815 0xffff0000000000000000000000000000a0a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [517, 573, 860, 867, 909, 916, 1202, 1209, 1251, 1258, 1259, 1264, 1308]) (ps := [(8, [531, 580], [517, 573])]) (by decide +kernel)

noncomputable def f5815 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (5954560 + i)

theorem c5815_0 : rowSum f5815 0 1024 = 1542848 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 5815) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover5815 (by decide)
  decide +kernel

theorem sum5815 : rowSum f5815 0 1024 = 1542848 :=
  c5815_0

theorem h5815 : P.leaf 34 5815 = 1542848 :=
  leaf_weighted (k := 24) (d := 10) (H := 5815) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 5815) (by decide) (by decide +kernel)) sum5815

theorem cover5820 : P.CoversSplit 24 10 5820 0xfca90000000000000000000000000000a0a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 508, 517, 524, 566, 573, 860, 916, 1202, 1209, 1251, 1258, 1259, 1264, 1308]) (ps := [(8, [531, 580], [517, 573])]) (by decide +kernel)

noncomputable def f5820 (i : ℕ) := rowWeight keep4 twice4 i * P.leaf 24 (5959680 + i)

theorem c5820_0 : rowSum f5820 0 1024 = 649760 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 5820) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover5820 (by decide)
  decide +kernel

theorem sum5820 : rowSum f5820 0 1024 = 649760 :=
  c5820_0

theorem h5820 : P.leaf 34 5820 = 649760 :=
  leaf_weighted (k := 24) (d := 10) (H := 5820) (keep := keep4) (twice := twice4) rows (by decide) (by decide) bal4 (invRow4 (H := 5820) (by decide) (by decide +kernel)) sum5820

theorem cover5821 : P.CoversSplit 24 10 5821 0xffff0000000000000000000000000000a0a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 517, 524, 566, 573, 860, 916, 1202, 1209, 1251, 1258, 1259, 1264, 1308]) (ps := [(8, [531, 580], [517, 573])]) (by decide +kernel)

noncomputable def f5821 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 24 (5960704 + i)

theorem c5821_0 : rowSum f5821 0 1024 = 2139040 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 5821) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover5821 (by decide)
  decide +kernel

theorem sum5821 : rowSum f5821 0 1024 = 2139040 :=
  c5821_0

theorem h5821 : P.leaf 34 5821 = 2139040 :=
  leaf_weighted (k := 24) (d := 10) (H := 5821) (keep := keep2) (twice := twice2) rows (by decide) (by decide) bal2 (invRow2 (H := 5821) (by decide) (by decide +kernel)) sum5821

theorem cover5823 : P.CoversSplit 24 10 5823 0xffff0000000000000000000000000000a0a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [517, 524, 566, 573, 860, 916, 1202, 1209, 1251, 1258, 1259, 1264, 1308]) (ps := [(8, [531, 580], [517, 573])]) (by decide +kernel)

noncomputable def f5823 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (5962752 + i)

theorem c5823_0 : rowSum f5823 0 1024 = 5236464 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 5823) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover5823 (by decide)
  decide +kernel

theorem sum5823 : rowSum f5823 0 1024 = 5236464 :=
  c5823_0

theorem h5823 : P.leaf 34 5823 = 5236464 :=
  leaf_weighted (k := 24) (d := 10) (H := 5823) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 5823) (by decide) (by decide +kernel)) sum5823

theorem h5826 : P.leaf 34 5826 = 30720 := by
  exact leaf_contract_factors (k := 34) (b := 18) (H := 5826) (ss := [(2, 1, 453), (3, 1, 417), (5, 1, 412), (4, 1, 417), (6, 1, 467), (12, 1, 460), (34, 1, 475), (15, 1, 486), (14, 1, 509), (32, 1, 523), (30, 18, 524), (35, 1, 536), (18, 1, 566), (26, 1, 465), (28, 1, 465), (31, 1, 1209)]) (ids := [5, 6, 7, 8, 9, 11, 14, 15, 17, 18, 19, 21, 23, 25, 27, 31, 20, 22]) (cs := [1, 1, 1, 1, 1, 2, 3, 4, 5, 6, 1, 7, 1, 1, 8, 9, 1, 10, 11, 12, 18, 13, 19, 14, 1, 15, 1, 16, 1, 1, 1, 17, 1, 1]) (bs := [16, 2]) (W := 30720) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem cover5827 : P.CoversSplit 24 10 5827 0xffff0000000000000000000000000000ffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [475, 515, 516, 523, 536, 566, 860, 1202, 1209]) (by decide +kernel)

theorem c5827_0 : P.sumLeaves 24 5966848 1024 = 519056 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5827) (lo := 0) (len := 1024) (W := 519056) check rows elimOK (by decide) (by decide) cover5827 (by decide)
  decide +kernel

theorem h5827 : P.leaf 34 5827 = 519056 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 519056)]) (.cons c5827_0 (.nil)) (by decide) (by decide))

theorem h5828 : P.leaf 34 5828 = 12416 := by
  exact leaf_contract_factors (k := 34) (b := 19) (H := 5828) (ss := [(6, 1, 466), (26, 1, 472), (35, 1, 475), (27, 1, 508), (30, 18, 524), (33, 1, 536), (17, 1, 565), (18, 1, 566), (12, 1, 867), (10, 1, 458), (11, 1, 459), (31, 1, 1209), (28, 1, 465), (32, 1, 1264), (34, 1, 1259)]) (ids := [0, 1, 2, 3, 5, 6, 7, 11, 12, 13, 14, 17, 18, 19, 20, 22, 23, 27, 21]) (cs := [2, 3, 4, 5, 1, 6, 7, 8, 1, 1, 1, 9, 10, 11, 12, 1, 1, 13, 14, 15, 16, 20, 17, 18, 1, 1, 1, 19, 1, 1, 1, 1, 1, 1]) (bs := [18, 1]) (W := 12416) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem cover5829 : P.CoversSplit 24 10 5829 0xcccc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 475, 515, 522, 536, 566, 860, 916, 1202, 1209, 1259, 1264]) (by decide +kernel)

theorem c5829_0 : P.sumLeaves 24 5968896 1024 = 310332 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5829) (lo := 0) (len := 1024) (W := 310332) check rows elimOK (by decide) (by decide) cover5829 (by decide)
  decide +kernel

theorem h5829 : P.leaf 34 5829 = 310332 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 310332)]) (.cons c5829_0 (.nil)) (by decide) (by decide))

theorem cover5830 : P.CoversSplit 24 10 5830 0xa0a00000000000000000000000000000a0a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 475, 515, 516, 522, 536, 566, 860, 916, 1209, 1210, 1259, 1264]) (by decide +kernel)

theorem c5830_0 : P.sumLeaves 24 5969920 832 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5830) (lo := 0) (len := 832) (W := 0) check rows elimOK (by decide) (by decide) cover5830 (by decide)
  decide +kernel

theorem contract5830_1 : P.leaf 30 93293 = 21328 := by
  exact leaf_contract_factors (k := 30) (b := 18) (H := 93293) (ss := [(30, 18, 524), (18, 4, 566), (12, 1, 867), (4, 1, 1251), (2, 1, 409), (3, 1, 409), (26, 1, 465), (28, 1, 465), (6, 1, 479), (31, 1, 516), (16, 1, 1265), (17, 1, 1266)]) (ids := [3, 5, 6, 7, 8, 9, 11, 12, 13, 17, 18, 19, 21, 22, 23, 25, 27, 20]) (cs := [1, 1, 1, 2, 1, 3, 4, 5, 6, 7, 1, 8, 9, 10, 1, 1, 1, 11, 12, 13, 19, 14, 15, 16, 1, 17, 1, 18, 1, 1]) (bs := [17, 1]) (W := 21328) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c5830_1 : P.sumLeaves 24 5970752 64 = 21328 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 93293) rows (by decide) (by decide)).symm.trans contract5830_1

theorem c5830_2 : P.sumLeaves 24 5970816 128 = 153680 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5830) (lo := 896) (len := 128) (W := 153680) check rows elimOK (by decide) (by decide) cover5830 (by decide)
  decide +kernel

theorem h5830 : P.leaf 34 5830 = 175008 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(832, 0), (64, 21328), (128, 153680)]) (.cons c5830_0 (.cons c5830_1 (.cons c5830_2 (.nil)))) (by decide) (by decide))

theorem cover5831 : P.CoversSplit 24 10 5831 0xffff0000000000000000000000000000ffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [475, 515, 522, 536, 566, 573, 860, 916, 1202, 1209, 1259, 1264]) (by decide +kernel)

theorem c5831_0 : P.sumLeaves 24 5970944 1024 = 3193868 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5831) (lo := 0) (len := 1024) (W := 3193868) check rows elimOK (by decide) (by decide) cover5831 (by decide)
  decide +kernel

theorem h5831 : P.leaf 34 5831 = 3193868 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 3193868)]) (.cons c5831_0 (.nil)) (by decide) (by decide))

theorem h5832 : P.leaf 34 5832 = 9136 := by
  exact leaf_contract_factors (k := 34) (b := 19) (H := 5832) (ss := [(6, 1, 466), (26, 1, 472), (18, 1, 475), (35, 14, 487), (27, 1, 508), (14, 1, 509), (32, 1, 523), (33, 1, 536), (15, 1, 486), (17, 1, 565), (12, 1, 803), (30, 1, 1209), (31, 1, 1209), (28, 1, 465), (34, 1, 1259)]) (ids := [0, 1, 2, 3, 5, 6, 7, 8, 9, 11, 14, 17, 18, 19, 20, 21, 23, 27, 22]) (cs := [2, 3, 4, 5, 1, 6, 7, 8, 9, 10, 1, 11, 1, 1, 12, 1, 1, 13, 14, 15, 16, 17, 20, 18, 1, 1, 1, 19, 1, 1, 1, 1, 1, 1]) (bs := [18, 1]) (W := 9136) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem cover5833 : P.CoversSplit 24 10 5833 0xcccc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 515, 522, 523, 536, 573, 860, 916, 1202, 1209, 1251, 1259, 1308]) (by decide +kernel)

theorem c5833_0 : P.sumLeaves 24 5972992 1024 = 60800 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5833) (lo := 0) (len := 1024) (W := 60800) check rows elimOK (by decide) (by decide) cover5833 (by decide)
  decide +kernel

theorem h5833 : P.leaf 34 5833 = 60800 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 60800)]) (.cons c5833_0 (.nil)) (by decide) (by decide))

theorem cover5834 : P.CoversSplit 24 10 5834 0xa0a00000000000000000000000000000a0a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 515, 516, 522, 523, 536, 860, 916, 1202, 1209, 1210, 1259]) (by decide +kernel)

theorem c5834_0 : P.sumLeaves 24 5974016 832 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5834) (lo := 0) (len := 832) (W := 0) check rows elimOK (by decide) (by decide) cover5834 (by decide)
  decide +kernel

theorem contract5834_1 : P.leaf 30 93357 = 11488 := by
  exact leaf_contract_factors (k := 30) (b := 17) (H := 93357) (ss := [(6, 1, 467), (15, 2, 486), (14, 1, 509), (18, 1, 524), (4, 1, 566), (3, 1, 417), (12, 1, 803), (16, 1, 874), (30, 1, 1251), (26, 1, 465), (28, 1, 465), (31, 1, 516), (17, 1, 1266)]) (ids := [0, 3, 5, 6, 7, 8, 9, 11, 17, 18, 19, 21, 23, 25, 27, 20, 22]) (cs := [2, 1, 1, 3, 1, 4, 5, 6, 7, 8, 1, 9, 1, 2, 1, 1, 1, 10, 11, 12, 17, 13, 18, 14, 1, 15, 1, 16, 1, 1]) (bs := [15, 2]) (W := 11488) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c5834_1 : P.sumLeaves 24 5974848 64 = 11488 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 93357) rows (by decide) (by decide)).symm.trans contract5834_1

theorem c5834_2 : P.sumLeaves 24 5974912 128 = 80472 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5834) (lo := 896) (len := 128) (W := 80472) check rows elimOK (by decide) (by decide) cover5834 (by decide)
  decide +kernel

theorem h5834 : P.leaf 34 5834 = 91960 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(832, 0), (64, 11488), (128, 80472)]) (.cons c5834_0 (.cons c5834_1 (.cons c5834_2 (.nil)))) (by decide) (by decide))

theorem cover5835 : P.CoversSplit 24 10 5835 0xffff0000000000000000000000000000ffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 516, 522, 523, 536, 860, 916, 1202, 1209, 1259]) (by decide +kernel)

theorem c5835_0 : P.sumLeaves 24 5975040 1024 = 1166808 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5835) (lo := 0) (len := 1024) (W := 1166808) check rows elimOK (by decide) (by decide) cover5835 (by decide)
  decide +kernel

theorem h5835 : P.leaf 34 5835 = 1166808 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1166808)]) (.cons c5835_0 (.nil)) (by decide) (by decide))

theorem h5836 : P.leaf 34 5836 = 40272 := by
  exact leaf_contract_factors (k := 34) (b := 21) (H := 5836) (ss := [(6, 1, 466), (26, 1, 472), (27, 1, 508), (18, 1, 524), (35, 33, 536), (17, 1, 565), (30, 1, 1209), (31, 1, 1209), (28, 1, 465), (12, 1, 909), (32, 1, 1264), (34, 1, 1259), (33, 1, 1308)]) (ids := [0, 1, 2, 3, 5, 6, 7, 8, 9, 11, 12, 13, 14, 17, 18, 19, 20, 21, 23, 27, 22]) (cs := [2, 3, 4, 5, 1, 6, 7, 8, 9, 10, 1, 11, 12, 13, 14, 1, 1, 15, 16, 17, 18, 19, 22, 20, 1, 1, 1, 21, 1, 1, 1, 1, 1, 1]) (bs := [20, 1]) (W := 40272) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem cover5837 : P.CoversSplit 24 10 5837 0xcccc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 515, 522, 536, 573, 860, 916, 1202, 1209, 1251, 1259, 1264, 1308]) (by decide +kernel)

theorem c5837_0 : P.sumLeaves 24 5977088 1024 = 435048 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5837) (lo := 0) (len := 1024) (W := 435048) check rows elimOK (by decide) (by decide) cover5837 (by decide)
  decide +kernel

theorem h5837 : P.leaf 34 5837 = 435048 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 435048)]) (.cons c5837_0 (.nil)) (by decide) (by decide))

theorem cover5838 : P.CoversSplit 24 10 5838 0xa0a00000000000000000000000000000a0a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 515, 516, 522, 536, 860, 916, 1202, 1209, 1210, 1259, 1264]) (by decide +kernel)

theorem c5838_0 : P.sumLeaves 24 5978112 1024 = 531420 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5838) (lo := 0) (len := 1024) (W := 531420) check rows elimOK (by decide) (by decide) cover5838 (by decide)
  decide +kernel

theorem h5838 : P.leaf 34 5838 = 531420 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 531420)]) (.cons c5838_0 (.nil)) (by decide) (by decide))

theorem cover5839 : P.CoversSplit 24 10 5839 0xffff0000000000000000000000000000ffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 522, 536, 860, 916, 1202, 1209, 1258, 1259, 1264]) (by decide +kernel)

theorem c5839_0 : P.sumLeaves 24 5979136 1024 = 5180176 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5839) (lo := 0) (len := 1024) (W := 5180176) check rows elimOK (by decide) (by decide) cover5839 (by decide)
  decide +kernel

theorem h5839 : P.leaf 34 5839 = 5180176 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 5180176)]) (.cons c5839_0 (.nil)) (by decide) (by decide))

theorem cover5843 : P.CoversSplit 24 10 5843 0xffffffffa0a000000000000000000000ffffffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [475, 516, 573, 860, 1202, 1210, 1217, 1259, 1264, 1308]) (ps := [(14, [923], [916])]) (by decide +kernel)

theorem c5843_0 : P.sumLeaves 24 5983232 448 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5843) (lo := 0) (len := 448) (W := 0) check rows elimOK (by decide) (by decide) cover5843 (by decide)
  decide +kernel

theorem contract5843_1 : P.leaf 30 93495 = 75864 := by
  exact leaf_contract_factors (k := 30) (b := 20) (H := 93495) (ss := [(6, 1, 478), (12, 1, 478), (27, 1, 573), (8, 1, 580), (18, 1, 580), (14, 1, 923), (29, 1, 916), (16, 1, 1265), (20, 1, 1657), (21, 1, 1658)]) (ids := [0, 1, 2, 3, 5, 7, 8, 9, 13, 15, 17, 20, 22, 24, 26, 28, 29, 11, 21, 23]) (cs := [2, 3, 4, 5, 1, 6, 1, 7, 8, 9, 1, 19, 1, 10, 1, 11, 1, 12, 1, 1, 13, 20, 14, 21, 15, 1, 16, 1, 17, 18]) (bs := [17, 3]) (W := 75864) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c5843_1 : P.sumLeaves 24 5983680 64 = 75864 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 93495) rows (by decide) (by decide)).symm.trans contract5843_1

theorem c5843_2 : P.sumLeaves 24 5983744 512 = 1926432 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5843) (lo := 512) (len := 512) (W := 1926432) check rows elimOK (by decide) (by decide) cover5843 (by decide)
  decide +kernel

theorem h5843 : P.leaf 34 5843 = 2002296 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(448, 0), (64, 75864), (512, 1926432)]) (.cons c5843_0 (.cons c5843_1 (.cons c5843_2 (.nil)))) (by decide) (by decide))

theorem cover5844 : P.CoversSplit 24 10 5844 0xfcfcfcfca0a000000000000000000000a0a0a4a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 475, 508, 516, 536, 573, 860, 1202, 1210, 1259, 1264]) (ps := [(6, [479], [472])]) (by decide +kernel)

theorem c5844_0 : P.sumLeaves 24 5984256 1024 = 218140 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5844) (lo := 0) (len := 1024) (W := 218140) check rows elimOK (by decide) (by decide) cover5844 (by decide)
  decide +kernel

theorem h5844 : P.leaf 34 5844 = 218140 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 218140)]) (.cons c5844_0 (.nil)) (by decide) (by decide))

theorem cover5845 : P.CoversSplit 24 10 5845 0xffffffffa0a000000000000000000000ffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 475, 516, 536, 573, 860, 916, 1202, 1210, 1259, 1264]) (by decide +kernel)

theorem c5845_0 : P.sumLeaves 24 5985280 1024 = 5075216 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5845) (lo := 0) (len := 1024) (W := 5075216) check rows elimOK (by decide) (by decide) cover5845 (by decide)
  decide +kernel

theorem h5845 : P.leaf 34 5845 = 5075216 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 5075216)]) (.cons c5845_0 (.nil)) (by decide) (by decide))

theorem cover5846 : P.CoversSplit 24 10 5846 0xffffffffa0a000000000000000000000a0a0a5a50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 475, 516, 573, 860, 916, 1202, 1210, 1259, 1264, 1308]) (by decide +kernel)

theorem c5846_0 : P.sumLeaves 24 5986304 1024 = 2807514 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5846) (lo := 0) (len := 1024) (W := 2807514) check rows elimOK (by decide) (by decide) cover5846 (by decide)
  decide +kernel

theorem h5846 : P.leaf 34 5846 = 2807514 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 2807514)]) (.cons c5846_0 (.nil)) (by decide) (by decide))

theorem cover5847 : P.CoversSplit 24 10 5847 0xffffffffa0a000000000000000000000ffffffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [475, 516, 573, 860, 916, 1202, 1210, 1217, 1259, 1264, 1308]) (by decide +kernel)

theorem c5847_0 : P.sumLeaves 24 5987328 1024 = 13135988 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5847) (lo := 0) (len := 1024) (W := 13135988) check rows elimOK (by decide) (by decide) cover5847 (by decide)
  decide +kernel

theorem h5847 : P.leaf 34 5847 = 13135988 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 13135988)]) (.cons c5847_0 (.nil)) (by decide) (by decide))

theorem cover5848 : P.CoversSplit 24 10 5848 0xfcfcfcfca0a000000000000000000000a0a0a0a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 508, 516, 536, 573, 860, 916, 1202, 1210, 1258, 1259, 1264, 1308]) (ps := [(6, [467], [472]), (8, [537], [516]), (14, [487, 509], [487, 860])]) (by decide +kernel)

theorem c5848_0 : P.sumLeaves 24 5988352 832 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5848) (lo := 0) (len := 832) (W := 0) check rows elimOK (by decide) (by decide) cover5848 (by decide)
  decide +kernel

theorem contract5848_1 : P.leaf 30 93581 = 37664 := by
  exact leaf_contract_factors (k := 30) (b := 18) (H := 93581) (ss := [(6, 1, 467), (18, 1, 475), (15, 2, 486), (14, 1, 487), (31, 1, 536), (8, 1, 537), (26, 1, 516), (17, 1, 537), (2, 1, 558), (12, 1, 803), (28, 1, 860), (16, 1, 874)]) (ids := [1, 2, 3, 5, 7, 8, 9, 11, 17, 18, 19, 20, 23, 25, 27, 28, 21, 22]) (cs := [1, 2, 3, 4, 1, 5, 1, 6, 7, 8, 1, 9, 1, 1, 1, 1, 1, 10, 11, 12, 13, 18, 19, 14, 1, 15, 1, 16, 17, 1]) (bs := [16, 2]) (W := 37664) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c5848_1 : P.sumLeaves 24 5989184 64 = 37664 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 93581) rows (by decide) (by decide)).symm.trans contract5848_1

theorem c5848_2 : P.sumLeaves 24 5989248 128 = 337316 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5848) (lo := 896) (len := 128) (W := 337316) check rows elimOK (by decide) (by decide) cover5848 (by decide)
  decide +kernel

theorem h5848 : P.leaf 34 5848 = 374980 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(832, 0), (64, 37664), (128, 337316)]) (.cons c5848_0 (.cons c5848_1 (.cons c5848_2 (.nil)))) (by decide) (by decide))

theorem cover5849 : P.CoversSplit 24 10 5849 0xffffffffa0a000000000000000000000ffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 516, 536, 573, 860, 916, 1202, 1210, 1258, 1259, 1264, 1308]) (ps := [(14, [923], [487])]) (by decide +kernel)

theorem c5849_0 : P.sumLeaves 24 5989376 1024 = 1750924 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5849) (lo := 0) (len := 1024) (W := 1750924) check rows elimOK (by decide) (by decide) cover5849 (by decide)
  decide +kernel

theorem h5849 : P.leaf 34 5849 = 1750924 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1750924)]) (.cons c5849_0 (.nil)) (by decide) (by decide))

theorem cover5850 : P.CoversSplit 24 10 5850 0xffffffffa0a000000000000000000000a0a0a0a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 516, 536, 573, 860, 916, 1202, 1210, 1258, 1259, 1264, 1308]) (ps := [(8, [537], [516]), (14, [509], [860, 916])]) (by decide +kernel)

theorem c5850_0 : P.sumLeaves 24 5990400 448 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5850) (lo := 0) (len := 448) (W := 0) check rows elimOK (by decide) (by decide) cover5850 (by decide)
  decide +kernel

theorem contract5850_1 : P.leaf 30 93607 = 110384 := by
  exact leaf_contract_factors (k := 30) (b := 20) (H := 93607) (ss := [(15, 1, 486), (14, 1, 509), (27, 1, 573), (8, 1, 580), (18, 1, 580), (12, 1, 867), (29, 1, 916), (16, 1, 1265), (20, 1, 1657), (21, 1, 1658)]) (ids := [0, 1, 2, 3, 4, 5, 7, 8, 9, 15, 17, 20, 21, 22, 24, 26, 28, 29, 11, 23]) (cs := [2, 3, 4, 5, 6, 7, 1, 8, 9, 10, 1, 20, 1, 1, 1, 11, 1, 12, 1, 1, 13, 14, 15, 21, 16, 1, 17, 1, 18, 19]) (bs := [18, 2]) (W := 110384) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c5850_1 : P.sumLeaves 24 5990848 64 = 110384 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 93607) rows (by decide) (by decide)).symm.trans contract5850_1

theorem c5850_2 : P.sumLeaves 24 5990912 512 = 1509656 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5850) (lo := 512) (len := 512) (W := 1509656) check rows elimOK (by decide) (by decide) cover5850 (by decide)
  decide +kernel

theorem h5850 : P.leaf 34 5850 = 1620040 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(448, 0), (64, 110384), (512, 1509656)]) (.cons c5850_0 (.cons c5850_1 (.cons c5850_2 (.nil)))) (by decide) (by decide))

theorem cover5851 : P.CoversSplit 24 10 5851 0xffffffffa0a000000000000000000000ffffffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [516, 536, 573, 860, 916, 1202, 1210, 1217, 1258, 1259, 1264, 1308]) (ps := [(14, [923], [916])]) (by decide +kernel)

theorem c5851_0 : P.sumLeaves 24 5991424 1024 = 4663832 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5851) (lo := 0) (len := 1024) (W := 4663832) check rows elimOK (by decide) (by decide) cover5851 (by decide)
  decide +kernel

theorem h5851 : P.leaf 34 5851 = 4663832 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 4663832)]) (.cons c5851_0 (.nil)) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(5629, 48), (5631, 24), (5811, 6), (5812, 24), (5813, 48), (5815, 24), (5820, 12), (5821, 24), (5823, 12), (5826, 24), (5827, 48), (5828, 48), (5829, 48), (5830, 48), (5831, 48), (5832, 48), (5833, 48), (5834, 48), (5835, 48), (5836, 48), (5837, 48), (5838, 48), (5839, 48), (5843, 24), (5844, 48), (5845, 48), (5846, 48), (5847, 48), (5848, 48), (5849, 48), (5850, 48), (5851, 48)]

theorem segOK : checkSeg 16 perms 5629 5852 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 5629 5852 1278 9876852744 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 9876852744)
    (SegSum.cons (w := 48) h5629 (SegSum.cons (w := 24) h5631 (SegSum.cons (w := 6) h5811 (SegSum.cons (w := 24) h5812 (SegSum.cons (w := 48) h5813 (SegSum.cons (w := 24) h5815 (SegSum.cons (w := 12) h5820 (SegSum.cons (w := 24) h5821 (SegSum.cons (w := 12) h5823 (SegSum.cons (w := 24) h5826 (SegSum.cons (w := 48) h5827 (SegSum.cons (w := 48) h5828 (SegSum.cons (w := 48) h5829 (SegSum.cons (w := 48) h5830 (SegSum.cons (w := 48) h5831 (SegSum.cons (w := 48) h5832 (SegSum.cons (w := 48) h5833 (SegSum.cons (w := 48) h5834 (SegSum.cons (w := 48) h5835 (SegSum.cons (w := 48) h5836 (SegSum.cons (w := 48) h5837 (SegSum.cons (w := 48) h5838 (SegSum.cons (w := 48) h5839 (SegSum.cons (w := 24) h5843 (SegSum.cons (w := 48) h5844 (SegSum.cons (w := 48) h5845 (SegSum.cons (w := 48) h5846 (SegSum.cons (w := 48) h5847 (SegSum.cons (w := 48) h5848 (SegSum.cons (w := 48) h5849 (SegSum.cons (w := 48) h5850 (SegSum.cons (w := 48) h5851 (show SegSum (P.leaf 34) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S4N1.C0.S32
