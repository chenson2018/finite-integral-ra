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

namespace RACert.S6N0.C0.S60

open RACert RACert.Problem

theorem cover89023 : P.CoversSplit 26 10 89023 0xffffffff00000000fffffffa00000000ffffffff00000030fafafafa00000000fffff0f000000000fafaf0f000000000fffff0f000000030fafaf0f00000000000000000000000000000000000000000003300330000000000320032000000000000000000000000000000000000000000330030000000000032003000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [538, 922, 972, 979, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem contract89023_0 : P.leaf 32 1424368 = 22512 := by
  exact leaf_contract_factors (k := 32) (b := 17) (H := 1424368) (ss := [(22, 1, 433), (2, 1, 488), (3, 1, 531), (4, 1, 586), (7, 1, 825), (8, 1, 1217), (16, 1, 1210), (18, 1, 1210), (29, 0, 1322), (33, 1, 1273), (6, 1, 636), (17, 0, 1322), (31, 0, 1322), (27, 1, 930), (9, 1, 1609)]) (ids := [3, 8, 9, 10, 11, 12, 13, 17, 18, 19, 21, 23, 24, 26, 28, 30, 22]) (cs := [1, 1, 1, 2, 1, 1, 1, 1, 3, 4, 5, 6, 7, 8, 1, 0, 1, 9, 10, 11, 1, 12, 18, 13, 14, 1, 15, 0, 16, 0, 17, 1]) (bs := [16, 1]) (W := 22512) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c89023_0 : P.sumLeaves 26 91159552 64 = 22512 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1424368) rows (by decide) (by decide)).symm.trans contract89023_0

theorem contract89023_1 : P.leaf 32 1424369 = 27792 := by
  exact leaf_contract_factors (k := 32) (b := 16) (H := 1424369) (ss := [(22, 1, 433), (2, 1, 488), (3, 1, 531), (4, 1, 580), (5, 1, 629), (7, 1, 825), (8, 1, 1217), (16, 1, 1210), (18, 1, 1210), (29, 0, 1322), (33, 1, 1273), (6, 1, 636), (17, 0, 1322), (31, 0, 1322), (27, 1, 930), (9, 1, 1609)]) (ids := [8, 9, 11, 12, 13, 17, 19, 21, 24, 26, 28, 30, 10, 18, 22, 23]) (cs := [1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 14, 4, 5, 6, 1, 0, 1, 7, 15, 8, 1, 9, 16, 17, 10, 1, 11, 0, 12, 0, 13, 1]) (bs := [12, 4]) (W := 27792) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c89023_1 : P.sumLeaves 26 91159616 64 = 27792 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1424369) rows (by decide) (by decide)).symm.trans contract89023_1

theorem c89023_2 : P.sumLeaves 26 91159680 632 = 73908241 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89023) (lo := 128) (len := 632) (W := 73908241) check rows elimOK (by decide) (by decide) cover89023 (by decide)
  decide +kernel

theorem c89023_3 : P.sumLeaves 26 91160312 232 = 181059851 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89023) (lo := 760) (len := 232) (W := 181059851) check rows elimOK (by decide) (by decide) cover89023 (by decide)
  decide +kernel

theorem c89023_4 : P.sumLeaves 26 91160544 32 = 100421234 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89023) (lo := 992) (len := 32) (W := 100421234) check rows elimOK (by decide) (by decide) cover89023 (by decide)
  decide +kernel

theorem h89023 : P.leaf 36 89023 = 355439630 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(64, 22512), (64, 27792), (632, 73908241), (232, 181059851), (32, 100421234)]) (.cons c89023_0 (.cons c89023_1 (.cons c89023_2 (.cons c89023_3 (.cons c89023_4 (.nil)))))) (by decide) (by decide))

theorem cover89029 : P.CoversSplit 26 10 89029 0xff000000ff030501ff000000ff030500ff000000ff030500fa000000c8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 922, 923, 972, 979, 1266, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f89029 (i : ℕ) := rowWeight keep4 twice4 i * P.leaf 26 (91165696 + i)

theorem c89029_0 : rowSum f89029 0 1024 = 1488936 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 89029) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover89029 (by decide)
  decide +kernel

theorem sum89029 : rowSum f89029 0 1024 = 1488936 :=
  c89029_0

theorem h89029 : P.leaf 36 89029 = 1488936 :=
  leaf_weighted (k := 26) (d := 10) (H := 89029) (keep := keep4) (twice := twice4) rows (by decide) (by decide) bal4 (invRow4 (H := 89029) (by decide) (by decide +kernel)) sum89029

theorem cover89030 : P.CoversSplit 26 10 89030 0xff000000ff030501ff000000ff030500ff000000ff030500fa000000c8000000000000000000000000000000000000000000000000000000000000000000000000000000333301010000000033330100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 874, 922, 972, 979, 1266, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c89030_0 : P.sumLeaves 26 91166720 384 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89030) (lo := 0) (len := 384) (W := 0) check rows elimOK (by decide) (by decide) cover89030 (by decide)
  decide +kernel

theorem contract89030_1 : P.leaf 32 1424486 = 15528 := by
  exact leaf_contract_factors (k := 32) (b := 18) (H := 1424486) (ss := [(3, 1, 531), (29, 0, 979), (33, 0, 979), (19, 1, 1273), (20, 1, 1665), (15, 1, 865), (14, 1, 872), (2, 1, 409), (8, 1, 515), (16, 1, 515), (17, 1, 516), (18, 1, 1210), (27, 1, 538), (21, 1, 1259)]) (ids := [2, 3, 4, 5, 7, 8, 9, 10, 11, 20, 21, 24, 26, 28, 29, 30, 22, 23]) (cs := [1, 1, 2, 3, 4, 5, 1, 6, 7, 8, 9, 10, 1, 1, 1, 1, 1, 1, 1, 1, 11, 12, 18, 19, 13, 1, 14, 0, 15, 16, 17, 0]) (bs := [16, 2]) (W := 15528) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c89030_1 : P.sumLeaves 26 91167104 64 = 15528 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1424486) rows (by decide) (by decide)).symm.trans contract89030_1

theorem c89030_2 : P.sumLeaves 26 91167168 576 = 1471772 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89030) (lo := 448) (len := 576) (W := 1471772) check rows elimOK (by decide) (by decide) cover89030 (by decide)
  decide +kernel

theorem h89030 : P.leaf 36 89030 = 1487300 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(384, 0), (64, 15528), (576, 1471772)]) (.cons c89030_0 (.cons c89030_1 (.cons c89030_2 (.nil)))) (by decide) (by decide))

theorem cover89031 : P.CoversSplit 26 10 89031 0xff000000ff030501ff000000ff030500ff000000ff030500fa000000c8000000000000000000000000000000000000000000000000000000000000000000000000000000333301010000000033330100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 922, 972, 979, 1266, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c89031_0 : P.sumLeaves 26 91167744 1024 = 14280416 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89031) (lo := 0) (len := 1024) (W := 14280416) check rows elimOK (by decide) (by decide) cover89031 (by decide)
  decide +kernel

theorem h89031 : P.leaf 36 89031 = 14280416 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 14280416)]) (.cons c89031_0 (.nil)) (by decide) (by decide))

theorem cover89037 : P.CoversSplit 26 10 89037 0xffff0000fffc0504ffff0000fffc0500ffff0000fffc0500fafa0000c8c80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 922, 923, 972, 979, 1266, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c89037_0 : P.sumLeaves 26 91173888 989 = 3490600 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89037) (lo := 0) (len := 989) (W := 3490600) check rows elimOK (by decide) (by decide) cover89037 (by decide)
  decide +kernel

theorem c89037_1 : P.sumLeaves 26 91174877 35 = 1059968 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89037) (lo := 989) (len := 35) (W := 1059968) check rows elimOK (by decide) (by decide) cover89037 (by decide)
  decide +kernel

theorem h89037 : P.leaf 36 89037 = 4550568 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(989, 3490600), (35, 1059968)]) (.cons c89037_0 (.cons c89037_1 (.nil))) (by decide) (by decide))

theorem cover89038 : P.CoversSplit 26 10 89038 0xffff0000fffc0504ffff0000fffc0500ffff0000fffc0500fafa0000c8c800000000000000000000000000000000000000000000000000000000000000000000ffff0000ffcc0504ffff0000ffcc0500ffff000000000000fafa0000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 874, 922, 972, 979, 1266, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c89038_0 : P.sumLeaves 26 91174912 819 = 1637620 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89038) (lo := 0) (len := 819) (W := 1637620) check rows elimOK (by decide) (by decide) cover89038 (by decide)
  decide +kernel

theorem c89038_1 : P.sumLeaves 26 91175731 193 = 3337620 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89038) (lo := 819) (len := 193) (W := 3337620) check rows elimOK (by decide) (by decide) cover89038 (by decide)
  decide +kernel

theorem c89038_2 : P.sumLeaves 26 91175924 12 = 1600448 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89038) (lo := 1012) (len := 12) (W := 1600448) check rows elimOK (by decide) (by decide) cover89038 (by decide)
  decide +kernel

theorem h89038 : P.leaf 36 89038 = 6575688 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(819, 1637620), (193, 3337620), (12, 1600448)]) (.cons c89038_0 (.cons c89038_1 (.cons c89038_2 (.nil)))) (by decide) (by decide))

theorem cover89039 : P.CoversSplit 26 10 89039 0xffff0000fffc0504ffff0000fffc0500ffff0000fffc0500fafa0000c8c800000000000000000000000000000000000000000000000000000000000000000000ffff0000ffcc0504ffff0000ffcc0500ffff000000000000fafa0000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 922, 972, 979, 1266, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c89039_0 : P.sumLeaves 26 91175936 819 = 7039120 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89039) (lo := 0) (len := 819) (W := 7039120) check rows elimOK (by decide) (by decide) cover89039 (by decide)
  decide +kernel

theorem c89039_1 : P.sumLeaves 26 91176755 193 = 18728768 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89039) (lo := 819) (len := 193) (W := 18728768) check rows elimOK (by decide) (by decide) cover89039 (by decide)
  decide +kernel

theorem c89039_2 : P.sumLeaves 26 91176948 12 = 4301760 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89039) (lo := 1012) (len := 12) (W := 4301760) check rows elimOK (by decide) (by decide) cover89039 (by decide)
  decide +kernel

theorem h89039 : P.leaf 36 89039 = 30069648 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(819, 7039120), (193, 18728768), (12, 4301760)]) (.cons c89039_0 (.cons c89039_1 (.cons c89039_2 (.nil)))) (by decide) (by decide))

theorem cover89046 : P.CoversSplit 26 10 89046 0xff000000ff030501ff000000ff030500ff000000ff030500fa000000c8000000050005000501050100000000000000000500050005010500000000000000000000000000333301010000000033330100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 874, 922, 972, 979, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f89046 (i : ℕ) := rowWeight keep4 twice4 i * P.leaf 26 (91183104 + i)

theorem c89046_0 : rowSum f89046 0 1024 = 75966616 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 89046) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover89046 (by decide)
  decide +kernel

theorem sum89046 : rowSum f89046 0 1024 = 75966616 :=
  c89046_0

theorem h89046 : P.leaf 36 89046 = 75966616 :=
  leaf_weighted (k := 26) (d := 10) (H := 89046) (keep := keep4) (twice := twice4) rows (by decide) (by decide) bal4 (invRow4 (H := 89046) (by decide) (by decide +kernel)) sum89046

theorem cover89047 : P.CoversSplit 26 10 89047 0xff000000ff030501ff000000ff030500ff000000ff030500fa000000c8000000050005000501050100000000000000000500050005010500000000000000000000000000333301010000000033330100000000000000000000000000000000000000000001010101000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 922, 972, 979, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f89047 (i : ℕ) := rowWeight keep4 twice4 i * P.leaf 26 (91184128 + i)

theorem c89047_0 : rowSum f89047 0 1024 = 169810808 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 89047) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover89047 (by decide)
  decide +kernel

theorem sum89047 : rowSum f89047 0 1024 = 169810808 :=
  c89047_0

theorem h89047 : P.leaf 36 89047 = 169810808 :=
  leaf_weighted (k := 26) (d := 10) (H := 89047) (keep := keep4) (twice := twice4) rows (by decide) (by decide) bal4 (invRow4 (H := 89047) (by decide) (by decide +kernel)) sum89047

theorem cover89052 : P.CoversSplit 26 10 89052 0xffff0000fffc0504ffff0000fffc0500ffff0000fffc0500fafa0000c8c80000050505050504050400000000000000000505050505040500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 874, 922, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c89052_0 : P.sumLeaves 26 91189248 947 = 5548848 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89052) (lo := 0) (len := 947) (W := 5548848) check rows elimOK (by decide) (by decide) cover89052 (by decide)
  decide +kernel

theorem c89052_1 : P.sumLeaves 26 91190195 77 = 13199912 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89052) (lo := 947) (len := 77) (W := 13199912) check rows elimOK (by decide) (by decide) cover89052 (by decide)
  decide +kernel

theorem h89052 : P.leaf 36 89052 = 18748760 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(947, 5548848), (77, 13199912)]) (.cons c89052_0 (.cons c89052_1 (.nil))) (by decide) (by decide))

theorem cover89053 : P.CoversSplit 26 10 89053 0xffff0000fffc0504ffff0000fffc0500ffff0000fffc0500fafa0000c8c80000050505050504050400000000000000000505050505040500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 922, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c89053_0 : P.sumLeaves 26 91190272 947 = 23005622 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89053) (lo := 0) (len := 947) (W := 23005622) check rows elimOK (by decide) (by decide) cover89053 (by decide)
  decide +kernel

theorem c89053_1 : P.sumLeaves 26 91191219 77 = 31864072 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89053) (lo := 947) (len := 77) (W := 31864072) check rows elimOK (by decide) (by decide) cover89053 (by decide)
  decide +kernel

theorem h89053 : P.leaf 36 89053 = 54869694 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(947, 23005622), (77, 31864072)]) (.cons c89053_0 (.cons c89053_1 (.nil))) (by decide) (by decide))

theorem cover89054 : P.CoversSplit 26 10 89054 0xffff0000fffc0504ffff0000fffc0500ffff0000fffc0500fafa0000c8c800000505050505040504000000000000000005050505050405000000000000000000ffff0000ffcc0504ffff0000ffcc0500ffff0000cc000400fafa0000c80000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 874, 922, 972, 979, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c89054_0 : P.sumLeaves 26 91191296 511 = 69557988 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89054) (lo := 0) (len := 511) (W := 69557988) check rows elimOK (by decide) (by decide) cover89054 (by decide)
  decide +kernel

theorem c89054_1 : P.sumLeaves 26 91191807 435 = 79945965 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89054) (lo := 511) (len := 435) (W := 79945965) check rows elimOK (by decide) (by decide) cover89054 (by decide)
  decide +kernel

theorem c89054_2 : P.sumLeaves 26 91192242 78 = 134635432 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89054) (lo := 946) (len := 78) (W := 134635432) check rows elimOK (by decide) (by decide) cover89054 (by decide)
  decide +kernel

theorem h89054 : P.leaf 36 89054 = 284139385 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(511, 69557988), (435, 79945965), (78, 134635432)]) (.cons c89054_0 (.cons c89054_1 (.cons c89054_2 (.nil)))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(89023, 720), (89029, 360), (89030, 720), (89031, 720), (89037, 720), (89038, 720), (89039, 720), (89046, 360), (89047, 360), (89052, 720), (89053, 720), (89054, 720)]

theorem segOK : checkSeg 20 perms 89023 89055 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 89023 89055 7560 643531873680 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 643531873680)
    (SegSum.cons (w := 720) h89023 (SegSum.cons (w := 360) h89029 (SegSum.cons (w := 720) h89030 (SegSum.cons (w := 720) h89031 (SegSum.cons (w := 720) h89037 (SegSum.cons (w := 720) h89038 (SegSum.cons (w := 720) h89039 (SegSum.cons (w := 360) h89046 (SegSum.cons (w := 360) h89047 (SegSum.cons (w := 720) h89052 (SegSum.cons (w := 720) h89053 (SegSum.cons (w := 720) h89054 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))) (by decide)

end RACert.S6N0.C0.S60
