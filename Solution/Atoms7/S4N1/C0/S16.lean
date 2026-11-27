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

namespace RACert.S4N1.C0.S16

open RACert RACert.Problem

theorem cover1967 : P.CoversSplit 24 10 1967 0xffff0000000000000000000000000000a0a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [515, 517, 522, 860, 872, 916, 1209, 1251, 1258, 1259, 1308]) (ps := [(16, [529], [1258])]) (by decide +kernel)

theorem c1967_0 : P.sumLeaves 24 2014208 832 = 1176240 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1967) (lo := 0) (len := 832) (W := 1176240) check rows elimOK (by decide) (by decide) cover1967 (by decide)
  decide +kernel

theorem contract1967_1 : P.leaf 30 31485 = 132128 := by
  exact leaf_contract_factors (k := 30) (b := 19) (H := 31485) (ss := [(16, 1, 529), (12, 1, 867), (31, 1, 872), (14, 1, 874), (8, 1, 531), (26, 1, 517), (28, 1, 860), (30, 1, 1209), (18, 1, 1265), (20, 1, 1314), (21, 1, 1315)]) (ids := [0, 1, 2, 3, 4, 7, 8, 9, 13, 15, 17, 20, 21, 25, 27, 5, 11, 22, 23]) (cs := [2, 3, 4, 5, 6, 17, 1, 7, 8, 9, 1, 18, 1, 10, 1, 11, 1, 12, 1, 1, 13, 14, 19, 20, 1, 15, 1, 16, 1, 1]) (bs := [15, 4]) (W := 132128) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1967_1 : P.sumLeaves 24 2015040 64 = 132128 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 31485) rows (by decide) (by decide)).symm.trans contract1967_1

theorem c1967_2 : P.sumLeaves 24 2015104 128 = 5152338 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1967) (lo := 896) (len := 128) (W := 5152338) check rows elimOK (by decide) (by decide) cover1967 (by decide)
  decide +kernel

theorem h1967 : P.leaf 34 1967 = 6460706 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(832, 1176240), (64, 132128), (128, 5152338)]) (.cons c1967_0 (.cons c1967_1 (.cons c1967_2 (.nil)))) (by decide) (by decide))

theorem cover1972 : P.CoversSplit 24 10 1972 0xff00000000000000ff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ff00000000000000ff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 468, 473, 475, 508, 517, 559, 867, 872, 915, 916, 1209, 1251, 1258]) (by decide +kernel)

theorem c1972_0 : P.sumLeaves 24 2019328 384 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1972) (lo := 0) (len := 384) (W := 0) check rows elimOK (by decide) (by decide) cover1972 (by decide)
  decide +kernel

theorem contract1972_1 : P.leaf 30 31558 = 15680 := by
  exact leaf_contract_factors (k := 30) (b := 16) (H := 31558) (ss := [(29, 2, 475), (2, 1, 480), (5, 1, 524), (31, 1, 872), (11, 1, 901), (6, 1, 458), (10, 1, 458), (12, 1, 818), (14, 1, 929), (16, 1, 486), (13, 1, 922), (18, 1, 922), (19, 1, 929), (30, 1, 1209)]) (ids := [1, 2, 6, 7, 13, 15, 18, 19, 20, 22, 23, 24, 25, 26, 5, 21]) (cs := [1, 2, 3, 1, 1, 16, 4, 5, 1, 1, 1, 1, 1, 6, 1, 7, 1, 1, 8, 9, 10, 17, 11, 12, 13, 14, 15, 1, 1, 1]) (bs := [14, 2]) (W := 15680) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1972_1 : P.sumLeaves 24 2019712 64 = 15680 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 31558) rows (by decide) (by decide)).symm.trans contract1972_1

theorem contract1972_2 : P.leaf 30 31559 = 20032 := by
  exact leaf_contract_factors (k := 30) (b := 17) (H := 31559) (ss := [(29, 2, 475), (2, 1, 480), (31, 1, 872), (11, 1, 901), (6, 1, 458), (10, 1, 458), (12, 1, 818), (14, 1, 929), (16, 1, 486), (13, 1, 922), (18, 1, 922), (19, 1, 929), (30, 1, 1209)]) (ids := [1, 2, 3, 6, 7, 13, 15, 18, 19, 20, 22, 23, 24, 25, 26, 5, 21]) (cs := [1, 2, 3, 4, 1, 17, 5, 6, 1, 1, 1, 1, 1, 7, 1, 8, 1, 1, 9, 10, 11, 18, 12, 13, 14, 15, 16, 1, 1, 1]) (bs := [15, 2]) (W := 20032) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1972_2 : P.sumLeaves 24 2019776 64 = 20032 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 31559) rows (by decide) (by decide)).symm.trans contract1972_2

theorem c1972_3 : P.sumLeaves 24 2019840 512 = 206592 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1972) (lo := 512) (len := 512) (W := 206592) check rows elimOK (by decide) (by decide) cover1972 (by decide)
  decide +kernel

theorem h1972 : P.leaf 34 1972 = 242304 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(384, 0), (64, 15680), (64, 20032), (512, 206592)]) (.cons c1972_0 (.cons c1972_1 (.cons c1972_2 (.cons c1972_3 (.nil))))) (by decide) (by decide))

theorem cover1973 : P.CoversSplit 24 10 1973 0xff00000000000000ff00000000000000a000000000000000a0000000000000000000000000000000000000000000000000000000000000000000000000000000ff00000000000000ff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [468, 473, 475, 517, 559, 860, 872, 915, 916, 1209, 1251, 1258, 1308]) (by decide +kernel)

theorem c1973_0 : P.sumLeaves 24 2020352 384 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1973) (lo := 0) (len := 384) (W := 0) check rows elimOK (by decide) (by decide) cover1973 (by decide)
  decide +kernel

theorem contract1973_1 : P.leaf 30 31574 = 84672 := by
  exact leaf_contract_factors (k := 30) (b := 18) (H := 31574) (ss := [(29, 2, 475), (2, 1, 480), (5, 1, 524), (31, 1, 872), (11, 1, 901), (12, 1, 818), (14, 1, 929), (19, 1, 929), (18, 1, 965), (13, 1, 922), (30, 1, 1209), (16, 1, 1265)]) (ids := [2, 4, 6, 7, 8, 13, 15, 18, 19, 20, 21, 22, 23, 24, 25, 26, 1, 5]) (cs := [1, 18, 2, 1, 3, 19, 4, 5, 6, 1, 1, 1, 1, 7, 1, 8, 1, 1, 9, 10, 11, 12, 13, 14, 15, 16, 17, 1, 1, 1]) (bs := [16, 2]) (W := 84672) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1973_1 : P.sumLeaves 24 2020736 64 = 84672 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 31574) rows (by decide) (by decide)).symm.trans contract1973_1

theorem contract1973_2 : P.leaf 30 31575 = 113856 := by
  exact leaf_contract_factors (k := 30) (b := 19) (H := 31575) (ss := [(29, 2, 475), (2, 1, 480), (31, 1, 872), (11, 1, 901), (12, 1, 818), (14, 1, 929), (19, 1, 929), (18, 1, 965), (13, 1, 922), (30, 1, 1209), (16, 1, 1265)]) (ids := [1, 2, 3, 4, 6, 7, 8, 13, 15, 18, 19, 20, 21, 22, 23, 24, 25, 26, 5]) (cs := [1, 2, 3, 4, 5, 20, 6, 7, 8, 1, 1, 1, 1, 9, 1, 10, 1, 1, 11, 12, 13, 14, 15, 16, 17, 18, 19, 1, 1, 1]) (bs := [18, 1]) (W := 113856) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1973_2 : P.sumLeaves 24 2020800 64 = 113856 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 31575) rows (by decide) (by decide)).symm.trans contract1973_2

theorem c1973_3 : P.sumLeaves 24 2020864 512 = 1290136 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1973) (lo := 512) (len := 512) (W := 1290136) check rows elimOK (by decide) (by decide) cover1973 (by decide)
  decide +kernel

theorem h1973 : P.leaf 34 1973 = 1488664 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(384, 0), (64, 84672), (64, 113856), (512, 1290136)]) (.cons c1973_0 (.cons c1973_1 (.cons c1973_2 (.cons c1973_3 (.nil))))) (by decide) (by decide))

theorem cover1974 : P.CoversSplit 24 10 1974 0xffff000000000000ffff00000000000000000000000000000000000000000000ffcc000000000000000000000000000000000000000000000000000000000000ffff000000000000ffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 468, 517, 860, 867, 872, 915, 916, 1209, 1251, 1258]) (by decide +kernel)

theorem c1974_0 : P.sumLeaves 24 2021376 1024 = 3451514 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1974) (lo := 0) (len := 1024) (W := 3451514) check rows elimOK (by decide) (by decide) cover1974 (by decide)
  decide +kernel

theorem h1974 : P.leaf 34 1974 = 3451514 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 3451514)]) (.cons c1974_0 (.nil)) (by decide) (by decide))

theorem cover1975 : P.CoversSplit 24 10 1975 0xffff000000000000ffff000000000000a0a0000000000000a0a0000000000000ffcc0000000000000000000000000000a0800000000000000000000000000000ffff000000000000ffff00000000000000000000000000000000000000000000ffcc000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [468, 517, 860, 872, 915, 916, 1209, 1251, 1258, 1308]) (by decide +kernel)

theorem c1975_0 : P.sumLeaves 24 2022400 768 = 2484324 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1975) (lo := 0) (len := 768) (W := 2484324) check rows elimOK (by decide) (by decide) cover1975 (by decide)
  decide +kernel

theorem contract1975_1 : P.leaf 30 31612 = 100944 := by
  exact leaf_contract_factors (k := 30) (b := 19) (H := 31612) (ss := [(31, 1, 468), (5, 1, 524), (8, 1, 531), (26, 1, 517), (16, 1, 531), (28, 1, 860), (14, 1, 874), (30, 1, 1209), (18, 1, 1265), (20, 1, 1314), (21, 1, 1315)]) (ids := [0, 1, 2, 4, 7, 8, 9, 10, 11, 13, 15, 17, 20, 21, 25, 27, 5, 22, 23]) (cs := [2, 3, 4, 1, 5, 18, 1, 6, 7, 8, 9, 10, 1, 11, 1, 12, 1, 13, 1, 1, 14, 15, 19, 20, 1, 16, 1, 17, 1, 1]) (bs := [16, 3]) (W := 100944) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1975_1 : P.sumLeaves 24 2023168 64 = 100944 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 31612) rows (by decide) (by decide)).symm.trans contract1975_1

theorem contract1975_2 : P.leaf 30 31613 = 122224 := by
  exact leaf_contract_factors (k := 30) (b := 20) (H := 31613) (ss := [(31, 1, 468), (8, 1, 531), (26, 1, 517), (16, 1, 531), (28, 1, 860), (14, 1, 874), (30, 1, 1209), (18, 1, 1265), (20, 1, 1314), (21, 1, 1315)]) (ids := [0, 1, 2, 3, 4, 5, 7, 8, 9, 10, 11, 13, 15, 17, 20, 21, 25, 27, 22, 23]) (cs := [2, 3, 4, 5, 6, 7, 1, 8, 9, 10, 11, 12, 1, 13, 1, 14, 1, 15, 1, 1, 16, 17, 20, 21, 1, 18, 1, 19, 1, 1]) (bs := [18, 2]) (W := 122224) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1975_2 : P.sumLeaves 24 2023232 64 = 122224 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 31613) rows (by decide) (by decide)).symm.trans contract1975_2

theorem c1975_3 : P.sumLeaves 24 2023296 128 = 6890070 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1975) (lo := 896) (len := 128) (W := 6890070) check rows elimOK (by decide) (by decide) cover1975 (by decide)
  decide +kernel

theorem h1975 : P.leaf 34 1975 = 9597562 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(768, 2484324), (64, 100944), (64, 122224), (128, 6890070)]) (.cons c1975_0 (.cons c1975_1 (.cons c1975_2 (.cons c1975_3 (.nil))))) (by decide) (by decide))

theorem cover1978 : P.CoversSplit 24 10 1978 0xffff000000000000ffff00000000000000000000000000000000000000000000ff00000000000000000000000000000000000000000000000000000000000000ffff000000000000ffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 517, 860, 872, 915, 916, 1202, 1209, 1251, 1258, 1308]) (ps := [(14, [874], [486])]) (by decide +kernel)

theorem c1978_0 : P.sumLeaves 24 2025472 704 = 400312 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1978) (lo := 0) (len := 704) (W := 400312) check rows elimOK (by decide) (by decide) cover1978 (by decide)
  decide +kernel

theorem contract1978_1 : P.leaf 30 31659 = 89792 := by
  exact leaf_contract_factors (k := 30) (b := 20) (H := 31659) (ss := [(16, 1, 468), (14, 1, 486), (15, 1, 509), (19, 1, 866), (12, 1, 867), (11, 1, 818), (31, 1, 872), (18, 1, 879), (29, 1, 916), (30, 1, 1209)]) (ids := [0, 1, 2, 3, 4, 5, 6, 7, 8, 11, 15, 18, 19, 20, 23, 24, 25, 26, 21, 22]) (cs := [2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 1, 11, 1, 1, 1, 12, 1, 1, 13, 14, 15, 20, 21, 16, 17, 18, 19, 1, 1, 1]) (bs := [18, 2]) (W := 89792) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1978_1 : P.sumLeaves 24 2026176 64 = 89792 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 31659) rows (by decide) (by decide)).symm.trans contract1978_1

theorem c1978_2 : P.sumLeaves 24 2026240 256 = 1651068 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1978) (lo := 768) (len := 256) (W := 1651068) check rows elimOK (by decide) (by decide) cover1978 (by decide)
  decide +kernel

theorem h1978 : P.leaf 34 1978 = 2141172 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(704, 400312), (64, 89792), (256, 1651068)]) (.cons c1978_0 (.cons c1978_1 (.cons c1978_2 (.nil)))) (by decide) (by decide))

theorem cover1979 : P.CoversSplit 24 10 1979 0xffff000000000000ffff000000000000a0a0000000000000a0a0000000000000ff000000000000000000000000000000a0000000000000000000000000000000ffff000000000000ffff00000000000000000000000000000000000000000000ff00000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [517, 860, 872, 915, 916, 1209, 1251, 1258, 1308]) (ps := [(14, [874], [860])]) (by decide +kernel)

theorem c1979_0 : P.sumLeaves 24 2026496 192 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1979) (lo := 0) (len := 192) (W := 0) check rows elimOK (by decide) (by decide) cover1979 (by decide)
  decide +kernel

theorem contract1979_1 : P.leaf 30 31667 = 44034 := by
  apply (leaf_contract (k := 30) (b := 18) (H := 31667) (ss := [(2, 1, 474), (3, 1, 524), (12, 1, 867), (31, 1, 872), (11, 1, 901), (29, 1, 916), (14, 1, 923), (18, 1, 923), (19, 1, 965), (15, 1, 930), (30, 1, 1209), (16, 1, 1265)]) (ids := [2, 3, 4, 5, 6, 7, 8, 11, 15, 18, 19, 20, 21, 22, 23, 24, 25, 26]) (cs := [1, 1, 2, 3, 4, 5, 6, 7, 8, 1, 1, 9, 1, 1, 1, 10, 1, 1, 11, 12, 13, 14, 15, 16, 17, 18, 19, 1, 1, 1]) check rows (by decide) (by decide +kernel) (by decide +kernel)).trans
  decide +kernel

theorem c1979_1 : P.sumLeaves 24 2026688 64 = 44034 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 31667) rows (by decide) (by decide)).symm.trans contract1979_1

theorem c1979_2 : P.sumLeaves 24 2026752 512 = 1121192 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1979) (lo := 256) (len := 512) (W := 1121192) check rows elimOK (by decide) (by decide) cover1979 (by decide)
  decide +kernel

theorem contract1979_3 : P.leaf 30 31676 = 56304 := by
  exact leaf_contract_factors (k := 30) (b := 18) (H := 31676) (ss := [(8, 1, 531), (16, 1, 531), (12, 1, 867), (31, 1, 486), (26, 1, 517), (11, 1, 818), (14, 1, 874), (28, 1, 860), (30, 1, 1209), (18, 1, 1265), (20, 1, 1314), (21, 1, 1315)]) (ids := [0, 1, 2, 3, 4, 5, 7, 8, 13, 15, 17, 20, 21, 25, 27, 11, 22, 23]) (cs := [2, 3, 4, 5, 6, 7, 1, 8, 9, 1, 1, 17, 1, 10, 1, 11, 1, 12, 1, 1, 13, 14, 18, 19, 1, 15, 1, 16, 1, 1]) (bs := [15, 3]) (W := 56304) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1979_3 : P.sumLeaves 24 2027264 64 = 56304 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 31676) rows (by decide) (by decide)).symm.trans contract1979_3

theorem contract1979_4 : P.leaf 30 31677 = 69632 := by
  exact leaf_contract_factors (k := 30) (b := 18) (H := 31677) (ss := [(8, 1, 531), (16, 1, 531), (12, 1, 867), (31, 1, 486), (26, 1, 517), (11, 1, 818), (14, 1, 874), (28, 1, 860), (30, 1, 1209), (18, 1, 1265), (20, 1, 1314), (21, 1, 1315)]) (ids := [0, 1, 2, 3, 4, 5, 7, 8, 13, 15, 17, 20, 21, 27, 11, 22, 23, 25]) (cs := [2, 3, 4, 5, 6, 7, 1, 8, 9, 1, 1, 16, 1, 10, 1, 11, 1, 12, 1, 1, 13, 14, 17, 18, 1, 19, 1, 15, 1, 1]) (bs := [14, 4]) (W := 69632) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1979_4 : P.sumLeaves 24 2027328 64 = 69632 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 31677) rows (by decide) (by decide)).symm.trans contract1979_4

theorem c1979_5 : P.sumLeaves 24 2027392 128 = 3176959 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1979) (lo := 896) (len := 128) (W := 3176959) check rows elimOK (by decide) (by decide) cover1979 (by decide)
  decide +kernel

theorem h1979 : P.leaf 34 1979 = 4468121 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(192, 0), (64, 44034), (512, 1121192), (64, 56304), (64, 69632), (128, 3176959)]) (.cons c1979_0 (.cons c1979_1 (.cons c1979_2 (.cons c1979_3 (.cons c1979_4 (.cons c1979_5 (.nil))))))) (by decide) (by decide))

theorem cover1980 : P.CoversSplit 24 10 1980 0xff00000000000000ff22000000000000a000000000000000a0000000000000000000000000000000000000000000000000000000000000000000000000000000ff00000000000000ff22000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 508, 517, 860, 867, 872, 915, 1209, 1251, 1258, 1308]) (ps := [(14, [874], [915])]) (by decide +kernel)

theorem c1980_0 : P.sumLeaves 24 2027520 1024 = 1561650 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1980) (lo := 0) (len := 1024) (W := 1561650) check rows elimOK (by decide) (by decide) cover1980 (by decide)
  decide +kernel

theorem h1980 : P.leaf 34 1980 = 1561650 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1561650)]) (.cons c1980_0 (.nil)) (by decide) (by decide))

theorem cover1981 : P.CoversSplit 24 10 1981 0xff00000000000000ff33000000000000a000000000000000a0000000000000000000000000000000000000000000000000000000000000000000000000000000ff00000000000000ff33000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 517, 860, 872, 915, 1209, 1251, 1258, 1308]) (ps := [(14, [874], [915])]) (by decide +kernel)

theorem c1981_0 : P.sumLeaves 24 2028544 1024 = 6228136 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1981) (lo := 0) (len := 1024) (W := 6228136) check rows elimOK (by decide) (by decide) cover1981 (by decide)
  decide +kernel

theorem h1981 : P.leaf 34 1981 = 6228136 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 6228136)]) (.cons c1981_0 (.nil)) (by decide) (by decide))

theorem cover1982 : P.CoversSplit 24 10 1982 0xffff000000000000ffff000000000000a0a0000000000000a0a0000000000000ffcc0000000000000000000000000000a0800000000000000000000000000000ffff000000000000ffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 517, 860, 867, 872, 915, 916, 1209, 1251, 1258, 1308]) (by decide +kernel)

theorem c1982_0 : P.sumLeaves 24 2029568 768 = 2446074 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1982) (lo := 0) (len := 768) (W := 2446074) check rows elimOK (by decide) (by decide) cover1982 (by decide)
  decide +kernel

theorem contract1982_1 : P.leaf 30 31724 = 121776 := by
  exact leaf_contract_factors (k := 30) (b := 20) (H := 31724) (ss := [(16, 1, 468), (8, 1, 531), (31, 1, 872), (26, 1, 517), (28, 1, 860), (14, 1, 874), (30, 1, 1209), (18, 1, 1265), (20, 1, 1314), (21, 1, 1315)]) (ids := [0, 1, 2, 3, 4, 5, 7, 8, 9, 10, 11, 13, 15, 17, 20, 21, 25, 27, 22, 23]) (cs := [2, 3, 4, 5, 6, 7, 1, 8, 9, 10, 11, 12, 1, 13, 1, 14, 1, 15, 1, 1, 16, 17, 20, 21, 1, 18, 1, 19, 1, 1]) (bs := [18, 2]) (W := 121776) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1982_1 : P.sumLeaves 24 2030336 64 = 121776 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 31724) rows (by decide) (by decide)).symm.trans contract1982_1

theorem contract1982_2 : P.leaf 30 31725 = 148112 := by
  exact leaf_contract_factors (k := 30) (b := 20) (H := 31725) (ss := [(16, 1, 468), (8, 1, 531), (31, 1, 872), (26, 1, 517), (28, 1, 860), (14, 1, 874), (30, 1, 1209), (18, 1, 1265), (20, 1, 1314), (21, 1, 1315)]) (ids := [0, 1, 2, 3, 4, 5, 7, 8, 9, 10, 11, 13, 15, 17, 20, 21, 25, 27, 22, 23]) (cs := [2, 3, 4, 5, 6, 7, 1, 8, 9, 10, 11, 12, 1, 13, 1, 14, 1, 15, 1, 1, 16, 17, 20, 21, 1, 18, 1, 19, 1, 1]) (bs := [18, 2]) (W := 148112) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1982_2 : P.sumLeaves 24 2030400 64 = 148112 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 31725) rows (by decide) (by decide)).symm.trans contract1982_2

theorem c1982_3 : P.sumLeaves 24 2030464 128 = 7502430 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1982) (lo := 896) (len := 128) (W := 7502430) check rows elimOK (by decide) (by decide) cover1982 (by decide)
  decide +kernel

theorem h1982 : P.leaf 34 1982 = 10218392 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(768, 2446074), (64, 121776), (64, 148112), (128, 7502430)]) (.cons c1982_0 (.cons c1982_1 (.cons c1982_2 (.cons c1982_3 (.nil))))) (by decide) (by decide))

theorem cover1983 : P.CoversSplit 24 10 1983 0xffff000000000000ffff000000000000a0a0000000000000a0a0000000000000ffcc0000000000000000000000000000a0800000000000000000000000000000ffff000000000000ffff00000000000000000000000000000000000000000000ffcc000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [517, 860, 872, 915, 916, 1209, 1251, 1258, 1308]) (by decide +kernel)

theorem c1983_0 : P.sumLeaves 24 2030592 768 = 9567740 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1983) (lo := 0) (len := 768) (W := 9567740) check rows elimOK (by decide) (by decide) cover1983 (by decide)
  decide +kernel

theorem contract1983_1 : P.leaf 30 31740 = 214064 := by
  exact leaf_contract_factors (k := 30) (b := 20) (H := 31740) (ss := [(8, 1, 531), (16, 1, 531), (31, 1, 872), (26, 1, 517), (28, 1, 860), (14, 1, 874), (30, 1, 1209), (18, 1, 1265), (20, 1, 1314), (21, 1, 1315)]) (ids := [0, 1, 2, 3, 4, 5, 7, 8, 9, 10, 11, 13, 15, 17, 20, 21, 25, 27, 22, 23]) (cs := [2, 3, 4, 5, 6, 7, 1, 8, 9, 10, 11, 12, 1, 13, 1, 14, 1, 15, 1, 1, 16, 17, 20, 21, 1, 18, 1, 19, 1, 1]) (bs := [18, 2]) (W := 214064) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1983_1 : P.sumLeaves 24 2031360 64 = 214064 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 31740) rows (by decide) (by decide)).symm.trans contract1983_1

theorem contract1983_2 : P.leaf 30 31741 = 249072 := by
  exact leaf_contract_factors (k := 30) (b := 20) (H := 31741) (ss := [(8, 1, 531), (16, 1, 531), (31, 1, 872), (26, 1, 517), (28, 1, 860), (14, 1, 874), (30, 1, 1209), (18, 1, 1265), (20, 1, 1314), (21, 1, 1315)]) (ids := [0, 1, 2, 3, 4, 5, 7, 8, 9, 10, 11, 13, 15, 17, 20, 21, 25, 27, 22, 23]) (cs := [2, 3, 4, 5, 6, 7, 1, 8, 9, 10, 11, 12, 1, 13, 1, 14, 1, 15, 1, 1, 16, 17, 20, 21, 1, 18, 1, 19, 1, 1]) (bs := [18, 2]) (W := 249072) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1983_2 : P.sumLeaves 24 2031424 64 = 249072 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 31741) rows (by decide) (by decide)).symm.trans contract1983_2

theorem c1983_3 : P.sumLeaves 24 2031488 128 = 18735296 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1983) (lo := 896) (len := 128) (W := 18735296) check rows elimOK (by decide) (by decide) cover1983 (by decide)
  decide +kernel

theorem h1983 : P.leaf 34 1983 = 28766172 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(768, 9567740), (64, 214064), (64, 249072), (128, 18735296)]) (.cons c1983_0 (.cons c1983_1 (.cons c1983_2 (.cons c1983_3 (.nil))))) (by decide) (by decide))

theorem cover1988 : P.CoversSplit 24 10 1988 0x8000000000000000000000000000000080000000000000000000000000000000000000000000000000200000000000000000000000000000002000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 508, 515, 516, 522, 566, 860, 872, 915, 916, 1202, 1209, 1259, 1308]) (by decide +kernel)

theorem c1988_0 : P.sumLeaves 24 2035712 1024 = 34536 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1988) (lo := 0) (len := 1024) (W := 34536) check rows elimOK (by decide) (by decide) cover1988 (by decide)
  decide +kernel

theorem h1988 : P.leaf 34 1988 = 34536 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 34536)]) (.cons c1988_0 (.nil)) (by decide) (by decide))

theorem cover1989 : P.CoversSplit 24 10 1989 0xcc000000000000000000000000000000cc0000000000000000000000000000000000000000000000003300000000000000000000000000000033000000000000cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 515, 522, 566, 860, 872, 915, 916, 1209, 1251, 1308, 1609]) (by decide +kernel)

theorem c1989_0 : P.sumLeaves 24 2036736 448 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1989) (lo := 0) (len := 448) (W := 0) check rows elimOK (by decide) (by decide) cover1989 (by decide)
  decide +kernel

theorem contract1989_1 : P.leaf 30 31831 = 45756 := by
  exact leaf_contract_factors (k := 30) (b := 17) (H := 31831) (ss := [(27, 1, 473), (29, 1, 473), (2, 1, 475), (3, 1, 523), (12, 1, 867), (31, 1, 872), (11, 1, 901), (14, 1, 929), (19, 1, 929), (18, 1, 965), (13, 1, 922), (30, 1, 1209), (17, 1, 1273)]) (ids := [2, 3, 4, 5, 6, 7, 8, 13, 14, 18, 19, 20, 21, 22, 24, 26, 23]) (cs := [1, 1, 2, 3, 4, 5, 6, 7, 8, 1, 1, 1, 1, 9, 10, 1, 1, 1, 11, 12, 13, 14, 15, 18, 16, 1, 17, 1, 1, 1]) (bs := [16, 1]) (W := 45756) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1989_1 : P.sumLeaves 24 2037184 64 = 45756 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 31831) rows (by decide) (by decide)).symm.trans contract1989_1

theorem c1989_2 : P.sumLeaves 24 2037248 512 = 708078 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1989) (lo := 512) (len := 512) (W := 708078) check rows elimOK (by decide) (by decide) cover1989 (by decide)
  decide +kernel

theorem h1989 : P.leaf 34 1989 = 753834 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(448, 0), (64, 45756), (512, 708078)]) (.cons c1989_0 (.cons c1989_1 (.cons c1989_2 (.nil)))) (by decide) (by decide))

theorem cover1990 : P.CoversSplit 24 10 1990 0xa0a00000000000000000000000000000a0a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000a0a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 515, 516, 522, 566, 860, 872, 915, 916, 1202, 1209, 1210, 1258, 1259, 1308]) (ps := [(17, [1308], [1259])]) (by decide +kernel)

theorem c1990_0 : P.sumLeaves 24 2037760 448 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1990) (lo := 0) (len := 448) (W := 0) check rows elimOK (by decide) (by decide) cover1990 (by decide)
  decide +kernel

theorem contract1990_1 : P.leaf 30 31847 = 52028 := by
  exact leaf_contract_factors (k := 30) (b := 19) (H := 31847) (ss := [(3, 1, 523), (12, 1, 867), (14, 1, 929), (19, 1, 929), (18, 1, 965), (30, 1, 1251), (26, 1, 465), (28, 1, 465), (2, 1, 409), (31, 1, 1209), (17, 1, 1273)]) (ids := [2, 3, 4, 5, 6, 7, 8, 9, 11, 13, 14, 18, 19, 20, 21, 23, 25, 27, 22]) (cs := [1, 1, 2, 3, 4, 5, 6, 7, 8, 9, 1, 10, 1, 11, 12, 1, 1, 1, 13, 14, 15, 16, 20, 17, 1, 18, 1, 19, 1, 1]) (bs := [18, 1]) (W := 52028) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1990_1 : P.sumLeaves 24 2038208 64 = 52028 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 31847) rows (by decide) (by decide)).symm.trans contract1990_1

theorem c1990_2 : P.sumLeaves 24 2038272 512 = 340616 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1990) (lo := 512) (len := 512) (W := 340616) check rows elimOK (by decide) (by decide) cover1990 (by decide)
  decide +kernel

theorem h1990 : P.leaf 34 1990 = 392644 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(448, 0), (64, 52028), (512, 340616)]) (.cons c1990_0 (.cons c1990_1 (.cons c1990_2 (.nil)))) (by decide) (by decide))

theorem cover1991 : P.CoversSplit 24 10 1991 0xffff0000000000000000000000000000ffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [515, 522, 566, 860, 915, 916, 1202, 1209, 1251, 1258, 1259, 1308]) (ps := [(17, [1308], [1259])]) (by decide +kernel)

theorem c1991_0 : P.sumLeaves 24 2038784 1024 = 4259570 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1991) (lo := 0) (len := 1024) (W := 4259570) check rows elimOK (by decide) (by decide) cover1991 (by decide)
  decide +kernel

theorem h1991 : P.leaf 34 1991 = 4259570 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 4259570)]) (.cons c1991_0 (.nil)) (by decide) (by decide))

theorem cover1996 : P.CoversSplit 24 10 1996 0x8000000000000000000000000000000080000000000000000000000000000000000000000000000000200000000000000000000000000000002000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 508, 515, 516, 522, 860, 872, 915, 1202, 1209, 1259, 1308]) (by decide +kernel)

theorem c1996_0 : P.sumLeaves 24 2043904 1024 = 138568 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1996) (lo := 0) (len := 1024) (W := 138568) check rows elimOK (by decide) (by decide) cover1996 (by decide)
  decide +kernel

theorem h1996 : P.leaf 34 1996 = 138568 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 138568)]) (.cons c1996_0 (.nil)) (by decide) (by decide))

theorem cover1997 : P.CoversSplit 24 10 1997 0xcc000000000000000000000000000000cc0000000000000000000000000000000000000000000000003300000000000000000000000000000033000000000000cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 515, 522, 860, 872, 915, 1209, 1251, 1308, 1609]) (by decide +kernel)

theorem c1997_0 : P.sumLeaves 24 2044928 1024 = 1807756 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1997) (lo := 0) (len := 1024) (W := 1807756) check rows elimOK (by decide) (by decide) cover1997 (by decide)
  decide +kernel

theorem h1997 : P.leaf 34 1997 = 1807756 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1807756)]) (.cons c1997_0 (.nil)) (by decide) (by decide))

theorem cover1998 : P.CoversSplit 24 10 1998 0xa0a00000000000000000000000000000a0a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000a0a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 515, 516, 522, 860, 872, 916, 1202, 1209, 1210, 1258, 1259, 1308]) (ps := [(17, [1308], [1259])]) (by decide +kernel)

theorem c1998_0 : P.sumLeaves 24 2045952 1024 = 1340356 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1998) (lo := 0) (len := 1024) (W := 1340356) check rows elimOK (by decide) (by decide) cover1998 (by decide)
  decide +kernel

theorem h1998 : P.leaf 34 1998 = 1340356 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1340356)]) (.cons c1998_0 (.nil)) (by decide) (by decide))

theorem cover1999 : P.CoversSplit 24 10 1999 0xffff0000000000000000000000000000ffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [515, 522, 860, 916, 1202, 1209, 1251, 1258, 1259, 1308]) (ps := [(17, [1308], [1259])]) (by decide +kernel)

theorem c1999_0 : P.sumLeaves 24 2046976 1024 = 8962256 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1999) (lo := 0) (len := 1024) (W := 8962256) check rows elimOK (by decide) (by decide) cover1999 (by decide)
  decide +kernel

theorem h1999 : P.leaf 34 1999 = 8962256 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 8962256)]) (.cons c1999_0 (.nil)) (by decide) (by decide))

theorem cover2006 : P.CoversSplit 24 10 2006 0xffffffffa0a0a0a0ffffffffa0a0a0a0a0a0a5a500000000a0a0a5a500000000ffccffcc80008000cc00cc0080008000a080a584000000008000840000000000ffffffffa0a0a0a0ffffffffa0a0a0a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 516, 860, 867, 915, 916, 1202, 1258, 1259, 1308]) (by decide +kernel)

theorem c2006_0 : P.sumLeaves 24 2054144 686 = 1143010 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 2006) (lo := 0) (len := 686) (W := 1143010) check rows elimOK (by decide) (by decide) cover2006 (by decide)
  decide +kernel

theorem c2006_1 : P.sumLeaves 24 2054830 279 = 3361152 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 2006) (lo := 686) (len := 279) (W := 3361152) check rows elimOK (by decide) (by decide) cover2006 (by decide)
  decide +kernel

theorem c2006_2 : P.sumLeaves 24 2055109 59 = 3745114 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 2006) (lo := 965) (len := 59) (W := 3745114) check rows elimOK (by decide) (by decide) cover2006 (by decide)
  decide +kernel

theorem h2006 : P.leaf 34 2006 = 8249276 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(686, 1143010), (279, 3361152), (59, 3745114)]) (.cons c2006_0 (.cons c2006_1 (.cons c2006_2 (.nil)))) (by decide) (by decide))

theorem cover2007 : P.CoversSplit 24 10 2007 0xffffffffa0a0a0a0ffffffffa0a0a0a0ffffffff0000a0a0ffffffff0000a0a0ffccffcc80008000cc00cc0080008000ffccffcc00008000cc00cc0000008000ffffffffa0a0a0a0ffffffffa0a0a0a000000000000000000000000000000000ffccffcc80008000cc00cc008000800000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [516, 860, 915, 916, 1202, 1217, 1258, 1259, 1308]) (by decide +kernel)

theorem c2007_0 : P.sumLeaves 24 2055168 492 = 2376521 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 2007) (lo := 0) (len := 492) (W := 2376521) check rows elimOK (by decide) (by decide) cover2007 (by decide)
  decide +kernel

theorem c2007_1 : P.sumLeaves 24 2055660 310 = 8390970 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 2007) (lo := 492) (len := 310) (W := 8390970) check rows elimOK (by decide) (by decide) cover2007 (by decide)
  decide +kernel

theorem c2007_2 : P.sumLeaves 24 2055970 148 = 6981801 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 2007) (lo := 802) (len := 148) (W := 6981801) check rows elimOK (by decide) (by decide) cover2007 (by decide)
  decide +kernel

theorem c2007_3 : P.sumLeaves 24 2056118 74 = 15218660 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 2007) (lo := 950) (len := 74) (W := 15218660) check rows elimOK (by decide) (by decide) cover2007 (by decide)
  decide +kernel

theorem h2007 : P.leaf 34 2007 = 32967952 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(492, 2376521), (310, 8390970), (148, 6981801), (74, 15218660)]) (.cons c2007_0 (.cons c2007_1 (.cons c2007_2 (.cons c2007_3 (.nil))))) (by decide) (by decide))

theorem cover2012 : P.CoversSplit 24 10 2012 0xff00ff0000000000ff22ff2200000000a000a50000000000a000a500000000000000000000000000000000000000000000000000000000000000000000000000ff00ff0000000000ff22ff2200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 508, 516, 860, 867, 872, 915, 1258, 1308]) (ps := [(14, [923], [915])]) (by decide +kernel)

theorem c2012_0 : P.sumLeaves 24 2060288 1024 = 2345194 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 2012) (lo := 0) (len := 1024) (W := 2345194) check rows elimOK (by decide) (by decide) cover2012 (by decide)
  decide +kernel

theorem h2012 : P.leaf 34 2012 = 2345194 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 2345194)]) (.cons c2012_0 (.nil)) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(1967, 48), (1972, 48), (1973, 48), (1974, 48), (1975, 48), (1978, 24), (1979, 24), (1980, 48), (1981, 48), (1982, 48), (1983, 48), (1988, 24), (1989, 24), (1990, 48), (1991, 48), (1996, 48), (1997, 48), (1998, 48), (1999, 48), (2006, 24), (2007, 24), (2012, 48)]

theorem segOK : checkSeg 16 perms 1967 2013 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 1967 2013 912 5355306696 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 5355306696)
    (SegSum.cons (w := 48) h1967 (SegSum.cons (w := 48) h1972 (SegSum.cons (w := 48) h1973 (SegSum.cons (w := 48) h1974 (SegSum.cons (w := 48) h1975 (SegSum.cons (w := 24) h1978 (SegSum.cons (w := 24) h1979 (SegSum.cons (w := 48) h1980 (SegSum.cons (w := 48) h1981 (SegSum.cons (w := 48) h1982 (SegSum.cons (w := 48) h1983 (SegSum.cons (w := 24) h1988 (SegSum.cons (w := 24) h1989 (SegSum.cons (w := 48) h1990 (SegSum.cons (w := 48) h1991 (SegSum.cons (w := 48) h1996 (SegSum.cons (w := 48) h1997 (SegSum.cons (w := 48) h1998 (SegSum.cons (w := 48) h1999 (SegSum.cons (w := 24) h2006 (SegSum.cons (w := 24) h2007 (SegSum.cons (w := 48) h2012 (show SegSum (P.leaf 34) [] 0 from rfl))))))))))))))))))))))) (by decide)

end RACert.S4N1.C0.S16
