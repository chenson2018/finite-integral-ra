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

namespace RACert.S4N1.C0.S33

open RACert RACert.Problem

theorem cover5852 : P.CoversSplit 24 10 5852 0xfcfcfcfca0a000000000000000000000a0a0a4a40000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 508, 516, 536, 573, 860, 916, 1202, 1210, 1258, 1259, 1264, 1308]) (by decide +kernel)

theorem c5852_0 : P.sumLeaves 24 5992448 1024 = 2737202 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5852) (lo := 0) (len := 1024) (W := 2737202) check rows elimOK (by decide) (by decide) cover5852 (by decide)
  decide +kernel

theorem h5852 : P.leaf 34 5852 = 2737202 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 2737202)]) (.cons c5852_0 (.nil)) (by decide) (by decide))

theorem cover5853 : P.CoversSplit 24 10 5853 0xffffffffa0a000000000000000000000ffffffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 516, 536, 573, 860, 867, 916, 1202, 1210, 1258, 1259, 1264, 1308]) (by decide +kernel)

theorem c5853_0 : P.sumLeaves 24 5993472 1024 = 7928344 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5853) (lo := 0) (len := 1024) (W := 7928344) check rows elimOK (by decide) (by decide) cover5853 (by decide)
  decide +kernel

theorem h5853 : P.leaf 34 5853 = 7928344 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 7928344)]) (.cons c5853_0 (.nil)) (by decide) (by decide))

theorem cover5854 : P.CoversSplit 24 10 5854 0xffffffffa0a000000000000000000000a0a0a5a50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 516, 536, 573, 860, 916, 1202, 1210, 1258, 1259, 1264, 1308]) (by decide +kernel)

theorem c5854_0 : P.sumLeaves 24 5994496 1024 = 6552175 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5854) (lo := 0) (len := 1024) (W := 6552175) check rows elimOK (by decide) (by decide) cover5854 (by decide)
  decide +kernel

theorem h5854 : P.leaf 34 5854 = 6552175 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 6552175)]) (.cons c5854_0 (.nil)) (by decide) (by decide))

theorem cover5855 : P.CoversSplit 24 10 5855 0xffffffffa0a000000000000000000000ffffffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [516, 536, 573, 860, 916, 1202, 1210, 1217, 1258, 1259, 1264, 1308]) (by decide +kernel)

theorem c5855_0 : P.sumLeaves 24 5995520 1024 = 18599145 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5855) (lo := 0) (len := 1024) (W := 18599145) check rows elimOK (by decide) (by decide) cover5855 (by decide)
  decide +kernel

theorem h5855 : P.leaf 34 5855 = 18599145 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 18599145)]) (.cons c5855_0 (.nil)) (by decide) (by decide))

theorem cover5858 : P.CoversSplit 24 10 5858 0xaaaa0000000000000000000000000000a0a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000088000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 475, 515, 523, 524, 565, 566, 573, 860, 1209, 1259, 1264, 1308]) (ps := [(14, [874, 923], [860, 916])]) (by decide +kernel)

theorem c5858_0 : P.sumLeaves 24 5998592 832 = 4480 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5858) (lo := 0) (len := 832) (W := 4480) check rows elimOK (by decide) (by decide) cover5858 (by decide)
  decide +kernel

theorem contract5858_1 : P.leaf 30 93741 = 7488 := by
  exact leaf_contract_factors (k := 30) (b := 16) (H := 93741) (ss := [(2, 1, 453), (5, 1, 453), (3, 1, 409), (6, 1, 478), (12, 1, 460), (30, 1, 524), (4, 1, 566), (14, 1, 874), (16, 1, 874), (31, 1, 1209), (26, 1, 515), (28, 1, 860), (18, 1, 1265), (17, 1, 1266)]) (ids := [5, 6, 7, 8, 9, 11, 13, 17, 18, 19, 21, 23, 25, 27, 20, 22]) (cs := [1, 1, 1, 1, 1, 2, 3, 4, 5, 6, 1, 7, 1, 8, 1, 1, 1, 9, 10, 11, 16, 12, 17, 13, 1, 14, 1, 15, 1, 1]) (bs := [14, 2]) (W := 7488) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c5858_1 : P.sumLeaves 24 5999424 64 = 7488 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 93741) rows (by decide) (by decide)).symm.trans contract5858_1

theorem c5858_2 : P.sumLeaves 24 5999488 128 = 55424 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5858) (lo := 896) (len := 128) (W := 55424) check rows elimOK (by decide) (by decide) cover5858 (by decide)
  decide +kernel

theorem h5858 : P.leaf 34 5858 = 67392 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(832, 4480), (64, 7488), (128, 55424)]) (.cons c5858_0 (.cons c5858_1 (.cons c5858_2 (.nil)))) (by decide) (by decide))

theorem cover5859 : P.CoversSplit 24 10 5859 0xffff0000000000000000000000000000ffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [475, 515, 523, 524, 566, 573, 860, 1202, 1209, 1251, 1259, 1264, 1308]) (ps := [(14, [923], [916])]) (by decide +kernel)

theorem c5859_0 : P.sumLeaves 24 5999616 448 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5859) (lo := 0) (len := 448) (W := 0) check rows elimOK (by decide) (by decide) cover5859 (by decide)
  decide +kernel

theorem contract5859_1 : P.leaf 30 93751 = 43200 := by
  exact leaf_contract_factors (k := 30) (b := 18) (H := 93751) (ss := [(6, 1, 478), (12, 1, 478), (30, 18, 524), (18, 1, 536), (27, 1, 573), (14, 1, 923), (8, 1, 580), (29, 1, 916), (31, 1, 1209), (16, 1, 1265), (20, 1, 1657), (21, 1, 1658)]) (ids := [0, 1, 2, 3, 5, 7, 8, 9, 13, 15, 17, 20, 21, 26, 11, 22, 23, 24]) (cs := [2, 3, 4, 5, 1, 6, 1, 7, 8, 9, 1, 16, 1, 10, 1, 11, 1, 12, 1, 1, 13, 14, 17, 18, 19, 1, 15, 1, 1, 1]) (bs := [14, 4]) (W := 43200) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c5859_1 : P.sumLeaves 24 6000064 64 = 43200 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 93751) rows (by decide) (by decide)).symm.trans contract5859_1

theorem c5859_2 : P.sumLeaves 24 6000128 512 = 1076352 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5859) (lo := 512) (len := 512) (W := 1076352) check rows elimOK (by decide) (by decide) cover5859 (by decide)
  decide +kernel

theorem h5859 : P.leaf 34 5859 = 1119552 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(448, 0), (64, 43200), (512, 1076352)]) (.cons c5859_0 (.cons c5859_1 (.cons c5859_2 (.nil)))) (by decide) (by decide))

theorem cover5860 : P.CoversSplit 24 10 5860 0x8888000000000000000000000000000080800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 475, 508, 515, 522, 524, 860, 1209, 1259]) (by decide +kernel)

theorem c5860_0 : P.sumLeaves 24 6000640 1024 = 81008 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5860) (lo := 0) (len := 1024) (W := 81008) check rows elimOK (by decide) (by decide) cover5860 (by decide)
  decide +kernel

theorem h5860 : P.leaf 34 5860 = 81008 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 81008)]) (.cons c5860_0 (.nil)) (by decide) (by decide))

theorem cover5861 : P.CoversSplit 24 10 5861 0xcccc0000000000000000000000000000cccc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 475, 515, 522, 524, 860, 916, 1202, 1209, 1259]) (by decide +kernel)

theorem c5861_0 : P.sumLeaves 24 6001664 1024 = 1515672 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5861) (lo := 0) (len := 1024) (W := 1515672) check rows elimOK (by decide) (by decide) cover5861 (by decide)
  decide +kernel

theorem h5861 : P.leaf 34 5861 = 1515672 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1515672)]) (.cons c5861_0 (.nil)) (by decide) (by decide))

theorem cover5862 : P.CoversSplit 24 10 5862 0xaaaa0000000000000000000000000000a0a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000088000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 475, 515, 522, 524, 566, 573, 860, 916, 1209, 1259, 1264, 1308]) (by decide +kernel)

theorem c5862_0 : P.sumLeaves 24 6002688 1024 = 869700 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5862) (lo := 0) (len := 1024) (W := 869700) check rows elimOK (by decide) (by decide) cover5862 (by decide)
  decide +kernel

theorem h5862 : P.leaf 34 5862 = 869700 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 869700)]) (.cons c5862_0 (.nil)) (by decide) (by decide))

theorem cover5863 : P.CoversSplit 24 10 5863 0xffff0000000000000000000000000000ffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [475, 515, 522, 524, 566, 573, 860, 916, 1202, 1209, 1251, 1259, 1264, 1308]) (by decide +kernel)

theorem c5863_0 : P.sumLeaves 24 6003712 448 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5863) (lo := 0) (len := 448) (W := 0) check rows elimOK (by decide) (by decide) cover5863 (by decide)
  decide +kernel

theorem contract5863_1 : P.leaf 30 93815 = 123584 := by
  exact leaf_contract_factors (k := 30) (b := 19) (H := 93815) (ss := [(30, 18, 524), (18, 1, 536), (27, 1, 573), (12, 1, 867), (29, 1, 916), (14, 1, 923), (8, 1, 580), (31, 1, 1209), (16, 1, 1265), (20, 1, 1657), (21, 1, 1658)]) (ids := [0, 1, 2, 3, 4, 7, 8, 9, 13, 15, 17, 20, 21, 26, 5, 11, 22, 23, 24]) (cs := [2, 3, 4, 5, 6, 16, 1, 7, 8, 9, 1, 17, 1, 10, 1, 11, 1, 12, 1, 1, 13, 14, 18, 19, 20, 1, 15, 1, 1, 1]) (bs := [14, 5]) (W := 123584) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c5863_1 : P.sumLeaves 24 6004160 64 = 123584 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 93815) rows (by decide) (by decide)).symm.trans contract5863_1

theorem c5863_2 : P.sumLeaves 24 6004224 512 = 5587360 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5863) (lo := 512) (len := 512) (W := 5587360) check rows elimOK (by decide) (by decide) cover5863 (by decide)
  decide +kernel

theorem h5863 : P.leaf 34 5863 = 5710944 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(448, 0), (64, 123584), (512, 5587360)]) (.cons c5863_0 (.cons c5863_1 (.cons c5863_2 (.nil)))) (by decide) (by decide))

theorem cover5864 : P.CoversSplit 24 10 5864 0x8888000000000000000000000000000080800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 508, 515, 522, 523, 573, 860, 916, 1202, 1209, 1259, 1308]) (ps := [(14, [487, 923], [487, 860])]) (by decide +kernel)

theorem c5864_0 : P.sumLeaves 24 6004736 1024 = 64812 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5864) (lo := 0) (len := 1024) (W := 64812) check rows elimOK (by decide) (by decide) cover5864 (by decide)
  decide +kernel

theorem h5864 : P.leaf 34 5864 = 64812 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 64812)]) (.cons c5864_0 (.nil)) (by decide) (by decide))

theorem cover5865 : P.CoversSplit 24 10 5865 0xcccc0000000000000000000000000000cccc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 515, 522, 523, 573, 860, 916, 1202, 1209, 1251, 1259, 1308]) (ps := [(14, [923], [487])]) (by decide +kernel)

theorem c5865_0 : P.sumLeaves 24 6005760 1024 = 470944 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5865) (lo := 0) (len := 1024) (W := 470944) check rows elimOK (by decide) (by decide) cover5865 (by decide)
  decide +kernel

theorem h5865 : P.leaf 34 5865 = 470944 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 470944)]) (.cons c5865_0 (.nil)) (by decide) (by decide))

theorem cover5866 : P.CoversSplit 24 10 5866 0xaaaa0000000000000000000000000000a0a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000088000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 515, 522, 523, 565, 573, 860, 916, 1209, 1259, 1264, 1308]) (ps := [(14, [874, 923], [860, 916])]) (by decide +kernel)

theorem c5866_0 : P.sumLeaves 24 6006784 832 = 34320 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5866) (lo := 0) (len := 832) (W := 34320) check rows elimOK (by decide) (by decide) cover5866 (by decide)
  decide +kernel

theorem contract5866_1 : P.leaf 30 93869 = 46724 := by
  exact leaf_contract_factors (k := 30) (b := 19) (H := 93869) (ss := [(4, 1, 566), (12, 1, 867), (14, 1, 874), (2, 1, 486), (16, 1, 874), (30, 1, 1251), (31, 1, 1209), (26, 1, 515), (28, 1, 860), (18, 1, 1265), (17, 1, 1266)]) (ids := [1, 3, 4, 5, 6, 7, 8, 9, 11, 13, 17, 18, 19, 20, 21, 23, 25, 27, 22]) (cs := [1, 2, 1, 3, 4, 5, 6, 7, 8, 9, 1, 10, 1, 11, 1, 1, 1, 12, 13, 14, 15, 16, 20, 17, 1, 18, 1, 19, 1, 1]) (bs := [18, 1]) (W := 46724) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c5866_1 : P.sumLeaves 24 6007616 64 = 46724 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 93869) rows (by decide) (by decide)).symm.trans contract5866_1

theorem c5866_2 : P.sumLeaves 24 6007680 128 = 538352 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5866) (lo := 896) (len := 128) (W := 538352) check rows elimOK (by decide) (by decide) cover5866 (by decide)
  decide +kernel

theorem h5866 : P.leaf 34 5866 = 619396 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(832, 34320), (64, 46724), (128, 538352)]) (.cons c5866_0 (.cons c5866_1 (.cons c5866_2 (.nil)))) (by decide) (by decide))

theorem cover5867 : P.CoversSplit 24 10 5867 0xffff0000000000000000000000000000ffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [515, 522, 523, 573, 860, 916, 1202, 1209, 1251, 1258, 1259, 1264, 1308]) (ps := [(14, [923], [916])]) (by decide +kernel)

theorem c5867_0 : P.sumLeaves 24 6007808 448 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5867) (lo := 0) (len := 448) (W := 0) check rows elimOK (by decide) (by decide) cover5867 (by decide)
  decide +kernel

theorem contract5867_1 : P.leaf 30 93879 = 117248 := by
  exact leaf_contract_factors (k := 30) (b := 19) (H := 93879) (ss := [(18, 1, 524), (27, 1, 573), (12, 1, 867), (14, 1, 923), (8, 1, 580), (29, 1, 916), (30, 1, 1251), (31, 1, 1209), (16, 1, 1265), (20, 1, 1657), (21, 1, 1658)]) (ids := [0, 1, 2, 3, 4, 5, 7, 8, 9, 13, 15, 17, 20, 21, 26, 11, 22, 23, 24]) (cs := [2, 3, 4, 5, 6, 7, 1, 8, 9, 10, 1, 17, 1, 11, 1, 12, 1, 13, 1, 1, 14, 15, 18, 19, 20, 1, 16, 1, 1, 1]) (bs := [15, 4]) (W := 117248) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c5867_1 : P.sumLeaves 24 6008256 64 = 117248 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 93879) rows (by decide) (by decide)).symm.trans contract5867_1

theorem c5867_2 : P.sumLeaves 24 6008320 512 = 2406680 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5867) (lo := 512) (len := 512) (W := 2406680) check rows elimOK (by decide) (by decide) cover5867 (by decide)
  decide +kernel

theorem h5867 : P.leaf 34 5867 = 2523928 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(448, 0), (64, 117248), (512, 2406680)]) (.cons c5867_0 (.cons c5867_1 (.cons c5867_2 (.nil)))) (by decide) (by decide))

theorem cover5868 : P.CoversSplit 24 10 5868 0x8888000000000000000000000000000080800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000088000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 508, 515, 522, 573, 860, 916, 1202, 1209, 1259, 1308]) (by decide +kernel)

theorem c5868_0 : P.sumLeaves 24 6008832 1024 = 312332 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5868) (lo := 0) (len := 1024) (W := 312332) check rows elimOK (by decide) (by decide) cover5868 (by decide)
  decide +kernel

theorem h5868 : P.leaf 34 5868 = 312332 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 312332)]) (.cons c5868_0 (.nil)) (by decide) (by decide))

theorem cover5869 : P.CoversSplit 24 10 5869 0xcccc0000000000000000000000000000cccc00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 515, 522, 573, 860, 916, 1202, 1209, 1251, 1259, 1308]) (by decide +kernel)

theorem c5869_0 : P.sumLeaves 24 6009856 448 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5869) (lo := 0) (len := 448) (W := 0) check rows elimOK (by decide) (by decide) cover5869 (by decide)
  decide +kernel

theorem contract5869_1 : P.leaf 30 93911 = 96704 := by
  exact leaf_contract_factors (k := 30) (b := 19) (H := 93911) (ss := [(18, 1, 475), (27, 1, 522), (12, 1, 867), (29, 1, 916), (14, 1, 923), (30, 1, 1251), (31, 1, 1209), (16, 1, 1265), (20, 1, 1657), (21, 1, 1658), (8, 1, 580)]) (ids := [0, 1, 2, 3, 4, 7, 8, 9, 13, 15, 17, 20, 21, 26, 5, 11, 22, 23, 24]) (cs := [2, 3, 4, 5, 6, 16, 1, 7, 8, 9, 1, 17, 1, 10, 1, 11, 1, 12, 1, 1, 13, 14, 18, 19, 20, 1, 15, 1, 1, 1]) (bs := [14, 5]) (W := 96704) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c5869_1 : P.sumLeaves 24 6010304 64 = 96704 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 93911) rows (by decide) (by decide)).symm.trans contract5869_1

theorem c5869_2 : P.sumLeaves 24 6010368 512 = 2264792 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5869) (lo := 512) (len := 512) (W := 2264792) check rows elimOK (by decide) (by decide) cover5869 (by decide)
  decide +kernel

theorem h5869 : P.leaf 34 5869 = 2361496 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(448, 0), (64, 96704), (512, 2264792)]) (.cons c5869_0 (.cons c5869_1 (.cons c5869_2 (.nil)))) (by decide) (by decide))

theorem cover5870 : P.CoversSplit 24 10 5870 0xaaaa0000000000000000000000000000a0a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000088000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 515, 522, 573, 860, 916, 1209, 1259, 1264, 1308]) (by decide +kernel)

theorem c5870_0 : P.sumLeaves 24 6010880 1024 = 2334430 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5870) (lo := 0) (len := 1024) (W := 2334430) check rows elimOK (by decide) (by decide) cover5870 (by decide)
  decide +kernel

theorem h5870 : P.leaf 34 5870 = 2334430 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 2334430)]) (.cons c5870_0 (.nil)) (by decide) (by decide))

theorem cover5871 : P.CoversSplit 24 10 5871 0xffff0000000000000000000000000000ffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 522, 573, 860, 916, 1202, 1209, 1251, 1258, 1259, 1264, 1308]) (by decide +kernel)

theorem c5871_0 : P.sumLeaves 24 6011904 448 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5871) (lo := 0) (len := 448) (W := 0) check rows elimOK (by decide) (by decide) cover5871 (by decide)
  decide +kernel

theorem contract5871_1 : P.leaf 30 93943 = 195136 := by
  exact leaf_contract_factors (k := 30) (b := 19) (H := 93943) (ss := [(18, 1, 524), (27, 1, 573), (12, 1, 867), (29, 1, 916), (14, 1, 923), (8, 1, 580), (30, 1, 1251), (31, 1, 1209), (16, 1, 1265), (20, 1, 1657), (21, 1, 1658)]) (ids := [0, 1, 2, 3, 4, 7, 8, 9, 13, 15, 17, 20, 21, 26, 5, 11, 22, 23, 24]) (cs := [2, 3, 4, 5, 6, 16, 1, 7, 8, 9, 1, 17, 1, 10, 1, 11, 1, 12, 1, 1, 13, 14, 18, 19, 20, 1, 15, 1, 1, 1]) (bs := [14, 5]) (W := 195136) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c5871_1 : P.sumLeaves 24 6012352 64 = 195136 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 93943) rows (by decide) (by decide)).symm.trans contract5871_1

theorem c5871_2 : P.sumLeaves 24 6012416 512 = 8802712 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5871) (lo := 512) (len := 512) (W := 8802712) check rows elimOK (by decide) (by decide) cover5871 (by decide)
  decide +kernel

theorem h5871 : P.leaf 34 5871 = 8997848 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(448, 0), (64, 195136), (512, 8802712)]) (.cons c5871_0 (.cons c5871_1 (.cons c5871_2 (.nil)))) (by decide) (by decide))

theorem cover5875 : P.CoversSplit 24 10 5875 0xffffffffa0a000000000000000000000ffffffffa0a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [475, 573, 860, 1202, 1210, 1259, 1264, 1308]) (ps := [(14, [923], [916])]) (by decide +kernel)

theorem c5875_0 : P.sumLeaves 24 6016000 448 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5875) (lo := 0) (len := 448) (W := 0) check rows elimOK (by decide) (by decide) cover5875 (by decide)
  decide +kernel

theorem contract5875_1 : P.leaf 30 94007 = 119840 := by
  exact leaf_contract_factors (k := 30) (b := 20) (H := 94007) (ss := [(6, 1, 478), (12, 1, 478), (27, 1, 573), (8, 1, 580), (18, 1, 580), (14, 1, 923), (29, 1, 916), (16, 1, 1265), (20, 1, 1657), (21, 1, 1658)]) (ids := [0, 1, 2, 3, 5, 7, 8, 9, 13, 15, 17, 20, 22, 24, 26, 28, 29, 11, 21, 23]) (cs := [2, 3, 4, 5, 1, 6, 1, 7, 8, 9, 1, 19, 1, 10, 1, 11, 1, 12, 1, 1, 13, 20, 14, 21, 15, 1, 16, 1, 17, 18]) (bs := [17, 3]) (W := 119840) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c5875_1 : P.sumLeaves 24 6016448 64 = 119840 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 94007) rows (by decide) (by decide)).symm.trans contract5875_1

theorem c5875_2 : P.sumLeaves 24 6016512 512 = 3483232 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5875) (lo := 512) (len := 512) (W := 3483232) check rows elimOK (by decide) (by decide) cover5875 (by decide)
  decide +kernel

theorem h5875 : P.leaf 34 5875 = 3603072 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(448, 0), (64, 119840), (512, 3483232)]) (.cons c5875_0 (.cons c5875_1 (.cons c5875_2 (.nil)))) (by decide) (by decide))

theorem cover5876 : P.CoversSplit 24 10 5876 0xfcfcfcfca8a800000000000000000000f4f4f4f4000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 475, 508, 573, 860, 909, 1202, 1210, 1259, 1264]) (by decide +kernel)

theorem c5876_0 : P.sumLeaves 24 6017024 1024 = 890124 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5876) (lo := 0) (len := 1024) (W := 890124) check rows elimOK (by decide) (by decide) cover5876 (by decide)
  decide +kernel

theorem h5876 : P.leaf 34 5876 = 890124 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 890124)]) (.cons c5876_0 (.nil)) (by decide) (by decide))

theorem cover5877 : P.CoversSplit 24 10 5877 0xffffffffaaaa00000000000000000000ffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 475, 573, 860, 909, 916, 1202, 1210, 1259, 1264]) (by decide +kernel)

theorem c5877_0 : P.sumLeaves 24 6018048 1024 = 8782736 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5877) (lo := 0) (len := 1024) (W := 8782736) check rows elimOK (by decide) (by decide) cover5877 (by decide)
  decide +kernel

theorem h5877 : P.leaf 34 5877 = 8782736 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 8782736)]) (.cons c5877_0 (.nil)) (by decide) (by decide))

theorem cover5878 : P.CoversSplit 24 10 5878 0xffffffffaaaa00000000000000000000f5f5f5f50505000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00880000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 475, 573, 860, 916, 1202, 1209, 1210, 1217, 1259, 1264, 1308]) (by decide +kernel)

theorem c5878_0 : P.sumLeaves 24 6019072 1024 = 6945688 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5878) (lo := 0) (len := 1024) (W := 6945688) check rows elimOK (by decide) (by decide) cover5878 (by decide)
  decide +kernel

theorem h5878 : P.leaf 34 5878 = 6945688 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 6945688)]) (.cons c5878_0 (.nil)) (by decide) (by decide))

theorem cover5879 : P.CoversSplit 24 10 5879 0xffffffffaaaa00000000000000000000ffffffffaaaa000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00880000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [475, 573, 860, 916, 1202, 1210, 1259, 1264, 1308]) (by decide +kernel)

theorem c5879_0 : P.sumLeaves 24 6020096 1024 = 21953292 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5879) (lo := 0) (len := 1024) (W := 21953292) check rows elimOK (by decide) (by decide) cover5879 (by decide)
  decide +kernel

theorem h5879 : P.leaf 34 5879 = 21953292 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 21953292)]) (.cons c5879_0 (.nil)) (by decide) (by decide))

theorem cover5880 : P.CoversSplit 24 10 5880 0xfcfcfcfca0a000000000000000000000f0f0f0f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 508, 573, 860, 916, 1202, 1210, 1258, 1259, 1264, 1308]) (ps := [(12, [867], [860, 909]), (14, [487, 923], [487, 860])]) (by decide +kernel)

theorem c5880_0 : P.sumLeaves 24 6021120 1024 = 995094 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5880) (lo := 0) (len := 1024) (W := 995094) check rows elimOK (by decide) (by decide) cover5880 (by decide)
  decide +kernel

theorem h5880 : P.leaf 34 5880 = 995094 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 995094)]) (.cons c5880_0 (.nil)) (by decide) (by decide))

theorem cover5881 : P.CoversSplit 24 10 5881 0xffffffffa0a000000000000000000000ffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 573, 860, 916, 1202, 1210, 1258, 1259, 1264, 1308]) (ps := [(12, [860], [909]), (14, [923], [487])]) (by decide +kernel)

theorem c5881_0 : P.sumLeaves 24 6022144 1024 = 4539328 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5881) (lo := 0) (len := 1024) (W := 4539328) check rows elimOK (by decide) (by decide) cover5881 (by decide)
  decide +kernel

theorem h5881 : P.leaf 34 5881 = 4539328 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 4539328)]) (.cons c5881_0 (.nil)) (by decide) (by decide))

theorem cover5882 : P.CoversSplit 24 10 5882 0xffffffffa0a000000000000000000000f0f0f0f00f0f000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 573, 860, 916, 1202, 1209, 1210, 1217, 1258, 1259, 1264, 1308]) (ps := [(12, [867], [860]), (14, [874, 923], [860, 916])]) (by decide +kernel)

theorem c5882_0 : P.sumLeaves 24 6023168 1024 = 4058016 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5882) (lo := 0) (len := 1024) (W := 4058016) check rows elimOK (by decide) (by decide) cover5882 (by decide)
  decide +kernel

theorem h5882 : P.leaf 34 5882 = 4058016 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 4058016)]) (.cons c5882_0 (.nil)) (by decide) (by decide))

theorem cover5883 : P.CoversSplit 24 10 5883 0xffffffffa0a000000000000000000000ffffffffa0a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [573, 860, 916, 1202, 1210, 1258, 1259, 1264, 1308]) (ps := [(14, [923], [916])]) (by decide +kernel)

theorem c5883_0 : P.sumLeaves 24 6024192 1024 = 8422220 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5883) (lo := 0) (len := 1024) (W := 8422220) check rows elimOK (by decide) (by decide) cover5883 (by decide)
  decide +kernel

theorem h5883 : P.leaf 34 5883 = 8422220 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 8422220)]) (.cons c5883_0 (.nil)) (by decide) (by decide))

theorem cover5884 : P.CoversSplit 24 10 5884 0xfcfcfcfca8a800000000000000000000f4f4f4f40000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00880000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 508, 573, 860, 867, 909, 916, 1202, 1210, 1258, 1259, 1264, 1308]) (by decide +kernel)

theorem c5884_0 : P.sumLeaves 24 6025216 1024 = 6298336 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5884) (lo := 0) (len := 1024) (W := 6298336) check rows elimOK (by decide) (by decide) cover5884 (by decide)
  decide +kernel

theorem h5884 : P.leaf 34 5884 = 6298336 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 6298336)]) (.cons c5884_0 (.nil)) (by decide) (by decide))

theorem cover5885 : P.CoversSplit 24 10 5885 0xffffffffaaaa00000000000000000000ffffffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00880000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 573, 860, 867, 909, 916, 1202, 1210, 1258, 1259, 1264, 1308]) (by decide +kernel)

theorem c5885_0 : P.sumLeaves 24 6026240 1024 = 14358744 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5885) (lo := 0) (len := 1024) (W := 14358744) check rows elimOK (by decide) (by decide) cover5885 (by decide)
  decide +kernel

theorem h5885 : P.leaf 34 5885 = 14358744 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 14358744)]) (.cons c5885_0 (.nil)) (by decide) (by decide))

theorem cover5886 : P.CoversSplit 24 10 5886 0xffffffffaaaa00000000000000000000f5f5f5f50505000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00880000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 573, 860, 867, 916, 1202, 1209, 1210, 1217, 1258, 1259, 1264, 1308]) (by decide +kernel)

theorem c5886_0 : P.sumLeaves 24 6027264 1024 = 15690892 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5886) (lo := 0) (len := 1024) (W := 15690892) check rows elimOK (by decide) (by decide) cover5886 (by decide)
  decide +kernel

theorem h5886 : P.leaf 34 5886 = 15690892 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 15690892)]) (.cons c5886_0 (.nil)) (by decide) (by decide))

theorem cover5887 : P.CoversSplit 24 10 5887 0xffffffffaaaa00000000000000000000ffffffffaaaa000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00880000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [573, 860, 867, 916, 1202, 1210, 1258, 1259, 1264, 1308]) (by decide +kernel)

theorem c5887_0 : P.sumLeaves 24 6028288 1024 = 33209680 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5887) (lo := 0) (len := 1024) (W := 33209680) check rows elimOK (by decide) (by decide) cover5887 (by decide)
  decide +kernel

theorem h5887 : P.leaf 34 5887 = 33209680 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 33209680)]) (.cons c5887_0 (.nil)) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(5852, 48), (5853, 48), (5854, 48), (5855, 48), (5858, 24), (5859, 48), (5860, 48), (5861, 48), (5862, 48), (5863, 48), (5864, 48), (5865, 48), (5866, 48), (5867, 48), (5868, 48), (5869, 48), (5870, 48), (5871, 48), (5875, 24), (5876, 48), (5877, 48), (5878, 48), (5879, 48), (5880, 48), (5881, 48), (5882, 48), (5883, 48), (5884, 48), (5885, 48), (5886, 48), (5887, 48)]

theorem segOK : checkSeg 16 perms 5852 5968 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 5852 5968 1440 9157358880 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 9157358880)
    (SegSum.cons (w := 48) h5852 (SegSum.cons (w := 48) h5853 (SegSum.cons (w := 48) h5854 (SegSum.cons (w := 48) h5855 (SegSum.cons (w := 24) h5858 (SegSum.cons (w := 48) h5859 (SegSum.cons (w := 48) h5860 (SegSum.cons (w := 48) h5861 (SegSum.cons (w := 48) h5862 (SegSum.cons (w := 48) h5863 (SegSum.cons (w := 48) h5864 (SegSum.cons (w := 48) h5865 (SegSum.cons (w := 48) h5866 (SegSum.cons (w := 48) h5867 (SegSum.cons (w := 48) h5868 (SegSum.cons (w := 48) h5869 (SegSum.cons (w := 48) h5870 (SegSum.cons (w := 48) h5871 (SegSum.cons (w := 24) h5875 (SegSum.cons (w := 48) h5876 (SegSum.cons (w := 48) h5877 (SegSum.cons (w := 48) h5878 (SegSum.cons (w := 48) h5879 (SegSum.cons (w := 48) h5880 (SegSum.cons (w := 48) h5881 (SegSum.cons (w := 48) h5882 (SegSum.cons (w := 48) h5883 (SegSum.cons (w := 48) h5884 (SegSum.cons (w := 48) h5885 (SegSum.cons (w := 48) h5886 (SegSum.cons (w := 48) h5887 (show SegSum (P.leaf 34) [] 0 from rfl)))))))))))))))))))))))))))))))) (by decide)

end RACert.S4N1.C0.S33
