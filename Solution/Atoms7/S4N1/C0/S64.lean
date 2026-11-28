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

namespace RACert.S4N1.C0.S64

open RACert RACert.Problem

theorem cover23292 : P.CoversSplit 24 10 23292 0xfcfcfcfca8a80000fcfcfcfca8a80000f0f0f4f400000000f0f0f4f4000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00880000000000000000000000c000c4000000000000300030000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 466, 473, 573, 859, 879, 916, 1202, 1210, 1259, 1601]) (by decide +kernel)

theorem c23292_0 : P.sumLeaves 24 23851008 320 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23292) (lo := 0) (len := 320) (W := 0) check rows elimOK (by decide) (by decide) cover23292 (by decide)
  decide +kernel

theorem contract23292_1 : P.leaf 30 372677 = 0 := by
  exact leaf_contract_zero (ss := [(18, 1, 475), (27, 1, 573), (31, 1, 879), (29, 1, 916), (8, 0, 1266), (21, 0, 580), (20, 1, 531), (10, 1, 880), (14, 1, 880), (28, 1, 859), (11, 1, 923)]) (q := 1266) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c23292_1 : P.sumLeaves 24 23851328 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 372677) rows (by decide) (by decide)).symm.trans contract23292_1

theorem c23292_2 : P.sumLeaves 24 23851392 628 = 30087119 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23292) (lo := 384) (len := 628) (W := 30087119) check rows elimOK (by decide) (by decide) cover23292 (by decide)
  decide +kernel

theorem c23292_3 : P.sumLeaves 24 23852020 12 = 6744048 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23292) (lo := 1012) (len := 12) (W := 6744048) check rows elimOK (by decide) (by decide) cover23292 (by decide)
  decide +kernel

theorem h23292 : P.leaf 34 23292 = 36831167 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(320, 0), (64, 0), (628, 30087119), (12, 6744048)]) (.cons c23292_0 (.cons c23292_1 (.cons c23292_2 (.cons c23292_3 (.nil))))) (by decide) (by decide))

theorem h22254 : P.leaf 34 22254 = 36831167 :=
  orient4 (v := 23292) (by decide) (by decide +kernel) h23292

theorem cover22255 : P.CoversSplit 24 10 22255 0xfffffffffafa0000fffffffffafa0000fffffffffafa0000ffff0000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00c80000000000000000000000cc00cc008800000000330000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [515, 522, 573, 860, 916, 1202, 1210, 1251, 1259, 1601]) (ps := [(14, [1217], [1266])]) (by decide +kernel)

theorem c22255_0 : P.sumLeaves 24 22789120 320 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22255) (lo := 0) (len := 320) (W := 0) check rows elimOK (by decide) (by decide) cover22255 (by decide)
  decide +kernel

theorem contract22255_1 : P.leaf 30 356085 = 0 := by
  exact leaf_contract_zero (ss := [(18, 1, 524), (27, 1, 573), (29, 1, 916), (14, 0, 1266), (12, 1, 867), (8, 0, 923), (5, 1, 433), (21, 0, 580), (20, 1, 433), (7, 1, 628)]) (q := 874) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c22255_1 : P.sumLeaves 24 22789440 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 356085) rows (by decide) (by decide)).symm.trans contract22255_1

theorem c22255_2 : P.sumLeaves 24 22789504 557 = 21593294 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22255) (lo := 384) (len := 557) (W := 21593294) check rows elimOK (by decide) (by decide) cover22255 (by decide)
  decide +kernel

theorem c22255_3 : P.sumLeaves 24 22790061 83 = 41070244 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22255) (lo := 941) (len := 83) (W := 41070244) check rows elimOK (by decide) (by decide) cover22255 (by decide)
  decide +kernel

theorem h22255 : P.leaf 34 22255 = 62663538 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(320, 0), (64, 0), (557, 21593294), (83, 41070244)]) (.cons c22255_0 (.cons c22255_1 (.cons c22255_2 (.cons c22255_3 (.nil))))) (by decide) (by decide))

theorem cover23263 : P.CoversSplit 24 10 23263 0xffffffff00000000ffffffff00000000a0a0000000000000a0a00000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00000000000000000000000000800084000000000080200000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [516, 536, 573, 859, 916, 1202, 1210, 1259, 1301, 1601]) (ps := [(17, [528, 1251], [1259])]) (by decide +kernel)

noncomputable def f23263 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (23821312 + i)

theorem c23263_0 : rowSum f23263 0 1024 = 23014275 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 23263) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover23263 (by decide)
  decide +kernel

theorem sum23263 : rowSum f23263 0 1024 = 23014275 :=
  c23263_0

theorem h23263 : P.leaf 34 23263 = 23014275 :=
  leaf_weighted (k := 24) (d := 10) (H := 23263) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 23263) (by decide) (by decide +kernel)) sum23263

theorem h22267 : P.leaf 34 22267 = 23014275 :=
  orient4 (v := 23263) (by decide) (by decide +kernel) h23263

theorem cover23278 : P.CoversSplit 24 10 23278 0xffffffffaaaa0000ffffffffaaaa0000f0f0000000000000f0f00000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00880000000000000000000000c00000000000000000300000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 515, 522, 573, 859, 879, 916, 1202, 1210, 1259, 1601]) (ps := [(17, [871, 1251], [1259]), (18, [524], [1210])]) (by decide +kernel)

theorem c23278_0 : P.sumLeaves 24 23836672 1010 = 18122138 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23278) (lo := 0) (len := 1010) (W := 18122138) check rows elimOK (by decide) (by decide) cover23278 (by decide)
  decide +kernel

theorem c23278_1 : P.sumLeaves 24 23837682 14 = 5911944 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23278) (lo := 1010) (len := 14) (W := 5911944) check rows elimOK (by decide) (by decide) cover23278 (by decide)
  decide +kernel

theorem h23278 : P.leaf 34 23278 = 24034082 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1010, 18122138), (14, 5911944)]) (.cons c23278_0 (.cons c23278_1 (.nil))) (by decide) (by decide))

theorem h22268 : P.leaf 34 22268 = 24034082 :=
  orient4 (v := 23278) (by decide) (by decide +kernel) h23278

theorem cover23279 : P.CoversSplit 24 10 23279 0xffffffffaaaa0000ffffffffaaaa0000ffff00000000aaaaffff00000000aaaa0000000000000000000000000000000000000000000000000000000000000000cc00cc00880000000000000000000000cc0000000000880000330000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [515, 522, 573, 879, 916, 1202, 1210, 1259, 1601]) (ps := [(8, [1217], [573]), (17, [1251], [1259]), (18, [524], [1210])]) (by decide +kernel)

theorem c23279_0 : P.sumLeaves 24 23837696 320 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23279) (lo := 0) (len := 320) (W := 0) check rows elimOK (by decide) (by decide) cover23279 (by decide)
  decide +kernel

theorem contract23279_1 : P.leaf 30 372469 = 0 := by
  exact leaf_contract_zero (ss := [(18, 1, 524), (4, 1, 536), (27, 1, 573), (29, 1, 916), (14, 0, 1266), (8, 0, 923), (5, 1, 433), (21, 0, 580), (20, 1, 433), (7, 1, 628), (12, 1, 825)]) (q := 880) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c23279_1 : P.sumLeaves 24 23838016 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 372469) rows (by decide) (by decide)).symm.trans contract23279_1

theorem c23279_2 : P.sumLeaves 24 23838080 574 = 24751792 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23279) (lo := 384) (len := 574) (W := 24751792) check rows elimOK (by decide) (by decide) cover23279 (by decide)
  decide +kernel

theorem c23279_3 : P.sumLeaves 24 23838654 66 = 23781309 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23279) (lo := 958) (len := 66) (W := 23781309) check rows elimOK (by decide) (by decide) cover23279 (by decide)
  decide +kernel

theorem h23279 : P.leaf 34 23279 = 48533101 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(320, 0), (64, 0), (574, 24751792), (66, 23781309)]) (.cons c23279_0 (.cons c23279_1 (.cons c23279_2 (.cons c23279_3 (.nil))))) (by decide) (by decide))

theorem h22269 : P.leaf 34 22269 = 48533101 :=
  orient4 (v := 23279) (by decide) (by decide +kernel) h23279

theorem cover23294 : P.CoversSplit 24 10 23294 0xffffffffaaaa0000ffffffffaaaa0000f0f0f5f500000000f0f0f5f5000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00880000000000000000000000c000c4000000000000300030000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 573, 859, 879, 916, 1202, 1210, 1259, 1601]) (ps := [(17, [871], [1259])]) (by decide +kernel)

theorem c23294_0 : P.sumLeaves 24 23853056 320 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23294) (lo := 0) (len := 320) (W := 0) check rows elimOK (by decide) (by decide) cover23294 (by decide)
  decide +kernel

theorem contract23294_1 : P.leaf 30 372709 = 0 := by
  exact leaf_contract_zero (ss := [(27, 1, 573), (29, 1, 916), (8, 0, 1266), (14, 0, 580), (5, 1, 433), (21, 0, 580), (20, 1, 433), (12, 1, 825)]) (q := 880) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c23294_1 : P.sumLeaves 24 23853376 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 372709) rows (by decide) (by decide)).symm.trans contract23294_1

theorem c23294_2 : P.sumLeaves 24 23853440 605 = 38362585 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23294) (lo := 384) (len := 605) (W := 38362585) check rows elimOK (by decide) (by decide) cover23294 (by decide)
  decide +kernel

theorem c23294_3 : P.sumLeaves 24 23854045 35 = 24159098 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23294) (lo := 989) (len := 35) (W := 24159098) check rows elimOK (by decide) (by decide) cover23294 (by decide)
  decide +kernel

theorem h23294 : P.leaf 34 23294 = 62521683 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(320, 0), (64, 0), (605, 38362585), (35, 24159098)]) (.cons c23294_0 (.cons c23294_1 (.cons c23294_2 (.cons c23294_3 (.nil))))) (by decide) (by decide))

theorem h22270 : P.leaf 34 22270 = 62521683 :=
  orient4 (v := 23294) (by decide) (by decide +kernel) h23294

theorem cover23295 : P.CoversSplit 24 10 23295 0xffffffffaaaa0000ffffffffaaaa0000ffffffffaaaa0000ffffffffaaaa00000000000000000000000000000000000000000000000000000000000000000000cc00cc00880000000000000000000000cc00cc008000000000330033002000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [573, 859, 879, 916, 1202, 1210, 1259, 1601]) (ps := [(8, [1217], [573, 1266])]) (by decide +kernel)

theorem c23295_0 : P.sumLeaves 24 23854080 256 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23295) (lo := 0) (len := 256) (W := 0) check rows elimOK (by decide) (by decide) cover23295 (by decide)
  decide +kernel

theorem contract23295_1 : P.leaf 30 372724 = 0 := by
  exact leaf_contract_zero (ss := [(17, 0, 1259), (27, 0, 1259), (8, 0, 573), (9, 0, 573), (29, 0, 573), (18, 1, 578), (14, 0, 580), (5, 1, 433), (21, 0, 580), (20, 1, 433), (7, 1, 628), (15, 0, 678), (12, 1, 825)]) (q := 880) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c23295_1 : P.sumLeaves 24 23854336 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 372724) rows (by decide) (by decide)).symm.trans contract23295_1

theorem contract23295_2 : P.leaf 30 372725 = 0 := by
  exact leaf_contract_zero (ss := [(27, 1, 573), (29, 1, 916), (8, 0, 1266), (14, 0, 580), (5, 1, 433), (21, 0, 580), (20, 1, 433), (12, 1, 825)]) (q := 880) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c23295_2 : P.sumLeaves 24 23854400 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 372725) rows (by decide) (by decide)).symm.trans contract23295_2

theorem c23295_3 : P.sumLeaves 24 23854464 541 = 32889858 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23295) (lo := 384) (len := 541) (W := 32889858) check rows elimOK (by decide) (by decide) cover23295 (by decide)
  decide +kernel

theorem c23295_4 : P.sumLeaves 24 23855005 99 = 71169969 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23295) (lo := 925) (len := 99) (W := 71169969) check rows elimOK (by decide) (by decide) cover23295 (by decide)
  decide +kernel

theorem h23295 : P.leaf 34 23295 = 104059827 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(256, 0), (64, 0), (64, 0), (541, 32889858), (99, 71169969)]) (.cons c23295_0 (.cons c23295_1 (.cons c23295_2 (.cons c23295_3 (.cons c23295_4 (.nil)))))) (by decide) (by decide))

theorem h22271 : P.leaf 34 22271 = 104059827 :=
  orient4 (v := 23295) (by decide) (by decide +kernel) h23295

theorem cover25899 : P.CoversSplit 24 10 25899 0x8000000080000000000000000000000080000000000004000000000000000000800000008000000000000000000000008000000000000400000000000000000080000000800000000000000000000000800000000000000000000000000000000000000000000000002000000020000000000000000000000000000000000001 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 517, 522, 529, 572, 858, 865, 1202]) (by decide +kernel)

theorem h25899 : P.leaf 34 25899 = 1505748 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 25899) (keep := keep5) (twice := twice5) rows (by decide) (by decide) bal5 (invRow5 (H := 25899) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 25899) (weight := rowWeight keep5 twice5) (xs := [0, 149, 181, 383, 479, 511, 586, 639, 735, 767, 842, 895, 991, 1023]) check rows elimOK (by decide) (by decide) cover25899 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h22309 : P.leaf 34 22309 = 1505748 :=
  orient5 (v := 25899) (by decide) (by decide +kernel) h25899

theorem cover25915 : P.CoversSplit 24 10 25915 0xfffffffffafa0000fffffffffafa0000f000ff0000000000f000000000000000ffccffccfac800000000000000000000f000ff00000000000000000000000000f000f000f0000000f0000000f0000000f000f00000000000f0000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [517, 529, 572, 858, 860, 865, 872, 915, 1202, 1251, 1259, 1264, 1601]) (ps := [(14, [867], [915])]) (by decide +kernel)

theorem c25915_0 : P.sumLeaves 24 26536960 917 = 11849023 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 25915) (lo := 0) (len := 917) (W := 11849023) check rows elimOK (by decide) (by decide) cover25915 (by decide)
  decide +kernel

theorem c25915_1 : P.sumLeaves 24 26537877 107 = 14832913 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 25915) (lo := 917) (len := 107) (W := 14832913) check rows elimOK (by decide) (by decide) cover25915 (by decide)
  decide +kernel

theorem h25915 : P.leaf 34 25915 = 26681936 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(917, 11849023), (107, 14832913)]) (.cons c25915_0 (.cons c25915_1 (.nil))) (by decide) (by decide))

theorem h22311 : P.leaf 34 22311 = 26681936 :=
  orient5 (v := 25915) (by decide) (by decide +kernel) h25915

theorem cover25962 : P.CoversSplit 24 10 25962 0xc0000000c00000000000000000000000c0000000000000000000000000000000d0000000d00000000000000000000000d0000000000000000000000000000000c0000000c00000000000000000000000c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 472, 515, 522, 572, 858, 860, 865, 1202]) (by decide +kernel)

theorem h25962 : P.leaf 34 25962 = 952424 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 25962) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 25962) (weight := fun _ => 1) (xs := [382, 383, 478, 479, 510, 511, 636, 638, 639, 732, 734, 735, 764, 766, 767, 894, 895, 990, 991, 1022, 1023]) check rows elimOK (by decide) (by decide) cover25962 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h22316 : P.leaf 34 22316 = 952424 :=
  orient5 (v := 25962) (by decide) (by decide +kernel) h25962

theorem cover25963 : P.CoversSplit 24 10 25963 0xc0000000c00000000000000000000000c0000000000000000000000000000000c0000000c00000000000000000000000c0000000000000000000000000000000c0000000c00000000000000000000000c00000000000000000000000000000000000000000000000003000000030000000000000000000000030000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [472, 515, 522, 572, 858, 865, 1202, 1210]) (by decide +kernel)

theorem h25963 : P.leaf 34 25963 = 4161120 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 25963) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 25963) (weight := fun _ => 1) (xs := [52, 53, 148, 149, 180, 181, 382, 383, 478, 479, 510, 511, 638, 639, 734, 735, 766, 767, 894, 895, 990, 991, 1022, 1023]) check rows elimOK (by decide) (by decide) cover25963 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h22317 : P.leaf 34 22317 = 4161120 :=
  orient5 (v := 25963) (by decide) (by decide +kernel) h25963

theorem cover39275 : P.CoversSplit 24 10 39275 0xf0000000f00000000000000000000000f0000000000000000000000000000000f0000000f00000000000000000000000f0000000000000000000000000000000f0000000f00000000000000000000000f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [466, 515, 522, 572, 858, 865, 1202, 1209, 1258]) (by decide +kernel)

theorem c39275_0 : P.sumLeaves 24 40217600 1024 = 5943344 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 39275) (lo := 0) (len := 1024) (W := 5943344) check rows elimOK (by decide) (by decide) cover39275 (by decide)
  decide +kernel

theorem h39275 : P.leaf 34 39275 = 5943344 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 5943344)]) (.cons c39275_0 (.nil)) (by decide) (by decide))

theorem h22318 : P.leaf 34 22318 = 5943344 :=
  orient25 (v := 39275) (by decide) (by decide +kernel) h39275

theorem cover22319 : P.CoversSplit 24 10 22319 0xfffffffffafa0000fffffffffafa000088888c8c000000008888000000000000cccccccc88880000cc00cc008800000088888c8c000000008800000000000000fffffffffafa0000000000000000000088888c8c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 517, 522, 529, 860, 916, 1202, 1210, 1251, 1259, 1601]) (by decide +kernel)

theorem c22319_0 : P.sumLeaves 24 22854656 819 = 15943634 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22319) (lo := 0) (len := 819) (W := 15943634) check rows elimOK (by decide) (by decide) cover22319 (by decide)
  decide +kernel

theorem c22319_1 : P.sumLeaves 24 22855475 199 = 34618296 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22319) (lo := 819) (len := 199) (W := 34618296) check rows elimOK (by decide) (by decide) cover22319 (by decide)
  decide +kernel

theorem c22319_2 : P.sumLeaves 24 22855674 6 = 4842606 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22319) (lo := 1018) (len := 6) (W := 4842606) check rows elimOK (by decide) (by decide) cover22319 (by decide)
  decide +kernel

theorem h22319 : P.leaf 34 22319 = 55404536 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(819, 15943634), (199, 34618296), (6, 4842606)]) (.cons c22319_0 (.cons c22319_1 (.cons c22319_2 (.nil)))) (by decide) (by decide))

theorem cover26427 : P.CoversSplit 24 10 26427 0xfffffffffafa0000fffffffffafa0000ffffffff00000000ffff000000000000ffccffccfac800000000000000000000ffccffcc000000000000000000000000fffffffffafa0000ffff0000fafa0000ffffffff00000000ffff0000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [517, 529, 572, 860, 872, 1202, 1217, 1251, 1259, 1264, 1308, 1601, 1609]) (ps := [(8, [615], [1217, 1272])]) (by decide +kernel)

noncomputable def f26427 (i : ℕ) := rowWeight keep5 twice5 i * P.leaf 24 (27061248 + i)

theorem c26427_0 : rowSum f26427 0 510 = 41292680 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 26427) (keep := keep5) (twice := twice5) check rows elimOK (by decide) (by decide) cover26427 (by decide)
  decide +kernel

theorem c26427_1 : rowSum f26427 510 514 = 62935282 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 26427) (keep := keep5) (twice := twice5) check rows elimOK (by decide) (by decide) cover26427 (by decide)
  decide +kernel

theorem sum26427 : rowSum f26427 0 1024 = 104227962 :=
  rowSum_append (F := f26427) (lo := 0) (n := 510) (m := 514) (A := 41292680) (B := 62935282) c26427_0 (c26427_1)

theorem h26427 : P.leaf 34 26427 = 104227962 :=
  leaf_weighted (k := 24) (d := 10) (H := 26427) (keep := keep5) (twice := twice5) rows (by decide) (by decide) (bal5) (invRow5 (H := 26427) (by decide) (by decide +kernel)) sum26427

theorem h22327 : P.leaf 34 22327 = 104227962 :=
  orient5 (v := 26427) (by decide) (by decide +kernel) h26427

def seg : List (ℕ × ℕ) := [(22254, 48), (22255, 48), (22267, 12), (22268, 48), (22269, 48), (22270, 48), (22271, 48), (22309, 24), (22311, 48), (22316, 48), (22317, 48), (22318, 48), (22319, 48), (22327, 24)]

theorem segOK : checkSeg 16 perms 22254 22332 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 22254 22332 588 23539544724 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 23539544724)
    (SegSum.cons (w := 48) h22254 (SegSum.cons (w := 48) h22255 (SegSum.cons (w := 12) h22267 (SegSum.cons (w := 48) h22268 (SegSum.cons (w := 48) h22269 (SegSum.cons (w := 48) h22270 (SegSum.cons (w := 48) h22271 (SegSum.cons (w := 24) h22309 (SegSum.cons (w := 48) h22311 (SegSum.cons (w := 48) h22316 (SegSum.cons (w := 48) h22317 (SegSum.cons (w := 48) h22318 (SegSum.cons (w := 48) h22319 (SegSum.cons (w := 24) h22327 (show SegSum (P.leaf 34) [] 0 from rfl))))))))))))))) (by decide)

end RACert.S4N1.C0.S64
