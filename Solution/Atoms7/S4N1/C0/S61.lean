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

namespace RACert.S4N1.C0.S61

open RACert RACert.Problem

theorem cover21822 : P.CoversSplit 24 10 21822 0xf0f00000f0f00000f0f00000f0f00000f000000000000000f000000000000000c0c0000080800000c000000080000000c000000000000000c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 529, 572, 858, 860, 865, 867, 909, 916, 1202, 1210, 1217, 1601]) (by decide +kernel)

theorem c21822_0 : P.sumLeaves 24 22345728 1024 = 5998848 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21822) (lo := 0) (len := 1024) (W := 5998848) check rows elimOK (by decide) (by decide) cover21822 (by decide)
  decide +kernel

theorem h21822 : P.leaf 34 21822 = 5998848 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 5998848)]) (.cons c21822_0 (.nil)) (by decide) (by decide))

theorem cover21823 : P.CoversSplit 24 10 21823 0xfffffffffafa0000fffffffffafa0000f500f50000000000f500000000000000cccccccc88880000cc00cc0088000000c400c40000000000c400000000000000fffffffffafa0000ffff0000fafa0000f500f50040000000f5000000000000000000000000000000cc0000008800000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [517, 529, 572, 858, 860, 865, 909, 916, 1202, 1210, 1217, 1251, 1264, 1308, 1601, 1609]) (by decide +kernel)

theorem c21823_0 : P.sumLeaves 24 22346752 511 = 11648726 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21823) (lo := 0) (len := 511) (W := 11648726) check rows elimOK (by decide) (by decide) cover21823 (by decide)
  decide +kernel

theorem c21823_1 : P.sumLeaves 24 22347263 443 = 21134398 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21823) (lo := 511) (len := 443) (W := 21134398) check rows elimOK (by decide) (by decide) cover21823 (by decide)
  decide +kernel

theorem c21823_2 : P.sumLeaves 24 22347706 70 = 30295952 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21823) (lo := 954) (len := 70) (W := 30295952) check rows elimOK (by decide) (by decide) cover21823 (by decide)
  decide +kernel

theorem h21823 : P.leaf 34 21823 = 63079076 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(511, 11648726), (443, 21134398), (70, 30295952)]) (.cons c21823_0 (.cons c21823_1 (.cons c21823_2 (.nil)))) (by decide) (by decide))

theorem cover21836 : P.CoversSplit 24 10 21836 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem h21836 : P.leaf 34 21836 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 21836) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 21836) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover21836 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover21837 : P.CoversSplit 24 10 21837 0xc0000000c00000000000000000000000c0000000000000000000000000000000c0000000800000000000000000000000c0000000000000000000000000000000c0000000c00000000000000000000000c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 515, 516, 522, 572, 858, 865, 916, 1202, 1210, 1217, 1259]) (ps := [(11, [472], [858])]) (by decide +kernel)

theorem h21837 : P.leaf 34 21837 = 187424 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 21837) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 21837) (weight := fun _ => 1) (xs := [382, 383, 478, 479, 510, 511, 638, 639, 735, 766, 767, 894, 895, 990, 991, 1022, 1023]) check rows elimOK (by decide) (by decide) cover21837 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover21839 : P.CoversSplit 24 10 21839 0xc0c00000c0c000000000000000000000c0c00000000000000000000000000000c0c00000800000000000000000000000c0c00000000000000000000000000000c0c00000c0c000000000000000000000c0c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [515, 516, 522, 572, 858, 1202, 1210, 1217, 1259, 1601, 1609]) (ps := [(8, [565], [1609])]) (by decide +kernel)

noncomputable def f21839 (i : ℕ) := rowWeight keep5 twice5 i * P.leaf 24 (22363136 + i)

theorem c21839_0 : rowSum f21839 0 1024 = 1155424 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 21839) (keep := keep5) (twice := twice5) check rows elimOK (by decide) (by decide) cover21839 (by decide)
  decide +kernel

theorem sum21839 : rowSum f21839 0 1024 = 1155424 :=
  c21839_0

theorem h21839 : P.leaf 34 21839 = 1155424 :=
  leaf_weighted (k := 24) (d := 10) (H := 21839) (keep := keep5) (twice := twice5) rows (by decide) (by decide) (bal5) (invRow5 (H := 21839) (by decide) (by decide +kernel)) sum21839

theorem cover21852 : P.CoversSplit 24 10 21852 0x80000000c000800080000000c000800080000000000000008000000000000000800000008000800080000000800080008000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 466, 472, 473, 516, 858, 867, 1202, 1210, 1601]) (by decide +kernel)

theorem h21852 : P.leaf 34 21852 = 732971 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 21852) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 21852) (weight := fun _ => 1) (xs := [575, 639, 655, 671, 703, 719, 735, 767, 831, 895, 911, 926, 927, 959, 975, 990, 991, 1023]) check rows elimOK (by decide) (by decide) cover21852 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover21853 : P.CoversSplit 24 10 21853 0xcc00cc00c0008000cc00cc00c0008000cc00000000000000cc00000000000000cc00cc0080008000cc00cc0080008000cc00000000000000cc00000000000000cc00cc00c0008000cc000000c0000000cc00440000000000cc000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 516, 572, 858, 909, 916, 1202, 1210, 1217, 1259, 1264, 1601]) (by decide +kernel)

theorem c21853_0 : P.sumLeaves 24 22377472 320 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21853) (lo := 0) (len := 320) (W := 0) check rows elimOK (by decide) (by decide) cover21853 (by decide)
  decide +kernel

theorem contract21853_1 : P.leaf 30 349653 = 0 := by
  exact leaf_contract_zero (ss := [(27, 1, 473), (29, 1, 473), (11, 1, 879), (8, 0, 1266), (31, 5, 565), (20, 1, 580), (21, 1, 586), (5, 1, 615)]) (q := 1266) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c21853_1 : P.sumLeaves 24 22377792 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 349653) rows (by decide) (by decide)).symm.trans contract21853_1

theorem c21853_2 : P.sumLeaves 24 22377856 640 = 9580338 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21853) (lo := 384) (len := 640) (W := 9580338) check rows elimOK (by decide) (by decide) cover21853 (by decide)
  decide +kernel

theorem h21853 : P.leaf 34 21853 = 9580338 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(320, 0), (64, 0), (640, 9580338)]) (.cons c21853_0 (.cons c21853_1 (.cons c21853_2 (.nil)))) (by decide) (by decide))

theorem cover21854 : P.CoversSplit 24 10 21854 0xa0a00000a0a00000a0a00000a0a00000a0a0000000000505a0a0000000000505808000008000000080000000800000008080000000000400800000000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 516, 572, 858, 865, 867, 1202, 1259, 1601]) (by decide +kernel)

theorem c21854_0 : P.sumLeaves 24 22378496 1024 = 3252897 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21854) (lo := 0) (len := 1024) (W := 3252897) check rows elimOK (by decide) (by decide) cover21854 (by decide)
  decide +kernel

theorem h21854 : P.leaf 34 21854 = 3252897 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 3252897)]) (.cons c21854_0 (.nil)) (by decide) (by decide))

theorem cover21855 : P.CoversSplit 24 10 21855 0xfffffffff0f0a0a0fffffffff0f0a0a0ffff000000000000ffff000000000000cccccccc80008000cc00cc0080008000cccc000000000000cc00000000000000fffffffff0f0a0a0ffff0000f0f00000ffff555500000000ffff0000000000000000000000000000cc00000080000000cccc000040000000cc00000040000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [516, 572, 1202, 1210, 1217, 1259, 1264, 1601, 1609]) (by decide +kernel)

theorem contract21855_0 : P.leaf 30 349680 = 0 := by
  exact leaf_contract_zero (ss := [(3, 1, 536), (4, 1, 578), (11, 1, 879), (29, 1, 1259), (30, 1, 1264), (8, 0, 1266), (5, 1, 565), (21, 0, 1266), (14, 1, 537), (10, 1, 874), (31, 20, 1272)]) (q := 1315) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c21855_0 : P.sumLeaves 24 22379520 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 349680) rows (by decide) (by decide)).symm.trans contract21855_0

theorem contract21855_1 : P.leaf 30 349681 = 0 := by
  exact leaf_contract_zero (ss := [(3, 1, 536), (4, 1, 578), (11, 1, 879), (30, 1, 1264), (8, 0, 1266), (5, 1, 565), (21, 0, 1266), (14, 1, 537), (10, 1, 874), (31, 20, 1272)]) (q := 1315) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c21855_1 : P.sumLeaves 24 22379584 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 349681) rows (by decide) (by decide)).symm.trans contract21855_1

theorem c21855_2 : P.sumLeaves 24 22379648 128 = 8512 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21855) (lo := 128) (len := 128) (W := 8512) check rows elimOK (by decide) (by decide) cover21855 (by decide)
  decide +kernel

theorem contract21855_3 : P.leaf 30 349684 = 0 := by
  exact leaf_contract_zero (ss := [(11, 1, 879), (30, 1, 1264), (31, 1, 1210), (8, 0, 1266), (5, 1, 565), (21, 0, 1266), (14, 1, 537), (10, 1, 874), (20, 1, 1272)]) (q := 1315) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c21855_3 : P.sumLeaves 24 22379776 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 349684) rows (by decide) (by decide)).symm.trans contract21855_3

theorem contract21855_4 : P.leaf 30 349685 = 0 := by
  exact leaf_contract_zero (ss := [(11, 1, 879), (8, 0, 1266), (5, 1, 565), (21, 0, 1266), (14, 1, 537), (10, 1, 874), (20, 1, 1272)]) (q := 1315) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c21855_4 : P.sumLeaves 24 22379840 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 349685) rows (by decide) (by decide)).symm.trans contract21855_4

theorem c21855_5 : P.sumLeaves 24 22379904 362 = 15961747 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21855) (lo := 384) (len := 362) (W := 15961747) check rows elimOK (by decide) (by decide) cover21855 (by decide)
  decide +kernel

theorem c21855_6 : P.sumLeaves 24 22380266 242 = 27544233 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21855) (lo := 746) (len := 242) (W := 27544233) check rows elimOK (by decide) (by decide) cover21855 (by decide)
  decide +kernel

theorem c21855_7 : P.sumLeaves 24 22380508 36 = 18714870 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21855) (lo := 988) (len := 36) (W := 18714870) check rows elimOK (by decide) (by decide) cover21855 (by decide)
  decide +kernel

theorem h21855 : P.leaf 34 21855 = 62229362 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(64, 0), (64, 0), (128, 8512), (64, 0), (64, 0), (362, 15961747), (242, 27544233), (36, 18714870)]) (.cons c21855_0 (.cons c21855_1 (.cons c21855_2 (.cons c21855_3 (.cons c21855_4 (.cons c21855_5 (.cons c21855_6 (.cons c21855_7 (.nil))))))))) (by decide) (by decide))

theorem cover22828 : P.CoversSplit 24 10 22828 0x8000000088008000000000000000000000000000000000000000000000000000808000008880808080000000880080000000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 515, 517, 522, 529, 572, 858, 865, 879, 1202, 1259]) (by decide +kernel)

theorem h22828 : P.leaf 34 22828 = 99492 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 22828) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 22828) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 22828) (weight := rowWeight keep1 twice1) (xs := [383, 655, 667, 671, 703, 711, 719, 727, 731, 735, 759, 767, 975, 987, 991, 1023]) check rows elimOK (by decide) (by decide) cover22828 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h21860 : P.leaf 34 21860 = 99492 :=
  orient4 (v := 22828) (by decide) (by decide +kernel) h22828

theorem cover22829 : P.CoversSplit 24 10 22829 0x8800000088008000000000000000000000000000000000000000000000000000880000008800800000000000000000000000000000000000000000000000000088000000880080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 515, 517, 522, 529, 572, 858, 865, 879, 916, 1202, 1601]) (by decide +kernel)

theorem h22829 : P.leaf 34 22829 = 483368 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 22829) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 22829) (weight := fun _ => 1) (xs := [463, 475, 479, 507, 511, 719, 731, 735, 763, 767, 975, 987, 991, 1019, 1023]) check rows elimOK (by decide) (by decide) cover22829 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h21861 : P.leaf 34 21861 = 483368 :=
  orient4 (v := 22829) (by decide) (by decide +kernel) h22829

theorem cover22844 : P.CoversSplit 24 10 22844 0x8000800080008000800080008000800000000000000000000000000000000000800080008000800080008000800080000000000000000000000000000000000000000000000000000000000000000000800080000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 508, 517, 529, 572, 858, 859, 879, 916, 1202, 1251, 1259, 1601]) (by decide +kernel)

theorem h22844 : P.leaf 34 22844 = 1320648 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 22844) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 22844) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 22844) (weight := rowWeight keep1 twice1) (xs := [319, 367, 383, 655, 671, 687, 703, 719, 735, 751, 767, 911, 927, 943, 959, 975, 991, 1007, 1023]) check rows elimOK (by decide) (by decide) cover22844 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h21862 : P.leaf 34 21862 = 1320648 :=
  orient4 (v := 22844) (by decide) (by decide +kernel) h22844

theorem cover21863 : P.CoversSplit 24 10 21863 0xc0c00000c0c000000000000000000000c0c00000000000000000000000000000c0c00000808000000000000000000000c0c00000404000000000000000000000c0c00000c0c000000000000000000000c0c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 522, 572, 858, 860, 916, 1202, 1210, 1259, 1601]) (by decide +kernel)

theorem c21863_0 : P.sumLeaves 24 22387712 1024 = 6103748 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21863) (lo := 0) (len := 1024) (W := 6103748) check rows elimOK (by decide) (by decide) cover21863 (by decide)
  decide +kernel

theorem h21863 : P.leaf 34 21863 = 6103748 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 6103748)]) (.cons c21863_0 (.nil)) (by decide) (by decide))

theorem cover21868 : P.CoversSplit 24 10 21868 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem h21868 : P.leaf 34 21868 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 21868) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 21868) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover21868 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover21869 : P.CoversSplit 24 10 21869 0xc0000000c00088000000000000000000c0000000000000000000000000000000c0000000800088000000000000000000c0000000400000000000000000000000c0000000c00088000000000000000000c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 515, 522, 572, 858, 860, 865, 916, 1210, 1601]) (by decide +kernel)

theorem h21869 : P.leaf 34 21869 = 1656318 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 21869) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 21869) (weight := fun _ => 1) (xs := [382, 383, 459, 463, 478, 479, 510, 511, 606, 638, 639, 715, 719, 735, 766, 767, 894, 895, 971, 975, 990, 991, 1022, 1023]) check rows elimOK (by decide) (by decide) cover21869 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover22908 : P.CoversSplit 24 10 22908 0xc000c00080008000c000c0008000800000000000000000000000000000000000c0c0c0c080808080c000c000800080000000000000000000000000000000000000000000000000000000000000000000c000c00000000000c0000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 508, 572, 859, 865, 879, 916, 1202, 1259, 1264, 1601]) (by decide +kernel)

theorem c22908_0 : P.sumLeaves 24 23457792 1024 = 2575264 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22908) (lo := 0) (len := 1024) (W := 2575264) check rows elimOK (by decide) (by decide) cover22908 (by decide)
  decide +kernel

theorem h22908 : P.leaf 34 22908 = 2575264 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 2575264)]) (.cons c22908_0 (.nil)) (by decide) (by decide))

theorem h21870 : P.leaf 34 21870 = 2575264 :=
  orient4 (v := 22908) (by decide) (by decide +kernel) h22908

theorem cover21871 : P.CoversSplit 24 10 21871 0xc0c00000c0c000000000000000000000c0c00000000000000000000000000000c0c00000808000000000000000000000c0c00000404000000000000000000000c0c00000c0c000000000000000000000c0c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 522, 572, 858, 860, 916, 1202, 1210, 1259, 1601]) (by decide +kernel)

theorem c21871_0 : P.sumLeaves 24 22395904 1024 = 7712560 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21871) (lo := 0) (len := 1024) (W := 7712560) check rows elimOK (by decide) (by decide) cover21871 (by decide)
  decide +kernel

theorem h21871 : P.leaf 34 21871 = 7712560 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 7712560)]) (.cons c21871_0 (.nil)) (by decide) (by decide))

theorem cover22831 : P.CoversSplit 24 10 22831 0x8888000088880000000000000000000088880000000000000000000000000000888800008888000000000000000000008888000000000000000000000000000088880000888800000000000000000000888800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 517, 522, 572, 858, 1202, 1210, 1259, 1601]) (by decide +kernel)

noncomputable def f22831 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (23378944 + i)

theorem c22831_0 : rowSum f22831 0 1024 = 9588616 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 22831) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover22831 (by decide)
  decide +kernel

theorem sum22831 : rowSum f22831 0 1024 = 9588616 :=
  c22831_0

theorem h22831 : P.leaf 34 22831 = 9588616 :=
  leaf_weighted (k := 24) (d := 10) (H := 22831) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 22831) (by decide) (by decide +kernel)) sum22831

theorem h21877 : P.leaf 34 21877 = 9588616 :=
  orient4 (v := 22831) (by decide) (by decide +kernel) h22831

theorem cover22847 : P.CoversSplit 24 10 22847 0xffffffffaaaaa0a0ffffffffaaaaa0a0ffffffff0000a0a0ffff000000000000cccccccc88888080cc00cc0088008000cccccccc00008080cc00000000000000ffffffffaaaaa0a0ffff0000aaaa0000ffffffff00000000ffff0000000000000000000000000000cc0000008800000000000000888800000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [517, 572, 858, 865, 1202, 1217, 1251, 1259, 1264, 1308, 1601, 1609]) (by decide +kernel)

noncomputable def f22847 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (23395328 + i)

theorem c22847_0 : rowSum f22847 0 505 = 41402066 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 22847) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover22847 (by decide)
  decide +kernel

theorem c22847_1 : rowSum f22847 505 519 = 88152421 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 22847) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover22847 (by decide)
  decide +kernel

theorem sum22847 : rowSum f22847 0 1024 = 129554487 :=
  rowSum_append (F := f22847) (lo := 0) (n := 505) (m := 519) (A := 41402066) (B := 88152421) c22847_0 (c22847_1)

theorem h22847 : P.leaf 34 22847 = 129554487 :=
  leaf_weighted (k := 24) (d := 10) (H := 22847) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 22847) (by decide) (by decide +kernel)) sum22847

theorem h21879 : P.leaf 34 21879 = 129554487 :=
  orient4 (v := 22847) (by decide) (by decide +kernel) h22847

theorem cover21884 : P.CoversSplit 24 10 21884 0xc0000000c0008000c0000000c0008000c000000040000000c000000040000000c0c0000080808080c000000080008000c000000000000000c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 466, 473, 572, 858, 860, 865, 867, 909, 916, 1202, 1210, 1601]) (by decide +kernel)

theorem h21884 : P.leaf 34 21884 = 3610180 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 21884) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 21884) (weight := fun _ => 1) (xs := [574, 575, 638, 639, 655, 671, 702, 703, 711, 719, 727, 735, 758, 759, 766, 767, 798, 830, 831, 862, 894, 895, 911, 926, 927, 958, 959, 975, 990, 991, 1022, 1023]) check rows elimOK (by decide) (by decide) cover21884 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover22895 : P.CoversSplit 24 10 22895 0xcccccccc888888880000000000000000cccc0000000000000000000000000000cccccccc888888880000000000000000cccc0000000000000000000000000000cccccccc888888880000000000000000cccc44440000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 522, 572, 858, 865, 1202, 1210, 1259, 1601]) (by decide +kernel)

theorem c22895_0 : P.sumLeaves 24 23444480 1018 = 22789816 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22895) (lo := 0) (len := 1018) (W := 22789816) check rows elimOK (by decide) (by decide) cover22895 (by decide)
  decide +kernel

theorem c22895_1 : P.sumLeaves 24 23445498 6 = 6292030 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22895) (lo := 1018) (len := 6) (W := 6292030) check rows elimOK (by decide) (by decide) cover22895 (by decide)
  decide +kernel

theorem h22895 : P.leaf 34 22895 = 29081846 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1018, 22789816), (6, 6292030)]) (.cons c22895_0 (.cons c22895_1 (.nil))) (by decide) (by decide))

theorem h21885 : P.leaf 34 21885 = 29081846 :=
  orient4 (v := 22895) (by decide) (by decide +kernel) h22895

theorem cover21886 : P.CoversSplit 24 10 21886 0xf0f00000f0f00000f0f00000f0f00000f0f0000050500000f0f0000050500000c0c0000080800000c000000080000000c0c0000000000000c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 572, 858, 860, 865, 867, 916, 1202, 1210, 1601]) (by decide +kernel)

theorem c21886_0 : P.sumLeaves 24 22411264 1024 = 20827198 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21886) (lo := 0) (len := 1024) (W := 20827198) check rows elimOK (by decide) (by decide) cover21886 (by decide)
  decide +kernel

theorem h21886 : P.leaf 34 21886 = 20827198 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 20827198)]) (.cons c21886_0 (.nil)) (by decide) (by decide))

theorem cover22911 : P.CoversSplit 24 10 22911 0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaacccccccc88888888cc00cc0088008800cccccccc88888888cc00cc0088008800ffffffffaaaaaaaaffff0000aaaa0000ffffffff00000000ffff0000000000000000000000000000cc00000088000000cccc000000000000cc00000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [572, 858, 865, 1202, 1259, 1264, 1308, 1601, 1609]) (by decide +kernel)

theorem c22911_0 : P.sumLeaves 24 23460864 461 = 20952173 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22911) (lo := 0) (len := 461) (W := 20952173) check rows elimOK (by decide) (by decide) cover22911 (by decide)
  decide +kernel

theorem c22911_1 : P.sumLeaves 24 23461325 270 = 39394297 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22911) (lo := 461) (len := 270) (W := 39394297) check rows elimOK (by decide) (by decide) cover22911 (by decide)
  decide +kernel

theorem c22911_2 : P.sumLeaves 24 23461595 147 = 44098619 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22911) (lo := 731) (len := 147) (W := 44098619) check rows elimOK (by decide) (by decide) cover22911 (by decide)
  decide +kernel

theorem c22911_3 : P.sumLeaves 24 23461742 128 = 95037861 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22911) (lo := 878) (len := 128) (W := 95037861) check rows elimOK (by decide) (by decide) cover22911 (by decide)
  decide +kernel

theorem c22911_4 : P.sumLeaves 24 23461870 18 = 36326443 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22911) (lo := 1006) (len := 18) (W := 36326443) check rows elimOK (by decide) (by decide) cover22911 (by decide)
  decide +kernel

theorem h22911 : P.leaf 34 22911 = 235809393 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(461, 20952173), (270, 39394297), (147, 44098619), (128, 95037861), (18, 36326443)]) (.cons c22911_0 (.cons c22911_1 (.cons c22911_2 (.cons c22911_3 (.cons c22911_4 (.nil)))))) (by decide) (by decide))

theorem h21887 : P.leaf 34 21887 = 235809393 :=
  orient4 (v := 22911) (by decide) (by decide +kernel) h22911

def seg : List (ℕ × ℕ) := [(21822, 48), (21823, 48), (21836, 24), (21837, 48), (21839, 24), (21852, 48), (21853, 48), (21854, 48), (21855, 48), (21860, 24), (21861, 48), (21862, 24), (21863, 48), (21868, 48), (21869, 48), (21870, 48), (21871, 48), (21877, 24), (21879, 24), (21884, 48), (21885, 48), (21886, 48), (21887, 48)]

theorem segOK : checkSeg 16 perms 21822 21932 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 21822 21932 960 25141445976 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 25141445976)
    (SegSum.cons (w := 48) h21822 (SegSum.cons (w := 48) h21823 (SegSum.cons (w := 24) h21836 (SegSum.cons (w := 48) h21837 (SegSum.cons (w := 24) h21839 (SegSum.cons (w := 48) h21852 (SegSum.cons (w := 48) h21853 (SegSum.cons (w := 48) h21854 (SegSum.cons (w := 48) h21855 (SegSum.cons (w := 24) h21860 (SegSum.cons (w := 48) h21861 (SegSum.cons (w := 24) h21862 (SegSum.cons (w := 48) h21863 (SegSum.cons (w := 48) h21868 (SegSum.cons (w := 48) h21869 (SegSum.cons (w := 48) h21870 (SegSum.cons (w := 48) h21871 (SegSum.cons (w := 24) h21877 (SegSum.cons (w := 24) h21879 (SegSum.cons (w := 48) h21884 (SegSum.cons (w := 48) h21885 (SegSum.cons (w := 48) h21886 (SegSum.cons (w := 48) h21887 (show SegSum (P.leaf 34) [] 0 from rfl)))))))))))))))))))))))) (by decide)

end RACert.S4N1.C0.S61
