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

namespace RACert.S4N1.C0.S70

open RACert RACert.Problem

theorem cover21807 : P.CoversSplit 24 10 21807 0x8080000080800000000000000000000080800000000004040000000000000000808000008080000000000000000000008080000000000404000000000000000080800000808000000000000000000000808000000000040400000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 517, 522, 529, 572, 858, 860, 1259, 1601]) (by decide +kernel)

theorem c21807_0 : P.sumLeaves 24 22330368 1024 = 1797293 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21807) (lo := 0) (len := 1024) (W := 1797293) check rows elimOK (by decide) (by decide) cover21807 (by decide)
  decide +kernel

theorem h21807 : P.leaf 34 21807 = 1797293 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1797293)]) (.cons c21807_0 (.nil)) (by decide) (by decide))

theorem cover21813 : P.CoversSplit 24 10 21813 0xcc00cc00c8000000cc00cc00c8000000c400c40000000000c400000000000000cc00cc0088000000cc00cc0088000000c400c40000000000c400000000000000cc00cc00c8000000cc000000c8000000c400c40040000000c4000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 517, 529, 572, 858, 860, 909, 916, 1202, 1210, 1217, 1251, 1264, 1308, 1601]) (by decide +kernel)

theorem c21813_0 : P.sumLeaves 24 22336512 1024 = 3157048 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21813) (lo := 0) (len := 1024) (W := 3157048) check rows elimOK (by decide) (by decide) cover21813 (by decide)
  decide +kernel

theorem h21813 : P.leaf 34 21813 = 3157048 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 3157048)]) (.cons c21813_0 (.nil)) (by decide) (by decide))

theorem cover21814 : P.CoversSplit 24 10 21814 0xf0f00000f0f00000f0f00000f0f00000f000000000000000f000000000000000c0c0000080800000c000000080000000c000000000000000c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 517, 529, 572, 858, 860, 865, 867, 909, 916, 1210, 1217, 1601]) (by decide +kernel)

theorem c21814_0 : P.sumLeaves 24 22337536 1024 = 877712 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21814) (lo := 0) (len := 1024) (W := 877712) check rows elimOK (by decide) (by decide) cover21814 (by decide)
  decide +kernel

theorem h21814 : P.leaf 34 21814 = 877712 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 877712)]) (.cons c21814_0 (.nil)) (by decide) (by decide))

theorem cover21815 : P.CoversSplit 24 10 21815 0xfffffffffafa0000fffffffffafa0000f500f50000000000f500000000000000cccccccc88880000cc00cc0088000000c400c40000000000c400000000000000fffffffffafa0000ffff0000fafa0000f500f50040000000f5000000000000000000000000000000cc0000008800000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [517, 529, 572, 858, 860, 865, 909, 916, 1202, 1210, 1217, 1251, 1264, 1308, 1601, 1609]) (by decide +kernel)

theorem c21815_0 : P.sumLeaves 24 22338560 128 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21815) (lo := 0) (len := 128) (W := 0) check rows elimOK (by decide) (by decide) cover21815 (by decide)
  decide +kernel

theorem contract21815_1 : P.leaf 30 349042 = 0 := by
  exact leaf_contract_zero (ss := [(4, 1, 578), (11, 1, 921), (30, 1, 1264), (25, 1, 1258), (18, 1, 1308), (29, 27, 1601), (27, 1, 572), (2, 1, 475), (13, 1, 922), (8, 0, 1609), (5, 1, 468), (3, 1, 524)]) (q := 622) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c21815_1 : P.sumLeaves 24 22338688 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 349042) rows (by decide) (by decide)).symm.trans contract21815_1

theorem c21815_2 : P.sumLeaves 24 22338752 431 = 9290386 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21815) (lo := 192) (len := 431) (W := 9290386) check rows elimOK (by decide) (by decide) cover21815 (by decide)
  decide +kernel

theorem c21815_3 : P.sumLeaves 24 22339183 354 = 13761099 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21815) (lo := 623) (len := 354) (W := 13761099) check rows elimOK (by decide) (by decide) cover21815 (by decide)
  decide +kernel

theorem c21815_4 : P.sumLeaves 24 22339537 47 = 15481746 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21815) (lo := 977) (len := 47) (W := 15481746) check rows elimOK (by decide) (by decide) cover21815 (by decide)
  decide +kernel

theorem h21815 : P.leaf 34 21815 = 38533231 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(128, 0), (64, 0), (431, 9290386), (354, 13761099), (47, 15481746)]) (.cons c21815_0 (.cons c21815_1 (.cons c21815_2 (.cons c21815_3 (.cons c21815_4 (.nil)))))) (by decide) (by decide))

theorem cover21820 : P.CoversSplit 24 10 21820 0xc0000000c0000000c0000000c0000000c000000000000000c000000000000000c000000080000000c000000080000000c000000000000000c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 466, 473, 508, 529, 858, 860, 867, 1202, 1210, 1217, 1601]) (by decide +kernel)

theorem c21820_0 : P.sumLeaves 24 22343680 1024 = 1442576 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21820) (lo := 0) (len := 1024) (W := 1442576) check rows elimOK (by decide) (by decide) cover21820 (by decide)
  decide +kernel

theorem h21820 : P.leaf 34 21820 = 1442576 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1442576)]) (.cons c21820_0 (.nil)) (by decide) (by decide))

theorem cover21821 : P.CoversSplit 24 10 21821 0xcc00cc00c8000000cc00cc00c8000000c400c40000000000c400000000000000cc00cc0088000000cc00cc0088000000c400c40000000000c400000000000000cc00cc00c8000000cc000000c8000000c400c40040000000c4000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 517, 529, 572, 858, 860, 909, 916, 1202, 1210, 1217, 1251, 1264, 1308, 1601]) (by decide +kernel)

theorem c21821_0 : P.sumLeaves 24 22344704 1024 = 11160970 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21821) (lo := 0) (len := 1024) (W := 11160970) check rows elimOK (by decide) (by decide) cover21821 (by decide)
  decide +kernel

theorem h21821 : P.leaf 34 21821 = 11160970 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 11160970)]) (.cons c21821_0 (.nil)) (by decide) (by decide))

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

theorem c21823_0 : P.sumLeaves 24 22346752 128 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21823) (lo := 0) (len := 128) (W := 0) check rows elimOK (by decide) (by decide) cover21823 (by decide)
  decide +kernel

theorem contract21823_1 : P.leaf 30 349170 = 2624 := by
  exact leaf_contract_factors (k := 30) (b := 13) (H := 349170) (ss := [(4, 1, 578), (11, 1, 921), (30, 1, 1264), (25, 1, 1258), (18, 1, 1308), (29, 27, 1601), (27, 1, 572), (8, 0, 1609), (5, 3, 524), (3, 1, 580), (14, 0, 1609), (9, 1, 629), (21, 1, 629), (20, 1, 678), (15, 1, 874), (12, 1, 965), (16, 1, 1265)]) (ids := [4, 5, 8, 17, 21, 22, 24, 26, 29, 0, 11, 15, 20]) (cs := [11, 1, 1, 1, 2, 3, 0, 1, 4, 1, 1, 12, 0, 1, 1, 13, 1, 5, 1, 1, 14, 6, 7, 1, 8, 1, 9, 1, 1, 10]) (bs := [9, 4]) (W := 2624) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c21823_1 : P.sumLeaves 24 22346880 64 = 2624 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 349170) rows (by decide) (by decide)).symm.trans contract21823_1

theorem c21823_2 : P.sumLeaves 24 22346944 431 = 12534294 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21823) (lo := 192) (len := 431) (W := 12534294) check rows elimOK (by decide) (by decide) cover21823 (by decide)
  decide +kernel

theorem c21823_3 : P.sumLeaves 24 22347375 354 = 24982574 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21823) (lo := 623) (len := 354) (W := 24982574) check rows elimOK (by decide) (by decide) cover21823 (by decide)
  decide +kernel

theorem c21823_4 : P.sumLeaves 24 22347729 47 = 25559584 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21823) (lo := 977) (len := 47) (W := 25559584) check rows elimOK (by decide) (by decide) cover21823 (by decide)
  decide +kernel

theorem h21823 : P.leaf 34 21823 = 63079076 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(128, 0), (64, 2624), (431, 12534294), (354, 24982574), (47, 25559584)]) (.cons c21823_0 (.cons c21823_1 (.cons c21823_2 (.cons c21823_3 (.cons c21823_4 (.nil)))))) (by decide) (by decide))

theorem cover21836 : P.CoversSplit 24 10 21836 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem c21836_0 : P.sumLeaves 24 22360064 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21836) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover21836 (by decide)
  decide +kernel

theorem h21836 : P.leaf 34 21836 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c21836_0 (.nil)) (by decide) (by decide))

theorem cover21837 : P.CoversSplit 24 10 21837 0xc0000000c00000000000000000000000c0000000000000000000000000000000c0000000800000000000000000000000c0000000000000000000000000000000c0000000c00000000000000000000000c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 515, 516, 522, 572, 858, 865, 916, 1202, 1210, 1217, 1259]) (ps := [(11, [472], [858])]) (by decide +kernel)

theorem c21837_0 : P.sumLeaves 24 22361088 1024 = 187424 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21837) (lo := 0) (len := 1024) (W := 187424) check rows elimOK (by decide) (by decide) cover21837 (by decide)
  decide +kernel

theorem h21837 : P.leaf 34 21837 = 187424 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 187424)]) (.cons c21837_0 (.nil)) (by decide) (by decide))

theorem cover21839 : P.CoversSplit 24 10 21839 0xc0c00000c0c000000000000000000000c0c00000000000000000000000000000c0c00000800000000000000000000000c0c00000000000000000000000000000c0c00000c0c000000000000000000000c0c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [515, 516, 522, 572, 858, 1202, 1210, 1217, 1259, 1601, 1609]) (ps := [(8, [565], [1609])]) (by decide +kernel)

noncomputable def f21839 (i : ℕ) := rowWeight keep5 twice5 i * P.leaf 24 (22363136 + i)

theorem c21839_0 : rowSum f21839 0 1024 = 1155424 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 21839) (keep := keep5) (twice := twice5) check rows elimOK (by decide) (by decide) cover21839 (by decide)
  decide +kernel

theorem sum21839 : rowSum f21839 0 1024 = 1155424 :=
  c21839_0

theorem h21839 : P.leaf 34 21839 = 1155424 :=
  leaf_weighted (k := 24) (d := 10) (H := 21839) (keep := keep5) (twice := twice5) rows (by decide) (by decide) bal5 (invRow5 (H := 21839) (by decide) (by decide +kernel)) sum21839

theorem cover21852 : P.CoversSplit 24 10 21852 0x80000000c000800080000000c000800080000000000000008000000000000000800000008000800080000000800080008000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 466, 472, 473, 516, 858, 867, 1202, 1210, 1601]) (by decide +kernel)

theorem c21852_0 : P.sumLeaves 24 22376448 1024 = 732971 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21852) (lo := 0) (len := 1024) (W := 732971) check rows elimOK (by decide) (by decide) cover21852 (by decide)
  decide +kernel

theorem h21852 : P.leaf 34 21852 = 732971 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 732971)]) (.cons c21852_0 (.nil)) (by decide) (by decide))

theorem cover21853 : P.CoversSplit 24 10 21853 0xcc00cc00c0008000cc00cc00c0008000cc00000000000000cc00000000000000cc00cc0080008000cc00cc0080008000cc00000000000000cc00000000000000cc00cc00c0008000cc000000c0000000cc00440000000000cc000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 516, 572, 858, 909, 916, 1202, 1210, 1217, 1259, 1264, 1601]) (by decide +kernel)

theorem c21853_0 : P.sumLeaves 24 22377472 256 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21853) (lo := 0) (len := 256) (W := 0) check rows elimOK (by decide) (by decide) cover21853 (by decide)
  decide +kernel

theorem contract21853_1 : P.leaf 30 349652 = 0 := by
  exact leaf_contract_zero (ss := [(27, 1, 473), (29, 1, 473), (11, 1, 879), (30, 1, 1264), (31, 1, 1210), (8, 0, 1266), (5, 1, 565), (20, 1, 580), (21, 1, 586)]) (q := 1266) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c21853_1 : P.sumLeaves 24 22377728 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 349652) rows (by decide) (by decide)).symm.trans contract21853_1

theorem contract21853_2 : P.leaf 30 349653 = 0 := by
  exact leaf_contract_zero (ss := [(27, 1, 473), (29, 1, 473), (11, 1, 879), (8, 0, 1266), (31, 5, 565), (20, 1, 580), (21, 1, 586), (5, 1, 615)]) (q := 1266) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c21853_2 : P.sumLeaves 24 22377792 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 349653) rows (by decide) (by decide)).symm.trans contract21853_2

theorem c21853_3 : P.sumLeaves 24 22377856 640 = 9580338 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21853) (lo := 384) (len := 640) (W := 9580338) check rows elimOK (by decide) (by decide) cover21853 (by decide)
  decide +kernel

theorem h21853 : P.leaf 34 21853 = 9580338 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(256, 0), (64, 0), (64, 0), (640, 9580338)]) (.cons c21853_0 (.cons c21853_1 (.cons c21853_2 (.cons c21853_3 (.nil))))) (by decide) (by decide))

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

theorem contract21855_2 : P.leaf 30 349682 = 8512 := by
  exact leaf_contract_factors (k := 30) (b := 15) (H := 349682) (ss := [(3, 1, 536), (4, 1, 578), (11, 1, 921), (29, 1, 1259), (30, 1, 1264), (18, 1, 1266), (27, 1, 1601), (8, 0, 1609), (5, 1, 565), (14, 0, 1609), (7, 1, 629), (20, 1, 628), (21, 1, 629), (12, 1, 965), (15, 1, 972)]) (ids := [0, 4, 23, 8, 11, 14, 15, 17, 21, 22, 24, 26, 29, 7, 20]) (cs := [2, 1, 1, 1, 3, 1, 0, 15, 5, 1, 1, 6, 0, 1, 7, 8, 1, 9, 1, 1, 16, 10, 11, 4, 12, 1, 13, 1, 1, 14]) (bs := [3, 10, 2]) (W := 8512) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c21855_2 : P.sumLeaves 24 22379648 64 = 8512 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 349682) rows (by decide) (by decide)).symm.trans contract21855_2

theorem c21855_3 : P.sumLeaves 24 22379712 64 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21855) (lo := 192) (len := 64) (W := 0) check rows elimOK (by decide) (by decide) cover21855 (by decide)
  decide +kernel

theorem contract21855_4 : P.leaf 30 349684 = 0 := by
  exact leaf_contract_zero (ss := [(11, 1, 879), (30, 1, 1264), (31, 1, 1210), (8, 0, 1266), (5, 1, 565), (21, 0, 1266), (14, 1, 537), (10, 1, 874), (20, 1, 1272)]) (q := 1315) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c21855_4 : P.sumLeaves 24 22379776 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 349684) rows (by decide) (by decide)).symm.trans contract21855_4

theorem contract21855_5 : P.leaf 30 349685 = 0 := by
  exact leaf_contract_zero (ss := [(11, 1, 879), (8, 0, 1266), (5, 1, 565), (21, 0, 1266), (14, 1, 537), (10, 1, 874), (20, 1, 1272)]) (q := 1315) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c21855_5 : P.sumLeaves 24 22379840 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 349685) rows (by decide) (by decide)).symm.trans contract21855_5

theorem c21855_6 : P.sumLeaves 24 22379904 362 = 15961747 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21855) (lo := 384) (len := 362) (W := 15961747) check rows elimOK (by decide) (by decide) cover21855 (by decide)
  decide +kernel

theorem c21855_7 : P.sumLeaves 24 22380266 242 = 27544233 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21855) (lo := 746) (len := 242) (W := 27544233) check rows elimOK (by decide) (by decide) cover21855 (by decide)
  decide +kernel

theorem c21855_8 : P.sumLeaves 24 22380508 36 = 18714870 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21855) (lo := 988) (len := 36) (W := 18714870) check rows elimOK (by decide) (by decide) cover21855 (by decide)
  decide +kernel

theorem h21855 : P.leaf 34 21855 = 62229362 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(64, 0), (64, 0), (64, 8512), (64, 0), (64, 0), (64, 0), (362, 15961747), (242, 27544233), (36, 18714870)]) (.cons c21855_0 (.cons c21855_1 (.cons c21855_2 (.cons c21855_3 (.cons c21855_4 (.cons c21855_5 (.cons c21855_6 (.cons c21855_7 (.cons c21855_8 (.nil)))))))))) (by decide) (by decide))

theorem cover21860 : P.CoversSplit 24 10 21860 0xc0000000c00088000000000000000000c0000000000000000000000000000000c0c0000080808880c000000080008800c000000040000000c000000040000000c0000000c00088000000000000000000c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 515, 522, 572, 858, 860, 865, 916, 1210, 1601]) (ps := [(2, [468], [473])]) (by decide +kernel)

theorem c21860_0 : P.sumLeaves 24 22384640 448 = 1000 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21860) (lo := 0) (len := 448) (W := 1000) check rows elimOK (by decide) (by decide) cover21860 (by decide)
  decide +kernel

theorem contract21860_1 : P.leaf 30 349767 = 6020 := by
  exact leaf_contract_factors (k := 30) (b := 17) (H := 349767) (ss := [(27, 1, 473), (29, 1, 473), (2, 1, 475), (6, 1, 480), (14, 0, 867), (10, 1, 811), (12, 1, 461), (11, 1, 459), (4, 1, 410), (18, 1, 879), (15, 1, 909), (21, 1, 923), (20, 1, 929)]) (ids := [1, 3, 5, 6, 7, 11, 14, 15, 17, 20, 22, 24, 26, 28, 29, 21, 23]) (cs := [1, 2, 1, 3, 1, 4, 5, 6, 1, 1, 1, 7, 0, 1, 8, 9, 1, 10, 1, 1, 11, 17, 12, 18, 13, 1, 14, 1, 15, 16]) (bs := [15, 2]) (W := 6020) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c21860_1 : P.sumLeaves 24 22385088 64 = 6020 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 349767) rows (by decide) (by decide)).symm.trans contract21860_1

theorem c21860_2 : P.sumLeaves 24 22385152 128 = 12552 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21860) (lo := 512) (len := 128) (W := 12552) check rows elimOK (by decide) (by decide) cover21860 (by decide)
  decide +kernel

theorem contract21860_3 : P.leaf 30 349770 = 4600 := by
  exact leaf_contract_factors (k := 30) (b := 19) (H := 349770) (ss := [(19, 1, 578), (10, 1, 865), (29, 1, 865), (14, 1, 867), (18, 1, 879), (15, 1, 909), (27, 1, 1601), (3, 0, 522), (5, 1, 417), (2, 1, 410), (4, 1, 410)]) (ids := [4, 5, 6, 7, 9, 10, 11, 14, 15, 18, 19, 21, 22, 23, 24, 26, 28, 29, 20]) (cs := [1, 0, 1, 1, 2, 3, 4, 5, 1, 6, 7, 8, 1, 1, 9, 10, 1, 1, 11, 12, 20, 13, 14, 15, 16, 1, 17, 1, 18, 19]) (bs := [18, 1]) (W := 4600) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c21860_3 : P.sumLeaves 24 22385280 64 = 4600 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 349770) rows (by decide) (by decide)).symm.trans contract21860_3

theorem c21860_4 : P.sumLeaves 24 22385344 320 = 75320 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21860) (lo := 704) (len := 320) (W := 75320) check rows elimOK (by decide) (by decide) cover21860 (by decide)
  decide +kernel

theorem h21860 : P.leaf 34 21860 = 99492 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(448, 1000), (64, 6020), (128, 12552), (64, 4600), (320, 75320)]) (.cons c21860_0 (.cons c21860_1 (.cons c21860_2 (.cons c21860_3 (.cons c21860_4 (.nil)))))) (by decide) (by decide))

theorem cover21861 : P.CoversSplit 24 10 21861 0xc0000000c00000000000000000000000c0000000000000000000000000000000c0000000800000000000000000000000c0000000400000000000000000000000c0000000c00000000000000000000000c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 515, 522, 572, 858, 860, 865, 916, 1210, 1601]) (ps := [(4, [515], [466])]) (by decide +kernel)

theorem c21861_0 : P.sumLeaves 24 22385664 1024 = 483368 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21861) (lo := 0) (len := 1024) (W := 483368) check rows elimOK (by decide) (by decide) cover21861 (by decide)
  decide +kernel

theorem h21861 : P.leaf 34 21861 = 483368 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 483368)]) (.cons c21861_0 (.nil)) (by decide) (by decide))

theorem cover21862 : P.CoversSplit 24 10 21862 0xc0c00000c0c000000000000000000000c0c00000000000000000000000000000c0c00000808000000000000000000000c0c00000404000000000000000000000c0c00000c0c000000000000000000000c0c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 515, 522, 572, 858, 860, 865, 916, 1202, 1210, 1259, 1601]) (ps := [(10, [865], [466])]) (by decide +kernel)

theorem c21862_0 : P.sumLeaves 24 22386688 320 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21862) (lo := 0) (len := 320) (W := 0) check rows elimOK (by decide) (by decide) cover21862 (by decide)
  decide +kernel

theorem contract21862_1 : P.leaf 30 349797 = 10968 := by
  exact leaf_contract_factors (k := 30) (b := 19) (H := 349797) (ss := [(10, 1, 466), (27, 1, 522), (14, 0, 867), (21, 1, 874), (18, 1, 879), (15, 1, 909), (12, 1, 965), (6, 1, 458), (20, 1, 880), (13, 1, 971), (19, 1, 1658)]) (ids := [0, 1, 2, 3, 5, 6, 7, 9, 14, 15, 20, 22, 24, 26, 27, 28, 29, 21, 23]) (cs := [2, 3, 4, 5, 1, 6, 7, 8, 1, 9, 1, 1, 0, 1, 10, 11, 1, 1, 1, 1, 12, 19, 13, 20, 14, 1, 15, 16, 17, 18]) (bs := [17, 2]) (W := 10968) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c21862_1 : P.sumLeaves 24 22387008 64 = 10968 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 349797) rows (by decide) (by decide)).symm.trans contract21862_1

theorem c21862_2 : P.sumLeaves 24 22387072 640 = 1309680 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21862) (lo := 384) (len := 640) (W := 1309680) check rows elimOK (by decide) (by decide) cover21862 (by decide)
  decide +kernel

theorem h21862 : P.leaf 34 21862 = 1320648 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(320, 0), (64, 10968), (640, 1309680)]) (.cons c21862_0 (.cons c21862_1 (.cons c21862_2 (.nil)))) (by decide) (by decide))

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

theorem c21868_0 : P.sumLeaves 24 22392832 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21868) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover21868 (by decide)
  decide +kernel

theorem h21868 : P.leaf 34 21868 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c21868_0 (.nil)) (by decide) (by decide))

theorem cover21869 : P.CoversSplit 24 10 21869 0xc0000000c00088000000000000000000c0000000000000000000000000000000c0000000800088000000000000000000c0000000400000000000000000000000c0000000c00088000000000000000000c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 515, 522, 572, 858, 860, 865, 916, 1210, 1601]) (by decide +kernel)

theorem c21869_0 : P.sumLeaves 24 22393856 1024 = 1656318 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21869) (lo := 0) (len := 1024) (W := 1656318) check rows elimOK (by decide) (by decide) cover21869 (by decide)
  decide +kernel

theorem h21869 : P.leaf 34 21869 = 1656318 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1656318)]) (.cons c21869_0 (.nil)) (by decide) (by decide))

theorem cover21870 : P.CoversSplit 24 10 21870 0xc0c00000c0c000000000000000000000c0c00000000000000000000000000000c0c0000080800000c000000080000000c0c0000040400000c000000040000000c0c00000c0c000000000000000000000c0c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 515, 522, 572, 858, 860, 865, 916, 1202, 1210, 1259, 1601]) (by decide +kernel)

theorem c21870_0 : P.sumLeaves 24 22394880 1024 = 2575264 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21870) (lo := 0) (len := 1024) (W := 2575264) check rows elimOK (by decide) (by decide) cover21870 (by decide)
  decide +kernel

theorem h21870 : P.leaf 34 21870 = 2575264 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 2575264)]) (.cons c21870_0 (.nil)) (by decide) (by decide))

theorem cover21871 : P.CoversSplit 24 10 21871 0xc0c00000c0c000000000000000000000c0c00000000000000000000000000000c0c00000808000000000000000000000c0c00000404000000000000000000000c0c00000c0c000000000000000000000c0c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 522, 572, 858, 860, 916, 1202, 1210, 1259, 1601]) (by decide +kernel)

theorem c21871_0 : P.sumLeaves 24 22395904 1024 = 7712560 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21871) (lo := 0) (len := 1024) (W := 7712560) check rows elimOK (by decide) (by decide) cover21871 (by decide)
  decide +kernel

theorem h21871 : P.leaf 34 21871 = 7712560 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 7712560)]) (.cons c21871_0 (.nil)) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(21807, 48), (21813, 48), (21814, 24), (21815, 48), (21820, 48), (21821, 48), (21822, 48), (21823, 48), (21836, 24), (21837, 48), (21839, 24), (21852, 48), (21853, 48), (21854, 48), (21855, 48), (21860, 24), (21861, 48), (21862, 24), (21863, 48), (21868, 48), (21869, 48), (21870, 48), (21871, 48)]

theorem segOK : checkSeg 16 perms 21807 21877 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 21807 21877 984 10627676640 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 10627676640)
    (SegSum.cons (w := 48) h21807 (SegSum.cons (w := 48) h21813 (SegSum.cons (w := 24) h21814 (SegSum.cons (w := 48) h21815 (SegSum.cons (w := 48) h21820 (SegSum.cons (w := 48) h21821 (SegSum.cons (w := 48) h21822 (SegSum.cons (w := 48) h21823 (SegSum.cons (w := 24) h21836 (SegSum.cons (w := 48) h21837 (SegSum.cons (w := 24) h21839 (SegSum.cons (w := 48) h21852 (SegSum.cons (w := 48) h21853 (SegSum.cons (w := 48) h21854 (SegSum.cons (w := 48) h21855 (SegSum.cons (w := 24) h21860 (SegSum.cons (w := 48) h21861 (SegSum.cons (w := 24) h21862 (SegSum.cons (w := 48) h21863 (SegSum.cons (w := 48) h21868 (SegSum.cons (w := 48) h21869 (SegSum.cons (w := 48) h21870 (SegSum.cons (w := 48) h21871 (show SegSum (P.leaf 34) [] 0 from rfl)))))))))))))))))))))))) (by decide)

end RACert.S4N1.C0.S70
