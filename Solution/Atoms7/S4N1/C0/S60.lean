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

namespace RACert.S4N1.C0.S60

open RACert RACert.Problem

theorem cover21735 : P.CoversSplit 24 10 21735 0xf0f00000f0f00000f0f00000f0f00000f0f0000000000000f0f00000000000000000000000000000000000000000000000000000000000000000000000000000c0000000c00000000000000000000000c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [466, 515, 522, 573, 858, 860, 916, 1202, 1210, 1259, 1601]) (ps := [(15, [909], [916])]) (by decide +kernel)

theorem c21735_0 : P.sumLeaves 24 22256640 1024 = 2962711 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21735) (lo := 0) (len := 1024) (W := 2962711) check rows elimOK (by decide) (by decide) cover21735 (by decide)
  decide +kernel

theorem h21735 : P.leaf 34 21735 = 2962711 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 2962711)]) (.cons c21735_0 (.nil)) (by decide) (by decide))

theorem cover21736 : P.CoversSplit 24 10 21736 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [472]) (by decide +kernel)

theorem h21736 : P.leaf 34 21736 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 21736) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 21736) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover21736 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover54616 : P.CoversSplit 24 10 54616 0x8000800080008000800080008000800080008000800080008000800080008000800080008000800080008000800080008000800000000000800080000000000080008000800080008000800080008000800080008000800080008000800080008000800000000000800080000000000080008000800080008000800080008000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 466, 472, 473, 516, 572]) (ps := [(12, [860, 916], [860, 916])]) (by decide +kernel)

noncomputable def f54616 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (55926784 + i)

theorem c54616_0 : rowSum f54616 0 1024 = 489506 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 54616) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover54616 (by decide)
  decide +kernel

theorem sum54616 : rowSum f54616 0 1024 = 489506 :=
  c54616_0

theorem h54616 : P.leaf 34 54616 = 489506 :=
  leaf_weighted (k := 24) (d := 10) (H := 54616) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 54616) (by decide) (by decide +kernel)) sum54616

theorem h21737 : P.leaf 34 21737 = 489506 :=
  orient25 (v := 54616) (by decide) (by decide +kernel) h54616

theorem cover22748 : P.CoversSplit 24 10 22748 0xf000f00000000000f000f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 466, 472, 516, 536, 573, 879, 1202, 1259, 1601]) (ps := [(17, [479], [1259]), (18, [487], [1210])]) (by decide +kernel)

theorem h22748 : P.leaf 34 22748 = 704276 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 22748) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 22748) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 22748) (weight := rowWeight keep1 twice1) (xs := [383, 940, 941, 942, 943, 956, 957, 958, 959, 1004, 1005, 1006, 1007, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover22748 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h21738 : P.leaf 34 21738 = 704276 :=
  orient4 (v := 22748) (by decide) (by decide +kernel) h22748

theorem cover21739 : P.CoversSplit 24 10 21739 0xf0f00000f0f00000f0f00000f0f00000f0f0000000000000f0f00000000000000000000000000000000000000000000000000000000000000000000000000000c0000000c00000000000000000000000c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [472, 515, 522, 573, 858, 860, 916, 1202, 1210, 1259, 1601]) (ps := [(15, [909], [916])]) (by decide +kernel)

theorem c21739_0 : P.sumLeaves 24 22260736 1024 = 2899074 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21739) (lo := 0) (len := 1024) (W := 2899074) check rows elimOK (by decide) (by decide) cover21739 (by decide)
  decide +kernel

theorem h21739 : P.leaf 34 21739 = 2899074 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 2899074)]) (.cons c21739_0 (.nil)) (by decide) (by decide))

theorem cover21740 : P.CoversSplit 24 10 21740 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [508]) (by decide +kernel)

theorem h21740 : P.leaf 34 21740 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 21740) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 21740) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover21740 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover21741 : P.CoversSplit 24 10 21741 0xf0f00000e0ea0000f0f00000e0ea0000f0f000000000aaaaf0f000000000aa880000000000000000000000000000000000000000000000000000000000000000c0000000c00000000000000000000000c00000000000880000300000000000200000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 515, 522, 573, 858, 860, 865, 916, 1210, 1259, 1601]) (ps := [(8, [1217], [573]), (17, [1259], [1251])]) (by decide +kernel)

theorem c21741_0 : P.sumLeaves 24 22262784 1024 = 1686540 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21741) (lo := 0) (len := 1024) (W := 1686540) check rows elimOK (by decide) (by decide) cover21741 (by decide)
  decide +kernel

theorem h21741 : P.leaf 34 21741 = 1686540 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1686540)]) (.cons c21741_0 (.nil)) (by decide) (by decide))

theorem cover22780 : P.CoversSplit 24 10 22780 0xf0f0f0f0a0a00000f0f0f0f0a0a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c000c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 466, 473, 573, 859, 865, 879, 916, 1202, 1210, 1259, 1601]) (ps := [(17, [908], [1259])]) (by decide +kernel)

theorem c22780_0 : P.sumLeaves 24 23326720 1024 = 3013200 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22780) (lo := 0) (len := 1024) (W := 3013200) check rows elimOK (by decide) (by decide) cover22780 (by decide)
  decide +kernel

theorem h22780 : P.leaf 34 22780 = 3013200 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 3013200)]) (.cons c22780_0 (.nil)) (by decide) (by decide))

theorem h21742 : P.leaf 34 21742 = 3013200 :=
  orient4 (v := 22780) (by decide) (by decide +kernel) h22780

theorem cover21743 : P.CoversSplit 24 10 21743 0xf0f00000f0f00000f0f00000f0f00000f0f0000000000000f0f00000000000000000000000000000000000000000000000000000000000000000000000000000c0000000c00000000000000000000000c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [515, 522, 573, 858, 860, 916, 1202, 1210, 1259, 1601]) (ps := [(15, [909], [916])]) (by decide +kernel)

theorem c21743_0 : P.sumLeaves 24 22264832 1024 = 5594138 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21743) (lo := 0) (len := 1024) (W := 5594138) check rows elimOK (by decide) (by decide) cover21743 (by decide)
  decide +kernel

theorem h21743 : P.leaf 34 21743 = 5594138 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 5594138)]) (.cons c21743_0 (.nil)) (by decide) (by decide))

theorem cover27047 : P.CoversSplit 24 10 27047 0xaa000000a00000000000000000000000aa000000000000000000000000000000aa000000800000000000000000000000aa000000000000000000000000000000aa000000a00000000000000000000000aa0000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [466, 515, 517, 522, 858, 859, 865, 915, 1210, 1259, 1601]) (by decide +kernel)

theorem h27047 : P.leaf 34 27047 = 2574462 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 27047) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 27047) (weight := fun _ => 1) (xs := [221, 377, 379, 381, 383, 477, 479, 505, 507, 509, 511, 633, 635, 637, 639, 735, 761, 763, 765, 767, 889, 891, 893, 895, 989, 991, 1017, 1019, 1021, 1023]) check rows elimOK (by decide) (by decide) cover27047 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h21750 : P.leaf 34 21750 = 2574462 :=
  orient24 (v := 27047) (by decide) (by decide +kernel) h27047

theorem cover22719 : P.CoversSplit 24 10 22719 0xffffffffaaaa0000ffffffffaaaa0000ffffffff00000000ffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [517, 573, 865, 879, 1202, 1210, 1217, 1251, 1259, 1601]) (by decide +kernel)

theorem c22719_0 : P.sumLeaves 24 23264256 992 = 19029730 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22719) (lo := 0) (len := 992) (W := 19029730) check rows elimOK (by decide) (by decide) cover22719 (by decide)
  decide +kernel

theorem c22719_1 : P.sumLeaves 24 23265248 32 = 14767752 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22719) (lo := 992) (len := 32) (W := 14767752) check rows elimOK (by decide) (by decide) cover22719 (by decide)
  decide +kernel

theorem h22719 : P.leaf 34 22719 = 33797482 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(992, 19029730), (32, 14767752)]) (.cons c22719_0 (.cons c22719_1 (.nil))) (by decide) (by decide))

theorem h21751 : P.leaf 34 21751 = 33797482 :=
  orient4 (v := 22719) (by decide) (by decide +kernel) h22719

theorem cover22735 : P.CoversSplit 24 10 22735 0xffffffff00000000ffffffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000800084000000000080208000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [515, 516, 522, 536, 573, 858, 859, 865, 916, 1202, 1259, 1601]) (ps := [(7, [523], [516]), (9, [566], [573])]) (by decide +kernel)

noncomputable def f22735 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (23280640 + i)

theorem c22735_0 : rowSum f22735 0 1024 = 3808700 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 22735) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover22735 (by decide)
  decide +kernel

theorem sum22735 : rowSum f22735 0 1024 = 3808700 :=
  c22735_0

theorem h22735 : P.leaf 34 22735 = 3808700 :=
  leaf_weighted (k := 24) (d := 10) (H := 22735) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 22735) (by decide) (by decide +kernel)) sum22735

theorem h21753 : P.leaf 34 21753 = 3808700 :=
  orient4 (v := 22735) (by decide) (by decide +kernel) h22735

theorem cover22751 : P.CoversSplit 24 10 22751 0xffffffff00000000ffffffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [516, 536, 573, 858, 859, 865, 879, 916, 1202, 1259, 1601]) (ps := [(17, [528, 908], [1259]), (18, [867], [1210])]) (by decide +kernel)

noncomputable def f22751 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (23297024 + i)

theorem c22751_0 : rowSum f22751 0 1024 = 14295386 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 22751) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover22751 (by decide)
  decide +kernel

theorem sum22751 : rowSum f22751 0 1024 = 14295386 :=
  c22751_0

theorem h22751 : P.leaf 34 22751 = 14295386 :=
  leaf_weighted (k := 24) (d := 10) (H := 22751) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 22751) (by decide) (by decide +kernel)) sum22751

theorem h21755 : P.leaf 34 21755 = 14295386 :=
  orient4 (v := 22751) (by decide) (by decide +kernel) h22751

theorem cover21756 : P.CoversSplit 24 10 21756 0xf0f00000f0f00000f0f00000f0f00000f000000050000000f000000050000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 508, 573, 858, 860, 865, 867, 909, 1202, 1210, 1601]) (by decide +kernel)

theorem c21756_0 : P.sumLeaves 24 22278144 1024 = 4308730 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21756) (lo := 0) (len := 1024) (W := 4308730) check rows elimOK (by decide) (by decide) cover21756 (by decide)
  decide +kernel

theorem h21756 : P.leaf 34 21756 = 4308730 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 4308730)]) (.cons c21756_0 (.nil)) (by decide) (by decide))

theorem cover22767 : P.CoversSplit 24 10 22767 0xffffffffaaaa0000ffffffffaaaa0000ffff00000000aaaaffff000000008888000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [515, 522, 573, 858, 865, 879, 1202, 1210, 1259, 1601]) (ps := [(17, [1259], [1251])]) (by decide +kernel)

theorem c22767_0 : P.sumLeaves 24 23313408 996 = 9475227 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22767) (lo := 0) (len := 996) (W := 9475227) check rows elimOK (by decide) (by decide) cover22767 (by decide)
  decide +kernel

theorem c22767_1 : P.sumLeaves 24 23314404 28 = 9764040 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22767) (lo := 996) (len := 28) (W := 9764040) check rows elimOK (by decide) (by decide) cover22767 (by decide)
  decide +kernel

theorem h22767 : P.leaf 34 22767 = 19239267 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(996, 9475227), (28, 9764040)]) (.cons c22767_0 (.cons c22767_1 (.nil))) (by decide) (by decide))

theorem h21757 : P.leaf 34 21757 = 19239267 :=
  orient4 (v := 22767) (by decide) (by decide +kernel) h22767

theorem cover21758 : P.CoversSplit 24 10 21758 0xf0f00000f0f00000f0f00000f0f00000f0f0000050500000f0f0000050500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 573, 858, 860, 865, 867, 916, 1202, 1210, 1601]) (by decide +kernel)

theorem c21758_0 : P.sumLeaves 24 22280192 1024 = 14561436 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21758) (lo := 0) (len := 1024) (W := 14561436) check rows elimOK (by decide) (by decide) cover21758 (by decide)
  decide +kernel

theorem h21758 : P.leaf 34 21758 = 14561436 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 14561436)]) (.cons c21758_0 (.nil)) (by decide) (by decide))

theorem cover22783 : P.CoversSplit 24 10 22783 0xffffffffaaaa0000ffffffffaaaa0000ffffffffaaaa0000ffffffffaaaa0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [573, 858, 865, 879, 1202, 1210, 1259, 1601]) (by decide +kernel)

theorem c22783_0 : P.sumLeaves 24 23329792 936 = 29696100 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22783) (lo := 0) (len := 936) (W := 29696100) check rows elimOK (by decide) (by decide) cover22783 (by decide)
  decide +kernel

theorem c22783_1 : P.sumLeaves 24 23330728 88 = 46778421 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22783) (lo := 936) (len := 88) (W := 46778421) check rows elimOK (by decide) (by decide) cover22783 (by decide)
  decide +kernel

theorem h22783 : P.leaf 34 22783 = 76474521 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(936, 29696100), (88, 46778421)]) (.cons c22783_0 (.cons c22783_1 (.nil))) (by decide) (by decide))

theorem h21759 : P.leaf 34 21759 = 76474521 :=
  orient4 (v := 22783) (by decide) (by decide +kernel) h22783

theorem cover21796 : P.CoversSplit 24 10 21796 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [508]) (by decide +kernel)

theorem h21796 : P.leaf 34 21796 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 21796) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 21796) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover21796 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover25897 : P.CoversSplit 24 10 25897 0x8000000080000000000000000000000080000000000004000000000000000000800000008000000000000000000000008000000000000400000000000000000080000000800000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 515, 517, 522, 529, 572, 858, 860, 865, 872, 1202]) (by decide +kernel)

theorem h25897 : P.leaf 34 25897 = 89207 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 25897) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 25897) (weight := fun _ => 1) (xs := [383, 479, 511, 586, 639, 735, 767, 842, 895, 991, 1023]) check rows elimOK (by decide) (by decide) cover25897 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h21797 : P.leaf 34 21797 = 89207 :=
  orient5 (v := 25897) (by decide) (by decide +kernel) h25897

theorem cover39209 : P.CoversSplit 24 10 39209 0xc0000000c0000000000000000000000000000000000000000000000000000000c0000000c0000000000000000000000000000000000000000000000000000000c0000000c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [466, 473, 515, 522, 529, 572, 858, 865, 1258]) (by decide +kernel)

theorem h39209 : P.leaf 34 39209 = 62016 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 39209) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 39209) (weight := fun _ => 1) (xs := [478, 479, 510, 511, 734, 735, 766, 767, 990, 991, 1022, 1023]) check rows elimOK (by decide) (by decide) cover39209 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h21798 : P.leaf 34 21798 = 62016 :=
  orient25 (v := 39209) (by decide) (by decide +kernel) h39209

theorem cover21799 : P.CoversSplit 24 10 21799 0x8080000080800000000000000000000080800000000004040000000000000000808000008080000000000000000000008080000000000404000000000000000080800000808000000000000000000000808000000000040400000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 517, 522, 529, 572, 858, 860, 1259, 1601]) (by decide +kernel)

theorem h21799 : P.leaf 34 21799 = 1082042 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 21799) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 21799) (weight := fun _ => 1) (xs := [322, 330, 375, 383, 471, 479, 503, 511, 578, 586, 631, 639, 727, 735, 759, 767, 834, 842, 887, 895, 983, 991, 1015, 1023]) check rows elimOK (by decide) (by decide) cover21799 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover21804 : P.CoversSplit 24 10 21804 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem h21804 : P.leaf 34 21804 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 21804) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 21804) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover21804 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover21805 : P.CoversSplit 24 10 21805 0x8000000080000000000000000000000080000000000004000000000000000000800000008000000000000000000000008000000000000400000000000000000080000000800000000000000000000000800000000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 515, 517, 522, 529, 572, 858, 860, 865, 916, 1202, 1601]) (by decide +kernel)

theorem h21805 : P.leaf 34 21805 = 304976 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 21805) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 21805) (weight := fun _ => 1) (xs := [330, 383, 479, 511, 586, 639, 735, 767, 842, 895, 991, 1023]) check rows elimOK (by decide) (by decide) cover21805 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover21806 : P.CoversSplit 24 10 21806 0x8080000080800000000000000000000080800000000000000000000000000000808000008080000000000000000000008080000000000000000000000000000080800000808000000000000000000000808000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 515, 517, 522, 529, 572, 858, 860, 865, 1259, 1601]) (ps := [(3, [508], [522])]) (by decide +kernel)

theorem h21806 : P.leaf 34 21806 = 265228 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 21806) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 21806) (weight := fun _ => 1) (xs := [375, 383, 471, 479, 503, 511, 631, 639, 727, 735, 759, 767, 887, 895, 983, 991, 1015, 1023]) check rows elimOK (by decide) (by decide) cover21806 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover21807 : P.CoversSplit 24 10 21807 0x8080000080800000000000000000000080800000000004040000000000000000808000008080000000000000000000008080000000000404000000000000000080800000808000000000000000000000808000000000040400000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 517, 522, 529, 572, 858, 860, 1259, 1601]) (by decide +kernel)

theorem h21807 : P.leaf 34 21807 = 1797293 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 21807) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 21807) (weight := fun _ => 1) (xs := [322, 330, 375, 383, 471, 479, 503, 511, 578, 586, 631, 639, 727, 735, 759, 767, 834, 842, 887, 895, 983, 991, 1015, 1023]) check rows elimOK (by decide) (by decide) cover21807 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover22823 : P.CoversSplit 24 10 22823 0x8888000088880000000000000000000088880000000000000000000000000000888800008888000000000000000000008888000000000000000000000000000088880000888800000000000000000000888800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [466, 515, 517, 522, 572, 858, 859, 1210, 1259, 1601]) (by decide +kernel)

theorem c22823_0 : P.sumLeaves 24 23370752 1024 = 3157048 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22823) (lo := 0) (len := 1024) (W := 3157048) check rows elimOK (by decide) (by decide) cover22823 (by decide)
  decide +kernel

theorem h22823 : P.leaf 34 22823 = 3157048 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 3157048)]) (.cons c22823_0 (.nil)) (by decide) (by decide))

theorem h21813 : P.leaf 34 21813 = 3157048 :=
  orient4 (v := 22823) (by decide) (by decide +kernel) h22823

theorem cover26795 : P.CoversSplit 24 10 26795 0xaa000000aa0000000000000000000000aa000000000000000000000000000000aa000000800000000000000000000000aa000000000000000000000000000000aa000000aa0000000000000000000000aa0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [515, 517, 522, 573, 865, 1202, 1210, 1217, 1259, 1601, 1609]) (ps := [(8, [524], [1217])]) (by decide +kernel)

noncomputable def f26795 (i : ℕ) := rowWeight keep5 twice5 i * P.leaf 24 (27438080 + i)

theorem c26795_0 : rowSum f26795 0 1024 = 877712 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 26795) (keep := keep5) (twice := twice5) check rows elimOK (by decide) (by decide) cover26795 (by decide)
  decide +kernel

theorem sum26795 : rowSum f26795 0 1024 = 877712 :=
  c26795_0

theorem h26795 : P.leaf 34 26795 = 877712 :=
  leaf_weighted (k := 24) (d := 10) (H := 26795) (keep := keep5) (twice := twice5) rows (by decide) (by decide) (bal5) (invRow5 (H := 26795) (by decide) (by decide +kernel)) sum26795

theorem h21814 : P.leaf 34 21814 = 877712 :=
  orient24 (v := 26795) (by decide) (by decide +kernel) h26795

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

theorem h21820 : P.leaf 34 21820 = 1442576 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 21820) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 21820) (weight := fun _ => 1) (xs := [574, 575, 638, 639, 671, 702, 703, 735, 766, 767, 830, 831, 894, 895, 926, 927, 958, 959, 990, 991, 1022, 1023]) check rows elimOK (by decide) (by decide) cover21820 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover21821 : P.CoversSplit 24 10 21821 0xcc00cc00c8000000cc00cc00c8000000c400c40000000000c400000000000000cc00cc0088000000cc00cc0088000000c400c40000000000c400000000000000cc00cc00c8000000cc000000c8000000c400c40040000000c4000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 517, 529, 572, 858, 860, 909, 916, 1202, 1210, 1217, 1251, 1264, 1308, 1601]) (by decide +kernel)

theorem c21821_0 : P.sumLeaves 24 22344704 1024 = 11160970 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21821) (lo := 0) (len := 1024) (W := 11160970) check rows elimOK (by decide) (by decide) cover21821 (by decide)
  decide +kernel

theorem h21821 : P.leaf 34 21821 = 11160970 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 11160970)]) (.cons c21821_0 (.nil)) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(21735, 48), (21736, 12), (21737, 24), (21738, 24), (21739, 48), (21740, 48), (21741, 48), (21742, 48), (21743, 48), (21750, 48), (21751, 48), (21753, 12), (21755, 24), (21756, 48), (21757, 48), (21758, 48), (21759, 48), (21796, 24), (21797, 48), (21798, 48), (21799, 48), (21804, 48), (21805, 48), (21806, 48), (21807, 48), (21813, 48), (21814, 24), (21815, 48), (21820, 48), (21821, 48)]

theorem segOK : checkSeg 16 perms 21735 21822 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 21735 21822 1248 11238804624 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 11238804624)
    (SegSum.cons (w := 48) h21735 (SegSum.cons (w := 12) h21736 (SegSum.cons (w := 24) h21737 (SegSum.cons (w := 24) h21738 (SegSum.cons (w := 48) h21739 (SegSum.cons (w := 48) h21740 (SegSum.cons (w := 48) h21741 (SegSum.cons (w := 48) h21742 (SegSum.cons (w := 48) h21743 (SegSum.cons (w := 48) h21750 (SegSum.cons (w := 48) h21751 (SegSum.cons (w := 12) h21753 (SegSum.cons (w := 24) h21755 (SegSum.cons (w := 48) h21756 (SegSum.cons (w := 48) h21757 (SegSum.cons (w := 48) h21758 (SegSum.cons (w := 48) h21759 (SegSum.cons (w := 24) h21796 (SegSum.cons (w := 48) h21797 (SegSum.cons (w := 48) h21798 (SegSum.cons (w := 48) h21799 (SegSum.cons (w := 48) h21804 (SegSum.cons (w := 48) h21805 (SegSum.cons (w := 48) h21806 (SegSum.cons (w := 48) h21807 (SegSum.cons (w := 48) h21813 (SegSum.cons (w := 24) h21814 (SegSum.cons (w := 48) h21815 (SegSum.cons (w := 48) h21820 (SegSum.cons (w := 48) h21821 (show SegSum (P.leaf 34) [] 0 from rfl))))))))))))))))))))))))))))))) (by decide)

end RACert.S4N1.C0.S60
