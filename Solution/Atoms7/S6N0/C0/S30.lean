/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Atoms7.S6N0.C0.Defs

/-! Generated certificate for the identity on six symmetric diversity atoms. -/

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option Elab.async false

@[expose] public section

namespace RACert.S6N0.C0.S30

open RACert RACert.Problem

theorem cover14332 : P.CoversSplit 26 10 14332 0xfffffffaffffc8c8fffffafaffffc8c8fffcfff8ffccc8c8aa88aa88aa888888000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [873, 874, 923, 972, 979, 1265, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c14332_0 : P.sumLeaves 26 14675968 939 = 10894053 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14332) (lo := 0) (len := 939) (W := 10894053) check rows elimOK (by decide) (by decide) cover14332 (by decide)
  decide +kernel

theorem c14332_1 : P.sumLeaves 26 14676907 85 = 17530940 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14332) (lo := 939) (len := 85) (W := 17530940) check rows elimOK (by decide) (by decide) cover14332 (by decide)
  decide +kernel

theorem h14332 : P.leaf 36 14332 = 28424993 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(939, 10894053), (85, 17530940)]) (.cons c14332_0 (.cons c14332_1 (.nil))) (by decide) (by decide))

theorem cover14333 : P.CoversSplit 26 10 14333 0xfffffffaffffc8c8fffffafaffffc8c8fffcfff8ffccc8c8aa88aa88aa8888880000000000000000000000000000000000000000000000000000000000000000fffffffaccccc8c8fffffafaccccc8c8ffccffc8cc00c800aa88aa88880088000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [873, 923, 930, 972, 979, 1265, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c14333_0 : P.sumLeaves 26 14676992 470 = 34017468 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14333) (lo := 0) (len := 470) (W := 34017468) check rows elimOK (by decide) (by decide) cover14333 (by decide)
  decide +kernel

theorem c14333_1 : P.sumLeaves 26 14677462 419 = 50645456 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14333) (lo := 470) (len := 419) (W := 50645456) check rows elimOK (by decide) (by decide) cover14333 (by decide)
  decide +kernel

theorem c14333_2 : P.sumLeaves 26 14677881 122 = 74540192 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14333) (lo := 889) (len := 122) (W := 74540192) check rows elimOK (by decide) (by decide) cover14333 (by decide)
  decide +kernel

theorem c14333_3 : P.sumLeaves 26 14678003 13 = 23231292 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14333) (lo := 1011) (len := 13) (W := 23231292) check rows elimOK (by decide) (by decide) cover14333 (by decide)
  decide +kernel

theorem h14333 : P.leaf 36 14333 = 182434408 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(470, 34017468), (419, 50645456), (122, 74540192), (13, 23231292)]) (.cons c14333_0 (.cons c14333_1 (.cons c14333_2 (.cons c14333_3 (.nil))))) (by decide) (by decide))

theorem cover14335 : P.CoversSplit 26 10 14335 0xfffffffaffffc8c8fffffafaffffc8c8fffcfff8ffccc8c8aa88aa88aa888888fffffafaffffc8c8aaaaaaaaaaaa8888fffcfaf8ffccc8c8aa88aa88aa888888fffffffaccccc8c8fffffafaccccc8c8ffccffc8ccccc8c8aa88aa8888888888fffffafaccccc8c8aaaaaaaa88888888ffccfac8ccccc8c8aa88aa8888888888 :=
  coversSplit check rows (by decide) (by decide) (xs := [873, 930, 972, 979, 1265, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c14335_0 : P.sumLeaves 26 14679040 229 = 8837504 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14335) (lo := 0) (len := 229) (W := 8837504) check rows elimOK (by decide) (by decide) cover14335 (by decide)
  decide +kernel

theorem c14335_1 : P.sumLeaves 26 14679269 188 = 153470763 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14335) (lo := 229) (len := 188) (W := 153470763) check rows elimOK (by decide) (by decide) cover14335 (by decide)
  decide +kernel

theorem c14335_2 : P.sumLeaves 26 14679457 166 = 292080421 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14335) (lo := 417) (len := 166) (W := 292080421) check rows elimOK (by decide) (by decide) cover14335 (by decide)
  decide +kernel

theorem c14335_3 : P.sumLeaves 26 14679623 160 = 263919888 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14335) (lo := 583) (len := 160) (W := 263919888) check rows elimOK (by decide) (by decide) cover14335 (by decide)
  decide +kernel

theorem c14335_4 : P.sumLeaves 26 14679783 169 = 275760706 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14335) (lo := 743) (len := 169) (W := 275760706) check rows elimOK (by decide) (by decide) cover14335 (by decide)
  decide +kernel

theorem c14335_5 : P.sumLeaves 26 14679952 112 = 506250904 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14335) (lo := 912) (len := 112) (W := 506250904) check rows elimOK (by decide) (by decide) cover14335 (by decide)
  decide +kernel

theorem h14335 : P.leaf 36 14335 = 1500320186 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(229, 8837504), (188, 153470763), (166, 292080421), (160, 263919888), (169, 275760706), (112, 506250904)]) (.cons c14335_0 (.cons c14335_1 (.cons c14335_2 (.cons c14335_3 (.cons c14335_4 (.cons c14335_5 (.nil))))))) (by decide) (by decide))

theorem cover15606 : P.CoversSplit 26 10 15606 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c15606_0 : P.sumLeaves 26 15980544 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 15606) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover15606 (by decide)
  decide +kernel

theorem h15606 : P.leaf 36 15606 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c15606_0 (.nil)) (by decide) (by decide))

theorem cover15607 : P.CoversSplit 26 10 15607 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c15607_0 : P.sumLeaves 26 15981568 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 15607) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover15607 (by decide)
  decide +kernel

theorem h15607 : P.leaf 36 15607 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c15607_0 (.nil)) (by decide) (by decide))

theorem cover15608 : P.CoversSplit 26 10 15608 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c15608_0 : P.sumLeaves 26 15982592 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 15608) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover15608 (by decide)
  decide +kernel

theorem h15608 : P.leaf 36 15608 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c15608_0 (.nil)) (by decide) (by decide))

theorem cover15609 : P.CoversSplit 26 10 15609 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c15609_0 : P.sumLeaves 26 15983616 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 15609) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover15609 (by decide)
  decide +kernel

theorem h15609 : P.leaf 36 15609 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c15609_0 (.nil)) (by decide) (by decide))

theorem cover15610 : P.CoversSplit 26 10 15610 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c15610_0 : P.sumLeaves 26 15984640 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 15610) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover15610 (by decide)
  decide +kernel

theorem h15610 : P.leaf 36 15610 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c15610_0 (.nil)) (by decide) (by decide))

theorem cover15611 : P.CoversSplit 26 10 15611 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c15611_0 : P.sumLeaves 26 15985664 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 15611) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover15611 (by decide)
  decide +kernel

theorem h15611 : P.leaf 36 15611 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c15611_0 (.nil)) (by decide) (by decide))

theorem cover15614 : P.CoversSplit 26 10 15614 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c15614_0 : P.sumLeaves 26 15988736 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 15614) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover15614 (by decide)
  decide +kernel

theorem h15614 : P.leaf 36 15614 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c15614_0 (.nil)) (by decide) (by decide))

theorem cover15615 : P.CoversSplit 26 10 15615 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c15615_0 : P.sumLeaves 26 15989760 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 15615) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover15615 (by decide)
  decide +kernel

theorem h15615 : P.leaf 36 15615 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c15615_0 (.nil)) (by decide) (by decide))

theorem cover15732 : P.CoversSplit 26 10 15732 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c15732_0 : P.sumLeaves 26 16109568 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 15732) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover15732 (by decide)
  decide +kernel

theorem h15732 : P.leaf 36 15732 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c15732_0 (.nil)) (by decide) (by decide))

theorem cover15733 : P.CoversSplit 26 10 15733 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c15733_0 : P.sumLeaves 26 16110592 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 15733) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover15733 (by decide)
  decide +kernel

theorem h15733 : P.leaf 36 15733 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c15733_0 (.nil)) (by decide) (by decide))

theorem cover15734 : P.CoversSplit 26 10 15734 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c15734_0 : P.sumLeaves 26 16111616 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 15734) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover15734 (by decide)
  decide +kernel

theorem h15734 : P.leaf 36 15734 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c15734_0 (.nil)) (by decide) (by decide))

theorem cover15735 : P.CoversSplit 26 10 15735 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c15735_0 : P.sumLeaves 26 16112640 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 15735) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover15735 (by decide)
  decide +kernel

theorem h15735 : P.leaf 36 15735 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c15735_0 (.nil)) (by decide) (by decide))

theorem cover15740 : P.CoversSplit 26 10 15740 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c15740_0 : P.sumLeaves 26 16117760 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 15740) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover15740 (by decide)
  decide +kernel

theorem h15740 : P.leaf 36 15740 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c15740_0 (.nil)) (by decide) (by decide))

theorem cover15741 : P.CoversSplit 26 10 15741 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c15741_0 : P.sumLeaves 26 16118784 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 15741) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover15741 (by decide)
  decide +kernel

theorem h15741 : P.leaf 36 15741 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c15741_0 (.nil)) (by decide) (by decide))

theorem cover15742 : P.CoversSplit 26 10 15742 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c15742_0 : P.sumLeaves 26 16119808 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 15742) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover15742 (by decide)
  decide +kernel

theorem h15742 : P.leaf 36 15742 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c15742_0 (.nil)) (by decide) (by decide))

theorem cover15743 : P.CoversSplit 26 10 15743 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c15743_0 : P.sumLeaves 26 16120832 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 15743) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover15743 (by decide)
  decide +kernel

theorem h15743 : P.leaf 36 15743 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c15743_0 (.nil)) (by decide) (by decide))

theorem cover15795 : P.CoversSplit 26 10 15795 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [482]) (by decide +kernel)

theorem c15795_0 : P.sumLeaves 26 16174080 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 15795) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover15795 (by decide)
  decide +kernel

theorem h15795 : P.leaf 36 15795 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c15795_0 (.nil)) (by decide) (by decide))

theorem cover15796 : P.CoversSplit 26 10 15796 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c15796_0 : P.sumLeaves 26 16175104 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 15796) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover15796 (by decide)
  decide +kernel

theorem h15796 : P.leaf 36 15796 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c15796_0 (.nil)) (by decide) (by decide))

theorem cover15797 : P.CoversSplit 26 10 15797 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c15797_0 : P.sumLeaves 26 16176128 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 15797) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover15797 (by decide)
  decide +kernel

theorem h15797 : P.leaf 36 15797 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c15797_0 (.nil)) (by decide) (by decide))

theorem cover15799 : P.CoversSplit 26 10 15799 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c15799_0 : P.sumLeaves 26 16178176 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 15799) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover15799 (by decide)
  decide +kernel

theorem h15799 : P.leaf 36 15799 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c15799_0 (.nil)) (by decide) (by decide))

theorem cover15800 : P.CoversSplit 26 10 15800 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c15800_0 : P.sumLeaves 26 16179200 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 15800) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover15800 (by decide)
  decide +kernel

theorem h15800 : P.leaf 36 15800 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c15800_0 (.nil)) (by decide) (by decide))

theorem cover15801 : P.CoversSplit 26 10 15801 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c15801_0 : P.sumLeaves 26 16180224 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 15801) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover15801 (by decide)
  decide +kernel

theorem h15801 : P.leaf 36 15801 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c15801_0 (.nil)) (by decide) (by decide))

theorem cover15803 : P.CoversSplit 26 10 15803 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c15803_0 : P.sumLeaves 26 16182272 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 15803) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover15803 (by decide)
  decide +kernel

theorem h15803 : P.leaf 36 15803 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c15803_0 (.nil)) (by decide) (by decide))

theorem cover15804 : P.CoversSplit 26 10 15804 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c15804_0 : P.sumLeaves 26 16183296 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 15804) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover15804 (by decide)
  decide +kernel

theorem h15804 : P.leaf 36 15804 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c15804_0 (.nil)) (by decide) (by decide))

theorem cover15805 : P.CoversSplit 26 10 15805 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c15805_0 : P.sumLeaves 26 16184320 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 15805) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover15805 (by decide)
  decide +kernel

theorem h15805 : P.leaf 36 15805 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c15805_0 (.nil)) (by decide) (by decide))

theorem cover15807 : P.CoversSplit 26 10 15807 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c15807_0 : P.sumLeaves 26 16186368 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 15807) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover15807 (by decide)
  decide +kernel

theorem h15807 : P.leaf 36 15807 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c15807_0 (.nil)) (by decide) (by decide))

theorem cover15827 : P.CoversSplit 26 10 15827 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [482]) (by decide +kernel)

theorem c15827_0 : P.sumLeaves 26 16206848 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 15827) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover15827 (by decide)
  decide +kernel

theorem h15827 : P.leaf 36 15827 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c15827_0 (.nil)) (by decide) (by decide))

theorem cover15828 : P.CoversSplit 26 10 15828 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c15828_0 : P.sumLeaves 26 16207872 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 15828) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover15828 (by decide)
  decide +kernel

theorem h15828 : P.leaf 36 15828 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c15828_0 (.nil)) (by decide) (by decide))

theorem cover15829 : P.CoversSplit 26 10 15829 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c15829_0 : P.sumLeaves 26 16208896 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 15829) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover15829 (by decide)
  decide +kernel

theorem h15829 : P.leaf 36 15829 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c15829_0 (.nil)) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(14332, 360), (14333, 720), (14335, 360), (15606, 180), (15607, 180), (15608, 180), (15609, 180), (15610, 360), (15611, 360), (15614, 180), (15615, 180), (15732, 720), (15733, 720), (15734, 720), (15735, 720), (15740, 360), (15741, 360), (15742, 360), (15743, 360), (15795, 180), (15796, 360), (15797, 720), (15799, 360), (15800, 360), (15801, 720), (15803, 360), (15804, 360), (15805, 720), (15807, 360), (15827, 180), (15828, 720), (15829, 720)]

theorem segOK : checkSeg 20 perms 14332 15830 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 14332 15830 13680 681701038200 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 681701038200)
    (SegSum.cons (w := 360) h14332 (SegSum.cons (w := 720) h14333 (SegSum.cons (w := 360) h14335 (SegSum.cons (w := 180) h15606 (SegSum.cons (w := 180) h15607 (SegSum.cons (w := 180) h15608 (SegSum.cons (w := 180) h15609 (SegSum.cons (w := 360) h15610 (SegSum.cons (w := 360) h15611 (SegSum.cons (w := 180) h15614 (SegSum.cons (w := 180) h15615 (SegSum.cons (w := 720) h15732 (SegSum.cons (w := 720) h15733 (SegSum.cons (w := 720) h15734 (SegSum.cons (w := 720) h15735 (SegSum.cons (w := 360) h15740 (SegSum.cons (w := 360) h15741 (SegSum.cons (w := 360) h15742 (SegSum.cons (w := 360) h15743 (SegSum.cons (w := 180) h15795 (SegSum.cons (w := 360) h15796 (SegSum.cons (w := 720) h15797 (SegSum.cons (w := 360) h15799 (SegSum.cons (w := 360) h15800 (SegSum.cons (w := 720) h15801 (SegSum.cons (w := 360) h15803 (SegSum.cons (w := 360) h15804 (SegSum.cons (w := 720) h15805 (SegSum.cons (w := 360) h15807 (SegSum.cons (w := 180) h15827 (SegSum.cons (w := 720) h15828 (SegSum.cons (w := 720) h15829 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S30
