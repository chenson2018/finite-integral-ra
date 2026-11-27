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

namespace RACert.S6N0.C0.S54

open RACert RACert.Problem

theorem cover81758 : P.CoversSplit 26 10 81758 0xffff0000ffff05000000000000000000ffff0000fffc050055550000550005000000000000000000050500000505000000000000000000000505000005000000ffff0000ffff05000000000000000000ffff0000ff00050055550000550005000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [530, 880, 930, 972, 979, 1315, 1322, 1658, 1665]) (ps := [(21, [867, 1272], [1658])]) (by decide +kernel)

theorem c81758_0 : P.sumLeaves 26 83720192 820 = 25241631 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81758) (lo := 0) (len := 820) (W := 25241631) check rows elimOK (by decide) (by decide) cover81758 (by decide)
  decide +kernel

theorem c81758_1 : P.sumLeaves 26 83721012 204 = 64124887 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81758) (lo := 820) (len := 204) (W := 64124887) check rows elimOK (by decide) (by decide) cover81758 (by decide)
  decide +kernel

theorem h81758 : P.leaf 36 81758 = 89366518 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(820, 25241631), (204, 64124887)]) (.cons c81758_0 (.cons c81758_1 (.nil))) (by decide) (by decide))

theorem cover81759 : P.CoversSplit 26 10 81759 0xffff0000ffff05000000000000000000ffff0000fffc050055550000550005000000000000000000050500000505000000000000000000000505000005000000ffff0000ffff05000000000000000000ffff0000ff00050055550000550005000000000000000000050500000505000000000000000000000505000005000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [530, 930, 972, 979, 1315, 1322, 1658, 1665]) (ps := [(21, [1272], [1658])]) (by decide +kernel)

theorem c81759_0 : P.sumLeaves 26 83721216 664 = 34100955 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81759) (lo := 0) (len := 664) (W := 34100955) check rows elimOK (by decide) (by decide) cover81759 (by decide)
  decide +kernel

theorem c81759_1 : P.sumLeaves 26 83721880 360 = 114023564 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81759) (lo := 664) (len := 360) (W := 114023564) check rows elimOK (by decide) (by decide) cover81759 (by decide)
  decide +kernel

theorem h81759 : P.leaf 36 81759 = 148124519 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(664, 34100955), (360, 114023564)]) (.cons c81759_0 (.cons c81759_1 (.nil))) (by decide) (by decide))

theorem cover81790 : P.CoversSplit 26 10 81790 0xfffffffafffffafa0000000000000000fffffffafffcfac855555550550050005555505055555050555550505555505000000000000000005555505055005000fffffffafffffafa0000000000000000fffffffaff00fa0055555550550050000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [579, 874, 930, 972, 979, 1315, 1322, 1658, 1665]) (ps := [(21, [867], [1658])]) (by decide +kernel)

noncomputable def f81790 (i : ℕ) := rowWeight keep3 twice3 i * P.leaf 26 (83752960 + i)

theorem c81790_0 : rowSum f81790 0 700 = 118702088 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 81790) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover81790 (by decide)
  decide +kernel

theorem c81790_1 : rowSum f81790 700 323 = 224563208 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 81790) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover81790 (by decide)
  decide +kernel

theorem c81790_2 : rowSum f81790 1023 1 = 6187024 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 81790) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover81790 (by decide)
  decide +kernel

theorem sum81790 : rowSum f81790 0 1024 = 349452320 :=
  rowSum_append (F := f81790) (lo := 0) (n := 700) (m := 324) (A := 118702088) (B := 230750232) c81790_0 (rowSum_append (F := f81790) (lo := 700) (n := 323) (m := 1) (A := 224563208) (B := 6187024) c81790_1 (c81790_2))

theorem h81790 : P.leaf 36 81790 = 349452320 :=
  leaf_weighted (k := 26) (d := 10) (H := 81790) (keep := keep3) (twice := twice3) rows (by decide) (by decide) bal3 (invRow3 (H := 81790) (by decide) (by decide +kernel)) sum81790

theorem cover81791 : P.CoversSplit 26 10 81791 0xfffffffafffffafa0000000000000000fffffffafffcfac855555550550050005555505055555050555550505555505055555050555450405555505055005000fffffffafffffafa0000000000000000fffffffaff00fa0055555550550050005555505055555050555550505555505055555050550050005555505055005000 :=
  coversSplit check rows (by decide) (by decide) (xs := [579, 930, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f81791 (i : ℕ) := rowWeight keep3 twice3 i * P.leaf 26 (83753984 + i)

theorem c81791_0 : rowSum f81791 0 462 = 71882629 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 81791) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover81791 (by decide)
  decide +kernel

theorem c81791_1 : rowSum f81791 462 384 = 187944348 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 81791) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover81791 (by decide)
  decide +kernel

theorem c81791_2 : rowSum f81791 846 178 = 288557254 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 81791) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover81791 (by decide)
  decide +kernel

theorem sum81791 : rowSum f81791 0 1024 = 548384231 :=
  rowSum_append (F := f81791) (lo := 0) (n := 462) (m := 562) (A := 71882629) (B := 476501602) c81791_0 (rowSum_append (F := f81791) (lo := 462) (n := 384) (m := 178) (A := 187944348) (B := 288557254) c81791_1 (c81791_2))

theorem h81791 : P.leaf 36 81791 = 548384231 :=
  leaf_weighted (k := 26) (d := 10) (H := 81791) (keep := keep3) (twice := twice3) rows (by decide) (by decide) bal3 (invRow3 (H := 81791) (by decide) (by decide +kernel)) sum81791

theorem cover81811 : P.CoversSplit 26 10 81811 0xc000000000000000c0000000000000000000000000000000000000000000000000000c000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 538, 608, 930, 972, 979, 1315]) (by decide +kernel)

theorem c81811_0 : P.sumLeaves 26 83774464 1024 = 4354144 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81811) (lo := 0) (len := 1024) (W := 4354144) check rows elimOK (by decide) (by decide) cover81811 (by decide)
  decide +kernel

theorem h81811 : P.leaf 36 81811 = 4354144 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 4354144)]) (.cons c81811_0 (.nil)) (by decide) (by decide))

theorem cover81812 : P.CoversSplit 26 10 81812 0xcc00000000000000cc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 538, 923, 930, 972, 979, 1273, 1315, 1658, 1665]) (by decide +kernel)

theorem c81812_0 : P.sumLeaves 26 83775488 1024 = 949522 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81812) (lo := 0) (len := 1024) (W := 949522) check rows elimOK (by decide) (by decide) cover81812 (by decide)
  decide +kernel

theorem h81812 : P.leaf 36 81812 = 949522 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 949522)]) (.cons c81812_0 (.nil)) (by decide) (by decide))

theorem cover81813 : P.CoversSplit 26 10 81813 0xcc00000000000000cc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 538, 923, 930, 972, 979, 1315, 1658, 1665]) (by decide +kernel)

theorem c81813_0 : P.sumLeaves 26 83776512 1024 = 3518552 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81813) (lo := 0) (len := 1024) (W := 3518552) check rows elimOK (by decide) (by decide) cover81813 (by decide)
  decide +kernel

theorem h81813 : P.leaf 36 81813 = 3518552 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 3518552)]) (.cons c81813_0 (.nil)) (by decide) (by decide))

theorem cover81814 : P.CoversSplit 26 10 81814 0xcc00000000000000cc00000000000000000000000000000000000000000000000c0000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 538, 930, 972, 979, 1273, 1315, 1658, 1665]) (by decide +kernel)

theorem c81814_0 : P.sumLeaves 26 83777536 1024 = 3333644 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81814) (lo := 0) (len := 1024) (W := 3333644) check rows elimOK (by decide) (by decide) cover81814 (by decide)
  decide +kernel

theorem h81814 : P.leaf 36 81814 = 3333644 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 3333644)]) (.cons c81814_0 (.nil)) (by decide) (by decide))

theorem cover81815 : P.CoversSplit 26 10 81815 0xcc00000000000000cc00000000000000000000000000000000000000000000000c0000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 538, 930, 972, 979, 1315, 1658, 1665]) (by decide +kernel)

theorem c81815_0 : P.sumLeaves 26 83778560 1024 = 14272764 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81815) (lo := 0) (len := 1024) (W := 14272764) check rows elimOK (by decide) (by decide) cover81815 (by decide)
  decide +kernel

theorem h81815 : P.leaf 36 81815 = 14272764 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 14272764)]) (.cons c81815_0 (.nil)) (by decide) (by decide))

theorem cover81816 : P.CoversSplit 26 10 81816 0xf0f0000000000000f0f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 538, 615, 923, 972, 1273, 1315, 1322, 1658]) (by decide +kernel)

theorem c81816_0 : P.sumLeaves 26 83779584 1024 = 502528 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81816) (lo := 0) (len := 1024) (W := 502528) check rows elimOK (by decide) (by decide) cover81816 (by decide)
  decide +kernel

theorem h81816 : P.leaf 36 81816 = 502528 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 502528)]) (.cons c81816_0 (.nil)) (by decide) (by decide))

theorem cover81817 : P.CoversSplit 26 10 81817 0xf0f0000000000000f0f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 538, 615, 923, 972, 1273, 1315, 1322, 1658]) (by decide +kernel)

theorem c81817_0 : P.sumLeaves 26 83780608 1024 = 9870724 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81817) (lo := 0) (len := 1024) (W := 9870724) check rows elimOK (by decide) (by decide) cover81817 (by decide)
  decide +kernel

theorem h81817 : P.leaf 36 81817 = 9870724 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 9870724)]) (.cons c81817_0 (.nil)) (by decide) (by decide))

theorem cover81818 : P.CoversSplit 26 10 81818 0xf0f0000000000000f0f000000000000000000000000000000000000000000000000005050000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003000000000000000200000000000000000000000000000000000000000000000000001000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 538, 615, 972, 1273, 1315, 1322, 1658]) (by decide +kernel)

theorem c81818_0 : P.sumLeaves 26 83781632 1024 = 8286110 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81818) (lo := 0) (len := 1024) (W := 8286110) check rows elimOK (by decide) (by decide) cover81818 (by decide)
  decide +kernel

theorem h81818 : P.leaf 36 81818 = 8286110 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 8286110)]) (.cons c81818_0 (.nil)) (by decide) (by decide))

theorem cover81819 : P.CoversSplit 26 10 81819 0xf0f0000000000000f0f000000000000000000000000000000000000000000000000005050000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003000000000000000200000000000000000000000000000000000000000000000000001000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 538, 615, 972, 1273, 1315, 1322, 1658]) (by decide +kernel)

theorem c81819_0 : P.sumLeaves 26 83782656 1024 = 26211328 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81819) (lo := 0) (len := 1024) (W := 26211328) check rows elimOK (by decide) (by decide) cover81819 (by decide)
  decide +kernel

theorem h81819 : P.leaf 36 81819 = 26211328 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 26211328)]) (.cons c81819_0 (.nil)) (by decide) (by decide))

theorem cover81820 : P.CoversSplit 26 10 81820 0xffff000000000000ffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003300000000000000220000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 538, 923, 930, 972, 1273, 1315, 1322, 1658]) (by decide +kernel)

theorem c81820_0 : P.sumLeaves 26 83783680 1024 = 8403120 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81820) (lo := 0) (len := 1024) (W := 8403120) check rows elimOK (by decide) (by decide) cover81820 (by decide)
  decide +kernel

theorem h81820 : P.leaf 36 81820 = 8403120 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 8403120)]) (.cons c81820_0 (.nil)) (by decide) (by decide))

theorem cover81821 : P.CoversSplit 26 10 81821 0xffff000000000000ffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003300000000000000220000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 538, 923, 930, 972, 1273, 1315, 1322, 1658]) (by decide +kernel)

theorem c81821_0 : P.sumLeaves 26 83784704 1024 = 34607802 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81821) (lo := 0) (len := 1024) (W := 34607802) check rows elimOK (by decide) (by decide) cover81821 (by decide)
  decide +kernel

theorem h81821 : P.leaf 36 81821 = 34607802 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 34607802)]) (.cons c81821_0 (.nil)) (by decide) (by decide))

theorem cover81822 : P.CoversSplit 26 10 81822 0xffff000000000000ffff000000000000000000000000000000000000000000000f0f0a0a000000000a0a0a0a000000000000000000000000000000000000000000000000000000000000000000000000003300000000000000220000000000000000000000000000000000000000000000030002000000000002000200000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 538, 972, 1273, 1315, 1322, 1658]) (by decide +kernel)

theorem c81822_0 : P.sumLeaves 26 83785728 1024 = 27650916 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81822) (lo := 0) (len := 1024) (W := 27650916) check rows elimOK (by decide) (by decide) cover81822 (by decide)
  decide +kernel

theorem h81822 : P.leaf 36 81822 = 27650916 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 27650916)]) (.cons c81822_0 (.nil)) (by decide) (by decide))

theorem cover81823 : P.CoversSplit 26 10 81823 0xffff000000000000ffff000000000000000000000000000000000000000000000f0f0a0a000000000a0a0a0a000000000000000000000000000000000000000000000000000000000000000000000000003300000000000000220000000000000000000000000000000000000000000000030002000000000002000200000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 538, 972, 1273, 1315, 1322, 1658]) (by decide +kernel)

theorem c81823_0 : P.sumLeaves 26 83786752 1024 = 77338324 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81823) (lo := 0) (len := 1024) (W := 77338324) check rows elimOK (by decide) (by decide) cover81823 (by decide)
  decide +kernel

theorem h81823 : P.leaf 36 81823 = 77338324 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 77338324)]) (.cons c81823_0 (.nil)) (by decide) (by decide))

theorem cover81846 : P.CoversSplit 26 10 81846 0xcc00cc0000000000cc00cc000000000000000000000000000000000000000000cc00c0000000000088008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 538, 930, 972, 979, 1273, 1658, 1665]) (by decide +kernel)

noncomputable def f81846 (i : ℕ) := rowWeight keep3 twice3 i * P.leaf 26 (83810304 + i)

theorem c81846_0 : rowSum f81846 0 1024 = 17990104 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 81846) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover81846 (by decide)
  decide +kernel

theorem sum81846 : rowSum f81846 0 1024 = 17990104 :=
  c81846_0

theorem h81846 : P.leaf 36 81846 = 17990104 :=
  leaf_weighted (k := 26) (d := 10) (H := 81846) (keep := keep3) (twice := twice3) rows (by decide) (by decide) bal3 (invRow3 (H := 81846) (by decide) (by decide +kernel)) sum81846

theorem cover81847 : P.CoversSplit 26 10 81847 0xcc00cc0000000000cc00cc000000000000000000000000000000000000000000cc00c0000000000088008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 538, 930, 972, 979, 1658, 1665]) (by decide +kernel)

noncomputable def f81847 (i : ℕ) := rowWeight keep3 twice3 i * P.leaf 26 (83811328 + i)

theorem c81847_0 : rowSum f81847 0 1024 = 73773806 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 81847) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover81847 (by decide)
  decide +kernel

theorem sum81847 : rowSum f81847 0 1024 = 73773806 :=
  c81847_0

theorem h81847 : P.leaf 36 81847 = 73773806 :=
  leaf_weighted (k := 26) (d := 10) (H := 81847) (keep := keep3) (twice := twice3) rows (by decide) (by decide) bal3 (invRow3 (H := 81847) (by decide) (by decide +kernel)) sum81847

theorem cover81848 : P.CoversSplit 26 10 81848 0xf0f0f0f500000000f0f0f0f50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003000310000000000200020000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 874, 923, 930, 972, 979, 1273, 1315, 1322, 1658]) (by decide +kernel)

theorem c81848_0 : P.sumLeaves 26 83812352 1024 = 1768443 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81848) (lo := 0) (len := 1024) (W := 1768443) check rows elimOK (by decide) (by decide) cover81848 (by decide)
  decide +kernel

theorem h81848 : P.leaf 36 81848 = 1768443 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1768443)]) (.cons c81848_0 (.nil)) (by decide) (by decide))

theorem cover81849 : P.CoversSplit 26 10 81849 0xf0f0f0f500000000f0f0f0f50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003000310000000000200020000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 923, 930, 972, 979, 1273, 1315, 1322, 1658]) (by decide +kernel)

theorem c81849_0 : P.sumLeaves 26 83813376 1024 = 60253869 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81849) (lo := 0) (len := 1024) (W := 60253869) check rows elimOK (by decide) (by decide) cover81849 (by decide)
  decide +kernel

theorem h81849 : P.leaf 36 81849 = 60253869 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 60253869)]) (.cons c81849_0 (.nil)) (by decide) (by decide))

theorem cover81850 : P.CoversSplit 26 10 81850 0xf0f0f0f500000000f0f0f0f50000000000000000000000000000000000000000000050500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003000310000000000200020000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 874, 972, 979, 1273, 1315, 1322, 1658]) (by decide +kernel)

theorem c81850_0 : P.sumLeaves 26 83814400 1024 = 42922789 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81850) (lo := 0) (len := 1024) (W := 42922789) check rows elimOK (by decide) (by decide) cover81850 (by decide)
  decide +kernel

theorem h81850 : P.leaf 36 81850 = 42922789 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 42922789)]) (.cons c81850_0 (.nil)) (by decide) (by decide))

theorem cover81851 : P.CoversSplit 26 10 81851 0xf0f0f0f500000000f0f0f0f50000000000000000000000000000000000000000000050500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003000310000000000200020000000000000000000000000000000000000000000000010000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 972, 979, 1273, 1315, 1322, 1658]) (by decide +kernel)

theorem c81851_0 : P.sumLeaves 26 83815424 1024 = 134977234 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81851) (lo := 0) (len := 1024) (W := 134977234) check rows elimOK (by decide) (by decide) cover81851 (by decide)
  decide +kernel

theorem h81851 : P.leaf 36 81851 = 134977234 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 134977234)]) (.cons c81851_0 (.nil)) (by decide) (by decide))

theorem cover81854 : P.CoversSplit 26 10 81854 0xfffffffa00000000fffffffa0000000000000000000000000000000000000000fffff0f000000000aaaaa0a0000000000000000000000000000000000000000000000000000000000000000000000000003300320000000000220022000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [538, 874, 972, 979, 1273, 1315, 1322, 1658]) (by decide +kernel)

theorem c81854_0 : P.sumLeaves 26 83818496 1013 = 135697686 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81854) (lo := 0) (len := 1013) (W := 135697686) check rows elimOK (by decide) (by decide) cover81854 (by decide)
  decide +kernel

theorem c81854_1 : P.sumLeaves 26 83819509 11 = 33768084 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81854) (lo := 1013) (len := 11) (W := 33768084) check rows elimOK (by decide) (by decide) cover81854 (by decide)
  decide +kernel

theorem h81854 : P.leaf 36 81854 = 169465770 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1013, 135697686), (11, 33768084)]) (.cons c81854_0 (.cons c81854_1 (.nil))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(81758, 720), (81759, 720), (81790, 180), (81791, 180), (81811, 360), (81812, 360), (81813, 360), (81814, 720), (81815, 720), (81816, 720), (81817, 720), (81818, 720), (81819, 720), (81820, 720), (81821, 720), (81822, 720), (81823, 720), (81846, 180), (81847, 180), (81848, 360), (81849, 360), (81850, 720), (81851, 720), (81854, 360)]

theorem segOK : checkSeg 20 perms 81758 81855 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 81758 81855 12960 715264981380 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 715264981380)
    (SegSum.cons (w := 720) h81758 (SegSum.cons (w := 720) h81759 (SegSum.cons (w := 180) h81790 (SegSum.cons (w := 180) h81791 (SegSum.cons (w := 360) h81811 (SegSum.cons (w := 360) h81812 (SegSum.cons (w := 360) h81813 (SegSum.cons (w := 720) h81814 (SegSum.cons (w := 720) h81815 (SegSum.cons (w := 720) h81816 (SegSum.cons (w := 720) h81817 (SegSum.cons (w := 720) h81818 (SegSum.cons (w := 720) h81819 (SegSum.cons (w := 720) h81820 (SegSum.cons (w := 720) h81821 (SegSum.cons (w := 720) h81822 (SegSum.cons (w := 720) h81823 (SegSum.cons (w := 180) h81846 (SegSum.cons (w := 180) h81847 (SegSum.cons (w := 360) h81848 (SegSum.cons (w := 360) h81849 (SegSum.cons (w := 720) h81850 (SegSum.cons (w := 720) h81851 (SegSum.cons (w := 360) h81854 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S54
