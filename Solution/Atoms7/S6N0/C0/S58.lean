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

namespace RACert.S6N0.C0.S58

open RACert RACert.Problem

theorem cover81757 : P.CoversSplit 26 10 81757 0xffff0000ffff05000000000000000000ffff0000fffc050055550000550005000000000000000000000000000000000000000000000000000000000000000000ffff0000ffff05000000000000000000ffff0000ff00050055550000550005000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 579, 923, 930, 972, 979, 1315, 1658, 1665]) (by decide +kernel)

theorem c81757_0 : P.sumLeaves 26 83719168 856 = 11433868 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81757) (lo := 0) (len := 856) (W := 11433868) check rows elimOK (by decide) (by decide) cover81757 (by decide)
  decide +kernel

theorem c81757_1 : P.sumLeaves 26 83720024 168 = 26406404 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81757) (lo := 856) (len := 168) (W := 26406404) check rows elimOK (by decide) (by decide) cover81757 (by decide)
  decide +kernel

theorem h81757 : P.leaf 36 81757 = 37840272 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(856, 11433868), (168, 26406404)]) (.cons c81757_0 (.cons c81757_1 (.nil))) (by decide) (by decide))

theorem cover81758 : P.CoversSplit 26 10 81758 0xffff0000ffff05000000000000000000ffff0000fffc050055550000550005000505000005050000050500000505000005050000050400000505000005000000ffff0000ffff05000000000000000000ffff0000ff00050055550000550005000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 880, 930, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c81758_0 : P.sumLeaves 26 83720192 722 = 23577985 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81758) (lo := 0) (len := 722) (W := 23577985) check rows elimOK (by decide) (by decide) cover81758 (by decide)
  decide +kernel

theorem c81758_1 : P.sumLeaves 26 83720914 302 = 65788533 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81758) (lo := 722) (len := 302) (W := 65788533) check rows elimOK (by decide) (by decide) cover81758 (by decide)
  decide +kernel

theorem h81758 : P.leaf 36 81758 = 89366518 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(722, 23577985), (302, 65788533)]) (.cons c81758_0 (.cons c81758_1 (.nil))) (by decide) (by decide))

theorem cover81759 : P.CoversSplit 26 10 81759 0xffff0000ffff05000000000000000000ffff0000fffc050055550000550005000505000005050000050500000505000005050000050400000505000005000000ffff0000ffff05000000000000000000ffff0000ff00050055550000550005000505000005050000050500000505000005050000050000000505000005000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 930, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c81759_0 : P.sumLeaves 26 83721216 506 = 26662862 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81759) (lo := 0) (len := 506) (W := 26662862) check rows elimOK (by decide) (by decide) cover81759 (by decide)
  decide +kernel

theorem c81759_1 : P.sumLeaves 26 83721722 483 = 69449501 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81759) (lo := 506) (len := 483) (W := 69449501) check rows elimOK (by decide) (by decide) cover81759 (by decide)
  decide +kernel

theorem c81759_2 : P.sumLeaves 26 83722205 35 = 52012156 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81759) (lo := 989) (len := 35) (W := 52012156) check rows elimOK (by decide) (by decide) cover81759 (by decide)
  decide +kernel

theorem h81759 : P.leaf 36 81759 = 148124519 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(506, 26662862), (483, 69449501), (35, 52012156)]) (.cons c81759_0 (.cons c81759_1 (.cons c81759_2 (.nil)))) (by decide) (by decide))

theorem cover81790 : P.CoversSplit 26 10 81790 0xfffffffafffffafa0000000000000000fffffffafffcfac855555550550050005555505055555050555550505555505055555050555450405555505055005000fffffffafffffafa0000000000000000fffffffaff00fa0055555550550050000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [579, 874, 930, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c81790_0 : P.sumLeaves 26 83752960 486 = 50450508 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81790) (lo := 0) (len := 486) (W := 50450508) check rows elimOK (by decide) (by decide) cover81790 (by decide)
  decide +kernel

theorem c81790_1 : P.sumLeaves 26 83753446 238 = 76247490 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81790) (lo := 486) (len := 238) (W := 76247490) check rows elimOK (by decide) (by decide) cover81790 (by decide)
  decide +kernel

theorem c81790_2 : P.sumLeaves 26 83753684 243 = 77660769 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81790) (lo := 724) (len := 243) (W := 77660769) check rows elimOK (by decide) (by decide) cover81790 (by decide)
  decide +kernel

theorem c81790_3 : P.sumLeaves 26 83753927 57 = 145093553 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81790) (lo := 967) (len := 57) (W := 145093553) check rows elimOK (by decide) (by decide) cover81790 (by decide)
  decide +kernel

theorem h81790 : P.leaf 36 81790 = 349452320 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(486, 50450508), (238, 76247490), (243, 77660769), (57, 145093553)]) (.cons c81790_0 (.cons c81790_1 (.cons c81790_2 (.cons c81790_3 (.nil))))) (by decide) (by decide))

theorem cover81791 : P.CoversSplit 26 10 81791 0xfffffffafffffafa0000000000000000fffffffafffcfac855555550550050005555505055555050555550505555505055555050555450405555505055005000fffffffafffffafa0000000000000000fffffffaff00fa0055555550550050005555505055555050555550505555505055555050550050005555505055005000 :=
  coversSplit check rows (by decide) (by decide) (xs := [579, 930, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c81791_0 : P.sumLeaves 26 83753984 304 = 7698601 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81791) (lo := 0) (len := 304) (W := 7698601) check rows elimOK (by decide) (by decide) cover81791 (by decide)
  decide +kernel

theorem c81791_1 : P.sumLeaves 26 83754288 194 = 105757982 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81791) (lo := 304) (len := 194) (W := 105757982) check rows elimOK (by decide) (by decide) cover81791 (by decide)
  decide +kernel

theorem c81791_2 : P.sumLeaves 26 83754482 258 = 104152924 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81791) (lo := 498) (len := 258) (W := 104152924) check rows elimOK (by decide) (by decide) cover81791 (by decide)
  decide +kernel

theorem c81791_3 : P.sumLeaves 26 83754740 225 = 145167800 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81791) (lo := 756) (len := 225) (W := 145167800) check rows elimOK (by decide) (by decide) cover81791 (by decide)
  decide +kernel

theorem c81791_4 : P.sumLeaves 26 83754965 43 = 185606924 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81791) (lo := 981) (len := 43) (W := 185606924) check rows elimOK (by decide) (by decide) cover81791 (by decide)
  decide +kernel

theorem h81791 : P.leaf 36 81791 = 548384231 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(304, 7698601), (194, 105757982), (258, 104152924), (225, 145167800), (43, 185606924)]) (.cons c81791_0 (.cons c81791_1 (.cons c81791_2 (.cons c81791_3 (.cons c81791_4 (.nil)))))) (by decide) (by decide))

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

def seg : List (ℕ × ℕ) := [(81757, 360), (81758, 720), (81759, 720), (81790, 180), (81791, 180), (81811, 360), (81812, 360), (81813, 360), (81814, 720), (81815, 720), (81816, 720), (81817, 720), (81818, 720)]

theorem segOK : checkSeg 20 perms 81757 81819 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 81757 81819 6840 375513976620 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 375513976620)
    (SegSum.cons (w := 360) h81757 (SegSum.cons (w := 720) h81758 (SegSum.cons (w := 720) h81759 (SegSum.cons (w := 180) h81790 (SegSum.cons (w := 180) h81791 (SegSum.cons (w := 360) h81811 (SegSum.cons (w := 360) h81812 (SegSum.cons (w := 360) h81813 (SegSum.cons (w := 720) h81814 (SegSum.cons (w := 720) h81815 (SegSum.cons (w := 720) h81816 (SegSum.cons (w := 720) h81817 (SegSum.cons (w := 720) h81818 (show SegSum (P.leaf 36) [] 0 from rfl)))))))))))))) (by decide)

end RACert.S6N0.C0.S58
