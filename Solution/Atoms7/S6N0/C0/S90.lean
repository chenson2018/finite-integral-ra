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

namespace RACert.S6N0.C0.S90

open RACert RACert.Problem

theorem cover120663 : P.CoversSplit 26 10 120663 0xa0a00000a0a000000000000000000000a0a00000a0a0000000000000000000000000000000000000000005050000050500000000000000000000050500000000a0a00000a0a000000000000000000000a0a000000000000000000000000000000000000000000000000005050000050500000000000000000000050500000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 579, 873, 1315, 1322]) (by decide +kernel)

theorem c120663_0 : P.sumLeaves 26 123558912 1024 = 42104416 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120663) (lo := 0) (len := 1024) (W := 42104416) check rows elimOK (by decide) (by decide) cover120663 (by decide)
  decide +kernel

theorem h120663 : P.leaf 36 120663 = 42104416 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 42104416)]) (.cons c120663_0 (.nil)) (by decide) (by decide))

theorem cover120671 : P.CoversSplit 26 10 120671 0xa0a00000a0a000000000000000000000a0a00000a0a0000000000000000000000000000000000000000005050000050500000000000000000000050500000000a0a00000a0a000000000000000000000a0a000000000000000000000000000000000000000000000000005050000050500000000000000000000050500000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 579, 873, 1273, 1315, 1322]) (by decide +kernel)

theorem c120671_0 : P.sumLeaves 26 123567104 1024 = 44955216 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120671) (lo := 0) (len := 1024) (W := 44955216) check rows elimOK (by decide) (by decide) cover120671 (by decide)
  decide +kernel

theorem h120671 : P.leaf 36 120671 = 44955216 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 44955216)]) (.cons c120671_0 (.nil)) (by decide) (by decide))

theorem cover120678 : P.CoversSplit 26 10 120678 0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0c0c000000000000000000000000000000000000000000000000000000000000000000000000000000000f0f0f0f0f0f0f0f00000000000000000f0c0f0c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 579, 873, 922, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c120678_0 : P.sumLeaves 26 123574272 1012 = 24775812 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120678) (lo := 0) (len := 1012) (W := 24775812) check rows elimOK (by decide) (by decide) cover120678 (by decide)
  decide +kernel

theorem c120678_1 : P.sumLeaves 26 123575284 12 = 6390336 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120678) (lo := 1012) (len := 12) (W := 6390336) check rows elimOK (by decide) (by decide) cover120678 (by decide)
  decide +kernel

theorem h120678 : P.leaf 36 120678 = 31166148 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1012, 24775812), (12, 6390336)]) (.cons c120678_0 (.cons c120678_1 (.nil))) (by decide) (by decide))

theorem cover120679 : P.CoversSplit 26 10 120679 0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0c0c000000000000000000000000000000000000000000000000000000000000000000000000000000000f0f0f0f0f0f0f0f00000000000000000f0f0f0f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 579, 922, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c120679_0 : P.sumLeaves 26 123575296 1004 = 55444124 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120679) (lo := 0) (len := 1004) (W := 55444124) check rows elimOK (by decide) (by decide) cover120679 (by decide)
  decide +kernel

theorem c120679_1 : P.sumLeaves 26 123576300 20 = 12322144 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120679) (lo := 1004) (len := 20) (W := 12322144) check rows elimOK (by decide) (by decide) cover120679 (by decide)
  decide +kernel

theorem h120679 : P.leaf 36 120679 = 67766268 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1004, 55444124), (20, 12322144)]) (.cons c120679_0 (.cons c120679_1 (.nil))) (by decide) (by decide))

theorem cover120686 : P.CoversSplit 26 10 120686 0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0c0c000000000000000000000000000000000000000000000000000000000000000000000000000000000f0f0f0f0f0f0f0f00000000000000000f0f0f0f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [579, 873, 922, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c120686_0 : P.sumLeaves 26 123582464 1004 = 28476800 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120686) (lo := 0) (len := 1004) (W := 28476800) check rows elimOK (by decide) (by decide) cover120686 (by decide)
  decide +kernel

theorem c120686_1 : P.sumLeaves 26 123583468 20 = 11062144 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120686) (lo := 1004) (len := 20) (W := 11062144) check rows elimOK (by decide) (by decide) cover120686 (by decide)
  decide +kernel

theorem h120686 : P.leaf 36 120686 = 39538944 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1004, 28476800), (20, 11062144)]) (.cons c120686_0 (.cons c120686_1 (.nil))) (by decide) (by decide))

theorem cover120687 : P.CoversSplit 26 10 120687 0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0c0c000000000000000000000000000000000000000000000000000000000000000000000000000000000f0f0f0f0f0f0f0f00000000000000000f0f0f0f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [579, 922, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c120687_0 : P.sumLeaves 26 123583488 1004 = 55551584 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120687) (lo := 0) (len := 1004) (W := 55551584) check rows elimOK (by decide) (by decide) cover120687 (by decide)
  decide +kernel

theorem c120687_1 : P.sumLeaves 26 123584492 20 = 12341152 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120687) (lo := 1004) (len := 20) (W := 12341152) check rows elimOK (by decide) (by decide) cover120687 (by decide)
  decide +kernel

theorem h120687 : P.leaf 36 120687 = 67892736 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1004, 55551584), (20, 12341152)]) (.cons c120687_0 (.cons c120687_1 (.nil))) (by decide) (by decide))

theorem cover120694 : P.CoversSplit 26 10 120694 0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0c0c000000000000000000000000000000000000000000000000000000000000000000000000000000000f0f0f0f0f0f0f0f00000000000000000f0c0f0c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 579, 873, 922, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c120694_0 : P.sumLeaves 26 123590656 1012 = 74580700 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120694) (lo := 0) (len := 1012) (W := 74580700) check rows elimOK (by decide) (by decide) cover120694 (by decide)
  decide +kernel

theorem c120694_1 : P.sumLeaves 26 123591668 12 = 13990976 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120694) (lo := 1012) (len := 12) (W := 13990976) check rows elimOK (by decide) (by decide) cover120694 (by decide)
  decide +kernel

theorem h120694 : P.leaf 36 120694 = 88571676 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1012, 74580700), (12, 13990976)]) (.cons c120694_0 (.cons c120694_1 (.nil))) (by decide) (by decide))

theorem cover120695 : P.CoversSplit 26 10 120695 0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0c0c000000000000000000000000000000000000000000000000000000000000000000000000000000000f0f0f0f0f0f0f0f00000000000000000f0f0f0f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 579, 922, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c120695_0 : P.sumLeaves 26 123591680 1004 = 166604936 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120695) (lo := 0) (len := 1004) (W := 166604936) check rows elimOK (by decide) (by decide) cover120695 (by decide)
  decide +kernel

theorem c120695_1 : P.sumLeaves 26 123592684 20 = 34670912 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120695) (lo := 1004) (len := 20) (W := 34670912) check rows elimOK (by decide) (by decide) cover120695 (by decide)
  decide +kernel

theorem h120695 : P.leaf 36 120695 = 201275848 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1004, 166604936), (20, 34670912)]) (.cons c120695_0 (.cons c120695_1 (.nil))) (by decide) (by decide))

theorem cover120702 : P.CoversSplit 26 10 120702 0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0c0c000000000000000000000000000000000000000000000000000000000000000000000000000000000f0f0f0f0f0f0f0f00000000000000000f0f0f0f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [579, 873, 922, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c120702_0 : P.sumLeaves 26 123598848 1004 = 93429332 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120702) (lo := 0) (len := 1004) (W := 93429332) check rows elimOK (by decide) (by decide) cover120702 (by decide)
  decide +kernel

theorem c120702_1 : P.sumLeaves 26 123599852 20 = 28108000 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120702) (lo := 1004) (len := 20) (W := 28108000) check rows elimOK (by decide) (by decide) cover120702 (by decide)
  decide +kernel

theorem h120702 : P.leaf 36 120702 = 121537332 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1004, 93429332), (20, 28108000)]) (.cons c120702_0 (.cons c120702_1 (.nil))) (by decide) (by decide))

theorem cover120703 : P.CoversSplit 26 10 120703 0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0c0c000000000000000000000000000000000000000000000000000000000000000000000000000000000f0f0f0f0f0f0f0f00000000000000000f0f0f0f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [579, 922, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c120703_0 : P.sumLeaves 26 123599872 1004 = 166604936 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120703) (lo := 0) (len := 1004) (W := 166604936) check rows elimOK (by decide) (by decide) cover120703 (by decide)
  decide +kernel

theorem c120703_1 : P.sumLeaves 26 123600876 20 = 34670912 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120703) (lo := 1004) (len := 20) (W := 34670912) check rows elimOK (by decide) (by decide) cover120703 (by decide)
  decide +kernel

theorem h120703 : P.leaf 36 120703 = 201275848 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1004, 166604936), (20, 34670912)]) (.cons c120703_0 (.cons c120703_1 (.nil))) (by decide) (by decide))

theorem cover120803 : P.CoversSplit 26 10 120803 0xf0f00000f0f000000000000000000000f0f00000f0c000000000000000000000f0f00000f0f000000000505000005050f0f00000f0c000000000505000004040f0f00000f0f000000000000000000000f0f00000c00000000000000000000000f0f00000f0f000000000505000005050f0f00000c00000000000505000004000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 608, 873, 922, 1273, 1322]) (by decide +kernel)

theorem c120803_0 : P.sumLeaves 26 123702272 727 = 56989111 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120803) (lo := 0) (len := 727) (W := 56989111) check rows elimOK (by decide) (by decide) cover120803 (by decide)
  decide +kernel

theorem c120803_1 : P.sumLeaves 26 123702999 297 = 88544732 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120803) (lo := 727) (len := 297) (W := 88544732) check rows elimOK (by decide) (by decide) cover120803 (by decide)
  decide +kernel

theorem h120803 : P.leaf 36 120803 = 145533843 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(727, 56989111), (297, 88544732)]) (.cons c120803_0 (.cons c120803_1 (.nil))) (by decide) (by decide))

theorem cover120805 : P.CoversSplit 26 10 120805 0xfffffffffffffafafffffffffffffafaffffffffffffc8c8fafafafac8c8c8c8fffffafafffffafafafaf0f0fafaf0f0fffffafaffffc8c8fafaf0f0c8c8c0c0ffffffffffccfac8ffffffffffccfac8ffffffffcc00c800fafafafac800c800fffffafaffccfac8fafaf0f0fac8f0c0fffffafacc00c800fafaf0f0c800c000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 873, 922, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c120805_0 : P.sumLeaves 26 123704320 198 = 13362539 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120805) (lo := 0) (len := 198) (W := 13362539) check rows elimOK (by decide) (by decide) cover120805 (by decide)
  decide +kernel

theorem c120805_1 : P.sumLeaves 26 123704518 165 = 28388770 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120805) (lo := 198) (len := 165) (W := 28388770) check rows elimOK (by decide) (by decide) cover120805 (by decide)
  decide +kernel

theorem c120805_2 : P.sumLeaves 26 123704683 118 = 54312664 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120805) (lo := 363) (len := 118) (W := 54312664) check rows elimOK (by decide) (by decide) cover120805 (by decide)
  decide +kernel

theorem c120805_3 : P.sumLeaves 26 123704801 144 = 75152126 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120805) (lo := 481) (len := 144) (W := 75152126) check rows elimOK (by decide) (by decide) cover120805 (by decide)
  decide +kernel

theorem c120805_4 : P.sumLeaves 26 123704945 128 = 87478696 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120805) (lo := 625) (len := 128) (W := 87478696) check rows elimOK (by decide) (by decide) cover120805 (by decide)
  decide +kernel

theorem c120805_5 : P.sumLeaves 26 123705073 134 = 108253976 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120805) (lo := 753) (len := 134) (W := 108253976) check rows elimOK (by decide) (by decide) cover120805 (by decide)
  decide +kernel

theorem c120805_6 : P.sumLeaves 26 123705207 104 = 115723929 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120805) (lo := 887) (len := 104) (W := 115723929) check rows elimOK (by decide) (by decide) cover120805 (by decide)
  decide +kernel

theorem c120805_7 : P.sumLeaves 26 123705311 33 = 99304866 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 120805) (lo := 991) (len := 33) (W := 99304866) check rows elimOK (by decide) (by decide) cover120805 (by decide)
  decide +kernel

theorem h120805 : P.leaf 36 120805 = 581977566 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(198, 13362539), (165, 28388770), (118, 54312664), (144, 75152126), (128, 87478696), (134, 108253976), (104, 115723929), (33, 99304866)]) (.cons c120805_0 (.cons c120805_1 (.cons c120805_2 (.cons c120805_3 (.cons c120805_4 (.cons c120805_5 (.cons c120805_6 (.cons c120805_7 (.nil))))))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(120663, 180), (120671, 180), (120678, 360), (120679, 360), (120686, 360), (120687, 360), (120694, 720), (120695, 720), (120702, 720), (120703, 720), (120803, 360), (120805, 720)]

theorem segOK : checkSeg 20 perms 120663 120807 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 120663 120807 5760 1002493546200 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 1002493546200)
    (SegSum.cons (w := 180) h120663 (SegSum.cons (w := 180) h120671 (SegSum.cons (w := 360) h120678 (SegSum.cons (w := 360) h120679 (SegSum.cons (w := 360) h120686 (SegSum.cons (w := 360) h120687 (SegSum.cons (w := 720) h120694 (SegSum.cons (w := 720) h120695 (SegSum.cons (w := 720) h120702 (SegSum.cons (w := 720) h120703 (SegSum.cons (w := 360) h120803 (SegSum.cons (w := 720) h120805 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))) (by decide)

end RACert.S6N0.C0.S90
