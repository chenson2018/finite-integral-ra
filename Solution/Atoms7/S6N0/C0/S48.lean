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

namespace RACert.S6N0.C0.S48

open RACert RACert.Problem

theorem cover78783 : P.CoversSplit 26 10 78783 0xfffffffa00000000fffffffa0000000000000000000000000000000000000000fffff0f000000000aaaaa0a0000000000000000000000000000000000000000000000000000000000000000000000000330033003300300022002200220020000000000000000000000000000000000033003000330030002200200022002000 :=
  coversSplit check rows (by decide) (by decide) (xs := [538, 873, 930, 972, 979, 1273, 1315, 1322, 1658]) (by decide +kernel)

theorem c78783_0 : P.sumLeaves 26 80673792 951 = 14338820 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78783) (lo := 0) (len := 951) (W := 14338820) check rows elimOK (by decide) (by decide) cover78783 (by decide)
  decide +kernel

theorem c78783_1 : P.sumLeaves 26 80674743 73 = 14487484 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78783) (lo := 951) (len := 73) (W := 14487484) check rows elimOK (by decide) (by decide) cover78783 (by decide)
  decide +kernel

theorem h78783 : P.leaf 36 78783 = 28826304 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(951, 14338820), (73, 14487484)]) (.cons c78783_0 (.cons c78783_1 (.nil))) (by decide) (by decide))

theorem cover78793 : P.CoversSplit 26 10 78793 0xf0f00000f0f00005f0f00000f0f00005f0f00000f0f00000a0a00000a08000000000000000000000000000000000000000000000000000000000000000000000f0f00000f0f00005f0f00000f0f00005f000000000000000a0000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 923, 930, 972, 979, 1273, 1315, 1658, 1665]) (by decide +kernel)

theorem c78793_0 : P.sumLeaves 26 80684032 1015 = 78560 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78793) (lo := 0) (len := 1015) (W := 78560) check rows elimOK (by decide) (by decide) cover78793 (by decide)
  decide +kernel

theorem c78793_1 : P.sumLeaves 26 80685047 9 = 21248 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78793) (lo := 1015) (len := 9) (W := 21248) check rows elimOK (by decide) (by decide) cover78793 (by decide)
  decide +kernel

theorem h78793 : P.leaf 36 78793 = 99808 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1015, 78560), (9, 21248)]) (.cons c78793_0 (.cons c78793_1 (.nil))) (by decide) (by decide))

theorem cover78795 : P.CoversSplit 26 10 78795 0xf0f00000f0f00005f0f00000f0f00005f0f00000f0f00000a0a00000a08000000000000000000000000000000000000000000000000000000000000000000000f0f00000f0f00005f0f00000f0f00005f000000000000000a0000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 930, 972, 979, 1266, 1273, 1315, 1658, 1665]) (by decide +kernel)

theorem c78795_0 : P.sumLeaves 26 80686080 1015 = 637296 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78795) (lo := 0) (len := 1015) (W := 637296) check rows elimOK (by decide) (by decide) cover78795 (by decide)
  decide +kernel

theorem c78795_1 : P.sumLeaves 26 80687095 9 = 100000 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78795) (lo := 1015) (len := 9) (W := 100000) check rows elimOK (by decide) (by decide) cover78795 (by decide)
  decide +kernel

theorem h78795 : P.leaf 36 78795 = 737296 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1015, 637296), (9, 100000)]) (.cons c78795_0 (.cons c78795_1 (.nil))) (by decide) (by decide))

theorem cover78798 : P.CoversSplit 26 10 78798 0xffff0000ffff0500ffff0000ffff050000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 873, 879, 880, 972, 1266, 1315]) (by decide +kernel)

theorem c78798_0 : P.sumLeaves 26 80689152 1024 = 1002640 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78798) (lo := 0) (len := 1024) (W := 1002640) check rows elimOK (by decide) (by decide) cover78798 (by decide)
  decide +kernel

theorem h78798 : P.leaf 36 78798 = 1002640 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1002640)]) (.cons c78798_0 (.nil)) (by decide) (by decide))

theorem cover78799 : P.CoversSplit 26 10 78799 0xffff0000ffff0500ffff0000ffff0500fffc0000fffc0000aaa80000aa8800000000000000000000000000000000000000000000000000000000000000000000ffff0000ffff0500ffff0000ffff0500ffcc000000000000aa880000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 930, 972, 979, 1266, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c78799_0 : P.sumLeaves 26 80690176 827 = 3471542 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78799) (lo := 0) (len := 827) (W := 3471542) check rows elimOK (by decide) (by decide) cover78799 (by decide)
  decide +kernel

theorem c78799_1 : P.sumLeaves 26 80691003 194 = 7143982 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78799) (lo := 827) (len := 194) (W := 7143982) check rows elimOK (by decide) (by decide) cover78799 (by decide)
  decide +kernel

theorem c78799_2 : P.sumLeaves 26 80691197 3 = 434624 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78799) (lo := 1021) (len := 3) (W := 434624) check rows elimOK (by decide) (by decide) cover78799 (by decide)
  decide +kernel

theorem h78799 : P.leaf 36 78799 = 11050148 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(827, 3471542), (194, 7143982), (3, 434624)]) (.cons c78799_0 (.cons c78799_1 (.cons c78799_2 (.nil)))) (by decide) (by decide))

theorem cover78811 : P.CoversSplit 26 10 78811 0xf0f00000f0f00005f0f00000f0f00005f0f00000f0f00000a0a00000a08000000000000000000000000000000000000000000000000000000000000000000000f0f00000f0f00005f0f00000f0f00005f000000000000000a0000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 873, 930, 972, 979, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c78811_0 : P.sumLeaves 26 80702464 1015 = 4161370 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78811) (lo := 0) (len := 1015) (W := 4161370) check rows elimOK (by decide) (by decide) cover78811 (by decide)
  decide +kernel

theorem c78811_1 : P.sumLeaves 26 80703479 9 = 672000 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78811) (lo := 1015) (len := 9) (W := 672000) check rows elimOK (by decide) (by decide) cover78811 (by decide)
  decide +kernel

theorem h78811 : P.leaf 36 78811 = 4833370 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1015, 4161370), (9, 672000)]) (.cons c78811_0 (.cons c78811_1 (.nil))) (by decide) (by decide))

theorem cover78812 : P.CoversSplit 26 10 78812 0xffff0000ffff0000ffff0000ffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [467, 867, 880, 923]) (by decide +kernel)

theorem c78812_0 : P.sumLeaves 26 80703488 1024 = 901968 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78812) (lo := 0) (len := 1024) (W := 901968) check rows elimOK (by decide) (by decide) cover78812 (by decide)
  decide +kernel

theorem h78812 : P.leaf 36 78812 = 901968 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 901968)]) (.cons c78812_0 (.nil)) (by decide) (by decide))

theorem cover78813 : P.CoversSplit 26 10 78813 0xffff0000ffff0500ffff0000ffff0500fffc0000fffc0000aaa80000aa8800000000000000000000000000000000000000000000000000000000000000000000ffff0000ffff0500ffff0000ffff0500ff00000000000000aa000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 873, 923, 930, 972, 979, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c78813_0 : P.sumLeaves 26 80704512 853 = 1680860 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78813) (lo := 0) (len := 853) (W := 1680860) check rows elimOK (by decide) (by decide) cover78813 (by decide)
  decide +kernel

theorem c78813_1 : P.sumLeaves 26 80705365 171 = 5301751 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78813) (lo := 853) (len := 171) (W := 5301751) check rows elimOK (by decide) (by decide) cover78813 (by decide)
  decide +kernel

theorem h78813 : P.leaf 36 78813 = 6982611 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(853, 1680860), (171, 5301751)]) (.cons c78813_0 (.cons c78813_1 (.nil))) (by decide) (by decide))

theorem cover78814 : P.CoversSplit 26 10 78814 0xffff0000ffff0500ffff0000ffff050000000000000000000000000000000000050500000505000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 867, 873, 880, 972, 1315, 1658]) (by decide +kernel)

theorem c78814_0 : P.sumLeaves 26 80705536 1024 = 3299858 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78814) (lo := 0) (len := 1024) (W := 3299858) check rows elimOK (by decide) (by decide) cover78814 (by decide)
  decide +kernel

theorem h78814 : P.leaf 36 78814 = 3299858 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 3299858)]) (.cons c78814_0 (.nil)) (by decide) (by decide))

theorem cover78815 : P.CoversSplit 26 10 78815 0xffff0000ffff0500ffff0000ffff0500fffc0000fffc0000aaa80000aa8800000505000005050000000000000000000005040000050400000000000000000000ffff0000ffff0500ffff0000ffff0500ffcc000000000000aa880000000000000505000005050000000000000000000005040000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 873, 930, 972, 979, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c78815_0 : P.sumLeaves 26 80706560 511 = 17284509 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78815) (lo := 0) (len := 511) (W := 17284509) check rows elimOK (by decide) (by decide) cover78815 (by decide)
  decide +kernel

theorem c78815_1 : P.sumLeaves 26 80707071 469 = 36905957 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78815) (lo := 511) (len := 469) (W := 36905957) check rows elimOK (by decide) (by decide) cover78815 (by decide)
  decide +kernel

theorem c78815_2 : P.sumLeaves 26 80707540 44 = 20498469 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78815) (lo := 980) (len := 44) (W := 20498469) check rows elimOK (by decide) (by decide) cover78815 (by decide)
  decide +kernel

theorem h78815 : P.leaf 36 78815 = 74688935 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(511, 17284509), (469, 36905957), (44, 20498469)]) (.cons c78815_0 (.cons c78815_1 (.cons c78815_2 (.nil)))) (by decide) (by decide))

theorem cover78846 : P.CoversSplit 26 10 78846 0xfffffffafffffafafffffffafffffafa00000000000000000000000000000000fffff0f0fffff0f0aaaaa0a0aaaaa0a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [867, 873, 874, 972, 1315, 1658]) (by decide +kernel)

theorem c78846_0 : P.sumLeaves 26 80738304 924 = 8649604 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78846) (lo := 0) (len := 924) (W := 8649604) check rows elimOK (by decide) (by decide) cover78846 (by decide)
  decide +kernel

theorem c78846_1 : P.sumLeaves 26 80739228 100 = 18250538 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78846) (lo := 924) (len := 100) (W := 18250538) check rows elimOK (by decide) (by decide) cover78846 (by decide)
  decide +kernel

theorem h78846 : P.leaf 36 78846 = 26900142 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(924, 8649604), (100, 18250538)]) (.cons c78846_0 (.cons c78846_1 (.nil))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(78783, 360), (78793, 180), (78795, 720), (78798, 360), (78799, 360), (78811, 360), (78812, 360), (78813, 360), (78814, 720), (78815, 720), (78846, 180)]

theorem segOK : checkSeg 20 perms 78783 78847 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 78783 78847 4680 80837709840 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 80837709840)
    (SegSum.cons (w := 360) h78783 (SegSum.cons (w := 180) h78793 (SegSum.cons (w := 720) h78795 (SegSum.cons (w := 360) h78798 (SegSum.cons (w := 360) h78799 (SegSum.cons (w := 360) h78811 (SegSum.cons (w := 360) h78812 (SegSum.cons (w := 360) h78813 (SegSum.cons (w := 720) h78814 (SegSum.cons (w := 720) h78815 (SegSum.cons (w := 180) h78846 (show SegSum (P.leaf 36) [] 0 from rfl)))))))))))) (by decide)

end RACert.S6N0.C0.S48
