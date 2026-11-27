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

namespace RACert.S6N0.C0.S54

open RACert RACert.Problem

theorem cover79788 : P.CoversSplit 26 10 79788 0xfffffffa00000000fffffffa0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [538, 566, 873, 874, 923, 972, 979, 1273]) (by decide +kernel)

theorem c79788_0 : P.sumLeaves 26 81702912 1024 = 1338368 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79788) (lo := 0) (len := 1024) (W := 1338368) check rows elimOK (by decide) (by decide) cover79788 (by decide)
  decide +kernel

theorem h79788 : P.leaf 36 79788 = 1338368 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1338368)]) (.cons c79788_0 (.nil)) (by decide) (by decide))

theorem cover79789 : P.CoversSplit 26 10 79789 0xfffffffa00000000fffffffa0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [538, 566, 873, 923, 972, 979, 1273, 1322]) (by decide +kernel)

theorem c79789_0 : P.sumLeaves 26 81703936 1024 = 6660816 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79789) (lo := 0) (len := 1024) (W := 6660816) check rows elimOK (by decide) (by decide) cover79789 (by decide)
  decide +kernel

theorem h79789 : P.leaf 36 79789 = 6660816 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 6660816)]) (.cons c79789_0 (.nil)) (by decide) (by decide))

theorem cover79790 : P.CoversSplit 26 10 79790 0xfffffffa00000000fffffffa0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [538, 873, 874, 972, 979, 1266, 1273]) (by decide +kernel)

theorem c79790_0 : P.sumLeaves 26 81704960 1024 = 4072188 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79790) (lo := 0) (len := 1024) (W := 4072188) check rows elimOK (by decide) (by decide) cover79790 (by decide)
  decide +kernel

theorem h79790 : P.leaf 36 79790 = 4072188 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 4072188)]) (.cons c79790_0 (.nil)) (by decide) (by decide))

theorem cover79791 : P.CoversSplit 26 10 79791 0xfffffffa00000000fffffffa0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [538, 873, 972, 979, 1266, 1273, 1315, 1322]) (by decide +kernel)

theorem c79791_0 : P.sumLeaves 26 81705984 1024 = 17948714 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79791) (lo := 0) (len := 1024) (W := 17948714) check rows elimOK (by decide) (by decide) cover79791 (by decide)
  decide +kernel

theorem h79791 : P.leaf 36 79791 = 17948714 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 17948714)]) (.cons c79791_0 (.nil)) (by decide) (by decide))

theorem cover79798 : P.CoversSplit 26 10 79798 0xcc00cc0000000000cc00cc000000000000000000000000000000000000000000cc00c0000000000088008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 538, 873, 930, 972, 979, 1273, 1658, 1665]) (by decide +kernel)

theorem c79798_0 : P.sumLeaves 26 81713152 1024 = 3188480 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79798) (lo := 0) (len := 1024) (W := 3188480) check rows elimOK (by decide) (by decide) cover79798 (by decide)
  decide +kernel

theorem h79798 : P.leaf 36 79798 = 3188480 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 3188480)]) (.cons c79798_0 (.nil)) (by decide) (by decide))

theorem cover79799 : P.CoversSplit 26 10 79799 0xcc00cc0000000000cc00cc000000000000000000000000000000000000000000cc00c0000000000088008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 538, 873, 930, 972, 979, 1658, 1665]) (by decide +kernel)

theorem c79799_0 : P.sumLeaves 26 81714176 1024 = 17343352 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79799) (lo := 0) (len := 1024) (W := 17343352) check rows elimOK (by decide) (by decide) cover79799 (by decide)
  decide +kernel

theorem h79799 : P.leaf 36 79799 = 17343352 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 17343352)]) (.cons c79799_0 (.nil)) (by decide) (by decide))

theorem cover79800 : P.CoversSplit 26 10 79800 0xf0f0f0f500000000f0f0f0f50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 873, 874, 923, 972, 979, 1273]) (by decide +kernel)

theorem c79800_0 : P.sumLeaves 26 81715200 1024 = 509008 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79800) (lo := 0) (len := 1024) (W := 509008) check rows elimOK (by decide) (by decide) cover79800 (by decide)
  decide +kernel

theorem h79800 : P.leaf 36 79800 = 509008 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 509008)]) (.cons c79800_0 (.nil)) (by decide) (by decide))

theorem cover79801 : P.CoversSplit 26 10 79801 0xf0f0f0f500000000f0f0f0f50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 923, 930, 972, 979, 1273, 1315, 1322]) (by decide +kernel)

theorem c79801_0 : P.sumLeaves 26 81716224 1024 = 8269536 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79801) (lo := 0) (len := 1024) (W := 8269536) check rows elimOK (by decide) (by decide) cover79801 (by decide)
  decide +kernel

theorem h79801 : P.leaf 36 79801 = 8269536 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 8269536)]) (.cons c79801_0 (.nil)) (by decide) (by decide))

theorem cover79802 : P.CoversSplit 26 10 79802 0xf0f0f0f500000000f0f0f0f50000000000000000000000000000000000000000000050500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 873, 874, 972, 979, 1273, 1315, 1658]) (by decide +kernel)

theorem c79802_0 : P.sumLeaves 26 81717248 1024 = 7144416 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79802) (lo := 0) (len := 1024) (W := 7144416) check rows elimOK (by decide) (by decide) cover79802 (by decide)
  decide +kernel

theorem h79802 : P.leaf 36 79802 = 7144416 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 7144416)]) (.cons c79802_0 (.nil)) (by decide) (by decide))

theorem cover79803 : P.CoversSplit 26 10 79803 0xf0f0f0f500000000f0f0f0f50000000000000000000000000000000000000000000050500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 972, 979, 1273, 1315, 1322, 1658]) (by decide +kernel)

theorem c79803_0 : P.sumLeaves 26 81718272 1024 = 26333016 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79803) (lo := 0) (len := 1024) (W := 26333016) check rows elimOK (by decide) (by decide) cover79803 (by decide)
  decide +kernel

theorem h79803 : P.leaf 36 79803 = 26333016 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 26333016)]) (.cons c79803_0 (.nil)) (by decide) (by decide))

theorem cover79804 : P.CoversSplit 26 10 79804 0xfffffffa00000000fffffffa0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [538, 873, 874, 923, 972, 979, 1273]) (by decide +kernel)

theorem c79804_0 : P.sumLeaves 26 81719296 1024 = 9625652 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79804) (lo := 0) (len := 1024) (W := 9625652) check rows elimOK (by decide) (by decide) cover79804 (by decide)
  decide +kernel

theorem h79804 : P.leaf 36 79804 = 9625652 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 9625652)]) (.cons c79804_0 (.nil)) (by decide) (by decide))

theorem cover79805 : P.CoversSplit 26 10 79805 0xfffffffa00000000fffffffa0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [538, 873, 923, 930, 972, 979, 1273, 1315, 1322]) (by decide +kernel)

theorem c79805_0 : P.sumLeaves 26 81720320 1024 = 30829228 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79805) (lo := 0) (len := 1024) (W := 30829228) check rows elimOK (by decide) (by decide) cover79805 (by decide)
  decide +kernel

theorem h79805 : P.leaf 36 79805 = 30829228 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 30829228)]) (.cons c79805_0 (.nil)) (by decide) (by decide))

theorem cover79806 : P.CoversSplit 26 10 79806 0xfffffffa00000000fffffffa0000000000000000000000000000000000000000fffff0f000000000aaaaa0a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [538, 873, 874, 972, 979, 1273, 1315, 1658]) (by decide +kernel)

theorem c79806_0 : P.sumLeaves 26 81721344 1024 = 34132756 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79806) (lo := 0) (len := 1024) (W := 34132756) check rows elimOK (by decide) (by decide) cover79806 (by decide)
  decide +kernel

theorem h79806 : P.leaf 36 79806 = 34132756 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 34132756)]) (.cons c79806_0 (.nil)) (by decide) (by decide))

theorem cover79807 : P.CoversSplit 26 10 79807 0xfffffffa00000000fffffffa0000000000000000000000000000000000000000fffff0f000000000aaaaa0a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [538, 873, 972, 979, 1273, 1315, 1322, 1658]) (by decide +kernel)

theorem c79807_0 : P.sumLeaves 26 81722368 1024 = 109033368 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79807) (lo := 0) (len := 1024) (W := 109033368) check rows elimOK (by decide) (by decide) cover79807 (by decide)
  decide +kernel

theorem h79807 : P.leaf 36 79807 = 109033368 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 109033368)]) (.cons c79807_0 (.nil)) (by decide) (by decide))

theorem cover79817 : P.CoversSplit 26 10 79817 0xf0f00000f0f00005f0f00000f0f00005f0f00000f0f00000a0a00000a08000000000000000000000000000000000000000000000000000000000000000000000f0f00000f0f00005f0f00000f0f00005f000000000000000a0000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 923, 930, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c79817_0 : P.sumLeaves 26 81732608 1015 = 1216240 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79817) (lo := 0) (len := 1015) (W := 1216240) check rows elimOK (by decide) (by decide) cover79817 (by decide)
  decide +kernel

theorem c79817_1 : P.sumLeaves 26 81733623 9 = 339968 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79817) (lo := 1015) (len := 9) (W := 339968) check rows elimOK (by decide) (by decide) cover79817 (by decide)
  decide +kernel

theorem h79817 : P.leaf 36 79817 = 1556208 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1015, 1216240), (9, 339968)]) (.cons c79817_0 (.cons c79817_1 (.nil))) (by decide) (by decide))

theorem cover79819 : P.CoversSplit 26 10 79819 0xf0f00000f0f00005f0f00000f0f00005f0f00000f0f00000a0a00000a08000000000000000000000000000000000000000000000000000000000000000000000f0f00000f0f00005f0f00000f0f00005f000000000000000a0000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 930, 972, 979, 1266, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c79819_0 : P.sumLeaves 26 81734656 1015 = 6388102 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79819) (lo := 0) (len := 1015) (W := 6388102) check rows elimOK (by decide) (by decide) cover79819 (by decide)
  decide +kernel

theorem c79819_1 : P.sumLeaves 26 81735671 9 = 1216512 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79819) (lo := 1015) (len := 9) (W := 1216512) check rows elimOK (by decide) (by decide) cover79819 (by decide)
  decide +kernel

theorem h79819 : P.leaf 36 79819 = 7604614 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1015, 6388102), (9, 1216512)]) (.cons c79819_0 (.cons c79819_1 (.nil))) (by decide) (by decide))

theorem cover79820 : P.CoversSplit 26 10 79820 0xffff0000ffff0000ffff0000ffff0000fffc0000fffc0000aaa80000aa880000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [467, 880, 923, 979, 1658, 1665]) (by decide +kernel)

theorem c79820_0 : P.sumLeaves 26 81735680 1015 = 2478592 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79820) (lo := 0) (len := 1015) (W := 2478592) check rows elimOK (by decide) (by decide) cover79820 (by decide)
  decide +kernel

theorem c79820_1 : P.sumLeaves 26 81736695 9 = 691592 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79820) (lo := 1015) (len := 9) (W := 691592) check rows elimOK (by decide) (by decide) cover79820 (by decide)
  decide +kernel

theorem h79820 : P.leaf 36 79820 = 3170184 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1015, 2478592), (9, 691592)]) (.cons c79820_0 (.cons c79820_1 (.nil))) (by decide) (by decide))

theorem cover79821 : P.CoversSplit 26 10 79821 0xffff0000ffff0500ffff0000ffff0500fffc0000fffc0000aaa80000aa8800000000000000000000000000000000000000000000000000000000000000000000ffff0000ffff0500ffff0000ffff0500ffcc000000000000aa880000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 923, 930, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c79821_0 : P.sumLeaves 26 81736704 827 = 3300324 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79821) (lo := 0) (len := 827) (W := 3300324) check rows elimOK (by decide) (by decide) cover79821 (by decide)
  decide +kernel

theorem c79821_1 : P.sumLeaves 26 81737531 194 = 9062096 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79821) (lo := 827) (len := 194) (W := 9062096) check rows elimOK (by decide) (by decide) cover79821 (by decide)
  decide +kernel

theorem c79821_2 : P.sumLeaves 26 81737725 3 = 882752 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79821) (lo := 1021) (len := 3) (W := 882752) check rows elimOK (by decide) (by decide) cover79821 (by decide)
  decide +kernel

theorem h79821 : P.leaf 36 79821 = 13245172 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(827, 3300324), (194, 9062096), (3, 882752)]) (.cons c79821_0 (.cons c79821_1 (.cons c79821_2 (.nil)))) (by decide) (by decide))

theorem cover79822 : P.CoversSplit 26 10 79822 0xffff0000ffff0500ffff0000ffff0500fffc0000fffc0000aaa80000aa880000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 873, 880, 972, 979, 1266, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c79822_0 : P.sumLeaves 26 81737728 1011 = 7327604 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79822) (lo := 0) (len := 1011) (W := 7327604) check rows elimOK (by decide) (by decide) cover79822 (by decide)
  decide +kernel

theorem c79822_1 : P.sumLeaves 26 81738739 13 = 1751152 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79822) (lo := 1011) (len := 13) (W := 1751152) check rows elimOK (by decide) (by decide) cover79822 (by decide)
  decide +kernel

theorem h79822 : P.leaf 36 79822 = 9078756 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1011, 7327604), (13, 1751152)]) (.cons c79822_0 (.cons c79822_1 (.nil))) (by decide) (by decide))

theorem cover79823 : P.CoversSplit 26 10 79823 0xffff0000ffff0500ffff0000ffff0500fffc0000fffc0000aaa80000aa8800000000000000000000000000000000000000000000000000000000000000000000ffff0000ffff0500ffff0000ffff0500ffcc000000000000aa880000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 930, 972, 979, 1266, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c79823_0 : P.sumLeaves 26 81738752 827 = 12151396 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79823) (lo := 0) (len := 827) (W := 12151396) check rows elimOK (by decide) (by decide) cover79823 (by decide)
  decide +kernel

theorem c79823_1 : P.sumLeaves 26 81739579 194 = 28792548 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79823) (lo := 827) (len := 194) (W := 28792548) check rows elimOK (by decide) (by decide) cover79823 (by decide)
  decide +kernel

theorem c79823_2 : P.sumLeaves 26 81739773 3 = 1643440 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79823) (lo := 1021) (len := 3) (W := 1643440) check rows elimOK (by decide) (by decide) cover79823 (by decide)
  decide +kernel

theorem h79823 : P.leaf 36 79823 = 42587384 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(827, 12151396), (194, 28792548), (3, 1643440)]) (.cons c79823_0 (.cons c79823_1 (.cons c79823_2 (.nil)))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(79788, 720), (79789, 720), (79790, 720), (79791, 720), (79798, 360), (79799, 360), (79800, 720), (79801, 720), (79802, 720), (79803, 720), (79804, 720), (79805, 720), (79806, 720), (79807, 720), (79817, 360), (79819, 720), (79820, 720), (79821, 720), (79822, 720), (79823, 720)]

theorem segOK : checkSeg 20 perms 79788 79835 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 79788 79835 13320 246691581120 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 246691581120)
    (SegSum.cons (w := 720) h79788 (SegSum.cons (w := 720) h79789 (SegSum.cons (w := 720) h79790 (SegSum.cons (w := 720) h79791 (SegSum.cons (w := 360) h79798 (SegSum.cons (w := 360) h79799 (SegSum.cons (w := 720) h79800 (SegSum.cons (w := 720) h79801 (SegSum.cons (w := 720) h79802 (SegSum.cons (w := 720) h79803 (SegSum.cons (w := 720) h79804 (SegSum.cons (w := 720) h79805 (SegSum.cons (w := 720) h79806 (SegSum.cons (w := 720) h79807 (SegSum.cons (w := 360) h79817 (SegSum.cons (w := 720) h79819 (SegSum.cons (w := 720) h79820 (SegSum.cons (w := 720) h79821 (SegSum.cons (w := 720) h79822 (SegSum.cons (w := 720) h79823 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S54
