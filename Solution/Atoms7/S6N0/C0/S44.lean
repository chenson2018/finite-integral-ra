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

namespace RACert.S6N0.C0.S44

open RACert RACert.Problem

theorem cover77695 : P.CoversSplit 26 10 77695 0xfffafffafffaaaaa0000000000000000fffafffafff8aa8855505550550000005050000050500000505000005050000050500000505000005050000050000000fffafffafffaaaaa0000000000000000fffafffaff00aa0055505550550000005050000050500000505000005050000050500000500000005050000050000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [579, 881, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c77695_0 : P.sumLeaves 26 79559680 470 = 12184514 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 77695) (lo := 0) (len := 470) (W := 12184514) check rows elimOK (by decide) (by decide) cover77695 (by decide)
  decide +kernel

theorem c77695_1 : P.sumLeaves 26 79560150 387 = 33282568 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 77695) (lo := 470) (len := 387) (W := 33282568) check rows elimOK (by decide) (by decide) cover77695 (by decide)
  decide +kernel

theorem c77695_2 : P.sumLeaves 26 79560537 167 = 69746644 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 77695) (lo := 857) (len := 167) (W := 69746644) check rows elimOK (by decide) (by decide) cover77695 (by decide)
  decide +kernel

theorem h77695 : P.leaf 36 77695 = 115213726 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(470, 12184514), (387, 33282568), (167, 69746644)]) (.cons c77695_0 (.cons c77695_1 (.cons c77695_2 (.nil)))) (by decide) (by decide))

theorem cover77823 : P.CoversSplit 26 10 77823 0xfffafffafffaaaaafffafffafffaaaaafffafffafff8aa88aaaaaaaaaa88aa88fafaaaaafafaaaaaaaaaaaaaaaaaaaaafafaaaaafaf8aa88aaaaaaaaaa88aa88fffafffafffaaaaafffafffafffaaaaafffafffaffc8aa88aaaaaaaaaa88aa88fafaaaaafafaaaaaaaaaaaaaaaaaaaaafafaaaaafac8aa88aaaaaaaaaa88aa88 :=
  coversSplit check rows (by decide) (by decide) (xs := [881, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c77823_0 : P.sumLeaves 26 79690752 195 = 8818688 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 77823) (lo := 0) (len := 195) (W := 8818688) check rows elimOK (by decide) (by decide) cover77823 (by decide)
  decide +kernel

theorem c77823_1 : P.sumLeaves 26 79690947 171 = 70200772 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 77823) (lo := 195) (len := 171) (W := 70200772) check rows elimOK (by decide) (by decide) cover77823 (by decide)
  decide +kernel

theorem c77823_2 : P.sumLeaves 26 79691118 124 = 233719510 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 77823) (lo := 366) (len := 124) (W := 233719510) check rows elimOK (by decide) (by decide) cover77823 (by decide)
  decide +kernel

theorem c77823_3 : P.sumLeaves 26 79691242 173 = 244905556 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 77823) (lo := 490) (len := 173) (W := 244905556) check rows elimOK (by decide) (by decide) cover77823 (by decide)
  decide +kernel

theorem c77823_4 : P.sumLeaves 26 79691415 189 = 384812646 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 77823) (lo := 663) (len := 189) (W := 384812646) check rows elimOK (by decide) (by decide) cover77823 (by decide)
  decide +kernel

theorem c77823_5 : P.sumLeaves 26 79691604 121 = 406502884 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 77823) (lo := 852) (len := 121) (W := 406502884) check rows elimOK (by decide) (by decide) cover77823 (by decide)
  decide +kernel

theorem c77823_6 : P.sumLeaves 26 79691725 51 = 306383290 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 77823) (lo := 973) (len := 51) (W := 306383290) check rows elimOK (by decide) (by decide) cover77823 (by decide)
  decide +kernel

theorem h77823 : P.leaf 36 77823 = 1655343346 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(195, 8818688), (171, 70200772), (124, 233719510), (173, 244905556), (189, 384812646), (121, 406502884), (51, 306383290)]) (.cons c77823_0 (.cons c77823_1 (.cons c77823_2 (.cons c77823_3 (.cons c77823_4 (.cons c77823_5 (.cons c77823_6 (.nil)))))))) (by decide) (by decide))

theorem cover78030 : P.CoversSplit 26 10 78030 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 536, 537, 580, 587, 629, 930, 972, 1273, 1315, 1658]) (by decide +kernel)

theorem c78030_0 : P.sumLeaves 26 79902720 1024 = 1024 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78030) (lo := 0) (len := 1024) (W := 1024) check rows elimOK (by decide) (by decide) cover78030 (by decide)
  decide +kernel

theorem h78030 : P.leaf 36 78030 = 1024 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1024)]) (.cons c78030_0 (.nil)) (by decide) (by decide))

theorem cover78031 : P.CoversSplit 26 10 78031 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 536, 537, 580, 587, 629, 930, 972, 1273, 1315, 1658]) (by decide +kernel)

theorem c78031_0 : P.sumLeaves 26 79903744 1024 = 7296 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78031) (lo := 0) (len := 1024) (W := 7296) check rows elimOK (by decide) (by decide) cover78031 (by decide)
  decide +kernel

theorem h78031 : P.leaf 36 78031 = 7296 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 7296)]) (.cons c78031_0 (.nil)) (by decide) (by decide))

theorem cover78044 : P.CoversSplit 26 10 78044 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 479, 487, 537, 580, 587, 629, 930, 972, 1273, 1658]) (by decide +kernel)

theorem c78044_0 : P.sumLeaves 26 79917056 1024 = 4096 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78044) (lo := 0) (len := 1024) (W := 4096) check rows elimOK (by decide) (by decide) cover78044 (by decide)
  decide +kernel

theorem h78044 : P.leaf 36 78044 = 4096 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 4096)]) (.cons c78044_0 (.nil)) (by decide) (by decide))

theorem cover78045 : P.CoversSplit 26 10 78045 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 487, 530, 537, 580, 587, 629, 930, 972, 1273, 1315, 1658]) (by decide +kernel)

theorem c78045_0 : P.sumLeaves 26 79918080 1024 = 13824 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78045) (lo := 0) (len := 1024) (W := 13824) check rows elimOK (by decide) (by decide) cover78045 (by decide)
  decide +kernel

theorem h78045 : P.leaf 36 78045 = 13824 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 13824)]) (.cons c78045_0 (.nil)) (by decide) (by decide))

theorem cover78046 : P.CoversSplit 26 10 78046 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 537, 580, 587, 629, 930, 972, 1273, 1315, 1658]) (by decide +kernel)

theorem c78046_0 : P.sumLeaves 26 79919104 1024 = 6912 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78046) (lo := 0) (len := 1024) (W := 6912) check rows elimOK (by decide) (by decide) cover78046 (by decide)
  decide +kernel

theorem h78046 : P.leaf 36 78046 = 6912 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 6912)]) (.cons c78046_0 (.nil)) (by decide) (by decide))

theorem cover78047 : P.CoversSplit 26 10 78047 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 537, 580, 587, 629, 930, 972, 1273, 1315, 1658]) (by decide +kernel)

theorem c78047_0 : P.sumLeaves 26 79920128 1024 = 45888 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78047) (lo := 0) (len := 1024) (W := 45888) check rows elimOK (by decide) (by decide) cover78047 (by decide)
  decide +kernel

theorem h78047 : P.leaf 36 78047 = 45888 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 45888)]) (.cons c78047_0 (.nil)) (by decide) (by decide))

theorem cover78078 : P.CoversSplit 26 10 78078 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 580, 587, 629, 636, 867, 930, 972, 1273, 1315, 1658]) (by decide +kernel)

theorem c78078_0 : P.sumLeaves 26 79951872 1024 = 20936 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78078) (lo := 0) (len := 1024) (W := 20936) check rows elimOK (by decide) (by decide) cover78078 (by decide)
  decide +kernel

theorem h78078 : P.leaf 36 78078 = 20936 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 20936)]) (.cons c78078_0 (.nil)) (by decide) (by decide))

theorem cover78079 : P.CoversSplit 26 10 78079 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 580, 587, 629, 636, 867, 930, 972, 1273, 1315, 1658]) (by decide +kernel)

theorem c78079_0 : P.sumLeaves 26 79952896 1024 = 242240 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78079) (lo := 0) (len := 1024) (W := 242240) check rows elimOK (by decide) (by decide) cover78079 (by decide)
  decide +kernel

theorem h78079 : P.leaf 36 78079 = 242240 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 242240)]) (.cons c78079_0 (.nil)) (by decide) (by decide))

theorem cover78117 : P.CoversSplit 26 10 78117 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000200000000001000010000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [482, 489, 538, 629, 636, 930, 972, 979, 1315, 1658]) (by decide +kernel)

theorem c78117_0 : P.sumLeaves 26 79991808 1024 = 676 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78117) (lo := 0) (len := 1024) (W := 676) check rows elimOK (by decide) (by decide) cover78117 (by decide)
  decide +kernel

theorem h78117 : P.leaf 36 78117 = 676 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 676)]) (.cons c78117_0 (.nil)) (by decide) (by decide))

theorem cover78119 : P.CoversSplit 26 10 78119 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000200000000001000010000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [482, 489, 538, 629, 636, 930, 972, 1315, 1658]) (by decide +kernel)

theorem c78119_0 : P.sumLeaves 26 79993856 1024 = 5803 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78119) (lo := 0) (len := 1024) (W := 5803) check rows elimOK (by decide) (by decide) cover78119 (by decide)
  decide +kernel

theorem h78119 : P.leaf 36 78119 = 5803 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 5803)]) (.cons c78119_0 (.nil)) (by decide) (by decide))

theorem cover78121 : P.CoversSplit 26 10 78121 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [474, 481, 482, 531, 636, 979, 1273, 1315, 1658]) (by decide +kernel)

theorem c78121_0 : P.sumLeaves 26 79995904 1024 = 256 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78121) (lo := 0) (len := 1024) (W := 256) check rows elimOK (by decide) (by decide) cover78121 (by decide)
  decide +kernel

theorem h78121 : P.leaf 36 78121 = 256 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 256)]) (.cons c78121_0 (.nil)) (by decide) (by decide))

theorem cover78123 : P.CoversSplit 26 10 78123 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 482, 531, 636, 979, 1273, 1315, 1658]) (by decide +kernel)

theorem c78123_0 : P.sumLeaves 26 79997952 1024 = 832 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78123) (lo := 0) (len := 1024) (W := 832) check rows elimOK (by decide) (by decide) cover78123 (by decide)
  decide +kernel

theorem h78123 : P.leaf 36 78123 = 832 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 832)]) (.cons c78123_0 (.nil)) (by decide) (by decide))

theorem cover78125 : P.CoversSplit 26 10 78125 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 531, 538, 580, 629, 636, 972, 979, 1273, 1315, 1658]) (by decide +kernel)

theorem c78125_0 : P.sumLeaves 26 80000000 1024 = 1024 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78125) (lo := 0) (len := 1024) (W := 1024) check rows elimOK (by decide) (by decide) cover78125 (by decide)
  decide +kernel

theorem h78125 : P.leaf 36 78125 = 1024 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1024)]) (.cons c78125_0 (.nil)) (by decide) (by decide))

theorem cover78127 : P.CoversSplit 26 10 78127 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 531, 538, 580, 629, 636, 972, 979, 1273, 1315, 1658]) (by decide +kernel)

theorem c78127_0 : P.sumLeaves 26 80002048 1024 = 14560 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78127) (lo := 0) (len := 1024) (W := 14560) check rows elimOK (by decide) (by decide) cover78127 (by decide)
  decide +kernel

theorem h78127 : P.leaf 36 78127 = 14560 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 14560)]) (.cons c78127_0 (.nil)) (by decide) (by decide))

theorem cover78134 : P.CoversSplit 26 10 78134 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000200000000001000010000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [482, 489, 538, 629, 636, 930, 972, 1315, 1658]) (by decide +kernel)

theorem c78134_0 : P.sumLeaves 26 80009216 1024 = 5476 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78134) (lo := 0) (len := 1024) (W := 5476) check rows elimOK (by decide) (by decide) cover78134 (by decide)
  decide +kernel

theorem h78134 : P.leaf 36 78134 = 5476 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 5476)]) (.cons c78134_0 (.nil)) (by decide) (by decide))

theorem cover78135 : P.CoversSplit 26 10 78135 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000200000000001000010000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [482, 489, 538, 629, 636, 930, 972, 1315, 1658]) (by decide +kernel)

theorem c78135_0 : P.sumLeaves 26 80010240 1024 = 46543 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78135) (lo := 0) (len := 1024) (W := 46543) check rows elimOK (by decide) (by decide) cover78135 (by decide)
  decide +kernel

theorem h78135 : P.leaf 36 78135 = 46543 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 46543)]) (.cons c78135_0 (.nil)) (by decide) (by decide))

theorem cover78137 : P.CoversSplit 26 10 78137 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [474, 481, 482, 531, 636, 979, 1273, 1315, 1658]) (by decide +kernel)

theorem c78137_0 : P.sumLeaves 26 80012288 1024 = 4096 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78137) (lo := 0) (len := 1024) (W := 4096) check rows elimOK (by decide) (by decide) cover78137 (by decide)
  decide +kernel

theorem h78137 : P.leaf 36 78137 = 4096 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 4096)]) (.cons c78137_0 (.nil)) (by decide) (by decide))

theorem cover78139 : P.CoversSplit 26 10 78139 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 482, 531, 636, 979, 1273, 1315, 1658]) (by decide +kernel)

theorem c78139_0 : P.sumLeaves 26 80014336 1024 = 28672 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78139) (lo := 0) (len := 1024) (W := 28672) check rows elimOK (by decide) (by decide) cover78139 (by decide)
  decide +kernel

theorem h78139 : P.leaf 36 78139 = 28672 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 28672)]) (.cons c78139_0 (.nil)) (by decide) (by decide))

theorem cover78140 : P.CoversSplit 26 10 78140 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 531, 538, 580, 629, 636, 867, 972, 979, 1273, 1315, 1658]) (by decide +kernel)

theorem c78140_0 : P.sumLeaves 26 80015360 1024 = 3184 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78140) (lo := 0) (len := 1024) (W := 3184) check rows elimOK (by decide) (by decide) cover78140 (by decide)
  decide +kernel

theorem h78140 : P.leaf 36 78140 = 3184 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 3184)]) (.cons c78140_0 (.nil)) (by decide) (by decide))

theorem cover78141 : P.CoversSplit 26 10 78141 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 531, 538, 580, 629, 636, 972, 979, 1273, 1315, 1658]) (by decide +kernel)

theorem c78141_0 : P.sumLeaves 26 80016384 1024 = 11632 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78141) (lo := 0) (len := 1024) (W := 11632) check rows elimOK (by decide) (by decide) cover78141 (by decide)
  decide +kernel

theorem h78141 : P.leaf 36 78141 = 11632 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 11632)]) (.cons c78141_0 (.nil)) (by decide) (by decide))

theorem cover78142 : P.CoversSplit 26 10 78142 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 531, 538, 580, 629, 636, 867, 972, 979, 1273, 1315, 1658]) (by decide +kernel)

theorem c78142_0 : P.sumLeaves 26 80017408 1024 = 28132 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78142) (lo := 0) (len := 1024) (W := 28132) check rows elimOK (by decide) (by decide) cover78142 (by decide)
  decide +kernel

theorem h78142 : P.leaf 36 78142 = 28132 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 28132)]) (.cons c78142_0 (.nil)) (by decide) (by decide))

theorem cover78143 : P.CoversSplit 26 10 78143 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 531, 538, 580, 629, 636, 972, 979, 1273, 1315, 1658]) (by decide +kernel)

theorem c78143_0 : P.sumLeaves 26 80018432 1024 = 137364 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78143) (lo := 0) (len := 1024) (W := 137364) check rows elimOK (by decide) (by decide) cover78143 (by decide)
  decide +kernel

theorem h78143 : P.leaf 36 78143 = 137364 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 137364)]) (.cons c78143_0 (.nil)) (by decide) (by decide))

theorem cover78157 : P.CoversSplit 26 10 78157 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 523, 530, 531, 629, 636, 923, 972, 979, 1322, 1658, 1665]) (by decide +kernel)

theorem c78157_0 : P.sumLeaves 26 80032768 1024 = 1344 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78157) (lo := 0) (len := 1024) (W := 1344) check rows elimOK (by decide) (by decide) cover78157 (by decide)
  decide +kernel

theorem h78157 : P.leaf 36 78157 = 1344 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1344)]) (.cons c78157_0 (.nil)) (by decide) (by decide))

theorem cover78158 : P.CoversSplit 26 10 78158 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 579, 629, 636, 873, 879, 972, 979, 1322, 1658]) (by decide +kernel)

theorem c78158_0 : P.sumLeaves 26 80033792 1024 = 3584 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78158) (lo := 0) (len := 1024) (W := 3584) check rows elimOK (by decide) (by decide) cover78158 (by decide)
  decide +kernel

theorem h78158 : P.leaf 36 78158 = 3584 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 3584)]) (.cons c78158_0 (.nil)) (by decide) (by decide))

theorem cover78159 : P.CoversSplit 26 10 78159 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 523, 530, 531, 629, 636, 923, 972, 979, 1322, 1658, 1665]) (by decide +kernel)

theorem c78159_0 : P.sumLeaves 26 80034816 1024 = 18976 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78159) (lo := 0) (len := 1024) (W := 18976) check rows elimOK (by decide) (by decide) cover78159 (by decide)
  decide +kernel

theorem h78159 : P.leaf 36 78159 = 18976 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 18976)]) (.cons c78159_0 (.nil)) (by decide) (by decide))

theorem cover78172 : P.CoversSplit 26 10 78172 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 479, 530, 531, 629, 636, 867, 972, 979, 1322, 1658]) (by decide +kernel)

theorem c78172_0 : P.sumLeaves 26 80048128 1024 = 2048 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78172) (lo := 0) (len := 1024) (W := 2048) check rows elimOK (by decide) (by decide) cover78172 (by decide)
  decide +kernel

theorem h78172 : P.leaf 36 78172 = 2048 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 2048)]) (.cons c78172_0 (.nil)) (by decide) (by decide))

theorem cover78173 : P.CoversSplit 26 10 78173 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 579, 629, 636, 923, 972, 979, 1322, 1658, 1665]) (by decide +kernel)

theorem c78173_0 : P.sumLeaves 26 80049152 1024 = 10544 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78173) (lo := 0) (len := 1024) (W := 10544) check rows elimOK (by decide) (by decide) cover78173 (by decide)
  decide +kernel

theorem h78173 : P.leaf 36 78173 = 10544 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 10544)]) (.cons c78173_0 (.nil)) (by decide) (by decide))

theorem cover78174 : P.CoversSplit 26 10 78174 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 579, 629, 636, 867, 873, 972, 979, 1322, 1658]) (by decide +kernel)

theorem c78174_0 : P.sumLeaves 26 80050176 1024 = 28672 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78174) (lo := 0) (len := 1024) (W := 28672) check rows elimOK (by decide) (by decide) cover78174 (by decide)
  decide +kernel

theorem h78174 : P.leaf 36 78174 = 28672 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 28672)]) (.cons c78174_0 (.nil)) (by decide) (by decide))

theorem cover78175 : P.CoversSplit 26 10 78175 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 579, 629, 636, 923, 972, 979, 1322, 1658, 1665]) (by decide +kernel)

theorem c78175_0 : P.sumLeaves 26 80051200 1024 = 246112 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78175) (lo := 0) (len := 1024) (W := 246112) check rows elimOK (by decide) (by decide) cover78175 (by decide)
  decide +kernel

theorem h78175 : P.leaf 36 78175 = 246112 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 246112)]) (.cons c78175_0 (.nil)) (by decide) (by decide))

theorem cover78189 : P.CoversSplit 26 10 78189 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 579, 580, 629, 636, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c78189_0 : P.sumLeaves 26 80065536 1024 = 8192 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78189) (lo := 0) (len := 1024) (W := 8192) check rows elimOK (by decide) (by decide) cover78189 (by decide)
  decide +kernel

theorem h78189 : P.leaf 36 78189 = 8192 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 8192)]) (.cons c78189_0 (.nil)) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(77695, 180), (77823, 30), (78030, 180), (78031, 180), (78044, 360), (78045, 360), (78046, 720), (78047, 720), (78078, 180), (78079, 180), (78117, 360), (78119, 360), (78121, 720), (78123, 360), (78125, 720), (78127, 360), (78134, 180), (78135, 360), (78137, 720), (78139, 720), (78140, 720), (78141, 720), (78142, 720), (78143, 720), (78157, 720), (78158, 720), (78159, 720), (78172, 720), (78173, 720), (78174, 720), (78175, 720), (78189, 360)]

theorem segOK : checkSeg 20 perms 77695 78190 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 77695 78190 16230 70899132180 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 70899132180)
    (SegSum.cons (w := 180) h77695 (SegSum.cons (w := 30) h77823 (SegSum.cons (w := 180) h78030 (SegSum.cons (w := 180) h78031 (SegSum.cons (w := 360) h78044 (SegSum.cons (w := 360) h78045 (SegSum.cons (w := 720) h78046 (SegSum.cons (w := 720) h78047 (SegSum.cons (w := 180) h78078 (SegSum.cons (w := 180) h78079 (SegSum.cons (w := 360) h78117 (SegSum.cons (w := 360) h78119 (SegSum.cons (w := 720) h78121 (SegSum.cons (w := 360) h78123 (SegSum.cons (w := 720) h78125 (SegSum.cons (w := 360) h78127 (SegSum.cons (w := 180) h78134 (SegSum.cons (w := 360) h78135 (SegSum.cons (w := 720) h78137 (SegSum.cons (w := 720) h78139 (SegSum.cons (w := 720) h78140 (SegSum.cons (w := 720) h78141 (SegSum.cons (w := 720) h78142 (SegSum.cons (w := 720) h78143 (SegSum.cons (w := 720) h78157 (SegSum.cons (w := 720) h78158 (SegSum.cons (w := 720) h78159 (SegSum.cons (w := 720) h78172 (SegSum.cons (w := 720) h78173 (SegSum.cons (w := 720) h78174 (SegSum.cons (w := 720) h78175 (SegSum.cons (w := 360) h78189 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S44
