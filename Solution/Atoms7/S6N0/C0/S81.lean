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

namespace RACert.S6N0.C0.S81

open RACert RACert.Problem

theorem cover97783 : P.CoversSplit 26 10 97783 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 482, 489, 629, 636, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c97783_0 : P.sumLeaves 26 100129792 1024 = 10320176 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97783) (lo := 0) (len := 1024) (W := 10320176) check rows elimOK (by decide) (by decide) cover97783 (by decide)
  decide +kernel

theorem h97783 : P.leaf 36 97783 = 10320176 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 10320176)]) (.cons c97783_0 (.nil)) (by decide) (by decide))

theorem cover97787 : P.CoversSplit 26 10 97787 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 481, 482, 629, 636, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c97787_0 : P.sumLeaves 26 100133888 1024 = 8219805 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97787) (lo := 0) (len := 1024) (W := 8219805) check rows elimOK (by decide) (by decide) cover97787 (by decide)
  decide +kernel

theorem h97787 : P.leaf 36 97787 = 8219805 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 8219805)]) (.cons c97787_0 (.nil)) (by decide) (by decide))

theorem cover97788 : P.CoversSplit 26 10 97788 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 972, 979, 1266, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c97788_0 : P.sumLeaves 26 100134912 1024 = 13088244 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97788) (lo := 0) (len := 1024) (W := 13088244) check rows elimOK (by decide) (by decide) cover97788 (by decide)
  decide +kernel

theorem h97788 : P.leaf 36 97788 = 13088244 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 13088244)]) (.cons c97788_0 (.nil)) (by decide) (by decide))

theorem cover97789 : P.CoversSplit 26 10 97789 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 972, 979, 1266, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c97789_0 : P.sumLeaves 26 100135936 1024 = 13921772 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97789) (lo := 0) (len := 1024) (W := 13921772) check rows elimOK (by decide) (by decide) cover97789 (by decide)
  decide +kernel

theorem h97789 : P.leaf 36 97789 = 13921772 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 13921772)]) (.cons c97789_0 (.nil)) (by decide) (by decide))

theorem cover97791 : P.CoversSplit 26 10 97791 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 972, 979, 1266, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c97791_0 : P.sumLeaves 26 100137984 1024 = 15556414 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97791) (lo := 0) (len := 1024) (W := 15556414) check rows elimOK (by decide) (by decide) cover97791 (by decide)
  decide +kernel

theorem h97791 : P.leaf 36 97791 = 15556414 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 15556414)]) (.cons c97791_0 (.nil)) (by decide) (by decide))

theorem cover98035 : P.CoversSplit 26 10 98035 0xc000c000c000c000c000c000c000c0000000000000000000000000000000000000000000000000000000c0000000c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 587, 972, 979, 1658, 1665]) (by decide +kernel)

theorem c98035_0 : P.sumLeaves 26 100387840 1024 = 57646968 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98035) (lo := 0) (len := 1024) (W := 57646968) check rows elimOK (by decide) (by decide) cover98035 (by decide)
  decide +kernel

theorem h98035 : P.leaf 36 98035 = 57646968 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 57646968)]) (.cons c98035_0 (.nil)) (by decide) (by decide))

theorem cover98038 : P.CoversSplit 26 10 98038 0xcc00cc00cc00c800cc00cc00cc00c80000000000000000000000000000000000cc00c800cc00c800c000c000c000c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 587, 874, 972, 979, 1315, 1658]) (by decide +kernel)

theorem c98038_0 : P.sumLeaves 26 100390912 1024 = 157509264 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98038) (lo := 0) (len := 1024) (W := 157509264) check rows elimOK (by decide) (by decide) cover98038 (by decide)
  decide +kernel

theorem h98038 : P.leaf 36 98038 = 157509264 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 157509264)]) (.cons c98038_0 (.nil)) (by decide) (by decide))

theorem cover98039 : P.CoversSplit 26 10 98039 0xcc00cc00cc00c800cc00cc00cc00c80000000000000000000000000000000000cc00c800cc00c800c000c000c000c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 587, 972, 979, 1315, 1658]) (by decide +kernel)

theorem c98039_0 : P.sumLeaves 26 100391936 1024 = 241084462 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98039) (lo := 0) (len := 1024) (W := 241084462) check rows elimOK (by decide) (by decide) cover98039 (by decide)
  decide +kernel

theorem h98039 : P.leaf 36 98039 = 241084462 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 241084462)]) (.cons c98039_0 (.nil)) (by decide) (by decide))

theorem cover98040 : P.CoversSplit 26 10 98040 0xf0f0f0f0f0f0f0f0f0f0f0f5f0f0f0f000000000000000000000000000300000000000000000000000005050000050500000000000000000000000000000000000000000003000300000000000300030000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 587, 874, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c98040_0 : P.sumLeaves 26 100392960 1024 = 17088193 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98040) (lo := 0) (len := 1024) (W := 17088193) check rows elimOK (by decide) (by decide) cover98040 (by decide)
  decide +kernel

theorem h98040 : P.leaf 36 98040 = 17088193 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 17088193)]) (.cons c98040_0 (.nil)) (by decide) (by decide))

theorem cover98041 : P.CoversSplit 26 10 98041 0xf0f0f0f0f0f0f0f0f0f0f0f5f0f0f0f000000000000000000000000000300000000000000000000000005050000050500000000000000000000000000000000000000000003000300000000000300030000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 587, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c98041_0 : P.sumLeaves 26 100393984 1024 = 133308928 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98041) (lo := 0) (len := 1024) (W := 133308928) check rows elimOK (by decide) (by decide) cover98041 (by decide)
  decide +kernel

theorem h98041 : P.leaf 36 98041 = 133308928 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 133308928)]) (.cons c98041_0 (.nil)) (by decide) (by decide))

theorem cover98042 : P.CoversSplit 26 10 98042 0xf0f0f0f0f0f0f0f0f0f0f0f5f0f0f0f000000000000000000000000000300000000000000000000000005050000050500000000000000000000000000000000000000000003000300000000000300030000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 587, 874, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c98042_0 : P.sumLeaves 26 100395008 1024 = 289384086 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98042) (lo := 0) (len := 1024) (W := 289384086) check rows elimOK (by decide) (by decide) cover98042 (by decide)
  decide +kernel

theorem h98042 : P.leaf 36 98042 = 289384086 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 289384086)]) (.cons c98042_0 (.nil)) (by decide) (by decide))

theorem cover98043 : P.CoversSplit 26 10 98043 0xf0f0f0f0f0f0f0f0f0f0f0f5f0f0f0f000000000000000000000000000300000000000000000000000005050000050500000000000000000000000000000000000000000003000300000000000300030000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 587, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c98043_0 : P.sumLeaves 26 100396032 1024 = 479892306 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98043) (lo := 0) (len := 1024) (W := 479892306) check rows elimOK (by decide) (by decide) cover98043 (by decide)
  decide +kernel

theorem h98043 : P.leaf 36 98043 = 479892306 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 479892306)]) (.cons c98043_0 (.nil)) (by decide) (by decide))

theorem cover98046 : P.CoversSplit 26 10 98046 0xfffffffffffffafafffffffafffffafa00000000000000000000000000300000fffffafafffffafaf0f0f0f0f0f0f0f00000000000000000000000000030000000000000003300320000000000330032000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [587, 874, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c98046_0 : P.sumLeaves 26 100399104 760 = 159319234 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98046) (lo := 0) (len := 760) (W := 159319234) check rows elimOK (by decide) (by decide) cover98046 (by decide)
  decide +kernel

theorem c98046_1 : P.sumLeaves 26 100399864 232 = 485325768 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98046) (lo := 760) (len := 232) (W := 485325768) check rows elimOK (by decide) (by decide) cover98046 (by decide)
  decide +kernel

theorem c98046_2 : P.sumLeaves 26 100400096 32 = 337975688 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98046) (lo := 992) (len := 32) (W := 337975688) check rows elimOK (by decide) (by decide) cover98046 (by decide)
  decide +kernel

theorem h98046 : P.leaf 36 98046 = 982620690 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(760, 159319234), (232, 485325768), (32, 337975688)]) (.cons c98046_0 (.cons c98046_1 (.cons c98046_2 (.nil)))) (by decide) (by decide))

theorem cover98047 : P.CoversSplit 26 10 98047 0xfffffffffffffafafffffffafffffafa00000000000000000000000000300000fffffafafffffafaf0f0f0f0f0f0f0f00000000000000000000000000030000000000000003300320000000000330032000000000000000000000000000000000000000000330032000000000030003000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [587, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c98047_0 : P.sumLeaves 26 100400128 749 = 204951510 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98047) (lo := 0) (len := 749) (W := 204951510) check rows elimOK (by decide) (by decide) cover98047 (by decide)
  decide +kernel

theorem c98047_1 : P.sumLeaves 26 100400877 232 = 722554668 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98047) (lo := 749) (len := 232) (W := 722554668) check rows elimOK (by decide) (by decide) cover98047 (by decide)
  decide +kernel

theorem c98047_2 : P.sumLeaves 26 100401109 43 = 454230480 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98047) (lo := 981) (len := 43) (W := 454230480) check rows elimOK (by decide) (by decide) cover98047 (by decide)
  decide +kernel

theorem h98047 : P.leaf 36 98047 = 1381736658 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(749, 204951510), (232, 722554668), (43, 454230480)]) (.cons c98047_0 (.cons c98047_1 (.cons c98047_2 (.nil)))) (by decide) (by decide))

theorem cover98115 : P.CoversSplit 26 10 98115 0xa0000000a00000000000000000000000a0000000a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 523, 530, 579, 608, 972, 979, 1266]) (by decide +kernel)

theorem c98115_0 : P.sumLeaves 26 100469760 1024 = 10602376 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98115) (lo := 0) (len := 1024) (W := 10602376) check rows elimOK (by decide) (by decide) cover98115 (by decide)
  decide +kernel

theorem h98115 : P.leaf 36 98115 = 10602376 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 10602376)]) (.cons c98115_0 (.nil)) (by decide) (by decide))

theorem cover98117 : P.CoversSplit 26 10 98117 0xff000000ff0005000000000000000000ff000000ff0305000500000005000500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003300010000000000010001000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 579, 923, 972, 979, 1266, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c98117_0 : P.sumLeaves 26 100471808 1024 = 9149809 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98117) (lo := 0) (len := 1024) (W := 9149809) check rows elimOK (by decide) (by decide) cover98117 (by decide)
  decide +kernel

theorem h98117 : P.leaf 36 98117 = 9149809 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 9149809)]) (.cons c98117_0 (.nil)) (by decide) (by decide))

theorem cover98119 : P.CoversSplit 26 10 98119 0xff000000ff0005000000000000000000ff000000ff0305000500000005000500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003300010000000000010001000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 579, 972, 979, 1266, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c98119_0 : P.sumLeaves 26 100473856 1024 = 128653387 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98119) (lo := 0) (len := 1024) (W := 128653387) check rows elimOK (by decide) (by decide) cover98119 (by decide)
  decide +kernel

theorem h98119 : P.leaf 36 98119 = 128653387 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 128653387)]) (.cons c98119_0 (.nil)) (by decide) (by decide))

theorem cover98123 : P.CoversSplit 26 10 98123 0xa0a00000a0a000000000000000000000a0a00000a0a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000a0a00000a0a000000000000000000000a0a00000a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 523, 530, 579, 972, 979]) (by decide +kernel)

theorem c98123_0 : P.sumLeaves 26 100477952 1024 = 63690598 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98123) (lo := 0) (len := 1024) (W := 63690598) check rows elimOK (by decide) (by decide) cover98123 (by decide)
  decide +kernel

theorem h98123 : P.leaf 36 98123 = 63690598 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 63690598)]) (.cons c98123_0 (.nil)) (by decide) (by decide))

theorem cover98125 : P.CoversSplit 26 10 98125 0xffff0000ffff05050000000000000000ffff0000fffc050005050000050005000000000000000000000000000000000000000000000000000000000000000000ffff0000ffff05050000000000000000ffff0000ff00050005050000050005000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 579, 923, 972, 979, 1266, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c98125_0 : P.sumLeaves 26 100480000 882 = 19856339 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98125) (lo := 0) (len := 882) (W := 19856339) check rows elimOK (by decide) (by decide) cover98125 (by decide)
  decide +kernel

theorem c98125_1 : P.sumLeaves 26 100480882 142 = 47932580 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98125) (lo := 882) (len := 142) (W := 47932580) check rows elimOK (by decide) (by decide) cover98125 (by decide)
  decide +kernel

theorem h98125 : P.leaf 36 98125 = 67788919 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(882, 19856339), (142, 47932580)]) (.cons c98125_0 (.cons c98125_1 (.nil))) (by decide) (by decide))

theorem cover98127 : P.CoversSplit 26 10 98127 0xffff0000ffff05050000000000000000ffff0000fffc050005050000050005000000000000000000000000000000000000000000000000000000000000000000ffff0000ffff05050000000000000000ffff0000ff00050005050000050005000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 579, 972, 979, 1266, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c98127_0 : P.sumLeaves 26 100482048 882 = 162082153 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98127) (lo := 0) (len := 882) (W := 162082153) check rows elimOK (by decide) (by decide) cover98127 (by decide)
  decide +kernel

theorem c98127_1 : P.sumLeaves 26 100482930 142 = 320320048 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98127) (lo := 882) (len := 142) (W := 320320048) check rows elimOK (by decide) (by decide) cover98127 (by decide)
  decide +kernel

theorem h98127 : P.leaf 36 98127 = 482402201 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(882, 162082153), (142, 320320048)]) (.cons c98127_0 (.cons c98127_1 (.nil))) (by decide) (by decide))

theorem cover98131 : P.CoversSplit 26 10 98131 0xa0000000a00000000000000000000000a0000000a0000000000000000000000000000000000000000000050000000500000000000000000000000500000005000000000000000000000000000000000000000000a000000000000000000000000000000000000000000000000000000000000000000000000000000000000500 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 530, 579, 608, 972, 979, 1315]) (by decide +kernel)

theorem c98131_0 : P.sumLeaves 26 100486144 1024 = 21536061 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98131) (lo := 0) (len := 1024) (W := 21536061) check rows elimOK (by decide) (by decide) cover98131 (by decide)
  decide +kernel

theorem h98131 : P.leaf 36 98131 = 21536061 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 21536061)]) (.cons c98131_0 (.nil)) (by decide) (by decide))

theorem cover98132 : P.CoversSplit 26 10 98132 0xff000000ff0005000000000000000000ff000000ff0305000500000005000500050005000500050005000000050000000500050005010500050000000500000000000000000000000000000000000000000000003300010000000000010001000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 874, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c98132_0 : P.sumLeaves 26 100487168 1024 = 6525173 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98132) (lo := 0) (len := 1024) (W := 6525173) check rows elimOK (by decide) (by decide) cover98132 (by decide)
  decide +kernel

theorem h98132 : P.leaf 36 98132 = 6525173 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 6525173)]) (.cons c98132_0 (.nil)) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(97783, 90), (97787, 90), (97788, 180), (97789, 360), (97791, 180), (98035, 720), (98038, 360), (98039, 360), (98040, 360), (98041, 360), (98042, 720), (98043, 720), (98046, 360), (98047, 360), (98115, 180), (98117, 360), (98119, 360), (98123, 180), (98125, 360), (98127, 360), (98131, 360), (98132, 360)]

theorem segOK : checkSeg 20 perms 97783 98133 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 97783 98133 7740 1927179377370 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 1927179377370)
    (SegSum.cons (w := 90) h97783 (SegSum.cons (w := 90) h97787 (SegSum.cons (w := 180) h97788 (SegSum.cons (w := 360) h97789 (SegSum.cons (w := 180) h97791 (SegSum.cons (w := 720) h98035 (SegSum.cons (w := 360) h98038 (SegSum.cons (w := 360) h98039 (SegSum.cons (w := 360) h98040 (SegSum.cons (w := 360) h98041 (SegSum.cons (w := 720) h98042 (SegSum.cons (w := 720) h98043 (SegSum.cons (w := 360) h98046 (SegSum.cons (w := 360) h98047 (SegSum.cons (w := 180) h98115 (SegSum.cons (w := 360) h98117 (SegSum.cons (w := 360) h98119 (SegSum.cons (w := 180) h98123 (SegSum.cons (w := 360) h98125 (SegSum.cons (w := 360) h98127 (SegSum.cons (w := 360) h98131 (SegSum.cons (w := 360) h98132 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S81
