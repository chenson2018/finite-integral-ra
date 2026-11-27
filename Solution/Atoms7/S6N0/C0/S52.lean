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

namespace RACert.S6N0.C0.S52

open RACert RACert.Problem

theorem cover79655 : P.CoversSplit 26 10 79655 0xcc00cc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 538, 579, 930, 972, 979, 1266, 1658, 1665]) (by decide +kernel)

theorem c79655_0 : P.sumLeaves 26 81566720 1024 = 810040 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79655) (lo := 0) (len := 1024) (W := 810040) check rows elimOK (by decide) (by decide) cover79655 (by decide)
  decide +kernel

theorem h79655 : P.leaf 36 79655 = 810040 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 810040)]) (.cons c79655_0 (.nil)) (by decide) (by decide))

theorem cover79656 : P.CoversSplit 26 10 79656 0xa0a0a0a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 509, 538, 566, 579, 874, 923, 1273, 1658]) (by decide +kernel)

theorem c79656_0 : P.sumLeaves 26 81567744 1024 = 6272 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79656) (lo := 0) (len := 1024) (W := 6272) check rows elimOK (by decide) (by decide) cover79656 (by decide)
  decide +kernel

theorem h79656 : P.leaf 36 79656 = 6272 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 6272)]) (.cons c79656_0 (.nil)) (by decide) (by decide))

theorem cover79657 : P.CoversSplit 26 10 79657 0xa0a0a0a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 566, 579, 923, 979, 1273, 1322, 1658]) (by decide +kernel)

theorem c79657_0 : P.sumLeaves 26 81568768 1024 = 110336 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79657) (lo := 0) (len := 1024) (W := 110336) check rows elimOK (by decide) (by decide) cover79657 (by decide)
  decide +kernel

theorem h79657 : P.leaf 36 79657 = 110336 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 110336)]) (.cons c79657_0 (.nil)) (by decide) (by decide))

theorem cover79658 : P.CoversSplit 26 10 79658 0xa0a0a0a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [479, 481, 538, 874, 972, 1266, 1273, 1658]) (by decide +kernel)

theorem c79658_0 : P.sumLeaves 26 81569792 1024 = 100800 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79658) (lo := 0) (len := 1024) (W := 100800) check rows elimOK (by decide) (by decide) cover79658 (by decide)
  decide +kernel

theorem h79658 : P.leaf 36 79658 = 100800 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 100800)]) (.cons c79658_0 (.nil)) (by decide) (by decide))

theorem cover79659 : P.CoversSplit 26 10 79659 0xa0a0a0a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 579, 972, 979, 1266, 1273, 1322, 1658]) (by decide +kernel)

theorem c79659_0 : P.sumLeaves 26 81570816 1024 = 888384 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79659) (lo := 0) (len := 1024) (W := 888384) check rows elimOK (by decide) (by decide) cover79659 (by decide)
  decide +kernel

theorem h79659 : P.leaf 36 79659 = 888384 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 888384)]) (.cons c79659_0 (.nil)) (by decide) (by decide))

theorem cover79660 : P.CoversSplit 26 10 79660 0xfffffffa00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [538, 566, 579, 873, 874, 923, 972, 979, 1273, 1658]) (by decide +kernel)

theorem c79660_0 : P.sumLeaves 26 81571840 1024 = 176032 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79660) (lo := 0) (len := 1024) (W := 176032) check rows elimOK (by decide) (by decide) cover79660 (by decide)
  decide +kernel

theorem h79660 : P.leaf 36 79660 = 176032 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 176032)]) (.cons c79660_0 (.nil)) (by decide) (by decide))

theorem cover79661 : P.CoversSplit 26 10 79661 0xfffffffa00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [538, 566, 579, 923, 972, 979, 1273, 1322, 1658]) (by decide +kernel)

theorem c79661_0 : P.sumLeaves 26 81572864 1024 = 869712 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79661) (lo := 0) (len := 1024) (W := 869712) check rows elimOK (by decide) (by decide) cover79661 (by decide)
  decide +kernel

theorem h79661 : P.leaf 36 79661 = 869712 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 869712)]) (.cons c79661_0 (.nil)) (by decide) (by decide))

theorem cover79662 : P.CoversSplit 26 10 79662 0xfffffffa00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [538, 579, 873, 874, 972, 979, 1266, 1273, 1658]) (by decide +kernel)

theorem c79662_0 : P.sumLeaves 26 81573888 1024 = 697264 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79662) (lo := 0) (len := 1024) (W := 697264) check rows elimOK (by decide) (by decide) cover79662 (by decide)
  decide +kernel

theorem h79662 : P.leaf 36 79662 = 697264 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 697264)]) (.cons c79662_0 (.nil)) (by decide) (by decide))

theorem cover79663 : P.CoversSplit 26 10 79663 0xfffffffa00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [538, 579, 972, 979, 1266, 1273, 1315, 1322, 1658]) (by decide +kernel)

theorem c79663_0 : P.sumLeaves 26 81574912 1024 = 3892712 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79663) (lo := 0) (len := 1024) (W := 3892712) check rows elimOK (by decide) (by decide) cover79663 (by decide)
  decide +kernel

theorem h79663 : P.leaf 36 79663 = 3892712 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 3892712)]) (.cons c79663_0 (.nil)) (by decide) (by decide))

theorem cover79670 : P.CoversSplit 26 10 79670 0xcc00cc0000000000000000000000000000000000000000000000000000000000440040000000000044004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 538, 579, 873, 930, 972, 979, 1273, 1658, 1665]) (by decide +kernel)

theorem c79670_0 : P.sumLeaves 26 81582080 1024 = 889584 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79670) (lo := 0) (len := 1024) (W := 889584) check rows elimOK (by decide) (by decide) cover79670 (by decide)
  decide +kernel

theorem h79670 : P.leaf 36 79670 = 889584 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 889584)]) (.cons c79670_0 (.nil)) (by decide) (by decide))

theorem cover79671 : P.CoversSplit 26 10 79671 0xcc00cc0000000000000000000000000000000000000000000000000000000000440040000000000044004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 538, 579, 930, 972, 979, 1658, 1665]) (by decide +kernel)

theorem c79671_0 : P.sumLeaves 26 81583104 1024 = 4524360 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79671) (lo := 0) (len := 1024) (W := 4524360) check rows elimOK (by decide) (by decide) cover79671 (by decide)
  decide +kernel

theorem h79671 : P.leaf 36 79671 = 4524360 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 4524360)]) (.cons c79671_0 (.nil)) (by decide) (by decide))

theorem cover79672 : P.CoversSplit 26 10 79672 0xa0a0a0a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 579, 873, 874, 923, 1273, 1658]) (by decide +kernel)

theorem c79672_0 : P.sumLeaves 26 81584128 1024 = 34016 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79672) (lo := 0) (len := 1024) (W := 34016) check rows elimOK (by decide) (by decide) cover79672 (by decide)
  decide +kernel

theorem h79672 : P.leaf 36 79672 = 34016 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 34016)]) (.cons c79672_0 (.nil)) (by decide) (by decide))

theorem cover79673 : P.CoversSplit 26 10 79673 0xa0a0a0a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 579, 923, 930, 979, 1273, 1322, 1658]) (by decide +kernel)

theorem c79673_0 : P.sumLeaves 26 81585152 1024 = 538752 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79673) (lo := 0) (len := 1024) (W := 538752) check rows elimOK (by decide) (by decide) cover79673 (by decide)
  decide +kernel

theorem h79673 : P.leaf 36 79673 = 538752 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 538752)]) (.cons c79673_0 (.nil)) (by decide) (by decide))

theorem cover79674 : P.CoversSplit 26 10 79674 0xa0a0a0a000000000000000000000000000000000000000000000000000000000000000000000000000005050000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 579, 873, 874, 972, 1273, 1658]) (by decide +kernel)

theorem c79674_0 : P.sumLeaves 26 81586176 1024 = 1174048 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79674) (lo := 0) (len := 1024) (W := 1174048) check rows elimOK (by decide) (by decide) cover79674 (by decide)
  decide +kernel

theorem h79674 : P.leaf 36 79674 = 1174048 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1174048)]) (.cons c79674_0 (.nil)) (by decide) (by decide))

theorem cover79675 : P.CoversSplit 26 10 79675 0xa0a0a0a000000000000000000000000000000000000000000000000000000000000000000000000000005050000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 579, 972, 979, 1273, 1322, 1658]) (by decide +kernel)

theorem c79675_0 : P.sumLeaves 26 81587200 1024 = 4008272 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79675) (lo := 0) (len := 1024) (W := 4008272) check rows elimOK (by decide) (by decide) cover79675 (by decide)
  decide +kernel

theorem h79675 : P.leaf 36 79675 = 4008272 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 4008272)]) (.cons c79675_0 (.nil)) (by decide) (by decide))

theorem cover79676 : P.CoversSplit 26 10 79676 0xfffffffa00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [538, 579, 873, 874, 923, 972, 979, 1273, 1658]) (by decide +kernel)

theorem c79676_0 : P.sumLeaves 26 81588224 1024 = 2403192 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79676) (lo := 0) (len := 1024) (W := 2403192) check rows elimOK (by decide) (by decide) cover79676 (by decide)
  decide +kernel

theorem h79676 : P.leaf 36 79676 = 2403192 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 2403192)]) (.cons c79676_0 (.nil)) (by decide) (by decide))

theorem cover79677 : P.CoversSplit 26 10 79677 0xfffffffa00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [538, 579, 923, 930, 972, 979, 1273, 1315, 1322, 1658]) (by decide +kernel)

theorem c79677_0 : P.sumLeaves 26 81589248 1024 = 6476448 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79677) (lo := 0) (len := 1024) (W := 6476448) check rows elimOK (by decide) (by decide) cover79677 (by decide)
  decide +kernel

theorem h79677 : P.leaf 36 79677 = 6476448 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 6476448)]) (.cons c79677_0 (.nil)) (by decide) (by decide))

theorem cover79678 : P.CoversSplit 26 10 79678 0xfffffffa00000000000000000000000000000000000000000000000000000000555550500000000055555050000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [538, 579, 873, 874, 972, 979, 1273, 1315, 1658]) (by decide +kernel)

theorem c79678_0 : P.sumLeaves 26 81590272 1024 = 8615360 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79678) (lo := 0) (len := 1024) (W := 8615360) check rows elimOK (by decide) (by decide) cover79678 (by decide)
  decide +kernel

theorem h79678 : P.leaf 36 79678 = 8615360 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 8615360)]) (.cons c79678_0 (.nil)) (by decide) (by decide))

theorem cover79679 : P.CoversSplit 26 10 79679 0xfffffffa00000000000000000000000000000000000000000000000000000000555550500000000055555050000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [538, 579, 972, 979, 1273, 1315, 1322, 1658]) (by decide +kernel)

theorem c79679_0 : P.sumLeaves 26 81591296 1024 = 24553540 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79679) (lo := 0) (len := 1024) (W := 24553540) check rows elimOK (by decide) (by decide) cover79679 (by decide)
  decide +kernel

theorem h79679 : P.leaf 36 79679 = 24553540 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 24553540)]) (.cons c79679_0 (.nil)) (by decide) (by decide))

theorem cover79689 : P.CoversSplit 26 10 79689 0xa0a00000a0a000000000000000000000a0a00000a0a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000a0a00000a0a000000000000000000000a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [474, 481, 530, 579, 923, 930, 979, 1322]) (by decide +kernel)

theorem c79689_0 : P.sumLeaves 26 81601536 1024 = 109568 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79689) (lo := 0) (len := 1024) (W := 109568) check rows elimOK (by decide) (by decide) cover79689 (by decide)
  decide +kernel

theorem h79689 : P.leaf 36 79689 = 109568 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 109568)]) (.cons c79689_0 (.nil)) (by decide) (by decide))

theorem cover79691 : P.CoversSplit 26 10 79691 0xa0a00000a0a000000000000000000000a0a00000a0a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000a0a00000a0a000000000000000000000a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 523, 530, 579, 930, 972, 979, 1322]) (by decide +kernel)

theorem c79691_0 : P.sumLeaves 26 81603584 1024 = 532608 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79691) (lo := 0) (len := 1024) (W := 532608) check rows elimOK (by decide) (by decide) cover79691 (by decide)
  decide +kernel

theorem h79691 : P.leaf 36 79691 = 532608 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 532608)]) (.cons c79691_0 (.nil)) (by decide) (by decide))

theorem cover79692 : P.CoversSplit 26 10 79692 0xaaaa0000aaaa00000000000000000000aaa80000aaa800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [467, 530, 579, 880, 923, 979, 1658]) (by decide +kernel)

theorem c79692_0 : P.sumLeaves 26 81604608 1024 = 214416 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79692) (lo := 0) (len := 1024) (W := 214416) check rows elimOK (by decide) (by decide) cover79692 (by decide)
  decide +kernel

theorem h79692 : P.leaf 36 79692 = 214416 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 214416)]) (.cons c79692_0 (.nil)) (by decide) (by decide))

theorem cover79693 : P.CoversSplit 26 10 79693 0xaaaa0000aaaa00000000000000000000aaa80000aaa8000000000000000000000000000000000000000000000000000000000000000000000000000000000000aaaa0000aaaa00000000000000000000aa8800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 579, 923, 930, 979, 1322, 1658]) (by decide +kernel)

theorem c79693_0 : P.sumLeaves 26 81605632 1024 = 943008 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79693) (lo := 0) (len := 1024) (W := 943008) check rows elimOK (by decide) (by decide) cover79693 (by decide)
  decide +kernel

theorem h79693 : P.leaf 36 79693 = 943008 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 943008)]) (.cons c79693_0 (.nil)) (by decide) (by decide))

theorem cover79694 : P.CoversSplit 26 10 79694 0xaaaa0000aaaa00000000000000000000aaa80000aaa800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 579, 873, 880, 972, 979, 1266, 1658]) (by decide +kernel)

theorem c79694_0 : P.sumLeaves 26 81606656 1024 = 575624 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79694) (lo := 0) (len := 1024) (W := 575624) check rows elimOK (by decide) (by decide) cover79694 (by decide)
  decide +kernel

theorem h79694 : P.leaf 36 79694 = 575624 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 575624)]) (.cons c79694_0 (.nil)) (by decide) (by decide))

theorem cover79695 : P.CoversSplit 26 10 79695 0xaaaa0000aaaa00000000000000000000aaa80000aaa8000000000000000000000000000000000000000000000000000000000000000000000000000000000000aaaa0000aaaa00000000000000000000aa8800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 579, 930, 972, 979, 1266, 1273, 1322, 1658]) (by decide +kernel)

theorem c79695_0 : P.sumLeaves 26 81607680 1024 = 2753120 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79695) (lo := 0) (len := 1024) (W := 2753120) check rows elimOK (by decide) (by decide) cover79695 (by decide)
  decide +kernel

theorem h79695 : P.leaf 36 79695 = 2753120 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 2753120)]) (.cons c79695_0 (.nil)) (by decide) (by decide))

theorem cover79707 : P.CoversSplit 26 10 79707 0xa0a00000a0a000000000000000000000a0a00000a0a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000a0a00000a0a000000000000000000000a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 579, 873, 930, 972, 979, 1322]) (by decide +kernel)

theorem c79707_0 : P.sumLeaves 26 81619968 1024 = 4098208 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79707) (lo := 0) (len := 1024) (W := 4098208) check rows elimOK (by decide) (by decide) cover79707 (by decide)
  decide +kernel

theorem h79707 : P.leaf 36 79707 = 4098208 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 4098208)]) (.cons c79707_0 (.nil)) (by decide) (by decide))

theorem cover79708 : P.CoversSplit 26 10 79708 0xaaaa0000aaaa00000000000000000000aaa80000aaa800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [467, 530, 880, 923, 979, 1658]) (by decide +kernel)

theorem c79708_0 : P.sumLeaves 26 81620992 1024 = 4259076 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79708) (lo := 0) (len := 1024) (W := 4259076) check rows elimOK (by decide) (by decide) cover79708 (by decide)
  decide +kernel

theorem h79708 : P.leaf 36 79708 = 4259076 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 4259076)]) (.cons c79708_0 (.nil)) (by decide) (by decide))

theorem cover79709 : P.CoversSplit 26 10 79709 0xaaaa0000aaaa00000000000000000000aaa80000aaa8000000000000000000000000000000000000000000000000000000000000000000000000000000000000aaaa0000aaaa00000000000000000000aa8800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 579, 923, 930, 979, 1322, 1658]) (by decide +kernel)

theorem c79709_0 : P.sumLeaves 26 81622016 1024 = 10082304 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79709) (lo := 0) (len := 1024) (W := 10082304) check rows elimOK (by decide) (by decide) cover79709 (by decide)
  decide +kernel

theorem h79709 : P.leaf 36 79709 = 10082304 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 10082304)]) (.cons c79709_0 (.nil)) (by decide) (by decide))

theorem cover79710 : P.CoversSplit 26 10 79710 0xaaaa0000aaaa00000000000000000000aaa80000aaa800000000000000000000000000000000000005050000050500000000000000000000050400000500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 579, 873, 880, 979, 1315, 1658, 1665]) (by decide +kernel)

theorem c79710_0 : P.sumLeaves 26 81623040 1024 = 9591805 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79710) (lo := 0) (len := 1024) (W := 9591805) check rows elimOK (by decide) (by decide) cover79710 (by decide)
  decide +kernel

theorem h79710 : P.leaf 36 79710 = 9591805 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 9591805)]) (.cons c79710_0 (.nil)) (by decide) (by decide))

theorem cover79711 : P.CoversSplit 26 10 79711 0xaaaa0000aaaa00000000000000000000aaa80000aaa8000000000000000000000000000000000000050500000505000000000000000000000504000005000000aaaa0000aaaa00000000000000000000aa8800000000000000000000000000000000000000000000050500000505000000000000000000000504000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 579, 930, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c79711_0 : P.sumLeaves 26 81624064 1024 = 25977142 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79711) (lo := 0) (len := 1024) (W := 25977142) check rows elimOK (by decide) (by decide) cover79711 (by decide)
  decide +kernel

theorem h79711 : P.leaf 36 79711 = 25977142 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 25977142)]) (.cons c79711_0 (.nil)) (by decide) (by decide))

theorem cover79724 : P.CoversSplit 26 10 79724 0xfffffffafffffafa0000000000000000fffcfff8fffcc8c85554555055004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [579, 873, 874, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c79724_0 : P.sumLeaves 26 81637376 997 = 2703562 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79724) (lo := 0) (len := 997) (W := 2703562) check rows elimOK (by decide) (by decide) cover79724 (by decide)
  decide +kernel

theorem c79724_1 : P.sumLeaves 26 81638373 27 = 3642115 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79724) (lo := 997) (len := 27) (W := 3642115) check rows elimOK (by decide) (by decide) cover79724 (by decide)
  decide +kernel

theorem h79724 : P.leaf 36 79724 = 6345677 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(997, 2703562), (27, 3642115)]) (.cons c79724_0 (.cons c79724_1 (.nil))) (by decide) (by decide))

theorem cover79725 : P.CoversSplit 26 10 79725 0xfffffffafffffafa0000000000000000fffcfff8fffcc8c855545550550040000000000000000000000000000000000000000000000000000000000000000000fffffffafffffafa0000000000000000ffccffc8cc00c80055445540440040000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [579, 923, 930, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c79725_0 : P.sumLeaves 26 81638400 506 = 4546596 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79725) (lo := 0) (len := 506) (W := 4546596) check rows elimOK (by decide) (by decide) cover79725 (by decide)
  decide +kernel

theorem c79725_1 : P.sumLeaves 26 81638906 483 = 5295322 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79725) (lo := 506) (len := 483) (W := 5295322) check rows elimOK (by decide) (by decide) cover79725 (by decide)
  decide +kernel

theorem c79725_2 : P.sumLeaves 26 81639389 35 = 6595790 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79725) (lo := 989) (len := 35) (W := 6595790) check rows elimOK (by decide) (by decide) cover79725 (by decide)
  decide +kernel

theorem h79725 : P.leaf 36 79725 = 16437708 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(506, 4546596), (483, 5295322), (35, 6595790)]) (.cons c79725_0 (.cons c79725_1 (.cons c79725_2 (.nil)))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(79655, 720), (79656, 360), (79657, 720), (79658, 720), (79659, 720), (79660, 720), (79661, 720), (79662, 720), (79663, 720), (79670, 360), (79671, 360), (79672, 720), (79673, 720), (79674, 720), (79675, 720), (79676, 720), (79677, 720), (79678, 720), (79679, 720), (79689, 180), (79691, 720), (79692, 360), (79693, 720), (79694, 720), (79695, 720), (79707, 360), (79708, 720), (79709, 720), (79710, 720), (79711, 720), (79724, 360), (79725, 360)]

theorem segOK : checkSeg 20 perms 79655 79726 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 79655 79726 19980 90971351640 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 90971351640)
    (SegSum.cons (w := 720) h79655 (SegSum.cons (w := 360) h79656 (SegSum.cons (w := 720) h79657 (SegSum.cons (w := 720) h79658 (SegSum.cons (w := 720) h79659 (SegSum.cons (w := 720) h79660 (SegSum.cons (w := 720) h79661 (SegSum.cons (w := 720) h79662 (SegSum.cons (w := 720) h79663 (SegSum.cons (w := 360) h79670 (SegSum.cons (w := 360) h79671 (SegSum.cons (w := 720) h79672 (SegSum.cons (w := 720) h79673 (SegSum.cons (w := 720) h79674 (SegSum.cons (w := 720) h79675 (SegSum.cons (w := 720) h79676 (SegSum.cons (w := 720) h79677 (SegSum.cons (w := 720) h79678 (SegSum.cons (w := 720) h79679 (SegSum.cons (w := 180) h79689 (SegSum.cons (w := 720) h79691 (SegSum.cons (w := 360) h79692 (SegSum.cons (w := 720) h79693 (SegSum.cons (w := 720) h79694 (SegSum.cons (w := 720) h79695 (SegSum.cons (w := 360) h79707 (SegSum.cons (w := 720) h79708 (SegSum.cons (w := 720) h79709 (SegSum.cons (w := 720) h79710 (SegSum.cons (w := 720) h79711 (SegSum.cons (w := 360) h79724 (SegSum.cons (w := 360) h79725 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S52
