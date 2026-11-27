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

namespace RACert.S6N0.C0.S46

open RACert RACert.Problem

theorem cover78593 : P.CoversSplit 26 10 78593 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [474, 481, 489, 530, 538, 559, 579, 923, 930, 972, 979]) (by decide +kernel)

theorem c78593_0 : P.sumLeaves 26 80479232 1024 = 64 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78593) (lo := 0) (len := 1024) (W := 64) check rows elimOK (by decide) (by decide) cover78593 (by decide)
  decide +kernel

theorem h78593 : P.leaf 36 78593 = 64 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 64)]) (.cons c78593_0 (.nil)) (by decide) (by decide))

theorem cover78595 : P.CoversSplit 26 10 78595 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 523, 530, 538, 579, 608, 930, 972, 979, 1266]) (by decide +kernel)

theorem c78595_0 : P.sumLeaves 26 80481280 1024 = 512 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78595) (lo := 0) (len := 1024) (W := 512) check rows elimOK (by decide) (by decide) cover78595 (by decide)
  decide +kernel

theorem h78595 : P.leaf 36 78595 = 512 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 512)]) (.cons c78595_0 (.nil)) (by decide) (by decide))

theorem cover78599 : P.CoversSplit 26 10 78599 0x8800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 523, 530, 538, 930, 972, 979, 1266, 1315, 1658, 1665]) (by decide +kernel)

theorem c78599_0 : P.sumLeaves 26 80485376 1024 = 6272 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78599) (lo := 0) (len := 1024) (W := 6272) check rows elimOK (by decide) (by decide) cover78599 (by decide)
  decide +kernel

theorem h78599 : P.leaf 36 78599 = 6272 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 6272)]) (.cons c78599_0 (.nil)) (by decide) (by decide))

theorem cover78601 : P.CoversSplit 26 10 78601 0xa0a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [474, 481, 530, 538, 566, 579, 923, 930, 1273, 1322]) (by decide +kernel)

theorem c78601_0 : P.sumLeaves 26 80487424 1024 = 1024 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78601) (lo := 0) (len := 1024) (W := 1024) check rows elimOK (by decide) (by decide) cover78601 (by decide)
  decide +kernel

theorem h78601 : P.leaf 36 78601 = 1024 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1024)]) (.cons c78601_0 (.nil)) (by decide) (by decide))

theorem cover78603 : P.CoversSplit 26 10 78603 0xa0a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 523, 530, 538, 579, 615, 930, 972, 979, 1273, 1322]) (by decide +kernel)

theorem c78603_0 : P.sumLeaves 26 80489472 1024 = 6272 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78603) (lo := 0) (len := 1024) (W := 6272) check rows elimOK (by decide) (by decide) cover78603 (by decide)
  decide +kernel

theorem h78603 : P.leaf 36 78603 = 6272 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 6272)]) (.cons c78603_0 (.nil)) (by decide) (by decide))

theorem cover78607 : P.CoversSplit 26 10 78607 0xaaaa000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000aa880000aa000a0000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [523, 530, 538, 930, 979, 1266, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c78607_0 : P.sumLeaves 26 80493568 1024 = 65280 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78607) (lo := 0) (len := 1024) (W := 65280) check rows elimOK (by decide) (by decide) cover78607 (by decide)
  decide +kernel

theorem h78607 : P.leaf 36 78607 = 65280 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 65280)]) (.cons c78607_0 (.nil)) (by decide) (by decide))

theorem cover78612 : P.CoversSplit 26 10 78612 0x8800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000222200002200000011110000110000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [467, 489, 530, 538, 923, 930, 979, 1658, 1665]) (by decide +kernel)

theorem c78612_0 : P.sumLeaves 26 80498688 1024 = 4256 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78612) (lo := 0) (len := 1024) (W := 4256) check rows elimOK (by decide) (by decide) cover78612 (by decide)
  decide +kernel

theorem h78612 : P.leaf 36 78612 = 4256 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 4256)]) (.cons c78612_0 (.nil)) (by decide) (by decide))

theorem cover78613 : P.CoversSplit 26 10 78613 0x8800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 538, 579, 923, 930, 972, 979, 1315, 1658, 1665]) (by decide +kernel)

theorem c78613_0 : P.sumLeaves 26 80499712 1024 = 6656 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78613) (lo := 0) (len := 1024) (W := 6656) check rows elimOK (by decide) (by decide) cover78613 (by decide)
  decide +kernel

theorem h78613 : P.leaf 36 78613 = 6656 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 6656)]) (.cons c78613_0 (.nil)) (by decide) (by decide))

theorem cover78614 : P.CoversSplit 26 10 78614 0x8800000000000000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000222200002200000011110000110001000000000000000000000000000000000000000000000000000101000001000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 538, 579, 873, 930, 972, 979, 1315, 1658, 1665]) (by decide +kernel)

theorem c78614_0 : P.sumLeaves 26 80500736 1024 = 24548 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78614) (lo := 0) (len := 1024) (W := 24548) check rows elimOK (by decide) (by decide) cover78614 (by decide)
  decide +kernel

theorem h78614 : P.leaf 36 78614 = 24548 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 24548)]) (.cons c78614_0 (.nil)) (by decide) (by decide))

theorem cover78615 : P.CoversSplit 26 10 78615 0x8800000000000000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 538, 579, 930, 972, 979, 1315, 1658, 1665]) (by decide +kernel)

theorem c78615_0 : P.sumLeaves 26 80501760 1024 = 87808 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78615) (lo := 0) (len := 1024) (W := 87808) check rows elimOK (by decide) (by decide) cover78615 (by decide)
  decide +kernel

theorem h78615 : P.leaf 36 78615 = 87808 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 87808)]) (.cons c78615_0 (.nil)) (by decide) (by decide))

theorem cover78617 : P.CoversSplit 26 10 78617 0xa0a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [474, 481, 530, 538, 579, 615, 923, 930, 1273, 1322]) (by decide +kernel)

theorem c78617_0 : P.sumLeaves 26 80503808 1024 = 7168 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78617) (lo := 0) (len := 1024) (W := 7168) check rows elimOK (by decide) (by decide) cover78617 (by decide)
  decide +kernel

theorem h78617 : P.leaf 36 78617 = 7168 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 7168)]) (.cons c78617_0 (.nil)) (by decide) (by decide))

theorem cover78619 : P.CoversSplit 26 10 78619 0xa0a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 538, 579, 615, 873, 930, 972, 979, 1273, 1322]) (by decide +kernel)

theorem c78619_0 : P.sumLeaves 26 80505856 1024 = 44800 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78619) (lo := 0) (len := 1024) (W := 44800) check rows elimOK (by decide) (by decide) cover78619 (by decide)
  decide +kernel

theorem h78619 : P.leaf 36 78619 = 44800 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 44800)]) (.cons c78619_0 (.nil)) (by decide) (by decide))

theorem cover78620 : P.CoversSplit 26 10 78620 0xaaaa000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [467, 530, 538, 867, 923, 1273, 1322, 1658]) (by decide +kernel)

theorem c78620_0 : P.sumLeaves 26 80506880 1024 = 7168 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78620) (lo := 0) (len := 1024) (W := 7168) check rows elimOK (by decide) (by decide) cover78620 (by decide)
  decide +kernel

theorem h78620 : P.leaf 36 78620 = 7168 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 7168)]) (.cons c78620_0 (.nil)) (by decide) (by decide))

theorem cover78621 : P.CoversSplit 26 10 78621 0xaaaa000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000220000002200000001000000010001000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 538, 579, 923, 930, 972, 979, 1273, 1315, 1322, 1658]) (by decide +kernel)

theorem c78621_0 : P.sumLeaves 26 80507904 1024 = 41232 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78621) (lo := 0) (len := 1024) (W := 41232) check rows elimOK (by decide) (by decide) cover78621 (by decide)
  decide +kernel

theorem h78621 : P.leaf 36 78621 = 41232 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 41232)]) (.cons c78621_0 (.nil)) (by decide) (by decide))

theorem cover78622 : P.CoversSplit 26 10 78622 0xaaaa000000000000000000000000000000000000000000000000000000000000000000000000000005050000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 538, 579, 867, 873, 972, 1273, 1315, 1322, 1658]) (by decide +kernel)

theorem c78622_0 : P.sumLeaves 26 80508928 1024 = 63840 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78622) (lo := 0) (len := 1024) (W := 63840) check rows elimOK (by decide) (by decide) cover78622 (by decide)
  decide +kernel

theorem h78622 : P.leaf 36 78622 = 63840 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 63840)]) (.cons c78622_0 (.nil)) (by decide) (by decide))

theorem cover78623 : P.CoversSplit 26 10 78623 0xaaaa000000000000000000000000000000000000000000000000000000000000000000000000000005050000000000000000000000000000000000000000000000000000000000000000000000000000220000002200000001000000010001000000000000000000000000000000000000000000000000000100000001000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 538, 579, 930, 972, 979, 1273, 1315, 1322, 1658]) (by decide +kernel)

theorem c78623_0 : P.sumLeaves 26 80509952 1024 = 486690 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78623) (lo := 0) (len := 1024) (W := 486690) check rows elimOK (by decide) (by decide) cover78623 (by decide)
  decide +kernel

theorem h78623 : P.leaf 36 78623 = 486690 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 486690)]) (.cons c78623_0 (.nil)) (by decide) (by decide))

theorem cover78646 : P.CoversSplit 26 10 78646 0xcc00cc0000000000000000000000000000000000000000000000000000000000440040000000000044004000000000000000000000000000000000000000000000000000000000000000000000000000333333303300300011111110110010000000000000000000000000000000000011111010110010001111101011001000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 538, 579, 873, 930, 972, 979, 1315, 1658, 1665]) (by decide +kernel)

theorem c78646_0 : P.sumLeaves 26 80533504 1024 = 181900 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78646) (lo := 0) (len := 1024) (W := 181900) check rows elimOK (by decide) (by decide) cover78646 (by decide)
  decide +kernel

theorem h78646 : P.leaf 36 78646 = 181900 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 181900)]) (.cons c78646_0 (.nil)) (by decide) (by decide))

theorem cover78647 : P.CoversSplit 26 10 78647 0xcc00cc0000000000000000000000000000000000000000000000000000000000440040000000000044004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 538, 579, 873, 930, 972, 979, 1658, 1665]) (by decide +kernel)

theorem c78647_0 : P.sumLeaves 26 80534528 1024 = 814304 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78647) (lo := 0) (len := 1024) (W := 814304) check rows elimOK (by decide) (by decide) cover78647 (by decide)
  decide +kernel

theorem h78647 : P.leaf 36 78647 = 814304 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 814304)]) (.cons c78647_0 (.nil)) (by decide) (by decide))

theorem cover78648 : P.CoversSplit 26 10 78648 0xa0a0a0a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 579, 867, 873, 874, 923, 1273, 1658]) (by decide +kernel)

theorem c78648_0 : P.sumLeaves 26 80535552 1024 = 7168 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78648) (lo := 0) (len := 1024) (W := 7168) check rows elimOK (by decide) (by decide) cover78648 (by decide)
  decide +kernel

theorem h78648 : P.leaf 36 78648 = 7168 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 7168)]) (.cons c78648_0 (.nil)) (by decide) (by decide))

theorem cover78649 : P.CoversSplit 26 10 78649 0xa0a0a0a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000200020002000200000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [474, 481, 538, 923, 930, 1273, 1322, 1658]) (by decide +kernel)

theorem c78649_0 : P.sumLeaves 26 80536576 1024 = 78464 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78649) (lo := 0) (len := 1024) (W := 78464) check rows elimOK (by decide) (by decide) cover78649 (by decide)
  decide +kernel

theorem h78649 : P.leaf 36 78649 = 78464 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 78464)]) (.cons c78649_0 (.nil)) (by decide) (by decide))

theorem cover78650 : P.CoversSplit 26 10 78650 0xa0a0a0a000000000000000000000000000000000000000000000000000000000000000000000000000005050000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 579, 867, 873, 874, 972, 1273, 1658]) (by decide +kernel)

theorem c78650_0 : P.sumLeaves 26 80537600 1024 = 118120 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78650) (lo := 0) (len := 1024) (W := 118120) check rows elimOK (by decide) (by decide) cover78650 (by decide)
  decide +kernel

theorem h78650 : P.leaf 36 78650 = 118120 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 118120)]) (.cons c78650_0 (.nil)) (by decide) (by decide))

theorem cover78651 : P.CoversSplit 26 10 78651 0xa0a0a0a000000000000000000000000000000000000000000000000000000000000000000000000000005050000000000000000000000000000000000000000000000000000000000000000000000000200020002000200000000000000000000000000000000000000000000000000000000000000000000000100000001000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 579, 930, 972, 979, 1273, 1322, 1658]) (by decide +kernel)

theorem c78651_0 : P.sumLeaves 26 80538624 1024 = 529272 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78651) (lo := 0) (len := 1024) (W := 529272) check rows elimOK (by decide) (by decide) cover78651 (by decide)
  decide +kernel

theorem h78651 : P.leaf 36 78651 = 529272 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 529272)]) (.cons c78651_0 (.nil)) (by decide) (by decide))

theorem cover78654 : P.CoversSplit 26 10 78654 0xfffffffa00000000000000000000000000000000000000000000000000000000555550500000000055555050000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [538, 579, 867, 873, 874, 972, 1273, 1658]) (by decide +kernel)

theorem c78654_0 : P.sumLeaves 26 80541696 1024 = 994626 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78654) (lo := 0) (len := 1024) (W := 994626) check rows elimOK (by decide) (by decide) cover78654 (by decide)
  decide +kernel

theorem h78654 : P.leaf 36 78654 = 994626 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 994626)]) (.cons c78654_0 (.nil)) (by decide) (by decide))

theorem cover78655 : P.CoversSplit 26 10 78655 0xfffffffa00000000000000000000000000000000000000000000000000000000555550500000000055555050000000000000000000000000000000000000000000000000000000000000000000000000330033003300300011001100110010000000000000000000000000000000000011001000110010001100100011001000 :=
  coversSplit check rows (by decide) (by decide) (xs := [538, 579, 873, 930, 972, 979, 1273, 1315, 1322, 1658]) (by decide +kernel)

theorem c78655_0 : P.sumLeaves 26 80542720 1024 = 5653362 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78655) (lo := 0) (len := 1024) (W := 5653362) check rows elimOK (by decide) (by decide) cover78655 (by decide)
  decide +kernel

theorem h78655 : P.leaf 36 78655 = 5653362 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 5653362)]) (.cons c78655_0 (.nil)) (by decide) (by decide))

theorem cover78665 : P.CoversSplit 26 10 78665 0xa0a00000a0a000000000000000000000a0a00000a0a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000a0a00000a0a000000000000000000000a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [474, 481, 530, 579, 923, 930, 1273]) (by decide +kernel)

theorem c78665_0 : P.sumLeaves 26 80552960 1024 = 6848 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78665) (lo := 0) (len := 1024) (W := 6848) check rows elimOK (by decide) (by decide) cover78665 (by decide)
  decide +kernel

theorem h78665 : P.leaf 36 78665 = 6848 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 6848)]) (.cons c78665_0 (.nil)) (by decide) (by decide))

theorem cover78667 : P.CoversSplit 26 10 78667 0xa0a00000a0a000000000000000000000a0a00000a0a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000a0a00000a0a000000000000000000000a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 523, 530, 579, 930, 972, 979, 1273]) (by decide +kernel)

theorem c78667_0 : P.sumLeaves 26 80555008 1024 = 52976 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78667) (lo := 0) (len := 1024) (W := 52976) check rows elimOK (by decide) (by decide) cover78667 (by decide)
  decide +kernel

theorem h78667 : P.leaf 36 78667 = 52976 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 52976)]) (.cons c78667_0 (.nil)) (by decide) (by decide))

theorem cover78670 : P.CoversSplit 26 10 78670 0xaaaa0000aaaa0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 579, 873, 879, 880, 1266, 1658]) (by decide +kernel)

theorem c78670_0 : P.sumLeaves 26 80558080 1024 = 68480 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78670) (lo := 0) (len := 1024) (W := 68480) check rows elimOK (by decide) (by decide) cover78670 (by decide)
  decide +kernel

theorem h78670 : P.leaf 36 78670 = 68480 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 68480)]) (.cons c78670_0 (.nil)) (by decide) (by decide))

theorem cover78671 : P.CoversSplit 26 10 78671 0xaaaa0000aaaa00000000000000000000aaa80000aaa8000000000000000000000000000000000000000000000000000000000000000000000000000000000000aaaa0000aaaa00000000000000000000aa8800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [523, 530, 930, 979, 1266, 1273, 1658]) (by decide +kernel)

theorem c78671_0 : P.sumLeaves 26 80559104 1024 = 765392 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78671) (lo := 0) (len := 1024) (W := 765392) check rows elimOK (by decide) (by decide) cover78671 (by decide)
  decide +kernel

theorem h78671 : P.leaf 36 78671 = 765392 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 765392)]) (.cons c78671_0 (.nil)) (by decide) (by decide))

theorem cover78683 : P.CoversSplit 26 10 78683 0xa0a00000a0a000000000000000000000a0a00000a0a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000a0a00000a0a000000000000000000000a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 579, 873, 930, 972, 979, 1273, 1322]) (by decide +kernel)

theorem c78683_0 : P.sumLeaves 26 80571392 1024 = 707328 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78683) (lo := 0) (len := 1024) (W := 707328) check rows elimOK (by decide) (by decide) cover78683 (by decide)
  decide +kernel

theorem h78683 : P.leaf 36 78683 = 707328 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 707328)]) (.cons c78683_0 (.nil)) (by decide) (by decide))

theorem cover78684 : P.CoversSplit 26 10 78684 0xaaaa0000aaaa0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [467, 530, 867, 880, 923, 1658]) (by decide +kernel)

theorem c78684_0 : P.sumLeaves 26 80572416 1024 = 90752 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78684) (lo := 0) (len := 1024) (W := 90752) check rows elimOK (by decide) (by decide) cover78684 (by decide)
  decide +kernel

theorem h78684 : P.leaf 36 78684 = 90752 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 90752)]) (.cons c78684_0 (.nil)) (by decide) (by decide))

theorem cover78685 : P.CoversSplit 26 10 78685 0xaaaa0000aaaa00000000000000000000aaa80000aaa8000000000000000000000000000000000000000000000000000000000000000000000000000000000000aaaa0000aaaa00000000000000000000aa0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 579, 923, 930, 979, 1273, 1322, 1658]) (by decide +kernel)

theorem c78685_0 : P.sumLeaves 26 80573440 1024 = 550016 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78685) (lo := 0) (len := 1024) (W := 550016) check rows elimOK (by decide) (by decide) cover78685 (by decide)
  decide +kernel

theorem h78685 : P.leaf 36 78685 = 550016 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 550016)]) (.cons c78685_0 (.nil)) (by decide) (by decide))

theorem cover78686 : P.CoversSplit 26 10 78686 0xaaaa0000aaaa0000000000000000000000000000000000000000000000000000000000000000000005050000050500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 579, 867, 873, 880, 1315, 1658]) (by decide +kernel)

theorem c78686_0 : P.sumLeaves 26 80574464 1024 = 559646 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78686) (lo := 0) (len := 1024) (W := 559646) check rows elimOK (by decide) (by decide) cover78686 (by decide)
  decide +kernel

theorem h78686 : P.leaf 36 78686 = 559646 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 559646)]) (.cons c78686_0 (.nil)) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(78593, 30), (78595, 240), (78599, 360), (78601, 180), (78603, 720), (78607, 360), (78612, 120), (78613, 360), (78614, 360), (78615, 720), (78617, 720), (78619, 720), (78620, 720), (78621, 720), (78622, 720), (78623, 720), (78646, 180), (78647, 180), (78648, 360), (78649, 360), (78650, 720), (78651, 720), (78654, 360), (78655, 360), (78665, 90), (78667, 720), (78670, 360), (78671, 360), (78683, 360), (78684, 360), (78685, 360), (78686, 720)]

theorem segOK : checkSeg 20 perms 78593 78687 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 78593 78687 14340 4870950960 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 4870950960)
    (SegSum.cons (w := 30) h78593 (SegSum.cons (w := 240) h78595 (SegSum.cons (w := 360) h78599 (SegSum.cons (w := 180) h78601 (SegSum.cons (w := 720) h78603 (SegSum.cons (w := 360) h78607 (SegSum.cons (w := 120) h78612 (SegSum.cons (w := 360) h78613 (SegSum.cons (w := 360) h78614 (SegSum.cons (w := 720) h78615 (SegSum.cons (w := 720) h78617 (SegSum.cons (w := 720) h78619 (SegSum.cons (w := 720) h78620 (SegSum.cons (w := 720) h78621 (SegSum.cons (w := 720) h78622 (SegSum.cons (w := 720) h78623 (SegSum.cons (w := 180) h78646 (SegSum.cons (w := 180) h78647 (SegSum.cons (w := 360) h78648 (SegSum.cons (w := 360) h78649 (SegSum.cons (w := 720) h78650 (SegSum.cons (w := 720) h78651 (SegSum.cons (w := 360) h78654 (SegSum.cons (w := 360) h78655 (SegSum.cons (w := 90) h78665 (SegSum.cons (w := 720) h78667 (SegSum.cons (w := 360) h78670 (SegSum.cons (w := 360) h78671 (SegSum.cons (w := 360) h78683 (SegSum.cons (w := 360) h78684 (SegSum.cons (w := 360) h78685 (SegSum.cons (w := 720) h78686 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S46
