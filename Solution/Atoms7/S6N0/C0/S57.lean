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

namespace RACert.S6N0.C0.S57

open RACert RACert.Problem

theorem cover81391 : P.CoversSplit 26 10 81391 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 923, 930, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c81391_0 : P.sumLeaves 26 83344384 1024 = 3569296 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81391) (lo := 0) (len := 1024) (W := 3569296) check rows elimOK (by decide) (by decide) cover81391 (by decide)
  decide +kernel

theorem h81391 : P.leaf 36 81391 = 3569296 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 3569296)]) (.cons c81391_0 (.nil)) (by decide) (by decide))

theorem cover81406 : P.CoversSplit 26 10 81406 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 923, 930, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c81406_0 : P.sumLeaves 26 83359744 1024 = 9553084 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81406) (lo := 0) (len := 1024) (W := 9553084) check rows elimOK (by decide) (by decide) cover81406 (by decide)
  decide +kernel

theorem h81406 : P.leaf 36 81406 = 9553084 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 9553084)]) (.cons c81406_0 (.nil)) (by decide) (by decide))

theorem cover81407 : P.CoversSplit 26 10 81407 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 923, 930, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c81407_0 : P.sumLeaves 26 83360768 1024 = 10138416 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81407) (lo := 0) (len := 1024) (W := 10138416) check rows elimOK (by decide) (by decide) cover81407 (by decide)
  decide +kernel

theorem h81407 : P.leaf 36 81407 = 10138416 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 10138416)]) (.cons c81407_0 (.nil)) (by decide) (by decide))

theorem cover81683 : P.CoversSplit 26 10 81683 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 530, 538, 579, 608, 930, 972, 979, 1658]) (by decide +kernel)

theorem c81683_0 : P.sumLeaves 26 83643392 1024 = 421804 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81683) (lo := 0) (len := 1024) (W := 421804) check rows elimOK (by decide) (by decide) cover81683 (by decide)
  decide +kernel

theorem h81683 : P.leaf 36 81683 = 421804 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 421804)]) (.cons c81683_0 (.nil)) (by decide) (by decide))

theorem cover81684 : P.CoversSplit 26 10 81684 0xcc00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 538, 923, 930, 972, 979, 1273, 1315, 1658, 1665]) (by decide +kernel)

theorem c81684_0 : P.sumLeaves 26 83644416 1024 = 57472 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81684) (lo := 0) (len := 1024) (W := 57472) check rows elimOK (by decide) (by decide) cover81684 (by decide)
  decide +kernel

theorem h81684 : P.leaf 36 81684 = 57472 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 57472)]) (.cons c81684_0 (.nil)) (by decide) (by decide))

theorem cover81685 : P.CoversSplit 26 10 81685 0xcc00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 538, 579, 923, 930, 972, 979, 1315, 1658, 1665]) (by decide +kernel)

theorem c81685_0 : P.sumLeaves 26 83645440 1024 = 583840 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81685) (lo := 0) (len := 1024) (W := 583840) check rows elimOK (by decide) (by decide) cover81685 (by decide)
  decide +kernel

theorem h81685 : P.leaf 36 81685 = 583840 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 583840)]) (.cons c81685_0 (.nil)) (by decide) (by decide))

theorem cover81686 : P.CoversSplit 26 10 81686 0xcc00000000000000000000000000000000000000000000000000000000000000040000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 538, 930, 972, 979, 1273, 1315, 1658, 1665]) (by decide +kernel)

theorem c81686_0 : P.sumLeaves 26 83646464 1024 = 693496 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81686) (lo := 0) (len := 1024) (W := 693496) check rows elimOK (by decide) (by decide) cover81686 (by decide)
  decide +kernel

theorem h81686 : P.leaf 36 81686 = 693496 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 693496)]) (.cons c81686_0 (.nil)) (by decide) (by decide))

theorem cover81687 : P.CoversSplit 26 10 81687 0xcc00000000000000000000000000000000000000000000000000000000000000040000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 538, 930, 972, 979, 1315, 1658, 1665]) (by decide +kernel)

theorem c81687_0 : P.sumLeaves 26 83647488 1024 = 3372526 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81687) (lo := 0) (len := 1024) (W := 3372526) check rows elimOK (by decide) (by decide) cover81687 (by decide)
  decide +kernel

theorem h81687 : P.leaf 36 81687 = 3372526 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 3372526)]) (.cons c81687_0 (.nil)) (by decide) (by decide))

theorem cover81688 : P.CoversSplit 26 10 81688 0xa0a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 538, 558, 579, 615, 923, 1273, 1322]) (by decide +kernel)

theorem c81688_0 : P.sumLeaves 26 83648512 1024 = 36064 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81688) (lo := 0) (len := 1024) (W := 36064) check rows elimOK (by decide) (by decide) cover81688 (by decide)
  decide +kernel

theorem h81688 : P.leaf 36 81688 = 36064 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 36064)]) (.cons c81688_0 (.nil)) (by decide) (by decide))

theorem cover81689 : P.CoversSplit 26 10 81689 0xa0a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [474, 481, 530, 538, 579, 615, 923, 1273, 1322]) (by decide +kernel)

theorem c81689_0 : P.sumLeaves 26 83649536 1024 = 813568 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81689) (lo := 0) (len := 1024) (W := 813568) check rows elimOK (by decide) (by decide) cover81689 (by decide)
  decide +kernel

theorem h81689 : P.leaf 36 81689 = 813568 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 813568)]) (.cons c81689_0 (.nil)) (by decide) (by decide))

theorem cover81690 : P.CoversSplit 26 10 81690 0xa0a0000000000000000000000000000000000000000000000000000000000000000000000000000000000505000000000000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 538, 579, 615, 972, 1273, 1322]) (by decide +kernel)

theorem c81690_0 : P.sumLeaves 26 83650560 1024 = 1110929 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81690) (lo := 0) (len := 1024) (W := 1110929) check rows elimOK (by decide) (by decide) cover81690 (by decide)
  decide +kernel

theorem h81690 : P.leaf 36 81690 = 1110929 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1110929)]) (.cons c81690_0 (.nil)) (by decide) (by decide))

theorem cover81691 : P.CoversSplit 26 10 81691 0xa0a0000000000000000000000000000000000000000000000000000000000000000000000000000000000505000000000000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 538, 579, 615, 972, 1273, 1322]) (by decide +kernel)

theorem c81691_0 : P.sumLeaves 26 83651584 1024 = 3525887 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81691) (lo := 0) (len := 1024) (W := 3525887) check rows elimOK (by decide) (by decide) cover81691 (by decide)
  decide +kernel

theorem h81691 : P.leaf 36 81691 = 3525887 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 3525887)]) (.cons c81691_0 (.nil)) (by decide) (by decide))

theorem cover81692 : P.CoversSplit 26 10 81692 0xffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003300000000000000110000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 538, 923, 930, 972, 1273, 1315, 1322, 1658]) (by decide +kernel)

theorem c81692_0 : P.sumLeaves 26 83652608 1024 = 672688 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81692) (lo := 0) (len := 1024) (W := 672688) check rows elimOK (by decide) (by decide) cover81692 (by decide)
  decide +kernel

theorem h81692 : P.leaf 36 81692 = 672688 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 672688)]) (.cons c81692_0 (.nil)) (by decide) (by decide))

theorem cover81693 : P.CoversSplit 26 10 81693 0xffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003300000000000000110000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 538, 579, 923, 930, 972, 1273, 1315, 1322, 1658]) (by decide +kernel)

theorem c81693_0 : P.sumLeaves 26 83653632 1024 = 4489188 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81693) (lo := 0) (len := 1024) (W := 4489188) check rows elimOK (by decide) (by decide) cover81693 (by decide)
  decide +kernel

theorem h81693 : P.leaf 36 81693 = 4489188 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 4489188)]) (.cons c81693_0 (.nil)) (by decide) (by decide))

theorem cover81694 : P.CoversSplit 26 10 81694 0xffff000000000000000000000000000000000000000000000000000000000000050500000000000005050000000000000000000000000000000000000000000000000000000000000000000000000000003300000000000000110000000000000000000000000000000000000000000000010000000000000001000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 538, 972, 1273, 1315, 1322, 1658]) (by decide +kernel)

theorem c81694_0 : P.sumLeaves 26 83654656 1024 = 4314857 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81694) (lo := 0) (len := 1024) (W := 4314857) check rows elimOK (by decide) (by decide) cover81694 (by decide)
  decide +kernel

theorem h81694 : P.leaf 36 81694 = 4314857 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 4314857)]) (.cons c81694_0 (.nil)) (by decide) (by decide))

theorem cover81695 : P.CoversSplit 26 10 81695 0xffff000000000000000000000000000000000000000000000000000000000000050500000000000005050000000000000000000000000000000000000000000000000000000000000000000000000000003300000000000000110000000000000000000000000000000000000000000000010000000000000001000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 538, 972, 1273, 1315, 1322, 1658]) (by decide +kernel)

theorem c81695_0 : P.sumLeaves 26 83655680 1024 = 15659500 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81695) (lo := 0) (len := 1024) (W := 15659500) check rows elimOK (by decide) (by decide) cover81695 (by decide)
  decide +kernel

theorem h81695 : P.leaf 36 81695 = 15659500 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 15659500)]) (.cons c81695_0 (.nil)) (by decide) (by decide))

theorem cover81718 : P.CoversSplit 26 10 81718 0xcc00cc0000000000000000000000000000000000000000000000000000000000440040000000000044004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 538, 579, 930, 972, 979, 1273, 1658, 1665]) (by decide +kernel)

theorem c81718_0 : P.sumLeaves 26 83679232 1024 = 4657828 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81718) (lo := 0) (len := 1024) (W := 4657828) check rows elimOK (by decide) (by decide) cover81718 (by decide)
  decide +kernel

theorem h81718 : P.leaf 36 81718 = 4657828 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 4657828)]) (.cons c81718_0 (.nil)) (by decide) (by decide))

theorem cover81719 : P.CoversSplit 26 10 81719 0xcc00cc0000000000000000000000000000000000000000000000000000000000440040000000000044004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 538, 579, 930, 972, 979, 1658, 1665]) (by decide +kernel)

theorem c81719_0 : P.sumLeaves 26 83680256 1024 = 18960778 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81719) (lo := 0) (len := 1024) (W := 18960778) check rows elimOK (by decide) (by decide) cover81719 (by decide)
  decide +kernel

theorem h81719 : P.leaf 36 81719 = 18960778 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 18960778)]) (.cons c81719_0 (.nil)) (by decide) (by decide))

theorem cover81720 : P.CoversSplit 26 10 81720 0xf0f0f0f500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003000310000000000100011000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 579, 874, 923, 930, 972, 979, 1273, 1315, 1322, 1658]) (by decide +kernel)

theorem c81720_0 : P.sumLeaves 26 83681280 1024 = 315492 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81720) (lo := 0) (len := 1024) (W := 315492) check rows elimOK (by decide) (by decide) cover81720 (by decide)
  decide +kernel

theorem h81720 : P.leaf 36 81720 = 315492 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 315492)]) (.cons c81720_0 (.nil)) (by decide) (by decide))

theorem cover81721 : P.CoversSplit 26 10 81721 0xf0f0f0f500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003000310000000000100011000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 579, 923, 930, 972, 979, 1273, 1315, 1322, 1658]) (by decide +kernel)

theorem c81721_0 : P.sumLeaves 26 83682304 1024 = 9537245 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81721) (lo := 0) (len := 1024) (W := 9537245) check rows elimOK (by decide) (by decide) cover81721 (by decide)
  decide +kernel

theorem h81721 : P.leaf 36 81721 = 9537245 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 9537245)]) (.cons c81721_0 (.nil)) (by decide) (by decide))

theorem cover81722 : P.CoversSplit 26 10 81722 0xf0f0f0f500000000000000000000000000000000000000000000000000000000000050500000000000005050000000000000000000000000000000000000000000000000000000000000000000000000003000310000000000100011000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 874, 972, 979, 1273, 1315, 1322, 1658]) (by decide +kernel)

theorem c81722_0 : P.sumLeaves 26 83683328 1024 = 10395308 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81722) (lo := 0) (len := 1024) (W := 10395308) check rows elimOK (by decide) (by decide) cover81722 (by decide)
  decide +kernel

theorem h81722 : P.leaf 36 81722 = 10395308 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 10395308)]) (.cons c81722_0 (.nil)) (by decide) (by decide))

theorem cover81723 : P.CoversSplit 26 10 81723 0xf0f0f0f500000000000000000000000000000000000000000000000000000000000050500000000000005050000000000000000000000000000000000000000000000000000000000000000000000000003000310000000000100011000000000000000000000000000000000000000000000010000000000000001000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 972, 979, 1273, 1315, 1322, 1658]) (by decide +kernel)

theorem c81723_0 : P.sumLeaves 26 83684352 1024 = 27548557 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81723) (lo := 0) (len := 1024) (W := 27548557) check rows elimOK (by decide) (by decide) cover81723 (by decide)
  decide +kernel

theorem h81723 : P.leaf 36 81723 = 27548557 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 27548557)]) (.cons c81723_0 (.nil)) (by decide) (by decide))

theorem cover81726 : P.CoversSplit 26 10 81726 0xfffffffa00000000000000000000000000000000000000000000000000000000555550500000000055555050000000000000000000000000000000000000000000000000000000000000000000000000003300320000000000110010000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [538, 579, 874, 972, 979, 1273, 1315, 1322, 1658]) (by decide +kernel)

theorem c81726_0 : P.sumLeaves 26 83687424 1024 = 39667563 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81726) (lo := 0) (len := 1024) (W := 39667563) check rows elimOK (by decide) (by decide) cover81726 (by decide)
  decide +kernel

theorem h81726 : P.leaf 36 81726 = 39667563 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 39667563)]) (.cons c81726_0 (.nil)) (by decide) (by decide))

theorem cover81727 : P.CoversSplit 26 10 81727 0xfffffffa00000000000000000000000000000000000000000000000000000000555550500000000055555050000000000000000000000000000000000000000000000000000000000000000000000000003300320000000000110010000000000000000000000000000000000000000000110010000000000011001000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [538, 579, 972, 979, 1273, 1315, 1322, 1658]) (by decide +kernel)

theorem c81727_0 : P.sumLeaves 26 83688448 1024 = 100494116 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81727) (lo := 0) (len := 1024) (W := 100494116) check rows elimOK (by decide) (by decide) cover81727 (by decide)
  decide +kernel

theorem h81727 : P.leaf 36 81727 = 100494116 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 100494116)]) (.cons c81727_0 (.nil)) (by decide) (by decide))

theorem cover81737 : P.CoversSplit 26 10 81737 0xa0a00000a0a000000000000000000000a0a00000a0a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000a0a00000a0a000000000000000000000a0a00000a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [474, 481, 530, 579, 923, 930]) (by decide +kernel)

theorem c81737_0 : P.sumLeaves 26 83698688 1024 = 880384 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81737) (lo := 0) (len := 1024) (W := 880384) check rows elimOK (by decide) (by decide) cover81737 (by decide)
  decide +kernel

theorem h81737 : P.leaf 36 81737 = 880384 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 880384)]) (.cons c81737_0 (.nil)) (by decide) (by decide))

theorem cover81738 : P.CoversSplit 26 10 81738 0xa0a00000a0a000000000000000000000a0a00000a0a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000a0a00000a0a000000000000000000000a0a00000a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 565, 579, 930, 972, 979]) (by decide +kernel)

theorem c81738_0 : P.sumLeaves 26 83699712 1024 = 1267928 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81738) (lo := 0) (len := 1024) (W := 1267928) check rows elimOK (by decide) (by decide) cover81738 (by decide)
  decide +kernel

theorem h81738 : P.leaf 36 81738 = 1267928 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1267928)]) (.cons c81738_0 (.nil)) (by decide) (by decide))

theorem cover81739 : P.CoversSplit 26 10 81739 0xa0a00000a0a000000000000000000000a0a00000a0a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000a0a00000a0a000000000000000000000a0a00000a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 523, 530, 579, 930, 972, 979]) (by decide +kernel)

theorem c81739_0 : P.sumLeaves 26 83700736 1024 = 6873032 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81739) (lo := 0) (len := 1024) (W := 6873032) check rows elimOK (by decide) (by decide) cover81739 (by decide)
  decide +kernel

theorem h81739 : P.leaf 36 81739 = 6873032 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 6873032)]) (.cons c81739_0 (.nil)) (by decide) (by decide))

theorem cover81742 : P.CoversSplit 26 10 81742 0xffff0000ffff05000000000000000000ffff0000fffc050055550000550005000000000000000000000000000000000000000000000000000000000000000000ffff0000ffff05000000000000000000ffff0000ff00050055550000550005000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 579, 880, 930, 972, 979, 1266, 1273, 1315, 1658, 1665]) (by decide +kernel)

theorem c81742_0 : P.sumLeaves 26 83703808 856 = 4603960 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81742) (lo := 0) (len := 856) (W := 4603960) check rows elimOK (by decide) (by decide) cover81742 (by decide)
  decide +kernel

theorem c81742_1 : P.sumLeaves 26 83704664 168 = 6016071 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81742) (lo := 856) (len := 168) (W := 6016071) check rows elimOK (by decide) (by decide) cover81742 (by decide)
  decide +kernel

theorem h81742 : P.leaf 36 81742 = 10620031 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(856, 4603960), (168, 6016071)]) (.cons c81742_0 (.cons c81742_1 (.nil))) (by decide) (by decide))

theorem cover81743 : P.CoversSplit 26 10 81743 0xffff0000ffff05000000000000000000ffff0000fffc050055550000550005000000000000000000000000000000000000000000000000000000000000000000ffff0000ffff05000000000000000000ffff0000ff00050055550000550005000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 579, 930, 972, 979, 1266, 1273, 1315, 1658, 1665]) (by decide +kernel)

theorem c81743_0 : P.sumLeaves 26 83704832 856 = 21043030 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81743) (lo := 0) (len := 856) (W := 21043030) check rows elimOK (by decide) (by decide) cover81743 (by decide)
  decide +kernel

theorem c81743_1 : P.sumLeaves 26 83705688 168 = 34392156 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81743) (lo := 856) (len := 168) (W := 34392156) check rows elimOK (by decide) (by decide) cover81743 (by decide)
  decide +kernel

theorem h81743 : P.leaf 36 81743 = 55435186 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(856, 21043030), (168, 34392156)]) (.cons c81743_0 (.cons c81743_1 (.nil))) (by decide) (by decide))

theorem cover81754 : P.CoversSplit 26 10 81754 0xa0a00000a0a000000000000000000000a0a00000a0a0000000000000000000000000000000000000000005050000050500000000000000000000050500000500a0a00000a0a000000000000000000000a0a00000a000000000000000000000000000000000000000000005050000050500000000000000000000050500000500 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 579, 930, 972, 979]) (by decide +kernel)

theorem c81754_0 : P.sumLeaves 26 83716096 1024 = 14712636 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81754) (lo := 0) (len := 1024) (W := 14712636) check rows elimOK (by decide) (by decide) cover81754 (by decide)
  decide +kernel

theorem h81754 : P.leaf 36 81754 = 14712636 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 14712636)]) (.cons c81754_0 (.nil)) (by decide) (by decide))

theorem cover81755 : P.CoversSplit 26 10 81755 0xa0a00000a0a000000000000000000000a0a00000a0a0000000000000000000000000000000000000000005050000050500000000000000000000050500000500a0a00000a0a000000000000000000000a0a00000a000000000000000000000000000000000000000000005050000050500000000000000000000050500000500 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 579, 930, 972, 979]) (by decide +kernel)

theorem c81755_0 : P.sumLeaves 26 83717120 1024 = 27153515 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81755) (lo := 0) (len := 1024) (W := 27153515) check rows elimOK (by decide) (by decide) cover81755 (by decide)
  decide +kernel

theorem h81755 : P.leaf 36 81755 = 27153515 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 27153515)]) (.cons c81755_0 (.nil)) (by decide) (by decide))

theorem cover81756 : P.CoversSplit 26 10 81756 0xffff0000ffff05000000000000000000ffff0000fffc050055550000550005000000000000000000000000000000000000000000000000000000000000000000ffff0000ffff05000000000000000000ffff0000ff00050055550000550005000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 880, 923, 930, 972, 979, 1315, 1658, 1665]) (by decide +kernel)

theorem c81756_0 : P.sumLeaves 26 83718144 856 = 6429272 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81756) (lo := 0) (len := 856) (W := 6429272) check rows elimOK (by decide) (by decide) cover81756 (by decide)
  decide +kernel

theorem c81756_1 : P.sumLeaves 26 83719000 168 = 14793356 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81756) (lo := 856) (len := 168) (W := 14793356) check rows elimOK (by decide) (by decide) cover81756 (by decide)
  decide +kernel

theorem h81756 : P.leaf 36 81756 = 21222628 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(856, 6429272), (168, 14793356)]) (.cons c81756_0 (.cons c81756_1 (.nil))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(81391, 720), (81406, 360), (81407, 360), (81683, 360), (81684, 360), (81685, 360), (81686, 720), (81687, 720), (81688, 360), (81689, 720), (81690, 720), (81691, 720), (81692, 720), (81693, 720), (81694, 720), (81695, 720), (81718, 180), (81719, 180), (81720, 360), (81721, 360), (81722, 720), (81723, 720), (81726, 360), (81727, 360), (81737, 90), (81738, 360), (81739, 720), (81742, 360), (81743, 360), (81754, 360), (81755, 360), (81756, 360)]

theorem segOK : checkSeg 20 perms 81391 81757 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 81391 81757 15570 172556669880 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 172556669880)
    (SegSum.cons (w := 720) h81391 (SegSum.cons (w := 360) h81406 (SegSum.cons (w := 360) h81407 (SegSum.cons (w := 360) h81683 (SegSum.cons (w := 360) h81684 (SegSum.cons (w := 360) h81685 (SegSum.cons (w := 720) h81686 (SegSum.cons (w := 720) h81687 (SegSum.cons (w := 360) h81688 (SegSum.cons (w := 720) h81689 (SegSum.cons (w := 720) h81690 (SegSum.cons (w := 720) h81691 (SegSum.cons (w := 720) h81692 (SegSum.cons (w := 720) h81693 (SegSum.cons (w := 720) h81694 (SegSum.cons (w := 720) h81695 (SegSum.cons (w := 180) h81718 (SegSum.cons (w := 180) h81719 (SegSum.cons (w := 360) h81720 (SegSum.cons (w := 360) h81721 (SegSum.cons (w := 720) h81722 (SegSum.cons (w := 720) h81723 (SegSum.cons (w := 360) h81726 (SegSum.cons (w := 360) h81727 (SegSum.cons (w := 90) h81737 (SegSum.cons (w := 360) h81738 (SegSum.cons (w := 720) h81739 (SegSum.cons (w := 360) h81742 (SegSum.cons (w := 360) h81743 (SegSum.cons (w := 360) h81754 (SegSum.cons (w := 360) h81755 (SegSum.cons (w := 360) h81756 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S57
