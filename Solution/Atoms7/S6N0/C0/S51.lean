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

namespace RACert.S6N0.C0.S51

open RACert RACert.Problem

theorem cover79547 : P.CoversSplit 26 10 79547 0xc000c00000000000c000c0000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 587, 930, 972, 1273, 1315, 1322, 1658]) (by decide +kernel)

theorem c79547_0 : P.sumLeaves 26 81456128 1024 = 468904 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79547) (lo := 0) (len := 1024) (W := 468904) check rows elimOK (by decide) (by decide) cover79547 (by decide)
  decide +kernel

theorem h79547 : P.leaf 36 79547 = 468904 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 468904)]) (.cons c79547_0 (.nil)) (by decide) (by decide))

theorem cover79548 : P.CoversSplit 26 10 79548 0xcc00cc0000000000cc00cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [475, 587, 873, 874, 923, 930, 1273]) (by decide +kernel)

theorem c79548_0 : P.sumLeaves 26 81457152 1024 = 427552 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79548) (lo := 0) (len := 1024) (W := 427552) check rows elimOK (by decide) (by decide) cover79548 (by decide)
  decide +kernel

theorem h79548 : P.leaf 36 79548 = 427552 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 427552)]) (.cons c79548_0 (.nil)) (by decide) (by decide))

theorem cover79549 : P.CoversSplit 26 10 79549 0xcc00cc0000000000cc00cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [475, 587, 873, 923, 930, 972, 1273, 1315, 1322]) (by decide +kernel)

theorem c79549_0 : P.sumLeaves 26 81458176 1024 = 906736 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79549) (lo := 0) (len := 1024) (W := 906736) check rows elimOK (by decide) (by decide) cover79549 (by decide)
  decide +kernel

theorem h79549 : P.leaf 36 79549 = 906736 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 906736)]) (.cons c79549_0 (.nil)) (by decide) (by decide))

theorem cover79550 : P.CoversSplit 26 10 79550 0xcc00cc0000000000cc00cc000000000000000000000000000000000000000000cc00c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [538, 587, 873, 874, 930, 972, 1273, 1315, 1658]) (by decide +kernel)

theorem c79550_0 : P.sumLeaves 26 81459200 1024 = 694000 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79550) (lo := 0) (len := 1024) (W := 694000) check rows elimOK (by decide) (by decide) cover79550 (by decide)
  decide +kernel

theorem h79550 : P.leaf 36 79550 = 694000 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 694000)]) (.cons c79550_0 (.nil)) (by decide) (by decide))

theorem cover79551 : P.CoversSplit 26 10 79551 0xcc00cc0000000000cc00cc000000000000000000000000000000000000000000cc00c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [538, 587, 873, 930, 972, 1273, 1315, 1322, 1658]) (by decide +kernel)

theorem c79551_0 : P.sumLeaves 26 81460224 1024 = 1278776 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79551) (lo := 0) (len := 1024) (W := 1278776) check rows elimOK (by decide) (by decide) cover79551 (by decide)
  decide +kernel

theorem h79551 : P.leaf 36 79551 = 1278776 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1278776)]) (.cons c79551_0 (.nil)) (by decide) (by decide))

theorem cover79561 : P.CoversSplit 26 10 79561 0xc000000000000000c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003000010000000000300001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [475, 481, 587, 923, 930, 972, 1273, 1315, 1665]) (by decide +kernel)

theorem c79561_0 : P.sumLeaves 26 81470464 1024 = 13056 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79561) (lo := 0) (len := 1024) (W := 13056) check rows elimOK (by decide) (by decide) cover79561 (by decide)
  decide +kernel

theorem h79561 : P.leaf 36 79561 = 13056 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 13056)]) (.cons c79561_0 (.nil)) (by decide) (by decide))

theorem cover79563 : P.CoversSplit 26 10 79563 0xc000000000000000c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003000010000000000300001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 524, 530, 587, 930, 972, 1266, 1273, 1315, 1665]) (by decide +kernel)

theorem c79563_0 : P.sumLeaves 26 81472512 1024 = 146112 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79563) (lo := 0) (len := 1024) (W := 146112) check rows elimOK (by decide) (by decide) cover79563 (by decide)
  decide +kernel

theorem h79563 : P.leaf 36 79563 = 146112 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 146112)]) (.cons c79563_0 (.nil)) (by decide) (by decide))

theorem cover79564 : P.CoversSplit 26 10 79564 0xcc00000000000000cc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [467, 475, 587, 880, 923, 930, 1273]) (by decide +kernel)

theorem c79564_0 : P.sumLeaves 26 81473536 1024 = 83328 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79564) (lo := 0) (len := 1024) (W := 83328) check rows elimOK (by decide) (by decide) cover79564 (by decide)
  decide +kernel

theorem h79564 : P.leaf 36 79564 = 83328 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 83328)]) (.cons c79564_0 (.nil)) (by decide) (by decide))

theorem cover79565 : P.CoversSplit 26 10 79565 0xcc00000000000000cc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003300000000000000330000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [475, 530, 587, 923, 930, 972, 1273, 1315, 1665]) (by decide +kernel)

theorem c79565_0 : P.sumLeaves 26 81474560 1024 = 156336 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79565) (lo := 0) (len := 1024) (W := 156336) check rows elimOK (by decide) (by decide) cover79565 (by decide)
  decide +kernel

theorem h79565 : P.leaf 36 79565 = 156336 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 156336)]) (.cons c79565_0 (.nil)) (by decide) (by decide))

theorem cover79566 : P.CoversSplit 26 10 79566 0xcc00000000000000cc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [524, 530, 587, 873, 880, 930, 1266, 1273, 1315]) (by decide +kernel)

theorem c79566_0 : P.sumLeaves 26 81475584 1024 = 111904 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79566) (lo := 0) (len := 1024) (W := 111904) check rows elimOK (by decide) (by decide) cover79566 (by decide)
  decide +kernel

theorem h79566 : P.leaf 36 79566 = 111904 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 111904)]) (.cons c79566_0 (.nil)) (by decide) (by decide))

theorem cover79567 : P.CoversSplit 26 10 79567 0xcc00000000000000cc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003300000000000000330000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [524, 530, 587, 930, 972, 1266, 1273, 1315, 1665]) (by decide +kernel)

theorem c79567_0 : P.sumLeaves 26 81476608 1024 = 405808 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79567) (lo := 0) (len := 1024) (W := 405808) check rows elimOK (by decide) (by decide) cover79567 (by decide)
  decide +kernel

theorem h79567 : P.leaf 36 79567 = 405808 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 405808)]) (.cons c79567_0 (.nil)) (by decide) (by decide))

theorem cover79579 : P.CoversSplit 26 10 79579 0xc000000000000000c00000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000003000010000000000300001000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 587, 930, 972, 979, 1273, 1315, 1665]) (by decide +kernel)

theorem c79579_0 : P.sumLeaves 26 81488896 1024 = 314144 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79579) (lo := 0) (len := 1024) (W := 314144) check rows elimOK (by decide) (by decide) cover79579 (by decide)
  decide +kernel

theorem h79579 : P.leaf 36 79579 = 314144 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 314144)]) (.cons c79579_0 (.nil)) (by decide) (by decide))

theorem cover79580 : P.CoversSplit 26 10 79580 0xcc00000000000000cc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [467, 475, 587, 880, 923, 930, 1273]) (by decide +kernel)

theorem c79580_0 : P.sumLeaves 26 81489920 1024 = 959352 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79580) (lo := 0) (len := 1024) (W := 959352) check rows elimOK (by decide) (by decide) cover79580 (by decide)
  decide +kernel

theorem h79580 : P.leaf 36 79580 = 959352 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 959352)]) (.cons c79580_0 (.nil)) (by decide) (by decide))

theorem cover79581 : P.CoversSplit 26 10 79581 0xcc00000000000000cc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003300000000000000330000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [475, 530, 587, 923, 930, 972, 1273, 1315, 1665]) (by decide +kernel)

theorem c79581_0 : P.sumLeaves 26 81490944 1024 = 1049680 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79581) (lo := 0) (len := 1024) (W := 1049680) check rows elimOK (by decide) (by decide) cover79581 (by decide)
  decide +kernel

theorem h79581 : P.leaf 36 79581 = 1049680 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1049680)]) (.cons c79581_0 (.nil)) (by decide) (by decide))

theorem cover79582 : P.CoversSplit 26 10 79582 0xcc00000000000000cc0000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 587, 873, 880, 930, 972, 1273, 1315, 1658]) (by decide +kernel)

theorem c79582_0 : P.sumLeaves 26 81491968 1024 = 1174072 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79582) (lo := 0) (len := 1024) (W := 1174072) check rows elimOK (by decide) (by decide) cover79582 (by decide)
  decide +kernel

theorem h79582 : P.leaf 36 79582 = 1174072 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1174072)]) (.cons c79582_0 (.nil)) (by decide) (by decide))

theorem cover79583 : P.CoversSplit 26 10 79583 0xcc00000000000000cc0000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000000003300000000000000330000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 587, 930, 972, 979, 1273, 1315, 1658, 1665]) (by decide +kernel)

theorem c79583_0 : P.sumLeaves 26 81492992 1024 = 1304068 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79583) (lo := 0) (len := 1024) (W := 1304068) check rows elimOK (by decide) (by decide) cover79583 (by decide)
  decide +kernel

theorem h79583 : P.leaf 36 79583 = 1304068 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1304068)]) (.cons c79583_0 (.nil)) (by decide) (by decide))

theorem cover79596 : P.CoversSplit 26 10 79596 0xcc00cc0000000000cc00cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [475, 587, 873, 874, 923, 930, 1273]) (by decide +kernel)

theorem c79596_0 : P.sumLeaves 26 81506304 1024 = 1260168 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79596) (lo := 0) (len := 1024) (W := 1260168) check rows elimOK (by decide) (by decide) cover79596 (by decide)
  decide +kernel

theorem h79596 : P.leaf 36 79596 = 1260168 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1260168)]) (.cons c79596_0 (.nil)) (by decide) (by decide))

theorem cover79597 : P.CoversSplit 26 10 79597 0xcc00cc0000000000cc00cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003300320000000000330032000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [475, 587, 873, 923, 930, 972, 1273, 1665]) (by decide +kernel)

theorem c79597_0 : P.sumLeaves 26 81507328 1024 = 1893880 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79597) (lo := 0) (len := 1024) (W := 1893880) check rows elimOK (by decide) (by decide) cover79597 (by decide)
  decide +kernel

theorem h79597 : P.leaf 36 79597 = 1893880 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1893880)]) (.cons c79597_0 (.nil)) (by decide) (by decide))

theorem cover79598 : P.CoversSplit 26 10 79598 0xcc00cc0000000000cc00cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [524, 587, 873, 874, 930, 972, 1266, 1273]) (by decide +kernel)

theorem c79598_0 : P.sumLeaves 26 81508352 1024 = 2914188 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79598) (lo := 0) (len := 1024) (W := 2914188) check rows elimOK (by decide) (by decide) cover79598 (by decide)
  decide +kernel

theorem h79598 : P.leaf 36 79598 = 2914188 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 2914188)]) (.cons c79598_0 (.nil)) (by decide) (by decide))

theorem cover79599 : P.CoversSplit 26 10 79599 0xcc00cc0000000000cc00cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003300320000000000330032000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [524, 587, 873, 930, 972, 1266, 1273, 1665]) (by decide +kernel)

theorem c79599_0 : P.sumLeaves 26 81509376 1024 = 3599708 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79599) (lo := 0) (len := 1024) (W := 3599708) check rows elimOK (by decide) (by decide) cover79599 (by decide)
  decide +kernel

theorem h79599 : P.leaf 36 79599 = 3599708 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 3599708)]) (.cons c79599_0 (.nil)) (by decide) (by decide))

theorem cover79614 : P.CoversSplit 26 10 79614 0xcc00cc0000000000cc00cc000000000000000000000000000000000000000000cc00c8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [587, 873, 874, 930, 972, 1273, 1658]) (by decide +kernel)

theorem c79614_0 : P.sumLeaves 26 81524736 1024 = 6995992 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79614) (lo := 0) (len := 1024) (W := 6995992) check rows elimOK (by decide) (by decide) cover79614 (by decide)
  decide +kernel

theorem h79614 : P.leaf 36 79614 = 6995992 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 6995992)]) (.cons c79614_0 (.nil)) (by decide) (by decide))

theorem cover79615 : P.CoversSplit 26 10 79615 0xcc00cc0000000000cc00cc000000000000000000000000000000000000000000cc00c8000000000000000000000000000000000000000000000000000000000000000000003300320000000000330032000000000000000000000000000000000000000000330032000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [587, 873, 930, 972, 979, 1273, 1658, 1665]) (by decide +kernel)

theorem c79615_0 : P.sumLeaves 26 81525760 1024 = 7806480 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79615) (lo := 0) (len := 1024) (W := 7806480) check rows elimOK (by decide) (by decide) cover79615 (by decide)
  decide +kernel

theorem h79615 : P.leaf 36 79615 = 7806480 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 7806480)]) (.cons c79615_0 (.nil)) (by decide) (by decide))

theorem cover79637 : P.CoversSplit 26 10 79637 0x8800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 538, 579, 923, 930, 972, 979, 1315, 1658, 1665]) (by decide +kernel)

theorem c79637_0 : P.sumLeaves 26 81548288 1024 = 129728 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79637) (lo := 0) (len := 1024) (W := 129728) check rows elimOK (by decide) (by decide) cover79637 (by decide)
  decide +kernel

theorem h79637 : P.leaf 36 79637 = 129728 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 129728)]) (.cons c79637_0 (.nil)) (by decide) (by decide))

theorem cover79639 : P.CoversSplit 26 10 79639 0x8800000000000000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 538, 579, 930, 972, 979, 1315, 1658, 1665]) (by decide +kernel)

theorem c79639_0 : P.sumLeaves 26 81550336 1024 = 607952 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79639) (lo := 0) (len := 1024) (W := 607952) check rows elimOK (by decide) (by decide) cover79639 (by decide)
  decide +kernel

theorem h79639 : P.leaf 36 79639 = 607952 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 607952)]) (.cons c79639_0 (.nil)) (by decide) (by decide))

theorem cover79641 : P.CoversSplit 26 10 79641 0xa0a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [474, 481, 530, 538, 579, 615, 923, 979, 1273, 1322]) (by decide +kernel)

theorem c79641_0 : P.sumLeaves 26 81552384 1024 = 96000 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79641) (lo := 0) (len := 1024) (W := 96000) check rows elimOK (by decide) (by decide) cover79641 (by decide)
  decide +kernel

theorem h79641 : P.leaf 36 79641 = 96000 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 96000)]) (.cons c79641_0 (.nil)) (by decide) (by decide))

theorem cover79643 : P.CoversSplit 26 10 79643 0xa0a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 538, 579, 615, 873, 972, 979, 1273, 1322]) (by decide +kernel)

theorem c79643_0 : P.sumLeaves 26 81554432 1024 = 651840 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79643) (lo := 0) (len := 1024) (W := 651840) check rows elimOK (by decide) (by decide) cover79643 (by decide)
  decide +kernel

theorem h79643 : P.leaf 36 79643 = 651840 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 651840)]) (.cons c79643_0 (.nil)) (by decide) (by decide))

theorem cover79644 : P.CoversSplit 26 10 79644 0xaaaa000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [467, 530, 538, 923, 930, 979, 1273, 1322, 1658]) (by decide +kernel)

theorem c79644_0 : P.sumLeaves 26 81555456 1024 = 143808 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79644) (lo := 0) (len := 1024) (W := 143808) check rows elimOK (by decide) (by decide) cover79644 (by decide)
  decide +kernel

theorem h79644 : P.leaf 36 79644 = 143808 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 143808)]) (.cons c79644_0 (.nil)) (by decide) (by decide))

theorem cover79645 : P.CoversSplit 26 10 79645 0xaaaa000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 538, 579, 923, 930, 972, 979, 1273, 1315, 1322, 1658]) (by decide +kernel)

theorem c79645_0 : P.sumLeaves 26 81556480 1024 = 1003976 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79645) (lo := 0) (len := 1024) (W := 1003976) check rows elimOK (by decide) (by decide) cover79645 (by decide)
  decide +kernel

theorem h79645 : P.leaf 36 79645 = 1003976 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1003976)]) (.cons c79645_0 (.nil)) (by decide) (by decide))

theorem cover79646 : P.CoversSplit 26 10 79646 0xaaaa000000000000000000000000000000000000000000000000000000000000000000000000000005050000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 538, 579, 873, 972, 979, 1273, 1315, 1322, 1658]) (by decide +kernel)

theorem c79646_0 : P.sumLeaves 26 81557504 1024 = 542624 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79646) (lo := 0) (len := 1024) (W := 542624) check rows elimOK (by decide) (by decide) cover79646 (by decide)
  decide +kernel

theorem h79646 : P.leaf 36 79646 = 542624 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 542624)]) (.cons c79646_0 (.nil)) (by decide) (by decide))

theorem cover79647 : P.CoversSplit 26 10 79647 0xaaaa000000000000000000000000000000000000000000000000000000000000000000000000000005050000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 538, 579, 972, 979, 1273, 1315, 1322, 1658]) (by decide +kernel)

theorem c79647_0 : P.sumLeaves 26 81558528 1024 = 2992312 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79647) (lo := 0) (len := 1024) (W := 2992312) check rows elimOK (by decide) (by decide) cover79647 (by decide)
  decide +kernel

theorem h79647 : P.leaf 36 79647 = 2992312 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 2992312)]) (.cons c79647_0 (.nil)) (by decide) (by decide))

theorem cover79653 : P.CoversSplit 26 10 79653 0xcc00cc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 538, 559, 579, 923, 930, 979, 1658]) (by decide +kernel)

theorem c79653_0 : P.sumLeaves 26 81564672 1024 = 102416 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79653) (lo := 0) (len := 1024) (W := 102416) check rows elimOK (by decide) (by decide) cover79653 (by decide)
  decide +kernel

theorem h79653 : P.leaf 36 79653 = 102416 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 102416)]) (.cons c79653_0 (.nil)) (by decide) (by decide))

theorem cover79654 : P.CoversSplit 26 10 79654 0xcc00cc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 538, 579, 873, 930, 972, 979, 1266, 1273, 1658, 1665]) (by decide +kernel)

theorem c79654_0 : P.sumLeaves 26 81565696 1024 = 96768 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79654) (lo := 0) (len := 1024) (W := 96768) check rows elimOK (by decide) (by decide) cover79654 (by decide)
  decide +kernel

theorem h79654 : P.leaf 36 79654 = 96768 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 96768)]) (.cons c79654_0 (.nil)) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(79547, 720), (79548, 720), (79549, 720), (79550, 720), (79551, 720), (79561, 360), (79563, 720), (79564, 360), (79565, 720), (79566, 720), (79567, 720), (79579, 360), (79580, 720), (79581, 720), (79582, 720), (79583, 720), (79596, 180), (79597, 360), (79598, 720), (79599, 720), (79614, 360), (79615, 360), (79637, 720), (79639, 720), (79641, 720), (79643, 720), (79644, 360), (79645, 720), (79646, 360), (79647, 720), (79653, 360), (79654, 720)]

theorem segOK : checkSeg 20 perms 79547 79655 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 79547 79655 19260 21915848160 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 21915848160)
    (SegSum.cons (w := 720) h79547 (SegSum.cons (w := 720) h79548 (SegSum.cons (w := 720) h79549 (SegSum.cons (w := 720) h79550 (SegSum.cons (w := 720) h79551 (SegSum.cons (w := 360) h79561 (SegSum.cons (w := 720) h79563 (SegSum.cons (w := 360) h79564 (SegSum.cons (w := 720) h79565 (SegSum.cons (w := 720) h79566 (SegSum.cons (w := 720) h79567 (SegSum.cons (w := 360) h79579 (SegSum.cons (w := 720) h79580 (SegSum.cons (w := 720) h79581 (SegSum.cons (w := 720) h79582 (SegSum.cons (w := 720) h79583 (SegSum.cons (w := 180) h79596 (SegSum.cons (w := 360) h79597 (SegSum.cons (w := 720) h79598 (SegSum.cons (w := 720) h79599 (SegSum.cons (w := 360) h79614 (SegSum.cons (w := 360) h79615 (SegSum.cons (w := 720) h79637 (SegSum.cons (w := 720) h79639 (SegSum.cons (w := 720) h79641 (SegSum.cons (w := 720) h79643 (SegSum.cons (w := 360) h79644 (SegSum.cons (w := 720) h79645 (SegSum.cons (w := 360) h79646 (SegSum.cons (w := 720) h79647 (SegSum.cons (w := 360) h79653 (SegSum.cons (w := 720) h79654 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S51
