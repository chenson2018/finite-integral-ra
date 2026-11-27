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

namespace RACert.S6N0.C0.S82

open RACert RACert.Problem

theorem cover98133 : P.CoversSplit 26 10 98133 0xff000000ff0005000000000000000000ff000000ff0305000500000005000500050005000500050005000000050000000500050005010500050000000500000000000000000000000000000000000000000000003300010000000000010001000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 579, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c98133_0 : P.sumLeaves 26 100488192 1024 = 96277938 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98133) (lo := 0) (len := 1024) (W := 96277938) check rows elimOK (by decide) (by decide) cover98133 (by decide)
  decide +kernel

theorem h98133 : P.leaf 36 98133 = 96277938 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 96277938)]) (.cons c98133_0 (.nil)) (by decide) (by decide))

theorem cover98135 : P.CoversSplit 26 10 98135 0xff000000ff0005000000000000000000ff000000ff0305000500000005000500050005000500050005000000050000000500050005010500050000000500000000000000000000000000000000000000000000003300010000000000010001000000000000000000000000000000000000000000010001000000000001000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c98135_0 : P.sumLeaves 26 100490240 1024 = 201376273 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98135) (lo := 0) (len := 1024) (W := 201376273) check rows elimOK (by decide) (by decide) cover98135 (by decide)
  decide +kernel

theorem h98135 : P.leaf 36 98135 = 201376273 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 201376273)]) (.cons c98135_0 (.nil)) (by decide) (by decide))

theorem cover98137 : P.CoversSplit 26 10 98137 0xa0a00000a0a000000000000000000000a0a00000a0a0000000000000000000000000000000000000000005050000050500000000000000000000050500000500a0a00000a0a000000000000000000000a0a00000a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 579, 923, 972, 979]) (by decide +kernel)

theorem c98137_0 : P.sumLeaves 26 100492288 1024 = 49044523 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98137) (lo := 0) (len := 1024) (W := 49044523) check rows elimOK (by decide) (by decide) cover98137 (by decide)
  decide +kernel

theorem h98137 : P.leaf 36 98137 = 49044523 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 49044523)]) (.cons c98137_0 (.nil)) (by decide) (by decide))

theorem cover98139 : P.CoversSplit 26 10 98139 0xa0a00000a0a000000000000000000000a0a00000a0a0000000000000000000000000000000000000000005050000050500000000000000000000050500000500a0a00000a0a000000000000000000000a0a00000a000000000000000000000000000000000000000000005050000050500000000000000000000050500000500 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 579, 972, 979]) (by decide +kernel)

theorem c98139_0 : P.sumLeaves 26 100494336 1024 = 109142691 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98139) (lo := 0) (len := 1024) (W := 109142691) check rows elimOK (by decide) (by decide) cover98139 (by decide)
  decide +kernel

theorem h98139 : P.leaf 36 98139 = 109142691 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 109142691)]) (.cons c98139_0 (.nil)) (by decide) (by decide))

theorem cover98140 : P.CoversSplit 26 10 98140 0xffff0000ffff05050000000000000000ffff0000fffc050005050000050005000505050505050505050500000505000005050505050405000505000005000000ffff0000ffff05050000000000000000ffff0000ff00050005050000050005000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 874, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c98140_0 : P.sumLeaves 26 100495360 698 = 33278632 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98140) (lo := 0) (len := 698) (W := 33278632) check rows elimOK (by decide) (by decide) cover98140 (by decide)
  decide +kernel

theorem c98140_1 : P.sumLeaves 26 100496058 326 = 148488416 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98140) (lo := 698) (len := 326) (W := 148488416) check rows elimOK (by decide) (by decide) cover98140 (by decide)
  decide +kernel

theorem h98140 : P.leaf 36 98140 = 181767048 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(698, 33278632), (326, 148488416)]) (.cons c98140_0 (.cons c98140_1 (.nil))) (by decide) (by decide))

theorem cover98141 : P.CoversSplit 26 10 98141 0xffff0000ffff05050000000000000000ffff0000fffc050005050000050005000505050505050505050500000505000005050505050405000505000005000000ffff0000ffff05050000000000000000ffff0000ff00050005050000050005000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 579, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c98141_0 : P.sumLeaves 26 100496384 698 = 59395946 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98141) (lo := 0) (len := 698) (W := 59395946) check rows elimOK (by decide) (by decide) cover98141 (by decide)
  decide +kernel

theorem c98141_1 : P.sumLeaves 26 100497082 326 = 303724557 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98141) (lo := 698) (len := 326) (W := 303724557) check rows elimOK (by decide) (by decide) cover98141 (by decide)
  decide +kernel

theorem h98141 : P.leaf 36 98141 = 363120503 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(698, 59395946), (326, 303724557)]) (.cons c98141_0 (.cons c98141_1 (.nil))) (by decide) (by decide))

theorem cover98143 : P.CoversSplit 26 10 98143 0xffff0000ffff05050000000000000000ffff0000fffc050005050000050005000505050505050505050500000505000005050505050405000505000005000000ffff0000ffff05050000000000000000ffff0000ff00050005050000050005000505050505050505050500000505000005050505050005000505000005000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c98143_0 : P.sumLeaves 26 100498432 496 = 52718126 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98143) (lo := 0) (len := 496) (W := 52718126) check rows elimOK (by decide) (by decide) cover98143 (by decide)
  decide +kernel

theorem c98143_1 : P.sumLeaves 26 100498928 397 = 266972314 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98143) (lo := 496) (len := 397) (W := 266972314) check rows elimOK (by decide) (by decide) cover98143 (by decide)
  decide +kernel

theorem c98143_2 : P.sumLeaves 26 100499325 131 = 376267704 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98143) (lo := 893) (len := 131) (W := 376267704) check rows elimOK (by decide) (by decide) cover98143 (by decide)
  decide +kernel

theorem h98143 : P.leaf 36 98143 = 695958144 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(496, 52718126), (397, 266972314), (131, 376267704)]) (.cons c98143_0 (.cons c98143_1 (.cons c98143_2 (.nil)))) (by decide) (by decide))

theorem cover98147 : P.CoversSplit 26 10 98147 0xf000f000f000f0000000000000000000f000f000f000f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000f000f00000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 579, 972, 979, 1266, 1273, 1658]) (by decide +kernel)

theorem c98147_0 : P.sumLeaves 26 100502528 1024 = 49939272 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98147) (lo := 0) (len := 1024) (W := 49939272) check rows elimOK (by decide) (by decide) cover98147 (by decide)
  decide +kernel

theorem h98147 : P.leaf 36 98147 = 49939272 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 49939272)]) (.cons c98147_0 (.nil)) (by decide) (by decide))

theorem cover98149 : P.CoversSplit 26 10 98149 0xff00ff00ff00fa000000000000000000ff00ff00ff03fa000500050005000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003300320000000000010000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 579, 923, 972, 979, 1266, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c98149_0 : P.sumLeaves 26 100504576 1024 = 23335469 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98149) (lo := 0) (len := 1024) (W := 23335469) check rows elimOK (by decide) (by decide) cover98149 (by decide)
  decide +kernel

theorem h98149 : P.leaf 36 98149 = 23335469 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 23335469)]) (.cons c98149_0 (.nil)) (by decide) (by decide))

theorem cover98150 : P.CoversSplit 26 10 98150 0xff00ff00ff00fa000000000000000000ff00ff00ff03fa000500050005000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003300320000000000010000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 579, 874, 972, 979, 1266, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c98150_0 : P.sumLeaves 26 100505600 1024 = 185607689 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98150) (lo := 0) (len := 1024) (W := 185607689) check rows elimOK (by decide) (by decide) cover98150 (by decide)
  decide +kernel

theorem h98150 : P.leaf 36 98150 = 185607689 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 185607689)]) (.cons c98150_0 (.nil)) (by decide) (by decide))

theorem cover98151 : P.CoversSplit 26 10 98151 0xff00ff00ff00fa000000000000000000ff00ff00ff03fa000500050005000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003300320000000000010000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 579, 972, 979, 1266, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c98151_0 : P.sumLeaves 26 100506624 1024 = 362491499 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98151) (lo := 0) (len := 1024) (W := 362491499) check rows elimOK (by decide) (by decide) cover98151 (by decide)
  decide +kernel

theorem h98151 : P.leaf 36 98151 = 362491499 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 362491499)]) (.cons c98151_0 (.nil)) (by decide) (by decide))

theorem cover98153 : P.CoversSplit 26 10 98153 0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0c000000005000000000000000000000000000000000000000000000000000000000000000000000000f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f000f00000000005000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 579, 923, 972, 979, 1315, 1322, 1658]) (by decide +kernel)

theorem c98153_0 : P.sumLeaves 26 100508672 974 = 14253260 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98153) (lo := 0) (len := 974) (W := 14253260) check rows elimOK (by decide) (by decide) cover98153 (by decide)
  decide +kernel

theorem c98153_1 : P.sumLeaves 26 100509646 50 = 19092796 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98153) (lo := 974) (len := 50) (W := 19092796) check rows elimOK (by decide) (by decide) cover98153 (by decide)
  decide +kernel

theorem h98153 : P.leaf 36 98153 = 33346056 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(974, 14253260), (50, 19092796)]) (.cons c98153_0 (.cons c98153_1 (.nil))) (by decide) (by decide))

theorem cover98154 : P.CoversSplit 26 10 98154 0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0c000000005000000000000000000000000000000000000000000000000000000000000000000000000f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f000f00000000005000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 874, 972, 979, 1266, 1315, 1322, 1658]) (by decide +kernel)

theorem c98154_0 : P.sumLeaves 26 100509696 974 = 49872664 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98154) (lo := 0) (len := 974) (W := 49872664) check rows elimOK (by decide) (by decide) cover98154 (by decide)
  decide +kernel

theorem c98154_1 : P.sumLeaves 26 100510670 50 = 69885918 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98154) (lo := 974) (len := 50) (W := 69885918) check rows elimOK (by decide) (by decide) cover98154 (by decide)
  decide +kernel

theorem h98154 : P.leaf 36 98154 = 119758582 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(974, 49872664), (50, 69885918)]) (.cons c98154_0 (.cons c98154_1 (.nil))) (by decide) (by decide))

theorem cover98155 : P.CoversSplit 26 10 98155 0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0c000000005000000000000000000000000000000000000000000000000000000000000000000000000f0f0f0f0f0f0f0f00000000000000000f0f0f0f0f000f00000000005000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 579, 972, 979, 1266, 1315, 1322, 1658]) (by decide +kernel)

theorem c98155_0 : P.sumLeaves 26 100510720 974 = 137474389 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98155) (lo := 0) (len := 974) (W := 137474389) check rows elimOK (by decide) (by decide) cover98155 (by decide)
  decide +kernel

theorem c98155_1 : P.sumLeaves 26 100511694 50 = 132490876 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98155) (lo := 974) (len := 50) (W := 132490876) check rows elimOK (by decide) (by decide) cover98155 (by decide)
  decide +kernel

theorem h98155 : P.leaf 36 98155 = 269965265 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(974, 137474389), (50, 132490876)]) (.cons c98155_0 (.cons c98155_1 (.nil))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(98133, 720), (98135, 360), (98137, 360), (98139, 360), (98140, 360), (98141, 720), (98143, 360), (98147, 720), (98149, 720), (98150, 720), (98151, 720), (98153, 360), (98154, 720), (98155, 720)]

theorem segOK : checkSeg 20 perms 98133 98156 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 98133 98156 7920 1516185780840 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 1516185780840)
    (SegSum.cons (w := 720) h98133 (SegSum.cons (w := 360) h98135 (SegSum.cons (w := 360) h98137 (SegSum.cons (w := 360) h98139 (SegSum.cons (w := 360) h98140 (SegSum.cons (w := 720) h98141 (SegSum.cons (w := 360) h98143 (SegSum.cons (w := 720) h98147 (SegSum.cons (w := 720) h98149 (SegSum.cons (w := 720) h98150 (SegSum.cons (w := 720) h98151 (SegSum.cons (w := 360) h98153 (SegSum.cons (w := 720) h98154 (SegSum.cons (w := 720) h98155 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))) (by decide)

end RACert.S6N0.C0.S82
