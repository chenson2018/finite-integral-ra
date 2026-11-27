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

namespace RACert.S6N0.C0.S145

open RACert RACert.Problem

theorem cover524286 : P.CoversSplit 26 10 524286 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffafaffccfac8fffffffffffffffffffffafafffffafafffffffffffffffffffffafaffccfac8ffffffffffffffffffffffffffffffffffffffffffccffccfffffafaffccfac8fffffffffffffffffffffafafffffafaffffffffffccffccfffffafaffccfac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [1658, 1665]) (by decide +kernel)

theorem c524286_0 : P.sumLeaves 26 536868864 119 = 734372241 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 524286) (lo := 0) (len := 119) (W := 734372241) check rows elimOK (by decide) (by decide) cover524286 (by decide)
  decide +kernel

theorem c524286_1 : P.sumLeaves 26 536868983 104 = 944280355 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 524286) (lo := 119) (len := 104) (W := 944280355) check rows elimOK (by decide) (by decide) cover524286 (by decide)
  decide +kernel

theorem c524286_2 : P.sumLeaves 26 536869087 119 = 1237276844 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 524286) (lo := 223) (len := 119) (W := 1237276844) check rows elimOK (by decide) (by decide) cover524286 (by decide)
  decide +kernel

theorem c524286_3 : P.sumLeaves 26 536869206 96 = 1653564595 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 524286) (lo := 342) (len := 96) (W := 1653564595) check rows elimOK (by decide) (by decide) cover524286 (by decide)
  decide +kernel

theorem c524286_4 : P.sumLeaves 26 536869302 109 = 2297658502 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 524286) (lo := 438) (len := 109) (W := 2297658502) check rows elimOK (by decide) (by decide) cover524286 (by decide)
  decide +kernel

theorem c524286_5 : P.sumLeaves 26 536869411 100 = 1669952835 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 524286) (lo := 547) (len := 100) (W := 1669952835) check rows elimOK (by decide) (by decide) cover524286 (by decide)
  decide +kernel

theorem c524286_6 : P.sumLeaves 26 536869511 102 = 1944752264 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 524286) (lo := 647) (len := 102) (W := 1944752264) check rows elimOK (by decide) (by decide) cover524286 (by decide)
  decide +kernel

theorem c524286_7 : P.sumLeaves 26 536869613 111 = 2129041924 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 524286) (lo := 749) (len := 111) (W := 2129041924) check rows elimOK (by decide) (by decide) cover524286 (by decide)
  decide +kernel

theorem c524286_8 : P.sumLeaves 26 536869724 96 = 2212442532 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 524286) (lo := 860) (len := 96) (W := 2212442532) check rows elimOK (by decide) (by decide) cover524286 (by decide)
  decide +kernel

theorem c524286_9 : P.sumLeaves 26 536869820 68 = 2227425480 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 524286) (lo := 956) (len := 68) (W := 2227425480) check rows elimOK (by decide) (by decide) cover524286 (by decide)
  decide +kernel

theorem h524286 : P.leaf 36 524286 = 17050767572 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(119, 734372241), (104, 944280355), (119, 1237276844), (96, 1653564595), (109, 2297658502), (100, 1669952835), (102, 1944752264), (111, 2129041924), (96, 2212442532), (68, 2227425480)]) (.cons c524286_0 (.cons c524286_1 (.cons c524286_2 (.cons c524286_3 (.cons c524286_4 (.cons c524286_5 (.cons c524286_6 (.cons c524286_7 (.cons c524286_8 (.cons c524286_9 (.nil))))))))))) (by decide) (by decide))

theorem cover524287 : P.CoversSplit 26 10 524287 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffafaffccfac8fffffffffffffffffffffafafffffafafffffffffffffffffffffafaffccfac8ffffffffffffffffffffffffffffffffffffffffffccffccfffffafaffccfac8fffffffffffffffffffffafafffffafaffffffffffccffccfffffafaffccfac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [1658, 1665]) (by decide +kernel)

theorem c524287_0 : P.sumLeaves 26 536869888 119 = 1770234737 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 524287) (lo := 0) (len := 119) (W := 1770234737) check rows elimOK (by decide) (by decide) cover524287 (by decide)
  decide +kernel

theorem c524287_1 : P.sumLeaves 26 536870007 104 = 2038073201 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 524287) (lo := 119) (len := 104) (W := 2038073201) check rows elimOK (by decide) (by decide) cover524287 (by decide)
  decide +kernel

theorem c524287_2 : P.sumLeaves 26 536870111 119 = 2350780740 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 524287) (lo := 223) (len := 119) (W := 2350780740) check rows elimOK (by decide) (by decide) cover524287 (by decide)
  decide +kernel

theorem c524287_3 : P.sumLeaves 26 536870230 96 = 2483217169 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 524287) (lo := 342) (len := 96) (W := 2483217169) check rows elimOK (by decide) (by decide) cover524287 (by decide)
  decide +kernel

theorem c524287_4 : P.sumLeaves 26 536870326 109 = 2924048648 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 524287) (lo := 438) (len := 109) (W := 2924048648) check rows elimOK (by decide) (by decide) cover524287 (by decide)
  decide +kernel

theorem c524287_5 : P.sumLeaves 26 536870435 100 = 2484494869 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 524287) (lo := 547) (len := 100) (W := 2484494869) check rows elimOK (by decide) (by decide) cover524287 (by decide)
  decide +kernel

theorem c524287_6 : P.sumLeaves 26 536870535 102 = 2678640642 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 524287) (lo := 647) (len := 102) (W := 2678640642) check rows elimOK (by decide) (by decide) cover524287 (by decide)
  decide +kernel

theorem c524287_7 : P.sumLeaves 26 536870637 111 = 3000352534 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 524287) (lo := 749) (len := 111) (W := 3000352534) check rows elimOK (by decide) (by decide) cover524287 (by decide)
  decide +kernel

theorem c524287_8 : P.sumLeaves 26 536870748 96 = 2992712562 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 524287) (lo := 860) (len := 96) (W := 2992712562) check rows elimOK (by decide) (by decide) cover524287 (by decide)
  decide +kernel

theorem c524287_9 : P.sumLeaves 26 536870844 68 = 2610153712 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 524287) (lo := 956) (len := 68) (W := 2610153712) check rows elimOK (by decide) (by decide) cover524287 (by decide)
  decide +kernel

theorem h524287 : P.leaf 36 524287 = 25332708814 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(119, 1770234737), (104, 2038073201), (119, 2350780740), (96, 2483217169), (109, 2924048648), (100, 2484494869), (102, 2678640642), (111, 3000352534), (96, 2992712562), (68, 2610153712)]) (.cons c524287_0 (.cons c524287_1 (.cons c524287_2 (.cons c524287_3 (.cons c524287_4 (.cons c524287_5 (.cons c524287_6 (.cons c524287_7 (.cons c524287_8 (.cons c524287_9 (.nil))))))))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(524286, 10), (524287, 20)]

theorem segOK : checkSeg 20 perms 524286 1048575 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 524286 1048575 30 677161852000 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 677161852000)
    (SegSum.cons (w := 10) h524286 (SegSum.cons (w := 20) h524287 (show SegSum (P.leaf 36) [] 0 from rfl))) (by decide)

end RACert.S6N0.C0.S145
