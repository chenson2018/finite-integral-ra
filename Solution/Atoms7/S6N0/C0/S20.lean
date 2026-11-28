/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Atoms7.S6N0.C0.Actions

/-! Generated identity-class certificate for the product-row count. -/

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option Elab.async false

@[expose] public section

namespace RACert.S6N0.C0.S20

open RACert RACert.Problem

theorem cover12542 : P.CoversSplit 26 10 12542 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h12542 : P.leaf 36 12542 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 12542) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 12542) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover12542 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover12543 : P.CoversSplit 26 10 12543 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h12543 : P.leaf 36 12543 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 12543) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 12543) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover12543 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover12576 : P.CoversSplit 26 10 12576 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem h12576 : P.leaf 36 12576 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 12576) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 12576) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover12576 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover12577 : P.CoversSplit 26 10 12577 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [482]) (by decide +kernel)

theorem h12577 : P.leaf 36 12577 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 12577) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 12577) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover12577 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover12579 : P.CoversSplit 26 10 12579 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [482]) (by decide +kernel)

theorem h12579 : P.leaf 36 12579 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 12579) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 12579) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover12579 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover12581 : P.CoversSplit 26 10 12581 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h12581 : P.leaf 36 12581 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 12581) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 12581) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover12581 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover12583 : P.CoversSplit 26 10 12583 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h12583 : P.leaf 36 12583 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 12583) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 12583) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover12583 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover12591 : P.CoversSplit 26 10 12591 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h12591 : P.leaf 36 12591 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 12591) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 12591) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover12591 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover12593 : P.CoversSplit 26 10 12593 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [482]) (by decide +kernel)

theorem h12593 : P.leaf 36 12593 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 12593) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 12593) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover12593 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover12595 : P.CoversSplit 26 10 12595 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [482]) (by decide +kernel)

theorem h12595 : P.leaf 36 12595 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 12595) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 12595) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover12595 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover12596 : P.CoversSplit 26 10 12596 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h12596 : P.leaf 36 12596 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 12596) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 12596) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover12596 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover12597 : P.CoversSplit 26 10 12597 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h12597 : P.leaf 36 12597 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 12597) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 12597) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover12597 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover12598 : P.CoversSplit 26 10 12598 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h12598 : P.leaf 36 12598 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 12598) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 12598) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover12598 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover12599 : P.CoversSplit 26 10 12599 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h12599 : P.leaf 36 12599 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 12599) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 12599) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover12599 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover12604 : P.CoversSplit 26 10 12604 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h12604 : P.leaf 36 12604 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 12604) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 12604) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover12604 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover12605 : P.CoversSplit 26 10 12605 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h12605 : P.leaf 36 12605 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 12605) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 12605) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover12605 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover12607 : P.CoversSplit 26 10 12607 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h12607 : P.leaf 36 12607 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 12607) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 12607) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover12607 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover12640 : P.CoversSplit 26 10 12640 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem h12640 : P.leaf 36 12640 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 12640) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 12640) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover12640 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover12641 : P.CoversSplit 26 10 12641 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [482]) (by decide +kernel)

theorem h12641 : P.leaf 36 12641 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 12641) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 12641) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover12641 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover12642 : P.CoversSplit 26 10 12642 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [482]) (by decide +kernel)

theorem h12642 : P.leaf 36 12642 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 12642) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 12642) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover12642 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover12643 : P.CoversSplit 26 10 12643 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [482]) (by decide +kernel)

theorem h12643 : P.leaf 36 12643 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 12643) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 12643) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover12643 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover12645 : P.CoversSplit 26 10 12645 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h12645 : P.leaf 36 12645 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 12645) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 12645) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover12645 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover12646 : P.CoversSplit 26 10 12646 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h12646 : P.leaf 36 12646 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 12646) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 12646) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover12646 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover12647 : P.CoversSplit 26 10 12647 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h12647 : P.leaf 36 12647 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 12647) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 12647) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover12647 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover12649 : P.CoversSplit 26 10 12649 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h12649 : P.leaf 36 12649 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 12649) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 12649) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover12649 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover12651 : P.CoversSplit 26 10 12651 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h12651 : P.leaf 36 12651 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 12651) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 12651) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover12651 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover12655 : P.CoversSplit 26 10 12655 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h12655 : P.leaf 36 12655 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 12655) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 12655) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover12655 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover12657 : P.CoversSplit 26 10 12657 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [482]) (by decide +kernel)

theorem h12657 : P.leaf 36 12657 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 12657) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 12657) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover12657 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover12658 : P.CoversSplit 26 10 12658 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [482]) (by decide +kernel)

theorem h12658 : P.leaf 36 12658 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 12658) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 12658) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover12658 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover12659 : P.CoversSplit 26 10 12659 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [482]) (by decide +kernel)

theorem h12659 : P.leaf 36 12659 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 12659) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 12659) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover12659 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover12660 : P.CoversSplit 26 10 12660 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h12660 : P.leaf 36 12660 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 12660) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 12660) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover12660 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover12661 : P.CoversSplit 26 10 12661 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem h12661 : P.leaf 36 12661 = 0 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 12661) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 12661) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover12661 (by decide) (by decide) (by decide +kernel)
  decide +kernel

def seg : List (ℕ × ℕ) := [(12542, 360), (12543, 360), (12576, 30), (12577, 360), (12579, 180), (12581, 360), (12583, 360), (12591, 90), (12593, 360), (12595, 360), (12596, 720), (12597, 720), (12598, 720), (12599, 720), (12604, 360), (12605, 720), (12607, 360), (12640, 120), (12641, 720), (12642, 720), (12643, 720), (12645, 720), (12646, 360), (12647, 720), (12649, 360), (12651, 720), (12655, 360), (12657, 360), (12658, 720), (12659, 720), (12660, 720), (12661, 720)]

theorem segOK : checkSeg 20 perms 12542 12662 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 12542 12662 15900 0 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 0)
    (SegSum.cons (w := 360) h12542 (SegSum.cons (w := 360) h12543 (SegSum.cons (w := 30) h12576 (SegSum.cons (w := 360) h12577 (SegSum.cons (w := 180) h12579 (SegSum.cons (w := 360) h12581 (SegSum.cons (w := 360) h12583 (SegSum.cons (w := 90) h12591 (SegSum.cons (w := 360) h12593 (SegSum.cons (w := 360) h12595 (SegSum.cons (w := 720) h12596 (SegSum.cons (w := 720) h12597 (SegSum.cons (w := 720) h12598 (SegSum.cons (w := 720) h12599 (SegSum.cons (w := 360) h12604 (SegSum.cons (w := 720) h12605 (SegSum.cons (w := 360) h12607 (SegSum.cons (w := 120) h12640 (SegSum.cons (w := 720) h12641 (SegSum.cons (w := 720) h12642 (SegSum.cons (w := 720) h12643 (SegSum.cons (w := 720) h12645 (SegSum.cons (w := 360) h12646 (SegSum.cons (w := 720) h12647 (SegSum.cons (w := 360) h12649 (SegSum.cons (w := 720) h12651 (SegSum.cons (w := 360) h12655 (SegSum.cons (w := 360) h12657 (SegSum.cons (w := 720) h12658 (SegSum.cons (w := 720) h12659 (SegSum.cons (w := 720) h12660 (SegSum.cons (w := 720) h12661 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S20
