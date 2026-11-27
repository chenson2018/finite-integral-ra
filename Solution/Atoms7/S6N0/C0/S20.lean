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

theorem c12542_0 : P.sumLeaves 26 12843008 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12542) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12542 (by decide)
  decide +kernel

theorem h12542 : P.leaf 36 12542 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12542_0 (.nil)) (by decide) (by decide))

theorem cover12543 : P.CoversSplit 26 10 12543 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c12543_0 : P.sumLeaves 26 12844032 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12543) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12543 (by decide)
  decide +kernel

theorem h12543 : P.leaf 36 12543 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12543_0 (.nil)) (by decide) (by decide))

theorem cover12576 : P.CoversSplit 26 10 12576 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem c12576_0 : P.sumLeaves 26 12877824 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12576) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12576 (by decide)
  decide +kernel

theorem h12576 : P.leaf 36 12576 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12576_0 (.nil)) (by decide) (by decide))

theorem cover12577 : P.CoversSplit 26 10 12577 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [482]) (by decide +kernel)

theorem c12577_0 : P.sumLeaves 26 12878848 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12577) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12577 (by decide)
  decide +kernel

theorem h12577 : P.leaf 36 12577 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12577_0 (.nil)) (by decide) (by decide))

theorem cover12579 : P.CoversSplit 26 10 12579 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [482]) (by decide +kernel)

theorem c12579_0 : P.sumLeaves 26 12880896 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12579) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12579 (by decide)
  decide +kernel

theorem h12579 : P.leaf 36 12579 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12579_0 (.nil)) (by decide) (by decide))

theorem cover12581 : P.CoversSplit 26 10 12581 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c12581_0 : P.sumLeaves 26 12882944 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12581) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12581 (by decide)
  decide +kernel

theorem h12581 : P.leaf 36 12581 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12581_0 (.nil)) (by decide) (by decide))

theorem cover12583 : P.CoversSplit 26 10 12583 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c12583_0 : P.sumLeaves 26 12884992 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12583) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12583 (by decide)
  decide +kernel

theorem h12583 : P.leaf 36 12583 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12583_0 (.nil)) (by decide) (by decide))

theorem cover12591 : P.CoversSplit 26 10 12591 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c12591_0 : P.sumLeaves 26 12893184 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12591) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12591 (by decide)
  decide +kernel

theorem h12591 : P.leaf 36 12591 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12591_0 (.nil)) (by decide) (by decide))

theorem cover12593 : P.CoversSplit 26 10 12593 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [482]) (by decide +kernel)

theorem c12593_0 : P.sumLeaves 26 12895232 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12593) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12593 (by decide)
  decide +kernel

theorem h12593 : P.leaf 36 12593 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12593_0 (.nil)) (by decide) (by decide))

theorem cover12595 : P.CoversSplit 26 10 12595 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [482]) (by decide +kernel)

theorem c12595_0 : P.sumLeaves 26 12897280 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12595) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12595 (by decide)
  decide +kernel

theorem h12595 : P.leaf 36 12595 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12595_0 (.nil)) (by decide) (by decide))

theorem cover12596 : P.CoversSplit 26 10 12596 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c12596_0 : P.sumLeaves 26 12898304 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12596) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12596 (by decide)
  decide +kernel

theorem h12596 : P.leaf 36 12596 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12596_0 (.nil)) (by decide) (by decide))

theorem cover12597 : P.CoversSplit 26 10 12597 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c12597_0 : P.sumLeaves 26 12899328 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12597) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12597 (by decide)
  decide +kernel

theorem h12597 : P.leaf 36 12597 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12597_0 (.nil)) (by decide) (by decide))

theorem cover12598 : P.CoversSplit 26 10 12598 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c12598_0 : P.sumLeaves 26 12900352 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12598) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12598 (by decide)
  decide +kernel

theorem h12598 : P.leaf 36 12598 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12598_0 (.nil)) (by decide) (by decide))

theorem cover12599 : P.CoversSplit 26 10 12599 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c12599_0 : P.sumLeaves 26 12901376 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12599) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12599 (by decide)
  decide +kernel

theorem h12599 : P.leaf 36 12599 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12599_0 (.nil)) (by decide) (by decide))

theorem cover12604 : P.CoversSplit 26 10 12604 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c12604_0 : P.sumLeaves 26 12906496 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12604) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12604 (by decide)
  decide +kernel

theorem h12604 : P.leaf 36 12604 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12604_0 (.nil)) (by decide) (by decide))

theorem cover12605 : P.CoversSplit 26 10 12605 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c12605_0 : P.sumLeaves 26 12907520 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12605) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12605 (by decide)
  decide +kernel

theorem h12605 : P.leaf 36 12605 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12605_0 (.nil)) (by decide) (by decide))

theorem cover12607 : P.CoversSplit 26 10 12607 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c12607_0 : P.sumLeaves 26 12909568 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12607) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12607 (by decide)
  decide +kernel

theorem h12607 : P.leaf 36 12607 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12607_0 (.nil)) (by decide) (by decide))

theorem cover12640 : P.CoversSplit 26 10 12640 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem c12640_0 : P.sumLeaves 26 12943360 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12640) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12640 (by decide)
  decide +kernel

theorem h12640 : P.leaf 36 12640 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12640_0 (.nil)) (by decide) (by decide))

theorem cover12641 : P.CoversSplit 26 10 12641 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [482]) (by decide +kernel)

theorem c12641_0 : P.sumLeaves 26 12944384 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12641) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12641 (by decide)
  decide +kernel

theorem h12641 : P.leaf 36 12641 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12641_0 (.nil)) (by decide) (by decide))

theorem cover12642 : P.CoversSplit 26 10 12642 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [482]) (by decide +kernel)

theorem c12642_0 : P.sumLeaves 26 12945408 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12642) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12642 (by decide)
  decide +kernel

theorem h12642 : P.leaf 36 12642 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12642_0 (.nil)) (by decide) (by decide))

theorem cover12643 : P.CoversSplit 26 10 12643 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [482]) (by decide +kernel)

theorem c12643_0 : P.sumLeaves 26 12946432 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12643) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12643 (by decide)
  decide +kernel

theorem h12643 : P.leaf 36 12643 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12643_0 (.nil)) (by decide) (by decide))

theorem cover12645 : P.CoversSplit 26 10 12645 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c12645_0 : P.sumLeaves 26 12948480 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12645) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12645 (by decide)
  decide +kernel

theorem h12645 : P.leaf 36 12645 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12645_0 (.nil)) (by decide) (by decide))

theorem cover12646 : P.CoversSplit 26 10 12646 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c12646_0 : P.sumLeaves 26 12949504 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12646) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12646 (by decide)
  decide +kernel

theorem h12646 : P.leaf 36 12646 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12646_0 (.nil)) (by decide) (by decide))

theorem cover12647 : P.CoversSplit 26 10 12647 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c12647_0 : P.sumLeaves 26 12950528 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12647) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12647 (by decide)
  decide +kernel

theorem h12647 : P.leaf 36 12647 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12647_0 (.nil)) (by decide) (by decide))

theorem cover12649 : P.CoversSplit 26 10 12649 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c12649_0 : P.sumLeaves 26 12952576 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12649) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12649 (by decide)
  decide +kernel

theorem h12649 : P.leaf 36 12649 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12649_0 (.nil)) (by decide) (by decide))

theorem cover12651 : P.CoversSplit 26 10 12651 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c12651_0 : P.sumLeaves 26 12954624 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12651) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12651 (by decide)
  decide +kernel

theorem h12651 : P.leaf 36 12651 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12651_0 (.nil)) (by decide) (by decide))

theorem cover12655 : P.CoversSplit 26 10 12655 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c12655_0 : P.sumLeaves 26 12958720 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12655) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12655 (by decide)
  decide +kernel

theorem h12655 : P.leaf 36 12655 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12655_0 (.nil)) (by decide) (by decide))

theorem cover12657 : P.CoversSplit 26 10 12657 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [482]) (by decide +kernel)

theorem c12657_0 : P.sumLeaves 26 12960768 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12657) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12657 (by decide)
  decide +kernel

theorem h12657 : P.leaf 36 12657 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12657_0 (.nil)) (by decide) (by decide))

theorem cover12658 : P.CoversSplit 26 10 12658 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [482]) (by decide +kernel)

theorem c12658_0 : P.sumLeaves 26 12961792 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12658) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12658 (by decide)
  decide +kernel

theorem h12658 : P.leaf 36 12658 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12658_0 (.nil)) (by decide) (by decide))

theorem cover12659 : P.CoversSplit 26 10 12659 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [482]) (by decide +kernel)

theorem c12659_0 : P.sumLeaves 26 12962816 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12659) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12659 (by decide)
  decide +kernel

theorem h12659 : P.leaf 36 12659 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12659_0 (.nil)) (by decide) (by decide))

theorem cover12660 : P.CoversSplit 26 10 12660 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c12660_0 : P.sumLeaves 26 12963840 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12660) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12660 (by decide)
  decide +kernel

theorem h12660 : P.leaf 36 12660 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12660_0 (.nil)) (by decide) (by decide))

theorem cover12661 : P.CoversSplit 26 10 12661 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c12661_0 : P.sumLeaves 26 12964864 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12661) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12661 (by decide)
  decide +kernel

theorem h12661 : P.leaf 36 12661 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12661_0 (.nil)) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(12542, 360), (12543, 360), (12576, 30), (12577, 360), (12579, 180), (12581, 360), (12583, 360), (12591, 90), (12593, 360), (12595, 360), (12596, 720), (12597, 720), (12598, 720), (12599, 720), (12604, 360), (12605, 720), (12607, 360), (12640, 120), (12641, 720), (12642, 720), (12643, 720), (12645, 720), (12646, 360), (12647, 720), (12649, 360), (12651, 720), (12655, 360), (12657, 360), (12658, 720), (12659, 720), (12660, 720), (12661, 720)]

theorem segOK : checkSeg 20 perms 12542 12662 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 12542 12662 15900 0 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 0)
    (SegSum.cons (w := 360) h12542 (SegSum.cons (w := 360) h12543 (SegSum.cons (w := 30) h12576 (SegSum.cons (w := 360) h12577 (SegSum.cons (w := 180) h12579 (SegSum.cons (w := 360) h12581 (SegSum.cons (w := 360) h12583 (SegSum.cons (w := 90) h12591 (SegSum.cons (w := 360) h12593 (SegSum.cons (w := 360) h12595 (SegSum.cons (w := 720) h12596 (SegSum.cons (w := 720) h12597 (SegSum.cons (w := 720) h12598 (SegSum.cons (w := 720) h12599 (SegSum.cons (w := 360) h12604 (SegSum.cons (w := 720) h12605 (SegSum.cons (w := 360) h12607 (SegSum.cons (w := 120) h12640 (SegSum.cons (w := 720) h12641 (SegSum.cons (w := 720) h12642 (SegSum.cons (w := 720) h12643 (SegSum.cons (w := 720) h12645 (SegSum.cons (w := 360) h12646 (SegSum.cons (w := 720) h12647 (SegSum.cons (w := 360) h12649 (SegSum.cons (w := 720) h12651 (SegSum.cons (w := 360) h12655 (SegSum.cons (w := 360) h12657 (SegSum.cons (w := 720) h12658 (SegSum.cons (w := 720) h12659 (SegSum.cons (w := 720) h12660 (SegSum.cons (w := 720) h12661 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S20
