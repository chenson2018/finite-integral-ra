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

namespace RACert.S6N0.C0.S17

open RACert RACert.Problem

theorem cover11622 : P.CoversSplit 26 10 11622 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c11622_0 : P.sumLeaves 26 11900928 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 11622) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover11622 (by decide)
  decide +kernel

theorem h11622 : P.leaf 36 11622 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c11622_0 (.nil)) (by decide) (by decide))

theorem cover11623 : P.CoversSplit 26 10 11623 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c11623_0 : P.sumLeaves 26 11901952 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 11623) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover11623 (by decide)
  decide +kernel

theorem h11623 : P.leaf 36 11623 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c11623_0 (.nil)) (by decide) (by decide))

theorem cover11624 : P.CoversSplit 26 10 11624 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c11624_0 : P.sumLeaves 26 11902976 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 11624) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover11624 (by decide)
  decide +kernel

theorem h11624 : P.leaf 36 11624 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c11624_0 (.nil)) (by decide) (by decide))

theorem cover11625 : P.CoversSplit 26 10 11625 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c11625_0 : P.sumLeaves 26 11904000 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 11625) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover11625 (by decide)
  decide +kernel

theorem h11625 : P.leaf 36 11625 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c11625_0 (.nil)) (by decide) (by decide))

theorem cover11626 : P.CoversSplit 26 10 11626 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c11626_0 : P.sumLeaves 26 11905024 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 11626) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover11626 (by decide)
  decide +kernel

theorem h11626 : P.leaf 36 11626 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c11626_0 (.nil)) (by decide) (by decide))

theorem cover11627 : P.CoversSplit 26 10 11627 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c11627_0 : P.sumLeaves 26 11906048 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 11627) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover11627 (by decide)
  decide +kernel

theorem h11627 : P.leaf 36 11627 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c11627_0 (.nil)) (by decide) (by decide))

theorem cover11628 : P.CoversSplit 26 10 11628 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c11628_0 : P.sumLeaves 26 11907072 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 11628) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover11628 (by decide)
  decide +kernel

theorem h11628 : P.leaf 36 11628 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c11628_0 (.nil)) (by decide) (by decide))

theorem cover11629 : P.CoversSplit 26 10 11629 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c11629_0 : P.sumLeaves 26 11908096 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 11629) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover11629 (by decide)
  decide +kernel

theorem h11629 : P.leaf 36 11629 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c11629_0 (.nil)) (by decide) (by decide))

theorem cover11630 : P.CoversSplit 26 10 11630 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c11630_0 : P.sumLeaves 26 11909120 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 11630) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover11630 (by decide)
  decide +kernel

theorem h11630 : P.leaf 36 11630 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c11630_0 (.nil)) (by decide) (by decide))

theorem cover11631 : P.CoversSplit 26 10 11631 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c11631_0 : P.sumLeaves 26 11910144 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 11631) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover11631 (by decide)
  decide +kernel

theorem h11631 : P.leaf 36 11631 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c11631_0 (.nil)) (by decide) (by decide))

theorem cover11632 : P.CoversSplit 26 10 11632 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [482]) (by decide +kernel)

theorem c11632_0 : P.sumLeaves 26 11911168 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 11632) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover11632 (by decide)
  decide +kernel

theorem h11632 : P.leaf 36 11632 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c11632_0 (.nil)) (by decide) (by decide))

theorem cover11633 : P.CoversSplit 26 10 11633 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [482]) (by decide +kernel)

theorem c11633_0 : P.sumLeaves 26 11912192 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 11633) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover11633 (by decide)
  decide +kernel

theorem h11633 : P.leaf 36 11633 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c11633_0 (.nil)) (by decide) (by decide))

theorem cover11634 : P.CoversSplit 26 10 11634 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [482]) (by decide +kernel)

theorem c11634_0 : P.sumLeaves 26 11913216 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 11634) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover11634 (by decide)
  decide +kernel

theorem h11634 : P.leaf 36 11634 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c11634_0 (.nil)) (by decide) (by decide))

theorem cover11635 : P.CoversSplit 26 10 11635 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [482]) (by decide +kernel)

theorem c11635_0 : P.sumLeaves 26 11914240 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 11635) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover11635 (by decide)
  decide +kernel

theorem h11635 : P.leaf 36 11635 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c11635_0 (.nil)) (by decide) (by decide))

theorem cover11636 : P.CoversSplit 26 10 11636 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c11636_0 : P.sumLeaves 26 11915264 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 11636) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover11636 (by decide)
  decide +kernel

theorem h11636 : P.leaf 36 11636 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c11636_0 (.nil)) (by decide) (by decide))

theorem cover11637 : P.CoversSplit 26 10 11637 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c11637_0 : P.sumLeaves 26 11916288 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 11637) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover11637 (by decide)
  decide +kernel

theorem h11637 : P.leaf 36 11637 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c11637_0 (.nil)) (by decide) (by decide))

theorem cover11638 : P.CoversSplit 26 10 11638 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c11638_0 : P.sumLeaves 26 11917312 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 11638) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover11638 (by decide)
  decide +kernel

theorem h11638 : P.leaf 36 11638 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c11638_0 (.nil)) (by decide) (by decide))

theorem cover11639 : P.CoversSplit 26 10 11639 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c11639_0 : P.sumLeaves 26 11918336 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 11639) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover11639 (by decide)
  decide +kernel

theorem h11639 : P.leaf 36 11639 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c11639_0 (.nil)) (by decide) (by decide))

theorem cover11640 : P.CoversSplit 26 10 11640 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c11640_0 : P.sumLeaves 26 11919360 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 11640) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover11640 (by decide)
  decide +kernel

theorem h11640 : P.leaf 36 11640 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c11640_0 (.nil)) (by decide) (by decide))

theorem cover11641 : P.CoversSplit 26 10 11641 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c11641_0 : P.sumLeaves 26 11920384 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 11641) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover11641 (by decide)
  decide +kernel

theorem h11641 : P.leaf 36 11641 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c11641_0 (.nil)) (by decide) (by decide))

theorem cover11642 : P.CoversSplit 26 10 11642 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c11642_0 : P.sumLeaves 26 11921408 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 11642) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover11642 (by decide)
  decide +kernel

theorem h11642 : P.leaf 36 11642 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c11642_0 (.nil)) (by decide) (by decide))

theorem cover11643 : P.CoversSplit 26 10 11643 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c11643_0 : P.sumLeaves 26 11922432 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 11643) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover11643 (by decide)
  decide +kernel

theorem h11643 : P.leaf 36 11643 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c11643_0 (.nil)) (by decide) (by decide))

theorem cover11644 : P.CoversSplit 26 10 11644 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c11644_0 : P.sumLeaves 26 11923456 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 11644) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover11644 (by decide)
  decide +kernel

theorem h11644 : P.leaf 36 11644 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c11644_0 (.nil)) (by decide) (by decide))

theorem cover11645 : P.CoversSplit 26 10 11645 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c11645_0 : P.sumLeaves 26 11924480 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 11645) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover11645 (by decide)
  decide +kernel

theorem h11645 : P.leaf 36 11645 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c11645_0 (.nil)) (by decide) (by decide))

theorem cover11646 : P.CoversSplit 26 10 11646 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c11646_0 : P.sumLeaves 26 11925504 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 11646) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover11646 (by decide)
  decide +kernel

theorem h11646 : P.leaf 36 11646 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c11646_0 (.nil)) (by decide) (by decide))

theorem cover11647 : P.CoversSplit 26 10 11647 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c11647_0 : P.sumLeaves 26 11926528 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 11647) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover11647 (by decide)
  decide +kernel

theorem h11647 : P.leaf 36 11647 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c11647_0 (.nil)) (by decide) (by decide))

theorem cover11744 : P.CoversSplit 26 10 11744 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [482]) (by decide +kernel)

theorem c11744_0 : P.sumLeaves 26 12025856 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 11744) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover11744 (by decide)
  decide +kernel

theorem h11744 : P.leaf 36 11744 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c11744_0 (.nil)) (by decide) (by decide))

theorem cover11745 : P.CoversSplit 26 10 11745 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [482]) (by decide +kernel)

theorem c11745_0 : P.sumLeaves 26 12026880 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 11745) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover11745 (by decide)
  decide +kernel

theorem h11745 : P.leaf 36 11745 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c11745_0 (.nil)) (by decide) (by decide))

theorem cover11747 : P.CoversSplit 26 10 11747 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [482]) (by decide +kernel)

theorem c11747_0 : P.sumLeaves 26 12028928 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 11747) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover11747 (by decide)
  decide +kernel

theorem h11747 : P.leaf 36 11747 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c11747_0 (.nil)) (by decide) (by decide))

theorem cover11748 : P.CoversSplit 26 10 11748 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c11748_0 : P.sumLeaves 26 12029952 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 11748) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover11748 (by decide)
  decide +kernel

theorem h11748 : P.leaf 36 11748 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c11748_0 (.nil)) (by decide) (by decide))

theorem cover11749 : P.CoversSplit 26 10 11749 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c11749_0 : P.sumLeaves 26 12030976 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 11749) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover11749 (by decide)
  decide +kernel

theorem h11749 : P.leaf 36 11749 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c11749_0 (.nil)) (by decide) (by decide))

theorem cover11751 : P.CoversSplit 26 10 11751 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c11751_0 : P.sumLeaves 26 12033024 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 11751) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover11751 (by decide)
  decide +kernel

theorem h11751 : P.leaf 36 11751 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c11751_0 (.nil)) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(11622, 720), (11623, 720), (11624, 720), (11625, 720), (11626, 720), (11627, 720), (11628, 720), (11629, 720), (11630, 720), (11631, 720), (11632, 720), (11633, 720), (11634, 720), (11635, 720), (11636, 720), (11637, 720), (11638, 720), (11639, 720), (11640, 720), (11641, 720), (11642, 720), (11643, 720), (11644, 720), (11645, 720), (11646, 720), (11647, 720), (11744, 360), (11745, 720), (11747, 360), (11748, 360), (11749, 720), (11751, 360)]

theorem segOK : checkSeg 20 perms 11622 11752 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 11622 11752 21600 0 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 0)
    (SegSum.cons (w := 720) h11622 (SegSum.cons (w := 720) h11623 (SegSum.cons (w := 720) h11624 (SegSum.cons (w := 720) h11625 (SegSum.cons (w := 720) h11626 (SegSum.cons (w := 720) h11627 (SegSum.cons (w := 720) h11628 (SegSum.cons (w := 720) h11629 (SegSum.cons (w := 720) h11630 (SegSum.cons (w := 720) h11631 (SegSum.cons (w := 720) h11632 (SegSum.cons (w := 720) h11633 (SegSum.cons (w := 720) h11634 (SegSum.cons (w := 720) h11635 (SegSum.cons (w := 720) h11636 (SegSum.cons (w := 720) h11637 (SegSum.cons (w := 720) h11638 (SegSum.cons (w := 720) h11639 (SegSum.cons (w := 720) h11640 (SegSum.cons (w := 720) h11641 (SegSum.cons (w := 720) h11642 (SegSum.cons (w := 720) h11643 (SegSum.cons (w := 720) h11644 (SegSum.cons (w := 720) h11645 (SegSum.cons (w := 720) h11646 (SegSum.cons (w := 720) h11647 (SegSum.cons (w := 360) h11744 (SegSum.cons (w := 720) h11745 (SegSum.cons (w := 360) h11747 (SegSum.cons (w := 360) h11748 (SegSum.cons (w := 720) h11749 (SegSum.cons (w := 360) h11751 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S17
