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

namespace RACert.S6N0.C0.S21

open RACert RACert.Problem

theorem cover12662 : P.CoversSplit 26 10 12662 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c12662_0 : P.sumLeaves 26 12965888 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12662) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12662 (by decide)
  decide +kernel

theorem h12662 : P.leaf 36 12662 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12662_0 (.nil)) (by decide) (by decide))

theorem cover12663 : P.CoversSplit 26 10 12663 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c12663_0 : P.sumLeaves 26 12966912 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12663) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12663 (by decide)
  decide +kernel

theorem h12663 : P.leaf 36 12663 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12663_0 (.nil)) (by decide) (by decide))

theorem cover12664 : P.CoversSplit 26 10 12664 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c12664_0 : P.sumLeaves 26 12967936 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12664) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12664 (by decide)
  decide +kernel

theorem h12664 : P.leaf 36 12664 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12664_0 (.nil)) (by decide) (by decide))

theorem cover12665 : P.CoversSplit 26 10 12665 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c12665_0 : P.sumLeaves 26 12968960 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12665) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12665 (by decide)
  decide +kernel

theorem h12665 : P.leaf 36 12665 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12665_0 (.nil)) (by decide) (by decide))

theorem cover12666 : P.CoversSplit 26 10 12666 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c12666_0 : P.sumLeaves 26 12969984 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12666) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12666 (by decide)
  decide +kernel

theorem h12666 : P.leaf 36 12666 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12666_0 (.nil)) (by decide) (by decide))

theorem cover12667 : P.CoversSplit 26 10 12667 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c12667_0 : P.sumLeaves 26 12971008 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12667) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12667 (by decide)
  decide +kernel

theorem h12667 : P.leaf 36 12667 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12667_0 (.nil)) (by decide) (by decide))

theorem cover12668 : P.CoversSplit 26 10 12668 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c12668_0 : P.sumLeaves 26 12972032 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12668) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12668 (by decide)
  decide +kernel

theorem h12668 : P.leaf 36 12668 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12668_0 (.nil)) (by decide) (by decide))

theorem cover12669 : P.CoversSplit 26 10 12669 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c12669_0 : P.sumLeaves 26 12973056 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12669) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12669 (by decide)
  decide +kernel

theorem h12669 : P.leaf 36 12669 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12669_0 (.nil)) (by decide) (by decide))

theorem cover12670 : P.CoversSplit 26 10 12670 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c12670_0 : P.sumLeaves 26 12974080 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12670) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12670 (by decide)
  decide +kernel

theorem h12670 : P.leaf 36 12670 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12670_0 (.nil)) (by decide) (by decide))

theorem cover12671 : P.CoversSplit 26 10 12671 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c12671_0 : P.sumLeaves 26 12975104 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12671) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12671 (by decide)
  decide +kernel

theorem h12671 : P.leaf 36 12671 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12671_0 (.nil)) (by decide) (by decide))

theorem cover12768 : P.CoversSplit 26 10 12768 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem c12768_0 : P.sumLeaves 26 13074432 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12768) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12768 (by decide)
  decide +kernel

theorem h12768 : P.leaf 36 12768 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12768_0 (.nil)) (by decide) (by decide))

theorem cover12769 : P.CoversSplit 26 10 12769 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [482]) (by decide +kernel)

theorem c12769_0 : P.sumLeaves 26 13075456 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12769) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12769 (by decide)
  decide +kernel

theorem h12769 : P.leaf 36 12769 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12769_0 (.nil)) (by decide) (by decide))

theorem cover12771 : P.CoversSplit 26 10 12771 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [482]) (by decide +kernel)

theorem c12771_0 : P.sumLeaves 26 13077504 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12771) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12771 (by decide)
  decide +kernel

theorem h12771 : P.leaf 36 12771 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12771_0 (.nil)) (by decide) (by decide))

theorem cover12773 : P.CoversSplit 26 10 12773 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c12773_0 : P.sumLeaves 26 13079552 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12773) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12773 (by decide)
  decide +kernel

theorem h12773 : P.leaf 36 12773 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12773_0 (.nil)) (by decide) (by decide))

theorem cover12774 : P.CoversSplit 26 10 12774 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c12774_0 : P.sumLeaves 26 13080576 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12774) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12774 (by decide)
  decide +kernel

theorem h12774 : P.leaf 36 12774 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12774_0 (.nil)) (by decide) (by decide))

theorem cover12775 : P.CoversSplit 26 10 12775 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c12775_0 : P.sumLeaves 26 13081600 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12775) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12775 (by decide)
  decide +kernel

theorem h12775 : P.leaf 36 12775 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12775_0 (.nil)) (by decide) (by decide))

theorem cover12783 : P.CoversSplit 26 10 12783 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c12783_0 : P.sumLeaves 26 13089792 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12783) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12783 (by decide)
  decide +kernel

theorem h12783 : P.leaf 36 12783 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12783_0 (.nil)) (by decide) (by decide))

theorem cover12784 : P.CoversSplit 26 10 12784 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [482]) (by decide +kernel)

theorem c12784_0 : P.sumLeaves 26 13090816 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12784) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12784 (by decide)
  decide +kernel

theorem h12784 : P.leaf 36 12784 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12784_0 (.nil)) (by decide) (by decide))

theorem cover12785 : P.CoversSplit 26 10 12785 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [482]) (by decide +kernel)

theorem c12785_0 : P.sumLeaves 26 13091840 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12785) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12785 (by decide)
  decide +kernel

theorem h12785 : P.leaf 36 12785 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12785_0 (.nil)) (by decide) (by decide))

theorem cover12787 : P.CoversSplit 26 10 12787 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [482]) (by decide +kernel)

theorem c12787_0 : P.sumLeaves 26 13093888 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12787) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12787 (by decide)
  decide +kernel

theorem h12787 : P.leaf 36 12787 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12787_0 (.nil)) (by decide) (by decide))

theorem cover12788 : P.CoversSplit 26 10 12788 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c12788_0 : P.sumLeaves 26 13094912 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12788) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12788 (by decide)
  decide +kernel

theorem h12788 : P.leaf 36 12788 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12788_0 (.nil)) (by decide) (by decide))

theorem cover12789 : P.CoversSplit 26 10 12789 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c12789_0 : P.sumLeaves 26 13095936 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12789) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12789 (by decide)
  decide +kernel

theorem h12789 : P.leaf 36 12789 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12789_0 (.nil)) (by decide) (by decide))

theorem cover12790 : P.CoversSplit 26 10 12790 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c12790_0 : P.sumLeaves 26 13096960 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12790) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12790 (by decide)
  decide +kernel

theorem h12790 : P.leaf 36 12790 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12790_0 (.nil)) (by decide) (by decide))

theorem cover12791 : P.CoversSplit 26 10 12791 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c12791_0 : P.sumLeaves 26 13097984 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12791) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12791 (by decide)
  decide +kernel

theorem h12791 : P.leaf 36 12791 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12791_0 (.nil)) (by decide) (by decide))

theorem cover12796 : P.CoversSplit 26 10 12796 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c12796_0 : P.sumLeaves 26 13103104 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12796) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12796 (by decide)
  decide +kernel

theorem h12796 : P.leaf 36 12796 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12796_0 (.nil)) (by decide) (by decide))

theorem cover12797 : P.CoversSplit 26 10 12797 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c12797_0 : P.sumLeaves 26 13104128 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12797) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12797 (by decide)
  decide +kernel

theorem h12797 : P.leaf 36 12797 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12797_0 (.nil)) (by decide) (by decide))

theorem cover12799 : P.CoversSplit 26 10 12799 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c12799_0 : P.sumLeaves 26 13106176 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12799) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12799 (by decide)
  decide +kernel

theorem h12799 : P.leaf 36 12799 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12799_0 (.nil)) (by decide) (by decide))

theorem cover13104 : P.CoversSplit 26 10 13104 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000010000000100000001000 :=
  coversProjected check rows (by decide) (by decide) (xs := [538, 579, 873, 930, 972, 979, 1265, 1273, 1315, 1665]) (ps := [(7, [468, 474], [468, 474])]) (by decide +kernel)

noncomputable def f13104 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 26 (13418496 + i)

theorem c13104_0 : rowSum f13104 0 1024 = 145 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 13104) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover13104 (by decide)
  decide +kernel

theorem sum13104 : rowSum f13104 0 1024 = 145 :=
  c13104_0

theorem h13104 : P.leaf 36 13104 = 145 :=
  leaf_weighted (k := 26) (d := 10) (H := 13104) (keep := keep2) (twice := twice2) rows (by decide) (by decide) bal2 (invRow2 (H := 13104) (by decide) (by decide +kernel)) sum13104

theorem cover13105 : P.CoversSplit 26 10 13105 0x8000000000000000000000000000000000000000000000000000000000000000000040000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 538, 579, 873, 930, 972, 979, 1273, 1315, 1665]) (by decide +kernel)

theorem c13105_0 : P.sumLeaves 26 13419520 1024 = 1968 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13105) (lo := 0) (len := 1024) (W := 1968) check rows elimOK (by decide) (by decide) cover13105 (by decide)
  decide +kernel

theorem h13105 : P.leaf 36 13105 = 1968 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1968)]) (.cons c13105_0 (.nil)) (by decide) (by decide))

theorem cover13107 : P.CoversSplit 26 10 13107 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 538, 579, 873, 930, 972, 979, 1315, 1665]) (by decide +kernel)

theorem c13107_0 : P.sumLeaves 26 13421568 1024 = 23552 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13107) (lo := 0) (len := 1024) (W := 23552) check rows elimOK (by decide) (by decide) cover13107 (by decide)
  decide +kernel

theorem h13107 : P.leaf 36 13107 = 23552 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 23552)]) (.cons c13107_0 (.nil)) (by decide) (by decide))

theorem cover13110 : P.CoversSplit 26 10 13110 0xcc00440000000000000000000000000000000000000000000000000000000000440040000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000330011003300100011001100110010000000000000000000000000000000000011001000110010001100100011001000 :=
  coversProjected check rows (by decide) (by decide) (xs := [489, 538, 579, 873, 930, 972, 979, 1265, 1315, 1658, 1665]) (ps := [(16, [867], [1265])]) (by decide +kernel)

theorem contract13110_0 : P.leaf 32 209760 = 396 := by
  exact leaf_contract_factors (k := 32) (b := 12) (H := 209760) (ss := [(29, 7, 468), (2, 1, 482), (8, 7, 486), (3, 1, 537), (20, 4, 580), (5, 4, 586), (10, 1, 866), (16, 0, 867), (7, 0, 858), (11, 0, 458), (12, 0, 458), (17, 0, 465), (23, 1, 817), (13, 1, 923), (14, 1, 1209), (28, 0, 1265), (26, 4, 481), (31, 1, 1665), (6, 1, 636), (22, 4, 433)]) (ids := [2, 7, 13, 16, 17, 19, 23, 28, 30, 31, 22, 25]) (cs := [1, 1, 2, 2, 1, 0, 0, 3, 1, 0, 0, 1, 1, 4, 0, 0, 5, 6, 2, 7, 2, 1, 12, 8, 2, 13, 0, 0, 9, 1, 10, 11]) (bs := [10, 2]) (W := 396) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c13110_0 : P.sumLeaves 26 13424640 64 = 396 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 209760) rows (by decide) (by decide)).symm.trans contract13110_0

theorem contract13110_1 : P.leaf 32 209761 = 248 := by
  exact leaf_contract_factors (k := 32) (b := 10) (H := 209761) (ss := [(29, 7, 468), (2, 1, 482), (8, 7, 486), (3, 1, 537), (4, 1, 580), (5, 1, 586), (10, 1, 866), (16, 0, 867), (7, 0, 858), (11, 0, 458), (12, 0, 458), (17, 0, 465), (23, 1, 817), (13, 1, 923), (14, 1, 1209), (21, 0, 1658), (9, 0, 1609), (22, 6, 426), (28, 0, 1658), (32, 19, 1265), (31, 1, 1665), (6, 1, 587)]) (ids := [13, 16, 17, 18, 23, 24, 28, 22, 25, 31]) (cs := [1, 1, 1, 1, 1, 0, 0, 0, 1, 0, 0, 1, 1, 2, 0, 0, 3, 4, 5, 0, 1, 1, 9, 6, 7, 10, 0, 0, 8, 1, 4, 11]) (bs := [7, 3]) (W := 248) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c13110_1 : P.sumLeaves 26 13424704 64 = 248 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 209761) rows (by decide) (by decide)).symm.trans contract13110_1

theorem c13110_2 : P.sumLeaves 26 13424768 128 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13110) (lo := 128) (len := 128) (W := 0) check rows elimOK (by decide) (by decide) cover13110 (by decide)
  decide +kernel

theorem contract13110_3 : P.leaf 32 209764 = 788 := by
  exact leaf_contract_factors (k := 32) (b := 16) (H := 209764) (ss := [(29, 7, 468), (8, 7, 486), (20, 4, 580), (5, 4, 586), (10, 1, 866), (16, 0, 867), (7, 0, 858), (11, 0, 458), (12, 0, 458), (17, 0, 465), (23, 1, 817), (13, 1, 923), (14, 1, 1209), (28, 0, 1265), (26, 4, 481), (31, 1, 1665)]) (ids := [0, 1, 2, 4, 7, 13, 16, 17, 19, 20, 23, 28, 30, 31, 22, 25]) (cs := [2, 3, 4, 4, 5, 0, 0, 6, 1, 0, 0, 1, 1, 7, 0, 0, 8, 9, 4, 10, 11, 1, 16, 12, 4, 17, 0, 0, 13, 1, 14, 15]) (bs := [14, 2]) (W := 788) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c13110_3 : P.sumLeaves 26 13424896 64 = 788 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 209764) rows (by decide) (by decide)).symm.trans contract13110_3

theorem contract13110_4 : P.leaf 32 209765 = 3952 := by
  exact leaf_contract_factors (k := 32) (b := 18) (H := 209765) (ss := [(29, 7, 468), (8, 7, 486), (4, 1, 580), (5, 1, 586), (10, 1, 866), (16, 0, 867), (7, 0, 858), (11, 0, 458), (12, 0, 458), (17, 0, 465), (23, 1, 817), (13, 1, 923), (14, 1, 1209), (31, 1, 1665)]) (ids := [0, 1, 4, 7, 13, 16, 17, 18, 19, 20, 23, 24, 26, 28, 30, 31, 22, 25]) (cs := [2, 3, 1, 1, 4, 0, 0, 5, 1, 0, 0, 1, 1, 6, 0, 0, 7, 8, 9, 10, 11, 1, 18, 12, 13, 19, 14, 0, 15, 1, 16, 17]) (bs := [16, 2]) (W := 3952) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c13110_4 : P.sumLeaves 26 13424960 64 = 3952 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 209765) rows (by decide) (by decide)).symm.trans contract13110_4

theorem c13110_5 : P.sumLeaves 26 13425024 576 = 3040 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13110) (lo := 384) (len := 576) (W := 3040) check rows elimOK (by decide) (by decide) cover13110 (by decide)
  decide +kernel

theorem contract13110_6 : P.leaf 32 209775 = 18488 := by
  exact leaf_contract_factors (k := 32) (b := 19) (H := 209775) (ss := [(29, 7, 468), (8, 7, 486), (7, 1, 489), (31, 1, 489), (33, 1, 538), (10, 1, 809), (11, 1, 809), (13, 1, 461), (12, 1, 810), (14, 1, 858), (16, 1, 858), (18, 1, 517), (17, 1, 859)]) (ids := [0, 1, 2, 3, 4, 7, 13, 17, 18, 19, 20, 23, 24, 26, 28, 30, 21, 22, 25]) (cs := [2, 3, 4, 5, 6, 1, 1, 7, 1, 1, 1, 1, 1, 8, 1, 1, 1, 9, 10, 11, 12, 18, 19, 13, 14, 20, 15, 1, 16, 1, 17, 1]) (bs := [16, 3]) (W := 18488) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c13110_6 : P.sumLeaves 26 13425600 64 = 18488 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 209775) rows (by decide) (by decide)).symm.trans contract13110_6

theorem h13110 : P.leaf 36 13110 = 26912 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(64, 396), (64, 248), (128, 0), (64, 788), (64, 3952), (576, 3040), (64, 18488)]) (.cons c13110_0 (.cons c13110_1 (.cons c13110_2 (.cons c13110_3 (.cons c13110_4 (.cons c13110_5 (.cons c13110_6 (.nil)))))))) (by decide) (by decide))

theorem cover13111 : P.CoversSplit 26 10 13111 0xcc00440000000000000000000000000000000000000000000000000000000000440040000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [489, 538, 579, 873, 930, 972, 979, 1265, 1658, 1665]) (ps := [(16, [867], [1265])]) (by decide +kernel)

theorem c13111_0 : P.sumLeaves 26 13425664 1024 = 159128 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13111) (lo := 0) (len := 1024) (W := 159128) check rows elimOK (by decide) (by decide) cover13111 (by decide)
  decide +kernel

theorem h13111 : P.leaf 36 13111 = 159128 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 159128)]) (.cons c13111_0 (.nil)) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(12662, 720), (12663, 720), (12664, 720), (12665, 720), (12666, 720), (12667, 720), (12668, 720), (12669, 720), (12670, 720), (12671, 720), (12768, 180), (12769, 720), (12771, 360), (12773, 360), (12774, 360), (12775, 720), (12783, 180), (12784, 360), (12785, 720), (12787, 360), (12788, 720), (12789, 720), (12790, 720), (12791, 720), (12796, 360), (12797, 720), (12799, 360), (13104, 90), (13105, 360), (13107, 360), (13110, 180), (13111, 360)]

theorem segOK : checkSeg 20 perms 12662 13119 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 12662 13119 17190 71330490 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 71330490)
    (SegSum.cons (w := 720) h12662 (SegSum.cons (w := 720) h12663 (SegSum.cons (w := 720) h12664 (SegSum.cons (w := 720) h12665 (SegSum.cons (w := 720) h12666 (SegSum.cons (w := 720) h12667 (SegSum.cons (w := 720) h12668 (SegSum.cons (w := 720) h12669 (SegSum.cons (w := 720) h12670 (SegSum.cons (w := 720) h12671 (SegSum.cons (w := 180) h12768 (SegSum.cons (w := 720) h12769 (SegSum.cons (w := 360) h12771 (SegSum.cons (w := 360) h12773 (SegSum.cons (w := 360) h12774 (SegSum.cons (w := 720) h12775 (SegSum.cons (w := 180) h12783 (SegSum.cons (w := 360) h12784 (SegSum.cons (w := 720) h12785 (SegSum.cons (w := 360) h12787 (SegSum.cons (w := 720) h12788 (SegSum.cons (w := 720) h12789 (SegSum.cons (w := 720) h12790 (SegSum.cons (w := 720) h12791 (SegSum.cons (w := 360) h12796 (SegSum.cons (w := 720) h12797 (SegSum.cons (w := 360) h12799 (SegSum.cons (w := 90) h13104 (SegSum.cons (w := 360) h13105 (SegSum.cons (w := 360) h13107 (SegSum.cons (w := 180) h13110 (SegSum.cons (w := 360) h13111 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S21
