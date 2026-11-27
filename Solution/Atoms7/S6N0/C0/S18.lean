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

namespace RACert.S6N0.C0.S18

open RACert RACert.Problem

theorem cover11752 : P.CoversSplit 26 10 11752 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c11752_0 : P.sumLeaves 26 12034048 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 11752) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover11752 (by decide)
  decide +kernel

theorem h11752 : P.leaf 36 11752 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c11752_0 (.nil)) (by decide) (by decide))

theorem cover11753 : P.CoversSplit 26 10 11753 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c11753_0 : P.sumLeaves 26 12035072 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 11753) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover11753 (by decide)
  decide +kernel

theorem h11753 : P.leaf 36 11753 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c11753_0 (.nil)) (by decide) (by decide))

theorem cover11755 : P.CoversSplit 26 10 11755 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c11755_0 : P.sumLeaves 26 12037120 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 11755) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover11755 (by decide)
  decide +kernel

theorem h11755 : P.leaf 36 11755 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c11755_0 (.nil)) (by decide) (by decide))

theorem cover11756 : P.CoversSplit 26 10 11756 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c11756_0 : P.sumLeaves 26 12038144 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 11756) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover11756 (by decide)
  decide +kernel

theorem h11756 : P.leaf 36 11756 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c11756_0 (.nil)) (by decide) (by decide))

theorem cover11757 : P.CoversSplit 26 10 11757 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c11757_0 : P.sumLeaves 26 12039168 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 11757) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover11757 (by decide)
  decide +kernel

theorem h11757 : P.leaf 36 11757 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c11757_0 (.nil)) (by decide) (by decide))

theorem cover11759 : P.CoversSplit 26 10 11759 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c11759_0 : P.sumLeaves 26 12041216 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 11759) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover11759 (by decide)
  decide +kernel

theorem h11759 : P.leaf 36 11759 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c11759_0 (.nil)) (by decide) (by decide))

theorem cover11760 : P.CoversSplit 26 10 11760 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [482]) (by decide +kernel)

theorem c11760_0 : P.sumLeaves 26 12042240 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 11760) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover11760 (by decide)
  decide +kernel

theorem h11760 : P.leaf 36 11760 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c11760_0 (.nil)) (by decide) (by decide))

theorem cover11761 : P.CoversSplit 26 10 11761 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [482]) (by decide +kernel)

theorem c11761_0 : P.sumLeaves 26 12043264 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 11761) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover11761 (by decide)
  decide +kernel

theorem h11761 : P.leaf 36 11761 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c11761_0 (.nil)) (by decide) (by decide))

theorem cover11763 : P.CoversSplit 26 10 11763 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [482]) (by decide +kernel)

theorem c11763_0 : P.sumLeaves 26 12045312 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 11763) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover11763 (by decide)
  decide +kernel

theorem h11763 : P.leaf 36 11763 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c11763_0 (.nil)) (by decide) (by decide))

theorem cover11764 : P.CoversSplit 26 10 11764 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c11764_0 : P.sumLeaves 26 12046336 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 11764) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover11764 (by decide)
  decide +kernel

theorem h11764 : P.leaf 36 11764 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c11764_0 (.nil)) (by decide) (by decide))

theorem cover11765 : P.CoversSplit 26 10 11765 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c11765_0 : P.sumLeaves 26 12047360 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 11765) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover11765 (by decide)
  decide +kernel

theorem h11765 : P.leaf 36 11765 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c11765_0 (.nil)) (by decide) (by decide))

theorem cover11767 : P.CoversSplit 26 10 11767 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c11767_0 : P.sumLeaves 26 12049408 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 11767) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover11767 (by decide)
  decide +kernel

theorem h11767 : P.leaf 36 11767 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c11767_0 (.nil)) (by decide) (by decide))

theorem cover11768 : P.CoversSplit 26 10 11768 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c11768_0 : P.sumLeaves 26 12050432 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 11768) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover11768 (by decide)
  decide +kernel

theorem h11768 : P.leaf 36 11768 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c11768_0 (.nil)) (by decide) (by decide))

theorem cover11769 : P.CoversSplit 26 10 11769 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c11769_0 : P.sumLeaves 26 12051456 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 11769) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover11769 (by decide)
  decide +kernel

theorem h11769 : P.leaf 36 11769 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c11769_0 (.nil)) (by decide) (by decide))

theorem cover11771 : P.CoversSplit 26 10 11771 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c11771_0 : P.sumLeaves 26 12053504 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 11771) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover11771 (by decide)
  decide +kernel

theorem h11771 : P.leaf 36 11771 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c11771_0 (.nil)) (by decide) (by decide))

theorem cover11772 : P.CoversSplit 26 10 11772 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c11772_0 : P.sumLeaves 26 12054528 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 11772) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover11772 (by decide)
  decide +kernel

theorem h11772 : P.leaf 36 11772 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c11772_0 (.nil)) (by decide) (by decide))

theorem cover11773 : P.CoversSplit 26 10 11773 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c11773_0 : P.sumLeaves 26 12055552 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 11773) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover11773 (by decide)
  decide +kernel

theorem h11773 : P.leaf 36 11773 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c11773_0 (.nil)) (by decide) (by decide))

theorem cover11775 : P.CoversSplit 26 10 11775 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c11775_0 : P.sumLeaves 26 12057600 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 11775) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover11775 (by decide)
  decide +kernel

theorem h11775 : P.leaf 36 11775 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c11775_0 (.nil)) (by decide) (by decide))

theorem cover12112 : P.CoversSplit 26 10 12112 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c12112_0 : P.sumLeaves 26 12402688 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12112) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12112 (by decide)
  decide +kernel

theorem h12112 : P.leaf 36 12112 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12112_0 (.nil)) (by decide) (by decide))

theorem cover12113 : P.CoversSplit 26 10 12113 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c12113_0 : P.sumLeaves 26 12403712 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12113) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12113 (by decide)
  decide +kernel

theorem h12113 : P.leaf 36 12113 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12113_0 (.nil)) (by decide) (by decide))

theorem cover12115 : P.CoversSplit 26 10 12115 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c12115_0 : P.sumLeaves 26 12405760 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12115) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12115 (by decide)
  decide +kernel

theorem h12115 : P.leaf 36 12115 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12115_0 (.nil)) (by decide) (by decide))

theorem cover12116 : P.CoversSplit 26 10 12116 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c12116_0 : P.sumLeaves 26 12406784 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12116) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12116 (by decide)
  decide +kernel

theorem h12116 : P.leaf 36 12116 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12116_0 (.nil)) (by decide) (by decide))

theorem cover12117 : P.CoversSplit 26 10 12117 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c12117_0 : P.sumLeaves 26 12407808 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12117) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12117 (by decide)
  decide +kernel

theorem h12117 : P.leaf 36 12117 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12117_0 (.nil)) (by decide) (by decide))

theorem cover12119 : P.CoversSplit 26 10 12119 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c12119_0 : P.sumLeaves 26 12409856 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12119) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12119 (by decide)
  decide +kernel

theorem h12119 : P.leaf 36 12119 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12119_0 (.nil)) (by decide) (by decide))

theorem cover12120 : P.CoversSplit 26 10 12120 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c12120_0 : P.sumLeaves 26 12410880 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12120) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12120 (by decide)
  decide +kernel

theorem h12120 : P.leaf 36 12120 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12120_0 (.nil)) (by decide) (by decide))

theorem cover12121 : P.CoversSplit 26 10 12121 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c12121_0 : P.sumLeaves 26 12411904 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12121) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12121 (by decide)
  decide +kernel

theorem h12121 : P.leaf 36 12121 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12121_0 (.nil)) (by decide) (by decide))

theorem cover12123 : P.CoversSplit 26 10 12123 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c12123_0 : P.sumLeaves 26 12413952 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12123) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12123 (by decide)
  decide +kernel

theorem h12123 : P.leaf 36 12123 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12123_0 (.nil)) (by decide) (by decide))

theorem cover12124 : P.CoversSplit 26 10 12124 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c12124_0 : P.sumLeaves 26 12414976 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12124) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12124 (by decide)
  decide +kernel

theorem h12124 : P.leaf 36 12124 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12124_0 (.nil)) (by decide) (by decide))

theorem cover12125 : P.CoversSplit 26 10 12125 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c12125_0 : P.sumLeaves 26 12416000 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12125) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12125 (by decide)
  decide +kernel

theorem h12125 : P.leaf 36 12125 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12125_0 (.nil)) (by decide) (by decide))

theorem cover12127 : P.CoversSplit 26 10 12127 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c12127_0 : P.sumLeaves 26 12418048 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12127) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12127 (by decide)
  decide +kernel

theorem h12127 : P.leaf 36 12127 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12127_0 (.nil)) (by decide) (by decide))

theorem cover12144 : P.CoversSplit 26 10 12144 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c12144_0 : P.sumLeaves 26 12435456 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12144) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12144 (by decide)
  decide +kernel

theorem h12144 : P.leaf 36 12144 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12144_0 (.nil)) (by decide) (by decide))

theorem cover12145 : P.CoversSplit 26 10 12145 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c12145_0 : P.sumLeaves 26 12436480 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12145) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12145 (by decide)
  decide +kernel

theorem h12145 : P.leaf 36 12145 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12145_0 (.nil)) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(11752, 360), (11753, 720), (11755, 360), (11756, 360), (11757, 720), (11759, 360), (11760, 360), (11761, 720), (11763, 360), (11764, 360), (11765, 720), (11767, 360), (11768, 360), (11769, 720), (11771, 360), (11772, 360), (11773, 720), (11775, 360), (12112, 360), (12113, 720), (12115, 360), (12116, 360), (12117, 720), (12119, 360), (12120, 360), (12121, 720), (12123, 360), (12124, 360), (12125, 720), (12127, 360), (12144, 360), (12145, 360)]

theorem segOK : checkSeg 20 perms 11752 12146 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 11752 12146 15120 0 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 0)
    (SegSum.cons (w := 360) h11752 (SegSum.cons (w := 720) h11753 (SegSum.cons (w := 360) h11755 (SegSum.cons (w := 360) h11756 (SegSum.cons (w := 720) h11757 (SegSum.cons (w := 360) h11759 (SegSum.cons (w := 360) h11760 (SegSum.cons (w := 720) h11761 (SegSum.cons (w := 360) h11763 (SegSum.cons (w := 360) h11764 (SegSum.cons (w := 720) h11765 (SegSum.cons (w := 360) h11767 (SegSum.cons (w := 360) h11768 (SegSum.cons (w := 720) h11769 (SegSum.cons (w := 360) h11771 (SegSum.cons (w := 360) h11772 (SegSum.cons (w := 720) h11773 (SegSum.cons (w := 360) h11775 (SegSum.cons (w := 360) h12112 (SegSum.cons (w := 720) h12113 (SegSum.cons (w := 360) h12115 (SegSum.cons (w := 360) h12116 (SegSum.cons (w := 720) h12117 (SegSum.cons (w := 360) h12119 (SegSum.cons (w := 360) h12120 (SegSum.cons (w := 720) h12121 (SegSum.cons (w := 360) h12123 (SegSum.cons (w := 360) h12124 (SegSum.cons (w := 720) h12125 (SegSum.cons (w := 360) h12127 (SegSum.cons (w := 360) h12144 (SegSum.cons (w := 360) h12145 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S18
