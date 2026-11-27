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

namespace RACert.S6N0.C0.S67

open RACert RACert.Problem

theorem cover90111 : P.CoversSplit 26 10 90111 0xfffffffffffcfaf8fffffffafffcfaf8fffffffffffcfac8fafafafac8c8c8c8fffffafafffcfaf8fafafafafaf8faf8fffffafafffcfac8fafafafac8c8c8c8ffffffffffccfac8fffffffaffccfac8ffffffffccccc8c8fafafafac8c8c8c8fffffafaffccfac8fafafafafac8fac8fffffafaccccc8c8fafafafac8c8c8c8 :=
  coversSplit check rows (by decide) (by decide) (xs := [922, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f90111 (i : ℕ) := rowWeight keep4 twice4 i * P.leaf 26 (92273664 + i)

theorem c90111_0 : rowSum f90111 0 271 = 58991475 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 90111) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover90111 (by decide)
  decide +kernel

theorem c90111_1 : rowSum f90111 271 143 = 1011367986 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 90111) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover90111 (by decide)
  decide +kernel

theorem c90111_2 : rowSum f90111 414 390 = 1428350124 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 90111) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover90111 (by decide)
  decide +kernel

theorem c90111_3 : rowSum f90111 804 219 = 2101215598 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 90111) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover90111 (by decide)
  decide +kernel

theorem c90111_4 : rowSum f90111 1023 1 = 20228520 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 90111) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover90111 (by decide)
  decide +kernel

theorem sum90111 : rowSum f90111 0 1024 = 4620153703 :=
  rowSum_append (F := f90111) (lo := 0) (n := 271) (m := 753) (A := 58991475) (B := 4561162228) c90111_0 (rowSum_append (F := f90111) (lo := 271) (n := 143) (m := 610) (A := 1011367986) (B := 3549794242) c90111_1 (rowSum_append (F := f90111) (lo := 414) (n := 390) (m := 220) (A := 1428350124) (B := 2121444118) c90111_2 (rowSum_append (F := f90111) (lo := 804) (n := 219) (m := 1) (A := 2101215598) (B := 20228520) c90111_3 (c90111_4))))

theorem h90111 : P.leaf 36 90111 = 4620153703 :=
  leaf_weighted (k := 26) (d := 10) (H := 90111) (keep := keep4) (twice := twice4) rows (by decide) (by decide) bal4 (invRow4 (H := 90111) (by decide) (by decide +kernel)) sum90111

theorem cover96741 : P.CoversSplit 26 10 96741 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 482, 489, 629, 636, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c96741_0 : P.sumLeaves 26 99062784 1024 = 1235616 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 96741) (lo := 0) (len := 1024) (W := 1235616) check rows elimOK (by decide) (by decide) cover96741 (by decide)
  decide +kernel

theorem h96741 : P.leaf 36 96741 = 1235616 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1235616)]) (.cons c96741_0 (.nil)) (by decide) (by decide))

theorem cover96743 : P.CoversSplit 26 10 96743 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 482, 489, 629, 636, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c96743_0 : P.sumLeaves 26 99064832 1024 = 1717468 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 96743) (lo := 0) (len := 1024) (W := 1717468) check rows elimOK (by decide) (by decide) cover96743 (by decide)
  decide +kernel

theorem h96743 : P.leaf 36 96743 = 1717468 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1717468)]) (.cons c96743_0 (.nil)) (by decide) (by decide))

theorem cover96745 : P.CoversSplit 26 10 96745 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 481, 482, 629, 636, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c96745_0 : P.sumLeaves 26 99066880 1024 = 1399204 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 96745) (lo := 0) (len := 1024) (W := 1399204) check rows elimOK (by decide) (by decide) cover96745 (by decide)
  decide +kernel

theorem h96745 : P.leaf 36 96745 = 1399204 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1399204)]) (.cons c96745_0 (.nil)) (by decide) (by decide))

theorem cover96747 : P.CoversSplit 26 10 96747 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 481, 482, 629, 636, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c96747_0 : P.sumLeaves 26 99068928 1024 = 1710352 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 96747) (lo := 0) (len := 1024) (W := 1710352) check rows elimOK (by decide) (by decide) cover96747 (by decide)
  decide +kernel

theorem h96747 : P.leaf 36 96747 = 1710352 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1710352)]) (.cons c96747_0 (.nil)) (by decide) (by decide))

theorem cover96749 : P.CoversSplit 26 10 96749 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 972, 979, 1266, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c96749_0 : P.sumLeaves 26 99070976 1024 = 1794144 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 96749) (lo := 0) (len := 1024) (W := 1794144) check rows elimOK (by decide) (by decide) cover96749 (by decide)
  decide +kernel

theorem h96749 : P.leaf 36 96749 = 1794144 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1794144)]) (.cons c96749_0 (.nil)) (by decide) (by decide))

theorem cover96751 : P.CoversSplit 26 10 96751 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 972, 979, 1266, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c96751_0 : P.sumLeaves 26 99073024 1024 = 2107682 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 96751) (lo := 0) (len := 1024) (W := 2107682) check rows elimOK (by decide) (by decide) cover96751 (by decide)
  decide +kernel

theorem h96751 : P.leaf 36 96751 = 2107682 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 2107682)]) (.cons c96751_0 (.nil)) (by decide) (by decide))

theorem cover96757 : P.CoversSplit 26 10 96757 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 482, 489, 629, 636, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c96757_0 : P.sumLeaves 26 99079168 1024 = 6546270 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 96757) (lo := 0) (len := 1024) (W := 6546270) check rows elimOK (by decide) (by decide) cover96757 (by decide)
  decide +kernel

theorem h96757 : P.leaf 36 96757 = 6546270 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 6546270)]) (.cons c96757_0 (.nil)) (by decide) (by decide))

theorem cover96759 : P.CoversSplit 26 10 96759 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 482, 489, 629, 636, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c96759_0 : P.sumLeaves 26 99081216 1024 = 8200480 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 96759) (lo := 0) (len := 1024) (W := 8200480) check rows elimOK (by decide) (by decide) cover96759 (by decide)
  decide +kernel

theorem h96759 : P.leaf 36 96759 = 8200480 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 8200480)]) (.cons c96759_0 (.nil)) (by decide) (by decide))

theorem cover96761 : P.CoversSplit 26 10 96761 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 481, 482, 629, 636, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c96761_0 : P.sumLeaves 26 99083264 1024 = 5301592 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 96761) (lo := 0) (len := 1024) (W := 5301592) check rows elimOK (by decide) (by decide) cover96761 (by decide)
  decide +kernel

theorem h96761 : P.leaf 36 96761 = 5301592 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 5301592)]) (.cons c96761_0 (.nil)) (by decide) (by decide))

theorem cover96763 : P.CoversSplit 26 10 96763 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 481, 482, 629, 636, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c96763_0 : P.sumLeaves 26 99085312 1024 = 6937056 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 96763) (lo := 0) (len := 1024) (W := 6937056) check rows elimOK (by decide) (by decide) cover96763 (by decide)
  decide +kernel

theorem h96763 : P.leaf 36 96763 = 6937056 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 6937056)]) (.cons c96763_0 (.nil)) (by decide) (by decide))

theorem cover96764 : P.CoversSplit 26 10 96764 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 972, 979, 1266, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c96764_0 : P.sumLeaves 26 99086336 1024 = 10978546 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 96764) (lo := 0) (len := 1024) (W := 10978546) check rows elimOK (by decide) (by decide) cover96764 (by decide)
  decide +kernel

theorem h96764 : P.leaf 36 96764 = 10978546 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 10978546)]) (.cons c96764_0 (.nil)) (by decide) (by decide))

theorem cover96765 : P.CoversSplit 26 10 96765 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 972, 979, 1266, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c96765_0 : P.sumLeaves 26 99087360 1024 = 11423406 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 96765) (lo := 0) (len := 1024) (W := 11423406) check rows elimOK (by decide) (by decide) cover96765 (by decide)
  decide +kernel

theorem h96765 : P.leaf 36 96765 = 11423406 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 11423406)]) (.cons c96765_0 (.nil)) (by decide) (by decide))

theorem cover96767 : P.CoversSplit 26 10 96767 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 972, 979, 1266, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c96767_0 : P.sumLeaves 26 99089408 1024 = 12935986 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 96767) (lo := 0) (len := 1024) (W := 12935986) check rows elimOK (by decide) (by decide) cover96767 (by decide)
  decide +kernel

theorem h96767 : P.leaf 36 96767 = 12935986 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 12935986)]) (.cons c96767_0 (.nil)) (by decide) (by decide))

theorem cover96979 : P.CoversSplit 26 10 96979 0xc0000000c0000000c0000000c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 587, 972, 979, 1315, 1322]) (by decide +kernel)

theorem c96979_0 : P.sumLeaves 26 99306496 1024 = 9987208 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 96979) (lo := 0) (len := 1024) (W := 9987208) check rows elimOK (by decide) (by decide) cover96979 (by decide)
  decide +kernel

theorem h96979 : P.leaf 36 96979 = 9987208 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 9987208)]) (.cons c96979_0 (.nil)) (by decide) (by decide))

theorem cover96982 : P.CoversSplit 26 10 96982 0xcc000000cc000400cc000000cc00040000000000000000000000000000000000040004000400040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 587, 874, 972, 979, 1315, 1658]) (by decide +kernel)

theorem c96982_0 : P.sumLeaves 26 99309568 1024 = 26401458 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 96982) (lo := 0) (len := 1024) (W := 26401458) check rows elimOK (by decide) (by decide) cover96982 (by decide)
  decide +kernel

theorem h96982 : P.leaf 36 96982 = 26401458 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 26401458)]) (.cons c96982_0 (.nil)) (by decide) (by decide))

theorem cover96983 : P.CoversSplit 26 10 96983 0xcc000000cc000400cc000000cc00040000000000000000000000000000000000040004000400040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 587, 972, 979, 1315, 1658]) (by decide +kernel)

theorem c96983_0 : P.sumLeaves 26 99310592 1024 = 58337348 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 96983) (lo := 0) (len := 1024) (W := 58337348) check rows elimOK (by decide) (by decide) cover96983 (by decide)
  decide +kernel

theorem h96983 : P.leaf 36 96983 = 58337348 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 58337348)]) (.cons c96983_0 (.nil)) (by decide) (by decide))

theorem cover96985 : P.CoversSplit 26 10 96985 0xf0f00000f0f00000f0f00000f0f0000500000000000000000000000000300000000000000000000000000000000000000000000000000000000000000000000000000000003000000000000000300001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 587, 923, 972, 979, 1315, 1665]) (by decide +kernel)

theorem c96985_0 : P.sumLeaves 26 99312640 1024 = 14193792 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 96985) (lo := 0) (len := 1024) (W := 14193792) check rows elimOK (by decide) (by decide) cover96985 (by decide)
  decide +kernel

theorem h96985 : P.leaf 36 96985 = 14193792 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 14193792)]) (.cons c96985_0 (.nil)) (by decide) (by decide))

theorem cover96986 : P.CoversSplit 26 10 96986 0xf0f00000f0f00000f0f00000f0f0000500000000000000000000000000300000000000000000000000000000000000000000000000000000000000000000000000000000003000000000000000300001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 587, 874, 972, 979, 1273, 1315, 1665]) (by decide +kernel)

theorem c96986_0 : P.sumLeaves 26 99313664 1024 = 30506700 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 96986) (lo := 0) (len := 1024) (W := 30506700) check rows elimOK (by decide) (by decide) cover96986 (by decide)
  decide +kernel

theorem h96986 : P.leaf 36 96986 = 30506700 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 30506700)]) (.cons c96986_0 (.nil)) (by decide) (by decide))

theorem cover96987 : P.CoversSplit 26 10 96987 0xf0f00000f0f00000f0f00000f0f0000500000000000000000000000000300000000000000000000000000000000000000000000000000000000000000000000000000000003000000000000000300001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 587, 972, 979, 1273, 1315, 1665]) (by decide +kernel)

theorem c96987_0 : P.sumLeaves 26 99314688 1024 = 66319708 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 96987) (lo := 0) (len := 1024) (W := 66319708) check rows elimOK (by decide) (by decide) cover96987 (by decide)
  decide +kernel

theorem h96987 : P.leaf 36 96987 = 66319708 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 66319708)]) (.cons c96987_0 (.nil)) (by decide) (by decide))

theorem cover96990 : P.CoversSplit 26 10 96990 0xffff0000ffff0505ffff0000ffff050000000000000000000000000000300000050505050505050500000000000000000000000000000000000000000000000000000000003300010000000000330000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 587, 874, 972, 979, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c96990_0 : P.sumLeaves 26 99317760 1023 = 122072284 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 96990) (lo := 0) (len := 1023) (W := 122072284) check rows elimOK (by decide) (by decide) cover96990 (by decide)
  decide +kernel

theorem c96990_1 : P.sumLeaves 26 99318783 1 = 3944448 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 96990) (lo := 1023) (len := 1) (W := 3944448) check rows elimOK (by decide) (by decide) cover96990 (by decide)
  decide +kernel

theorem h96990 : P.leaf 36 96990 = 126016732 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1023, 122072284), (1, 3944448)]) (.cons c96990_0 (.cons c96990_1 (.nil))) (by decide) (by decide))

theorem cover96991 : P.CoversSplit 26 10 96991 0xffff0000ffff0505ffff0000ffff050000000000000000000000000000300000050505050505050500000000000000000000000000000000000000000000000000000000003300010000000000330000000000000000000000000000000000000000000000010001000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 587, 972, 979, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c96991_0 : P.sumLeaves 26 99318784 1021 = 252065230 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 96991) (lo := 0) (len := 1021) (W := 252065230) check rows elimOK (by decide) (by decide) cover96991 (by decide)
  decide +kernel

theorem c96991_1 : P.sumLeaves 26 99319805 3 = 15955012 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 96991) (lo := 1021) (len := 3) (W := 15955012) check rows elimOK (by decide) (by decide) cover96991 (by decide)
  decide +kernel

theorem h96991 : P.leaf 36 96991 = 268020242 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1021, 252065230), (3, 15955012)]) (.cons c96991_0 (.cons c96991_1 (.nil))) (by decide) (by decide))

theorem cover97010 : P.CoversSplit 26 10 97010 0xc000c000c000c000c000c000c000c0000000000000000000000000000000000000000000000000000000c0000000c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 587, 874, 972, 979, 1658, 1665]) (by decide +kernel)

theorem c97010_0 : P.sumLeaves 26 99338240 1024 = 4934022 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97010) (lo := 0) (len := 1024) (W := 4934022) check rows elimOK (by decide) (by decide) cover97010 (by decide)
  decide +kernel

theorem h97010 : P.leaf 36 97010 = 4934022 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 4934022)]) (.cons c97010_0 (.nil)) (by decide) (by decide))

theorem cover97011 : P.CoversSplit 26 10 97011 0xc000c000c000c000c000c000c000c0000000000000000000000000000000000000000000000000000000c0000000c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 587, 972, 979, 1658, 1665]) (by decide +kernel)

theorem c97011_0 : P.sumLeaves 26 99339264 1024 = 27724310 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97011) (lo := 0) (len := 1024) (W := 27724310) check rows elimOK (by decide) (by decide) cover97011 (by decide)
  decide +kernel

theorem h97011 : P.leaf 36 97011 = 27724310 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 27724310)]) (.cons c97011_0 (.nil)) (by decide) (by decide))

theorem cover97013 : P.CoversSplit 26 10 97013 0xcc00cc00cc00c800cc00cc00cc00c80000000000000000000000000000000000cc00c800cc00c800c000c000c000c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 587, 923, 972, 979, 1273, 1315, 1658]) (by decide +kernel)

theorem c97013_0 : P.sumLeaves 26 99341312 1024 = 20508396 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97013) (lo := 0) (len := 1024) (W := 20508396) check rows elimOK (by decide) (by decide) cover97013 (by decide)
  decide +kernel

theorem h97013 : P.leaf 36 97013 = 20508396 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 20508396)]) (.cons c97013_0 (.nil)) (by decide) (by decide))

theorem cover97014 : P.CoversSplit 26 10 97014 0xcc00cc00cc00c800cc00cc00cc00c80000000000000000000000000000000000cc00c800cc00c800c000c000c000c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 587, 874, 972, 979, 1315, 1658]) (by decide +kernel)

theorem c97014_0 : P.sumLeaves 26 99342336 1024 = 59565504 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97014) (lo := 0) (len := 1024) (W := 59565504) check rows elimOK (by decide) (by decide) cover97014 (by decide)
  decide +kernel

theorem h97014 : P.leaf 36 97014 = 59565504 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 59565504)]) (.cons c97014_0 (.nil)) (by decide) (by decide))

theorem cover97015 : P.CoversSplit 26 10 97015 0xcc00cc00cc00c800cc00cc00cc00c80000000000000000000000000000000000cc00c800cc00c800c000c000c000c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 587, 972, 979, 1315, 1658]) (by decide +kernel)

theorem c97015_0 : P.sumLeaves 26 99343360 1024 = 117788882 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97015) (lo := 0) (len := 1024) (W := 117788882) check rows elimOK (by decide) (by decide) cover97015 (by decide)
  decide +kernel

theorem h97015 : P.leaf 36 97015 = 117788882 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 117788882)]) (.cons c97015_0 (.nil)) (by decide) (by decide))

theorem cover97016 : P.CoversSplit 26 10 97016 0xf0f0f0f0f0f0f0f0f0f0f0f5f0f0f0f000000000000000000000000000300000000000000000000000005050000050500000000000000000000000000000000000000000003000300000000000300030000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 587, 874, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c97016_0 : P.sumLeaves 26 99344384 384 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97016) (lo := 0) (len := 384) (W := 0) check rows elimOK (by decide) (by decide) cover97016 (by decide)
  decide +kernel

theorem contract97016_1 : P.leaf 32 1552262 = 22000 := by
  exact leaf_contract_factors (k := 32) (b := 19) (H := 1552262) (ss := [(2, 1, 466), (20, 0, 1665), (9, 1, 1609), (19, 1, 1259), (21, 1, 573), (11, 1, 915), (4, 1, 410), (7, 1, 460), (12, 1, 460), (29, 0, 1665), (31, 0, 1665), (27, 1, 489), (33, 0, 1665)]) (ids := [1, 3, 4, 6, 8, 11, 12, 13, 14, 15, 16, 20, 22, 24, 26, 28, 30, 21, 23]) (cs := [1, 2, 1, 3, 4, 1, 5, 1, 6, 1, 1, 7, 8, 9, 10, 11, 12, 1, 0, 1, 13, 19, 14, 20, 15, 1, 16, 0, 17, 0, 18, 0]) (bs := [17, 2]) (W := 22000) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c97016_1 : P.sumLeaves 26 99344768 64 = 22000 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1552262) rows (by decide) (by decide)).symm.trans contract97016_1

theorem contract97016_2 : P.leaf 32 1552263 = 26976 := by
  exact leaf_contract_factors (k := 32) (b := 18) (H := 1552263) (ss := [(2, 1, 466), (30, 1, 972), (20, 0, 1665), (9, 1, 1609), (19, 1, 1259), (21, 1, 573), (29, 0, 1665), (31, 0, 1665), (27, 1, 489), (33, 0, 1665), (11, 1, 879), (4, 1, 410), (7, 1, 460), (12, 1, 460)]) (ids := [1, 3, 4, 6, 8, 11, 12, 13, 14, 15, 16, 20, 22, 26, 30, 21, 23, 24]) (cs := [1, 2, 1, 3, 4, 1, 5, 1, 6, 1, 1, 7, 8, 9, 10, 11, 12, 1, 0, 1, 13, 17, 14, 18, 19, 1, 15, 0, 1, 0, 16, 0]) (bs := [15, 3]) (W := 26976) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c97016_2 : P.sumLeaves 26 99344832 64 = 26976 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1552263) rows (by decide) (by decide)).symm.trans contract97016_2

theorem c97016_3 : P.sumLeaves 26 99344896 512 = 4908318 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97016) (lo := 512) (len := 512) (W := 4908318) check rows elimOK (by decide) (by decide) cover97016 (by decide)
  decide +kernel

theorem h97016 : P.leaf 36 97016 = 4957294 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(384, 0), (64, 22000), (64, 26976), (512, 4908318)]) (.cons c97016_0 (.cons c97016_1 (.cons c97016_2 (.cons c97016_3 (.nil))))) (by decide) (by decide))

theorem cover97017 : P.CoversSplit 26 10 97017 0xf0f0f0f0f0f0f0f0f0f0f0f5f0f0f0f000000000000000000000000000300000000000000000000000005050000050500000000000000000000000000000000000000000003000300000000000300030000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 587, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c97017_0 : P.sumLeaves 26 99345408 448 = 168410 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97017) (lo := 0) (len := 448) (W := 168410) check rows elimOK (by decide) (by decide) cover97017 (by decide)
  decide +kernel

theorem contract97017_1 : P.leaf 32 1552279 = 231224 := by
  exact leaf_contract_factors (k := 32) (b := 21) (H := 1552279) (ss := [(2, 1, 482), (30, 1, 972), (20, 0, 1665), (9, 1, 1609), (19, 1, 1259), (21, 1, 573), (29, 0, 1665), (31, 0, 1665), (33, 0, 1665), (27, 1, 489), (11, 1, 879)]) (ids := [1, 2, 3, 4, 5, 6, 8, 10, 11, 12, 13, 14, 15, 16, 20, 21, 22, 26, 23, 24, 30]) (cs := [1, 2, 3, 4, 5, 6, 7, 1, 8, 1, 9, 10, 11, 12, 13, 14, 15, 1, 0, 1, 16, 17, 18, 20, 21, 1, 19, 0, 1, 0, 22, 0]) (bs := [18, 3]) (W := 231224) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c97017_1 : P.sumLeaves 26 99345856 64 = 231224 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1552279) rows (by decide) (by decide)).symm.trans contract97017_1

theorem c97017_2 : P.sumLeaves 26 99345920 512 = 43497944 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97017) (lo := 512) (len := 512) (W := 43497944) check rows elimOK (by decide) (by decide) cover97017 (by decide)
  decide +kernel

theorem h97017 : P.leaf 36 97017 = 43897578 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(448, 168410), (64, 231224), (512, 43497944)]) (.cons c97017_0 (.cons c97017_1 (.cons c97017_2 (.nil)))) (by decide) (by decide))

theorem cover97018 : P.CoversSplit 26 10 97018 0xf0f0f0f0f0f0f0f0f0f0f0f5f0f0f0f000000000000000000000000000300000000000000000000000005050000050500000000000000000000000000000000000000000003000300000000000300030000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 587, 874, 972, 979, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c97018_0 : P.sumLeaves 26 99346432 1024 = 100717536 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97018) (lo := 0) (len := 1024) (W := 100717536) check rows elimOK (by decide) (by decide) cover97018 (by decide)
  decide +kernel

theorem h97018 : P.leaf 36 97018 = 100717536 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 100717536)]) (.cons c97018_0 (.nil)) (by decide) (by decide))

theorem cover97019 : P.CoversSplit 26 10 97019 0xf0f0f0f0f0f0f0f0f0f0f0f5f0f0f0f000000000000000000000000000300000000000000000000000005050000050500000000000000000000000000000000000000000003000300000000000300030000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 587, 972, 979, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c97019_0 : P.sumLeaves 26 99347456 1024 = 212234684 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97019) (lo := 0) (len := 1024) (W := 212234684) check rows elimOK (by decide) (by decide) cover97019 (by decide)
  decide +kernel

theorem h97019 : P.leaf 36 97019 = 212234684 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 212234684)]) (.cons c97019_0 (.nil)) (by decide) (by decide))

theorem cover97020 : P.CoversSplit 26 10 97020 0xfffffffffffffafafffffffafffffafa00000000000000000000000000300000fffffafafffffafaf0f0f0f0f0f0f0f00000000000000000000000000030000000000000003300320000000000330032000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [587, 874, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c97020_0 : P.sumLeaves 26 99348480 760 = 13384552 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97020) (lo := 0) (len := 760) (W := 13384552) check rows elimOK (by decide) (by decide) cover97020 (by decide)
  decide +kernel

theorem c97020_1 : P.sumLeaves 26 99349240 232 = 34739890 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97020) (lo := 760) (len := 232) (W := 34739890) check rows elimOK (by decide) (by decide) cover97020 (by decide)
  decide +kernel

theorem c97020_2 : P.sumLeaves 26 99349472 32 = 27017016 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97020) (lo := 992) (len := 32) (W := 27017016) check rows elimOK (by decide) (by decide) cover97020 (by decide)
  decide +kernel

theorem h97020 : P.leaf 36 97020 = 75141458 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(760, 13384552), (232, 34739890), (32, 27017016)]) (.cons c97020_0 (.cons c97020_1 (.cons c97020_2 (.nil)))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(90111, 360), (96741, 360), (96743, 180), (96745, 360), (96747, 180), (96749, 360), (96751, 180), (96757, 360), (96759, 360), (96761, 360), (96763, 360), (96764, 360), (96765, 720), (96767, 360), (96979, 720), (96982, 360), (96983, 360), (96985, 360), (96986, 720), (96987, 720), (96990, 360), (96991, 360), (97010, 720), (97011, 720), (97013, 720), (97014, 720), (97015, 720), (97016, 720), (97017, 720), (97018, 720), (97019, 720), (97020, 720)]

theorem segOK : checkSeg 20 perms 90111 97021 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 90111 97021 16020 2427347985120 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 2427347985120)
    (SegSum.cons (w := 360) h90111 (SegSum.cons (w := 360) h96741 (SegSum.cons (w := 180) h96743 (SegSum.cons (w := 360) h96745 (SegSum.cons (w := 180) h96747 (SegSum.cons (w := 360) h96749 (SegSum.cons (w := 180) h96751 (SegSum.cons (w := 360) h96757 (SegSum.cons (w := 360) h96759 (SegSum.cons (w := 360) h96761 (SegSum.cons (w := 360) h96763 (SegSum.cons (w := 360) h96764 (SegSum.cons (w := 720) h96765 (SegSum.cons (w := 360) h96767 (SegSum.cons (w := 720) h96979 (SegSum.cons (w := 360) h96982 (SegSum.cons (w := 360) h96983 (SegSum.cons (w := 360) h96985 (SegSum.cons (w := 720) h96986 (SegSum.cons (w := 720) h96987 (SegSum.cons (w := 360) h96990 (SegSum.cons (w := 360) h96991 (SegSum.cons (w := 720) h97010 (SegSum.cons (w := 720) h97011 (SegSum.cons (w := 720) h97013 (SegSum.cons (w := 720) h97014 (SegSum.cons (w := 720) h97015 (SegSum.cons (w := 720) h97016 (SegSum.cons (w := 720) h97017 (SegSum.cons (w := 720) h97018 (SegSum.cons (w := 720) h97019 (SegSum.cons (w := 720) h97020 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S67
