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

namespace RACert.S6N0.C0.S71

open RACert RACert.Problem

theorem cover290302 : P.CoversSplit 26 10 290302 0xff00ff00ff00ff00000000000000000000000000000000000000000000000000050005000500050000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [482, 629, 636, 881, 972, 979, 1265, 1273, 1658, 1665]) (by decide +kernel)

theorem c290302_0 : P.sumLeaves 26 297269248 1024 = 121537332 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 290302) (lo := 0) (len := 1024) (W := 121537332) check rows elimOK (by decide) (by decide) cover290302 (by decide)
  decide +kernel

theorem h290302 : P.leaf 36 290302 = 121537332 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 121537332)]) (.cons c290302_0 (.nil)) (by decide) (by decide))

theorem h120702 : P.leaf 36 120702 = 121537332 :=
  orient6 (v := 290302) (by decide) (by decide +kernel) h290302

theorem cover290303 : P.CoversSplit 26 10 290303 0xff00ff00ff00ff00000000000000000000000000000000000000000000000000050005000500050000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [629, 636, 972, 979, 1265, 1273, 1658, 1665]) (by decide +kernel)

theorem c290303_0 : P.sumLeaves 26 297270272 1024 = 201275848 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 290303) (lo := 0) (len := 1024) (W := 201275848) check rows elimOK (by decide) (by decide) cover290303 (by decide)
  decide +kernel

theorem h290303 : P.leaf 36 290303 = 201275848 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 201275848)]) (.cons c290303_0 (.nil)) (by decide) (by decide))

theorem h120703 : P.leaf 36 120703 = 201275848 :=
  orient6 (v := 290303) (by decide) (by decide +kernel) h290303

theorem cover604542 : P.CoversSplit 26 10 604542 0xaa00aa0000000000aa00ab0000000000aa00aa0000000002aa00ab0000000002000000000000000000000a0000000000000000000000000000000a000000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [579, 629, 636, 874, 930, 972, 979, 1273, 1315, 1322]) (by decide +kernel)

noncomputable def f604542 (i : ℕ) := rowWeight keep3 twice3 i * P.leaf 26 (619051008 + i)

theorem c604542_0 : rowSum f604542 0 1024 = 145533843 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 604542) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover604542 (by decide)
  decide +kernel

theorem sum604542 : rowSum f604542 0 1024 = 145533843 :=
  c604542_0

theorem h604542 : P.leaf 36 604542 = 145533843 :=
  leaf_weighted (k := 26) (d := 10) (H := 604542) (keep := keep3) (twice := twice3) rows (by decide) (by decide) (bal3) (invRow3 (H := 604542) (by decide) (by decide +kernel)) sum604542

theorem h120803 : P.leaf 36 120803 = 145533843 :=
  orient86 (v := 604542) (by decide) (by decide +kernel) h604542

theorem cover605022 : P.CoversSplit 26 10 605022 0xfffffffafffffafafffffffafffffafafffffffafffcfa00fffffffafffcfa00fffffafafffffafaffffaaaaffffaaaafffffafafffcfa00ffffaaaafffcaa00fffffffafffffafafffffffafffffafaffccffc8cc00c800ffccffc8cc00c8000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 880, 930, 972, 979, 1273, 1315, 1322]) (by decide +kernel)

theorem c605022_0 : P.sumLeaves 26 619542528 426 = 51902552 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 605022) (lo := 0) (len := 426) (W := 51902552) check rows elimOK (by decide) (by decide) cover605022 (by decide)
  decide +kernel

theorem c605022_1 : P.sumLeaves 26 619542954 116 = 93982970 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 605022) (lo := 426) (len := 116) (W := 93982970) check rows elimOK (by decide) (by decide) cover605022 (by decide)
  decide +kernel

theorem c605022_2 : P.sumLeaves 26 619543070 128 = 69416801 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 605022) (lo := 542) (len := 128) (W := 69416801) check rows elimOK (by decide) (by decide) cover605022 (by decide)
  decide +kernel

theorem c605022_3 : P.sumLeaves 26 619543198 124 = 108207540 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 605022) (lo := 670) (len := 124) (W := 108207540) check rows elimOK (by decide) (by decide) cover605022 (by decide)
  decide +kernel

theorem c605022_4 : P.sumLeaves 26 619543322 116 = 85966851 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 605022) (lo := 794) (len := 116) (W := 85966851) check rows elimOK (by decide) (by decide) cover605022 (by decide)
  decide +kernel

theorem c605022_5 : P.sumLeaves 26 619543438 104 = 128605218 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 605022) (lo := 910) (len := 104) (W := 128605218) check rows elimOK (by decide) (by decide) cover605022 (by decide)
  decide +kernel

theorem c605022_6 : P.sumLeaves 26 619543542 10 = 43895634 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 605022) (lo := 1014) (len := 10) (W := 43895634) check rows elimOK (by decide) (by decide) cover605022 (by decide)
  decide +kernel

theorem h605022 : P.leaf 36 605022 = 581977566 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(426, 51902552), (116, 93982970), (128, 69416801), (124, 108207540), (116, 85966851), (104, 128605218), (10, 43895634)]) (.cons c605022_0 (.cons c605022_1 (.cons c605022_2 (.cons c605022_3 (.cons c605022_4 (.cons c605022_5 (.cons c605022_6 (.nil)))))))) (by decide) (by decide))

theorem h120805 : P.leaf 36 120805 = 581977566 :=
  orient86 (v := 605022) (by decide) (by decide +kernel) h605022

theorem cover605054 : P.CoversSplit 26 10 605054 0xfffffffafffffafafffffffafffffafafffffffafffcfac8fffffffafffcfac8fffffafafffffafafffffafafffffafafffffafafffcfac8fffffafafffcfac8fffffffafffffafafffffffafffffafaffccffc8ccccc8c8ffccffc8ccccc8c80000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [579, 874, 930, 972, 979, 1273, 1315, 1322]) (by decide +kernel)

noncomputable def f605054 (i : ℕ) := rowWeight keep3 twice3 i * P.leaf 26 (619575296 + i)

theorem c605054_0 : rowSum f605054 0 468 = 204150237 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 605054) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover605054 (by decide)
  decide +kernel

theorem c605054_1 : rowSum f605054 468 186 = 287994256 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 605054) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover605054 (by decide)
  decide +kernel

theorem c605054_2 : rowSum f605054 654 190 = 309924915 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 605054) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover605054 (by decide)
  decide +kernel

theorem c605054_3 : rowSum f605054 844 176 = 521525458 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 605054) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover605054 (by decide)
  decide +kernel

theorem c605054_4 : rowSum f605054 1020 4 = 47221688 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 605054) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover605054 (by decide)
  decide +kernel

theorem sum605054 : rowSum f605054 0 1024 = 1370816554 :=
  rowSum_append (F := f605054) (lo := 0) (n := 468) (m := 556) (A := 204150237) (B := 1166666317) c605054_0 (rowSum_append (F := f605054) (lo := 468) (n := 186) (m := 370) (A := 287994256) (B := 878672061) c605054_1 (rowSum_append (F := f605054) (lo := 654) (n := 190) (m := 180) (A := 309924915) (B := 568747146) c605054_2 (rowSum_append (F := f605054) (lo := 844) (n := 176) (m := 4) (A := 521525458) (B := 47221688) c605054_3 (c605054_4))))

theorem h605054 : P.leaf 36 605054 = 1370816554 :=
  leaf_weighted (k := 26) (d := 10) (H := 605054) (keep := keep3) (twice := twice3) rows (by decide) (by decide) (bal3) (invRow3 (H := 605054) (by decide) (by decide +kernel)) sum605054

theorem h120807 : P.leaf 36 120807 = 1370816554 :=
  orient86 (v := 605054) (by decide) (by decide +kernel) h605054

theorem cover604670 : P.CoversSplit 26 10 604670 0xff00ff0000000000ff00fe0000000000ff00ff0000000002ff00fe0000000002ff00fa0000000000ff00fa0000000000ff00fa0000000002ff00fa000000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [629, 636, 874, 930, 972, 979, 1273, 1315, 1322]) (by decide +kernel)

noncomputable def f604670 (i : ℕ) := rowWeight keep3 twice3 i * P.leaf 26 (619182080 + i)

theorem c604670_0 : rowSum f604670 0 1024 = 459688168 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 604670) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover604670 (by decide)
  decide +kernel

theorem sum604670 : rowSum f604670 0 1024 = 459688168 :=
  c604670_0

theorem h604670 : P.leaf 36 604670 = 459688168 :=
  leaf_weighted (k := 26) (d := 10) (H := 604670) (keep := keep3) (twice := twice3) rows (by decide) (by decide) (bal3) (invRow3 (H := 604670) (by decide) (by decide +kernel)) sum604670

theorem h120811 : P.leaf 36 120811 = 459688168 :=
  orient86 (v := 604670) (by decide) (by decide +kernel) h604670

theorem cover321011 : P.CoversSplit 26 10 321011 0xffffff00f0f0f00fffffea00f0f0e00affffff00e0c0e00cfac8ea00e0c0e008ffffff00f0f0f00ffafaaa00f0f0a00affffff00e0c0e00cfac8aa00e0c0a008ffffff00f0f0f00fffffea00f0f0e00affccff00c0c0c00cfac8ea00c0c0c008ffffff00f0f0f00ffafaaa00f0f0a00affccff00c0c0c00cfac8aa00c0c08008 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 629, 636, 958, 1658, 1665]) (by decide +kernel)

noncomputable def f321011 (i : ℕ) := rowWeight keep18 twice18 i * P.leaf 26 (328715264 + i)

theorem c321011_0 : rowSum f321011 0 366 = 72133568 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 321011) (keep := keep18) (twice := twice18) check rows elimOK (by decide) (by decide) cover321011 (by decide)
  decide +kernel

theorem c321011_1 : rowSum f321011 366 433 = 226865668 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 321011) (keep := keep18) (twice := twice18) check rows elimOK (by decide) (by decide) cover321011 (by decide)
  decide +kernel

theorem c321011_2 : rowSum f321011 799 225 = 186437042 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 321011) (keep := keep18) (twice := twice18) check rows elimOK (by decide) (by decide) cover321011 (by decide)
  decide +kernel

theorem sum321011 : rowSum f321011 0 1024 = 485436278 :=
  rowSum_append (F := f321011) (lo := 0) (n := 366) (m := 658) (A := 72133568) (B := 413302710) c321011_0 (rowSum_append (F := f321011) (lo := 366) (n := 433) (m := 225) (A := 226865668) (B := 186437042) c321011_1 (c321011_2))

theorem h321011 : P.leaf 36 321011 = 485436278 :=
  leaf_weighted (k := 26) (d := 10) (H := 321011) (keep := keep18) (twice := twice18) rows (by decide) (by decide) (bal18) (invRow18 (H := 321011) (by decide) (by decide +kernel)) sum321011

theorem h120812 : P.leaf 36 120812 = 485436278 :=
  orient80 (v := 321011) (by decide) (by decide +kernel) h321011

def seg : List (ℕ × ℕ) := [(120702, 720), (120703, 720), (120803, 360), (120805, 720), (120807, 360), (120811, 360), (120812, 180)]

theorem segOK : checkSeg 20 perms 120702 120813 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 120702 120813 3420 1450201750560 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 1450201750560)
    (SegSum.cons (w := 720) h120702 (SegSum.cons (w := 720) h120703 (SegSum.cons (w := 360) h120803 (SegSum.cons (w := 720) h120805 (SegSum.cons (w := 360) h120807 (SegSum.cons (w := 360) h120811 (SegSum.cons (w := 180) h120812 (show SegSum (P.leaf 36) [] 0 from rfl)))))))) (by decide)

end RACert.S6N0.C0.S71
