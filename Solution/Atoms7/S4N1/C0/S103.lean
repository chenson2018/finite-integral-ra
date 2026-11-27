/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Atoms7.S4N1.C0.Actions

/-! Generated identity-class certificate for the product-row count. -/

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option Elab.async false

@[expose] public section

namespace RACert.S4N1.C0.S103

open RACert RACert.Problem

theorem cover28603 : P.CoversSplit 24 10 28603 0xfffffffffafaf0f0fffffffffafaf0f0fffffffffafaf0f0fffffffffafaf0f0ffccffccfac8f0c0ccccccccc8c8c0c0ffccffccfac8f0c0ccccccccc8c8c0c0fffffffffafaf0f0fffffffffafaf0f0fffffffffafaf0f0fffffffffafaf0f0ffccffccfac8f0c0ccccccccc8c8c0c0ffccffcc80008000cccccccc80008000 :=
  coversProjected check rows (by decide) (by decide) (xs := [517, 915, 1202, 1259, 1601]) (ps := [(8, [1217, 1609], [1272]), (14, [1217, 1609], [1272])]) (by decide +kernel)

noncomputable def f28603 (i : ℕ) := rowWeight keep5 twice5 i * P.leaf 24 (29289472 + i)

theorem c28603_0 : rowSum f28603 0 242 = 55454676 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 28603) (keep := keep5) (twice := twice5) check rows elimOK (by decide) (by decide) cover28603 (by decide)
  decide +kernel

theorem c28603_1 : rowSum f28603 242 202 = 141699113 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 28603) (keep := keep5) (twice := twice5) check rows elimOK (by decide) (by decide) cover28603 (by decide)
  decide +kernel

theorem c28603_2 : rowSum f28603 444 305 = 268227353 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 28603) (keep := keep5) (twice := twice5) check rows elimOK (by decide) (by decide) cover28603 (by decide)
  decide +kernel

theorem c28603_3 : rowSum f28603 749 275 = 249344858 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 28603) (keep := keep5) (twice := twice5) check rows elimOK (by decide) (by decide) cover28603 (by decide)
  decide +kernel

theorem sum28603 : rowSum f28603 0 1024 = 714726000 :=
  rowSum_append (F := f28603) (lo := 0) (n := 242) (m := 782) (A := 55454676) (B := 659271324) c28603_0 (rowSum_append (F := f28603) (lo := 242) (n := 202) (m := 580) (A := 141699113) (B := 517572211) c28603_1 (rowSum_append (F := f28603) (lo := 444) (n := 305) (m := 275) (A := 268227353) (B := 249344858) c28603_2 (c28603_3)))

theorem h28603 : P.leaf 34 28603 = 714726000 :=
  leaf_weighted (k := 24) (d := 10) (H := 28603) (keep := keep5) (twice := twice5) rows (by decide) (by decide) bal5 (invRow5 (H := 28603) (by decide) (by decide +kernel)) sum28603

theorem cover28604 : P.CoversSplit 24 10 28604 0xffaaffaafaaaf0a0ffaaffaafaaaf0a0ffaaffaafaaaf0a0ffaaffaafaaaf0a0ff88ff88fa88f080cc88cc88c888c080ff88ff88fa88f080cc88cc88c888c080ffaaffaafaaaf0a0ffaaffaafaaaf0a0ffaaffaafaaaf0a0ffaaffaafaaaf0a0ff88ff88fa88f080cc88cc88c888c080ff88ff8880008000cc88cc8880008000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 472, 473, 1202, 1601]) (ps := [(8, [1217, 1609], [1272]), (14, [1217, 1609], [1272])]) (by decide +kernel)

noncomputable def f28604 (i : ℕ) := rowWeight keep5 twice5 i * P.leaf 24 (29290496 + i)

theorem c28604_0 : rowSum f28604 0 307 = 15465124 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 28604) (keep := keep5) (twice := twice5) check rows elimOK (by decide) (by decide) cover28604 (by decide)
  decide +kernel

theorem c28604_1 : rowSum f28604 307 203 = 106598752 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 28604) (keep := keep5) (twice := twice5) check rows elimOK (by decide) (by decide) cover28604 (by decide)
  decide +kernel

theorem c28604_2 : rowSum f28604 510 514 = 151110682 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 28604) (keep := keep5) (twice := twice5) check rows elimOK (by decide) (by decide) cover28604 (by decide)
  decide +kernel

theorem sum28604 : rowSum f28604 0 1024 = 273174558 :=
  rowSum_append (F := f28604) (lo := 0) (n := 307) (m := 717) (A := 15465124) (B := 257709434) c28604_0 (rowSum_append (F := f28604) (lo := 307) (n := 203) (m := 514) (A := 106598752) (B := 151110682) c28604_1 (c28604_2))

theorem h28604 : P.leaf 34 28604 = 273174558 :=
  leaf_weighted (k := 24) (d := 10) (H := 28604) (keep := keep5) (twice := twice5) rows (by decide) (by decide) bal5 (invRow5 (H := 28604) (by decide) (by decide +kernel)) sum28604

theorem cover28605 : P.CoversSplit 24 10 28605 0xfffffffffafaf0f0fffffffffafaf0f0fffffffffafaf0f0fffffffffafaf0f0ffccffccfac8f0c0ccccccccc8c8c0c0ffccffccfac8f0c0ccccccccc8c8c0c0fffffffffafaf0f0fffffffffafaf0f0fffffffffafaf0f0fffffffffafaf0f0ffccffccfac8f0c0ccccccccc8c8c0c0ffccffcc80008000cccccccc80008000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 517, 1202, 1259, 1601]) (ps := [(8, [1217, 1609], [1272]), (14, [1217, 1609], [1272])]) (by decide +kernel)

theorem c28605_0 : P.sumLeaves 24 29291520 239 = 18664397 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28605) (lo := 0) (len := 239) (W := 18664397) check rows elimOK (by decide) (by decide) cover28605 (by decide)
  decide +kernel

theorem c28605_1 : P.sumLeaves 24 29291759 124 = 26260032 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28605) (lo := 239) (len := 124) (W := 26260032) check rows elimOK (by decide) (by decide) cover28605 (by decide)
  decide +kernel

theorem c28605_2 : P.sumLeaves 24 29291883 120 = 75154858 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28605) (lo := 363) (len := 120) (W := 75154858) check rows elimOK (by decide) (by decide) cover28605 (by decide)
  decide +kernel

theorem c28605_3 : P.sumLeaves 24 29292003 171 = 81974008 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28605) (lo := 483) (len := 171) (W := 81974008) check rows elimOK (by decide) (by decide) cover28605 (by decide)
  decide +kernel

theorem c28605_4 : P.sumLeaves 24 29292174 159 = 90643285 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28605) (lo := 654) (len := 159) (W := 90643285) check rows elimOK (by decide) (by decide) cover28605 (by decide)
  decide +kernel

theorem c28605_5 : P.sumLeaves 24 29292333 120 = 114811519 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28605) (lo := 813) (len := 120) (W := 114811519) check rows elimOK (by decide) (by decide) cover28605 (by decide)
  decide +kernel

theorem c28605_6 : P.sumLeaves 24 29292453 91 = 186731001 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28605) (lo := 933) (len := 91) (W := 186731001) check rows elimOK (by decide) (by decide) cover28605 (by decide)
  decide +kernel

theorem h28605 : P.leaf 34 28605 = 594239100 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(239, 18664397), (124, 26260032), (120, 75154858), (171, 81974008), (159, 90643285), (120, 114811519), (91, 186731001)]) (.cons c28605_0 (.cons c28605_1 (.cons c28605_2 (.cons c28605_3 (.cons c28605_4 (.cons c28605_5 (.cons c28605_6 (.nil)))))))) (by decide) (by decide))

theorem cover28607 : P.CoversSplit 24 10 28607 0xfffffffffafaf0f0fffffffffafaf0f0fffffffffafaf0f0fffffffffafaf0f0ffccffccfac8f0c0ccccccccc8c8c0c0ffccffccfac8f0c0ccccccccc8c8c0c0fffffffffafaf0f0fffffffffafaf0f0fffffffffafaf0f0fffffffffafaf0f0ffccffccfac8f0c0ccccccccc8c8c0c0ffccffcc80008000cccccccc80008000 :=
  coversProjected check rows (by decide) (by decide) (xs := [517, 915, 1202, 1259, 1601]) (ps := [(8, [1217, 1609], [1272]), (14, [1217, 1609], [1272])]) (by decide +kernel)

noncomputable def f28607 (i : ℕ) := rowWeight keep5 twice5 i * P.leaf 24 (29293568 + i)

theorem c28607_0 : rowSum f28607 0 242 = 100167988 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 28607) (keep := keep5) (twice := twice5) check rows elimOK (by decide) (by decide) cover28607 (by decide)
  decide +kernel

theorem c28607_1 : rowSum f28607 242 202 = 221665232 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 28607) (keep := keep5) (twice := twice5) check rows elimOK (by decide) (by decide) cover28607 (by decide)
  decide +kernel

theorem c28607_2 : rowSum f28607 444 305 = 366812963 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 28607) (keep := keep5) (twice := twice5) check rows elimOK (by decide) (by decide) cover28607 (by decide)
  decide +kernel

theorem c28607_3 : rowSum f28607 749 275 = 334526070 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 28607) (keep := keep5) (twice := twice5) check rows elimOK (by decide) (by decide) cover28607 (by decide)
  decide +kernel

theorem sum28607 : rowSum f28607 0 1024 = 1023172253 :=
  rowSum_append (F := f28607) (lo := 0) (n := 242) (m := 782) (A := 100167988) (B := 923004265) c28607_0 (rowSum_append (F := f28607) (lo := 242) (n := 202) (m := 580) (A := 221665232) (B := 701339033) c28607_1 (rowSum_append (F := f28607) (lo := 444) (n := 305) (m := 275) (A := 366812963) (B := 334526070) c28607_2 (c28607_3)))

theorem h28607 : P.leaf 34 28607 = 1023172253 :=
  leaf_weighted (k := 24) (d := 10) (H := 28607) (keep := keep5) (twice := twice5) rows (by decide) (by decide) bal5 (invRow5 (H := 28607) (by decide) (by decide +kernel)) sum28607

def seg : List (ℕ × ℕ) := [(28603, 6), (28604, 24), (28605, 48), (28607, 24)]

theorem segOK : checkSeg 16 perms 28603 28652 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 28603 28652 102 63924156264 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 63924156264)
    (SegSum.cons (w := 6) h28603 (SegSum.cons (w := 24) h28604 (SegSum.cons (w := 48) h28605 (SegSum.cons (w := 24) h28607 (show SegSum (P.leaf 34) [] 0 from rfl))))) (by decide)

end RACert.S4N1.C0.S103
