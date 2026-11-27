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

namespace RACert.S6N0.C0.S38

open RACert RACert.Problem

theorem cover32767 : P.CoversSplit 26 10 32767 0xfffffffffffffac8fffffafafffffac8ffffffffffccfac8fac8fac8fac8fac8fffffafafffffac8fafafafafafafac8fffffafaffccfac8fac8fac8fac8fac8ffffffffffccfac8fffffafaffccfac8ffccffccffccfac8fac8fac8fac8fac8fffffafaffccfac8fafafafafac8fac8ffccfac8ffccfac8fac8fac8fac8fac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [972, 979, 1265, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f32767 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 26 (33553408 + i)

theorem c32767_0 : rowSum f32767 0 268 = 61414139 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 32767) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover32767 (by decide)
  decide +kernel

theorem c32767_1 : rowSum f32767 268 147 = 1170850732 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 32767) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover32767 (by decide)
  decide +kernel

theorem c32767_2 : rowSum f32767 415 384 = 1444041416 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 32767) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover32767 (by decide)
  decide +kernel

theorem c32767_3 : rowSum f32767 799 225 = 2084896320 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 32767) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover32767 (by decide)
  decide +kernel

theorem sum32767 : rowSum f32767 0 1024 = 4761202607 :=
  rowSum_append (F := f32767) (lo := 0) (n := 268) (m := 756) (A := 61414139) (B := 4699788468) c32767_0 (rowSum_append (F := f32767) (lo := 268) (n := 147) (m := 609) (A := 1170850732) (B := 3528937736) c32767_1 (rowSum_append (F := f32767) (lo := 415) (n := 384) (m := 225) (A := 1444041416) (B := 2084896320) c32767_2 (c32767_3)))

theorem h32767 : P.leaf 36 32767 = 4761202607 :=
  leaf_weighted (k := 26) (d := 10) (H := 32767) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 32767) (by decide) (by decide +kernel)) sum32767

theorem cover65520 : P.CoversSplit 26 10 65520 0xfac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489]) (by decide +kernel)

noncomputable def f65520 (i : ℕ) := rowWeight keep9 twice9 i * P.leaf 26 (67092480 + i)

theorem c65520_0 : rowSum f65520 0 303 = 4311076 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 65520) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover65520 (by decide)
  decide +kernel

theorem c65520_1 : rowSum f65520 303 319 = 5119568 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 65520) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover65520 (by decide)
  decide +kernel

theorem c65520_2 : rowSum f65520 622 335 = 5630128 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 65520) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover65520 (by decide)
  decide +kernel

theorem c65520_3 : rowSum f65520 957 67 = 549376 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 65520) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover65520 (by decide)
  decide +kernel

theorem sum65520 : rowSum f65520 0 1024 = 15610148 :=
  rowSum_append (F := f65520) (lo := 0) (n := 303) (m := 721) (A := 4311076) (B := 11299072) c65520_0 (rowSum_append (F := f65520) (lo := 303) (n := 319) (m := 402) (A := 5119568) (B := 6179504) c65520_1 (rowSum_append (F := f65520) (lo := 622) (n := 335) (m := 67) (A := 5630128) (B := 549376) c65520_2 (c65520_3)))

theorem h65520 : P.leaf 36 65520 = 15610148 :=
  leaf_weighted (k := 26) (d := 10) (H := 65520) (keep := keep9) (twice := twice9) rows (by decide) (by decide) bal9 (invRow9 (H := 65520) (by decide) (by decide +kernel)) sum65520

theorem cover65521 : P.CoversSplit 26 10 65521 0xfffffafaffccfac8fffffafaffccfac8fffffafaffccfac8fac8fac8fac8fac8fffffafaffccfac8fafafafafac8fac8fffffafaffccfac8fac8fac8fac8fac8fffffafaffccfac8fffffafaffccfac8ffccfac8ffccfac8fac8fac8fac8fac8fffffafaffccfac8fafafafafac8fac8ffccfac8ffccfac8fac8fac8fac8fac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 1658, 1665]) (by decide +kernel)

noncomputable def f65521 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 26 (67093504 + i)

theorem c65521_0 : rowSum f65521 0 268 = 23993406 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 65521) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover65521 (by decide)
  decide +kernel

theorem c65521_1 : rowSum f65521 268 152 = 170823072 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 65521) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover65521 (by decide)
  decide +kernel

theorem c65521_2 : rowSum f65521 420 415 = 339096772 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 65521) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover65521 (by decide)
  decide +kernel

theorem c65521_3 : rowSum f65521 835 189 = 307586160 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 65521) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover65521 (by decide)
  decide +kernel

theorem sum65521 : rowSum f65521 0 1024 = 841499410 :=
  rowSum_append (F := f65521) (lo := 0) (n := 268) (m := 756) (A := 23993406) (B := 817506004) c65521_0 (rowSum_append (F := f65521) (lo := 268) (n := 152) (m := 604) (A := 170823072) (B := 646682932) c65521_1 (rowSum_append (F := f65521) (lo := 420) (n := 415) (m := 189) (A := 339096772) (B := 307586160) c65521_2 (c65521_3)))

theorem h65521 : P.leaf 36 65521 = 841499410 :=
  leaf_weighted (k := 26) (d := 10) (H := 65521) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 65521) (by decide) (by decide +kernel)) sum65521

theorem cover65523 : P.CoversSplit 26 10 65523 0xfffffffffffffac8fffffafafffffac8ffffffffffccfac8fac8fac8fac8fac8fffffafafffffac8fafafafafafafac8fffffafaffccfac8fac8fac8fac8fac8ffffffffffccfac8fffffafaffccfac8ffccffccffccfac8fac8fac8fac8fac8fffffafaffccfac8fafafafafac8fac8ffccfac8ffccfac8fac8fac8fac8fac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f65523 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 26 (67095552 + i)

theorem c65523_0 : rowSum f65523 0 268 = 115229408 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 65523) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover65523 (by decide)
  decide +kernel

theorem c65523_1 : rowSum f65523 268 147 = 397846896 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 65523) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover65523 (by decide)
  decide +kernel

theorem c65523_2 : rowSum f65523 415 384 = 620085264 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 65523) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover65523 (by decide)
  decide +kernel

theorem c65523_3 : rowSum f65523 799 225 = 682561384 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 65523) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover65523 (by decide)
  decide +kernel

theorem sum65523 : rowSum f65523 0 1024 = 1815722952 :=
  rowSum_append (F := f65523) (lo := 0) (n := 268) (m := 756) (A := 115229408) (B := 1700493544) c65523_0 (rowSum_append (F := f65523) (lo := 268) (n := 147) (m := 609) (A := 397846896) (B := 1302646648) c65523_1 (rowSum_append (F := f65523) (lo := 415) (n := 384) (m := 225) (A := 620085264) (B := 682561384) c65523_2 (c65523_3)))

theorem h65523 : P.leaf 36 65523 = 1815722952 :=
  leaf_weighted (k := 26) (d := 10) (H := 65523) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 65523) (by decide) (by decide +kernel)) sum65523

def seg : List (ℕ × ℕ) := [(32767, 180), (65520, 15), (65521, 60), (65523, 90)]

theorem segOK : checkSeg 20 perms 32767 65527 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 32767 65527 345 1071155651760 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 1071155651760)
    (SegSum.cons (w := 180) h32767 (SegSum.cons (w := 15) h65520 (SegSum.cons (w := 60) h65521 (SegSum.cons (w := 90) h65523 (show SegSum (P.leaf 36) [] 0 from rfl))))) (by decide)

end RACert.S6N0.C0.S38
