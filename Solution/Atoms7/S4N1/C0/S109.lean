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

namespace RACert.S4N1.C0.S109

open RACert RACert.Problem

theorem cover32759 : P.CoversSplit 24 10 32759 0xfffffffffafafafafffffffffafafafafffffffffafafafafffffffffafafafaffccffccfac8fac8ffccffccfac8fac8ffccffccfac8fac8ffccffccfac8fac8fffffffffafafafafffffffffafafafafffffffffafafafafffffffffafafafaffccffccfac8fac8ffccffccfac8fac8ffccffccfac8fac8ffccffccfac8fac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [1202, 1210, 1259, 1601]) (by decide +kernel)

noncomputable def f32759 (i : ℕ) := rowWeight keep5 twice5 i * P.leaf 24 (33545216 + i)

theorem c32759_0 : rowSum f32759 0 173 = 73439716 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 32759) (keep := keep5) (twice := twice5) check rows elimOK (by decide) (by decide) cover32759 (by decide)
  decide +kernel

theorem c32759_1 : rowSum f32759 173 216 = 164518721 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 32759) (keep := keep5) (twice := twice5) check rows elimOK (by decide) (by decide) cover32759 (by decide)
  decide +kernel

theorem c32759_2 : rowSum f32759 389 110 = 381346504 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 32759) (keep := keep5) (twice := twice5) check rows elimOK (by decide) (by decide) cover32759 (by decide)
  decide +kernel

theorem c32759_3 : rowSum f32759 499 449 = 436833780 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 32759) (keep := keep5) (twice := twice5) check rows elimOK (by decide) (by decide) cover32759 (by decide)
  decide +kernel

theorem c32759_4 : rowSum f32759 948 76 = 208815024 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 32759) (keep := keep5) (twice := twice5) check rows elimOK (by decide) (by decide) cover32759 (by decide)
  decide +kernel

theorem sum32759 : rowSum f32759 0 1024 = 1264953745 :=
  rowSum_append (F := f32759) (lo := 0) (n := 173) (m := 851) (A := 73439716) (B := 1191514029) c32759_0 (rowSum_append (F := f32759) (lo := 173) (n := 216) (m := 635) (A := 164518721) (B := 1026995308) c32759_1 (rowSum_append (F := f32759) (lo := 389) (n := 110) (m := 525) (A := 381346504) (B := 645648804) c32759_2 (rowSum_append (F := f32759) (lo := 499) (n := 449) (m := 76) (A := 436833780) (B := 208815024) c32759_3 (c32759_4))))

theorem h32759 : P.leaf 34 32759 = 1264953745 :=
  leaf_weighted (k := 24) (d := 10) (H := 32759) (keep := keep5) (twice := twice5) rows (by decide) (by decide) bal5 (invRow5 (H := 32759) (by decide) (by decide +kernel)) sum32759

theorem cover32764 : P.CoversSplit 24 10 32764 0xfffffffffafafafafffffffffafafafafffffffffafafafafffffffffafafafaffccffccfac8fac8ffccffccfac8fac8ffccffccfac8fac8ffccffccfac8fac8fffffffffafafafafffffffffafafafafffffffffafafafafffffffffafafafaffccffccfac8fac8ffccffccfac8fac8ffccffccfac8fac8ffccffccfac8fac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473]) (by decide +kernel)

noncomputable def f32764 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (33550336 + i)

theorem c32764_0 : rowSum f32764 0 173 = 56002274 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 32764) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover32764 (by decide)
  decide +kernel

theorem c32764_1 : rowSum f32764 173 216 = 139656528 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 32764) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover32764 (by decide)
  decide +kernel

theorem c32764_2 : rowSum f32764 389 110 = 279367020 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 32764) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover32764 (by decide)
  decide +kernel

theorem c32764_3 : rowSum f32764 499 449 = 329177451 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 32764) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover32764 (by decide)
  decide +kernel

theorem c32764_4 : rowSum f32764 948 76 = 151354588 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 32764) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover32764 (by decide)
  decide +kernel

theorem sum32764 : rowSum f32764 0 1024 = 955557861 :=
  rowSum_append (F := f32764) (lo := 0) (n := 173) (m := 851) (A := 56002274) (B := 899555587) c32764_0 (rowSum_append (F := f32764) (lo := 173) (n := 216) (m := 635) (A := 139656528) (B := 759899059) c32764_1 (rowSum_append (F := f32764) (lo := 389) (n := 110) (m := 525) (A := 279367020) (B := 480532039) c32764_2 (rowSum_append (F := f32764) (lo := 499) (n := 449) (m := 76) (A := 329177451) (B := 151354588) c32764_3 (c32764_4))))

theorem h32764 : P.leaf 34 32764 = 955557861 :=
  leaf_weighted (k := 24) (d := 10) (H := 32764) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 32764) (by decide) (by decide +kernel)) sum32764

theorem cover32765 : P.CoversSplit 24 10 32765 0xfffffffffafafafafffffffffafafafafffffffffafafafafffffffffafafafaffccffccfac8fac8ffccffccfac8fac8ffccffccfac8fac8ffccffccfac8fac8fffffffffafafafafffffffffafafafafffffffffafafafafffffffffafafafaffccffccfac8fac8ffccffccfac8fac8ffccffccfac8fac8ffccffccfac8fac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 1202, 1210, 1259, 1601]) (by decide +kernel)

noncomputable def f32765 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 24 (33551360 + i)

theorem c32765_0 : rowSum f32765 0 257 = 155718898 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 32765) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover32765 (by decide)
  decide +kernel

theorem c32765_1 : rowSum f32765 257 180 = 205131162 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 32765) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover32765 (by decide)
  decide +kernel

theorem c32765_2 : rowSum f32765 437 230 = 307670268 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 32765) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover32765 (by decide)
  decide +kernel

theorem c32765_3 : rowSum f32765 667 208 = 389881042 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 32765) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover32765 (by decide)
  decide +kernel

theorem c32765_4 : rowSum f32765 875 149 = 506403819 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 32765) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover32765 (by decide)
  decide +kernel

theorem sum32765 : rowSum f32765 0 1024 = 1564805189 :=
  rowSum_append (F := f32765) (lo := 0) (n := 257) (m := 767) (A := 155718898) (B := 1409086291) c32765_0 (rowSum_append (F := f32765) (lo := 257) (n := 180) (m := 587) (A := 205131162) (B := 1203955129) c32765_1 (rowSum_append (F := f32765) (lo := 437) (n := 230) (m := 357) (A := 307670268) (B := 896284861) c32765_2 (rowSum_append (F := f32765) (lo := 667) (n := 208) (m := 149) (A := 389881042) (B := 506403819) c32765_3 (c32765_4))))

theorem h32765 : P.leaf 34 32765 = 1564805189 :=
  leaf_weighted (k := 24) (d := 10) (H := 32765) (keep := keep2) (twice := twice2) rows (by decide) (by decide) bal2 (invRow2 (H := 32765) (by decide) (by decide +kernel)) sum32765

theorem cover32767 : P.CoversSplit 24 10 32767 0xfffffffffafafafafffffffffafafafafffffffffafafafafffffffffafafafaffccffccfac8fac8ffccffccfac8fac8ffccffccfac8fac8ffccffccfac8fac8fffffffffafafafafffffffffafafafafffffffffafafafafffffffffafafafaffccffccfac8fac8ffccffccfac8fac8ffccffccfac8fac8ffccffccfac8fac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [1202, 1210, 1259, 1601]) (by decide +kernel)

noncomputable def f32767 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (33553408 + i)

theorem c32767_0 : rowSum f32767 0 173 = 256174771 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 32767) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover32767 (by decide)
  decide +kernel

theorem c32767_1 : rowSum f32767 173 216 = 428553642 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 32767) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover32767 (by decide)
  decide +kernel

theorem c32767_2 : rowSum f32767 389 110 = 626104116 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 32767) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover32767 (by decide)
  decide +kernel

theorem c32767_3 : rowSum f32767 499 449 = 797984488 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 32767) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover32767 (by decide)
  decide +kernel

theorem c32767_4 : rowSum f32767 948 76 = 271548088 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 32767) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover32767 (by decide)
  decide +kernel

theorem sum32767 : rowSum f32767 0 1024 = 2380365105 :=
  rowSum_append (F := f32767) (lo := 0) (n := 173) (m := 851) (A := 256174771) (B := 2124190334) c32767_0 (rowSum_append (F := f32767) (lo := 173) (n := 216) (m := 635) (A := 428553642) (B := 1695636692) c32767_1 (rowSum_append (F := f32767) (lo := 389) (n := 110) (m := 525) (A := 626104116) (B := 1069532576) c32767_2 (rowSum_append (F := f32767) (lo := 499) (n := 449) (m := 76) (A := 797984488) (B := 271548088) c32767_3 (c32767_4))))

theorem h32767 : P.leaf 34 32767 = 2380365105 :=
  leaf_weighted (k := 24) (d := 10) (H := 32767) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 32767) (by decide) (by decide +kernel)) sum32767

def seg : List (ℕ × ℕ) := [(32759, 12), (32764, 12), (32765, 24), (32767, 12)]

theorem segOK : checkSeg 16 perms 32759 65004 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 32759 65004 60 92765845068 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 92765845068)
    (SegSum.cons (w := 12) h32759 (SegSum.cons (w := 12) h32764 (SegSum.cons (w := 24) h32765 (SegSum.cons (w := 12) h32767 (show SegSum (P.leaf 34) [] 0 from rfl))))) (by decide)

end RACert.S4N1.C0.S109
