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

namespace RACert.S4N1.C0.S90

open RACert RACert.Problem

theorem cover57279 : P.CoversSplit 24 10 57279 0xfffffffffffff0f0fffffffffffff0f0fffffffffffff0f0fffffffffffff0f0fffffffffffff0f0ccccccccccccc0c0fffffffffffff0f0ccccccccccccc0c0fffffffffffff0f0fffffffffffff0f0fffffffffafaf0f0fffffffffafaf0f0fffffffffffff0f0ccccccccccccc0c0ffccffcc00000000cccccccc00000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [517, 916, 1202, 1217, 1308, 1601, 1609]) (by decide +kernel)

noncomputable def f57279 (i : ℕ) := rowWeight keep4 twice4 i * P.leaf 24 (58653696 + i)

theorem c57279_0 : rowSum f57279 0 228 = 110359214 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 57279) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover57279 (by decide)
  decide +kernel

theorem c57279_1 : rowSum f57279 228 196 = 236198984 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 57279) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover57279 (by decide)
  decide +kernel

theorem c57279_2 : rowSum f57279 424 259 = 402135693 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 57279) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover57279 (by decide)
  decide +kernel

theorem c57279_3 : rowSum f57279 683 341 = 516259854 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 57279) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover57279 (by decide)
  decide +kernel

theorem sum57279 : rowSum f57279 0 1024 = 1264953745 :=
  rowSum_append (F := f57279) (lo := 0) (n := 228) (m := 796) (A := 110359214) (B := 1154594531) c57279_0 (rowSum_append (F := f57279) (lo := 228) (n := 196) (m := 600) (A := 236198984) (B := 918395547) c57279_1 (rowSum_append (F := f57279) (lo := 424) (n := 259) (m := 341) (A := 402135693) (B := 516259854) c57279_2 (c57279_3)))

theorem h57279 : P.leaf 34 57279 = 1264953745 :=
  leaf_weighted (k := 24) (d := 10) (H := 57279) (keep := keep4) (twice := twice4) rows (by decide) (by decide) (bal4) (invRow4 (H := 57279) (by decide) (by decide +kernel)) sum57279

theorem h32759 : P.leaf 34 32759 = 1264953745 :=
  orient4 (v := 57279) (by decide) (by decide +kernel) h57279

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
  leaf_weighted (k := 24) (d := 10) (H := 32764) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 32764) (by decide) (by decide +kernel)) sum32764

theorem cover65015 : P.CoversSplit 24 10 65015 0xfffffffffffafafafffffffffffafafafffffffffffafafafffffffffffafafafffcfffcfff8faf8ffccffccffc8fac8fffcfffcfff8faf8ffccffccffc8fac8fffffffffffafafafffffffffffafafafffffffffafafafafffffffffafafafafffcfffcfff8faf8ffccffccffc8fac8ffccffccfac8fac8ffccffccfac8fac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [858, 865, 1217, 1609]) (by decide +kernel)

noncomputable def f65015 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (66575360 + i)

theorem c65015_0 : rowSum f65015 0 171 = 112566804 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 65015) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover65015 (by decide)
  decide +kernel

theorem c65015_1 : rowSum f65015 171 198 = 309183413 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 65015) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover65015 (by decide)
  decide +kernel

theorem c65015_2 : rowSum f65015 369 114 = 372698786 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 65015) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover65015 (by decide)
  decide +kernel

theorem c65015_3 : rowSum f65015 483 275 = 466448900 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 65015) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover65015 (by decide)
  decide +kernel

theorem c65015_4 : rowSum f65015 758 266 = 303907286 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 65015) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover65015 (by decide)
  decide +kernel

theorem sum65015 : rowSum f65015 0 1024 = 1564805189 :=
  rowSum_append (F := f65015) (lo := 0) (n := 171) (m := 853) (A := 112566804) (B := 1452238385) c65015_0 (rowSum_append (F := f65015) (lo := 171) (n := 198) (m := 655) (A := 309183413) (B := 1143054972) c65015_1 (rowSum_append (F := f65015) (lo := 369) (n := 114) (m := 541) (A := 372698786) (B := 770356186) c65015_2 (rowSum_append (F := f65015) (lo := 483) (n := 275) (m := 266) (A := 466448900) (B := 303907286) c65015_3 (c65015_4))))

theorem h65015 : P.leaf 34 65015 = 1564805189 :=
  leaf_weighted (k := 24) (d := 10) (H := 65015) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 65015) (by decide) (by decide +kernel)) sum65015

theorem h32765 : P.leaf 34 32765 = 1564805189 :=
  orient32 (v := 65015) (by decide) (by decide +kernel) h65015

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
  leaf_weighted (k := 24) (d := 10) (H := 32767) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 32767) (by decide) (by decide +kernel)) sum32767

def seg : List (ℕ × ℕ) := [(32759, 12), (32764, 12), (32765, 24), (32767, 12)]

theorem segOK : checkSeg 16 perms 32759 65004 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 32759 65004 60 92765845068 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 92765845068)
    (SegSum.cons (w := 12) h32759 (SegSum.cons (w := 12) h32764 (SegSum.cons (w := 24) h32765 (SegSum.cons (w := 12) h32767 (show SegSum (P.leaf 34) [] 0 from rfl))))) (by decide)

end RACert.S4N1.C0.S90
