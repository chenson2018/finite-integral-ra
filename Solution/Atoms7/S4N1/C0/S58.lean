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

namespace RACert.S4N1.C0.S58

open RACert RACert.Problem

theorem cover32755 : P.CoversSplit 24 10 32755 0xfffffffffafafafafffffffffafafafafffffffffafafafafffffffffafafafaffccffccfac8fac8ffccffccfac8fac8ffccffccfac8fac8ffccffccfac8fac8fffffffffafafafafffffffffafafafafffffffffafafafafffffffffafafafaffccffccfac8fac8ffccffccfac8fac8ffccffccfac8fac8ffccffccfac8fac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [1202, 1210, 1259, 1601]) (by decide +kernel)

noncomputable def f32755 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (33541120 + i)

theorem c32755_0 : rowSum f32755 0 173 = 61003150 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 32755) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover32755 (by decide)
  decide +kernel

theorem c32755_1 : rowSum f32755 173 216 = 133826624 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 32755) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover32755 (by decide)
  decide +kernel

theorem c32755_2 : rowSum f32755 389 110 = 291464066 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 32755) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover32755 (by decide)
  decide +kernel

theorem c32755_3 : rowSum f32755 499 449 = 324253970 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 32755) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover32755 (by decide)
  decide +kernel

theorem c32755_4 : rowSum f32755 948 76 = 169679760 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 32755) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover32755 (by decide)
  decide +kernel

theorem sum32755 : rowSum f32755 0 1024 = 980227570 :=
  rowSum_append (F := f32755) (lo := 0) (n := 173) (m := 851) (A := 61003150) (B := 919224420) c32755_0 (rowSum_append (F := f32755) (lo := 173) (n := 216) (m := 635) (A := 133826624) (B := 785397796) c32755_1 (rowSum_append (F := f32755) (lo := 389) (n := 110) (m := 525) (A := 291464066) (B := 493933730) c32755_2 (rowSum_append (F := f32755) (lo := 499) (n := 449) (m := 76) (A := 324253970) (B := 169679760) c32755_3 (c32755_4))))

theorem h32755 : P.leaf 34 32755 = 980227570 :=
  leaf_weighted (k := 24) (d := 10) (H := 32755) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 32755) (by decide) (by decide +kernel)) sum32755

theorem h16375 : P.leaf 34 16375 = 980227570 :=
  orient32 (v := 32755) (by decide) (by decide +kernel) h32755

theorem cover64995 : P.CoversSplit 24 10 64995 0xfffffffffefafafaffff0000fefa0000fffffffffefafafaffff0000fefa0000ffecffecfee8fae8ffcc0000fec80000ffecffecfee8fae8ffcc0000fec80000fffffffffefafafaffff0000fefa0000fffffffffafafafaffff0000fafa0000ffecffecfee8fae8ffcc0000fec80000ffccffccfac8fac8ffcc0000fac80000 :=
  coversSplit check rows (by decide) (by decide) (xs := [466, 515, 522, 858, 865, 1217, 1609]) (by decide +kernel)

noncomputable def f64995 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (66554880 + i)

theorem c64995_0 : rowSum f64995 0 229 = 78186984 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 64995) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover64995 (by decide)
  decide +kernel

theorem c64995_1 : rowSum f64995 229 242 = 145761528 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 64995) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover64995 (by decide)
  decide +kernel

theorem c64995_2 : rowSum f64995 471 474 = 229970728 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 64995) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover64995 (by decide)
  decide +kernel

theorem c64995_3 : rowSum f64995 945 79 = 60602848 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 64995) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover64995 (by decide)
  decide +kernel

theorem sum64995 : rowSum f64995 0 1024 = 514522088 :=
  rowSum_append (F := f64995) (lo := 0) (n := 229) (m := 795) (A := 78186984) (B := 436335104) c64995_0 (rowSum_append (F := f64995) (lo := 229) (n := 242) (m := 553) (A := 145761528) (B := 290573576) c64995_1 (rowSum_append (F := f64995) (lo := 471) (n := 474) (m := 79) (A := 229970728) (B := 60602848) c64995_2 (c64995_3)))

theorem h64995 : P.leaf 34 64995 = 514522088 :=
  leaf_weighted (k := 24) (d := 10) (H := 64995) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 64995) (by decide) (by decide +kernel)) sum64995

theorem h16380 : P.leaf 34 16380 = 514522088 :=
  orient32 (v := 64995) (by decide) (by decide +kernel) h64995

theorem cover65011 : P.CoversSplit 24 10 65011 0xfffffffffffafafafffffffffffafafafffffffffffafafafffffffffffafafafffcfffcfff8faf8ffccffccffc8fac8fffcfffcfff8faf8ffccffccffc8fac8fffffffffffafafafffffffffffafafafffffffffafafafafffffffffafafafafffcfffcfff8faf8ffccffccffc8fac8ffccffccfac8fac8ffccffccfac8fac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [858, 865, 1217, 1609]) (by decide +kernel)

noncomputable def f65011 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (66571264 + i)

theorem c65011_0 : rowSum f65011 0 171 = 78118976 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 65011) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover65011 (by decide)
  decide +kernel

theorem c65011_1 : rowSum f65011 171 198 = 222187888 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 65011) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover65011 (by decide)
  decide +kernel

theorem c65011_2 : rowSum f65011 369 114 = 229279014 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 65011) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover65011 (by decide)
  decide +kernel

theorem c65011_3 : rowSum f65011 483 275 = 304410276 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 65011) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover65011 (by decide)
  decide +kernel

theorem c65011_4 : rowSum f65011 758 266 = 186426968 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 65011) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover65011 (by decide)
  decide +kernel

theorem sum65011 : rowSum f65011 0 1024 = 1020423122 :=
  rowSum_append (F := f65011) (lo := 0) (n := 171) (m := 853) (A := 78118976) (B := 942304146) c65011_0 (rowSum_append (F := f65011) (lo := 171) (n := 198) (m := 655) (A := 222187888) (B := 720116258) c65011_1 (rowSum_append (F := f65011) (lo := 369) (n := 114) (m := 541) (A := 229279014) (B := 490837244) c65011_2 (rowSum_append (F := f65011) (lo := 483) (n := 275) (m := 266) (A := 304410276) (B := 186426968) c65011_3 (c65011_4))))

theorem h65011 : P.leaf 34 65011 = 1020423122 :=
  leaf_weighted (k := 24) (d := 10) (H := 65011) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 65011) (by decide) (by decide +kernel)) sum65011

theorem h16381 : P.leaf 34 16381 = 1020423122 :=
  orient32 (v := 65011) (by decide) (by decide +kernel) h65011

theorem cover16383 : P.CoversSplit 24 10 16383 0xfffffffffffffafafffffffffffffafafffffffffffffafafffffffffffffafafffffffffac8fac8ffccffccfac8fac8fffffffffac8fac8ffccffccfac8fac8fffffffffffffafafffffffffffffafafffffffffafafafafffffffffafafafafffffffffac8fac8ffccffccfac8fac8ffccffccfac8fac8ffccffccfac8fac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [1209, 1217, 1258, 1609]) (by decide +kernel)

noncomputable def f16383 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (16776192 + i)

theorem c16383_0 : rowSum f16383 0 173 = 201215250 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 16383) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover16383 (by decide)
  decide +kernel

theorem c16383_1 : rowSum f16383 173 201 = 343554458 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 16383) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover16383 (by decide)
  decide +kernel

theorem c16383_2 : rowSum f16383 374 109 = 417010060 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 16383) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover16383 (by decide)
  decide +kernel

theorem c16383_3 : rowSum f16383 483 275 = 592831626 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 16383) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover16383 (by decide)
  decide +kernel

theorem c16383_4 : rowSum f16383 758 266 = 401641260 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 16383) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover16383 (by decide)
  decide +kernel

theorem sum16383 : rowSum f16383 0 1024 = 1956252654 :=
  rowSum_append (F := f16383) (lo := 0) (n := 173) (m := 851) (A := 201215250) (B := 1755037404) c16383_0 (rowSum_append (F := f16383) (lo := 173) (n := 201) (m := 650) (A := 343554458) (B := 1411482946) c16383_1 (rowSum_append (F := f16383) (lo := 374) (n := 109) (m := 541) (A := 417010060) (B := 994472886) c16383_2 (rowSum_append (F := f16383) (lo := 483) (n := 275) (m := 266) (A := 592831626) (B := 401641260) c16383_3 (c16383_4))))

theorem h16383 : P.leaf 34 16383 = 1956252654 :=
  leaf_weighted (k := 24) (d := 10) (H := 16383) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 16383) (by decide) (by decide +kernel)) sum16383

def seg : List (ℕ × ℕ) := [(16375, 12), (16380, 6), (16381, 12), (16383, 6)]

theorem segOK : checkSeg 16 perms 16375 21668 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 16375 21668 36 38832456756 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 38832456756)
    (SegSum.cons (w := 12) h16375 (SegSum.cons (w := 6) h16380 (SegSum.cons (w := 12) h16381 (SegSum.cons (w := 6) h16383 (show SegSum (P.leaf 34) [] 0 from rfl))))) (by decide)

end RACert.S4N1.C0.S58
