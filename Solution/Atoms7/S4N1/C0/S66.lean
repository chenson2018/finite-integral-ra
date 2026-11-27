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

namespace RACert.S4N1.C0.S66

open RACert RACert.Problem

theorem cover15871 : P.CoversSplit 24 10 15871 0xfffffffffffafafafffffffffffafafafffffffffffafafafffffffffffafafafffcfffcfac8fac8ffccffccfac8fac8fffcfffcfac8fac8ffccffccfac8fac8fffffffffffafafafffffffffffafafafffffffffafafafafffffffffafafafafffcfffcfac8fac8ffccffccfac8fac8ffccffccfac8fac8ffccffccfac8fac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [858, 865, 1209, 1217, 1258, 1609]) (by decide +kernel)

noncomputable def f15871 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (16251904 + i)

theorem c15871_0 : rowSum f15871 0 173 = 66305407 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 15871) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover15871 (by decide)
  decide +kernel

theorem c15871_1 : rowSum f15871 173 210 = 165606750 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 15871) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover15871 (by decide)
  decide +kernel

theorem c15871_2 : rowSum f15871 383 108 = 164866312 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 15871) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover15871 (by decide)
  decide +kernel

theorem c15871_3 : rowSum f15871 491 440 = 335769398 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 15871) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover15871 (by decide)
  decide +kernel

theorem c15871_4 : rowSum f15871 931 93 = 139379680 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 15871) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover15871 (by decide)
  decide +kernel

theorem sum15871 : rowSum f15871 0 1024 = 871927547 :=
  rowSum_append (F := f15871) (lo := 0) (n := 173) (m := 851) (A := 66305407) (B := 805622140) c15871_0 (rowSum_append (F := f15871) (lo := 173) (n := 210) (m := 641) (A := 165606750) (B := 640015390) c15871_1 (rowSum_append (F := f15871) (lo := 383) (n := 108) (m := 533) (A := 164866312) (B := 475149078) c15871_2 (rowSum_append (F := f15871) (lo := 491) (n := 440) (m := 93) (A := 335769398) (B := 139379680) c15871_3 (c15871_4))))

theorem h15871 : P.leaf 34 15871 = 871927547 :=
  leaf_weighted (k := 24) (d := 10) (H := 15871) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 15871) (by decide) (by decide +kernel)) sum15871

theorem cover16371 : P.CoversSplit 24 10 16371 0xfffffffffffffafafffffffffffffafafffffffffffffafafffffffffffffafafffffffffac8fac8ffccffccfac8fac8fffffffffac8fac8ffccffccfac8fac8fffffffffffffafafffffffffffffafafffffffffafafafafffffffffafafafafffffffffac8fac8ffccffccfac8fac8ffccffccfac8fac8ffccffccfac8fac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [1209, 1217, 1258, 1609]) (by decide +kernel)

noncomputable def f16371 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (16763904 + i)

theorem c16371_0 : rowSum f16371 0 173 = 42594742 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 16371) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover16371 (by decide)
  decide +kernel

theorem c16371_1 : rowSum f16371 173 201 = 97206188 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 16371) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover16371 (by decide)
  decide +kernel

theorem c16371_2 : rowSum f16371 374 109 = 168533414 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 16371) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover16371 (by decide)
  decide +kernel

theorem c16371_3 : rowSum f16371 483 275 = 271651262 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 16371) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover16371 (by decide)
  decide +kernel

theorem c16371_4 : rowSum f16371 758 266 = 215636186 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 16371) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover16371 (by decide)
  decide +kernel

theorem sum16371 : rowSum f16371 0 1024 = 795621792 :=
  rowSum_append (F := f16371) (lo := 0) (n := 173) (m := 851) (A := 42594742) (B := 753027050) c16371_0 (rowSum_append (F := f16371) (lo := 173) (n := 201) (m := 650) (A := 97206188) (B := 655820862) c16371_1 (rowSum_append (F := f16371) (lo := 374) (n := 109) (m := 541) (A := 168533414) (B := 487287448) c16371_2 (rowSum_append (F := f16371) (lo := 483) (n := 275) (m := 266) (A := 271651262) (B := 215636186) c16371_3 (c16371_4))))

theorem h16371 : P.leaf 34 16371 = 795621792 :=
  leaf_weighted (k := 24) (d := 10) (H := 16371) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 16371) (by decide) (by decide +kernel)) sum16371

theorem cover16372 : P.CoversSplit 24 10 16372 0xfffffffffafafafafffffffffafafafafffffffffafafafafffffffffafafafaffccffccfac8fac8ffccffccfac8fac8ffccffccfac8fac8ffccffccfac8fac8fffffffffafafafafffffffffafafafafffffffffafafafafffffffffafafafaffccffccfac8fac8ffccffccfac8fac8ffccffccfac8fac8ffccffccfac8fac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473]) (by decide +kernel)

noncomputable def f16372 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (16764928 + i)

theorem c16372_0 : rowSum f16372 0 173 = 6202284 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 16372) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover16372 (by decide)
  decide +kernel

theorem c16372_1 : rowSum f16372 173 216 = 23084736 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 16372) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover16372 (by decide)
  decide +kernel

theorem c16372_2 : rowSum f16372 389 110 = 45757960 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 16372) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover16372 (by decide)
  decide +kernel

theorem c16372_3 : rowSum f16372 499 449 = 58334622 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 16372) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover16372 (by decide)
  decide +kernel

theorem c16372_4 : rowSum f16372 948 76 = 26918152 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 16372) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover16372 (by decide)
  decide +kernel

theorem sum16372 : rowSum f16372 0 1024 = 160297754 :=
  rowSum_append (F := f16372) (lo := 0) (n := 173) (m := 851) (A := 6202284) (B := 154095470) c16372_0 (rowSum_append (F := f16372) (lo := 173) (n := 216) (m := 635) (A := 23084736) (B := 131010734) c16372_1 (rowSum_append (F := f16372) (lo := 389) (n := 110) (m := 525) (A := 45757960) (B := 85252774) c16372_2 (rowSum_append (F := f16372) (lo := 499) (n := 449) (m := 76) (A := 58334622) (B := 26918152) c16372_3 (c16372_4))))

theorem h16372 : P.leaf 34 16372 = 160297754 :=
  leaf_weighted (k := 24) (d := 10) (H := 16372) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 16372) (by decide) (by decide +kernel)) sum16372

theorem cover16373 : P.CoversSplit 24 10 16373 0xfffffffffffffafafffffffffffffafafffffffffffffafafffffffffffffafafffffffffac8fac8ffccffccfac8fac8fffffffffac8fac8ffccffccfac8fac8fffffffffffffafafffffffffffffafafffffffffafafafafffffffffafafafafffffffffac8fac8ffccffccfac8fac8ffccffccfac8fac8ffccffccfac8fac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 1209, 1217, 1258, 1609]) (by decide +kernel)

noncomputable def f16373 (i : ℕ) := rowWeight keep3 twice3 i * P.leaf 24 (16765952 + i)

theorem c16373_0 : rowSum f16373 0 245 = 27450006 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 16373) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover16373 (by decide)
  decide +kernel

theorem c16373_1 : rowSum f16373 245 177 = 46791538 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 16373) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover16373 (by decide)
  decide +kernel

theorem c16373_2 : rowSum f16373 422 202 = 121306192 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 16373) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover16373 (by decide)
  decide +kernel

theorem c16373_3 : rowSum f16373 624 198 = 119772782 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 16373) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover16373 (by decide)
  decide +kernel

theorem c16373_4 : rowSum f16373 822 170 = 171480443 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 16373) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover16373 (by decide)
  decide +kernel

theorem c16373_5 : rowSum f16373 992 32 = 93423394 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 16373) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover16373 (by decide)
  decide +kernel

theorem sum16373 : rowSum f16373 0 1024 = 580224355 :=
  rowSum_append (F := f16373) (lo := 0) (n := 245) (m := 779) (A := 27450006) (B := 552774349) c16373_0 (rowSum_append (F := f16373) (lo := 245) (n := 177) (m := 602) (A := 46791538) (B := 505982811) c16373_1 (rowSum_append (F := f16373) (lo := 422) (n := 202) (m := 400) (A := 121306192) (B := 384676619) c16373_2 (rowSum_append (F := f16373) (lo := 624) (n := 198) (m := 202) (A := 119772782) (B := 264903837) c16373_3 (rowSum_append (F := f16373) (lo := 822) (n := 170) (m := 32) (A := 171480443) (B := 93423394) c16373_4 (c16373_5)))))

theorem h16373 : P.leaf 34 16373 = 580224355 :=
  leaf_weighted (k := 24) (d := 10) (H := 16373) (keep := keep3) (twice := twice3) rows (by decide) (by decide) bal3 (invRow3 (H := 16373) (by decide) (by decide +kernel)) sum16373

def seg : List (ℕ × ℕ) := [(15871, 12), (16371, 3), (16372, 12), (16373, 24)]

theorem segOK : checkSeg 16 perms 15871 16375 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 15871 16375 51 28698953508 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 28698953508)
    (SegSum.cons (w := 12) h15871 (SegSum.cons (w := 3) h16371 (SegSum.cons (w := 12) h16372 (SegSum.cons (w := 24) h16373 (show SegSum (P.leaf 34) [] 0 from rfl))))) (by decide)

end RACert.S4N1.C0.S66
