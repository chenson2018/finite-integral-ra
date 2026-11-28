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

namespace RACert.S4N1.C0.S57

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
  leaf_weighted (k := 24) (d := 10) (H := 15871) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 15871) (by decide) (by decide +kernel)) sum15871

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
  leaf_weighted (k := 24) (d := 10) (H := 16371) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 16371) (by decide) (by decide +kernel)) sum16371

theorem cover32227 : P.CoversSplit 24 10 32227 0xfffffffffafafafaffff0000fafa0000ffff000000000000ffff000000000000ffccffccfac8fac8ffcc0000fac80000ffcc000000000000ffcc000000000000fffffffffafafafa0000000000000000ffff05050000000000330000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [466, 515, 522, 858, 865, 1202, 1210, 1259, 1601]) (by decide +kernel)

noncomputable def f32227 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (33000448 + i)

theorem c32227_0 : rowSum f32227 0 735 = 85129622 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 32227) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover32227 (by decide)
  decide +kernel

theorem c32227_1 : rowSum f32227 735 289 = 75168132 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 32227) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover32227 (by decide)
  decide +kernel

theorem sum32227 : rowSum f32227 0 1024 = 160297754 :=
  rowSum_append (F := f32227) (lo := 0) (n := 735) (m := 289) (A := 85129622) (B := 75168132) c32227_0 (c32227_1)

theorem h32227 : P.leaf 34 32227 = 160297754 :=
  leaf_weighted (k := 24) (d := 10) (H := 32227) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 32227) (by decide) (by decide +kernel)) sum32227

theorem h16372 : P.leaf 34 16372 = 160297754 :=
  orient32 (v := 32227) (by decide) (by decide +kernel) h32227

theorem cover32243 : P.CoversSplit 24 10 32243 0xfffffffffafafafafffffffffafafafafffffffffafafafafffffffffafafafaffccffccfac8fac8ffccffccfac8fac8ffccffccfac8fac8ffccffccfac8fac8fffffffffafafafafffffffffafafafafffffffffafafafafffffffffafafafaffccffccfac8fac8ffccffccfac8fac8ffccffccfac8fac8ffccffccfac8fac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [858, 865, 1202, 1259, 1601]) (by decide +kernel)

noncomputable def f32243 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (33016832 + i)

theorem c32243_0 : rowSum f32243 0 173 = 33964384 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 32243) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover32243 (by decide)
  decide +kernel

theorem c32243_1 : rowSum f32243 173 216 = 91091703 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 32243) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover32243 (by decide)
  decide +kernel

theorem c32243_2 : rowSum f32243 389 110 = 160759818 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 32243) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover32243 (by decide)
  decide +kernel

theorem c32243_3 : rowSum f32243 499 449 = 196365342 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 32243) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover32243 (by decide)
  decide +kernel

theorem c32243_4 : rowSum f32243 948 76 = 98043108 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 32243) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover32243 (by decide)
  decide +kernel

theorem sum32243 : rowSum f32243 0 1024 = 580224355 :=
  rowSum_append (F := f32243) (lo := 0) (n := 173) (m := 851) (A := 33964384) (B := 546259971) c32243_0 (rowSum_append (F := f32243) (lo := 173) (n := 216) (m := 635) (A := 91091703) (B := 455168268) c32243_1 (rowSum_append (F := f32243) (lo := 389) (n := 110) (m := 525) (A := 160759818) (B := 294408450) c32243_2 (rowSum_append (F := f32243) (lo := 499) (n := 449) (m := 76) (A := 196365342) (B := 98043108) c32243_3 (c32243_4))))

theorem h32243 : P.leaf 34 32243 = 580224355 :=
  leaf_weighted (k := 24) (d := 10) (H := 32243) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 32243) (by decide) (by decide +kernel)) sum32243

theorem h16373 : P.leaf 34 16373 = 580224355 :=
  orient32 (v := 32243) (by decide) (by decide +kernel) h32243

def seg : List (ℕ × ℕ) := [(15871, 12), (16371, 3), (16372, 12), (16373, 24)]

theorem segOK : checkSeg 16 perms 15871 16375 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 15871 16375 51 28698953508 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 28698953508)
    (SegSum.cons (w := 12) h15871 (SegSum.cons (w := 3) h16371 (SegSum.cons (w := 12) h16372 (SegSum.cons (w := 24) h16373 (show SegSum (P.leaf 34) [] 0 from rfl))))) (by decide)

end RACert.S4N1.C0.S57
