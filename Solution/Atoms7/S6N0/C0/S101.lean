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

namespace RACert.S6N0.C0.S101

open RACert RACert.Problem

theorem cover524286 : P.CoversSplit 26 10 524286 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffafaffccfac8fffffffffffffffffffffafafffffafafffffffffffffffffffffafaffccfac8ffffffffffffffffffffffffffffffffffffffffffccffccfffffafaffccfac8fffffffffffffffffffffafafffffafaffffffffffccffccfffffafaffccfac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [1658, 1665]) (by decide +kernel)

noncomputable def f524286 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 26 (536868864 + i)

theorem c524286_0 : rowSum f524286 0 210 = 1526344968 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 524286) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover524286 (by decide)
  decide +kernel

theorem c524286_1 : rowSum f524286 210 141 = 2432467066 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 524286) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover524286 (by decide)
  decide +kernel

theorem c524286_2 : rowSum f524286 351 96 = 3512533574 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 524286) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover524286 (by decide)
  decide +kernel

theorem c524286_3 : rowSum f524286 447 388 = 4658338528 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 524286) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover524286 (by decide)
  decide +kernel

theorem c524286_4 : rowSum f524286 835 188 = 4884504232 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 524286) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover524286 (by decide)
  decide +kernel

theorem c524286_5 : rowSum f524286 1023 1 = 36579204 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 524286) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover524286 (by decide)
  decide +kernel

theorem sum524286 : rowSum f524286 0 1024 = 17050767572 :=
  rowSum_append (F := f524286) (lo := 0) (n := 210) (m := 814) (A := 1526344968) (B := 15524422604) c524286_0 (rowSum_append (F := f524286) (lo := 210) (n := 141) (m := 673) (A := 2432467066) (B := 13091955538) c524286_1 (rowSum_append (F := f524286) (lo := 351) (n := 96) (m := 577) (A := 3512533574) (B := 9579421964) c524286_2 (rowSum_append (F := f524286) (lo := 447) (n := 388) (m := 189) (A := 4658338528) (B := 4921083436) c524286_3 (rowSum_append (F := f524286) (lo := 835) (n := 188) (m := 1) (A := 4884504232) (B := 36579204) c524286_4 (c524286_5)))))

theorem h524286 : P.leaf 36 524286 = 17050767572 :=
  leaf_weighted (k := 26) (d := 10) (H := 524286) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 524286) (by decide) (by decide +kernel)) sum524286

theorem cover524287 : P.CoversSplit 26 10 524287 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffafaffccfac8fffffffffffffffffffffafafffffafafffffffffffffffffffffafaffccfac8ffffffffffffffffffffffffffffffffffffffffffccffccfffffafaffccfac8fffffffffffffffffffffafafffffafaffffffffffccffccfffffafaffccfac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [1658, 1665]) (by decide +kernel)

noncomputable def f524287 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 26 (536869888 + i)

theorem c524287_0 : rowSum f524287 0 210 = 3505878644 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 524287) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover524287 (by decide)
  decide +kernel

theorem c524287_1 : rowSum f524287 210 141 = 4539362338 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 524287) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover524287 (by decide)
  decide +kernel

theorem c524287_2 : rowSum f524287 351 96 = 5181333726 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 524287) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover524287 (by decide)
  decide +kernel

theorem c524287_3 : rowSum f524287 447 388 = 5844267226 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 524287) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover524287 (by decide)
  decide +kernel

theorem c524287_4 : rowSum f524287 835 188 = 6219367048 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 524287) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover524287 (by decide)
  decide +kernel

theorem c524287_5 : rowSum f524287 1023 1 = 42499832 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 524287) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover524287 (by decide)
  decide +kernel

theorem sum524287 : rowSum f524287 0 1024 = 25332708814 :=
  rowSum_append (F := f524287) (lo := 0) (n := 210) (m := 814) (A := 3505878644) (B := 21826830170) c524287_0 (rowSum_append (F := f524287) (lo := 210) (n := 141) (m := 673) (A := 4539362338) (B := 17287467832) c524287_1 (rowSum_append (F := f524287) (lo := 351) (n := 96) (m := 577) (A := 5181333726) (B := 12106134106) c524287_2 (rowSum_append (F := f524287) (lo := 447) (n := 388) (m := 189) (A := 5844267226) (B := 6261866880) c524287_3 (rowSum_append (F := f524287) (lo := 835) (n := 188) (m := 1) (A := 6219367048) (B := 42499832) c524287_4 (c524287_5)))))

theorem h524287 : P.leaf 36 524287 = 25332708814 :=
  leaf_weighted (k := 26) (d := 10) (H := 524287) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 524287) (by decide) (by decide +kernel)) sum524287

theorem cover1048575 : P.CoversSplit 26 10 1048575 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff :=
  coversSplit check rows (by decide) (by decide) (xs := []) (by decide +kernel)

noncomputable def f1048575 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 26 (1073740800 + i)

theorem c1048575_0 : rowSum f1048575 0 124 = 4129309955 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 1048575) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover1048575 (by decide)
  decide +kernel

theorem c1048575_1 : rowSum f1048575 124 188 = 5019465627 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 1048575) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover1048575 (by decide)
  decide +kernel

theorem c1048575_2 : rowSum f1048575 312 96 = 5616156730 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 1048575) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover1048575 (by decide)
  decide +kernel

theorem c1048575_3 : rowSum f1048575 408 96 = 7070309334 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 1048575) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover1048575 (by decide)
  decide +kernel

theorem c1048575_4 : rowSum f1048575 504 380 = 6342688549 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 1048575) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover1048575 (by decide)
  decide +kernel

theorem c1048575_5 : rowSum f1048575 884 140 = 3732439680 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 1048575) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover1048575 (by decide)
  decide +kernel

theorem sum1048575 : rowSum f1048575 0 1024 = 31910369875 :=
  rowSum_append (F := f1048575) (lo := 0) (n := 124) (m := 900) (A := 4129309955) (B := 27781059920) c1048575_0 (rowSum_append (F := f1048575) (lo := 124) (n := 188) (m := 712) (A := 5019465627) (B := 22761594293) c1048575_1 (rowSum_append (F := f1048575) (lo := 312) (n := 96) (m := 616) (A := 5616156730) (B := 17145437563) c1048575_2 (rowSum_append (F := f1048575) (lo := 408) (n := 96) (m := 520) (A := 7070309334) (B := 10075128229) c1048575_3 (rowSum_append (F := f1048575) (lo := 504) (n := 380) (m := 140) (A := 6342688549) (B := 3732439680) c1048575_4 (c1048575_5)))))

theorem h1048575 : P.leaf 36 1048575 = 31910369875 :=
  leaf_weighted (k := 26) (d := 10) (H := 1048575) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 1048575) (by decide) (by decide +kernel)) sum1048575

def seg : List (ℕ × ℕ) := [(524286, 10), (524287, 20), (1048575, 1)]

theorem segOK : checkSeg 20 perms 524286 1048576 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 524286 1048576 31 709072221875 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 709072221875)
    (SegSum.cons (w := 10) h524286 (SegSum.cons (w := 20) h524287 (SegSum.cons (w := 1) h1048575 (show SegSum (P.leaf 36) [] 0 from rfl)))) (by decide)

end RACert.S6N0.C0.S101
