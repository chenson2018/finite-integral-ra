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

namespace RACert.S6N0.C0.S100

open RACert RACert.Problem

theorem cover520157 : P.CoversSplit 26 10 520157 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffafaffccfac8fffffffffffffffffffffafafffffafafffffffffffffffffffffafaffccfac8ffffffffffffffffffffffffffffffffffffffffffccffccfffffafaffccfac8fffffffffffffffffffffafafffffafaffffffffffccffccfffffafaffccfac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 881, 1658, 1665]) (by decide +kernel)

noncomputable def f520157 (i : ℕ) := rowWeight keep8 twice8 i * P.leaf 26 (532640768 + i)

theorem c520157_0 : rowSum f520157 0 210 = 1600175403 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 520157) (keep := keep8) (twice := twice8) check rows elimOK (by decide) (by decide) cover520157 (by decide)
  decide +kernel

theorem c520157_1 : rowSum f520157 210 141 = 2299489916 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 520157) (keep := keep8) (twice := twice8) check rows elimOK (by decide) (by decide) cover520157 (by decide)
  decide +kernel

theorem c520157_2 : rowSum f520157 351 96 = 2819316196 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 520157) (keep := keep8) (twice := twice8) check rows elimOK (by decide) (by decide) cover520157 (by decide)
  decide +kernel

theorem c520157_3 : rowSum f520157 447 388 = 3413659279 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 520157) (keep := keep8) (twice := twice8) check rows elimOK (by decide) (by decide) cover520157 (by decide)
  decide +kernel

theorem c520157_4 : rowSum f520157 835 188 = 3881634176 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 520157) (keep := keep8) (twice := twice8) check rows elimOK (by decide) (by decide) cover520157 (by decide)
  decide +kernel

theorem c520157_5 : rowSum f520157 1023 1 = 30177572 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 520157) (keep := keep8) (twice := twice8) check rows elimOK (by decide) (by decide) cover520157 (by decide)
  decide +kernel

theorem sum520157 : rowSum f520157 0 1024 = 14044452542 :=
  rowSum_append (F := f520157) (lo := 0) (n := 210) (m := 814) (A := 1600175403) (B := 12444277139) c520157_0 (rowSum_append (F := f520157) (lo := 210) (n := 141) (m := 673) (A := 2299489916) (B := 10144787223) c520157_1 (rowSum_append (F := f520157) (lo := 351) (n := 96) (m := 577) (A := 2819316196) (B := 7325471027) c520157_2 (rowSum_append (F := f520157) (lo := 447) (n := 388) (m := 189) (A := 3413659279) (B := 3911811748) c520157_3 (rowSum_append (F := f520157) (lo := 835) (n := 188) (m := 1) (A := 3881634176) (B := 30177572) c520157_4 (c520157_5)))))

theorem h520157 : P.leaf 36 520157 = 14044452542 :=
  leaf_weighted (k := 26) (d := 10) (H := 520157) (keep := keep8) (twice := twice8) rows (by decide) (by decide) (bal8) (invRow8 (H := 520157) (by decide) (by decide +kernel)) sum520157

theorem cover520159 : P.CoversSplit 26 10 520159 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffafaffccfac8fffffffffffffffffffffafafffffafafffffffffffffffffffffafaffccfac8ffffffffffffffffffffffffffffffffffffffffffccffccfffffafaffccfac8fffffffffffffffffffffafafffffafaffffffffffccffccfffffafaffccfac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 881, 1658, 1665]) (by decide +kernel)

noncomputable def f520159 (i : ℕ) := rowWeight keep8 twice8 i * P.leaf 26 (532642816 + i)

theorem c520159_0 : rowSum f520159 0 210 = 2147644662 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 520159) (keep := keep8) (twice := twice8) check rows elimOK (by decide) (by decide) cover520159 (by decide)
  decide +kernel

theorem c520159_1 : rowSum f520159 210 141 = 2851987413 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 520159) (keep := keep8) (twice := twice8) check rows elimOK (by decide) (by decide) cover520159 (by decide)
  decide +kernel

theorem c520159_2 : rowSum f520159 351 96 = 3353226258 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 520159) (keep := keep8) (twice := twice8) check rows elimOK (by decide) (by decide) cover520159 (by decide)
  decide +kernel

theorem c520159_3 : rowSum f520159 447 388 = 4096331004 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 520159) (keep := keep8) (twice := twice8) check rows elimOK (by decide) (by decide) cover520159 (by decide)
  decide +kernel

theorem c520159_4 : rowSum f520159 835 188 = 4269687268 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 520159) (keep := keep8) (twice := twice8) check rows elimOK (by decide) (by decide) cover520159 (by decide)
  decide +kernel

theorem c520159_5 : rowSum f520159 1023 1 = 33310104 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 520159) (keep := keep8) (twice := twice8) check rows elimOK (by decide) (by decide) cover520159 (by decide)
  decide +kernel

theorem sum520159 : rowSum f520159 0 1024 = 16752186709 :=
  rowSum_append (F := f520159) (lo := 0) (n := 210) (m := 814) (A := 2147644662) (B := 14604542047) c520159_0 (rowSum_append (F := f520159) (lo := 210) (n := 141) (m := 673) (A := 2851987413) (B := 11752554634) c520159_1 (rowSum_append (F := f520159) (lo := 351) (n := 96) (m := 577) (A := 3353226258) (B := 8399328376) c520159_2 (rowSum_append (F := f520159) (lo := 447) (n := 388) (m := 189) (A := 4096331004) (B := 4302997372) c520159_3 (rowSum_append (F := f520159) (lo := 835) (n := 188) (m := 1) (A := 4269687268) (B := 33310104) c520159_4 (c520159_5)))))

theorem h520159 : P.leaf 36 520159 = 16752186709 :=
  leaf_weighted (k := 26) (d := 10) (H := 520159) (keep := keep8) (twice := twice8) rows (by decide) (by decide) (bal8) (invRow8 (H := 520159) (by decide) (by decide +kernel)) sum520159

theorem cover523263 : P.CoversSplit 26 10 523263 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffafaffccfac8fffffffffffffffffffffafafffffafafffffffffffffffffffffafaffccfac8ffffffffffffffffffffffffffffffffffffffffffccffccfffffafaffccfac8fffffffffffffffffffffafafffffafaffffffffffccffccfffffafaffccfac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [1658, 1665]) (by decide +kernel)

noncomputable def f523263 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 26 (535821312 + i)

theorem c523263_0 : rowSum f523263 0 210 = 2564291152 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 523263) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover523263 (by decide)
  decide +kernel

theorem c523263_1 : rowSum f523263 210 141 = 3597607880 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 523263) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover523263 (by decide)
  decide +kernel

theorem c523263_2 : rowSum f523263 351 96 = 4058972444 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 523263) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover523263 (by decide)
  decide +kernel

theorem c523263_3 : rowSum f523263 447 388 = 4704206700 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 523263) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover523263 (by decide)
  decide +kernel

theorem c523263_4 : rowSum f523263 835 188 = 5452772700 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 523263) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover523263 (by decide)
  decide +kernel

theorem c523263_5 : rowSum f523263 1023 1 = 37110984 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 523263) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover523263 (by decide)
  decide +kernel

theorem sum523263 : rowSum f523263 0 1024 = 20414961860 :=
  rowSum_append (F := f523263) (lo := 0) (n := 210) (m := 814) (A := 2564291152) (B := 17850670708) c523263_0 (rowSum_append (F := f523263) (lo := 210) (n := 141) (m := 673) (A := 3597607880) (B := 14253062828) c523263_1 (rowSum_append (F := f523263) (lo := 351) (n := 96) (m := 577) (A := 4058972444) (B := 10194090384) c523263_2 (rowSum_append (F := f523263) (lo := 447) (n := 388) (m := 189) (A := 4704206700) (B := 5489883684) c523263_3 (rowSum_append (F := f523263) (lo := 835) (n := 188) (m := 1) (A := 5452772700) (B := 37110984) c523263_4 (c523263_5)))))

theorem h523263 : P.leaf 36 523263 = 20414961860 :=
  leaf_weighted (k := 26) (d := 10) (H := 523263) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 523263) (by decide) (by decide +kernel)) sum523263

theorem h520191 : P.leaf 36 520191 = 20414961860 :=
  orient6 (v := 523263) (by decide) (by decide +kernel) h523263

def seg : List (ℕ × ℕ) := [(520157, 30), (520159, 120), (520191, 90)]

theorem segOK : checkSeg 20 perms 520157 524286 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 520157 524286 240 4268942548740 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 4268942548740)
    (SegSum.cons (w := 30) h520157 (SegSum.cons (w := 120) h520159 (SegSum.cons (w := 90) h520191 (show SegSum (P.leaf 36) [] 0 from rfl)))) (by decide)

end RACert.S6N0.C0.S100
