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

namespace RACert.S4N1.C0.S86

open RACert RACert.Problem

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
  leaf_weighted (k := 24) (d := 10) (H := 28607) (keep := keep5) (twice := twice5) rows (by decide) (by decide) (bal5) (invRow5 (H := 28607) (by decide) (by decide +kernel)) sum28607

theorem cover59372 : P.CoversSplit 24 10 59372 0xffffffffeaeaaaaaffffffffeaeaaaaaffffffffea00aa00ffffffffea00aa00eecceecceac8aa88ccccccccc8c88888eecceeccea00aa00ccccccccc8008800ffffffffeaeaaaaaffffffffeaeaaaaaffffffffea00aa00ffffffffea00aa00e0c0e0c0e0c0a080c0c0c0c0c0c08080e0c0e0c0e008a008c0c0c0c0c0088008 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 515, 522, 872]) (by decide +kernel)

noncomputable def f59372 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (60796928 + i)

theorem c59372_0 : rowSum f59372 0 389 = 36045836 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 59372) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover59372 (by decide)
  decide +kernel

theorem c59372_1 : rowSum f59372 389 121 = 85561382 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 59372) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover59372 (by decide)
  decide +kernel

theorem c59372_2 : rowSum f59372 510 514 = 136554335 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 59372) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover59372 (by decide)
  decide +kernel

theorem sum59372 : rowSum f59372 0 1024 = 258161553 :=
  rowSum_append (F := f59372) (lo := 0) (n := 389) (m := 635) (A := 36045836) (B := 222115717) c59372_0 (rowSum_append (F := f59372) (lo := 389) (n := 121) (m := 514) (A := 85561382) (B := 136554335) c59372_1 (c59372_2))

theorem h59372 : P.leaf 34 59372 = 258161553 :=
  leaf_weighted (k := 24) (d := 10) (H := 59372) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 59372) (by decide) (by decide +kernel)) sum59372

theorem h28652 : P.leaf 34 28652 = 258161553 :=
  orient24 (v := 59372) (by decide) (by decide +kernel) h59372

theorem cover59388 : P.CoversSplit 24 10 59388 0xfffffffffafaaaaafffffffffafaaaaafffffffffa00aa00fffffffffa00aa00ffccffccfac8aa88ccccccccc8c88888ffccffccfa00aa00ccccccccc8008800fffffffffafaaaaafffffffffafaaaaafffffffffa00aa00fffffffffa00aa00f0c0f0c0f0c0a080c0c0c0c0c0c08080f0c0f0c0f008a008c0c0c0c0c0088008 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 872, 1202, 1601]) (by decide +kernel)

noncomputable def f59388 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (60813312 + i)

theorem c59388_0 : rowSum f59388 0 375 = 71497892 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 59388) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover59388 (by decide)
  decide +kernel

theorem c59388_1 : rowSum f59388 375 125 = 131563676 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 59388) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover59388 (by decide)
  decide +kernel

theorem c59388_2 : rowSum f59388 500 512 = 211704697 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 59388) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover59388 (by decide)
  decide +kernel

theorem c59388_3 : rowSum f59388 1012 12 = 28629892 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 59388) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover59388 (by decide)
  decide +kernel

theorem sum59388 : rowSum f59388 0 1024 = 443396157 :=
  rowSum_append (F := f59388) (lo := 0) (n := 375) (m := 649) (A := 71497892) (B := 371898265) c59388_0 (rowSum_append (F := f59388) (lo := 375) (n := 125) (m := 524) (A := 131563676) (B := 240334589) c59388_1 (rowSum_append (F := f59388) (lo := 500) (n := 512) (m := 12) (A := 211704697) (B := 28629892) c59388_2 (c59388_3)))

theorem h59388 : P.leaf 34 59388 = 443396157 :=
  leaf_weighted (k := 24) (d := 10) (H := 59388) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 59388) (by decide) (by decide +kernel)) sum59388

theorem h28653 : P.leaf 34 28653 = 443396157 :=
  orient24 (v := 59388) (by decide) (by decide +kernel) h59388

theorem cover28654 : P.CoversSplit 24 10 28654 0xfffffffffafafafafffffffffafafafafffffffffafafafafffffffffafafafaeecceecceac8eac8ccccccccc8c8c8c8eecceecceac8eac8ccccccccc8c8c8c8fffffffffafafafaffff0000fafa0000fffffffffafafafaffff0000fafa0000eecc0000eac80000cccc0000c8c80000eecc0000eac80000cccc0000c8c80000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 515, 522, 1202, 1259, 1264, 1601]) (by decide +kernel)

theorem c28654_0 : P.sumLeaves 24 29341696 326 = 34303892 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28654) (lo := 0) (len := 326) (W := 34303892) check rows elimOK (by decide) (by decide) cover28654 (by decide)
  decide +kernel

theorem c28654_1 : P.sumLeaves 24 29342022 144 = 63999032 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28654) (lo := 326) (len := 144) (W := 63999032) check rows elimOK (by decide) (by decide) cover28654 (by decide)
  decide +kernel

theorem c28654_2 : P.sumLeaves 24 29342166 160 = 68952951 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28654) (lo := 470) (len := 160) (W := 68952951) check rows elimOK (by decide) (by decide) cover28654 (by decide)
  decide +kernel

theorem c28654_3 : P.sumLeaves 24 29342326 170 = 86138171 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28654) (lo := 630) (len := 170) (W := 86138171) check rows elimOK (by decide) (by decide) cover28654 (by decide)
  decide +kernel

theorem c28654_4 : P.sumLeaves 24 29342496 108 = 85419256 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28654) (lo := 800) (len := 108) (W := 85419256) check rows elimOK (by decide) (by decide) cover28654 (by decide)
  decide +kernel

theorem c28654_5 : P.sumLeaves 24 29342604 108 = 181442973 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28654) (lo := 908) (len := 108) (W := 181442973) check rows elimOK (by decide) (by decide) cover28654 (by decide)
  decide +kernel

theorem c28654_6 : P.sumLeaves 24 29342712 8 = 25850632 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28654) (lo := 1016) (len := 8) (W := 25850632) check rows elimOK (by decide) (by decide) cover28654 (by decide)
  decide +kernel

theorem h28654 : P.leaf 34 28654 = 546106907 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(326, 34303892), (144, 63999032), (160, 68952951), (170, 86138171), (108, 85419256), (108, 181442973), (8, 25850632)]) (.cons c28654_0 (.cons c28654_1 (.cons c28654_2 (.cons c28654_3 (.cons c28654_4 (.cons c28654_5 (.cons c28654_6 (.nil)))))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(28607, 24), (28652, 24), (28653, 24), (28654, 48)]

theorem segOK : checkSeg 16 perms 28607 28655 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 28607 28655 120 67606650648 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 67606650648)
    (SegSum.cons (w := 24) h28607 (SegSum.cons (w := 24) h28652 (SegSum.cons (w := 24) h28653 (SegSum.cons (w := 48) h28654 (show SegSum (P.leaf 34) [] 0 from rfl))))) (by decide)

end RACert.S4N1.C0.S86
