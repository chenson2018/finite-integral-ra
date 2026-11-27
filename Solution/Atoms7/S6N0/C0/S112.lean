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

namespace RACert.S6N0.C0.S112

open RACert RACert.Problem

theorem cover245691 : P.CoversSplit 26 10 245691 0xfffffffffffffffffffffffffffff0f0ffffffffffffffccffffaaaaffcca080ffffffffffffffffffffa0a0ffffa0a0ffffffffffffffccffffa0a0ffcca080fffffffffffffffffffffffffffff0f0ffffffffffccffccffffaaaaffcca080ffffffffffffffffffffa0a0ffffa0a0ffffffffffccffccffffa0a0ffcca080 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f245691 (i : ℕ) := rowWeight keep9 twice9 i * P.leaf 26 (251587584 + i)

theorem c245691_0 : rowSum f245691 0 245 = 192758455 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 245691) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover245691 (by decide)
  decide +kernel

theorem c245691_1 : rowSum f245691 245 190 = 617524318 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 245691) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover245691 (by decide)
  decide +kernel

theorem c245691_2 : rowSum f245691 435 202 = 1230743408 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 245691) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover245691 (by decide)
  decide +kernel

theorem c245691_3 : rowSum f245691 637 243 = 1586115068 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 245691) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover245691 (by decide)
  decide +kernel

theorem c245691_4 : rowSum f245691 880 144 = 1260302678 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 245691) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover245691 (by decide)
  decide +kernel

theorem sum245691 : rowSum f245691 0 1024 = 4887443927 :=
  rowSum_append (F := f245691) (lo := 0) (n := 245) (m := 779) (A := 192758455) (B := 4694685472) c245691_0 (rowSum_append (F := f245691) (lo := 245) (n := 190) (m := 589) (A := 617524318) (B := 4077161154) c245691_1 (rowSum_append (F := f245691) (lo := 435) (n := 202) (m := 387) (A := 1230743408) (B := 2846417746) c245691_2 (rowSum_append (F := f245691) (lo := 637) (n := 243) (m := 144) (A := 1586115068) (B := 1260302678) c245691_3 (c245691_4))))

theorem h245691 : P.leaf 36 245691 = 4887443927 :=
  leaf_weighted (k := 26) (d := 10) (H := 245691) (keep := keep9) (twice := twice9) rows (by decide) (by decide) bal9 (invRow9 (H := 245691) (by decide) (by decide +kernel)) sum245691

theorem cover245693 : P.CoversSplit 26 10 245693 0xfffffffffffffffffffffffffffff0f0ffffffffffffffccffffaaaaffcca080ffffffffffffffffffffa0a0ffffa0a0ffffffffffffffccffffa0a0ffcca080fffffffffffffffffffffffffffff0f0ffffffffff00ff00ffffaaaaff00a000ffffffffffffffffffffa0a0ffffa0a0ffffffffff00ff00ffffa0a0ff00a000 :=
  coversSplit check rows (by decide) (by decide) (xs := [538, 930, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c245693_0 : P.sumLeaves 26 251589632 158 = 93736748 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245693) (lo := 0) (len := 158) (W := 93736748) check rows elimOK (by decide) (by decide) cover245693 (by decide)
  decide +kernel

theorem c245693_1 : P.sumLeaves 26 251589790 131 = 146774370 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245693) (lo := 158) (len := 131) (W := 146774370) check rows elimOK (by decide) (by decide) cover245693 (by decide)
  decide +kernel

theorem c245693_2 : P.sumLeaves 26 251589921 127 = 430627889 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245693) (lo := 289) (len := 127) (W := 430627889) check rows elimOK (by decide) (by decide) cover245693 (by decide)
  decide +kernel

theorem c245693_3 : P.sumLeaves 26 251590048 103 = 751087225 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245693) (lo := 416) (len := 103) (W := 751087225) check rows elimOK (by decide) (by decide) cover245693 (by decide)
  decide +kernel

theorem c245693_4 : P.sumLeaves 26 251590151 128 = 341444583 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245693) (lo := 519) (len := 128) (W := 341444583) check rows elimOK (by decide) (by decide) cover245693 (by decide)
  decide +kernel

theorem c245693_5 : P.sumLeaves 26 251590279 114 = 429383332 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245693) (lo := 647) (len := 114) (W := 429383332) check rows elimOK (by decide) (by decide) cover245693 (by decide)
  decide +kernel

theorem c245693_6 : P.sumLeaves 26 251590393 125 = 644248869 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245693) (lo := 761) (len := 125) (W := 644248869) check rows elimOK (by decide) (by decide) cover245693 (by decide)
  decide +kernel

theorem c245693_7 : P.sumLeaves 26 251590518 104 = 838287936 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245693) (lo := 886) (len := 104) (W := 838287936) check rows elimOK (by decide) (by decide) cover245693 (by decide)
  decide +kernel

theorem c245693_8 : P.sumLeaves 26 251590622 34 = 445344302 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 245693) (lo := 990) (len := 34) (W := 445344302) check rows elimOK (by decide) (by decide) cover245693 (by decide)
  decide +kernel

theorem h245693 : P.leaf 36 245693 = 4120935254 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(158, 93736748), (131, 146774370), (127, 430627889), (103, 751087225), (128, 341444583), (114, 429383332), (125, 644248869), (104, 838287936), (34, 445344302)]) (.cons c245693_0 (.cons c245693_1 (.cons c245693_2 (.cons c245693_3 (.cons c245693_4 (.cons c245693_5 (.cons c245693_6 (.cons c245693_7 (.cons c245693_8 (.nil)))))))))) (by decide) (by decide))

theorem cover245695 : P.CoversSplit 26 10 245695 0xfffffffffffffffffffffffffffff0f0ffffffffffffffccffffaaaaffcca080ffffffffffffffffffffa0a0ffffa0a0ffffffffffffffccffffa0a0ffcca080fffffffffffffffffffffffffffff0f0ffffffffffccffccffffaaaaffcca080ffffffffffffffffffffa0a0ffffa0a0ffffffffffccffccffffa0a0ffcca080 :=
  coversSplit check rows (by decide) (by decide) (xs := [538, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f245695 (i : ℕ) := rowWeight keep9 twice9 i * P.leaf 26 (251591680 + i)

theorem c245695_0 : rowSum f245695 0 245 = 723939629 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 245695) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover245695 (by decide)
  decide +kernel

theorem c245695_1 : rowSum f245695 245 190 = 1232731399 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 245695) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover245695 (by decide)
  decide +kernel

theorem c245695_2 : rowSum f245695 435 202 = 1634577083 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 245695) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover245695 (by decide)
  decide +kernel

theorem c245695_3 : rowSum f245695 637 243 = 1771671494 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 245695) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover245695 (by decide)
  decide +kernel

theorem c245695_4 : rowSum f245695 880 144 = 1351711030 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 245695) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover245695 (by decide)
  decide +kernel

theorem sum245695 : rowSum f245695 0 1024 = 6714630635 :=
  rowSum_append (F := f245695) (lo := 0) (n := 245) (m := 779) (A := 723939629) (B := 5990691006) c245695_0 (rowSum_append (F := f245695) (lo := 245) (n := 190) (m := 589) (A := 1232731399) (B := 4757959607) c245695_1 (rowSum_append (F := f245695) (lo := 435) (n := 202) (m := 387) (A := 1634577083) (B := 3123382524) c245695_2 (rowSum_append (F := f245695) (lo := 637) (n := 243) (m := 144) (A := 1771671494) (B := 1351711030) c245695_3 (c245695_4))))

theorem h245695 : P.leaf 36 245695 = 6714630635 :=
  leaf_weighted (k := 26) (d := 10) (H := 245695) (keep := keep9) (twice := twice9) rows (by decide) (by decide) bal9 (invRow9 (H := 245695) (by decide) (by decide +kernel)) sum245695

def seg : List (ℕ × ℕ) := [(245691, 360), (245693, 720), (245695, 360)]

theorem segOK : checkSeg 20 perms 245691 245724 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 245691 245724 1440 7143820225200 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 7143820225200)
    (SegSum.cons (w := 360) h245691 (SegSum.cons (w := 720) h245693 (SegSum.cons (w := 360) h245695 (show SegSum (P.leaf 36) [] 0 from rfl)))) (by decide)

end RACert.S6N0.C0.S112
