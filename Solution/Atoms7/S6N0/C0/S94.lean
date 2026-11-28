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

namespace RACert.S6N0.C0.S94

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
  leaf_weighted (k := 26) (d := 10) (H := 245691) (keep := keep9) (twice := twice9) rows (by decide) (by decide) (bal9) (invRow9 (H := 245691) (by decide) (by decide +kernel)) sum245691

theorem cover835549 : P.CoversSplit 26 10 835549 0xfffffffffffffffffffffafafffffafaffff0000ffcc0000ffff0000ffcc0000fffffffffffffffffffffafafffffafaffff0000ffcc0000ffff0000ffcc0000fffffffffffffffffffffafafffffafaffff0000ff000000ffff0000ff000000fffffffffffffffffffffafafffffafaffff0000ff000000ffff0000ff000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 930, 1265, 1272, 1273]) (by decide +kernel)

theorem c835549_0 : P.sumLeaves 26 855602176 184 = 352567409 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 835549) (lo := 0) (len := 184) (W := 352567409) check rows elimOK (by decide) (by decide) cover835549 (by decide)
  decide +kernel

theorem c835549_1 : P.sumLeaves 26 855602360 160 = 515034894 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 835549) (lo := 184) (len := 160) (W := 515034894) check rows elimOK (by decide) (by decide) cover835549 (by decide)
  decide +kernel

theorem c835549_2 : P.sumLeaves 26 855602520 120 = 507215135 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 835549) (lo := 344) (len := 120) (W := 507215135) check rows elimOK (by decide) (by decide) cover835549 (by decide)
  decide +kernel

theorem c835549_3 : P.sumLeaves 26 855602640 168 = 635308225 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 835549) (lo := 464) (len := 168) (W := 635308225) check rows elimOK (by decide) (by decide) cover835549 (by decide)
  decide +kernel

theorem c835549_4 : P.sumLeaves 26 855602808 104 = 557011292 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 835549) (lo := 632) (len := 104) (W := 557011292) check rows elimOK (by decide) (by decide) cover835549 (by decide)
  decide +kernel

theorem c835549_5 : P.sumLeaves 26 855602912 172 = 618226816 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 835549) (lo := 736) (len := 172) (W := 618226816) check rows elimOK (by decide) (by decide) cover835549 (by decide)
  decide +kernel

theorem c835549_6 : P.sumLeaves 26 855603084 100 = 729589683 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 835549) (lo := 908) (len := 100) (W := 729589683) check rows elimOK (by decide) (by decide) cover835549 (by decide)
  decide +kernel

theorem c835549_7 : P.sumLeaves 26 855603184 16 = 205981800 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 835549) (lo := 1008) (len := 16) (W := 205981800) check rows elimOK (by decide) (by decide) cover835549 (by decide)
  decide +kernel

theorem h835549 : P.leaf 36 835549 = 4120935254 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(184, 352567409), (160, 515034894), (120, 507215135), (168, 635308225), (104, 557011292), (172, 618226816), (100, 729589683), (16, 205981800)]) (.cons c835549_0 (.cons c835549_1 (.cons c835549_2 (.cons c835549_3 (.cons c835549_4 (.cons c835549_5 (.cons c835549_6 (.cons c835549_7 (.nil))))))))) (by decide) (by decide))

theorem h245693 : P.leaf 36 245693 = 4120935254 :=
  orient86 (v := 835549) (by decide) (by decide +kernel) h835549

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
  leaf_weighted (k := 26) (d := 10) (H := 245695) (keep := keep9) (twice := twice9) rows (by decide) (by decide) (bal9) (invRow9 (H := 245695) (by decide) (by decide +kernel)) sum245695

def seg : List (ℕ × ℕ) := [(245691, 360), (245693, 720), (245695, 360)]

theorem segOK : checkSeg 20 perms 245691 245724 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 245691 245724 1440 7143820225200 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 7143820225200)
    (SegSum.cons (w := 360) h245691 (SegSum.cons (w := 720) h245693 (SegSum.cons (w := 360) h245695 (show SegSum (P.leaf 36) [] 0 from rfl)))) (by decide)

end RACert.S6N0.C0.S94
