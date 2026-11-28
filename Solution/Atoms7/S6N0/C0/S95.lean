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

namespace RACert.S6N0.C0.S95

open RACert RACert.Problem

theorem cover835539 : P.CoversSplit 26 10 835539 0xffaaffaaffaaffaaffaafaaaffaafaaaffaa0000ff880000ffaa0000ff880000ffaaffaaffaaffaaffaafaaaffaafaaaffaa0000ff880000ffaa0000ff880000ffaaffaaffaaffaaffaafaaaffaafaaaffaa0000ff880000ffaa0000ff880000ffaaffaaffaaffaaffaafaaaffaafaaaffaa0000ff880000ffaa0000ff880000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 488, 489, 1272]) (by decide +kernel)

noncomputable def f835539 (i : ℕ) := rowWeight keep10 twice10 i * P.leaf 26 (855591936 + i)

theorem c835539_0 : rowSum f835539 0 346 = 443468824 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 835539) (keep := keep10) (twice := twice10) check rows elimOK (by decide) (by decide) cover835539 (by decide)
  decide +kernel

theorem c835539_1 : rowSum f835539 346 148 = 607846536 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 835539) (keep := keep10) (twice := twice10) check rows elimOK (by decide) (by decide) cover835539 (by decide)
  decide +kernel

theorem c835539_2 : rowSum f835539 494 530 = 664264880 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 835539) (keep := keep10) (twice := twice10) check rows elimOK (by decide) (by decide) cover835539 (by decide)
  decide +kernel

theorem sum835539 : rowSum f835539 0 1024 = 1715580240 :=
  rowSum_append (F := f835539) (lo := 0) (n := 346) (m := 678) (A := 443468824) (B := 1272111416) c835539_0 (rowSum_append (F := f835539) (lo := 346) (n := 148) (m := 530) (A := 607846536) (B := 664264880) c835539_1 (c835539_2))

theorem h835539 : P.leaf 36 835539 = 1715580240 :=
  leaf_weighted (k := 26) (d := 10) (H := 835539) (keep := keep10) (twice := twice10) rows (by decide) (by decide) (bal10) (invRow10 (H := 835539) (by decide) (by decide +kernel)) sum835539

theorem h245724 : P.leaf 36 245724 = 1715580240 :=
  orient80 (v := 835539) (by decide) (by decide +kernel) h835539

theorem cover384955 : P.CoversSplit 26 10 384955 0xfffffffffffffffffffffffffffffffffffffffffffffffffafafafac8c8c8c8fffffffffffffffffafafafafafafafafffffffffffffffffafafafac8c8c8c8ffffffffffffffffffffffffffffffffffffffffccccccccfafafafac8c8c8c8fffffffffffffffffafafafafafafafaffffffffccccccccfafafafac8c8c8c8 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 1658, 1665]) (by decide +kernel)

noncomputable def f384955 (i : ℕ) := rowWeight keep4 twice4 i * P.leaf 26 (394193920 + i)

theorem c384955_0 : rowSum f384955 0 229 = 496432364 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 384955) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover384955 (by decide)
  decide +kernel

theorem c384955_1 : rowSum f384955 229 158 = 722887366 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 384955) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover384955 (by decide)
  decide +kernel

theorem c384955_2 : rowSum f384955 387 96 = 792578880 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 384955) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover384955 (by decide)
  decide +kernel

theorem c384955_3 : rowSum f384955 483 395 = 1234354066 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 384955) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover384955 (by decide)
  decide +kernel

theorem c384955_4 : rowSum f384955 878 146 = 949033537 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 384955) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover384955 (by decide)
  decide +kernel

theorem sum384955 : rowSum f384955 0 1024 = 4195286213 :=
  rowSum_append (F := f384955) (lo := 0) (n := 229) (m := 795) (A := 496432364) (B := 3698853849) c384955_0 (rowSum_append (F := f384955) (lo := 229) (n := 158) (m := 637) (A := 722887366) (B := 2975966483) c384955_1 (rowSum_append (F := f384955) (lo := 387) (n := 96) (m := 541) (A := 792578880) (B := 2183387603) c384955_2 (rowSum_append (F := f384955) (lo := 483) (n := 395) (m := 146) (A := 1234354066) (B := 949033537) c384955_3 (c384955_4))))

theorem h384955 : P.leaf 36 384955 = 4195286213 :=
  leaf_weighted (k := 26) (d := 10) (H := 384955) (keep := keep4) (twice := twice4) rows (by decide) (by decide) (bal4) (invRow4 (H := 384955) (by decide) (by decide +kernel)) sum384955

theorem h245725 : P.leaf 36 245725 = 4195286213 :=
  orient6 (v := 384955) (by decide) (by decide +kernel) h384955

theorem cover835551 : P.CoversSplit 26 10 835551 0xfffffffffffffffffffffafafffffafaffff0000ffcc0000ffff0000ffcc0000fffffffffffffffffffffafafffffafaffff0000ffcc0000ffff0000ffcc0000fffffffffffffffffffffafafffffafaffff0000ffcc0000ffff0000ffcc0000fffffffffffffffffffffafafffffafaffff0000ffcc0000ffff0000ffcc0000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 930, 1265, 1272, 1273]) (by decide +kernel)

noncomputable def f835551 (i : ℕ) := rowWeight keep10 twice10 i * P.leaf 26 (855604224 + i)

theorem c835551_0 : rowSum f835551 0 280 = 1440283351 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 835551) (keep := keep10) (twice := twice10) check rows elimOK (by decide) (by decide) cover835551 (by decide)
  decide +kernel

theorem c835551_1 : rowSum f835551 280 156 = 1609706374 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 835551) (keep := keep10) (twice := twice10) check rows elimOK (by decide) (by decide) cover835551 (by decide)
  decide +kernel

theorem c835551_2 : rowSum f835551 436 388 = 2119361934 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 835551) (keep := keep10) (twice := twice10) check rows elimOK (by decide) (by decide) cover835551 (by decide)
  decide +kernel

theorem c835551_3 : rowSum f835551 824 200 = 1775890904 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 835551) (keep := keep10) (twice := twice10) check rows elimOK (by decide) (by decide) cover835551 (by decide)
  decide +kernel

theorem sum835551 : rowSum f835551 0 1024 = 6945242563 :=
  rowSum_append (F := f835551) (lo := 0) (n := 280) (m := 744) (A := 1440283351) (B := 5504959212) c835551_0 (rowSum_append (F := f835551) (lo := 280) (n := 156) (m := 588) (A := 1609706374) (B := 3895252838) c835551_1 (rowSum_append (F := f835551) (lo := 436) (n := 388) (m := 200) (A := 2119361934) (B := 1775890904) c835551_2 (c835551_3)))

theorem h835551 : P.leaf 36 835551 = 6945242563 :=
  leaf_weighted (k := 26) (d := 10) (H := 835551) (keep := keep10) (twice := twice10) rows (by decide) (by decide) (bal10) (invRow10 (H := 835551) (by decide) (by decide +kernel)) sum835551

theorem h245727 : P.leaf 36 245727 = 6945242563 :=
  orient80 (v := 835551) (by decide) (by decide +kernel) h835551

theorem cover384982 : P.CoversSplit 26 10 384982 0xfffffffffffffffffffffffffffffffffffffffffffffffffafafafac8c8c8c8fffffffffffffffffafaaaaafafaaaaafffffffffffffffffafaaaaac8c88888ffffffffffffffffffffffffffffffffffccffccccccccccfac8fac8c8c8c8c8fffffffffffffffffafaaaaafafaaaaaffccffccccccccccfac8aa88c8c88888 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 1658, 1665]) (by decide +kernel)

noncomputable def f384982 (i : ℕ) := rowWeight keep4 twice4 i * P.leaf 26 (394221568 + i)

theorem c384982_0 : rowSum f384982 0 271 = 454711416 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 384982) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover384982 (by decide)
  decide +kernel

theorem c384982_1 : rowSum f384982 271 144 = 507191792 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 384982) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover384982 (by decide)
  decide +kernel

theorem c384982_2 : rowSum f384982 415 96 = 1016106794 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 384982) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover384982 (by decide)
  decide +kernel

theorem c384982_3 : rowSum f384982 511 460 = 705719224 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 384982) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover384982 (by decide)
  decide +kernel

theorem c384982_4 : rowSum f384982 971 53 = 388245614 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 384982) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover384982 (by decide)
  decide +kernel

theorem sum384982 : rowSum f384982 0 1024 = 3071974840 :=
  rowSum_append (F := f384982) (lo := 0) (n := 271) (m := 753) (A := 454711416) (B := 2617263424) c384982_0 (rowSum_append (F := f384982) (lo := 271) (n := 144) (m := 609) (A := 507191792) (B := 2110071632) c384982_1 (rowSum_append (F := f384982) (lo := 415) (n := 96) (m := 513) (A := 1016106794) (B := 1093964838) c384982_2 (rowSum_append (F := f384982) (lo := 511) (n := 460) (m := 53) (A := 705719224) (B := 388245614) c384982_3 (c384982_4))))

theorem h384982 : P.leaf 36 384982 = 3071974840 :=
  leaf_weighted (k := 26) (d := 10) (H := 384982) (keep := keep4) (twice := twice4) rows (by decide) (by decide) (bal4) (invRow4 (H := 384982) (by decide) (by decide +kernel)) sum384982

theorem h245738 : P.leaf 36 245738 = 3071974840 :=
  orient6 (v := 384982) (by decide) (by decide +kernel) h384982

def seg : List (ℕ × ℕ) := [(245724, 60), (245725, 360), (245727, 360), (245738, 180)]

theorem segOK : checkSeg 20 perms 245724 245739 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 245724 245739 960 4666480644960 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 4666480644960)
    (SegSum.cons (w := 60) h245724 (SegSum.cons (w := 360) h245725 (SegSum.cons (w := 360) h245727 (SegSum.cons (w := 180) h245738 (show SegSum (P.leaf 36) [] 0 from rfl))))) (by decide)

end RACert.S6N0.C0.S95
