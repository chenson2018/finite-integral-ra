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

namespace RACert.S6N0.C0.S85

open RACert RACert.Problem

theorem cover827323 : P.CoversSplit 26 10 827323 0xfffffffffffffffffffffafa00000000f0f0f0f0f0c0f0c0f0f0f0f000000000fffffffffffffffffffffafa00000000f0f0f0f0f0c0f0c0f0f0f0f000000000fffffffffffffffffffffafa00000000f0f0f0f0f0c0f0c0f0f0f0f000000000fffffffffffffffffffffafa00000000f0f0f0f0f0c0f0c0f0f0f0f000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 922, 929, 930, 1266]) (by decide +kernel)

noncomputable def f827323 (i : ℕ) := rowWeight keep4 twice4 i * P.leaf 26 (847178752 + i)

theorem c827323_0 : rowSum f827323 0 342 = 594174123 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 827323) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover827323 (by decide)
  decide +kernel

theorem c827323_1 : rowSum f827323 342 152 = 805023622 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 827323) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover827323 (by decide)
  decide +kernel

theorem c827323_2 : rowSum f827323 494 530 = 1010251229 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 827323) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover827323 (by decide)
  decide +kernel

theorem sum827323 : rowSum f827323 0 1024 = 2409448974 :=
  rowSum_append (F := f827323) (lo := 0) (n := 342) (m := 682) (A := 594174123) (B := 1815274851) c827323_0 (rowSum_append (F := f827323) (lo := 342) (n := 152) (m := 530) (A := 805023622) (B := 1010251229) c827323_1 (c827323_2))

theorem h827323 : P.leaf 36 827323 = 2409448974 :=
  leaf_weighted (k := 26) (d := 10) (H := 827323) (keep := keep4) (twice := twice4) rows (by decide) (by decide) (bal4) (invRow4 (H := 827323) (by decide) (by decide +kernel)) sum827323

theorem h241534 : P.leaf 36 241534 = 2409448974 :=
  orient80 (v := 827323) (by decide) (by decide +kernel) h827323

theorem cover383487 : P.CoversSplit 26 10 383487 0xfffffffffffffffffffffefefffffefeffffffffffeeffeefafafafac8c8c8c8fffffffffffffffffafafafafafafafaffffffffffeeffeefafafafac8c8c8c8fffffffffffffffffffffefefffffefeffffffffccccccccfafafafac8c8c8c8fffffffffffffffffafafafafafafafaffffffffccccccccfafafafac8c8c8c8 :=
  coversSplit check rows (by decide) (by decide) (xs := [629, 636, 922, 1273, 1658, 1665]) (by decide +kernel)

noncomputable def f383487 (i : ℕ) := rowWeight keep4 twice4 i * P.leaf 26 (392690688 + i)

theorem c383487_0 : rowSum f383487 0 229 = 259926126 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 383487) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover383487 (by decide)
  decide +kernel

theorem c383487_1 : rowSum f383487 229 159 = 700479346 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 383487) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover383487 (by decide)
  decide +kernel

theorem c383487_2 : rowSum f383487 388 99 = 852611670 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 383487) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover383487 (by decide)
  decide +kernel

theorem c383487_3 : rowSum f383487 487 399 = 1506514382 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 383487) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover383487 (by decide)
  decide +kernel

theorem c383487_4 : rowSum f383487 886 138 = 1078539884 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 383487) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover383487 (by decide)
  decide +kernel

theorem sum383487 : rowSum f383487 0 1024 = 4398071408 :=
  rowSum_append (F := f383487) (lo := 0) (n := 229) (m := 795) (A := 259926126) (B := 4138145282) c383487_0 (rowSum_append (F := f383487) (lo := 229) (n := 159) (m := 636) (A := 700479346) (B := 3437665936) c383487_1 (rowSum_append (F := f383487) (lo := 388) (n := 99) (m := 537) (A := 852611670) (B := 2585054266) c383487_2 (rowSum_append (F := f383487) (lo := 487) (n := 399) (m := 138) (A := 1506514382) (B := 1078539884) c383487_3 (c383487_4))))

theorem h383487 : P.leaf 36 383487 = 4398071408 :=
  leaf_weighted (k := 26) (d := 10) (H := 383487) (keep := keep4) (twice := twice4) rows (by decide) (by decide) (bal4) (invRow4 (H := 383487) (by decide) (by decide +kernel)) sum383487

theorem h241535 : P.leaf 36 241535 = 4398071408 :=
  orient6 (v := 383487) (by decide) (by decide +kernel) h383487

theorem cover383959 : P.CoversSplit 26 10 383959 0xfffffffffffffffffffffffffffffffffffffffffffffffffafafafac8c8c8c8fffffffffffffffffafafafafafafafafffffffffffffffffafafafac8c8c8c8ffffffffffffffffffffffffffffffffffffffffccccccccfafafafac8c8c8c8fffffffffffffffffafafafafafafafaffffffffccccccccfafafafac8c8c8c8 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 922, 1273, 1658, 1665]) (by decide +kernel)

noncomputable def f383959 (i : ℕ) := rowWeight keep4 twice4 i * P.leaf 26 (393174016 + i)

theorem c383959_0 : rowSum f383959 0 229 = 461729936 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 383959) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover383959 (by decide)
  decide +kernel

theorem c383959_1 : rowSum f383959 229 158 = 561356102 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 383959) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover383959 (by decide)
  decide +kernel

theorem c383959_2 : rowSum f383959 387 96 = 713273780 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 383959) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover383959 (by decide)
  decide +kernel

theorem c383959_3 : rowSum f383959 483 395 = 807236806 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 383959) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover383959 (by decide)
  decide +kernel

theorem c383959_4 : rowSum f383959 878 146 = 614426796 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 383959) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover383959 (by decide)
  decide +kernel

theorem sum383959 : rowSum f383959 0 1024 = 3158023420 :=
  rowSum_append (F := f383959) (lo := 0) (n := 229) (m := 795) (A := 461729936) (B := 2696293484) c383959_0 (rowSum_append (F := f383959) (lo := 229) (n := 158) (m := 637) (A := 561356102) (B := 2134937382) c383959_1 (rowSum_append (F := f383959) (lo := 387) (n := 96) (m := 541) (A := 713273780) (B := 1421663602) c383959_2 (rowSum_append (F := f383959) (lo := 483) (n := 395) (m := 146) (A := 807236806) (B := 614426796) c383959_3 (c383959_4))))

theorem h383959 : P.leaf 36 383959 = 3158023420 :=
  leaf_weighted (k := 26) (d := 10) (H := 383959) (keep := keep4) (twice := twice4) rows (by decide) (by decide) (bal4) (invRow4 (H := 383959) (by decide) (by decide +kernel)) sum383959

theorem h241643 : P.leaf 36 241643 = 3158023420 :=
  orient6 (v := 383959) (by decide) (by decide +kernel) h383959

theorem cover826879 : P.CoversSplit 26 10 826879 0xfffffffffffffffffffffafafffffafaffffffffffccffccfffffafaffccfac8fffffffffffffffffffffafafffffafaffffffffffccffccfffffafaffccfac8fffffffffffffffffffffafafffffafaffffffffffccffccfffffafaffccfac8fffffffffffffffffffffafafffffafaffffffffffccffccfffffafaffccfac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [629, 636, 922, 930]) (by decide +kernel)

noncomputable def f826879 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 26 (846724096 + i)

theorem c826879_0 : rowSum f826879 0 210 = 385102520 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 826879) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover826879 (by decide)
  decide +kernel

theorem c826879_1 : rowSum f826879 210 141 = 675890078 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 826879) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover826879 (by decide)
  decide +kernel

theorem c826879_2 : rowSum f826879 351 104 = 1130103842 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 826879) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover826879 (by decide)
  decide +kernel

theorem c826879_3 : rowSum f826879 455 392 = 1549349997 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 826879) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover826879 (by decide)
  decide +kernel

theorem c826879_4 : rowSum f826879 847 177 = 1480156779 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 826879) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover826879 (by decide)
  decide +kernel

theorem sum826879 : rowSum f826879 0 1024 = 5220603216 :=
  rowSum_append (F := f826879) (lo := 0) (n := 210) (m := 814) (A := 385102520) (B := 4835500696) c826879_0 (rowSum_append (F := f826879) (lo := 210) (n := 141) (m := 673) (A := 675890078) (B := 4159610618) c826879_1 (rowSum_append (F := f826879) (lo := 351) (n := 104) (m := 569) (A := 1130103842) (B := 3029506776) c826879_2 (rowSum_append (F := f826879) (lo := 455) (n := 392) (m := 177) (A := 1549349997) (B := 1480156779) c826879_3 (c826879_4))))

theorem h826879 : P.leaf 36 826879 = 5220603216 :=
  leaf_weighted (k := 26) (d := 10) (H := 826879) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 826879) (by decide) (by decide +kernel)) sum826879

theorem h241647 : P.leaf 36 241647 = 5220603216 :=
  orient80 (v := 826879) (by decide) (by decide +kernel) h826879

def seg : List (ℕ × ℕ) := [(241534, 180), (241535, 360), (241643, 90), (241647, 180)]

theorem segOK : checkSeg 20 perms 241534 241663 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 241534 241663 810 3240937208880 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 3240937208880)
    (SegSum.cons (w := 180) h241534 (SegSum.cons (w := 360) h241535 (SegSum.cons (w := 90) h241643 (SegSum.cons (w := 180) h241647 (show SegSum (P.leaf 36) [] 0 from rfl))))) (by decide)

end RACert.S6N0.C0.S85
