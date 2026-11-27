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

namespace RACert.S6N0.C0.S86

open RACert RACert.Problem

theorem cover122836 : P.CoversSplit 26 10 122836 0xfffffffffffffafafffffffffffffafafffffffffffffa00fafafafac8c8c800fffffafafffffafafafaa0a0fafaa0a0fffffafafffffa00fafaa0a0c8c88000ffccffccffccfac8ffccffccffccfac8ffccffcccc00c800fac8fac8c800c800ffccfac8ffccfac8fac8a080fac8a080ffccfac8cc00c800fac8a080c8008000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 922, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f122836 (i : ℕ) := rowWeight keep9 twice9 i * P.leaf 26 (125784064 + i)

theorem c122836_0 : rowSum f122836 0 370 = 26116560 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 122836) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover122836 (by decide)
  decide +kernel

theorem c122836_1 : rowSum f122836 370 267 = 71279816 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 122836) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover122836 (by decide)
  decide +kernel

theorem c122836_2 : rowSum f122836 637 253 = 68686336 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 122836) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover122836 (by decide)
  decide +kernel

theorem c122836_3 : rowSum f122836 890 134 = 53935672 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 122836) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover122836 (by decide)
  decide +kernel

theorem sum122836 : rowSum f122836 0 1024 = 220018384 :=
  rowSum_append (F := f122836) (lo := 0) (n := 370) (m := 654) (A := 26116560) (B := 193901824) c122836_0 (rowSum_append (F := f122836) (lo := 370) (n := 267) (m := 387) (A := 71279816) (B := 122622008) c122836_1 (rowSum_append (F := f122836) (lo := 637) (n := 253) (m := 134) (A := 68686336) (B := 53935672) c122836_2 (c122836_3)))

theorem h122836 : P.leaf 36 122836 = 220018384 :=
  leaf_weighted (k := 26) (d := 10) (H := 122836) (keep := keep9) (twice := twice9) rows (by decide) (by decide) bal9 (invRow9 (H := 122836) (by decide) (by decide +kernel)) sum122836

theorem cover122837 : P.CoversSplit 26 10 122837 0xfffffffffffffafafffffffffffffafafffffffffffffa00fafafafac8c8c800fffffafafffffafafafaf0f0fafaf0f0fffffafafffffa00fafaf0f0c8c8c000ffffffffffccfac8ffffffffffccfac8ffffffffcc00c800fafafafac800c800fffffafaffccfac8fafaf0f0fac8f0c0fffffafacc00c800fafaf0f0c800c000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 922, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c122837_0 : P.sumLeaves 26 125785088 198 = 28319642 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122837) (lo := 0) (len := 198) (W := 28319642) check rows elimOK (by decide) (by decide) cover122837 (by decide)
  decide +kernel

theorem c122837_1 : P.sumLeaves 26 125785286 165 = 61695767 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122837) (lo := 198) (len := 165) (W := 61695767) check rows elimOK (by decide) (by decide) cover122837 (by decide)
  decide +kernel

theorem c122837_2 : P.sumLeaves 26 125785451 118 = 153247456 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122837) (lo := 363) (len := 118) (W := 153247456) check rows elimOK (by decide) (by decide) cover122837 (by decide)
  decide +kernel

theorem c122837_3 : P.sumLeaves 26 125785569 146 = 161307366 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122837) (lo := 481) (len := 146) (W := 161307366) check rows elimOK (by decide) (by decide) cover122837 (by decide)
  decide +kernel

theorem c122837_4 : P.sumLeaves 26 125785715 128 = 198975576 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122837) (lo := 627) (len := 128) (W := 198975576) check rows elimOK (by decide) (by decide) cover122837 (by decide)
  decide +kernel

theorem c122837_5 : P.sumLeaves 26 125785843 137 = 202335113 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122837) (lo := 755) (len := 137) (W := 202335113) check rows elimOK (by decide) (by decide) cover122837 (by decide)
  decide +kernel

theorem c122837_6 : P.sumLeaves 26 125785980 104 = 269364186 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122837) (lo := 892) (len := 104) (W := 269364186) check rows elimOK (by decide) (by decide) cover122837 (by decide)
  decide +kernel

theorem c122837_7 : P.sumLeaves 26 125786084 28 = 150049318 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122837) (lo := 996) (len := 28) (W := 150049318) check rows elimOK (by decide) (by decide) cover122837 (by decide)
  decide +kernel

theorem h122837 : P.leaf 36 122837 = 1225294424 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(198, 28319642), (165, 61695767), (118, 153247456), (146, 161307366), (128, 198975576), (137, 202335113), (104, 269364186), (28, 150049318)]) (.cons c122837_0 (.cons c122837_1 (.cons c122837_2 (.cons c122837_3 (.cons c122837_4 (.cons c122837_5 (.cons c122837_6 (.cons c122837_7 (.nil))))))))) (by decide) (by decide))

theorem cover122839 : P.CoversSplit 26 10 122839 0xfffffffffffffafafffffffffffffafafffffffffffffa00fafafafac8c8c800fffffafafffffafafafafafafafafafafffffafafffffa00fafafafac8c8c800fffffffffffffafafffffffffffffafaffffffffcc00c800fafafafac800c800fffffafafffffafafafafafafafafafafffffafacc00c800fafafafac800c800 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f122839 (i : ℕ) := rowWeight keep9 twice9 i * P.leaf 26 (125787136 + i)

theorem c122839_0 : rowSum f122839 0 292 = 211812174 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 122839) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover122839 (by decide)
  decide +kernel

theorem c122839_1 : rowSum f122839 292 242 = 726229624 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 122839) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover122839 (by decide)
  decide +kernel

theorem c122839_2 : rowSum f122839 534 245 = 602188850 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 122839) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover122839 (by decide)
  decide +kernel

theorem c122839_3 : rowSum f122839 779 177 = 789573712 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 122839) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover122839 (by decide)
  decide +kernel

theorem c122839_4 : rowSum f122839 956 68 = 229699898 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 122839) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover122839 (by decide)
  decide +kernel

theorem sum122839 : rowSum f122839 0 1024 = 2559504258 :=
  rowSum_append (F := f122839) (lo := 0) (n := 292) (m := 732) (A := 211812174) (B := 2347692084) c122839_0 (rowSum_append (F := f122839) (lo := 292) (n := 242) (m := 490) (A := 726229624) (B := 1621462460) c122839_1 (rowSum_append (F := f122839) (lo := 534) (n := 245) (m := 245) (A := 602188850) (B := 1019273610) c122839_2 (rowSum_append (F := f122839) (lo := 779) (n := 177) (m := 68) (A := 789573712) (B := 229699898) c122839_3 (c122839_4))))

theorem h122839 : P.leaf 36 122839 = 2559504258 :=
  leaf_weighted (k := 26) (d := 10) (H := 122839) (keep := keep9) (twice := twice9) rows (by decide) (by decide) bal9 (invRow9 (H := 122839) (by decide) (by decide +kernel)) sum122839

def seg : List (ℕ × ℕ) := [(122836, 360), (122837, 720), (122839, 360)]

theorem segOK : checkSeg 20 perms 122836 122841 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 122836 122841 1440 1882840136400 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 1882840136400)
    (SegSum.cons (w := 360) h122836 (SegSum.cons (w := 720) h122837 (SegSum.cons (w := 360) h122839 (show SegSum (P.leaf 36) [] 0 from rfl)))) (by decide)

end RACert.S6N0.C0.S86
