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

theorem cover120831 : P.CoversSplit 26 10 120831 0xfffffffffffffafafffffffffffffafaffffffffffffc8c8fafafafac8c8c8c8fffffafafffffafafafafafafafafafafffffafaffffc8c8fafafafac8c8c8c8fffffffffffffafafffffffffffffafaffffffffccccc8c8fafafafac8c8c8c8fffffafafffffafafafafafafafafafafffffafaccccc8c8fafafafac8c8c8c8 :=
  coversSplit check rows (by decide) (by decide) (xs := [873, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f120831 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 26 (123730944 + i)

theorem c120831_0 : rowSum f120831 0 240 = 876901094 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 120831) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover120831 (by decide)
  decide +kernel

theorem c120831_1 : rowSum f120831 240 180 = 1138034609 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 120831) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover120831 (by decide)
  decide +kernel

theorem c120831_2 : rowSum f120831 420 189 = 1293709189 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 120831) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover120831 (by decide)
  decide +kernel

theorem c120831_3 : rowSum f120831 609 213 = 1688195784 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 120831) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover120831 (by decide)
  decide +kernel

theorem c120831_4 : rowSum f120831 822 194 = 1758749927 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 120831) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover120831 (by decide)
  decide +kernel

theorem c120831_5 : rowSum f120831 1016 8 = 156775660 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 120831) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover120831 (by decide)
  decide +kernel

theorem sum120831 : rowSum f120831 0 1024 = 6912366263 :=
  rowSum_append (F := f120831) (lo := 0) (n := 240) (m := 784) (A := 876901094) (B := 6035465169) c120831_0 (rowSum_append (F := f120831) (lo := 240) (n := 180) (m := 604) (A := 1138034609) (B := 4897430560) c120831_1 (rowSum_append (F := f120831) (lo := 420) (n := 189) (m := 415) (A := 1293709189) (B := 3603721371) c120831_2 (rowSum_append (F := f120831) (lo := 609) (n := 213) (m := 202) (A := 1688195784) (B := 1915525587) c120831_3 (rowSum_append (F := f120831) (lo := 822) (n := 194) (m := 8) (A := 1758749927) (B := 156775660) c120831_4 (c120831_5)))))

theorem h120831 : P.leaf 36 120831 = 6912366263 :=
  leaf_weighted (k := 26) (d := 10) (H := 120831) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 120831) (by decide) (by decide +kernel)) sum120831

theorem cover122742 : P.CoversSplit 26 10 122742 0xfffffffffffffafa0000000000000000fffffffffffffac805050505000000000505000005050000050500000505000005050000050500000505000000000000fffffffffffffafa0000000000000000ffccffcc0000000005040504000000000505000005050000050500000505000005040000000000000504000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 579, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f122742 (i : ℕ) := rowWeight keep7 twice7 i * P.leaf 26 (125687808 + i)

theorem c122742_0 : rowSum f122742 0 818 = 121729240 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 122742) (keep := keep7) (twice := twice7) check rows elimOK (by decide) (by decide) cover122742 (by decide)
  decide +kernel

theorem c122742_1 : rowSum f122742 818 206 = 179093628 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 122742) (keep := keep7) (twice := twice7) check rows elimOK (by decide) (by decide) cover122742 (by decide)
  decide +kernel

theorem sum122742 : rowSum f122742 0 1024 = 300822868 :=
  rowSum_append (F := f122742) (lo := 0) (n := 818) (m := 206) (A := 121729240) (B := 179093628) c122742_0 (c122742_1)

theorem h122742 : P.leaf 36 122742 = 300822868 :=
  leaf_weighted (k := 26) (d := 10) (H := 122742) (keep := keep7) (twice := twice7) rows (by decide) (by decide) bal7 (invRow7 (H := 122742) (by decide) (by decide +kernel)) sum122742

theorem cover122743 : P.CoversSplit 26 10 122743 0xfffffffffffffafa0000000000000000fffffffffffffac805050505000000000505000005050000050500000505000005050000050500000505000000000000fffffffffffffafa0000000000000000ffffffff0000000005050505000000000505000005050000050500000505000005050000000000000505000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 579, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f122743 (i : ℕ) := rowWeight keep7 twice7 i * P.leaf 26 (125688832 + i)

theorem c122743_0 : rowSum f122743 0 720 = 238361776 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 122743) (keep := keep7) (twice := twice7) check rows elimOK (by decide) (by decide) cover122743 (by decide)
  decide +kernel

theorem c122743_1 : rowSum f122743 720 304 = 337315074 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 122743) (keep := keep7) (twice := twice7) check rows elimOK (by decide) (by decide) cover122743 (by decide)
  decide +kernel

theorem sum122743 : rowSum f122743 0 1024 = 575676850 :=
  rowSum_append (F := f122743) (lo := 0) (n := 720) (m := 304) (A := 238361776) (B := 337315074) c122743_0 (c122743_1)

theorem h122743 : P.leaf 36 122743 = 575676850 :=
  leaf_weighted (k := 26) (d := 10) (H := 122743) (keep := keep7) (twice := twice7) rows (by decide) (by decide) bal7 (invRow7 (H := 122743) (by decide) (by decide +kernel)) sum122743

theorem cover122750 : P.CoversSplit 26 10 122750 0xfffffffffffffafa0000000000000000fffffffffffffac805050505000000000505000005050000050500000505000005050000050500000505000000000000fffffffffffffafa0000000000000000ffffffff0000000005050505000000000505000005050000050500000505000005050000000000000505000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [579, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f122750 (i : ℕ) := rowWeight keep7 twice7 i * P.leaf 26 (125696000 + i)

theorem c122750_0 : rowSum f122750 0 720 = 198208813 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 122750) (keep := keep7) (twice := twice7) check rows elimOK (by decide) (by decide) cover122750 (by decide)
  decide +kernel

theorem c122750_1 : rowSum f122750 720 304 = 281470490 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 122750) (keep := keep7) (twice := twice7) check rows elimOK (by decide) (by decide) cover122750 (by decide)
  decide +kernel

theorem sum122750 : rowSum f122750 0 1024 = 479679303 :=
  rowSum_append (F := f122750) (lo := 0) (n := 720) (m := 304) (A := 198208813) (B := 281470490) c122750_0 (c122750_1)

theorem h122750 : P.leaf 36 122750 = 479679303 :=
  leaf_weighted (k := 26) (d := 10) (H := 122750) (keep := keep7) (twice := twice7) rows (by decide) (by decide) bal7 (invRow7 (H := 122750) (by decide) (by decide +kernel)) sum122750

theorem cover122751 : P.CoversSplit 26 10 122751 0xfffffffffffffafa0000000000000000fffffffffffffac805050505000000000505000005050000050500000505000005050000050500000505000000000000fffffffffffffafa0000000000000000ffffffff0000000005050505000000000505000005050000050500000505000005050000000000000505000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [579, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f122751 (i : ℕ) := rowWeight keep7 twice7 i * P.leaf 26 (125697024 + i)

theorem c122751_0 : rowSum f122751 0 720 = 256250864 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 122751) (keep := keep7) (twice := twice7) check rows elimOK (by decide) (by decide) cover122751 (by decide)
  decide +kernel

theorem c122751_1 : rowSum f122751 720 304 = 345366634 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 122751) (keep := keep7) (twice := twice7) check rows elimOK (by decide) (by decide) cover122751 (by decide)
  decide +kernel

theorem sum122751 : rowSum f122751 0 1024 = 601617498 :=
  rowSum_append (F := f122751) (lo := 0) (n := 720) (m := 304) (A := 256250864) (B := 345366634) c122751_0 (c122751_1)

theorem h122751 : P.leaf 36 122751 = 601617498 :=
  leaf_weighted (k := 26) (d := 10) (H := 122751) (keep := keep7) (twice := twice7) rows (by decide) (by decide) bal7 (invRow7 (H := 122751) (by decide) (by decide +kernel)) sum122751

theorem cover122835 : P.CoversSplit 26 10 122835 0xfffffffffffffafafffffafafffffafaffffffffffccfa00fafafafac8c8c800fffffafafffffafafafafafafafafafafffffafaffccfa00fafafafac8c8c800fffffffffffffafafffffafafffffafaffffffffcc00c800fafafafac800c800fffffafafffffafafafafafafafafafafffffafacc00c800fafafafac800c800 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f122835 (i : ℕ) := rowWeight keep9 twice9 i * P.leaf 26 (125783040 + i)

theorem c122835_0 : rowSum f122835 0 292 = 61796226 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 122835) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover122835 (by decide)
  decide +kernel

theorem c122835_1 : rowSum f122835 292 250 = 314775734 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 122835) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover122835 (by decide)
  decide +kernel

theorem c122835_2 : rowSum f122835 542 256 = 315904384 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 122835) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover122835 (by decide)
  decide +kernel

theorem c122835_3 : rowSum f122835 798 221 = 440770604 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 122835) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover122835 (by decide)
  decide +kernel

theorem c122835_4 : rowSum f122835 1019 5 = 28004704 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 122835) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover122835 (by decide)
  decide +kernel

theorem sum122835 : rowSum f122835 0 1024 = 1161251652 :=
  rowSum_append (F := f122835) (lo := 0) (n := 292) (m := 732) (A := 61796226) (B := 1099455426) c122835_0 (rowSum_append (F := f122835) (lo := 292) (n := 250) (m := 482) (A := 314775734) (B := 784679692) c122835_1 (rowSum_append (F := f122835) (lo := 542) (n := 256) (m := 226) (A := 315904384) (B := 468775308) c122835_2 (rowSum_append (F := f122835) (lo := 798) (n := 221) (m := 5) (A := 440770604) (B := 28004704) c122835_3 (c122835_4))))

theorem h122835 : P.leaf 36 122835 = 1161251652 :=
  leaf_weighted (k := 26) (d := 10) (H := 122835) (keep := keep9) (twice := twice9) rows (by decide) (by decide) bal9 (invRow9 (H := 122835) (by decide) (by decide +kernel)) sum122835

def seg : List (ℕ × ℕ) := [(120831, 360), (122742, 180), (122743, 180), (122750, 180), (122751, 180), (122835, 360)]

theorem segOK : checkSeg 20 perms 120831 122836 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 120831 122836 1440 3258905822820 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 3258905822820)
    (SegSum.cons (w := 360) h120831 (SegSum.cons (w := 180) h122742 (SegSum.cons (w := 180) h122743 (SegSum.cons (w := 180) h122750 (SegSum.cons (w := 180) h122751 (SegSum.cons (w := 360) h122835 (show SegSum (P.leaf 36) [] 0 from rfl))))))) (by decide)

end RACert.S6N0.C0.S85
