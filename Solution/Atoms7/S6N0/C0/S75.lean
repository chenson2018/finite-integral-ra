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

namespace RACert.S6N0.C0.S75

open RACert RACert.Problem

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
  leaf_weighted (k := 26) (d := 10) (H := 122839) (keep := keep9) (twice := twice9) rows (by decide) (by decide) (bal9) (invRow9 (H := 122839) (by decide) (by decide +kernel)) sum122839

theorem cover831325 : P.CoversSplit 26 10 831325 0xfffffffffffffffffffffafa00000000ffff0000ffcc0000ffff000000000000ffffffffffffffffffffaaaa00000000ffff0000ffcc0000ffff000000000000fffffffffffffffffffffafa00000000ffff0000ff000000ffff000000000000ffffffffffffffffffffaaaa00000000ffff0000ff000000ffff000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 579, 881, 930, 1265, 1266, 1272, 1273]) (by decide +kernel)

noncomputable def f831325 (i : ℕ) := rowWeight keep8 twice8 i * P.leaf 26 (851276800 + i)

theorem c831325_0 : rowSum f831325 0 370 = 263172553 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 831325) (keep := keep8) (twice := twice8) check rows elimOK (by decide) (by decide) cover831325 (by decide)
  decide +kernel

theorem c831325_1 : rowSum f831325 370 132 = 372867874 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 831325) (keep := keep8) (twice := twice8) check rows elimOK (by decide) (by decide) cover831325 (by decide)
  decide +kernel

theorem c831325_2 : rowSum f831325 502 522 = 464850108 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 831325) (keep := keep8) (twice := twice8) check rows elimOK (by decide) (by decide) cover831325 (by decide)
  decide +kernel

theorem sum831325 : rowSum f831325 0 1024 = 1100890535 :=
  rowSum_append (F := f831325) (lo := 0) (n := 370) (m := 654) (A := 263172553) (B := 837717982) c831325_0 (rowSum_append (F := f831325) (lo := 370) (n := 132) (m := 522) (A := 372867874) (B := 464850108) c831325_1 (c831325_2))

theorem h831325 : P.leaf 36 831325 = 1100890535 :=
  leaf_weighted (k := 26) (d := 10) (H := 831325) (keep := keep8) (twice := twice8) rows (by decide) (by decide) (bal8) (invRow8 (H := 831325) (by decide) (by decide +kernel)) sum831325

theorem h122841 : P.leaf 36 122841 = 1100890535 :=
  orient84 (v := 831325) (by decide) (by decide +kernel) h831325

theorem cover323550 : P.CoversSplit 26 10 323550 0xfffffffffffffffffffffafafffffafaffffffffffccffccfac8fac8fac8fac8fffffffffffffffffafaaaaafafaaaaaffffffffffccffccfac8aa88fac8aa88fffffffffffffffffffffafafffffafaffccffccff00ff00fac8fac8fa00fa00fffffffffffffffffafaaaaafafaaaaaffccffccff00ff00fac8aa88fa00aa00 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 881, 1265, 1273, 1658, 1665]) (by decide +kernel)

noncomputable def f323550 (i : ℕ) := rowWeight keep8 twice8 i * P.leaf 26 (331315200 + i)

theorem c323550_0 : rowSum f323550 0 271 = 355522464 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 323550) (keep := keep8) (twice := twice8) check rows elimOK (by decide) (by decide) cover323550 (by decide)
  decide +kernel

theorem c323550_1 : rowSum f323550 271 150 = 437056268 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 323550) (keep := keep8) (twice := twice8) check rows elimOK (by decide) (by decide) cover323550 (by decide)
  decide +kernel

theorem c323550_2 : rowSum f323550 421 369 = 670676214 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 323550) (keep := keep8) (twice := twice8) check rows elimOK (by decide) (by decide) cover323550 (by decide)
  decide +kernel

theorem c323550_3 : rowSum f323550 790 218 = 607755648 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 323550) (keep := keep8) (twice := twice8) check rows elimOK (by decide) (by decide) cover323550 (by decide)
  decide +kernel

theorem c323550_4 : rowSum f323550 1008 16 = 139531560 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 323550) (keep := keep8) (twice := twice8) check rows elimOK (by decide) (by decide) cover323550 (by decide)
  decide +kernel

theorem sum323550 : rowSum f323550 0 1024 = 2210542154 :=
  rowSum_append (F := f323550) (lo := 0) (n := 271) (m := 753) (A := 355522464) (B := 1855019690) c323550_0 (rowSum_append (F := f323550) (lo := 271) (n := 150) (m := 603) (A := 437056268) (B := 1417963422) c323550_1 (rowSum_append (F := f323550) (lo := 421) (n := 369) (m := 234) (A := 670676214) (B := 747287208) c323550_2 (rowSum_append (F := f323550) (lo := 790) (n := 218) (m := 16) (A := 607755648) (B := 139531560) c323550_3 (c323550_4))))

theorem h323550 : P.leaf 36 323550 = 2210542154 :=
  leaf_weighted (k := 26) (d := 10) (H := 323550) (keep := keep8) (twice := twice8) rows (by decide) (by decide) (bal8) (invRow8 (H := 323550) (by decide) (by decide +kernel)) sum323550

theorem h122843 : P.leaf 36 122843 = 2210542154 :=
  orient80 (v := 323550) (by decide) (by decide +kernel) h323550

theorem cover122844 : P.CoversSplit 26 10 122844 0xfffffffffffffafafffffffffffffafafffffffffffffa00fafafafac8c8c800fffffafafffffafafafaa0a0fafaa0a0fffffafafffffa00fafaa0a0c8c88000fffffffffffffafafffffffffffffafaffffffffcc00c800fafafafac800c800fffffafafffffafafafaa0a0fafaa0a0fffffafacc00c800fafaa0a0c8008000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 922, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f122844 (i : ℕ) := rowWeight keep9 twice9 i * P.leaf 26 (125792256 + i)

theorem c122844_0 : rowSum f122844 0 309 = 47821408 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 122844) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover122844 (by decide)
  decide +kernel

theorem c122844_1 : rowSum f122844 309 258 = 182546393 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 122844) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover122844 (by decide)
  decide +kernel

theorem c122844_2 : rowSum f122844 567 258 = 352690674 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 122844) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover122844 (by decide)
  decide +kernel

theorem c122844_3 : rowSum f122844 825 199 = 473492624 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 122844) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover122844 (by decide)
  decide +kernel

theorem sum122844 : rowSum f122844 0 1024 = 1056551099 :=
  rowSum_append (F := f122844) (lo := 0) (n := 309) (m := 715) (A := 47821408) (B := 1008729691) c122844_0 (rowSum_append (F := f122844) (lo := 309) (n := 258) (m := 457) (A := 182546393) (B := 826183298) c122844_1 (rowSum_append (F := f122844) (lo := 567) (n := 258) (m := 199) (A := 352690674) (B := 473492624) c122844_2 (c122844_3)))

theorem h122844 : P.leaf 36 122844 = 1056551099 :=
  leaf_weighted (k := 26) (d := 10) (H := 122844) (keep := keep9) (twice := twice9) rows (by decide) (by decide) (bal9) (invRow9 (H := 122844) (by decide) (by decide +kernel)) sum122844

def seg : List (ℕ × ℕ) := [(122839, 360), (122841, 360), (122843, 360), (122844, 360)]

theorem segOK : checkSeg 20 perms 122839 122845 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 122839 122845 1440 2493895696560 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 2493895696560)
    (SegSum.cons (w := 360) h122839 (SegSum.cons (w := 360) h122841 (SegSum.cons (w := 360) h122843 (SegSum.cons (w := 360) h122844 (show SegSum (P.leaf 36) [] 0 from rfl))))) (by decide)

end RACert.S6N0.C0.S75
