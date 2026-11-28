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

namespace RACert.S6N0.C0.S93

open RACert RACert.Problem

theorem cover243711 : P.CoversSplit 26 10 243711 0xfffffffffffffffffffffffffffffafaffffffffffffccccffffaaaaffcc8888ffffffffffffffffffffaaaaffffaaaaffffffffffffccccffffaaaaffcc8888fffffffffffffffffffffffffffffafaffffffffccccccccffffaaaacccc8888ffffffffffffffffffffaaaaffffaaaaffffffffccccccccffffaaaacccc8888 :=
  coversSplit check rows (by decide) (by decide) (xs := [873, 930, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f243711 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 26 (249560064 + i)

theorem c243711_0 : rowSum f243711 0 241 = 1068857872 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 243711) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover243711 (by decide)
  decide +kernel

theorem c243711_1 : rowSum f243711 241 148 = 1799394924 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 243711) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover243711 (by decide)
  decide +kernel

theorem c243711_2 : rowSum f243711 389 98 = 2507536434 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 243711) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover243711 (by decide)
  decide +kernel

theorem c243711_3 : rowSum f243711 487 399 = 2778279733 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 243711) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover243711 (by decide)
  decide +kernel

theorem c243711_4 : rowSum f243711 886 138 = 1740689580 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 243711) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover243711 (by decide)
  decide +kernel

theorem sum243711 : rowSum f243711 0 1024 = 9894758543 :=
  rowSum_append (F := f243711) (lo := 0) (n := 241) (m := 783) (A := 1068857872) (B := 8825900671) c243711_0 (rowSum_append (F := f243711) (lo := 241) (n := 148) (m := 635) (A := 1799394924) (B := 7026505747) c243711_1 (rowSum_append (F := f243711) (lo := 389) (n := 98) (m := 537) (A := 2507536434) (B := 4518969313) c243711_2 (rowSum_append (F := f243711) (lo := 487) (n := 399) (m := 138) (A := 2778279733) (B := 1740689580) c243711_3 (c243711_4))))

theorem h243711 : P.leaf 36 243711 = 9894758543 :=
  leaf_weighted (k := 26) (d := 10) (H := 243711) (keep := keep2) (twice := twice2) rows (by decide) (by decide) (bal2) (invRow2 (H := 243711) (by decide) (by decide +kernel)) sum243711

theorem cover245630 : P.CoversSplit 26 10 245630 0xfffffffffffffffffffffffffffffafaffffffffffffffccffffaaaaff00aa00ffffffffffffffffffffaaaaffffaaaaffffffffffffffccffffaaaaff00aa00fffffffffffffffffffffffffffffafaffffffffff00ff00ffffaaaaff00aa00ffffffffffffffffffffaaaaffffaaaaffffffffff00ff00ffffaaaaff00aa00 :=
  coversSplit check rows (by decide) (by decide) (xs := [579, 930, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f245630 (i : ℕ) := rowWeight keep8 twice8 i * P.leaf 26 (251525120 + i)

theorem c245630_0 : rowSum f245630 0 241 = 256236192 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 245630) (keep := keep8) (twice := twice8) check rows elimOK (by decide) (by decide) cover245630 (by decide)
  decide +kernel

theorem c245630_1 : rowSum f245630 241 148 = 911084386 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 245630) (keep := keep8) (twice := twice8) check rows elimOK (by decide) (by decide) cover245630 (by decide)
  decide +kernel

theorem c245630_2 : rowSum f245630 389 98 = 1760402476 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 245630) (keep := keep8) (twice := twice8) check rows elimOK (by decide) (by decide) cover245630 (by decide)
  decide +kernel

theorem c245630_3 : rowSum f245630 487 399 = 2088871370 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 245630) (keep := keep8) (twice := twice8) check rows elimOK (by decide) (by decide) cover245630 (by decide)
  decide +kernel

theorem c245630_4 : rowSum f245630 886 138 = 1403483454 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 245630) (keep := keep8) (twice := twice8) check rows elimOK (by decide) (by decide) cover245630 (by decide)
  decide +kernel

theorem sum245630 : rowSum f245630 0 1024 = 6420077878 :=
  rowSum_append (F := f245630) (lo := 0) (n := 241) (m := 783) (A := 256236192) (B := 6163841686) c245630_0 (rowSum_append (F := f245630) (lo := 241) (n := 148) (m := 635) (A := 911084386) (B := 5252757300) c245630_1 (rowSum_append (F := f245630) (lo := 389) (n := 98) (m := 537) (A := 1760402476) (B := 3492354824) c245630_2 (rowSum_append (F := f245630) (lo := 487) (n := 399) (m := 138) (A := 2088871370) (B := 1403483454) c245630_3 (c245630_4))))

theorem h245630 : P.leaf 36 245630 = 6420077878 :=
  leaf_weighted (k := 26) (d := 10) (H := 245630) (keep := keep8) (twice := twice8) rows (by decide) (by decide) (bal8) (invRow8 (H := 245630) (by decide) (by decide +kernel)) sum245630

theorem cover245631 : P.CoversSplit 26 10 245631 0xfffffffffffffffffffffffffffffafaffffffffffffffccffffaaaaff00aa00ffffffffffffffffffffaaaaffffaaaaffffffffffffffccffffaaaaff00aa00fffffffffffffffffffffffffffffafaffffffffff00ff00ffffaaaaff00aa00ffffffffffffffffffffaaaaffffaaaaffffffffff00ff00ffffaaaaff00aa00 :=
  coversSplit check rows (by decide) (by decide) (xs := [579, 930, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f245631 (i : ℕ) := rowWeight keep8 twice8 i * P.leaf 26 (251526144 + i)

theorem c245631_0 : rowSum f245631 0 241 = 933417976 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 245631) (keep := keep8) (twice := twice8) check rows elimOK (by decide) (by decide) cover245631 (by decide)
  decide +kernel

theorem c245631_1 : rowSum f245631 241 148 = 1722630542 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 245631) (keep := keep8) (twice := twice8) check rows elimOK (by decide) (by decide) cover245631 (by decide)
  decide +kernel

theorem c245631_2 : rowSum f245631 389 98 = 2126752640 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 245631) (keep := keep8) (twice := twice8) check rows elimOK (by decide) (by decide) cover245631 (by decide)
  decide +kernel

theorem c245631_3 : rowSum f245631 487 399 = 2668692319 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 245631) (keep := keep8) (twice := twice8) check rows elimOK (by decide) (by decide) cover245631 (by decide)
  decide +kernel

theorem c245631_4 : rowSum f245631 886 138 = 1610413467 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 245631) (keep := keep8) (twice := twice8) check rows elimOK (by decide) (by decide) cover245631 (by decide)
  decide +kernel

theorem sum245631 : rowSum f245631 0 1024 = 9061906944 :=
  rowSum_append (F := f245631) (lo := 0) (n := 241) (m := 783) (A := 933417976) (B := 8128488968) c245631_0 (rowSum_append (F := f245631) (lo := 241) (n := 148) (m := 635) (A := 1722630542) (B := 6405858426) c245631_1 (rowSum_append (F := f245631) (lo := 389) (n := 98) (m := 537) (A := 2126752640) (B := 4279105786) c245631_2 (rowSum_append (F := f245631) (lo := 487) (n := 399) (m := 138) (A := 2668692319) (B := 1610413467) c245631_3 (c245631_4))))

theorem h245631 : P.leaf 36 245631 = 9061906944 :=
  leaf_weighted (k := 26) (d := 10) (H := 245631) (keep := keep8) (twice := twice8) rows (by decide) (by decide) (bal8) (invRow8 (H := 245631) (by decide) (by decide +kernel)) sum245631

theorem cover385005 : P.CoversSplit 26 10 385005 0xfffffffffffffffffffffffffffffffffffffffffffffffffafafafac8c8c8c8fffffffffffffffffafaf0f0fafaf0f0fffffffffffffffffafaf0f0c8c8c0c0ffffffffffffffffffffffffffffffffffffffffcc00cc00fafafafac800c800fffffffffffffffffafaf0f0fafaf0f0ffffffffcc00cc00fafaf0f0c800c000 :=
  coversSplit check rows (by decide) (by decide) (xs := [922, 1273, 1658, 1665]) (by decide +kernel)

noncomputable def f385005 (i : ℕ) := rowWeight keep4 twice4 i * P.leaf 26 (394245120 + i)

theorem c385005_0 : rowSum f385005 0 287 = 399693970 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 385005) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover385005 (by decide)
  decide +kernel

theorem c385005_1 : rowSum f385005 287 128 = 502804736 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 385005) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover385005 (by decide)
  decide +kernel

theorem c385005_2 : rowSum f385005 415 96 = 1282585108 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 385005) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover385005 (by decide)
  decide +kernel

theorem c385005_3 : rowSum f385005 511 460 = 850703184 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 385005) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover385005 (by decide)
  decide +kernel

theorem c385005_4 : rowSum f385005 971 53 = 622429475 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 385005) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover385005 (by decide)
  decide +kernel

theorem sum385005 : rowSum f385005 0 1024 = 3658216473 :=
  rowSum_append (F := f385005) (lo := 0) (n := 287) (m := 737) (A := 399693970) (B := 3258522503) c385005_0 (rowSum_append (F := f385005) (lo := 287) (n := 128) (m := 609) (A := 502804736) (B := 2755717767) c385005_1 (rowSum_append (F := f385005) (lo := 415) (n := 96) (m := 513) (A := 1282585108) (B := 1473132659) c385005_2 (rowSum_append (F := f385005) (lo := 511) (n := 460) (m := 53) (A := 850703184) (B := 622429475) c385005_3 (c385005_4))))

theorem h385005 : P.leaf 36 385005 = 3658216473 :=
  leaf_weighted (k := 26) (d := 10) (H := 385005) (keep := keep4) (twice := twice4) rows (by decide) (by decide) (bal4) (invRow4 (H := 385005) (by decide) (by decide +kernel)) sum385005

theorem h245687 : P.leaf 36 245687 = 3658216473 :=
  orient6 (v := 385005) (by decide) (by decide +kernel) h385005

def seg : List (ℕ × ℕ) := [(243711, 360), (245630, 120), (245631, 120), (245687, 72)]

theorem segOK : checkSeg 20 perms 243711 245691 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 243711 245691 672 5683342840176 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 5683342840176)
    (SegSum.cons (w := 360) h243711 (SegSum.cons (w := 120) h245630 (SegSum.cons (w := 120) h245631 (SegSum.cons (w := 72) h245687 (show SegSum (P.leaf 36) [] 0 from rfl))))) (by decide)

end RACert.S6N0.C0.S93
