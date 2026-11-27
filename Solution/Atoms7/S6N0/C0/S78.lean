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

namespace RACert.S6N0.C0.S78

open RACert RACert.Problem

theorem cover98287 : P.CoversSplit 26 10 98287 0xfffffffffffffafafffffffafffffafafffffffffffcfac8fafafafafac8fac80000000000000000000000000000000000000000000000000000000000000000fffffffffffffafafffffffafffffafaffffffffff00fa00fafafafafa00fa000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [972, 979, 1266, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f98287 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 26 (100645888 + i)

theorem c98287_0 : rowSum f98287 0 438 = 621841949 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 98287) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover98287 (by decide)
  decide +kernel

theorem c98287_1 : rowSum f98287 438 440 = 1283197102 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 98287) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover98287 (by decide)
  decide +kernel

theorem c98287_2 : rowSum f98287 878 146 = 1194790634 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 98287) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover98287 (by decide)
  decide +kernel

theorem sum98287 : rowSum f98287 0 1024 = 3099829685 :=
  rowSum_append (F := f98287) (lo := 0) (n := 438) (m := 586) (A := 621841949) (B := 2477987736) c98287_0 (rowSum_append (F := f98287) (lo := 438) (n := 440) (m := 146) (A := 1283197102) (B := 1194790634) c98287_1 (c98287_2))

theorem h98287 : P.leaf 36 98287 = 3099829685 :=
  leaf_weighted (k := 26) (d := 10) (H := 98287) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 98287) (by decide) (by decide +kernel)) sum98287

theorem cover98291 : P.CoversSplit 26 10 98291 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00800000000000000000000fa000000fa0000000000000000000000fa000000fa080000000000000000000000000000000000000000f0c0f0c000000000f0c0f0c8000000000000000000000000000000000000000000000000000000000000fac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 972, 979]) (by decide +kernel)

noncomputable def f98291 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 26 (100649984 + i)

theorem c98291_0 : rowSum f98291 0 1024 = 266379128 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 98291) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover98291 (by decide)
  decide +kernel

theorem sum98291 : rowSum f98291 0 1024 = 266379128 :=
  c98291_0

theorem h98291 : P.leaf 36 98291 = 266379128 :=
  leaf_weighted (k := 26) (d := 10) (H := 98291) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 98291) (by decide) (by decide +kernel)) sum98291

theorem cover98292 : P.CoversSplit 26 10 98292 0xff00ff00ff00fa00ff00ff00ff00fa00ff00ff00ff03fa00fa00fa00fa00fa00ff00fa00ff00fa00fa00f000fa00f000ff00fa00ff03fa00fa00f000fa00f00000000000000000000000000000000000000000003300320000000000320032000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 874, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f98292 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 26 (100651008 + i)

theorem c98292_0 : rowSum f98292 0 848 = 112850551 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 98292) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover98292 (by decide)
  decide +kernel

theorem c98292_1 : rowSum f98292 848 176 = 144298794 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 98292) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover98292 (by decide)
  decide +kernel

theorem sum98292 : rowSum f98292 0 1024 = 257149345 :=
  rowSum_append (F := f98292) (lo := 0) (n := 848) (m := 176) (A := 112850551) (B := 144298794) c98292_0 (c98292_1)

theorem h98292 : P.leaf 36 98292 = 257149345 :=
  leaf_weighted (k := 26) (d := 10) (H := 98292) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 98292) (by decide) (by decide +kernel)) sum98292

theorem cover98293 : P.CoversSplit 26 10 98293 0xff00ff00ff00fa00ff00ff00ff00fa00ff00ff00ff03fa00fa00fa00fa00fa00ff00fa00ff00fa00fa00f000fa00f000ff00fa00ff03fa00fa00f000fa00f00000000000000000000000000000000000000000003300320000000000320032000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c98293_0 : P.sumLeaves 26 100652032 735 = 168198806 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98293) (lo := 0) (len := 735) (W := 168198806) check rows elimOK (by decide) (by decide) cover98293 (by decide)
  decide +kernel

theorem c98293_1 : P.sumLeaves 26 100652767 220 = 410059559 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98293) (lo := 735) (len := 220) (W := 410059559) check rows elimOK (by decide) (by decide) cover98293 (by decide)
  decide +kernel

theorem c98293_2 : P.sumLeaves 26 100652987 69 = 300133008 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98293) (lo := 955) (len := 69) (W := 300133008) check rows elimOK (by decide) (by decide) cover98293 (by decide)
  decide +kernel

theorem h98293 : P.leaf 36 98293 = 878391373 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(735, 168198806), (220, 410059559), (69, 300133008)]) (.cons c98293_0 (.cons c98293_1 (.cons c98293_2 (.nil)))) (by decide) (by decide))

theorem cover98295 : P.CoversSplit 26 10 98295 0xff00ff00ff00fa00ff00ff00ff00fa00ff00ff00ff03fa00fa00fa00fa00fa00ff00fa00ff00fa00fa00f000fa00f000ff00fa00ff03fa00fa00f000fa00f00000000000000000000000000000000000000000003300320000000000320032000000000000000000000000000000000000000000330032000000000032003000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f98295 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 26 (100654080 + i)

theorem c98295_0 : rowSum f98295 0 813 = 496247032 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 98295) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover98295 (by decide)
  decide +kernel

theorem c98295_1 : rowSum f98295 813 211 = 880547995 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 98295) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover98295 (by decide)
  decide +kernel

theorem sum98295 : rowSum f98295 0 1024 = 1376795027 :=
  rowSum_append (F := f98295) (lo := 0) (n := 813) (m := 211) (A := 496247032) (B := 880547995) c98295_0 (c98295_1)

theorem h98295 : P.leaf 36 98295 = 1376795027 :=
  leaf_weighted (k := 26) (d := 10) (H := 98295) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 98295) (by decide) (by decide +kernel)) sum98295

theorem cover98296 : P.CoversSplit 26 10 98296 0xf0f0f0f0f0f0f0f0f0f0f0f5f0f0f0f0f0f0f0f0f0f0f0c0f0f0f0f0f0c0f0c00000000000000000000050500000505000000000000000000000505000005040f0f0f0f0f0f0f0f0f0f0f0f5f0f0f0f0f0f0f0f0f000f000f0f0f0f0f000f0000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 874, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f98296 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 26 (100655104 + i)

theorem c98296_0 : rowSum f98296 0 807 = 93597082 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 98296) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover98296 (by decide)
  decide +kernel

theorem c98296_1 : rowSum f98296 807 217 = 199085391 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 98296) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover98296 (by decide)
  decide +kernel

theorem sum98296 : rowSum f98296 0 1024 = 292682473 :=
  rowSum_append (F := f98296) (lo := 0) (n := 807) (m := 217) (A := 93597082) (B := 199085391) c98296_0 (c98296_1)

theorem h98296 : P.leaf 36 98296 = 292682473 :=
  leaf_weighted (k := 26) (d := 10) (H := 98296) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 98296) (by decide) (by decide +kernel)) sum98296

theorem cover98297 : P.CoversSplit 26 10 98297 0xf0f0f0f0f0f0f0f0f0f0f0f5f0f0f0f0f0f0f0f0f0f0f0c0f0f0f0f0f0c0f0c00000000000000000000050500000505000000000000000000000505000005040f0f0f0f0f0f0f0f0f0f0f0f5f0f0f0f0f0f0f0f0f000f000f0f0f0f0f000f0000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c98297_0 : P.sumLeaves 26 100656128 478 = 145318368 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98297) (lo := 0) (len := 478) (W := 145318368) check rows elimOK (by decide) (by decide) cover98297 (by decide)
  decide +kernel

theorem c98297_1 : P.sumLeaves 26 100656606 431 = 276486063 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98297) (lo := 478) (len := 431) (W := 276486063) check rows elimOK (by decide) (by decide) cover98297 (by decide)
  decide +kernel

theorem c98297_2 : P.sumLeaves 26 100657037 115 = 449897586 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98297) (lo := 909) (len := 115) (W := 449897586) check rows elimOK (by decide) (by decide) cover98297 (by decide)
  decide +kernel

theorem h98297 : P.leaf 36 98297 = 871702017 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(478, 145318368), (431, 276486063), (115, 449897586)]) (.cons c98297_0 (.cons c98297_1 (.cons c98297_2 (.nil)))) (by decide) (by decide))

theorem cover98299 : P.CoversSplit 26 10 98299 0xf0f0f0f0f0f0f0f0f0f0f0f5f0f0f0f0f0f0f0f0f0f0f0c0f0f0f0f0f0c0f0c00000000000000000000050500000505000000000000000000000505000005040f0f0f0f0f0f0f0f0f0f0f0f5f0f0f0f0f0f0f0f0f000f000f0f0f0f0f000f0000000000000000000000050500000505000000000000000000000505000005000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f98299 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 26 (100658176 + i)

theorem c98299_0 : rowSum f98299 0 783 = 344118737 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 98299) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover98299 (by decide)
  decide +kernel

theorem c98299_1 : rowSum f98299 783 241 = 1030158574 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 98299) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover98299 (by decide)
  decide +kernel

theorem sum98299 : rowSum f98299 0 1024 = 1374277311 :=
  rowSum_append (F := f98299) (lo := 0) (n := 783) (m := 241) (A := 344118737) (B := 1030158574) c98299_0 (c98299_1)

theorem h98299 : P.leaf 36 98299 = 1374277311 :=
  leaf_weighted (k := 26) (d := 10) (H := 98299) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 98299) (by decide) (by decide +kernel)) sum98299

def seg : List (ℕ × ℕ) := [(98287, 360), (98291, 360), (98292, 360), (98293, 720), (98295, 360), (98296, 360), (98297, 720), (98299, 360)]

theorem segOK : checkSeg 20 perms 98287 98300 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 98287 98300 3600 3660227909640 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 3660227909640)
    (SegSum.cons (w := 360) h98287 (SegSum.cons (w := 360) h98291 (SegSum.cons (w := 360) h98292 (SegSum.cons (w := 720) h98293 (SegSum.cons (w := 360) h98295 (SegSum.cons (w := 360) h98296 (SegSum.cons (w := 720) h98297 (SegSum.cons (w := 360) h98299 (show SegSum (P.leaf 36) [] 0 from rfl))))))))) (by decide)

end RACert.S6N0.C0.S78
