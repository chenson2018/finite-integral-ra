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

namespace RACert.S6N0.C0.S69

open RACert RACert.Problem

theorem cover98291 : P.CoversSplit 26 10 98291 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00800000000000000000000fa000000fa0000000000000000000000fa000000fa080000000000000000000000000000000000000000f0c0f0c000000000f0c0f0c8000000000000000000000000000000000000000000000000000000000000fac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 972, 979]) (by decide +kernel)

noncomputable def f98291 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 26 (100649984 + i)

theorem c98291_0 : rowSum f98291 0 1024 = 266379128 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 98291) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover98291 (by decide)
  decide +kernel

theorem sum98291 : rowSum f98291 0 1024 = 266379128 :=
  c98291_0

theorem h98291 : P.leaf 36 98291 = 266379128 :=
  leaf_weighted (k := 26) (d := 10) (H := 98291) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 98291) (by decide) (by decide +kernel)) sum98291

theorem cover372187 : P.CoversSplit 26 10 372187 0xaaaaaaaaaaaaaaaaaaaaababaaaaabab00000000000000000000000000220022000000000000000000000a0a00000a0a0000000000000000000000000000000200000000002200220000000000220023000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 629, 636, 1665]) (by decide +kernel)

noncomputable def f372187 (i : ℕ) := rowWeight keep3 twice3 i * P.leaf 26 (381119488 + i)

theorem c372187_0 : rowSum f372187 0 1024 = 257149345 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 372187) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover372187 (by decide)
  decide +kernel

theorem sum372187 : rowSum f372187 0 1024 = 257149345 :=
  c372187_0

theorem h372187 : P.leaf 36 372187 = 257149345 :=
  leaf_weighted (k := 26) (d := 10) (H := 372187) (keep := keep3) (twice := twice3) rows (by decide) (by decide) (bal3) (invRow3 (H := 372187) (by decide) (by decide +kernel)) sum372187

theorem h98292 : P.leaf 36 98292 = 257149345 :=
  orient84 (v := 372187) (by decide) (by decide +kernel) h372187

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
  leaf_weighted (k := 26) (d := 10) (H := 98295) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 98295) (by decide) (by decide +kernel)) sum98295

theorem cover375259 : P.CoversSplit 26 10 375259 0xaaaaaaaaaaaaaaaaaaaaababaaaaabab00000000000000000000000000220022000000000000000000000a0a00000a0a0000000000000000000000000000000200000000002200220000000000220023000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 629, 636, 1665]) (by decide +kernel)

noncomputable def f375259 (i : ℕ) := rowWeight keep3 twice3 i * P.leaf 26 (384265216 + i)

theorem c375259_0 : rowSum f375259 0 1024 = 292682473 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 375259) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover375259 (by decide)
  decide +kernel

theorem sum375259 : rowSum f375259 0 1024 = 292682473 :=
  c375259_0

theorem h375259 : P.leaf 36 375259 = 292682473 :=
  leaf_weighted (k := 26) (d := 10) (H := 375259) (keep := keep3) (twice := twice3) rows (by decide) (by decide) (bal3) (invRow3 (H := 375259) (by decide) (by decide +kernel)) sum375259

theorem h98296 : P.leaf 36 98296 = 292682473 :=
  orient86 (v := 375259) (by decide) (by decide +kernel) h375259

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

theorem cover375295 : P.CoversSplit 26 10 375295 0xfffffffffffffffffffffefefffffefe00000000000000000000000000220022ffffffffffffffffaaaaaaaaaaaaaaaa0000000000000000000000000022002200000000003300330000000000330032000000000000000000000000000000000000000000330033000000000022002200000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [629, 636, 930, 1273, 1658, 1665]) (by decide +kernel)

noncomputable def f375295 (i : ℕ) := rowWeight keep3 twice3 i * P.leaf 26 (384302080 + i)

theorem c375295_0 : rowSum f375295 0 908 = 404334105 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 375295) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover375295 (by decide)
  decide +kernel

theorem c375295_1 : rowSum f375295 908 116 = 969943206 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 375295) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover375295 (by decide)
  decide +kernel

theorem sum375295 : rowSum f375295 0 1024 = 1374277311 :=
  rowSum_append (F := f375295) (lo := 0) (n := 908) (m := 116) (A := 404334105) (B := 969943206) c375295_0 (c375295_1)

theorem h375295 : P.leaf 36 375295 = 1374277311 :=
  leaf_weighted (k := 26) (d := 10) (H := 375295) (keep := keep3) (twice := twice3) rows (by decide) (by decide) (bal3) (invRow3 (H := 375295) (by decide) (by decide +kernel)) sum375295

theorem h98299 : P.leaf 36 98299 = 1374277311 :=
  orient86 (v := 375295) (by decide) (by decide +kernel) h375295

theorem cover326643 : P.CoversSplit 26 10 326643 0xffffffffffffffffffffaaaaffffaaaaffffffffccccccccfac8aa88c8c88888fffffffffffffffffafaaaaafafaaaaaffffffffccccccccfac8aa88c8c88888ffffffffffffffffffffaaaaffffaaaaffccffccccccccccfac8aa88c8c88888fffffffffffffffffafaaaaafafaaaaaffccffccccccccccfac8aa88c8c88888 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 1265, 1273, 1658, 1665]) (by decide +kernel)

noncomputable def f326643 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 26 (334482432 + i)

theorem c326643_0 : rowSum f326643 0 278 = 444047645 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 326643) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover326643 (by decide)
  decide +kernel

theorem c326643_1 : rowSum f326643 278 158 = 486256048 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 326643) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover326643 (by decide)
  decide +kernel

theorem c326643_2 : rowSum f326643 436 407 = 715796367 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 326643) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover326643 (by decide)
  decide +kernel

theorem c326643_3 : rowSum f326643 843 181 = 628180412 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 326643) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover326643 (by decide)
  decide +kernel

theorem sum326643 : rowSum f326643 0 1024 = 2274280472 :=
  rowSum_append (F := f326643) (lo := 0) (n := 278) (m := 746) (A := 444047645) (B := 1830232827) c326643_0 (rowSum_append (F := f326643) (lo := 278) (n := 158) (m := 588) (A := 486256048) (B := 1343976779) c326643_1 (rowSum_append (F := f326643) (lo := 436) (n := 407) (m := 181) (A := 715796367) (B := 628180412) c326643_2 (c326643_3)))

theorem h326643 : P.leaf 36 326643 = 2274280472 :=
  leaf_weighted (k := 26) (d := 10) (H := 326643) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 326643) (by decide) (by decide +kernel)) sum326643

theorem h98300 : P.leaf 36 98300 = 2274280472 :=
  orient80 (v := 326643) (by decide) (by decide +kernel) h326643

theorem cover98301 : P.CoversSplit 26 10 98301 0xfffffffffffffafafffffffafffffafafffffffffffcfac8fafafafafac8fac8fffffafafffffafafafafafafafafafafffffafafffcfac8fafafafafac8fac8fffffffffffffafafffffffafffffafaffffffffffccfac8fafafafafac8fac80000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c98301_0 : P.sumLeaves 26 100660224 387 = 220499446 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98301) (lo := 0) (len := 387) (W := 220499446) check rows elimOK (by decide) (by decide) cover98301 (by decide)
  decide +kernel

theorem c98301_1 : P.sumLeaves 26 100660611 104 = 481966487 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98301) (lo := 387) (len := 104) (W := 481966487) check rows elimOK (by decide) (by decide) cover98301 (by decide)
  decide +kernel

theorem c98301_2 : P.sumLeaves 26 100660715 131 = 392221131 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98301) (lo := 491) (len := 131) (W := 392221131) check rows elimOK (by decide) (by decide) cover98301 (by decide)
  decide +kernel

theorem c98301_3 : P.sumLeaves 26 100660846 118 = 502600926 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98301) (lo := 622) (len := 118) (W := 502600926) check rows elimOK (by decide) (by decide) cover98301 (by decide)
  decide +kernel

theorem c98301_4 : P.sumLeaves 26 100660964 129 = 578575690 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98301) (lo := 740) (len := 129) (W := 578575690) check rows elimOK (by decide) (by decide) cover98301 (by decide)
  decide +kernel

theorem c98301_5 : P.sumLeaves 26 100661093 106 = 984023096 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98301) (lo := 869) (len := 106) (W := 984023096) check rows elimOK (by decide) (by decide) cover98301 (by decide)
  decide +kernel

theorem c98301_6 : P.sumLeaves 26 100661199 49 = 726298394 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98301) (lo := 975) (len := 49) (W := 726298394) check rows elimOK (by decide) (by decide) cover98301 (by decide)
  decide +kernel

theorem h98301 : P.leaf 36 98301 = 3886185170 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(387, 220499446), (104, 481966487), (131, 392221131), (118, 502600926), (129, 578575690), (106, 984023096), (49, 726298394)]) (.cons c98301_0 (.cons c98301_1 (.cons c98301_2 (.cons c98301_3 (.cons c98301_4 (.cons c98301_5 (.cons c98301_6 (.nil)))))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(98291, 360), (98292, 360), (98293, 720), (98295, 360), (98296, 360), (98297, 720), (98299, 360), (98300, 360), (98301, 720)]

theorem segOK : checkSeg 20 perms 98291 98303 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 98291 98303 4320 6161083515360 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 6161083515360)
    (SegSum.cons (w := 360) h98291 (SegSum.cons (w := 360) h98292 (SegSum.cons (w := 720) h98293 (SegSum.cons (w := 360) h98295 (SegSum.cons (w := 360) h98296 (SegSum.cons (w := 720) h98297 (SegSum.cons (w := 360) h98299 (SegSum.cons (w := 360) h98300 (SegSum.cons (w := 720) h98301 (show SegSum (P.leaf 36) [] 0 from rfl)))))))))) (by decide)

end RACert.S6N0.C0.S69
