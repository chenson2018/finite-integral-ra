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

namespace RACert.S6N0.C0.S63

open RACert RACert.Problem

theorem cover97249 : P.CoversSplit 26 10 97249 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 923, 972, 979, 1266, 1273]) (by decide +kernel)

theorem c97249_0 : P.sumLeaves 26 99582976 1024 = 9845368 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97249) (lo := 0) (len := 1024) (W := 9845368) check rows elimOK (by decide) (by decide) cover97249 (by decide)
  decide +kernel

theorem h97249 : P.leaf 36 97249 = 9845368 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 9845368)]) (.cons c97249_0 (.nil)) (by decide) (by decide))

theorem cover97251 : P.CoversSplit 26 10 97251 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 972, 979, 1266, 1273]) (by decide +kernel)

noncomputable def f97251 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 26 (99585024 + i)

theorem c97251_0 : rowSum f97251 0 1024 = 45324694 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 97251) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover97251 (by decide)
  decide +kernel

theorem sum97251 : rowSum f97251 0 1024 = 45324694 :=
  c97251_0

theorem h97251 : P.leaf 36 97251 = 45324694 :=
  leaf_weighted (k := 26) (d := 10) (H := 97251) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 97251) (by decide) (by decide +kernel)) sum97251

theorem cover112595 : P.CoversSplit 26 10 112595 0xff000000ff000500ff000000ff000000000000000000000000000000000000000500050005000500000000000000000000000000000000000000000000000000ff000000ff220500ff000000ff220000000000000000000000000000000000000500050005000500000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 608, 930, 1315, 1322, 1658]) (by decide +kernel)

theorem c112595_0 : P.sumLeaves 26 115297280 1024 = 61211012 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 112595) (lo := 0) (len := 1024) (W := 61211012) check rows elimOK (by decide) (by decide) cover112595 (by decide)
  decide +kernel

theorem h112595 : P.leaf 36 112595 = 61211012 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 61211012)]) (.cons c112595_0 (.nil)) (by decide) (by decide))

theorem h97253 : P.leaf 36 97253 = 61211012 :=
  orient4 (v := 112595) (by decide) (by decide +kernel) h112595

theorem cover293373 : P.CoversSplit 26 10 293373 0xffffffffffffffff000000000000000000000000000000000001000000000000050505050505050505050000050500000000000000000000000100000000000000330033003300330000000000000000003300330000000000010000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [629, 636, 923, 972, 979, 1265, 1273, 1658, 1665]) (by decide +kernel)

noncomputable def f293373 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 26 (300413952 + i)

theorem c293373_0 : rowSum f293373 0 1024 = 176246396 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 293373) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover293373 (by decide)
  decide +kernel

theorem sum293373 : rowSum f293373 0 1024 = 176246396 :=
  c293373_0

theorem h293373 : P.leaf 36 293373 = 176246396 :=
  leaf_weighted (k := 26) (d := 10) (H := 293373) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 293373) (by decide) (by decide +kernel)) sum293373

theorem h97255 : P.leaf 36 97255 = 176246396 :=
  orient80 (v := 293373) (by decide) (by decide +kernel) h293373

theorem cover309206 : P.CoversSplit 26 10 309206 0xff000000ff000000050000000500000000000000000000000000000000000000ff000000ff000000000000000000000000000000000000000000000000000000ff000000ff330000050000000501000000000000000000000000000000000000ff000000ff330000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [467, 489, 930, 1265, 1272, 1658]) (by decide +kernel)

theorem c309206_0 : P.sumLeaves 26 316626944 1024 = 74223127 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 309206) (lo := 0) (len := 1024) (W := 74223127) check rows elimOK (by decide) (by decide) cover309206 (by decide)
  decide +kernel

theorem h309206 : P.leaf 36 309206 = 74223127 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 74223127)]) (.cons c309206_0 (.nil)) (by decide) (by decide))

theorem h97257 : P.leaf 36 97257 = 74223127 :=
  orient74 (v := 309206) (by decide) (by decide +kernel) h309206

theorem cover293374 : P.CoversSplit 26 10 293374 0xffffffffffffffff000000000000000000000000000000000001000000000000050505050505050505050000050500000000000000000000000100000000000000330033003300330000000000000000003300330000000000010000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [482, 629, 636, 972, 979, 1265, 1273, 1658, 1665]) (by decide +kernel)

noncomputable def f293374 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 26 (300414976 + i)

theorem c293374_0 : rowSum f293374 0 1024 = 197461166 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 293374) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover293374 (by decide)
  decide +kernel

theorem sum293374 : rowSum f293374 0 1024 = 197461166 :=
  c293374_0

theorem h293374 : P.leaf 36 293374 = 197461166 :=
  leaf_weighted (k := 26) (d := 10) (H := 293374) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 293374) (by decide) (by decide +kernel)) sum293374

theorem h97259 : P.leaf 36 97259 = 197461166 :=
  orient80 (v := 293374) (by decide) (by decide +kernel) h293374

theorem cover293367 : P.CoversSplit 26 10 293367 0xffffffffffffffff000000000000000000000000000000000001000000000000050505050505050505050000050500000000000000000000000100000000000000330033003300330000000000000000003300330000000000010000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 629, 636, 929, 972, 979, 1265, 1273, 1658, 1665]) (by decide +kernel)

theorem c293367_0 : P.sumLeaves 26 300407808 1005 = 101345675 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 293367) (lo := 0) (len := 1005) (W := 101345675) check rows elimOK (by decide) (by decide) cover293367 (by decide)
  decide +kernel

theorem c293367_1 : P.sumLeaves 26 300408813 19 = 59712520 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 293367) (lo := 1005) (len := 19) (W := 59712520) check rows elimOK (by decide) (by decide) cover293367 (by decide)
  decide +kernel

theorem h293367 : P.leaf 36 293367 = 161058195 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1005, 101345675), (19, 59712520)]) (.cons c293367_0 (.cons c293367_1 (.nil))) (by decide) (by decide))

theorem h97261 : P.leaf 36 97261 = 161058195 :=
  orient80 (v := 293367) (by decide) (by decide +kernel) h293367

theorem cover293375 : P.CoversSplit 26 10 293375 0xffffffffffffffff000000000000000000000000000000000001000000000000050505050505050505050000050500000000000000000000000100000000000000330033003300330000000000000000003300330000000000010000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [629, 636, 923, 972, 979, 1265, 1273, 1658, 1665]) (by decide +kernel)

noncomputable def f293375 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 26 (300416000 + i)

theorem c293375_0 : rowSum f293375 0 1024 = 401744664 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 293375) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover293375 (by decide)
  decide +kernel

theorem sum293375 : rowSum f293375 0 1024 = 401744664 :=
  c293375_0

theorem h293375 : P.leaf 36 293375 = 401744664 :=
  leaf_weighted (k := 26) (d := 10) (H := 293375) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 293375) (by decide) (by decide +kernel)) sum293375

theorem h97263 : P.leaf 36 97263 = 401744664 :=
  orient80 (v := 293375) (by decide) (by decide +kernel) h293375

theorem cover97267 : P.CoversSplit 26 10 97267 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00800000000000000000000fa000000fa0000000000000000000000fa000000fa080000000000000000000000000000000000000000c0c0c0c000000000c0c0c0c8000000000000000000000000000000000000000000000000000000000000c8c8 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 972, 979, 1273]) (by decide +kernel)

noncomputable def f97267 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 26 (99601408 + i)

theorem c97267_0 : rowSum f97267 0 1024 = 206783492 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 97267) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover97267 (by decide)
  decide +kernel

theorem sum97267 : rowSum f97267 0 1024 = 206783492 :=
  c97267_0

theorem h97267 : P.leaf 36 97267 = 206783492 :=
  leaf_weighted (k := 26) (d := 10) (H := 97267) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 97267) (by decide) (by decide +kernel)) sum97267

theorem cover370139 : P.CoversSplit 26 10 370139 0xaaaaaa00a0a0a00aaaaaaa00a0a0a00a00000000000000000000000000000000000000000000000000000a000000000a0000000000000000000000000000000000000000002000020000000000200002000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 629, 636, 873, 881, 958, 1665]) (by decide +kernel)

noncomputable def f370139 (i : ℕ) := rowWeight keep18 twice18 i * P.leaf 26 (379022336 + i)

theorem c370139_0 : rowSum f370139 0 1024 = 94681548 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 370139) (keep := keep18) (twice := twice18) check rows elimOK (by decide) (by decide) cover370139 (by decide)
  decide +kernel

theorem sum370139 : rowSum f370139 0 1024 = 94681548 :=
  c370139_0

theorem h370139 : P.leaf 36 370139 = 94681548 :=
  leaf_weighted (k := 26) (d := 10) (H := 370139) (keep := keep18) (twice := twice18) rows (by decide) (by decide) (bal18) (invRow18 (H := 370139) (by decide) (by decide +kernel)) sum370139

theorem h97268 : P.leaf 36 97268 = 94681548 :=
  orient84 (v := 370139) (by decide) (by decide +kernel) h370139

theorem cover370143 : P.CoversSplit 26 10 370143 0xffffff00ffffff00fffffa00fffffa0000000000000000000000000000000000ffffff00ffffff00aaaaaa00aaaaaa000000000000000000000000000000000000000000003300000000000000330000000000000000000000000000000000000000000000330000000000000022000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 629, 636, 873, 881, 958, 1658, 1665]) (by decide +kernel)

theorem c370143_0 : P.sumLeaves 26 379026432 916 = 191052804 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 370143) (lo := 0) (len := 916) (W := 191052804) check rows elimOK (by decide) (by decide) cover370143 (by decide)
  decide +kernel

theorem c370143_1 : P.sumLeaves 26 379027348 108 = 287640214 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 370143) (lo := 916) (len := 108) (W := 287640214) check rows elimOK (by decide) (by decide) cover370143 (by decide)
  decide +kernel

theorem h370143 : P.leaf 36 370143 = 478693018 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(916, 191052804), (108, 287640214)]) (.cons c370143_0 (.cons c370143_1 (.nil))) (by decide) (by decide))

theorem h97269 : P.leaf 36 97269 = 478693018 :=
  orient84 (v := 370143) (by decide) (by decide +kernel) h370143

theorem cover97271 : P.CoversSplit 26 10 97271 0xff00ff00ff00fa00ff00ff00ff00fa00ff00ff00ff03fa00fa00fa00fa00fa00ff00fa00ff00fa00fa00f000fa00f000ff00fa00ff03fa00fa00f000fa00f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 972, 979, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f97271 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 26 (99605504 + i)

theorem c97271_0 : rowSum f97271 0 872 = 520753771 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 97271) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover97271 (by decide)
  decide +kernel

theorem c97271_1 : rowSum f97271 872 152 = 542507956 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 97271) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover97271 (by decide)
  decide +kernel

theorem sum97271 : rowSum f97271 0 1024 = 1063261727 :=
  rowSum_append (F := f97271) (lo := 0) (n := 872) (m := 152) (A := 520753771) (B := 542507956) c97271_0 (c97271_1)

theorem h97271 : P.leaf 36 97271 = 1063261727 :=
  leaf_weighted (k := 26) (d := 10) (H := 97271) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 97271) (by decide) (by decide +kernel)) sum97271

theorem cover373211 : P.CoversSplit 26 10 373211 0xaaaaaaaaaaaaaaaaaaaaababaaaaabab00000000000000000000000000220022000000000000000000000a0a00000a0a0000000000000000000000000000000200000000002200220000000000220023000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 629, 636, 1665]) (by decide +kernel)

noncomputable def f373211 (i : ℕ) := rowWeight keep3 twice3 i * P.leaf 26 (382168064 + i)

theorem c373211_0 : rowSum f373211 0 1024 = 93959502 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 373211) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover373211 (by decide)
  decide +kernel

theorem sum373211 : rowSum f373211 0 1024 = 93959502 :=
  c373211_0

theorem h373211 : P.leaf 36 373211 = 93959502 :=
  leaf_weighted (k := 26) (d := 10) (H := 373211) (keep := keep3) (twice := twice3) rows (by decide) (by decide) (bal3) (invRow3 (H := 373211) (by decide) (by decide +kernel)) sum373211

theorem h97272 : P.leaf 36 97272 = 93959502 :=
  orient86 (v := 373211) (by decide) (by decide +kernel) h373211

theorem cover97273 : P.CoversSplit 26 10 97273 0xf0f0f0f0f0f0f0f0f0f0f0f5f0f0f0f0f0f0f0f0f0f0f0c0f0f0f0f0f0c0f0c00000000000000000000050500000505000000000000000000000505000005040f0f0f0f0f0f0f0f0f0f0f0f5f0f0f0f0f0f0f0f0c000c000f0f0f0f0c000c0000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 923, 972, 979, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c97273_0 : P.sumLeaves 26 99607552 494 = 82528991 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97273) (lo := 0) (len := 494) (W := 82528991) check rows elimOK (by decide) (by decide) cover97273 (by decide)
  decide +kernel

theorem c97273_1 : P.sumLeaves 26 99608046 431 = 166922687 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97273) (lo := 494) (len := 431) (W := 166922687) check rows elimOK (by decide) (by decide) cover97273 (by decide)
  decide +kernel

theorem c97273_2 : P.sumLeaves 26 99608477 99 = 214550566 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97273) (lo := 925) (len := 99) (W := 214550566) check rows elimOK (by decide) (by decide) cover97273 (by decide)
  decide +kernel

theorem h97273 : P.leaf 36 97273 = 464002244 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(494, 82528991), (431, 166922687), (99, 214550566)]) (.cons c97273_0 (.cons c97273_1 (.cons c97273_2 (.nil)))) (by decide) (by decide))

theorem cover373247 : P.CoversSplit 26 10 373247 0xfffffffffffffffffffffefefffffefe00000000000000000000000000220022fffffafafffffafaaaaaaaaaaaaaaaaa0000000000000000000000000022002200000000003300330000000000330032000000000000000000000000000000000000000000330032000000000022002200000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [629, 636, 873, 930, 1273, 1658, 1665]) (by decide +kernel)

noncomputable def f373247 (i : ℕ) := rowWeight keep3 twice3 i * P.leaf 26 (382204928 + i)

theorem c373247_0 : rowSum f373247 0 919 = 372391298 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 373247) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover373247 (by decide)
  decide +kernel

theorem c373247_1 : rowSum f373247 919 105 = 735786388 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 373247) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover373247 (by decide)
  decide +kernel

theorem sum373247 : rowSum f373247 0 1024 = 1108177686 :=
  rowSum_append (F := f373247) (lo := 0) (n := 919) (m := 105) (A := 372391298) (B := 735786388) c373247_0 (c373247_1)

theorem h373247 : P.leaf 36 373247 = 1108177686 :=
  leaf_weighted (k := 26) (d := 10) (H := 373247) (keep := keep3) (twice := twice3) rows (by decide) (by decide) (bal3) (invRow3 (H := 373247) (by decide) (by decide +kernel)) sum373247

theorem h97275 : P.leaf 36 97275 = 1108177686 :=
  orient86 (v := 373247) (by decide) (by decide +kernel) h373247

def seg : List (ℕ × ℕ) := [(97249, 240), (97251, 360), (97253, 720), (97255, 360), (97257, 720), (97259, 360), (97261, 720), (97263, 360), (97267, 360), (97268, 180), (97269, 720), (97271, 360), (97272, 360), (97273, 720), (97275, 360)]

theorem segOK : checkSeg 20 perms 97249 97276 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 97249 97276 6900 2097085993800 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 2097085993800)
    (SegSum.cons (w := 240) h97249 (SegSum.cons (w := 360) h97251 (SegSum.cons (w := 720) h97253 (SegSum.cons (w := 360) h97255 (SegSum.cons (w := 720) h97257 (SegSum.cons (w := 360) h97259 (SegSum.cons (w := 720) h97261 (SegSum.cons (w := 360) h97263 (SegSum.cons (w := 360) h97267 (SegSum.cons (w := 180) h97268 (SegSum.cons (w := 720) h97269 (SegSum.cons (w := 360) h97271 (SegSum.cons (w := 360) h97272 (SegSum.cons (w := 720) h97273 (SegSum.cons (w := 360) h97275 (show SegSum (P.leaf 36) [] 0 from rfl)))))))))))))))) (by decide)

end RACert.S6N0.C0.S63
