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

namespace RACert.S6N0.C0.S71

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
  leaf_weighted (k := 26) (d := 10) (H := 97251) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 97251) (by decide) (by decide +kernel)) sum97251

theorem cover97253 : P.CoversSplit 26 10 97253 0xff00ff00ff00fa00ff00ff00ff00fa00ff00ff00ff03fa00fa00fa00fa00fa00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 923, 972, 979, 1266, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c97253_0 : P.sumLeaves 26 99587072 988 = 44871116 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97253) (lo := 0) (len := 988) (W := 44871116) check rows elimOK (by decide) (by decide) cover97253 (by decide)
  decide +kernel

theorem c97253_1 : P.sumLeaves 26 99588060 36 = 16339896 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97253) (lo := 988) (len := 36) (W := 16339896) check rows elimOK (by decide) (by decide) cover97253 (by decide)
  decide +kernel

theorem h97253 : P.leaf 36 97253 = 61211012 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(988, 44871116), (36, 16339896)]) (.cons c97253_0 (.cons c97253_1 (.nil))) (by decide) (by decide))

theorem cover97255 : P.CoversSplit 26 10 97255 0xff00ff00ff00fa00ff00ff00ff00fa00ff00ff00ff03fa00fa00fa00fa00fa00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 972, 979, 1266, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f97255 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 26 (99589120 + i)

theorem c97255_0 : rowSum f97255 0 1024 = 176246396 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 97255) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover97255 (by decide)
  decide +kernel

theorem sum97255 : rowSum f97255 0 1024 = 176246396 :=
  c97255_0

theorem h97255 : P.leaf 36 97255 = 176246396 :=
  leaf_weighted (k := 26) (d := 10) (H := 97255) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 97255) (by decide) (by decide +kernel)) sum97255

theorem cover97257 : P.CoversSplit 26 10 97257 0xf0f0f0f0f0f0f0f0f0f0f0f5f0f0f0f0f0f0f0f0f0f0f0c0f0f0f0f0f0c0f0c00000000000000000000000000000000000000000000000000000000000000000f0f0f0f0f0f0f0f0f0f0f0f5f0f0f0f0f0f0f0f000000000f0f0f0f0000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 923, 972, 979, 1266, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c97257_0 : P.sumLeaves 26 99591168 510 = 9701592 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97257) (lo := 0) (len := 510) (W := 9701592) check rows elimOK (by decide) (by decide) cover97257 (by decide)
  decide +kernel

theorem c97257_1 : P.sumLeaves 26 99591678 456 = 41240303 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97257) (lo := 510) (len := 456) (W := 41240303) check rows elimOK (by decide) (by decide) cover97257 (by decide)
  decide +kernel

theorem c97257_2 : P.sumLeaves 26 99592134 58 = 23281232 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97257) (lo := 966) (len := 58) (W := 23281232) check rows elimOK (by decide) (by decide) cover97257 (by decide)
  decide +kernel

theorem h97257 : P.leaf 36 97257 = 74223127 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(510, 9701592), (456, 41240303), (58, 23281232)]) (.cons c97257_0 (.cons c97257_1 (.cons c97257_2 (.nil)))) (by decide) (by decide))

theorem cover97259 : P.CoversSplit 26 10 97259 0xf0f0f0f0f0f0f0f0f0f0f0f5f0f0f0f0f0f0f0f0f0f0f0c0f0f0f0f0f0c0f0c00000000000000000000000000000000000000000000000000000000000000000f0f0f0f0f0f0f0f0f0f0f0f5f0f0f0f0f0f0f0f000000000f0f0f0f0000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 972, 979, 1266, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f97259 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 26 (99593216 + i)

theorem c97259_0 : rowSum f97259 0 870 = 94916346 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 97259) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover97259 (by decide)
  decide +kernel

theorem c97259_1 : rowSum f97259 870 154 = 102544820 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 97259) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover97259 (by decide)
  decide +kernel

theorem sum97259 : rowSum f97259 0 1024 = 197461166 :=
  rowSum_append (F := f97259) (lo := 0) (n := 870) (m := 154) (A := 94916346) (B := 102544820) c97259_0 (c97259_1)

theorem h97259 : P.leaf 36 97259 = 197461166 :=
  leaf_weighted (k := 26) (d := 10) (H := 97259) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 97259) (by decide) (by decide +kernel)) sum97259

theorem cover97261 : P.CoversSplit 26 10 97261 0xfffffffffffffafafffffffafffffafafffffffffffcfac8fafafafafac8fac80000000000000000000000000000000000000000000000000000000000000000fffffffffffffafafffffffafffffafaffffffff00000000fafafafa000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [923, 972, 979, 1266, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c97261_0 : P.sumLeaves 26 99595264 430 = 12511868 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97261) (lo := 0) (len := 430) (W := 12511868) check rows elimOK (by decide) (by decide) cover97261 (by decide)
  decide +kernel

theorem c97261_1 : P.sumLeaves 26 99595694 371 = 26057022 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97261) (lo := 430) (len := 371) (W := 26057022) check rows elimOK (by decide) (by decide) cover97261 (by decide)
  decide +kernel

theorem c97261_2 : P.sumLeaves 26 99596065 116 = 52189193 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97261) (lo := 801) (len := 116) (W := 52189193) check rows elimOK (by decide) (by decide) cover97261 (by decide)
  decide +kernel

theorem c97261_3 : P.sumLeaves 26 99596181 102 = 61133100 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97261) (lo := 917) (len := 102) (W := 61133100) check rows elimOK (by decide) (by decide) cover97261 (by decide)
  decide +kernel

theorem c97261_4 : P.sumLeaves 26 99596283 5 = 9167012 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97261) (lo := 1019) (len := 5) (W := 9167012) check rows elimOK (by decide) (by decide) cover97261 (by decide)
  decide +kernel

theorem h97261 : P.leaf 36 97261 = 161058195 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(430, 12511868), (371, 26057022), (116, 52189193), (102, 61133100), (5, 9167012)]) (.cons c97261_0 (.cons c97261_1 (.cons c97261_2 (.cons c97261_3 (.cons c97261_4 (.nil)))))) (by decide) (by decide))

theorem cover97263 : P.CoversSplit 26 10 97263 0xfffffffffffffafafffffffafffffafafffffffffffcfac8fafafafafac8fac80000000000000000000000000000000000000000000000000000000000000000fffffffffffffafafffffffafffffafaffffffff00000000fafafafa000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [972, 979, 1266, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f97263 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 26 (99597312 + i)

theorem c97263_0 : rowSum f97263 0 506 = 77453892 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 97263) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover97263 (by decide)
  decide +kernel

theorem c97263_1 : rowSum f97263 506 426 = 230268980 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 97263) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover97263 (by decide)
  decide +kernel

theorem c97263_2 : rowSum f97263 932 92 = 94021792 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 97263) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover97263 (by decide)
  decide +kernel

theorem sum97263 : rowSum f97263 0 1024 = 401744664 :=
  rowSum_append (F := f97263) (lo := 0) (n := 506) (m := 518) (A := 77453892) (B := 324290772) c97263_0 (rowSum_append (F := f97263) (lo := 506) (n := 426) (m := 92) (A := 230268980) (B := 94021792) c97263_1 (c97263_2))

theorem h97263 : P.leaf 36 97263 = 401744664 :=
  leaf_weighted (k := 26) (d := 10) (H := 97263) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 97263) (by decide) (by decide +kernel)) sum97263

theorem cover97267 : P.CoversSplit 26 10 97267 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00800000000000000000000fa000000fa0000000000000000000000fa000000fa080000000000000000000000000000000000000000c0c0c0c000000000c0c0c0c8000000000000000000000000000000000000000000000000000000000000c8c8 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 972, 979, 1273]) (by decide +kernel)

noncomputable def f97267 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 26 (99601408 + i)

theorem c97267_0 : rowSum f97267 0 1024 = 206783492 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 97267) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover97267 (by decide)
  decide +kernel

theorem sum97267 : rowSum f97267 0 1024 = 206783492 :=
  c97267_0

theorem h97267 : P.leaf 36 97267 = 206783492 :=
  leaf_weighted (k := 26) (d := 10) (H := 97267) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 97267) (by decide) (by decide +kernel)) sum97267

theorem cover97268 : P.CoversSplit 26 10 97268 0xff00ff00ff00fa00ff00ff00ff00fa00ff00ff00ff03fa00fa00fa00fa00fa00ff00fa00ff00fa00fa00f000fa00f000ff00fa00ff03fa00fa00f000fa00f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 874, 972, 979, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f97268 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 26 (99602432 + i)

theorem c97268_0 : rowSum f97268 0 872 = 37951644 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 97268) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover97268 (by decide)
  decide +kernel

theorem c97268_1 : rowSum f97268 872 152 = 56729904 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 97268) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover97268 (by decide)
  decide +kernel

theorem sum97268 : rowSum f97268 0 1024 = 94681548 :=
  rowSum_append (F := f97268) (lo := 0) (n := 872) (m := 152) (A := 37951644) (B := 56729904) c97268_0 (c97268_1)

theorem h97268 : P.leaf 36 97268 = 94681548 :=
  leaf_weighted (k := 26) (d := 10) (H := 97268) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 97268) (by decide) (by decide +kernel)) sum97268

def seg : List (ℕ × ℕ) := [(97249, 240), (97251, 360), (97253, 720), (97255, 360), (97257, 720), (97259, 360), (97261, 720), (97263, 360), (97267, 360), (97268, 180)]

theorem segOK : checkSeg 20 perms 97249 97269 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 97249 97269 4380 602801795760 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 602801795760)
    (SegSum.cons (w := 240) h97249 (SegSum.cons (w := 360) h97251 (SegSum.cons (w := 720) h97253 (SegSum.cons (w := 360) h97255 (SegSum.cons (w := 720) h97257 (SegSum.cons (w := 360) h97259 (SegSum.cons (w := 720) h97261 (SegSum.cons (w := 360) h97263 (SegSum.cons (w := 360) h97267 (SegSum.cons (w := 180) h97268 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))) (by decide)

end RACert.S6N0.C0.S71
