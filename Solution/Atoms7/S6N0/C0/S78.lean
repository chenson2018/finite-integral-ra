/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Atoms7.S6N0.C0.Defs

/-! Generated certificate for the identity on six symmetric diversity atoms. -/

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option Elab.async false

@[expose] public section

namespace RACert.S6N0.C0.S78

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

theorem c97251_0 : P.sumLeaves 26 99585024 1024 = 45324694 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97251) (lo := 0) (len := 1024) (W := 45324694) check rows elimOK (by decide) (by decide) cover97251 (by decide)
  decide +kernel

theorem h97251 : P.leaf 36 97251 = 45324694 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 45324694)]) (.cons c97251_0 (.nil)) (by decide) (by decide))

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

theorem c97255_0 : P.sumLeaves 26 99589120 988 = 139154036 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97255) (lo := 0) (len := 988) (W := 139154036) check rows elimOK (by decide) (by decide) cover97255 (by decide)
  decide +kernel

theorem c97255_1 : P.sumLeaves 26 99590108 36 = 37092360 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97255) (lo := 988) (len := 36) (W := 37092360) check rows elimOK (by decide) (by decide) cover97255 (by decide)
  decide +kernel

theorem h97255 : P.leaf 36 97255 = 176246396 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(988, 139154036), (36, 37092360)]) (.cons c97255_0 (.cons c97255_1 (.nil))) (by decide) (by decide))

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

theorem c97259_0 : P.sumLeaves 26 99593216 510 = 23717360 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97259) (lo := 0) (len := 510) (W := 23717360) check rows elimOK (by decide) (by decide) cover97259 (by decide)
  decide +kernel

theorem c97259_1 : P.sumLeaves 26 99593726 456 = 119417146 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97259) (lo := 510) (len := 456) (W := 119417146) check rows elimOK (by decide) (by decide) cover97259 (by decide)
  decide +kernel

theorem c97259_2 : P.sumLeaves 26 99594182 58 = 54326660 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97259) (lo := 966) (len := 58) (W := 54326660) check rows elimOK (by decide) (by decide) cover97259 (by decide)
  decide +kernel

theorem h97259 : P.leaf 36 97259 = 197461166 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(510, 23717360), (456, 119417146), (58, 54326660)]) (.cons c97259_0 (.cons c97259_1 (.cons c97259_2 (.nil)))) (by decide) (by decide))

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

theorem c97263_0 : P.sumLeaves 26 99597312 430 = 37698220 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97263) (lo := 0) (len := 430) (W := 37698220) check rows elimOK (by decide) (by decide) cover97263 (by decide)
  decide +kernel

theorem c97263_1 : P.sumLeaves 26 99597742 371 = 66380974 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97263) (lo := 430) (len := 371) (W := 66380974) check rows elimOK (by decide) (by decide) cover97263 (by decide)
  decide +kernel

theorem c97263_2 : P.sumLeaves 26 99598113 116 = 134236578 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97263) (lo := 801) (len := 116) (W := 134236578) check rows elimOK (by decide) (by decide) cover97263 (by decide)
  decide +kernel

theorem c97263_3 : P.sumLeaves 26 99598229 102 = 152718816 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97263) (lo := 917) (len := 102) (W := 152718816) check rows elimOK (by decide) (by decide) cover97263 (by decide)
  decide +kernel

theorem c97263_4 : P.sumLeaves 26 99598331 5 = 10710076 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97263) (lo := 1019) (len := 5) (W := 10710076) check rows elimOK (by decide) (by decide) cover97263 (by decide)
  decide +kernel

theorem h97263 : P.leaf 36 97263 = 401744664 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(430, 37698220), (371, 66380974), (116, 134236578), (102, 152718816), (5, 10710076)]) (.cons c97263_0 (.cons c97263_1 (.cons c97263_2 (.cons c97263_3 (.cons c97263_4 (.nil)))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(97249, 240), (97251, 360), (97253, 720), (97255, 360), (97257, 720), (97259, 360), (97261, 720), (97263, 360)]

theorem segOK : checkSeg 20 perms 97249 97267 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 97249 97267 3840 511317060000 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 511317060000)
    (SegSum.cons (w := 240) h97249 (SegSum.cons (w := 360) h97251 (SegSum.cons (w := 720) h97253 (SegSum.cons (w := 360) h97255 (SegSum.cons (w := 720) h97257 (SegSum.cons (w := 360) h97259 (SegSum.cons (w := 720) h97261 (SegSum.cons (w := 360) h97263 (show SegSum (P.leaf 36) [] 0 from rfl))))))))) (by decide)

end RACert.S6N0.C0.S78
