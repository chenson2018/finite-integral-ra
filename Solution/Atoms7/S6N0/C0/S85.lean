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

namespace RACert.S6N0.C0.S85

open RACert RACert.Problem

theorem cover98277 : P.CoversSplit 26 10 98277 0xff00ff00ff00fa00ff00ff00ff00fa00ff00ff00ff03fa00fa00fa00fa00fa00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003300320000000000320032000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 923, 972, 979, 1266, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c98277_0 : P.sumLeaves 26 100635648 957 = 233604073 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98277) (lo := 0) (len := 957) (W := 233604073) check rows elimOK (by decide) (by decide) cover98277 (by decide)
  decide +kernel

theorem c98277_1 : P.sumLeaves 26 100636605 67 = 181508530 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98277) (lo := 957) (len := 67) (W := 181508530) check rows elimOK (by decide) (by decide) cover98277 (by decide)
  decide +kernel

theorem h98277 : P.leaf 36 98277 = 415112603 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(957, 233604073), (67, 181508530)]) (.cons c98277_0 (.cons c98277_1 (.nil))) (by decide) (by decide))

theorem cover98279 : P.CoversSplit 26 10 98279 0xff00ff00ff00fa00ff00ff00ff00fa00ff00ff00ff03fa00fa00fa00fa00fa00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003300320000000000320032000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 972, 979, 1266, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c98279_0 : P.sumLeaves 26 100637696 957 = 509113029 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98279) (lo := 0) (len := 957) (W := 509113029) check rows elimOK (by decide) (by decide) cover98279 (by decide)
  decide +kernel

theorem c98279_1 : P.sumLeaves 26 100638653 67 = 307952092 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98279) (lo := 957) (len := 67) (W := 307952092) check rows elimOK (by decide) (by decide) cover98279 (by decide)
  decide +kernel

theorem h98279 : P.leaf 36 98279 = 817065121 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(957, 509113029), (67, 307952092)]) (.cons c98279_0 (.cons c98279_1 (.nil))) (by decide) (by decide))

theorem cover98280 : P.CoversSplit 26 10 98280 0xf0f0f0f0f0f0f0f0f0f0f0f5f0f0f0f0f0f0f0f0f0f0f0c0f0f0f0f0f0c0f0c00000000000000000000000000000000000000000000000000000000000000000f0f0f0f0f0f0f0f0f0f0f0f5f0f0f0f0f0f0f0f0f000f000f0f0f0f0f000f0000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 874, 972, 979, 1266, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c98280_0 : P.sumLeaves 26 100638720 478 = 20285108 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98280) (lo := 0) (len := 478) (W := 20285108) check rows elimOK (by decide) (by decide) cover98280 (by decide)
  decide +kernel

theorem c98280_1 : P.sumLeaves 26 100639198 456 = 54447856 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98280) (lo := 478) (len := 456) (W := 54447856) check rows elimOK (by decide) (by decide) cover98280 (by decide)
  decide +kernel

theorem c98280_2 : P.sumLeaves 26 100639654 90 = 72333144 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98280) (lo := 934) (len := 90) (W := 72333144) check rows elimOK (by decide) (by decide) cover98280 (by decide)
  decide +kernel

theorem h98280 : P.leaf 36 98280 = 147066108 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(478, 20285108), (456, 54447856), (90, 72333144)]) (.cons c98280_0 (.cons c98280_1 (.cons c98280_2 (.nil)))) (by decide) (by decide))

theorem cover98281 : P.CoversSplit 26 10 98281 0xf0f0f0f0f0f0f0f0f0f0f0f5f0f0f0f0f0f0f0f0f0f0f0c0f0f0f0f0f0c0f0c00000000000000000000000000000000000000000000000000000000000000000f0f0f0f0f0f0f0f0f0f0f0f5f0f0f0f0f0f0f0f0f000f000f0f0f0f0f000f0000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 923, 972, 979, 1266, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c98281_0 : P.sumLeaves 26 100639744 478 = 66961908 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98281) (lo := 0) (len := 478) (W := 66961908) check rows elimOK (by decide) (by decide) cover98281 (by decide)
  decide +kernel

theorem c98281_1 : P.sumLeaves 26 100640222 456 = 206022722 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98281) (lo := 478) (len := 456) (W := 206022722) check rows elimOK (by decide) (by decide) cover98281 (by decide)
  decide +kernel

theorem c98281_2 : P.sumLeaves 26 100640678 90 = 211940800 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98281) (lo := 934) (len := 90) (W := 211940800) check rows elimOK (by decide) (by decide) cover98281 (by decide)
  decide +kernel

theorem h98281 : P.leaf 36 98281 = 484925430 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(478, 66961908), (456, 206022722), (90, 211940800)]) (.cons c98281_0 (.cons c98281_1 (.cons c98281_2 (.nil)))) (by decide) (by decide))

theorem cover98283 : P.CoversSplit 26 10 98283 0xf0f0f0f0f0f0f0f0f0f0f0f5f0f0f0f0f0f0f0f0f0f0f0c0f0f0f0f0f0c0f0c00000000000000000000000000000000000000000000000000000000000000000f0f0f0f0f0f0f0f0f0f0f0f5f0f0f0f0f0f0f0f0f000f000f0f0f0f0f000f0000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 972, 979, 1266, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c98283_0 : P.sumLeaves 26 100641792 478 = 168143928 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98283) (lo := 0) (len := 478) (W := 168143928) check rows elimOK (by decide) (by decide) cover98283 (by decide)
  decide +kernel

theorem c98283_1 : P.sumLeaves 26 100642270 456 = 491405584 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98283) (lo := 478) (len := 456) (W := 491405584) check rows elimOK (by decide) (by decide) cover98283 (by decide)
  decide +kernel

theorem c98283_2 : P.sumLeaves 26 100642726 90 = 400193032 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98283) (lo := 934) (len := 90) (W := 400193032) check rows elimOK (by decide) (by decide) cover98283 (by decide)
  decide +kernel

theorem h98283 : P.leaf 36 98283 = 1059742544 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(478, 168143928), (456, 491405584), (90, 400193032)]) (.cons c98283_0 (.cons c98283_1 (.cons c98283_2 (.nil)))) (by decide) (by decide))

theorem cover98284 : P.CoversSplit 26 10 98284 0xfffffffffffffafafffffffafffffafafffffffffffcfac8fafafafafac8fac80000000000000000000000000000000000000000000000000000000000000000fffffffffffffafafffffffafffffafaffffffffff00fa00fafafafafa00fa000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [874, 972, 979, 1266, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c98284_0 : P.sumLeaves 26 100642816 402 = 43414976 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98284) (lo := 0) (len := 402) (W := 43414976) check rows elimOK (by decide) (by decide) cover98284 (by decide)
  decide +kernel

theorem c98284_1 : P.sumLeaves 26 100643218 102 = 133899446 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98284) (lo := 402) (len := 102) (W := 133899446) check rows elimOK (by decide) (by decide) cover98284 (by decide)
  decide +kernel

theorem c98284_2 : P.sumLeaves 26 100643320 383 = 162103044 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98284) (lo := 504) (len := 383) (W := 162103044) check rows elimOK (by decide) (by decide) cover98284 (by decide)
  decide +kernel

theorem c98284_3 : P.sumLeaves 26 100643703 106 = 273030536 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98284) (lo := 887) (len := 106) (W := 273030536) check rows elimOK (by decide) (by decide) cover98284 (by decide)
  decide +kernel

theorem c98284_4 : P.sumLeaves 26 100643809 31 = 221976310 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98284) (lo := 993) (len := 31) (W := 221976310) check rows elimOK (by decide) (by decide) cover98284 (by decide)
  decide +kernel

theorem h98284 : P.leaf 36 98284 = 834424312 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(402, 43414976), (102, 133899446), (383, 162103044), (106, 273030536), (31, 221976310)]) (.cons c98284_0 (.cons c98284_1 (.cons c98284_2 (.cons c98284_3 (.cons c98284_4 (.nil)))))) (by decide) (by decide))

theorem cover98285 : P.CoversSplit 26 10 98285 0xfffffffffffffafafffffffafffffafafffffffffffcfac8fafafafafac8fac80000000000000000000000000000000000000000000000000000000000000000fffffffffffffafafffffffafffffafaffffffffff00fa00fafafafafa00fa000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [923, 972, 979, 1266, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c98285_0 : P.sumLeaves 26 100643840 402 = 117510290 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98285) (lo := 0) (len := 402) (W := 117510290) check rows elimOK (by decide) (by decide) cover98285 (by decide)
  decide +kernel

theorem c98285_1 : P.sumLeaves 26 100644242 102 = 276163029 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98285) (lo := 402) (len := 102) (W := 276163029) check rows elimOK (by decide) (by decide) cover98285 (by decide)
  decide +kernel

theorem c98285_2 : P.sumLeaves 26 100644344 383 = 365275410 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98285) (lo := 504) (len := 383) (W := 365275410) check rows elimOK (by decide) (by decide) cover98285 (by decide)
  decide +kernel

theorem c98285_3 : P.sumLeaves 26 100644727 106 = 540469858 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98285) (lo := 887) (len := 106) (W := 540469858) check rows elimOK (by decide) (by decide) cover98285 (by decide)
  decide +kernel

theorem c98285_4 : P.sumLeaves 26 100644833 31 = 346544220 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98285) (lo := 993) (len := 31) (W := 346544220) check rows elimOK (by decide) (by decide) cover98285 (by decide)
  decide +kernel

theorem h98285 : P.leaf 36 98285 = 1645962807 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(402, 117510290), (102, 276163029), (383, 365275410), (106, 540469858), (31, 346544220)]) (.cons c98285_0 (.cons c98285_1 (.cons c98285_2 (.cons c98285_3 (.cons c98285_4 (.nil)))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(98277, 720), (98279, 360), (98280, 180), (98281, 720), (98283, 360), (98284, 360), (98285, 720)]

theorem segOK : checkSeg 20 perms 98277 98287 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 98277 98287 3420 2835636015960 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 2835636015960)
    (SegSum.cons (w := 720) h98277 (SegSum.cons (w := 360) h98279 (SegSum.cons (w := 180) h98280 (SegSum.cons (w := 720) h98281 (SegSum.cons (w := 360) h98283 (SegSum.cons (w := 360) h98284 (SegSum.cons (w := 720) h98285 (show SegSum (P.leaf 36) [] 0 from rfl)))))))) (by decide)

end RACert.S6N0.C0.S85
