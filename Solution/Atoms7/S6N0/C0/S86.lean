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

namespace RACert.S6N0.C0.S86

open RACert RACert.Problem

theorem cover98287 : P.CoversSplit 26 10 98287 0xfffffffffffffafafffffffafffffafafffffffffffcfac8fafafafafac8fac80000000000000000000000000000000000000000000000000000000000000000fffffffffffffafafffffffafffffafaffffffffff00fa00fafafafafa00fa000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [972, 979, 1266, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c98287_0 : P.sumLeaves 26 100645888 402 = 339022704 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98287) (lo := 0) (len := 402) (W := 339022704) check rows elimOK (by decide) (by decide) cover98287 (by decide)
  decide +kernel

theorem c98287_1 : P.sumLeaves 26 100646290 102 = 460738933 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98287) (lo := 402) (len := 102) (W := 460738933) check rows elimOK (by decide) (by decide) cover98287 (by decide)
  decide +kernel

theorem c98287_2 : P.sumLeaves 26 100646392 383 = 852072730 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98287) (lo := 504) (len := 383) (W := 852072730) check rows elimOK (by decide) (by decide) cover98287 (by decide)
  decide +kernel

theorem c98287_3 : P.sumLeaves 26 100646775 106 = 1011775848 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98287) (lo := 887) (len := 106) (W := 1011775848) check rows elimOK (by decide) (by decide) cover98287 (by decide)
  decide +kernel

theorem c98287_4 : P.sumLeaves 26 100646881 31 = 436219470 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98287) (lo := 993) (len := 31) (W := 436219470) check rows elimOK (by decide) (by decide) cover98287 (by decide)
  decide +kernel

theorem h98287 : P.leaf 36 98287 = 3099829685 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(402, 339022704), (102, 460738933), (383, 852072730), (106, 1011775848), (31, 436219470)]) (.cons c98287_0 (.cons c98287_1 (.cons c98287_2 (.cons c98287_3 (.cons c98287_4 (.nil)))))) (by decide) (by decide))

theorem cover98291 : P.CoversSplit 26 10 98291 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00800000000000000000000fa000000fa0000000000000000000000fa000000fa080000000000000000000000000000000000000000f0c0f0c000000000f0c0f0c8000000000000000000000000000000000000000000000000000000000000fac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 972, 979]) (by decide +kernel)

theorem c98291_0 : P.sumLeaves 26 100649984 924 = 136221894 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98291) (lo := 0) (len := 924) (W := 136221894) check rows elimOK (by decide) (by decide) cover98291 (by decide)
  decide +kernel

theorem c98291_1 : P.sumLeaves 26 100650908 100 = 130157234 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98291) (lo := 924) (len := 100) (W := 130157234) check rows elimOK (by decide) (by decide) cover98291 (by decide)
  decide +kernel

theorem h98291 : P.leaf 36 98291 = 266379128 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(924, 136221894), (100, 130157234)]) (.cons c98291_0 (.cons c98291_1 (.nil))) (by decide) (by decide))

theorem cover98292 : P.CoversSplit 26 10 98292 0xff00ff00ff00fa00ff00ff00ff00fa00ff00ff00ff03fa00fa00fa00fa00fa00ff00fa00ff00fa00fa00f000fa00f000ff00fa00ff03fa00fa00f000fa00f00000000000000000000000000000000000000000003300320000000000320032000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 874, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c98292_0 : P.sumLeaves 26 100651008 735 = 48532627 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98292) (lo := 0) (len := 735) (W := 48532627) check rows elimOK (by decide) (by decide) cover98292 (by decide)
  decide +kernel

theorem c98292_1 : P.sumLeaves 26 100651743 220 = 118557000 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98292) (lo := 735) (len := 220) (W := 118557000) check rows elimOK (by decide) (by decide) cover98292 (by decide)
  decide +kernel

theorem c98292_2 : P.sumLeaves 26 100651963 69 = 90059718 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98292) (lo := 955) (len := 69) (W := 90059718) check rows elimOK (by decide) (by decide) cover98292 (by decide)
  decide +kernel

theorem h98292 : P.leaf 36 98292 = 257149345 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(735, 48532627), (220, 118557000), (69, 90059718)]) (.cons c98292_0 (.cons c98292_1 (.cons c98292_2 (.nil)))) (by decide) (by decide))

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

theorem c98295_0 : P.sumLeaves 26 100654080 715 = 233720418 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98295) (lo := 0) (len := 715) (W := 233720418) check rows elimOK (by decide) (by decide) cover98295 (by decide)
  decide +kernel

theorem c98295_1 : P.sumLeaves 26 100654795 212 = 624018059 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98295) (lo := 715) (len := 212) (W := 624018059) check rows elimOK (by decide) (by decide) cover98295 (by decide)
  decide +kernel

theorem c98295_2 : P.sumLeaves 26 100655007 97 = 519056550 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98295) (lo := 927) (len := 97) (W := 519056550) check rows elimOK (by decide) (by decide) cover98295 (by decide)
  decide +kernel

theorem h98295 : P.leaf 36 98295 = 1376795027 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(715, 233720418), (212, 624018059), (97, 519056550)]) (.cons c98295_0 (.cons c98295_1 (.cons c98295_2 (.nil)))) (by decide) (by decide))

theorem cover98296 : P.CoversSplit 26 10 98296 0xf0f0f0f0f0f0f0f0f0f0f0f5f0f0f0f0f0f0f0f0f0f0f0c0f0f0f0f0f0c0f0c00000000000000000000050500000505000000000000000000000505000005040f0f0f0f0f0f0f0f0f0f0f0f5f0f0f0f0f0f0f0f0f000f000f0f0f0f0f000f0000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 874, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c98296_0 : P.sumLeaves 26 100655104 478 = 50950676 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98296) (lo := 0) (len := 478) (W := 50950676) check rows elimOK (by decide) (by decide) cover98296 (by decide)
  decide +kernel

theorem c98296_1 : P.sumLeaves 26 100655582 431 = 92961168 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98296) (lo := 478) (len := 431) (W := 92961168) check rows elimOK (by decide) (by decide) cover98296 (by decide)
  decide +kernel

theorem c98296_2 : P.sumLeaves 26 100656013 115 = 148770629 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98296) (lo := 909) (len := 115) (W := 148770629) check rows elimOK (by decide) (by decide) cover98296 (by decide)
  decide +kernel

theorem h98296 : P.leaf 36 98296 = 292682473 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(478, 50950676), (431, 92961168), (115, 148770629)]) (.cons c98296_0 (.cons c98296_1 (.cons c98296_2 (.nil)))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(98287, 360), (98291, 360), (98292, 360), (98293, 720), (98295, 360), (98296, 360)]

theorem segOK : checkSeg 20 perms 98287 98297 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 98287 98297 2520 2537862625440 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 2537862625440)
    (SegSum.cons (w := 360) h98287 (SegSum.cons (w := 360) h98291 (SegSum.cons (w := 360) h98292 (SegSum.cons (w := 720) h98293 (SegSum.cons (w := 360) h98295 (SegSum.cons (w := 360) h98296 (show SegSum (P.leaf 36) [] 0 from rfl))))))) (by decide)

end RACert.S6N0.C0.S86
