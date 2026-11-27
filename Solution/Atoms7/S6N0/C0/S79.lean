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

namespace RACert.S6N0.C0.S79

open RACert RACert.Problem

theorem cover97267 : P.CoversSplit 26 10 97267 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00800000000000000000000fa000000fa0000000000000000000000fa000000fa080000000000000000000000000000000000000000c0c0c0c000000000c0c0c0c8000000000000000000000000000000000000000000000000000000000000c8c8 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 972, 979, 1273]) (by decide +kernel)

theorem c97267_0 : P.sumLeaves 26 99601408 959 = 137972670 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97267) (lo := 0) (len := 959) (W := 137972670) check rows elimOK (by decide) (by decide) cover97267 (by decide)
  decide +kernel

theorem c97267_1 : P.sumLeaves 26 99602367 65 = 68810822 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97267) (lo := 959) (len := 65) (W := 68810822) check rows elimOK (by decide) (by decide) cover97267 (by decide)
  decide +kernel

theorem h97267 : P.leaf 36 97267 = 206783492 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(959, 137972670), (65, 68810822)]) (.cons c97267_0 (.cons c97267_1 (.nil))) (by decide) (by decide))

theorem cover97268 : P.CoversSplit 26 10 97268 0xff00ff00ff00fa00ff00ff00ff00fa00ff00ff00ff03fa00fa00fa00fa00fa00ff00fa00ff00fa00fa00f000fa00f000ff00fa00ff03fa00fa00f000fa00f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 874, 972, 979, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c97268_0 : P.sumLeaves 26 99602432 766 = 20439372 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97268) (lo := 0) (len := 766) (W := 20439372) check rows elimOK (by decide) (by decide) cover97268 (by decide)
  decide +kernel

theorem c97268_1 : P.sumLeaves 26 99603198 220 = 45021964 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97268) (lo := 766) (len := 220) (W := 45021964) check rows elimOK (by decide) (by decide) cover97268 (by decide)
  decide +kernel

theorem c97268_2 : P.sumLeaves 26 99603418 38 = 29220212 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97268) (lo := 986) (len := 38) (W := 29220212) check rows elimOK (by decide) (by decide) cover97268 (by decide)
  decide +kernel

theorem h97268 : P.leaf 36 97268 = 94681548 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(766, 20439372), (220, 45021964), (38, 29220212)]) (.cons c97268_0 (.cons c97268_1 (.cons c97268_2 (.nil)))) (by decide) (by decide))

theorem cover97269 : P.CoversSplit 26 10 97269 0xff00ff00ff00fa00ff00ff00ff00fa00ff00ff00ff03fa00fa00fa00fa00fa00ff00fa00ff00fa00fa00f000fa00f000ff00fa00ff03fa00fa00f000fa00f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 923, 972, 979, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c97269_0 : P.sumLeaves 26 99603456 766 = 103713584 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97269) (lo := 0) (len := 766) (W := 103713584) check rows elimOK (by decide) (by decide) cover97269 (by decide)
  decide +kernel

theorem c97269_1 : P.sumLeaves 26 99604222 220 = 253398824 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97269) (lo := 766) (len := 220) (W := 253398824) check rows elimOK (by decide) (by decide) cover97269 (by decide)
  decide +kernel

theorem c97269_2 : P.sumLeaves 26 99604442 38 = 121580610 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97269) (lo := 986) (len := 38) (W := 121580610) check rows elimOK (by decide) (by decide) cover97269 (by decide)
  decide +kernel

theorem h97269 : P.leaf 36 97269 = 478693018 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(766, 103713584), (220, 253398824), (38, 121580610)]) (.cons c97269_0 (.cons c97269_1 (.cons c97269_2 (.nil)))) (by decide) (by decide))

theorem cover97271 : P.CoversSplit 26 10 97271 0xff00ff00ff00fa00ff00ff00ff00fa00ff00ff00ff03fa00fa00fa00fa00fa00ff00fa00ff00fa00fa00f000fa00f000ff00fa00ff03fa00fa00f000fa00f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 972, 979, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c97271_0 : P.sumLeaves 26 99605504 766 = 229984233 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97271) (lo := 0) (len := 766) (W := 229984233) check rows elimOK (by decide) (by decide) cover97271 (by decide)
  decide +kernel

theorem c97271_1 : P.sumLeaves 26 99606270 220 = 611661894 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97271) (lo := 766) (len := 220) (W := 611661894) check rows elimOK (by decide) (by decide) cover97271 (by decide)
  decide +kernel

theorem c97271_2 : P.sumLeaves 26 99606490 38 = 221615600 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97271) (lo := 986) (len := 38) (W := 221615600) check rows elimOK (by decide) (by decide) cover97271 (by decide)
  decide +kernel

theorem h97271 : P.leaf 36 97271 = 1063261727 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(766, 229984233), (220, 611661894), (38, 221615600)]) (.cons c97271_0 (.cons c97271_1 (.cons c97271_2 (.nil)))) (by decide) (by decide))

theorem cover97272 : P.CoversSplit 26 10 97272 0xf0f0f0f0f0f0f0f0f0f0f0f5f0f0f0f0f0f0f0f0f0f0f0c0f0f0f0f0f0c0f0c00000000000000000000050500000505000000000000000000000505000005040f0f0f0f0f0f0f0f0f0f0f0f5f0f0f0f0f0f0f0f0c000c000f0f0f0f0c000c0000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 874, 972, 979, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c97272_0 : P.sumLeaves 26 99606528 494 = 20554086 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97272) (lo := 0) (len := 494) (W := 20554086) check rows elimOK (by decide) (by decide) cover97272 (by decide)
  decide +kernel

theorem c97272_1 : P.sumLeaves 26 99607022 431 = 28287229 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97272) (lo := 494) (len := 431) (W := 28287229) check rows elimOK (by decide) (by decide) cover97272 (by decide)
  decide +kernel

theorem c97272_2 : P.sumLeaves 26 99607453 99 = 45118187 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97272) (lo := 925) (len := 99) (W := 45118187) check rows elimOK (by decide) (by decide) cover97272 (by decide)
  decide +kernel

theorem h97272 : P.leaf 36 97272 = 93959502 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(494, 20554086), (431, 28287229), (99, 45118187)]) (.cons c97272_0 (.cons c97272_1 (.cons c97272_2 (.nil)))) (by decide) (by decide))

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

theorem cover97275 : P.CoversSplit 26 10 97275 0xf0f0f0f0f0f0f0f0f0f0f0f5f0f0f0f0f0f0f0f0f0f0f0c0f0f0f0f0f0c0f0c00000000000000000000050500000505000000000000000000000505000005040f0f0f0f0f0f0f0f0f0f0f0f5f0f0f0f0f0f0f0f0c000c000f0f0f0f0c000c0000000000000000000000050500000505000000000000000000000505000004000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 972, 979, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c97275_0 : P.sumLeaves 26 99609600 469 = 159395835 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97275) (lo := 0) (len := 469) (W := 159395835) check rows elimOK (by decide) (by decide) cover97275 (by decide)
  decide +kernel

theorem c97275_1 : P.sumLeaves 26 99610069 431 = 412097801 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97275) (lo := 469) (len := 431) (W := 412097801) check rows elimOK (by decide) (by decide) cover97275 (by decide)
  decide +kernel

theorem c97275_2 : P.sumLeaves 26 99610500 124 = 536684050 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97275) (lo := 900) (len := 124) (W := 536684050) check rows elimOK (by decide) (by decide) cover97275 (by decide)
  decide +kernel

theorem h97275 : P.leaf 36 97275 = 1108177686 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(469, 159395835), (431, 412097801), (124, 536684050)]) (.cons c97275_0 (.cons c97275_1 (.cons c97275_2 (.nil)))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(97267, 360), (97268, 180), (97269, 720), (97271, 360), (97272, 360), (97273, 720), (97275, 360)]

theorem segOK : checkSeg 20 perms 97267 97276 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 97267 97276 3060 1585768933800 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 1585768933800)
    (SegSum.cons (w := 360) h97267 (SegSum.cons (w := 180) h97268 (SegSum.cons (w := 720) h97269 (SegSum.cons (w := 360) h97271 (SegSum.cons (w := 360) h97272 (SegSum.cons (w := 720) h97273 (SegSum.cons (w := 360) h97275 (show SegSum (P.leaf 36) [] 0 from rfl)))))))) (by decide)

end RACert.S6N0.C0.S79
