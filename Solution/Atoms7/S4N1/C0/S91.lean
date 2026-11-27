/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Atoms7.S4N1.C0.Actions

/-! Generated identity-class certificate for the product-row count. -/

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option Elab.async false

@[expose] public section

namespace RACert.S4N1.C0.S91

open RACert RACert.Problem

theorem cover24366 : P.CoversSplit 24 10 24366 0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa000000000000aaaa0000000000008888000088880000880000008800000088880000000000008800000000000000aaaa0000aaaa00000000000000000000aaaa00000000000000220000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 515, 517, 522, 529, 1202, 1259, 1601]) (by decide +kernel)

theorem c24366_0 : P.sumLeaves 24 24950784 1024 = 24259907 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24366) (lo := 0) (len := 1024) (W := 24259907) check rows elimOK (by decide) (by decide) cover24366 (by decide)
  decide +kernel

theorem h24366 : P.leaf 34 24366 = 24259907 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 24259907)]) (.cons c24366_0 (.nil)) (by decide) (by decide))

theorem cover24367 : P.CoversSplit 24 10 24367 0xfffffffffafaa0a0fffffffffafaa0a0fffffffffafaa0a0fffffffffafaa0a0cccccccc88888080cc00cc0088008000cccccccc88888080cc00cc0088008000fffffffffafaa0a00000000000000000fffffffffafaa0a000330033003200200000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 522, 1202, 1210, 1259, 1308, 1601]) (by decide +kernel)

theorem c24367_0 : P.sumLeaves 24 24951808 500 = 17817962 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24367) (lo := 0) (len := 500) (W := 17817962) check rows elimOK (by decide) (by decide) cover24367 (by decide)
  decide +kernel

theorem c24367_1 : P.sumLeaves 24 24952308 302 = 43317201 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24367) (lo := 500) (len := 302) (W := 43317201) check rows elimOK (by decide) (by decide) cover24367 (by decide)
  decide +kernel

theorem c24367_2 : P.sumLeaves 24 24952610 128 = 65529434 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24367) (lo := 802) (len := 128) (W := 65529434) check rows elimOK (by decide) (by decide) cover24367 (by decide)
  decide +kernel

theorem c24367_3 : P.sumLeaves 24 24952738 94 = 95297934 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24367) (lo := 930) (len := 94) (W := 95297934) check rows elimOK (by decide) (by decide) cover24367 (by decide)
  decide +kernel

theorem h24367 : P.leaf 34 24367 = 221962531 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(500, 17817962), (302, 43317201), (128, 65529434), (94, 95297934)]) (.cons c24367_0 (.cons c24367_1 (.cons c24367_2 (.cons c24367_3 (.nil))))) (by decide) (by decide))

theorem cover24375 : P.CoversSplit 24 10 24375 0xfffffffffafaa0a0fffffffffafaa0a0fffffffffafaa0a0fffffffffafaa0a0cccccccc88888080cc00cc0088008000cccccccc88888080cc00cc0088008000fffffffffafaa0a0fffffffffafaa0a0fffffffffafaa0a0fffffffffafaa0a00000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [517, 572, 1202, 1210, 1259, 1308, 1601, 1609]) (ps := [(14, [965], [1609])]) (by decide +kernel)

theorem c24375_0 : P.sumLeaves 24 24960000 389 = 17544730 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24375) (lo := 0) (len := 389) (W := 17544730) check rows elimOK (by decide) (by decide) cover24375 (by decide)
  decide +kernel

theorem c24375_1 : P.sumLeaves 24 24960389 138 = 49317084 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24375) (lo := 389) (len := 138) (W := 49317084) check rows elimOK (by decide) (by decide) cover24375 (by decide)
  decide +kernel

theorem c24375_2 : P.sumLeaves 24 24960527 287 = 31362754 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24375) (lo := 527) (len := 287) (W := 31362754) check rows elimOK (by decide) (by decide) cover24375 (by decide)
  decide +kernel

theorem c24375_3 : P.sumLeaves 24 24960814 128 = 88250808 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24375) (lo := 814) (len := 128) (W := 88250808) check rows elimOK (by decide) (by decide) cover24375 (by decide)
  decide +kernel

theorem c24375_4 : P.sumLeaves 24 24960942 82 = 112566198 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24375) (lo := 942) (len := 82) (W := 112566198) check rows elimOK (by decide) (by decide) cover24375 (by decide)
  decide +kernel

theorem h24375 : P.leaf 34 24375 = 299041574 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(389, 17544730), (138, 49317084), (287, 31362754), (128, 88250808), (82, 112566198)]) (.cons c24375_0 (.cons c24375_1 (.cons c24375_2 (.cons c24375_3 (.cons c24375_4 (.nil)))))) (by decide) (by decide))

theorem cover24380 : P.CoversSplit 24 10 24380 0xffaaffaafaaaa0a0ffaaffaafaaaa0a0ffaaffaac8888080ffaaffaac8888080cc88cc8888888080cc00cc0088008000cc88cc8888888080cc00cc0088008000ff00ff00fa00a000ff22ff22fa22a020ff00ff00c8008000ff22ff22c80080000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 508, 529, 916, 1202, 1210, 1308, 1601]) (by decide +kernel)

theorem c24380_0 : P.sumLeaves 24 24965120 509 = 16490527 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24380) (lo := 0) (len := 509) (W := 16490527) check rows elimOK (by decide) (by decide) cover24380 (by decide)
  decide +kernel

theorem c24380_1 : P.sumLeaves 24 24965629 350 = 24618233 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24380) (lo := 509) (len := 350) (W := 24618233) check rows elimOK (by decide) (by decide) cover24380 (by decide)
  decide +kernel

theorem c24380_2 : P.sumLeaves 24 24965979 158 = 62791423 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24380) (lo := 859) (len := 158) (W := 62791423) check rows elimOK (by decide) (by decide) cover24380 (by decide)
  decide +kernel

theorem c24380_3 : P.sumLeaves 24 24966137 7 = 11500180 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24380) (lo := 1017) (len := 7) (W := 11500180) check rows elimOK (by decide) (by decide) cover24380 (by decide)
  decide +kernel

theorem h24380 : P.leaf 34 24380 = 115400363 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(509, 16490527), (350, 24618233), (158, 62791423), (7, 11500180)]) (.cons c24380_0 (.cons c24380_1 (.cons c24380_2 (.cons c24380_3 (.nil))))) (by decide) (by decide))

theorem cover24381 : P.CoversSplit 24 10 24381 0xfffffffffafaa0a0fffffffffafaa0a0ffffffffc8c88080ffffffffc8c88080cccccccc88888080cc00cc0088008000cccccccc88888080cc00cc0088008000ff00ff00fa00a000ff33ff33fa32a020ff00ff00c8008000ff33ff33c80080000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 517, 529, 916, 1202, 1210, 1259, 1308, 1601]) (by decide +kernel)

theorem c24381_0 : P.sumLeaves 24 24966144 492 = 23826502 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24381) (lo := 0) (len := 492) (W := 23826502) check rows elimOK (by decide) (by decide) cover24381 (by decide)
  decide +kernel

theorem c24381_1 : P.sumLeaves 24 24966636 318 = 44077420 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24381) (lo := 492) (len := 318) (W := 44077420) check rows elimOK (by decide) (by decide) cover24381 (by decide)
  decide +kernel

theorem c24381_2 : P.sumLeaves 24 24966954 136 = 66626580 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24381) (lo := 810) (len := 136) (W := 66626580) check rows elimOK (by decide) (by decide) cover24381 (by decide)
  decide +kernel

theorem c24381_3 : P.sumLeaves 24 24967090 78 = 81620996 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24381) (lo := 946) (len := 78) (W := 81620996) check rows elimOK (by decide) (by decide) cover24381 (by decide)
  decide +kernel

theorem h24381 : P.leaf 34 24381 = 216151498 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(492, 23826502), (318, 44077420), (136, 66626580), (78, 81620996)]) (.cons c24381_0 (.cons c24381_1 (.cons c24381_2 (.cons c24381_3 (.nil))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(24366, 48), (24367, 48), (24375, 12), (24380, 48), (24381, 48)]

theorem segOK : checkSeg 16 perms 24366 24382 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 24366 24382 204 31321665240 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 31321665240)
    (SegSum.cons (w := 48) h24366 (SegSum.cons (w := 48) h24367 (SegSum.cons (w := 12) h24375 (SegSum.cons (w := 48) h24380 (SegSum.cons (w := 48) h24381 (show SegSum (P.leaf 34) [] 0 from rfl)))))) (by decide)

end RACert.S4N1.C0.S91
