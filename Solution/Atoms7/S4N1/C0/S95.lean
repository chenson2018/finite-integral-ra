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

namespace RACert.S4N1.C0.S95

open RACert RACert.Problem

theorem cover24494 : P.CoversSplit 24 10 24494 0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa000000000000aaaa0000000000008888000088880000888800008888000088880000000000008888000000000000aaaa0000aaaa00000000000000000000aaaa00000000000000220000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 515, 517, 522, 1202, 1259, 1601]) (by decide +kernel)

theorem c24494_0 : P.sumLeaves 24 25081856 1021 = 51729310 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24494) (lo := 0) (len := 1021) (W := 51729310) check rows elimOK (by decide) (by decide) cover24494 (by decide)
  decide +kernel

theorem c24494_1 : P.sumLeaves 24 25082877 3 = 3627272 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24494) (lo := 1021) (len := 3) (W := 3627272) check rows elimOK (by decide) (by decide) cover24494 (by decide)
  decide +kernel

theorem h24494 : P.leaf 34 24494 = 55356582 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1021, 51729310), (3, 3627272)]) (.cons c24494_0 (.cons c24494_1 (.nil))) (by decide) (by decide))

theorem cover24495 : P.CoversSplit 24 10 24495 0xfffffffffafaa0a0fffffffffafaa0a0fffffffffafaa0a0fffffffffafaa0a0cccccccc88888080cccccccc88888080cccccccc88888080cccccccc88888080fffffffffafaa0a00000000000000000fffffffffafaa0a000330033003200200000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 522, 1202, 1210, 1259, 1308, 1601]) (by decide +kernel)

theorem c24495_0 : P.sumLeaves 24 25082880 500 = 33138416 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24495) (lo := 0) (len := 500) (W := 33138416) check rows elimOK (by decide) (by decide) cover24495 (by decide)
  decide +kernel

theorem c24495_1 : P.sumLeaves 24 25083380 262 = 49950790 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24495) (lo := 500) (len := 262) (W := 49950790) check rows elimOK (by decide) (by decide) cover24495 (by decide)
  decide +kernel

theorem c24495_2 : P.sumLeaves 24 25083642 130 = 76087389 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24495) (lo := 762) (len := 130) (W := 76087389) check rows elimOK (by decide) (by decide) cover24495 (by decide)
  decide +kernel

theorem c24495_3 : P.sumLeaves 24 25083772 128 = 147798178 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24495) (lo := 892) (len := 128) (W := 147798178) check rows elimOK (by decide) (by decide) cover24495 (by decide)
  decide +kernel

theorem c24495_4 : P.sumLeaves 24 25083900 4 = 10815916 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24495) (lo := 1020) (len := 4) (W := 10815916) check rows elimOK (by decide) (by decide) cover24495 (by decide)
  decide +kernel

theorem h24495 : P.leaf 34 24495 = 317790689 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(500, 33138416), (262, 49950790), (130, 76087389), (128, 147798178), (4, 10815916)]) (.cons c24495_0 (.cons c24495_1 (.cons c24495_2 (.cons c24495_3 (.cons c24495_4 (.nil)))))) (by decide) (by decide))

theorem cover24503 : P.CoversSplit 24 10 24503 0xfffffffffafaa0a0fffffffffafaa0a0fffffffffafaa0a0fffffffffafaa0a0cccccccc88888080cccccccc88888080cccccccc88888080cccccccc88888080fffffffffafaa0a0fffffffffafaa0a0fffffffffafaa0a0fffffffffafaa0a0cccccccc88888080cccccccc8888808000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [517, 916, 1202, 1210, 1259, 1308, 1601]) (by decide +kernel)

theorem c24503_0 : P.sumLeaves 24 25091072 337 = 13201311 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24503) (lo := 0) (len := 337) (W := 13201311) check rows elimOK (by decide) (by decide) cover24503 (by decide)
  decide +kernel

theorem c24503_1 : P.sumLeaves 24 25091409 128 = 48187339 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24503) (lo := 337) (len := 128) (W := 48187339) check rows elimOK (by decide) (by decide) cover24503 (by decide)
  decide +kernel

theorem c24503_2 : P.sumLeaves 24 25091537 213 = 53090723 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24503) (lo := 465) (len := 213) (W := 53090723) check rows elimOK (by decide) (by decide) cover24503 (by decide)
  decide +kernel

theorem c24503_3 : P.sumLeaves 24 25091750 182 = 67616889 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24503) (lo := 678) (len := 182) (W := 67616889) check rows elimOK (by decide) (by decide) cover24503 (by decide)
  decide +kernel

theorem c24503_4 : P.sumLeaves 24 25091932 128 = 140682999 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24503) (lo := 860) (len := 128) (W := 140682999) check rows elimOK (by decide) (by decide) cover24503 (by decide)
  decide +kernel

theorem c24503_5 : P.sumLeaves 24 25092060 36 = 87307169 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24503) (lo := 988) (len := 36) (W := 87307169) check rows elimOK (by decide) (by decide) cover24503 (by decide)
  decide +kernel

theorem h24503 : P.leaf 34 24503 = 410086430 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(337, 13201311), (128, 48187339), (213, 53090723), (182, 67616889), (128, 140682999), (36, 87307169)]) (.cons c24503_0 (.cons c24503_1 (.cons c24503_2 (.cons c24503_3 (.cons c24503_4 (.cons c24503_5 (.nil))))))) (by decide) (by decide))

theorem cover24507 : P.CoversSplit 24 10 24507 0xfffffffffafaa0a0fffffffffafaa0a0fffffffffafaa0a0fffffffffafaa0a0cccccccc88888080cc00cc0088008000cccccccc88888080cc00cc0088008000fffffffffafaa0a0fffffffffafaa0a0fffffffffafaa0a0fffffffffafaa0a0cccccccc88888080cc00cc008800800000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [517, 916, 1202, 1210, 1259, 1308, 1601]) (by decide +kernel)

theorem c24507_0 : P.sumLeaves 24 25095168 351 = 12098603 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24507) (lo := 0) (len := 351) (W := 12098603) check rows elimOK (by decide) (by decide) cover24507 (by decide)
  decide +kernel

theorem c24507_1 : P.sumLeaves 24 25095519 128 = 33302360 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24507) (lo := 351) (len := 128) (W := 33302360) check rows elimOK (by decide) (by decide) cover24507 (by decide)
  decide +kernel

theorem c24507_2 : P.sumLeaves 24 25095647 284 = 45727846 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24507) (lo := 479) (len := 284) (W := 45727846) check rows elimOK (by decide) (by decide) cover24507 (by decide)
  decide +kernel

theorem c24507_3 : P.sumLeaves 24 25095931 130 = 61366288 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24507) (lo := 763) (len := 130) (W := 61366288) check rows elimOK (by decide) (by decide) cover24507 (by decide)
  decide +kernel

theorem c24507_4 : P.sumLeaves 24 25096061 128 = 135172695 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24507) (lo := 893) (len := 128) (W := 135172695) check rows elimOK (by decide) (by decide) cover24507 (by decide)
  decide +kernel

theorem c24507_5 : P.sumLeaves 24 25096189 3 = 6802412 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24507) (lo := 1021) (len := 3) (W := 6802412) check rows elimOK (by decide) (by decide) cover24507 (by decide)
  decide +kernel

theorem h24507 : P.leaf 34 24507 = 294470204 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(351, 12098603), (128, 33302360), (284, 45727846), (130, 61366288), (128, 135172695), (3, 6802412)]) (.cons c24507_0 (.cons c24507_1 (.cons c24507_2 (.cons c24507_3 (.cons c24507_4 (.cons c24507_5 (.nil))))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(24494, 48), (24495, 48), (24503, 12), (24507, 24)]

theorem segOK : checkSeg 16 perms 24494 24508 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 24494 24508 132 29899391064 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 29899391064)
    (SegSum.cons (w := 48) h24494 (SegSum.cons (w := 48) h24495 (SegSum.cons (w := 12) h24503 (SegSum.cons (w := 24) h24507 (show SegSum (P.leaf 34) [] 0 from rfl))))) (by decide)

end RACert.S4N1.C0.S95
