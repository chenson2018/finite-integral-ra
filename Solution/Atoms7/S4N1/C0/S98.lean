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

namespace RACert.S4N1.C0.S98

open RACert RACert.Problem

theorem cover24558 : P.CoversSplit 24 10 24558 0xfffffffffafaaaaafffffffffafaaaaafffffffffafaaaaafffffffffafaaaaacccccccc88888888cccccccc88888888cccccccc88888888cccccccc88888888fffffffffafaaaaa0000000000000000fffffffffafaaaaa00330033003200220000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 515, 522, 1202, 1210, 1259, 1601]) (by decide +kernel)

theorem c24558_0 : P.sumLeaves 24 25147392 491 = 44449524 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24558) (lo := 0) (len := 491) (W := 44449524) check rows elimOK (by decide) (by decide) cover24558 (by decide)
  decide +kernel

theorem c24558_1 : P.sumLeaves 24 25147883 228 = 45732498 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24558) (lo := 491) (len := 228) (W := 45732498) check rows elimOK (by decide) (by decide) cover24558 (by decide)
  decide +kernel

theorem c24558_2 : P.sumLeaves 24 25148111 148 = 57172411 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24558) (lo := 719) (len := 148) (W := 57172411) check rows elimOK (by decide) (by decide) cover24558 (by decide)
  decide +kernel

theorem c24558_3 : P.sumLeaves 24 25148259 120 = 123723385 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24558) (lo := 867) (len := 120) (W := 123723385) check rows elimOK (by decide) (by decide) cover24558 (by decide)
  decide +kernel

theorem c24558_4 : P.sumLeaves 24 25148379 37 = 99435660 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24558) (lo := 987) (len := 37) (W := 99435660) check rows elimOK (by decide) (by decide) cover24558 (by decide)
  decide +kernel

theorem h24558 : P.leaf 34 24558 = 370513478 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(491, 44449524), (228, 45732498), (148, 57172411), (120, 123723385), (37, 99435660)]) (.cons c24558_0 (.cons c24558_1 (.cons c24558_2 (.cons c24558_3 (.cons c24558_4 (.nil)))))) (by decide) (by decide))

theorem cover24559 : P.CoversSplit 24 10 24559 0xfffffffffafaaaaafffffffffafaaaaafffffffffafaaaaafffffffffafaaaaacccccccc88888888cccccccc88888888cccccccc88888888cccccccc88888888fffffffffafaaaaa0000000000000000fffffffffafaaaaa00330033003200220000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 522, 1202, 1210, 1259, 1601]) (by decide +kernel)

theorem c24559_0 : P.sumLeaves 24 25148416 491 = 65887033 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24559) (lo := 0) (len := 491) (W := 65887033) check rows elimOK (by decide) (by decide) cover24559 (by decide)
  decide +kernel

theorem c24559_1 : P.sumLeaves 24 25148907 228 = 77946663 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24559) (lo := 491) (len := 228) (W := 77946663) check rows elimOK (by decide) (by decide) cover24559 (by decide)
  decide +kernel

theorem c24559_2 : P.sumLeaves 24 25149135 148 = 97004138 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24559) (lo := 719) (len := 148) (W := 97004138) check rows elimOK (by decide) (by decide) cover24559 (by decide)
  decide +kernel

theorem c24559_3 : P.sumLeaves 24 25149283 120 = 177480291 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24559) (lo := 867) (len := 120) (W := 177480291) check rows elimOK (by decide) (by decide) cover24559 (by decide)
  decide +kernel

theorem c24559_4 : P.sumLeaves 24 25149403 37 = 138626286 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24559) (lo := 987) (len := 37) (W := 138626286) check rows elimOK (by decide) (by decide) cover24559 (by decide)
  decide +kernel

theorem h24559 : P.leaf 34 24559 = 556944411 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(491, 65887033), (228, 77946663), (148, 97004138), (120, 177480291), (37, 138626286)]) (.cons c24559_0 (.cons c24559_1 (.cons c24559_2 (.cons c24559_3 (.cons c24559_4 (.nil)))))) (by decide) (by decide))

theorem cover24574 : P.CoversSplit 24 10 24574 0xfffffffffafaaaaafffffffffafaaaaafffffffffafaaaaafffffffffafaaaaacccccccc88888888cccccccc88888888cccccccc88888888cccccccc88888888fffffffffafaaaaafffffffffafaaaaafffffffffafaaaaafffffffffafaaaaacccccccc88888888cccccccc88888888cccccccc88888888cccccccc88888888 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 916, 1202, 1210, 1259, 1601]) (by decide +kernel)

theorem c24574_0 : P.sumLeaves 24 25163776 257 = 35338088 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24574) (lo := 0) (len := 257) (W := 35338088) check rows elimOK (by decide) (by decide) cover24574 (by decide)
  decide +kernel

theorem c24574_1 : P.sumLeaves 24 25164033 119 = 61224776 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24574) (lo := 257) (len := 119) (W := 61224776) check rows elimOK (by decide) (by decide) cover24574 (by decide)
  decide +kernel

theorem c24574_2 : P.sumLeaves 24 25164152 120 = 118594076 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24574) (lo := 376) (len := 120) (W := 118594076) check rows elimOK (by decide) (by decide) cover24574 (by decide)
  decide +kernel

theorem c24574_3 : P.sumLeaves 24 25164272 242 = 106889996 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24574) (lo := 496) (len := 242) (W := 106889996) check rows elimOK (by decide) (by decide) cover24574 (by decide)
  decide +kernel

theorem c24574_4 : P.sumLeaves 24 25164514 134 = 145226194 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24574) (lo := 738) (len := 134) (W := 145226194) check rows elimOK (by decide) (by decide) cover24574 (by decide)
  decide +kernel

theorem c24574_5 : P.sumLeaves 24 25164648 120 = 269189314 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24574) (lo := 872) (len := 120) (W := 269189314) check rows elimOK (by decide) (by decide) cover24574 (by decide)
  decide +kernel

theorem c24574_6 : P.sumLeaves 24 25164768 32 = 129669428 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24574) (lo := 992) (len := 32) (W := 129669428) check rows elimOK (by decide) (by decide) cover24574 (by decide)
  decide +kernel

theorem h24574 : P.leaf 34 24574 = 866131872 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(257, 35338088), (119, 61224776), (120, 118594076), (242, 106889996), (134, 145226194), (120, 269189314), (32, 129669428)]) (.cons c24574_0 (.cons c24574_1 (.cons c24574_2 (.cons c24574_3 (.cons c24574_4 (.cons c24574_5 (.cons c24574_6 (.nil)))))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(24558, 48), (24559, 48), (24574, 24)]

theorem segOK : checkSeg 16 perms 24558 24575 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 24558 24575 120 65305143600 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 65305143600)
    (SegSum.cons (w := 48) h24558 (SegSum.cons (w := 48) h24559 (SegSum.cons (w := 24) h24574 (show SegSum (P.leaf 34) [] 0 from rfl)))) (by decide)

end RACert.S4N1.C0.S98
