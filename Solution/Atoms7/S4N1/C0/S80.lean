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

namespace RACert.S4N1.C0.S80

open RACert RACert.Problem

theorem cover22447 : P.CoversSplit 24 10 22447 0xfffffffffafa0000fffffffffafa0000aaaaafaf00000000aaaa000000000000cccccccc88880000cccccccc8888000088888c8c000000008888000000000000fffffffffafa00000000000000000000aaaaafaf0000000000220000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 517, 522, 860, 916, 1202, 1210, 1251, 1259, 1601]) (by decide +kernel)

theorem c22447_0 : P.sumLeaves 24 22985728 698 = 17201184 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22447) (lo := 0) (len := 698) (W := 17201184) check rows elimOK (by decide) (by decide) cover22447 (by decide)
  decide +kernel

theorem c22447_1 : P.sumLeaves 24 22986426 279 = 35190731 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22447) (lo := 698) (len := 279) (W := 35190731) check rows elimOK (by decide) (by decide) cover22447 (by decide)
  decide +kernel

theorem c22447_2 : P.sumLeaves 24 22986705 47 = 40333688 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22447) (lo := 977) (len := 47) (W := 40333688) check rows elimOK (by decide) (by decide) cover22447 (by decide)
  decide +kernel

theorem h22447 : P.leaf 34 22447 = 92725603 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(698, 17201184), (279, 35190731), (47, 40333688)]) (.cons c22447_0 (.cons c22447_1 (.cons c22447_2 (.nil)))) (by decide) (by decide))

theorem cover22460 : P.CoversSplit 24 10 22460 0xffaaffaafaaa0000ffaaffaafaaa0000ffaaffaa00000000ffaa000000000000cc88cc8888880000cc88cc8888880000cc88cc8800000000cc88000000000000ff22ff22fa220000ff22ff22fa220000ff22ff22fa000000ff220000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 508, 867, 909, 916, 1202, 1210, 1217, 1251, 1601]) (by decide +kernel)

theorem c22460_0 : P.sumLeaves 24 22999040 574 = 9382759 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22460) (lo := 0) (len := 574) (W := 9382759) check rows elimOK (by decide) (by decide) cover22460 (by decide)
  decide +kernel

theorem c22460_1 : P.sumLeaves 24 22999614 362 = 13832209 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22460) (lo := 574) (len := 362) (W := 13832209) check rows elimOK (by decide) (by decide) cover22460 (by decide)
  decide +kernel

theorem c22460_2 : P.sumLeaves 24 22999976 88 = 24055852 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22460) (lo := 936) (len := 88) (W := 24055852) check rows elimOK (by decide) (by decide) cover22460 (by decide)
  decide +kernel

theorem h22460 : P.leaf 34 22460 = 47270820 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(574, 9382759), (362, 13832209), (88, 24055852)]) (.cons c22460_0 (.cons c22460_1 (.cons c22460_2 (.nil)))) (by decide) (by decide))

theorem cover22461 : P.CoversSplit 24 10 22461 0xfffffffffafa0000fffffffffafa0000ffffffff00000000ffff000000000000cccccccc88880000cccccccc88880000cccccccc00000000cccc000000000000ff33ff33fa320000ff33ff33fa320000ff33ff33fa000000ff330000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 517, 860, 909, 916, 1202, 1210, 1217, 1251, 1259, 1308, 1601]) (by decide +kernel)

theorem c22461_0 : P.sumLeaves 24 23000064 496 = 16129282 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22461) (lo := 0) (len := 496) (W := 16129282) check rows elimOK (by decide) (by decide) cover22461 (by decide)
  decide +kernel

theorem c22461_1 : P.sumLeaves 24 23000560 372 = 25317683 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22461) (lo := 496) (len := 372) (W := 25317683) check rows elimOK (by decide) (by decide) cover22461 (by decide)
  decide +kernel

theorem c22461_2 : P.sumLeaves 24 23000932 136 = 50633028 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22461) (lo := 868) (len := 136) (W := 50633028) check rows elimOK (by decide) (by decide) cover22461 (by decide)
  decide +kernel

theorem c22461_3 : P.sumLeaves 24 23001068 20 = 20517792 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22461) (lo := 1004) (len := 20) (W := 20517792) check rows elimOK (by decide) (by decide) cover22461 (by decide)
  decide +kernel

theorem h22461 : P.leaf 34 22461 = 112597785 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(496, 16129282), (372, 25317683), (136, 50633028), (20, 20517792)]) (.cons c22461_0 (.cons c22461_1 (.cons c22461_2 (.cons c22461_3 (.nil))))) (by decide) (by decide))

theorem cover22462 : P.CoversSplit 24 10 22462 0xfffffffffafa0000fffffffffafa0000ffffffff00000000ffff000000000000cccccccc88880000cccccccc88880000cccccccc00000000cccc000000000000fffffffffafa0000fffffffffafa0000fffffffffa000000ffff0000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 860, 867, 909, 916, 1202, 1210, 1217, 1251, 1601]) (by decide +kernel)

theorem c22462_0 : P.sumLeaves 24 23001088 446 = 10650991 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22462) (lo := 0) (len := 446) (W := 10650991) check rows elimOK (by decide) (by decide) cover22462 (by decide)
  decide +kernel

theorem c22462_1 : P.sumLeaves 24 23001534 296 = 20057882 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22462) (lo := 446) (len := 296) (W := 20057882) check rows elimOK (by decide) (by decide) cover22462 (by decide)
  decide +kernel

theorem c22462_2 : P.sumLeaves 24 23001830 208 = 30460465 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22462) (lo := 742) (len := 208) (W := 30460465) check rows elimOK (by decide) (by decide) cover22462 (by decide)
  decide +kernel

theorem c22462_3 : P.sumLeaves 24 23002038 74 = 44438342 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22462) (lo := 950) (len := 74) (W := 44438342) check rows elimOK (by decide) (by decide) cover22462 (by decide)
  decide +kernel

theorem h22462 : P.leaf 34 22462 = 105607680 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(446, 10650991), (296, 20057882), (208, 30460465), (74, 44438342)]) (.cons c22462_0 (.cons c22462_1 (.cons c22462_2 (.cons c22462_3 (.nil))))) (by decide) (by decide))

theorem cover22463 : P.CoversSplit 24 10 22463 0xfffffffffafa0000fffffffffafa0000ffffffff00000000ffff000000000000cccccccc88880000cccccccc88880000cccccccc00000000cccc000000000000fffffffffafa0000fffffffffafa0000fffffffffa000000ffff000000000000cccccccc88880000cccccccc8888000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [517, 860, 909, 916, 1202, 1210, 1217, 1251, 1308, 1601]) (by decide +kernel)

theorem c22463_0 : P.sumLeaves 24 23002112 404 = 12130926 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22463) (lo := 0) (len := 404) (W := 12130926) check rows elimOK (by decide) (by decide) cover22463 (by decide)
  decide +kernel

theorem c22463_1 : P.sumLeaves 24 23002516 210 = 53730647 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22463) (lo := 404) (len := 210) (W := 53730647) check rows elimOK (by decide) (by decide) cover22463 (by decide)
  decide +kernel

theorem c22463_2 : P.sumLeaves 24 23002726 276 = 55546600 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22463) (lo := 614) (len := 276) (W := 55546600) check rows elimOK (by decide) (by decide) cover22463 (by decide)
  decide +kernel

theorem c22463_3 : P.sumLeaves 24 23003002 134 = 133462388 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22463) (lo := 890) (len := 134) (W := 133462388) check rows elimOK (by decide) (by decide) cover22463 (by decide)
  decide +kernel

theorem h22463 : P.leaf 34 22463 = 254870561 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(404, 12130926), (210, 53730647), (276, 55546600), (134, 133462388)]) (.cons c22463_0 (.cons c22463_1 (.cons c22463_2 (.cons c22463_3 (.nil))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(22447, 48), (22460, 48), (22461, 48), (22462, 48), (22463, 48)]

theorem segOK : checkSeg 16 perms 22447 22508 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 22447 22508 240 29427477552 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 29427477552)
    (SegSum.cons (w := 48) h22447 (SegSum.cons (w := 48) h22460 (SegSum.cons (w := 48) h22461 (SegSum.cons (w := 48) h22462 (SegSum.cons (w := 48) h22463 (show SegSum (P.leaf 34) [] 0 from rfl)))))) (by decide)

end RACert.S4N1.C0.S80
