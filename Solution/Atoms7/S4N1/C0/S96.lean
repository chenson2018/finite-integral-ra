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

namespace RACert.S4N1.C0.S96

open RACert RACert.Problem

theorem cover24508 : P.CoversSplit 24 10 24508 0xffaaffaafaaaa0a0ffaaffaafaaaa0a0ffaaffaafaaaa0a0ffaaffaafaaaa0a0cc88cc8888888080cc88cc8888888080cc88cc8888888080cc88cc8888888080ff00ff00fa00a000ff22ff22fa22a020ff00ff00fa00a000ff22ff22fa22a0200000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 508, 916, 1202, 1210, 1308, 1601]) (by decide +kernel)

theorem c24508_0 : P.sumLeaves 24 25096192 490 = 26786567 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24508) (lo := 0) (len := 490) (W := 26786567) check rows elimOK (by decide) (by decide) cover24508 (by decide)
  decide +kernel

theorem c24508_1 : P.sumLeaves 24 25096682 306 = 33937073 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24508) (lo := 490) (len := 306) (W := 33937073) check rows elimOK (by decide) (by decide) cover24508 (by decide)
  decide +kernel

theorem c24508_2 : P.sumLeaves 24 25096988 156 = 62677958 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24508) (lo := 796) (len := 156) (W := 62677958) check rows elimOK (by decide) (by decide) cover24508 (by decide)
  decide +kernel

theorem c24508_3 : P.sumLeaves 24 25097144 72 = 73122696 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24508) (lo := 952) (len := 72) (W := 73122696) check rows elimOK (by decide) (by decide) cover24508 (by decide)
  decide +kernel

theorem h24508 : P.leaf 34 24508 = 196524294 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(490, 26786567), (306, 33937073), (156, 62677958), (72, 73122696)]) (.cons c24508_0 (.cons c24508_1 (.cons c24508_2 (.cons c24508_3 (.nil))))) (by decide) (by decide))

theorem cover24509 : P.CoversSplit 24 10 24509 0xfffffffffafaa0a0fffffffffafaa0a0fffffffffafaa0a0fffffffffafaa0a0cccccccc88888080cccccccc88888080cccccccc88888080cccccccc88888080ff00ff00fa00a000ff33ff33fa32a020ff00ff00fa00a000ff33ff33fa22a0200000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 517, 916, 1202, 1210, 1259, 1308, 1601]) (ps := [(14, [1217], [916])]) (by decide +kernel)

theorem c24509_0 : P.sumLeaves 24 25097216 463 = 43970027 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24509) (lo := 0) (len := 463) (W := 43970027) check rows elimOK (by decide) (by decide) cover24509 (by decide)
  decide +kernel

theorem c24509_1 : P.sumLeaves 24 25097679 276 = 53154822 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24509) (lo := 463) (len := 276) (W := 53154822) check rows elimOK (by decide) (by decide) cover24509 (by decide)
  decide +kernel

theorem c24509_2 : P.sumLeaves 24 25097955 142 = 81025459 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24509) (lo := 739) (len := 142) (W := 81025459) check rows elimOK (by decide) (by decide) cover24509 (by decide)
  decide +kernel

theorem c24509_3 : P.sumLeaves 24 25098097 128 = 157096046 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24509) (lo := 881) (len := 128) (W := 157096046) check rows elimOK (by decide) (by decide) cover24509 (by decide)
  decide +kernel

theorem c24509_4 : P.sumLeaves 24 25098225 15 = 37336386 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24509) (lo := 1009) (len := 15) (W := 37336386) check rows elimOK (by decide) (by decide) cover24509 (by decide)
  decide +kernel

theorem h24509 : P.leaf 34 24509 = 372582740 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(463, 43970027), (276, 53154822), (142, 81025459), (128, 157096046), (15, 37336386)]) (.cons c24509_0 (.cons c24509_1 (.cons c24509_2 (.cons c24509_3 (.cons c24509_4 (.nil)))))) (by decide) (by decide))

theorem cover24510 : P.CoversSplit 24 10 24510 0xfffffffffafaa0a0fffffffffafaa0a0fffffffffafaa0a0fffffffffafaa0a0cccccccc88888080cccccccc88888080cccccccc88888080cccccccc88888080fffffffffafaa0a0fffffffffafaa0a0fffffffffafaa0a0fffffffffafaa0a0cccccccc88888080cccccccc8888808000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 916, 1202, 1210, 1259, 1308, 1601]) (by decide +kernel)

theorem c24510_0 : P.sumLeaves 24 25098240 337 = 18158578 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24510) (lo := 0) (len := 337) (W := 18158578) check rows elimOK (by decide) (by decide) cover24510 (by decide)
  decide +kernel

theorem c24510_1 : P.sumLeaves 24 25098577 128 = 51981538 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24510) (lo := 337) (len := 128) (W := 51981538) check rows elimOK (by decide) (by decide) cover24510 (by decide)
  decide +kernel

theorem c24510_2 : P.sumLeaves 24 25098705 213 = 55372197 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24510) (lo := 465) (len := 213) (W := 55372197) check rows elimOK (by decide) (by decide) cover24510 (by decide)
  decide +kernel

theorem c24510_3 : P.sumLeaves 24 25098918 182 = 72009035 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24510) (lo := 678) (len := 182) (W := 72009035) check rows elimOK (by decide) (by decide) cover24510 (by decide)
  decide +kernel

theorem c24510_4 : P.sumLeaves 24 25099100 128 = 154318211 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24510) (lo := 860) (len := 128) (W := 154318211) check rows elimOK (by decide) (by decide) cover24510 (by decide)
  decide +kernel

theorem c24510_5 : P.sumLeaves 24 25099228 36 = 96561020 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24510) (lo := 988) (len := 36) (W := 96561020) check rows elimOK (by decide) (by decide) cover24510 (by decide)
  decide +kernel

theorem h24510 : P.leaf 34 24510 = 448400579 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(337, 18158578), (128, 51981538), (213, 55372197), (182, 72009035), (128, 154318211), (36, 96561020)]) (.cons c24510_0 (.cons c24510_1 (.cons c24510_2 (.cons c24510_3 (.cons c24510_4 (.cons c24510_5 (.nil))))))) (by decide) (by decide))

theorem cover24511 : P.CoversSplit 24 10 24511 0xfffffffffafaa0a0fffffffffafaa0a0fffffffffafaa0a0fffffffffafaa0a0cccccccc88888080cccccccc88888080cccccccc88888080cccccccc88888080fffffffffafaa0a0fffffffffafaa0a0fffffffffafaa0a0fffffffffafaa0a0cccccccc88888080cccccccc8888808000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [517, 916, 1202, 1210, 1259, 1308, 1601]) (by decide +kernel)

theorem c24511_0 : P.sumLeaves 24 25099264 337 = 33349657 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24511) (lo := 0) (len := 337) (W := 33349657) check rows elimOK (by decide) (by decide) cover24511 (by decide)
  decide +kernel

theorem c24511_1 : P.sumLeaves 24 25099601 128 = 84207562 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24511) (lo := 337) (len := 128) (W := 84207562) check rows elimOK (by decide) (by decide) cover24511 (by decide)
  decide +kernel

theorem c24511_2 : P.sumLeaves 24 25099729 213 = 82767012 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24511) (lo := 465) (len := 213) (W := 82767012) check rows elimOK (by decide) (by decide) cover24511 (by decide)
  decide +kernel

theorem c24511_3 : P.sumLeaves 24 25099942 182 = 130285849 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24511) (lo := 678) (len := 182) (W := 130285849) check rows elimOK (by decide) (by decide) cover24511 (by decide)
  decide +kernel

theorem c24511_4 : P.sumLeaves 24 25100124 128 = 242909644 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24511) (lo := 860) (len := 128) (W := 242909644) check rows elimOK (by decide) (by decide) cover24511 (by decide)
  decide +kernel

theorem c24511_5 : P.sumLeaves 24 25100252 36 = 131741622 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24511) (lo := 988) (len := 36) (W := 131741622) check rows elimOK (by decide) (by decide) cover24511 (by decide)
  decide +kernel

theorem h24511 : P.leaf 34 24511 = 705261346 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(337, 33349657), (128, 84207562), (213, 82767012), (182, 130285849), (128, 242909644), (36, 131741622)]) (.cons c24511_0 (.cons c24511_1 (.cons c24511_2 (.cons c24511_3 (.cons c24511_4 (.cons c24511_5 (.nil))))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(24508, 48), (24509, 48), (24510, 48), (24511, 48)]

theorem segOK : checkSeg 16 perms 24508 24539 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 24508 24539 192 82692910032 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 82692910032)
    (SegSum.cons (w := 48) h24508 (SegSum.cons (w := 48) h24509 (SegSum.cons (w := 48) h24510 (SegSum.cons (w := 48) h24511 (show SegSum (P.leaf 34) [] 0 from rfl))))) (by decide)

end RACert.S4N1.C0.S96
