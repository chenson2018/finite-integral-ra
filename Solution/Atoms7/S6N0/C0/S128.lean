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

namespace RACert.S6N0.C0.S128

open RACert RACert.Problem

theorem cover243695 : P.CoversSplit 26 10 243695 0xfffffffffffffffffffffffffffffafaffffffffffffccccffffaaaaffcc8888ffffffffffffffffffffaaaaffffaaaaffffffffffffccccffffaaaaffcc8888fffffffffffffffffffffffffffffafaffffffffccccccccffffaaaacccc8888ffffffffffffffffffffaaaaffffaaaaffffffffccccccccffffaaaacccc8888 :=
  coversSplit check rows (by decide) (by decide) (xs := [873, 930, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c243695_0 : P.sumLeaves 26 249543680 148 = 185974559 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243695) (lo := 0) (len := 148) (W := 185974559) check rows elimOK (by decide) (by decide) cover243695 (by decide)
  decide +kernel

theorem c243695_1 : P.sumLeaves 26 249543828 104 = 428726840 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243695) (lo := 148) (len := 104) (W := 428726840) check rows elimOK (by decide) (by decide) cover243695 (by decide)
  decide +kernel

theorem c243695_2 : P.sumLeaves 26 249543932 144 = 389651619 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243695) (lo := 252) (len := 144) (W := 389651619) check rows elimOK (by decide) (by decide) cover243695 (by decide)
  decide +kernel

theorem c243695_3 : P.sumLeaves 26 249544076 96 = 812415403 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243695) (lo := 396) (len := 96) (W := 812415403) check rows elimOK (by decide) (by decide) cover243695 (by decide)
  decide +kernel

theorem c243695_4 : P.sumLeaves 26 249544172 128 = 580770901 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243695) (lo := 492) (len := 128) (W := 580770901) check rows elimOK (by decide) (by decide) cover243695 (by decide)
  decide +kernel

theorem c243695_5 : P.sumLeaves 26 249544300 112 = 754211471 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243695) (lo := 620) (len := 112) (W := 754211471) check rows elimOK (by decide) (by decide) cover243695 (by decide)
  decide +kernel

theorem c243695_6 : P.sumLeaves 26 249544412 128 = 753150850 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243695) (lo := 732) (len := 128) (W := 753150850) check rows elimOK (by decide) (by decide) cover243695 (by decide)
  decide +kernel

theorem c243695_7 : P.sumLeaves 26 249544540 100 = 952901862 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243695) (lo := 860) (len := 100) (W := 952901862) check rows elimOK (by decide) (by decide) cover243695 (by decide)
  decide +kernel

theorem c243695_8 : P.sumLeaves 26 249544640 64 = 909648060 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243695) (lo := 960) (len := 64) (W := 909648060) check rows elimOK (by decide) (by decide) cover243695 (by decide)
  decide +kernel

theorem h243695 : P.leaf 36 243695 = 5767451565 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(148, 185974559), (104, 428726840), (144, 389651619), (96, 812415403), (128, 580770901), (112, 754211471), (128, 753150850), (100, 952901862), (64, 909648060)]) (.cons c243695_0 (.cons c243695_1 (.cons c243695_2 (.cons c243695_3 (.cons c243695_4 (.cons c243695_5 (.cons c243695_6 (.cons c243695_7 (.cons c243695_8 (.nil)))))))))) (by decide) (by decide))

theorem cover243699 : P.CoversSplit 26 10 243699 0xfffffffffffffffffffffafafffffafaffffffffffccccccffffaaaaffcc8888ffffffffffffffffffffaaaaffffaaaaffffffffffccccccffffaaaaffcc8888fffffffffffffffffffffafafffffafaffffffffccccccccffffaaaacccc8888ffffffffffffffffffffaaaaffffaaaaffffffffccccccccffffaaaacccc8888 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 1322, 1658]) (by decide +kernel)

theorem c243699_0 : P.sumLeaves 26 249547776 148 = 14268097 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243699) (lo := 0) (len := 148) (W := 14268097) check rows elimOK (by decide) (by decide) cover243699 (by decide)
  decide +kernel

theorem c243699_1 : P.sumLeaves 26 249547924 104 = 36398397 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243699) (lo := 148) (len := 104) (W := 36398397) check rows elimOK (by decide) (by decide) cover243699 (by decide)
  decide +kernel

theorem c243699_2 : P.sumLeaves 26 249548028 144 = 128058826 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243699) (lo := 252) (len := 144) (W := 128058826) check rows elimOK (by decide) (by decide) cover243699 (by decide)
  decide +kernel

theorem c243699_3 : P.sumLeaves 26 249548172 100 = 303888620 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243699) (lo := 396) (len := 100) (W := 303888620) check rows elimOK (by decide) (by decide) cover243699 (by decide)
  decide +kernel

theorem c243699_4 : P.sumLeaves 26 249548272 132 = 209106676 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243699) (lo := 496) (len := 132) (W := 209106676) check rows elimOK (by decide) (by decide) cover243699 (by decide)
  decide +kernel

theorem c243699_5 : P.sumLeaves 26 249548404 112 = 281273506 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243699) (lo := 628) (len := 112) (W := 281273506) check rows elimOK (by decide) (by decide) cover243699 (by decide)
  decide +kernel

theorem c243699_6 : P.sumLeaves 26 249548516 132 = 273163644 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243699) (lo := 740) (len := 132) (W := 273163644) check rows elimOK (by decide) (by decide) cover243699 (by decide)
  decide +kernel

theorem c243699_7 : P.sumLeaves 26 249548648 104 = 406837418 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243699) (lo := 872) (len := 104) (W := 406837418) check rows elimOK (by decide) (by decide) cover243699 (by decide)
  decide +kernel

theorem c243699_8 : P.sumLeaves 26 249548752 48 = 307178390 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243699) (lo := 976) (len := 48) (W := 307178390) check rows elimOK (by decide) (by decide) cover243699 (by decide)
  decide +kernel

theorem h243699 : P.leaf 36 243699 = 1960173574 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(148, 14268097), (104, 36398397), (144, 128058826), (100, 303888620), (132, 209106676), (112, 281273506), (132, 273163644), (104, 406837418), (48, 307178390)]) (.cons c243699_0 (.cons c243699_1 (.cons c243699_2 (.cons c243699_3 (.cons c243699_4 (.cons c243699_5 (.cons c243699_6 (.cons c243699_7 (.cons c243699_8 (.nil)))))))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(243695, 360), (243699, 120)]

theorem segOK : checkSeg 20 perms 243695 243702 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 243695 243702 480 2311503392280 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 2311503392280)
    (SegSum.cons (w := 360) h243695 (SegSum.cons (w := 120) h243699 (show SegSum (P.leaf 36) [] 0 from rfl))) (by decide)

end RACert.S6N0.C0.S128
