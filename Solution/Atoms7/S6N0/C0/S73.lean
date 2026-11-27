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

namespace RACert.S6N0.C0.S73

open RACert RACert.Problem

theorem cover90095 : P.CoversSplit 26 10 90095 0xfffffffffffcfaf8fffffffafffcfaf8fffffffffffcfac8fafafafac8c8c8c80000000000000000000000000000000000000000000000000000000000000000ffffffffffccfac8fffffffaffccfac8ffffffffcc00c800fafafafac800c8000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [922, 972, 979, 1266, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c90095_0 : P.sumLeaves 26 92257280 424 = 225496962 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90095) (lo := 0) (len := 424) (W := 225496962) check rows elimOK (by decide) (by decide) cover90095 (by decide)
  decide +kernel

theorem c90095_1 : P.sumLeaves 26 92257704 387 = 346914580 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90095) (lo := 424) (len := 387) (W := 346914580) check rows elimOK (by decide) (by decide) cover90095 (by decide)
  decide +kernel

theorem c90095_2 : P.sumLeaves 26 92258091 116 = 505824282 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90095) (lo := 811) (len := 116) (W := 505824282) check rows elimOK (by decide) (by decide) cover90095 (by decide)
  decide +kernel

theorem c90095_3 : P.sumLeaves 26 92258207 97 = 647564493 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90095) (lo := 927) (len := 97) (W := 647564493) check rows elimOK (by decide) (by decide) cover90095 (by decide)
  decide +kernel

theorem h90095 : P.leaf 36 90095 = 1725800317 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(424, 225496962), (387, 346914580), (116, 505824282), (97, 647564493)]) (.cons c90095_0 (.cons c90095_1 (.cons c90095_2 (.cons c90095_3 (.nil))))) (by decide) (by decide))

theorem cover90110 : P.CoversSplit 26 10 90110 0xfffffffffffcfaf8fffffffafffcfaf8fffffffffffcfac8fafafafac8c8c8c8fffffafafffcfaf8fafafafafaf8faf8fffffafafffcfac8fafafafac8c8c8c8ffffffffffccfac8fffffffaffccfac8ffffffffccccc8c8fafafafac8c8c8c80000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [874, 922, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c90110_0 : P.sumLeaves 26 92272640 409 = 194974236 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90110) (lo := 0) (len := 409) (W := 194974236) check rows elimOK (by decide) (by decide) cover90110 (by decide)
  decide +kernel

theorem c90110_1 : P.sumLeaves 26 92273049 122 = 394861714 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90110) (lo := 409) (len := 122) (W := 394861714) check rows elimOK (by decide) (by decide) cover90110 (by decide)
  decide +kernel

theorem c90110_2 : P.sumLeaves 26 92273171 132 = 240439651 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90110) (lo := 531) (len := 132) (W := 240439651) check rows elimOK (by decide) (by decide) cover90110 (by decide)
  decide +kernel

theorem c90110_3 : P.sumLeaves 26 92273303 138 = 371408399 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90110) (lo := 663) (len := 138) (W := 371408399) check rows elimOK (by decide) (by decide) cover90110 (by decide)
  decide +kernel

theorem c90110_4 : P.sumLeaves 26 92273441 119 = 467284186 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90110) (lo := 801) (len := 119) (W := 467284186) check rows elimOK (by decide) (by decide) cover90110 (by decide)
  decide +kernel

theorem c90110_5 : P.sumLeaves 26 92273560 104 = 730633320 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90110) (lo := 920) (len := 104) (W := 730633320) check rows elimOK (by decide) (by decide) cover90110 (by decide)
  decide +kernel

theorem h90110 : P.leaf 36 90110 = 2399601506 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(409, 194974236), (122, 394861714), (132, 240439651), (138, 371408399), (119, 467284186), (104, 730633320)]) (.cons c90110_0 (.cons c90110_1 (.cons c90110_2 (.cons c90110_3 (.cons c90110_4 (.cons c90110_5 (.nil))))))) (by decide) (by decide))

theorem cover90111 : P.CoversSplit 26 10 90111 0xfffffffffffcfaf8fffffffafffcfaf8fffffffffffcfac8fafafafac8c8c8c8fffffafafffcfaf8fafafafafaf8faf8fffffafafffcfac8fafafafac8c8c8c8ffffffffffccfac8fffffffaffccfac8ffffffffccccc8c8fafafafac8c8c8c8fffffafaffccfac8fafafafafac8fac8fffffafaccccc8c8fafafafac8c8c8c8 :=
  coversSplit check rows (by decide) (by decide) (xs := [922, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c90111_0 : P.sumLeaves 26 92273664 161 = 8831583 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90111) (lo := 0) (len := 161) (W := 8831583) check rows elimOK (by decide) (by decide) cover90111 (by decide)
  decide +kernel

theorem c90111_1 : P.sumLeaves 26 92273825 142 = 119639126 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90111) (lo := 161) (len := 142) (W := 119639126) check rows elimOK (by decide) (by decide) cover90111 (by decide)
  decide +kernel

theorem c90111_2 : P.sumLeaves 26 92273967 131 = 528653815 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90111) (lo := 303) (len := 131) (W := 528653815) check rows elimOK (by decide) (by decide) cover90111 (by decide)
  decide +kernel

theorem c90111_3 : P.sumLeaves 26 92274098 133 = 646322620 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90111) (lo := 434) (len := 133) (W := 646322620) check rows elimOK (by decide) (by decide) cover90111 (by decide)
  decide +kernel

theorem c90111_4 : P.sumLeaves 26 92274231 127 = 534791261 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90111) (lo := 567) (len := 127) (W := 534791261) check rows elimOK (by decide) (by decide) cover90111 (by decide)
  decide +kernel

theorem c90111_5 : P.sumLeaves 26 92274358 137 = 817276292 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90111) (lo := 694) (len := 137) (W := 817276292) check rows elimOK (by decide) (by decide) cover90111 (by decide)
  decide +kernel

theorem c90111_6 : P.sumLeaves 26 92274495 114 = 953762416 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90111) (lo := 831) (len := 114) (W := 953762416) check rows elimOK (by decide) (by decide) cover90111 (by decide)
  decide +kernel

theorem c90111_7 : P.sumLeaves 26 92274609 79 = 1010876590 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90111) (lo := 945) (len := 79) (W := 1010876590) check rows elimOK (by decide) (by decide) cover90111 (by decide)
  decide +kernel

theorem h90111 : P.leaf 36 90111 = 4620153703 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(161, 8831583), (142, 119639126), (131, 528653815), (133, 646322620), (127, 534791261), (137, 817276292), (114, 953762416), (79, 1010876590)]) (.cons c90111_0 (.cons c90111_1 (.cons c90111_2 (.cons c90111_3 (.cons c90111_4 (.cons c90111_5 (.cons c90111_6 (.cons c90111_7 (.nil))))))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(90095, 720), (90110, 360), (90111, 360)]

theorem segOK : checkSeg 20 perms 90095 96741 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 90095 96741 1440 3769688103480 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 3769688103480)
    (SegSum.cons (w := 720) h90095 (SegSum.cons (w := 360) h90110 (SegSum.cons (w := 360) h90111 (show SegSum (P.leaf 36) [] 0 from rfl)))) (by decide)

end RACert.S6N0.C0.S73
