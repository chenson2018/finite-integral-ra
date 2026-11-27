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

namespace RACert.S6N0.C0.S40

open RACert RACert.Problem

theorem cover65520 : P.CoversSplit 26 10 65520 0xfac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489]) (by decide +kernel)

theorem c65520_0 : P.sumLeaves 26 67092480 173 = 2029972 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 65520) (lo := 0) (len := 173) (W := 2029972) check rows elimOK (by decide) (by decide) cover65520 (by decide)
  decide +kernel

theorem c65520_1 : P.sumLeaves 26 67092653 172 = 2425376 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 65520) (lo := 173) (len := 172) (W := 2425376) check rows elimOK (by decide) (by decide) cover65520 (by decide)
  decide +kernel

theorem c65520_2 : P.sumLeaves 26 67092825 170 = 2816096 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 65520) (lo := 345) (len := 170) (W := 2816096) check rows elimOK (by decide) (by decide) cover65520 (by decide)
  decide +kernel

theorem c65520_3 : P.sumLeaves 26 67092995 170 = 2425944 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 65520) (lo := 515) (len := 170) (W := 2425944) check rows elimOK (by decide) (by decide) cover65520 (by decide)
  decide +kernel

theorem c65520_4 : P.sumLeaves 26 67093165 172 = 2837720 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 65520) (lo := 685) (len := 172) (W := 2837720) check rows elimOK (by decide) (by decide) cover65520 (by decide)
  decide +kernel

theorem c65520_5 : P.sumLeaves 26 67093337 167 = 3075040 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 65520) (lo := 857) (len := 167) (W := 3075040) check rows elimOK (by decide) (by decide) cover65520 (by decide)
  decide +kernel

theorem h65520 : P.leaf 36 65520 = 15610148 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(173, 2029972), (172, 2425376), (170, 2816096), (170, 2425944), (172, 2837720), (167, 3075040)]) (.cons c65520_0 (.cons c65520_1 (.cons c65520_2 (.cons c65520_3 (.cons c65520_4 (.cons c65520_5 (.nil))))))) (by decide) (by decide))

theorem cover65521 : P.CoversSplit 26 10 65521 0xfffffafaffccfac8fffffafaffccfac8fffffafaffccfac8fac8fac8fac8fac8fffffafaffccfac8fafafafafac8fac8fffffafaffccfac8fac8fac8fac8fac8fffffafaffccfac8fffffafaffccfac8ffccfac8ffccfac8fac8fac8fac8fac8fffffafaffccfac8fafafafafac8fac8ffccfac8ffccfac8fac8fac8fac8fac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 1658, 1665]) (by decide +kernel)

theorem c65521_0 : P.sumLeaves 26 67093504 161 = 12435390 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 65521) (lo := 0) (len := 161) (W := 12435390) check rows elimOK (by decide) (by decide) cover65521 (by decide)
  decide +kernel

theorem c65521_1 : P.sumLeaves 26 67093665 139 = 18570456 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 65521) (lo := 161) (len := 139) (W := 18570456) check rows elimOK (by decide) (by decide) cover65521 (by decide)
  decide +kernel

theorem c65521_2 : P.sumLeaves 26 67093804 140 = 96275526 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 65521) (lo := 300) (len := 140) (W := 96275526) check rows elimOK (by decide) (by decide) cover65521 (by decide)
  decide +kernel

theorem c65521_3 : P.sumLeaves 26 67093944 145 = 158860327 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 65521) (lo := 440) (len := 145) (W := 158860327) check rows elimOK (by decide) (by decide) cover65521 (by decide)
  decide +kernel

theorem c65521_4 : P.sumLeaves 26 67094089 134 = 104150727 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 65521) (lo := 585) (len := 134) (W := 104150727) check rows elimOK (by decide) (by decide) cover65521 (by decide)
  decide +kernel

theorem c65521_5 : P.sumLeaves 26 67094223 143 = 160167428 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 65521) (lo := 719) (len := 143) (W := 160167428) check rows elimOK (by decide) (by decide) cover65521 (by decide)
  decide +kernel

theorem c65521_6 : P.sumLeaves 26 67094366 126 = 161935032 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 65521) (lo := 862) (len := 126) (W := 161935032) check rows elimOK (by decide) (by decide) cover65521 (by decide)
  decide +kernel

theorem c65521_7 : P.sumLeaves 26 67094492 36 = 129104524 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 65521) (lo := 988) (len := 36) (W := 129104524) check rows elimOK (by decide) (by decide) cover65521 (by decide)
  decide +kernel

theorem h65521 : P.leaf 36 65521 = 841499410 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(161, 12435390), (139, 18570456), (140, 96275526), (145, 158860327), (134, 104150727), (143, 160167428), (126, 161935032), (36, 129104524)]) (.cons c65521_0 (.cons c65521_1 (.cons c65521_2 (.cons c65521_3 (.cons c65521_4 (.cons c65521_5 (.cons c65521_6 (.cons c65521_7 (.nil))))))))) (by decide) (by decide))

theorem cover65523 : P.CoversSplit 26 10 65523 0xfffffffffffffac8fffffafafffffac8ffffffffffccfac8fac8fac8fac8fac8fffffafafffffac8fafafafafafafac8fffffafaffccfac8fac8fac8fac8fac8ffffffffffccfac8fffffafaffccfac8ffccffccffccfac8fac8fac8fac8fac8fffffafaffccfac8fafafafafac8fac8ffccfac8ffccfac8fac8fac8fac8fac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c65523_0 : P.sumLeaves 26 67095552 161 = 60131984 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 65523) (lo := 0) (len := 161) (W := 60131984) check rows elimOK (by decide) (by decide) cover65523 (by decide)
  decide +kernel

theorem c65523_1 : P.sumLeaves 26 67095713 139 = 73867096 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 65523) (lo := 161) (len := 139) (W := 73867096) check rows elimOK (by decide) (by decide) cover65523 (by decide)
  decide +kernel

theorem c65523_2 : P.sumLeaves 26 67095852 137 = 213547356 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 65523) (lo := 300) (len := 137) (W := 213547356) check rows elimOK (by decide) (by decide) cover65523 (by decide)
  decide +kernel

theorem c65523_3 : P.sumLeaves 26 67095989 135 = 299703976 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 65523) (lo := 437) (len := 135) (W := 299703976) check rows elimOK (by decide) (by decide) cover65523 (by decide)
  decide +kernel

theorem c65523_4 : P.sumLeaves 26 67096124 130 = 222274844 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 65523) (lo := 572) (len := 130) (W := 222274844) check rows elimOK (by decide) (by decide) cover65523 (by decide)
  decide +kernel

theorem c65523_5 : P.sumLeaves 26 67096254 142 = 315845912 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 65523) (lo := 702) (len := 142) (W := 315845912) check rows elimOK (by decide) (by decide) cover65523 (by decide)
  decide +kernel

theorem c65523_6 : P.sumLeaves 26 67096396 111 = 293086936 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 65523) (lo := 844) (len := 111) (W := 293086936) check rows elimOK (by decide) (by decide) cover65523 (by decide)
  decide +kernel

theorem c65523_7 : P.sumLeaves 26 67096507 69 = 337264848 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 65523) (lo := 955) (len := 69) (W := 337264848) check rows elimOK (by decide) (by decide) cover65523 (by decide)
  decide +kernel

theorem h65523 : P.leaf 36 65523 = 1815722952 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(161, 60131984), (139, 73867096), (137, 213547356), (135, 299703976), (130, 222274844), (142, 315845912), (111, 293086936), (69, 337264848)]) (.cons c65523_0 (.cons c65523_1 (.cons c65523_2 (.cons c65523_3 (.cons c65523_4 (.cons c65523_5 (.cons c65523_6 (.cons c65523_7 (.nil))))))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(65520, 15), (65521, 60), (65523, 90)]

theorem segOK : checkSeg 20 perms 65520 65527 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 65520 65527 165 214139182500 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 214139182500)
    (SegSum.cons (w := 15) h65520 (SegSum.cons (w := 60) h65521 (SegSum.cons (w := 90) h65523 (show SegSum (P.leaf 36) [] 0 from rfl)))) (by decide)

end RACert.S6N0.C0.S40
