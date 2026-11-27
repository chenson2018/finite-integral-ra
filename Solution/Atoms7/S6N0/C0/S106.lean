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

namespace RACert.S6N0.C0.S106

open RACert RACert.Problem

theorem cover131063 : P.CoversSplit 26 10 131063 0xfffffffffffffafafffffffffffffafafffffffffffffac8fafafafafac8fac8fffffafafffffafafafafafafafafafafffffafafffffac8fafafafafac8fac8fffffffffffffafafffffffffffffafaffffffffffccfac8fafafafafac8fac8fffffafafffffafafafafafafafafafafffffafaffccfac8fafafafafac8fac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c131063_0 : P.sumLeaves 26 134208512 135 = 220422976 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 131063) (lo := 0) (len := 135) (W := 220422976) check rows elimOK (by decide) (by decide) cover131063 (by decide)
  decide +kernel

theorem c131063_1 : P.sumLeaves 26 134208647 118 = 274462344 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 131063) (lo := 135) (len := 118) (W := 274462344) check rows elimOK (by decide) (by decide) cover131063 (by decide)
  decide +kernel

theorem c131063_2 : P.sumLeaves 26 134208765 129 = 568940898 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 131063) (lo := 253) (len := 129) (W := 568940898) check rows elimOK (by decide) (by decide) cover131063 (by decide)
  decide +kernel

theorem c131063_3 : P.sumLeaves 26 134208894 104 = 820794356 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 131063) (lo := 382) (len := 104) (W := 820794356) check rows elimOK (by decide) (by decide) cover131063 (by decide)
  decide +kernel

theorem c131063_4 : P.sumLeaves 26 134208998 127 = 748372316 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 131063) (lo := 486) (len := 127) (W := 748372316) check rows elimOK (by decide) (by decide) cover131063 (by decide)
  decide +kernel

theorem c131063_5 : P.sumLeaves 26 134209125 118 = 704322106 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 131063) (lo := 613) (len := 118) (W := 704322106) check rows elimOK (by decide) (by decide) cover131063 (by decide)
  decide +kernel

theorem c131063_6 : P.sumLeaves 26 134209243 129 = 882659870 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 131063) (lo := 731) (len := 129) (W := 882659870) check rows elimOK (by decide) (by decide) cover131063 (by decide)
  decide +kernel

theorem c131063_7 : P.sumLeaves 26 134209372 101 = 1024761040 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 131063) (lo := 860) (len := 101) (W := 1024761040) check rows elimOK (by decide) (by decide) cover131063 (by decide)
  decide +kernel

theorem c131063_8 : P.sumLeaves 26 134209473 63 = 835596064 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 131063) (lo := 961) (len := 63) (W := 835596064) check rows elimOK (by decide) (by decide) cover131063 (by decide)
  decide +kernel

theorem h131063 : P.leaf 36 131063 = 6080331970 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(135, 220422976), (118, 274462344), (129, 568940898), (104, 820794356), (127, 748372316), (118, 704322106), (129, 882659870), (101, 1024761040), (63, 835596064)]) (.cons c131063_0 (.cons c131063_1 (.cons c131063_2 (.cons c131063_3 (.cons c131063_4 (.cons c131063_5 (.cons c131063_6 (.cons c131063_7 (.cons c131063_8 (.nil)))))))))) (by decide) (by decide))

theorem cover131064 : P.CoversSplit 26 10 131064 0xfffffffffffffafafffffffffffffafafffffffffffffac8fafafafafac8fac8fafafafafafafafafafafafafafafafafafafafafafafac8fafafafafac8fac8fffffffffffffafafffffffffffffafaffffffffffccfac8fafafafafac8fac8fafafafafafafafafafafafafafafafafafafafafac8fac8fafafafafac8fac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c131064_0 : P.sumLeaves 26 134209536 145 = 9914160 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 131064) (lo := 0) (len := 145) (W := 9914160) check rows elimOK (by decide) (by decide) cover131064 (by decide)
  decide +kernel

theorem c131064_1 : P.sumLeaves 26 134209681 136 = 19438776 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 131064) (lo := 145) (len := 136) (W := 19438776) check rows elimOK (by decide) (by decide) cover131064 (by decide)
  decide +kernel

theorem c131064_2 : P.sumLeaves 26 134209817 120 = 152217932 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 131064) (lo := 281) (len := 120) (W := 152217932) check rows elimOK (by decide) (by decide) cover131064 (by decide)
  decide +kernel

theorem c131064_3 : P.sumLeaves 26 134209937 100 = 340269816 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 131064) (lo := 401) (len := 100) (W := 340269816) check rows elimOK (by decide) (by decide) cover131064 (by decide)
  decide +kernel

theorem c131064_4 : P.sumLeaves 26 134210037 137 = 258576108 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 131064) (lo := 501) (len := 137) (W := 258576108) check rows elimOK (by decide) (by decide) cover131064 (by decide)
  decide +kernel

theorem c131064_5 : P.sumLeaves 26 134210174 128 = 447446504 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 131064) (lo := 638) (len := 128) (W := 447446504) check rows elimOK (by decide) (by decide) cover131064 (by decide)
  decide +kernel

theorem c131064_6 : P.sumLeaves 26 134210302 125 = 283521644 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 131064) (lo := 766) (len := 125) (W := 283521644) check rows elimOK (by decide) (by decide) cover131064 (by decide)
  decide +kernel

theorem c131064_7 : P.sumLeaves 26 134210427 104 = 509114069 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 131064) (lo := 891) (len := 104) (W := 509114069) check rows elimOK (by decide) (by decide) cover131064 (by decide)
  decide +kernel

theorem c131064_8 : P.sumLeaves 26 134210531 29 = 306671257 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 131064) (lo := 995) (len := 29) (W := 306671257) check rows elimOK (by decide) (by decide) cover131064 (by decide)
  decide +kernel

theorem h131064 : P.leaf 36 131064 = 2327170266 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(145, 9914160), (136, 19438776), (120, 152217932), (100, 340269816), (137, 258576108), (128, 447446504), (125, 283521644), (104, 509114069), (29, 306671257)]) (.cons c131064_0 (.cons c131064_1 (.cons c131064_2 (.cons c131064_3 (.cons c131064_4 (.cons c131064_5 (.cons c131064_6 (.cons c131064_7 (.cons c131064_8 (.nil)))))))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(131063, 60), (131064, 60)]

theorem segOK : checkSeg 20 perms 131063 131065 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 131063 131065 120 504450134160 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 504450134160)
    (SegSum.cons (w := 60) h131063 (SegSum.cons (w := 60) h131064 (show SegSum (P.leaf 36) [] 0 from rfl))) (by decide)

end RACert.S6N0.C0.S106
