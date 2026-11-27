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

namespace RACert.S6N0.C0.S107

open RACert RACert.Problem

theorem cover131065 : P.CoversSplit 26 10 131065 0xfffffffffffffafafffffffffffffafafffffffffffffac8fafafafafac8fac8fffffafafffffafafafafafafafafafafffffafafffffac8fafafafafac8fac8fffffffffffffafafffffffffffffafaffffffffffccfac8fafafafafac8fac8fffffafafffffafafafafafafafafafafffffafaffccfac8fafafafafac8fac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c131065_0 : P.sumLeaves 26 134210560 135 = 49935024 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 131065) (lo := 0) (len := 135) (W := 49935024) check rows elimOK (by decide) (by decide) cover131065 (by decide)
  decide +kernel

theorem c131065_1 : P.sumLeaves 26 134210695 118 = 59039552 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 131065) (lo := 135) (len := 118) (W := 59039552) check rows elimOK (by decide) (by decide) cover131065 (by decide)
  decide +kernel

theorem c131065_2 : P.sumLeaves 26 134210813 129 = 233655028 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 131065) (lo := 253) (len := 129) (W := 233655028) check rows elimOK (by decide) (by decide) cover131065 (by decide)
  decide +kernel

theorem c131065_3 : P.sumLeaves 26 134210942 104 = 512083084 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 131065) (lo := 382) (len := 104) (W := 512083084) check rows elimOK (by decide) (by decide) cover131065 (by decide)
  decide +kernel

theorem c131065_4 : P.sumLeaves 26 134211046 127 = 470709684 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 131065) (lo := 486) (len := 127) (W := 470709684) check rows elimOK (by decide) (by decide) cover131065 (by decide)
  decide +kernel

theorem c131065_5 : P.sumLeaves 26 134211173 118 = 659384536 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 131065) (lo := 613) (len := 118) (W := 659384536) check rows elimOK (by decide) (by decide) cover131065 (by decide)
  decide +kernel

theorem c131065_6 : P.sumLeaves 26 134211291 129 = 675019954 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 131065) (lo := 731) (len := 129) (W := 675019954) check rows elimOK (by decide) (by decide) cover131065 (by decide)
  decide +kernel

theorem c131065_7 : P.sumLeaves 26 134211420 101 = 864700828 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 131065) (lo := 860) (len := 101) (W := 864700828) check rows elimOK (by decide) (by decide) cover131065 (by decide)
  decide +kernel

theorem c131065_8 : P.sumLeaves 26 134211521 63 = 764646780 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 131065) (lo := 961) (len := 63) (W := 764646780) check rows elimOK (by decide) (by decide) cover131065 (by decide)
  decide +kernel

theorem h131065 : P.leaf 36 131065 = 4289174470 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(135, 49935024), (118, 59039552), (129, 233655028), (104, 512083084), (127, 470709684), (118, 659384536), (129, 675019954), (101, 864700828), (63, 764646780)]) (.cons c131065_0 (.cons c131065_1 (.cons c131065_2 (.cons c131065_3 (.cons c131065_4 (.cons c131065_5 (.cons c131065_6 (.cons c131065_7 (.cons c131065_8 (.nil)))))))))) (by decide) (by decide))

theorem cover131067 : P.CoversSplit 26 10 131067 0xfffffffffffffafafffffffffffffafafffffffffffffac8fafafafafac8fac8fffffafafffffafafafafafafafafafafffffafafffffac8fafafafafac8fac8fffffffffffffafafffffffffffffafaffffffffffccfac8fafafafafac8fac8fffffafafffffafafafafafafafafafafffffafaffccfac8fafafafafac8fac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c131067_0 : P.sumLeaves 26 134212608 135 = 220769000 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 131067) (lo := 0) (len := 135) (W := 220769000) check rows elimOK (by decide) (by decide) cover131067 (by decide)
  decide +kernel

theorem c131067_1 : P.sumLeaves 26 134212743 118 = 275748072 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 131067) (lo := 135) (len := 118) (W := 275748072) check rows elimOK (by decide) (by decide) cover131067 (by decide)
  decide +kernel

theorem c131067_2 : P.sumLeaves 26 134212861 129 = 471161296 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 131067) (lo := 253) (len := 129) (W := 471161296) check rows elimOK (by decide) (by decide) cover131067 (by decide)
  decide +kernel

theorem c131067_3 : P.sumLeaves 26 134212990 104 = 704538756 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 131067) (lo := 382) (len := 104) (W := 704538756) check rows elimOK (by decide) (by decide) cover131067 (by decide)
  decide +kernel

theorem c131067_4 : P.sumLeaves 26 134213094 127 = 777389406 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 131067) (lo := 486) (len := 127) (W := 777389406) check rows elimOK (by decide) (by decide) cover131067 (by decide)
  decide +kernel

theorem c131067_5 : P.sumLeaves 26 134213221 118 = 1133419238 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 131067) (lo := 613) (len := 118) (W := 1133419238) check rows elimOK (by decide) (by decide) cover131067 (by decide)
  decide +kernel

theorem c131067_6 : P.sumLeaves 26 134213339 129 = 1145921862 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 131067) (lo := 731) (len := 129) (W := 1145921862) check rows elimOK (by decide) (by decide) cover131067 (by decide)
  decide +kernel

theorem c131067_7 : P.sumLeaves 26 134213468 101 = 1334473992 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 131067) (lo := 860) (len := 101) (W := 1334473992) check rows elimOK (by decide) (by decide) cover131067 (by decide)
  decide +kernel

theorem c131067_8 : P.sumLeaves 26 134213569 63 = 1080592312 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 131067) (lo := 961) (len := 63) (W := 1080592312) check rows elimOK (by decide) (by decide) cover131067 (by decide)
  decide +kernel

theorem h131067 : P.leaf 36 131067 = 7144013934 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(135, 220769000), (118, 275748072), (129, 471161296), (104, 704538756), (127, 777389406), (118, 1133419238), (129, 1145921862), (101, 1334473992), (63, 1080592312)]) (.cons c131067_0 (.cons c131067_1 (.cons c131067_2 (.cons c131067_3 (.cons c131067_4 (.cons c131067_5 (.cons c131067_6 (.cons c131067_7 (.cons c131067_8 (.nil)))))))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(131065, 180), (131067, 180)]

theorem segOK : checkSeg 20 perms 131065 131071 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 131065 131071 360 2057973912720 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 2057973912720)
    (SegSum.cons (w := 180) h131065 (SegSum.cons (w := 180) h131067 (show SegSum (P.leaf 36) [] 0 from rfl))) (by decide)

end RACert.S6N0.C0.S107
