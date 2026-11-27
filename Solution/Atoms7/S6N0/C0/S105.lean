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

namespace RACert.S6N0.C0.S105

open RACert RACert.Problem

theorem cover131056 : P.CoversSplit 26 10 131056 0xfac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489]) (by decide +kernel)

theorem c131056_0 : P.sumLeaves 26 134201344 173 = 2029520 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 131056) (lo := 0) (len := 173) (W := 2029520) check rows elimOK (by decide) (by decide) cover131056 (by decide)
  decide +kernel

theorem c131056_1 : P.sumLeaves 26 134201517 172 = 2450928 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 131056) (lo := 173) (len := 172) (W := 2450928) check rows elimOK (by decide) (by decide) cover131056 (by decide)
  decide +kernel

theorem c131056_2 : P.sumLeaves 26 134201689 170 = 3045904 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 131056) (lo := 345) (len := 170) (W := 3045904) check rows elimOK (by decide) (by decide) cover131056 (by decide)
  decide +kernel

theorem c131056_3 : P.sumLeaves 26 134201859 170 = 2537304 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 131056) (lo := 515) (len := 170) (W := 2537304) check rows elimOK (by decide) (by decide) cover131056 (by decide)
  decide +kernel

theorem c131056_4 : P.sumLeaves 26 134202029 172 = 3141664 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 131056) (lo := 685) (len := 172) (W := 3141664) check rows elimOK (by decide) (by decide) cover131056 (by decide)
  decide +kernel

theorem c131056_5 : P.sumLeaves 26 134202201 167 = 3647888 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 131056) (lo := 857) (len := 167) (W := 3647888) check rows elimOK (by decide) (by decide) cover131056 (by decide)
  decide +kernel

theorem h131056 : P.leaf 36 131056 = 16853208 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(173, 2029520), (172, 2450928), (170, 3045904), (170, 2537304), (172, 3141664), (167, 3647888)]) (.cons c131056_0 (.cons c131056_1 (.cons c131056_2 (.cons c131056_3 (.cons c131056_4 (.cons c131056_5 (.nil))))))) (by decide) (by decide))

theorem cover131057 : P.CoversSplit 26 10 131057 0xfffffafaffccfac8fffffafaffccfac8fffffafaffccfac8fafafafafac8fac8fffffafaffccfac8fafafafafac8fac8fffffafaffccfac8fafafafafac8fac8fffffafaffccfac8fffffafaffccfac8fffffafaffccfac8fafafafafac8fac8fffffafaffccfac8fafafafafac8fac8fffffafaffccfac8fafafafafac8fac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 1658]) (by decide +kernel)

theorem c131057_0 : P.sumLeaves 26 134202368 140 = 11014020 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 131057) (lo := 0) (len := 140) (W := 11014020) check rows elimOK (by decide) (by decide) cover131057 (by decide)
  decide +kernel

theorem c131057_1 : P.sumLeaves 26 134202508 138 = 19655250 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 131057) (lo := 140) (len := 138) (W := 19655250) check rows elimOK (by decide) (by decide) cover131057 (by decide)
  decide +kernel

theorem c131057_2 : P.sumLeaves 26 134202646 132 = 157219538 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 131057) (lo := 278) (len := 132) (W := 157219538) check rows elimOK (by decide) (by decide) cover131057 (by decide)
  decide +kernel

theorem c131057_3 : P.sumLeaves 26 134202778 129 = 368657646 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 131057) (lo := 410) (len := 129) (W := 368657646) check rows elimOK (by decide) (by decide) cover131057 (by decide)
  decide +kernel

theorem c131057_4 : P.sumLeaves 26 134202907 134 = 210038816 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 131057) (lo := 539) (len := 134) (W := 210038816) check rows elimOK (by decide) (by decide) cover131057 (by decide)
  decide +kernel

theorem c131057_5 : P.sumLeaves 26 134203041 134 = 403257136 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 131057) (lo := 673) (len := 134) (W := 403257136) check rows elimOK (by decide) (by decide) cover131057 (by decide)
  decide +kernel

theorem c131057_6 : P.sumLeaves 26 134203175 132 = 329205278 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 131057) (lo := 807) (len := 132) (W := 329205278) check rows elimOK (by decide) (by decide) cover131057 (by decide)
  decide +kernel

theorem c131057_7 : P.sumLeaves 26 134203307 85 = 523671910 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 131057) (lo := 939) (len := 85) (W := 523671910) check rows elimOK (by decide) (by decide) cover131057 (by decide)
  decide +kernel

theorem h131057 : P.leaf 36 131057 = 2022719594 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(140, 11014020), (138, 19655250), (132, 157219538), (129, 368657646), (134, 210038816), (134, 403257136), (132, 329205278), (85, 523671910)]) (.cons c131057_0 (.cons c131057_1 (.cons c131057_2 (.cons c131057_3 (.cons c131057_4 (.cons c131057_5 (.cons c131057_6 (.cons c131057_7 (.nil))))))))) (by decide) (by decide))

theorem cover131059 : P.CoversSplit 26 10 131059 0xfffffffffffffafafffffafafffffafaffffffffffccfac8fafafafafac8fac8fffffafafffffafafafafafafafafafafffffafaffccfac8fafafafafac8fac8fffffffffffffafafffffafafffffafaffffffffffccfac8fafafafafac8fac8fffffafafffffafafafafafafafafafafffffafaffccfac8fafafafafac8fac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 1315, 1658]) (by decide +kernel)

theorem c131059_0 : P.sumLeaves 26 134204416 135 = 51159040 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 131059) (lo := 0) (len := 135) (W := 51159040) check rows elimOK (by decide) (by decide) cover131059 (by decide)
  decide +kernel

theorem c131059_1 : P.sumLeaves 26 134204551 118 = 66298208 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 131059) (lo := 135) (len := 118) (W := 66298208) check rows elimOK (by decide) (by decide) cover131059 (by decide)
  decide +kernel

theorem c131059_2 : P.sumLeaves 26 134204669 129 = 260091238 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 131059) (lo := 253) (len := 129) (W := 260091238) check rows elimOK (by decide) (by decide) cover131059 (by decide)
  decide +kernel

theorem c131059_3 : P.sumLeaves 26 134204798 108 = 449158084 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 131059) (lo := 382) (len := 108) (W := 449158084) check rows elimOK (by decide) (by decide) cover131059 (by decide)
  decide +kernel

theorem c131059_4 : P.sumLeaves 26 134204906 133 = 425472228 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 131059) (lo := 490) (len := 133) (W := 425472228) check rows elimOK (by decide) (by decide) cover131059 (by decide)
  decide +kernel

theorem c131059_5 : P.sumLeaves 26 134205039 118 = 535856192 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 131059) (lo := 623) (len := 118) (W := 535856192) check rows elimOK (by decide) (by decide) cover131059 (by decide)
  decide +kernel

theorem c131059_6 : P.sumLeaves 26 134205157 131 = 568732954 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 131059) (lo := 741) (len := 131) (W := 568732954) check rows elimOK (by decide) (by decide) cover131059 (by decide)
  decide +kernel

theorem c131059_7 : P.sumLeaves 26 134205288 108 = 771409750 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 131059) (lo := 872) (len := 108) (W := 771409750) check rows elimOK (by decide) (by decide) cover131059 (by decide)
  decide +kernel

theorem c131059_8 : P.sumLeaves 26 134205396 44 = 496117904 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 131059) (lo := 980) (len := 44) (W := 496117904) check rows elimOK (by decide) (by decide) cover131059 (by decide)
  decide +kernel

theorem h131059 : P.leaf 36 131059 = 3624295598 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(135, 51159040), (118, 66298208), (129, 260091238), (108, 449158084), (133, 425472228), (118, 535856192), (131, 568732954), (108, 771409750), (44, 496117904)]) (.cons c131059_0 (.cons c131059_1 (.cons c131059_2 (.cons c131059_3 (.cons c131059_4 (.cons c131059_5 (.cons c131059_6 (.cons c131059_7 (.cons c131059_8 (.nil)))))))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(131056, 60), (131057, 180), (131059, 180)]

theorem segOK : checkSeg 20 perms 131056 131063 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 131056 131063 420 1017473927040 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 1017473927040)
    (SegSum.cons (w := 60) h131056 (SegSum.cons (w := 180) h131057 (SegSum.cons (w := 180) h131059 (show SegSum (P.leaf 36) [] 0 from rfl)))) (by decide)

end RACert.S6N0.C0.S105
