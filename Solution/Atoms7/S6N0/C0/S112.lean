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

namespace RACert.S6N0.C0.S112

open RACert RACert.Problem

theorem cover229119 : P.CoversSplit 26 10 229119 0xfffffffffffffffffffffffafffffafa00000000000000000000000000300000fffffffffffffffffffff0f0fffff0f00000000000000000000000000030000000000000003300330000000000330032000000000000000000000000000000000000000000330033000000000033003000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [587, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c229119_0 : P.sumLeaves 26 234617856 721 = 284247369 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 229119) (lo := 0) (len := 721) (W := 284247369) check rows elimOK (by decide) (by decide) cover229119 (by decide)
  decide +kernel

theorem c229119_1 : P.sumLeaves 26 234618577 228 = 956757990 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 229119) (lo := 721) (len := 228) (W := 956757990) check rows elimOK (by decide) (by decide) cover229119 (by decide)
  decide +kernel

theorem c229119_2 : P.sumLeaves 26 234618805 75 = 1364898104 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 229119) (lo := 949) (len := 75) (W := 1364898104) check rows elimOK (by decide) (by decide) cover229119 (by decide)
  decide +kernel

theorem h229119 : P.leaf 36 229119 = 2605903463 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(721, 284247369), (228, 956757990), (75, 1364898104)]) (.cons c229119_0 (.cons c229119_1 (.cons c229119_2 (.nil)))) (by decide) (by decide))

theorem cover229357 : P.CoversSplit 26 10 229357 0xfffffffffffffffffffffffafffffafafffffffffffcffccfffffafaffccfac8fffffffffffffffffffffafafffffafafffffffffffcffccfffffafaffccfac8fffffffffffffffffffffffafffffafaffffffffffccffccfffffafaffccfac80000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c229357_0 : P.sumLeaves 26 234861568 375 = 284224460 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 229357) (lo := 0) (len := 375) (W := 284224460) check rows elimOK (by decide) (by decide) cover229357 (by decide)
  decide +kernel

theorem c229357_1 : P.sumLeaves 26 234861943 102 = 410259057 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 229357) (lo := 375) (len := 102) (W := 410259057) check rows elimOK (by decide) (by decide) cover229357 (by decide)
  decide +kernel

theorem c229357_2 : P.sumLeaves 26 234862045 117 = 429050650 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 229357) (lo := 477) (len := 117) (W := 429050650) check rows elimOK (by decide) (by decide) cover229357 (by decide)
  decide +kernel

theorem c229357_3 : P.sumLeaves 26 234862162 104 = 366416191 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 229357) (lo := 594) (len := 104) (W := 366416191) check rows elimOK (by decide) (by decide) cover229357 (by decide)
  decide +kernel

theorem c229357_4 : P.sumLeaves 26 234862266 109 = 584366954 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 229357) (lo := 698) (len := 109) (W := 584366954) check rows elimOK (by decide) (by decide) cover229357 (by decide)
  decide +kernel

theorem c229357_5 : P.sumLeaves 26 234862375 108 = 945281386 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 229357) (lo := 807) (len := 108) (W := 945281386) check rows elimOK (by decide) (by decide) cover229357 (by decide)
  decide +kernel

theorem c229357_6 : P.sumLeaves 26 234862483 98 = 1139609872 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 229357) (lo := 915) (len := 98) (W := 1139609872) check rows elimOK (by decide) (by decide) cover229357 (by decide)
  decide +kernel

theorem c229357_7 : P.sumLeaves 26 234862581 11 = 196983720 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 229357) (lo := 1013) (len := 11) (W := 196983720) check rows elimOK (by decide) (by decide) cover229357 (by decide)
  decide +kernel

theorem h229357 : P.leaf 36 229357 = 4356192290 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(375, 284224460), (102, 410259057), (117, 429050650), (104, 366416191), (109, 584366954), (108, 945281386), (98, 1139609872), (11, 196983720)]) (.cons c229357_0 (.cons c229357_1 (.cons c229357_2 (.cons c229357_3 (.cons c229357_4 (.cons c229357_5 (.cons c229357_6 (.cons c229357_7 (.nil))))))))) (by decide) (by decide))

theorem cover229359 : P.CoversSplit 26 10 229359 0xfffffffffffffffffffffffafffffafafffffffffffcffccfffffafaffccfac8fffffffffffffffffffffafafffffafafffffffffffcffccfffffafaffccfac8fffffffffffffffffffffffafffffafaffffffffffccffccfffffafaffccfac80000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [972, 979, 1266, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c229359_0 : P.sumLeaves 26 234863616 375 = 552328408 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 229359) (lo := 0) (len := 375) (W := 552328408) check rows elimOK (by decide) (by decide) cover229359 (by decide)
  decide +kernel

theorem c229359_1 : P.sumLeaves 26 234863991 102 = 688560839 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 229359) (lo := 375) (len := 102) (W := 688560839) check rows elimOK (by decide) (by decide) cover229359 (by decide)
  decide +kernel

theorem c229359_2 : P.sumLeaves 26 234864093 117 = 693035658 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 229359) (lo := 477) (len := 117) (W := 693035658) check rows elimOK (by decide) (by decide) cover229359 (by decide)
  decide +kernel

theorem c229359_3 : P.sumLeaves 26 234864210 104 = 628036259 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 229359) (lo := 594) (len := 104) (W := 628036259) check rows elimOK (by decide) (by decide) cover229359 (by decide)
  decide +kernel

theorem c229359_4 : P.sumLeaves 26 234864314 109 = 921229198 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 229359) (lo := 698) (len := 109) (W := 921229198) check rows elimOK (by decide) (by decide) cover229359 (by decide)
  decide +kernel

theorem c229359_5 : P.sumLeaves 26 234864423 108 = 1529701344 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 229359) (lo := 807) (len := 108) (W := 1529701344) check rows elimOK (by decide) (by decide) cover229359 (by decide)
  decide +kernel

theorem c229359_6 : P.sumLeaves 26 234864531 98 = 1666093904 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 229359) (lo := 915) (len := 98) (W := 1666093904) check rows elimOK (by decide) (by decide) cover229359 (by decide)
  decide +kernel

theorem c229359_7 : P.sumLeaves 26 234864629 11 = 231918980 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 229359) (lo := 1013) (len := 11) (W := 231918980) check rows elimOK (by decide) (by decide) cover229359 (by decide)
  decide +kernel

theorem h229359 : P.leaf 36 229359 = 6910904590 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(375, 552328408), (102, 688560839), (117, 693035658), (104, 628036259), (109, 921229198), (108, 1529701344), (98, 1666093904), (11, 231918980)]) (.cons c229359_0 (.cons c229359_1 (.cons c229359_2 (.cons c229359_3 (.cons c229359_4 (.cons c229359_5 (.cons c229359_6 (.cons c229359_7 (.nil))))))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(229119, 360), (229357, 180), (229359, 180)]

theorem segOK : checkSeg 20 perms 229119 229375 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 229119 229375 720 2966202685080 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 2966202685080)
    (SegSum.cons (w := 360) h229119 (SegSum.cons (w := 180) h229357 (SegSum.cons (w := 180) h229359 (show SegSum (P.leaf 36) [] 0 from rfl)))) (by decide)

end RACert.S6N0.C0.S112
