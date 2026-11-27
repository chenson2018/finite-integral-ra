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

namespace RACert.S6N0.C0.S89

open RACert RACert.Problem

theorem cover119799 : P.CoversSplit 26 10 119799 0xfffffffffffffafafffffffffffffafaffffffffffffc8c8fafafafac8c8c8c8fffffafafffffafafafafafafafafafafffffafaffffc8c8fafafafac8c8c8c8fffffffffffffafafffffffffffffafaffffffffccccc8c8fafafafac8c8c8c8fffffafafffffafafafafafafafafafafffffafaccccc8c8fafafafac8c8c8c8 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 873, 922, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c119799_0 : P.sumLeaves 26 122674176 153 = 69604142 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 119799) (lo := 0) (len := 153) (W := 69604142) check rows elimOK (by decide) (by decide) cover119799 (by decide)
  decide +kernel

theorem c119799_1 : P.sumLeaves 26 122674329 133 = 93277351 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 119799) (lo := 153) (len := 133) (W := 93277351) check rows elimOK (by decide) (by decide) cover119799 (by decide)
  decide +kernel

theorem c119799_2 : P.sumLeaves 26 122674462 126 = 190432247 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 119799) (lo := 286) (len := 126) (W := 190432247) check rows elimOK (by decide) (by decide) cover119799 (by decide)
  decide +kernel

theorem c119799_3 : P.sumLeaves 26 122674588 103 = 303105414 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 119799) (lo := 412) (len := 103) (W := 303105414) check rows elimOK (by decide) (by decide) cover119799 (by decide)
  decide +kernel

theorem c119799_4 : P.sumLeaves 26 122674691 139 = 188133042 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 119799) (lo := 515) (len := 139) (W := 188133042) check rows elimOK (by decide) (by decide) cover119799 (by decide)
  decide +kernel

theorem c119799_5 : P.sumLeaves 26 122674830 121 = 290276070 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 119799) (lo := 654) (len := 121) (W := 290276070) check rows elimOK (by decide) (by decide) cover119799 (by decide)
  decide +kernel

theorem c119799_6 : P.sumLeaves 26 122674951 133 = 256331691 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 119799) (lo := 775) (len := 133) (W := 256331691) check rows elimOK (by decide) (by decide) cover119799 (by decide)
  decide +kernel

theorem c119799_7 : P.sumLeaves 26 122675084 100 = 330724225 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 119799) (lo := 908) (len := 100) (W := 330724225) check rows elimOK (by decide) (by decide) cover119799 (by decide)
  decide +kernel

theorem c119799_8 : P.sumLeaves 26 122675184 16 = 96891784 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 119799) (lo := 1008) (len := 16) (W := 96891784) check rows elimOK (by decide) (by decide) cover119799 (by decide)
  decide +kernel

theorem h119799 : P.leaf 36 119799 = 1818775966 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(153, 69604142), (133, 93277351), (126, 190432247), (103, 303105414), (139, 188133042), (121, 290276070), (133, 256331691), (100, 330724225), (16, 96891784)]) (.cons c119799_0 (.cons c119799_1 (.cons c119799_2 (.cons c119799_3 (.cons c119799_4 (.cons c119799_5 (.cons c119799_6 (.cons c119799_7 (.cons c119799_8 (.nil)))))))))) (by decide) (by decide))

theorem cover119807 : P.CoversSplit 26 10 119807 0xfffffffffffffafafffffffffffffafaffffffffffffc8c8fafafafac8c8c8c8fffffafafffffafafafafafafafafafafffffafaffffc8c8fafafafac8c8c8c8fffffffffffffafafffffffffffffafaffffffffccccc8c8fafafafac8c8c8c8fffffafafffffafafafafafafafafafafffffafaccccc8c8fafafafac8c8c8c8 :=
  coversSplit check rows (by decide) (by decide) (xs := [873, 922, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c119807_0 : P.sumLeaves 26 122682368 153 = 344423759 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 119807) (lo := 0) (len := 153) (W := 344423759) check rows elimOK (by decide) (by decide) cover119807 (by decide)
  decide +kernel

theorem c119807_1 : P.sumLeaves 26 122682521 133 = 402688192 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 119807) (lo := 153) (len := 133) (W := 402688192) check rows elimOK (by decide) (by decide) cover119807 (by decide)
  decide +kernel

theorem c119807_2 : P.sumLeaves 26 122682654 126 = 509516351 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 119807) (lo := 286) (len := 126) (W := 509516351) check rows elimOK (by decide) (by decide) cover119807 (by decide)
  decide +kernel

theorem c119807_3 : P.sumLeaves 26 122682780 103 = 695937121 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 119807) (lo := 412) (len := 103) (W := 695937121) check rows elimOK (by decide) (by decide) cover119807 (by decide)
  decide +kernel

theorem c119807_4 : P.sumLeaves 26 122682883 139 = 555608518 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 119807) (lo := 515) (len := 139) (W := 555608518) check rows elimOK (by decide) (by decide) cover119807 (by decide)
  decide +kernel

theorem c119807_5 : P.sumLeaves 26 122683022 121 = 734869540 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 119807) (lo := 654) (len := 121) (W := 734869540) check rows elimOK (by decide) (by decide) cover119807 (by decide)
  decide +kernel

theorem c119807_6 : P.sumLeaves 26 122683143 133 = 704943495 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 119807) (lo := 775) (len := 133) (W := 704943495) check rows elimOK (by decide) (by decide) cover119807 (by decide)
  decide +kernel

theorem c119807_7 : P.sumLeaves 26 122683276 100 = 800957570 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 119807) (lo := 908) (len := 100) (W := 800957570) check rows elimOK (by decide) (by decide) cover119807 (by decide)
  decide +kernel

theorem c119807_8 : P.sumLeaves 26 122683376 16 = 225881489 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 119807) (lo := 1008) (len := 16) (W := 225881489) check rows elimOK (by decide) (by decide) cover119807 (by decide)
  decide +kernel

theorem h119807 : P.leaf 36 119807 = 4974826035 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(153, 344423759), (133, 402688192), (126, 509516351), (103, 695937121), (139, 555608518), (121, 734869540), (133, 704943495), (100, 800957570), (16, 225881489)]) (.cons c119807_0 (.cons c119807_1 (.cons c119807_2 (.cons c119807_3 (.cons c119807_4 (.cons c119807_5 (.cons c119807_6 (.cons c119807_7 (.cons c119807_8 (.nil)))))))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(119799, 60), (119807, 60)]

theorem segOK : checkSeg 20 perms 119799 120663 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 119799 120663 120 407616120060 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 407616120060)
    (SegSum.cons (w := 60) h119799 (SegSum.cons (w := 60) h119807 (show SegSum (P.leaf 36) [] 0 from rfl))) (by decide)

end RACert.S6N0.C0.S89
