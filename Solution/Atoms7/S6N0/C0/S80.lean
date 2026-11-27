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

namespace RACert.S6N0.C0.S80

open RACert RACert.Problem

theorem cover97276 : P.CoversSplit 26 10 97276 0xfffffffffffffafafffffffafffffafafffffffffffcfac8fafafafafac8fac8fffffafafffffafafafafafafafafafafffffafafffcfac8fafafafafac8fac8fffffffffffffafafffffffafffffafaffffffffccccc8c8fafafafac8c8c8c80000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [874, 972, 979, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c97276_0 : P.sumLeaves 26 99610624 402 = 44163736 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97276) (lo := 0) (len := 402) (W := 44163736) check rows elimOK (by decide) (by decide) cover97276 (by decide)
  decide +kernel

theorem c97276_1 : P.sumLeaves 26 99611026 102 = 120474593 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97276) (lo := 402) (len := 102) (W := 120474593) check rows elimOK (by decide) (by decide) cover97276 (by decide)
  decide +kernel

theorem c97276_2 : P.sumLeaves 26 99611128 131 = 83380308 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97276) (lo := 504) (len := 131) (W := 83380308) check rows elimOK (by decide) (by decide) cover97276 (by decide)
  decide +kernel

theorem c97276_3 : P.sumLeaves 26 99611259 120 = 108871198 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97276) (lo := 635) (len := 120) (W := 108871198) check rows elimOK (by decide) (by decide) cover97276 (by decide)
  decide +kernel

theorem c97276_4 : P.sumLeaves 26 99611379 127 = 144171138 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97276) (lo := 755) (len := 127) (W := 144171138) check rows elimOK (by decide) (by decide) cover97276 (by decide)
  decide +kernel

theorem c97276_5 : P.sumLeaves 26 99611506 106 = 224913720 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97276) (lo := 882) (len := 106) (W := 224913720) check rows elimOK (by decide) (by decide) cover97276 (by decide)
  decide +kernel

theorem c97276_6 : P.sumLeaves 26 99611612 36 = 203822628 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97276) (lo := 988) (len := 36) (W := 203822628) check rows elimOK (by decide) (by decide) cover97276 (by decide)
  decide +kernel

theorem h97276 : P.leaf 36 97276 = 929797321 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(402, 44163736), (102, 120474593), (131, 83380308), (120, 108871198), (127, 144171138), (106, 224913720), (36, 203822628)]) (.cons c97276_0 (.cons c97276_1 (.cons c97276_2 (.cons c97276_3 (.cons c97276_4 (.cons c97276_5 (.cons c97276_6 (.nil)))))))) (by decide) (by decide))

theorem cover97277 : P.CoversSplit 26 10 97277 0xfffffffffffffafafffffffafffffafafffffffffffcfac8fafafafafac8fac8fffffafafffffafafafafafafafafafafffffafafffcfac8fafafafafac8fac8fffffffffffffafafffffffafffffafaffffffffccccc8c8fafafafac8c8c8c80000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [923, 972, 979, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c97277_0 : P.sumLeaves 26 99611648 402 = 132713370 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97277) (lo := 0) (len := 402) (W := 132713370) check rows elimOK (by decide) (by decide) cover97277 (by decide)
  decide +kernel

theorem c97277_1 : P.sumLeaves 26 99612050 102 = 275691909 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97277) (lo := 402) (len := 102) (W := 275691909) check rows elimOK (by decide) (by decide) cover97277 (by decide)
  decide +kernel

theorem c97277_2 : P.sumLeaves 26 99612152 131 = 199880229 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97277) (lo := 504) (len := 131) (W := 199880229) check rows elimOK (by decide) (by decide) cover97277 (by decide)
  decide +kernel

theorem c97277_3 : P.sumLeaves 26 99612283 120 = 256007510 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97277) (lo := 635) (len := 120) (W := 256007510) check rows elimOK (by decide) (by decide) cover97277 (by decide)
  decide +kernel

theorem c97277_4 : P.sumLeaves 26 99612403 127 = 361001368 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97277) (lo := 755) (len := 127) (W := 361001368) check rows elimOK (by decide) (by decide) cover97277 (by decide)
  decide +kernel

theorem c97277_5 : P.sumLeaves 26 99612530 106 = 512938940 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97277) (lo := 882) (len := 106) (W := 512938940) check rows elimOK (by decide) (by decide) cover97277 (by decide)
  decide +kernel

theorem c97277_6 : P.sumLeaves 26 99612636 36 = 366870608 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97277) (lo := 988) (len := 36) (W := 366870608) check rows elimOK (by decide) (by decide) cover97277 (by decide)
  decide +kernel

theorem h97277 : P.leaf 36 97277 = 2105103934 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(402, 132713370), (102, 275691909), (131, 199880229), (120, 256007510), (127, 361001368), (106, 512938940), (36, 366870608)]) (.cons c97277_0 (.cons c97277_1 (.cons c97277_2 (.cons c97277_3 (.cons c97277_4 (.cons c97277_5 (.cons c97277_6 (.nil)))))))) (by decide) (by decide))

theorem cover97279 : P.CoversSplit 26 10 97279 0xfffffffffffffafafffffffafffffafafffffffffffcfac8fafafafafac8fac8fffffafafffffafafafafafafafafafafffffafafffcfac8fafafafafac8fac8fffffffffffffafafffffffafffffafaffffffffccccc8c8fafafafac8c8c8c8fffffafafffffafafafafafafafafafafffffafaccccc8c8fafafafac8c8c8c8 :=
  coversSplit check rows (by decide) (by decide) (xs := [972, 979, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c97279_0 : P.sumLeaves 26 99613696 153 = 7189599 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97279) (lo := 0) (len := 153) (W := 7189599) check rows elimOK (by decide) (by decide) cover97279 (by decide)
  decide +kernel

theorem c97279_1 : P.sumLeaves 26 99613849 133 = 60959150 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97279) (lo := 153) (len := 133) (W := 60959150) check rows elimOK (by decide) (by decide) cover97279 (by decide)
  decide +kernel

theorem c97279_2 : P.sumLeaves 26 99613982 126 = 471626426 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97279) (lo := 286) (len := 126) (W := 471626426) check rows elimOK (by decide) (by decide) cover97279 (by decide)
  decide +kernel

theorem c97279_3 : P.sumLeaves 26 99614108 107 = 621595186 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97279) (lo := 412) (len := 107) (W := 621595186) check rows elimOK (by decide) (by decide) cover97279 (by decide)
  decide +kernel

theorem c97279_4 : P.sumLeaves 26 99614215 128 = 551177397 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97279) (lo := 519) (len := 128) (W := 551177397) check rows elimOK (by decide) (by decide) cover97279 (by decide)
  decide +kernel

theorem c97279_5 : P.sumLeaves 26 99614343 118 = 678163570 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97279) (lo := 647) (len := 118) (W := 678163570) check rows elimOK (by decide) (by decide) cover97279 (by decide)
  decide +kernel

theorem c97279_6 : P.sumLeaves 26 99614461 127 = 1069939295 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97279) (lo := 765) (len := 127) (W := 1069939295) check rows elimOK (by decide) (by decide) cover97279 (by decide)
  decide +kernel

theorem c97279_7 : P.sumLeaves 26 99614588 106 = 1267640784 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97279) (lo := 892) (len := 106) (W := 1267640784) check rows elimOK (by decide) (by decide) cover97279 (by decide)
  decide +kernel

theorem c97279_8 : P.sumLeaves 26 99614694 26 = 460930038 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97279) (lo := 998) (len := 26) (W := 460930038) check rows elimOK (by decide) (by decide) cover97279 (by decide)
  decide +kernel

theorem h97279 : P.leaf 36 97279 = 5189221445 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(153, 7189599), (133, 60959150), (126, 471626426), (107, 621595186), (128, 551177397), (118, 678163570), (127, 1069939295), (106, 1267640784), (26, 460930038)]) (.cons c97279_0 (.cons c97279_1 (.cons c97279_2 (.cons c97279_3 (.cons c97279_4 (.cons c97279_5 (.cons c97279_6 (.cons c97279_7 (.cons c97279_8 (.nil)))))))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(97276, 360), (97277, 720), (97279, 360)]

theorem segOK : checkSeg 20 perms 97276 97783 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 97276 97783 1440 3718521588240 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 3718521588240)
    (SegSum.cons (w := 360) h97276 (SegSum.cons (w := 720) h97277 (SegSum.cons (w := 360) h97279 (show SegSum (P.leaf 36) [] 0 from rfl)))) (by decide)

end RACert.S6N0.C0.S80
