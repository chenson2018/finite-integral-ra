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

namespace RACert.S6N0.C0.S122

open RACert RACert.Problem

theorem cover243511 : P.CoversSplit 26 10 243511 0xfffffffffffffffffffffffffffff0f0ffffffffffffccccffffaaaaff008000ffffffffffffffffffffa0a0ffffa0a0ffffffffffffccccffffa0a0ff008000fffffffffffffffffffffffffffff0f0ffffffffcc00cc00ffffaaaacc008000ffffffffffffffffffffa0a0ffffa0a0ffffffffcc00cc00ffffa0a0cc008000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 579, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c243511_0 : P.sumLeaves 26 249355264 183 = 35124295 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243511) (lo := 0) (len := 183) (W := 35124295) check rows elimOK (by decide) (by decide) cover243511 (by decide)
  decide +kernel

theorem c243511_1 : P.sumLeaves 26 249355447 131 = 70778367 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243511) (lo := 183) (len := 131) (W := 70778367) check rows elimOK (by decide) (by decide) cover243511 (by decide)
  decide +kernel

theorem c243511_2 : P.sumLeaves 26 249355578 128 = 182529796 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243511) (lo := 314) (len := 128) (W := 182529796) check rows elimOK (by decide) (by decide) cover243511 (by decide)
  decide +kernel

theorem c243511_3 : P.sumLeaves 26 249355706 131 = 244406751 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243511) (lo := 442) (len := 131) (W := 244406751) check rows elimOK (by decide) (by decide) cover243511 (by decide)
  decide +kernel

theorem c243511_4 : P.sumLeaves 26 249355837 128 = 138690898 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243511) (lo := 573) (len := 128) (W := 138690898) check rows elimOK (by decide) (by decide) cover243511 (by decide)
  decide +kernel

theorem c243511_5 : P.sumLeaves 26 249355965 127 = 199781616 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243511) (lo := 701) (len := 127) (W := 199781616) check rows elimOK (by decide) (by decide) cover243511 (by decide)
  decide +kernel

theorem c243511_6 : P.sumLeaves 26 249356092 112 = 222903634 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243511) (lo := 828) (len := 112) (W := 222903634) check rows elimOK (by decide) (by decide) cover243511 (by decide)
  decide +kernel

theorem c243511_7 : P.sumLeaves 26 249356204 84 = 302817984 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243511) (lo := 940) (len := 84) (W := 302817984) check rows elimOK (by decide) (by decide) cover243511 (by decide)
  decide +kernel

theorem h243511 : P.leaf 36 243511 = 1397033341 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(183, 35124295), (131, 70778367), (128, 182529796), (131, 244406751), (128, 138690898), (127, 199781616), (112, 222903634), (84, 302817984)]) (.cons c243511_0 (.cons c243511_1 (.cons c243511_2 (.cons c243511_3 (.cons c243511_4 (.cons c243511_5 (.cons c243511_6 (.cons c243511_7 (.nil))))))))) (by decide) (by decide))

theorem cover243519 : P.CoversSplit 26 10 243519 0xfffffffffffffffffffffffffffff0f0ffffffffffffccccffffaaaaff008000ffffffffffffffffffffa0a0ffffa0a0ffffffffffffccccffffa0a0ff008000fffffffffffffffffffffffffffff0f0ffffffffcc00cc00ffffaaaacc008000ffffffffffffffffffffa0a0ffffa0a0ffffffffcc00cc00ffffa0a0cc008000 :=
  coversSplit check rows (by decide) (by decide) (xs := [538, 579, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c243519_0 : P.sumLeaves 26 249363456 183 = 146845554 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243519) (lo := 0) (len := 183) (W := 146845554) check rows elimOK (by decide) (by decide) cover243519 (by decide)
  decide +kernel

theorem c243519_1 : P.sumLeaves 26 249363639 131 = 230807475 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243519) (lo := 183) (len := 131) (W := 230807475) check rows elimOK (by decide) (by decide) cover243519 (by decide)
  decide +kernel

theorem c243519_2 : P.sumLeaves 26 249363770 128 = 336351869 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243519) (lo := 314) (len := 128) (W := 336351869) check rows elimOK (by decide) (by decide) cover243519 (by decide)
  decide +kernel

theorem c243519_3 : P.sumLeaves 26 249363898 131 = 446632115 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243519) (lo := 442) (len := 131) (W := 446632115) check rows elimOK (by decide) (by decide) cover243519 (by decide)
  decide +kernel

theorem c243519_4 : P.sumLeaves 26 249364029 128 = 346476659 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243519) (lo := 573) (len := 128) (W := 346476659) check rows elimOK (by decide) (by decide) cover243519 (by decide)
  decide +kernel

theorem c243519_5 : P.sumLeaves 26 249364157 127 = 462291786 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243519) (lo := 701) (len := 127) (W := 462291786) check rows elimOK (by decide) (by decide) cover243519 (by decide)
  decide +kernel

theorem c243519_6 : P.sumLeaves 26 249364284 112 = 416689770 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243519) (lo := 828) (len := 112) (W := 416689770) check rows elimOK (by decide) (by decide) cover243519 (by decide)
  decide +kernel

theorem c243519_7 : P.sumLeaves 26 249364396 84 = 567879940 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 243519) (lo := 940) (len := 84) (W := 567879940) check rows elimOK (by decide) (by decide) cover243519 (by decide)
  decide +kernel

theorem h243519 : P.leaf 36 243519 = 2953975168 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(183, 146845554), (131, 230807475), (128, 336351869), (131, 446632115), (128, 346476659), (127, 462291786), (112, 416689770), (84, 567879940)]) (.cons c243519_0 (.cons c243519_1 (.cons c243519_2 (.cons c243519_3 (.cons c243519_4 (.cons c243519_5 (.cons c243519_6 (.cons c243519_7 (.nil))))))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(243511, 360), (243519, 180)]

theorem segOK : checkSeg 20 perms 243511 243558 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 243511 243558 540 1034647533000 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 1034647533000)
    (SegSum.cons (w := 360) h243511 (SegSum.cons (w := 180) h243519 (show SegSum (P.leaf 36) [] 0 from rfl))) (by decide)

end RACert.S6N0.C0.S122
