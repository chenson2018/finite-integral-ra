/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Atoms7.S4N1.C0.Actions

/-! Generated identity-class certificate for the product-row count. -/

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option Elab.async false

@[expose] public section

namespace RACert.S4N1.C0.S107

open RACert RACert.Problem

theorem cover32246 : P.CoversSplit 24 10 32246 0xfffffffffafafafafffffffffafafafafffffffffafafafafffffffffafafafaffc0ffc0fac0fac0ff00ff00fa00fa00ffc0ffc0fac0fac0ff00ff00fa00fa00fffffffffafafafafffffffffafafafafffffffffafafafafffffffffafafafaffc0ffc0fac0fac0ff00ff00fa00fa00ffc0ffc0fac0fac0ff00ff00fa00fa00 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 858, 865, 1202, 1259, 1601]) (by decide +kernel)

theorem c32246_0 : P.sumLeaves 24 33019904 204 = 11044592 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 32246) (lo := 0) (len := 204) (W := 11044592) check rows elimOK (by decide) (by decide) cover32246 (by decide)
  decide +kernel

theorem c32246_1 : P.sumLeaves 24 33020108 128 = 23753146 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 32246) (lo := 204) (len := 128) (W := 23753146) check rows elimOK (by decide) (by decide) cover32246 (by decide)
  decide +kernel

theorem c32246_2 : P.sumLeaves 24 33020236 108 = 33359105 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 32246) (lo := 332) (len := 108) (W := 33359105) check rows elimOK (by decide) (by decide) cover32246 (by decide)
  decide +kernel

theorem c32246_3 : P.sumLeaves 24 33020344 148 = 65413785 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 32246) (lo := 440) (len := 148) (W := 65413785) check rows elimOK (by decide) (by decide) cover32246 (by decide)
  decide +kernel

theorem c32246_4 : P.sumLeaves 24 33020492 181 = 74507399 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 32246) (lo := 588) (len := 181) (W := 74507399) check rows elimOK (by decide) (by decide) cover32246 (by decide)
  decide +kernel

theorem c32246_5 : P.sumLeaves 24 33020673 111 = 48350928 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 32246) (lo := 769) (len := 111) (W := 48350928) check rows elimOK (by decide) (by decide) cover32246 (by decide)
  decide +kernel

theorem c32246_6 : P.sumLeaves 24 33020784 112 = 98433015 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 32246) (lo := 880) (len := 112) (W := 98433015) check rows elimOK (by decide) (by decide) cover32246 (by decide)
  decide +kernel

theorem c32246_7 : P.sumLeaves 24 33020896 32 = 79402732 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 32246) (lo := 992) (len := 32) (W := 79402732) check rows elimOK (by decide) (by decide) cover32246 (by decide)
  decide +kernel

theorem h32246 : P.leaf 34 32246 = 434264702 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(204, 11044592), (128, 23753146), (108, 33359105), (148, 65413785), (181, 74507399), (111, 48350928), (112, 98433015), (32, 79402732)]) (.cons c32246_0 (.cons c32246_1 (.cons c32246_2 (.cons c32246_3 (.cons c32246_4 (.cons c32246_5 (.cons c32246_6 (.cons c32246_7 (.nil))))))))) (by decide) (by decide))

theorem cover32247 : P.CoversSplit 24 10 32247 0xfffffffffafafafafffffffffafafafafffffffffafafafafffffffffafafafaffccffccfac8fac8ffccffccfac8fac8ffccffccfac8fac8ffccffccfac8fac8fffffffffafafafafffffffffafafafafffffffffafafafafffffffffafafafaffccffccfac8fac8ffccffccfac8fac8ffccffccfac8fac8ffccffccfac8fac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [858, 865, 1202, 1259, 1601]) (by decide +kernel)

theorem c32247_0 : P.sumLeaves 24 33020928 153 = 22663596 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 32247) (lo := 0) (len := 153) (W := 22663596) check rows elimOK (by decide) (by decide) cover32247 (by decide)
  decide +kernel

theorem c32247_1 : P.sumLeaves 24 33021081 135 = 50448428 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 32247) (lo := 153) (len := 135) (W := 50448428) check rows elimOK (by decide) (by decide) cover32247 (by decide)
  decide +kernel

theorem c32247_2 : P.sumLeaves 24 33021216 108 = 50751879 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 32247) (lo := 288) (len := 108) (W := 50751879) check rows elimOK (by decide) (by decide) cover32247 (by decide)
  decide +kernel

theorem c32247_3 : P.sumLeaves 24 33021324 108 = 136082849 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 32247) (lo := 396) (len := 108) (W := 136082849) check rows elimOK (by decide) (by decide) cover32247 (by decide)
  decide +kernel

theorem c32247_4 : P.sumLeaves 24 33021432 147 = 92236354 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 32247) (lo := 504) (len := 147) (W := 92236354) check rows elimOK (by decide) (by decide) cover32247 (by decide)
  decide +kernel

theorem c32247_5 : P.sumLeaves 24 33021579 139 = 126502969 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 32247) (lo := 651) (len := 139) (W := 126502969) check rows elimOK (by decide) (by decide) cover32247 (by decide)
  decide +kernel

theorem c32247_6 : P.sumLeaves 24 33021718 107 = 136506797 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 32247) (lo := 790) (len := 107) (W := 136506797) check rows elimOK (by decide) (by decide) cover32247 (by decide)
  decide +kernel

theorem c32247_7 : P.sumLeaves 24 33021825 111 = 195821288 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 32247) (lo := 897) (len := 111) (W := 195821288) check rows elimOK (by decide) (by decide) cover32247 (by decide)
  decide +kernel

theorem c32247_8 : P.sumLeaves 24 33021936 16 = 66800888 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 32247) (lo := 1008) (len := 16) (W := 66800888) check rows elimOK (by decide) (by decide) cover32247 (by decide)
  decide +kernel

theorem h32247 : P.leaf 34 32247 = 877815048 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(153, 22663596), (135, 50448428), (108, 50751879), (108, 136082849), (147, 92236354), (139, 126502969), (107, 136506797), (111, 195821288), (16, 66800888)]) (.cons c32247_0 (.cons c32247_1 (.cons c32247_2 (.cons c32247_3 (.cons c32247_4 (.cons c32247_5 (.cons c32247_6 (.cons c32247_7 (.cons c32247_8 (.nil)))))))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(32246, 24), (32247, 48)]

theorem segOK : checkSeg 16 perms 32246 32252 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 32246 32252 72 52557475152 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 52557475152)
    (SegSum.cons (w := 24) h32246 (SegSum.cons (w := 48) h32247 (show SegSum (P.leaf 34) [] 0 from rfl))) (by decide)

end RACert.S4N1.C0.S107
