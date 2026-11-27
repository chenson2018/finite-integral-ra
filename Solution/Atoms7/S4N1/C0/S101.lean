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

namespace RACert.S4N1.C0.S101

open RACert RACert.Problem

theorem cover28092 : P.CoversSplit 24 10 28092 0xff00ff00fa00f0000000000000000000ff00ff00fa00f0000000000000000000ff00ff00fa00f000cc00cc00c800c000ff00ff00fa00f000cc00000000000000ff00ff00fa00f0000000000000000000ff00ff00fa00f00000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 472, 858, 865, 915, 1251, 1601]) (by decide +kernel)

theorem c28092_0 : P.sumLeaves 24 28766208 717 = 11720682 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28092) (lo := 0) (len := 717) (W := 11720682) check rows elimOK (by decide) (by decide) cover28092 (by decide)
  decide +kernel

theorem c28092_1 : P.sumLeaves 24 28766925 307 = 34535999 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28092) (lo := 717) (len := 307) (W := 34535999) check rows elimOK (by decide) (by decide) cover28092 (by decide)
  decide +kernel

theorem h28092 : P.leaf 34 28092 = 46256681 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(717, 11720682), (307, 34535999)]) (.cons c28092_0 (.cons c28092_1 (.nil))) (by decide) (by decide))

theorem cover28093 : P.CoversSplit 24 10 28093 0xff00ff00fa00f0000000000000000000ff00ff00fa00f0000000000000000000ff00ff00fa00f0000000000000000000ff00ff00fa00f0000000000000000000ff00ff00fa00f0000000000000000000ff00ff00fa00f00000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 517, 858, 865, 915, 1202, 1251, 1601]) (by decide +kernel)

theorem c28093_0 : P.sumLeaves 24 28767232 760 = 40936680 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28093) (lo := 0) (len := 760) (W := 40936680) check rows elimOK (by decide) (by decide) cover28093 (by decide)
  decide +kernel

theorem c28093_1 : P.sumLeaves 24 28767992 264 = 62115834 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28093) (lo := 760) (len := 264) (W := 62115834) check rows elimOK (by decide) (by decide) cover28093 (by decide)
  decide +kernel

theorem h28093 : P.leaf 34 28093 = 103052514 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(760, 40936680), (264, 62115834)]) (.cons c28093_0 (.cons c28093_1 (.nil))) (by decide) (by decide))

theorem cover28094 : P.CoversSplit 24 10 28094 0xfffffffffafaf0f0fffffffffafaf0f0fffffffffafaf0f0ffff000000000000ffc0ffc0fac0f0c0cc00cc00c800c000ffc0ffc0fac0f0c0cc00000000000000fffffffffafaf0f0fffffffffafaf0f0fffffffffafaf0f0ffff000000000000ffc0ffc0fac0f0c0cc00cc00c800c000ffc0ffc0f000f000cc00000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 858, 865, 1202, 1251, 1259, 1601]) (ps := [(8, [1217, 1609], [1272])]) (by decide +kernel)

theorem c28094_0 : P.sumLeaves 24 28768256 325 = 14492665 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28094) (lo := 0) (len := 325) (W := 14492665) check rows elimOK (by decide) (by decide) cover28094 (by decide)
  decide +kernel

theorem c28094_1 : P.sumLeaves 24 28768581 116 = 18819608 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28094) (lo := 325) (len := 116) (W := 18819608) check rows elimOK (by decide) (by decide) cover28094 (by decide)
  decide +kernel

theorem c28094_2 : P.sumLeaves 24 28768697 198 = 49210744 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28094) (lo := 441) (len := 198) (W := 49210744) check rows elimOK (by decide) (by decide) cover28094 (by decide)
  decide +kernel

theorem c28094_3 : P.sumLeaves 24 28768895 237 = 55462841 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28094) (lo := 639) (len := 237) (W := 55462841) check rows elimOK (by decide) (by decide) cover28094 (by decide)
  decide +kernel

theorem c28094_4 : P.sumLeaves 24 28769132 120 = 80687085 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28094) (lo := 876) (len := 120) (W := 80687085) check rows elimOK (by decide) (by decide) cover28094 (by decide)
  decide +kernel

theorem c28094_5 : P.sumLeaves 24 28769252 28 = 49829144 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28094) (lo := 996) (len := 28) (W := 49829144) check rows elimOK (by decide) (by decide) cover28094 (by decide)
  decide +kernel

theorem h28094 : P.leaf 34 28094 = 268502087 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(325, 14492665), (116, 18819608), (198, 49210744), (237, 55462841), (120, 80687085), (28, 49829144)]) (.cons c28094_0 (.cons c28094_1 (.cons c28094_2 (.cons c28094_3 (.cons c28094_4 (.cons c28094_5 (.nil))))))) (by decide) (by decide))

theorem cover28095 : P.CoversSplit 24 10 28095 0xfffffffffafaf0f0fffffffffafaf0f0fffffffffafaf0f0ffff000000000000ffccffccfac8f0c0ccccccccc8c8c0c0ffccffccfac8f0c0cccc000000000000fffffffffafaf0f0fffffffffafaf0f0fffffffffafaf0f0ffff000000000000ffccffccfac8f0c0ccccccccc8c8c0c0ffccffccf000f000cccc000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [517, 858, 865, 1202, 1251, 1259, 1601]) (ps := [(8, [1217, 1609], [1272])]) (by decide +kernel)

theorem c28095_0 : P.sumLeaves 24 28769280 247 = 33040498 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28095) (lo := 0) (len := 247) (W := 33040498) check rows elimOK (by decide) (by decide) cover28095 (by decide)
  decide +kernel

theorem c28095_1 : P.sumLeaves 24 28769527 168 = 45705885 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28095) (lo := 247) (len := 168) (W := 45705885) check rows elimOK (by decide) (by decide) cover28095 (by decide)
  decide +kernel

theorem c28095_2 : P.sumLeaves 24 28769695 174 = 101226563 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28095) (lo := 415) (len := 174) (W := 101226563) check rows elimOK (by decide) (by decide) cover28095 (by decide)
  decide +kernel

theorem c28095_3 : P.sumLeaves 24 28769869 174 = 107798844 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28095) (lo := 589) (len := 174) (W := 107798844) check rows elimOK (by decide) (by decide) cover28095 (by decide)
  decide +kernel

theorem c28095_4 : P.sumLeaves 24 28770043 168 = 111945972 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28095) (lo := 763) (len := 168) (W := 111945972) check rows elimOK (by decide) (by decide) cover28095 (by decide)
  decide +kernel

theorem c28095_5 : P.sumLeaves 24 28770211 93 = 176732630 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28095) (lo := 931) (len := 93) (W := 176732630) check rows elimOK (by decide) (by decide) cover28095 (by decide)
  decide +kernel

theorem h28095 : P.leaf 34 28095 = 576450392 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(247, 33040498), (168, 45705885), (174, 101226563), (174, 107798844), (168, 111945972), (93, 176732630)]) (.cons c28095_0 (.cons c28095_1 (.cons c28095_2 (.cons c28095_3 (.cons c28095_4 (.cons c28095_5 (.nil))))))) (by decide) (by decide))

theorem cover28140 : P.CoversSplit 24 10 28140 0xff00ff00ea00a0000000000000000000ff000000000000000000000000000000ee0cee0cea00a000ccccccccc8c08080ee0c000000000000cccc000000000000ff00ff00ea00a0000000000000000000ff0005000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 515, 522, 858, 865, 915, 1210]) (by decide +kernel)

theorem c28140_0 : P.sumLeaves 24 28815360 889 = 7101696 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28140) (lo := 0) (len := 889) (W := 7101696) check rows elimOK (by decide) (by decide) cover28140 (by decide)
  decide +kernel

theorem c28140_1 : P.sumLeaves 24 28816249 135 = 15149224 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 28140) (lo := 889) (len := 135) (W := 15149224) check rows elimOK (by decide) (by decide) cover28140 (by decide)
  decide +kernel

theorem h28140 : P.leaf 34 28140 = 22250920 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(889, 7101696), (135, 15149224)]) (.cons c28140_0 (.cons c28140_1 (.nil))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(28092, 48), (28093, 48), (28094, 48), (28095, 48), (28140, 24)]

theorem segOK : checkSeg 16 perms 28092 28141 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 28092 28141 216 48258582432 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 48258582432)
    (SegSum.cons (w := 48) h28092 (SegSum.cons (w := 48) h28093 (SegSum.cons (w := 48) h28094 (SegSum.cons (w := 48) h28095 (SegSum.cons (w := 24) h28140 (show SegSum (P.leaf 34) [] 0 from rfl)))))) (by decide)

end RACert.S4N1.C0.S101
