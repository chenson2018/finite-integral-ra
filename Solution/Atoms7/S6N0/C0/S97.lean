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

namespace RACert.S6N0.C0.S97

open RACert RACert.Problem

theorem cover122836 : P.CoversSplit 26 10 122836 0xfffffffffffffafafffffffffffffafafffffffffffffa00fafafafac8c8c800fffffafafffffafafafaa0a0fafaa0a0fffffafafffffa00fafaa0a0c8c88000ffccffccffccfac8ffccffccffccfac8ffccffcccc00c800fac8fac8c800c800ffccfac8ffccfac8fac8a080fac8a080ffccfac8cc00c800fac8a080c8008000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 922, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c122836_0 : P.sumLeaves 26 125784064 238 = 4665104 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122836) (lo := 0) (len := 238) (W := 4665104) check rows elimOK (by decide) (by decide) cover122836 (by decide)
  decide +kernel

theorem c122836_1 : P.sumLeaves 26 125784302 188 = 25595744 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122836) (lo := 238) (len := 188) (W := 25595744) check rows elimOK (by decide) (by decide) cover122836 (by decide)
  decide +kernel

theorem c122836_2 : P.sumLeaves 26 125784490 170 = 49202556 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122836) (lo := 426) (len := 170) (W := 49202556) check rows elimOK (by decide) (by decide) cover122836 (by decide)
  decide +kernel

theorem c122836_3 : P.sumLeaves 26 125784660 136 = 26754552 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122836) (lo := 596) (len := 136) (W := 26754552) check rows elimOK (by decide) (by decide) cover122836 (by decide)
  decide +kernel

theorem c122836_4 : P.sumLeaves 26 125784796 141 = 36520866 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122836) (lo := 732) (len := 141) (W := 36520866) check rows elimOK (by decide) (by decide) cover122836 (by decide)
  decide +kernel

theorem c122836_5 : P.sumLeaves 26 125784937 104 = 41512438 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122836) (lo := 873) (len := 104) (W := 41512438) check rows elimOK (by decide) (by decide) cover122836 (by decide)
  decide +kernel

theorem c122836_6 : P.sumLeaves 26 125785041 47 = 35767124 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122836) (lo := 977) (len := 47) (W := 35767124) check rows elimOK (by decide) (by decide) cover122836 (by decide)
  decide +kernel

theorem h122836 : P.leaf 36 122836 = 220018384 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(238, 4665104), (188, 25595744), (170, 49202556), (136, 26754552), (141, 36520866), (104, 41512438), (47, 35767124)]) (.cons c122836_0 (.cons c122836_1 (.cons c122836_2 (.cons c122836_3 (.cons c122836_4 (.cons c122836_5 (.cons c122836_6 (.nil)))))))) (by decide) (by decide))

theorem cover122837 : P.CoversSplit 26 10 122837 0xfffffffffffffafafffffffffffffafafffffffffffffa00fafafafac8c8c800fffffafafffffafafafaf0f0fafaf0f0fffffafafffffa00fafaf0f0c8c8c000ffffffffffccfac8ffffffffffccfac8ffffffffcc00c800fafafafac800c800fffffafaffccfac8fafaf0f0fac8f0c0fffffafacc00c800fafaf0f0c800c000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 922, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c122837_0 : P.sumLeaves 26 125785088 198 = 28319642 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122837) (lo := 0) (len := 198) (W := 28319642) check rows elimOK (by decide) (by decide) cover122837 (by decide)
  decide +kernel

theorem c122837_1 : P.sumLeaves 26 125785286 165 = 61695767 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122837) (lo := 198) (len := 165) (W := 61695767) check rows elimOK (by decide) (by decide) cover122837 (by decide)
  decide +kernel

theorem c122837_2 : P.sumLeaves 26 125785451 118 = 153247456 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122837) (lo := 363) (len := 118) (W := 153247456) check rows elimOK (by decide) (by decide) cover122837 (by decide)
  decide +kernel

theorem c122837_3 : P.sumLeaves 26 125785569 146 = 161307366 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122837) (lo := 481) (len := 146) (W := 161307366) check rows elimOK (by decide) (by decide) cover122837 (by decide)
  decide +kernel

theorem c122837_4 : P.sumLeaves 26 125785715 128 = 198975576 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122837) (lo := 627) (len := 128) (W := 198975576) check rows elimOK (by decide) (by decide) cover122837 (by decide)
  decide +kernel

theorem c122837_5 : P.sumLeaves 26 125785843 137 = 202335113 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122837) (lo := 755) (len := 137) (W := 202335113) check rows elimOK (by decide) (by decide) cover122837 (by decide)
  decide +kernel

theorem c122837_6 : P.sumLeaves 26 125785980 104 = 269364186 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122837) (lo := 892) (len := 104) (W := 269364186) check rows elimOK (by decide) (by decide) cover122837 (by decide)
  decide +kernel

theorem c122837_7 : P.sumLeaves 26 125786084 28 = 150049318 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122837) (lo := 996) (len := 28) (W := 150049318) check rows elimOK (by decide) (by decide) cover122837 (by decide)
  decide +kernel

theorem h122837 : P.leaf 36 122837 = 1225294424 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(198, 28319642), (165, 61695767), (118, 153247456), (146, 161307366), (128, 198975576), (137, 202335113), (104, 269364186), (28, 150049318)]) (.cons c122837_0 (.cons c122837_1 (.cons c122837_2 (.cons c122837_3 (.cons c122837_4 (.cons c122837_5 (.cons c122837_6 (.cons c122837_7 (.nil))))))))) (by decide) (by decide))

theorem cover122839 : P.CoversSplit 26 10 122839 0xfffffffffffffafafffffffffffffafafffffffffffffa00fafafafac8c8c800fffffafafffffafafafafafafafafafafffffafafffffa00fafafafac8c8c800fffffffffffffafafffffffffffffafaffffffffcc00c800fafafafac800c800fffffafafffffafafafafafafafafafafffffafacc00c800fafafafac800c800 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c122839_0 : P.sumLeaves 26 125787136 171 = 88055042 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122839) (lo := 0) (len := 171) (W := 88055042) check rows elimOK (by decide) (by decide) cover122839 (by decide)
  decide +kernel

theorem c122839_1 : P.sumLeaves 26 125787307 140 = 141228395 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122839) (lo := 171) (len := 140) (W := 141228395) check rows elimOK (by decide) (by decide) cover122839 (by decide)
  decide +kernel

theorem c122839_2 : P.sumLeaves 26 125787447 127 = 310320084 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122839) (lo := 311) (len := 127) (W := 310320084) check rows elimOK (by decide) (by decide) cover122839 (by decide)
  decide +kernel

theorem c122839_3 : P.sumLeaves 26 125787574 129 = 432400016 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122839) (lo := 438) (len := 129) (W := 432400016) check rows elimOK (by decide) (by decide) cover122839 (by decide)
  decide +kernel

theorem c122839_4 : P.sumLeaves 26 125787703 126 = 255673566 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122839) (lo := 567) (len := 126) (W := 255673566) check rows elimOK (by decide) (by decide) cover122839 (by decide)
  decide +kernel

theorem c122839_5 : P.sumLeaves 26 125787829 137 = 411932525 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122839) (lo := 693) (len := 137) (W := 411932525) check rows elimOK (by decide) (by decide) cover122839 (by decide)
  decide +kernel

theorem c122839_6 : P.sumLeaves 26 125787966 110 = 375488809 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122839) (lo := 830) (len := 110) (W := 375488809) check rows elimOK (by decide) (by decide) cover122839 (by decide)
  decide +kernel

theorem c122839_7 : P.sumLeaves 26 125788076 84 = 544405821 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122839) (lo := 940) (len := 84) (W := 544405821) check rows elimOK (by decide) (by decide) cover122839 (by decide)
  decide +kernel

theorem h122839 : P.leaf 36 122839 = 2559504258 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(171, 88055042), (140, 141228395), (127, 310320084), (129, 432400016), (126, 255673566), (137, 411932525), (110, 375488809), (84, 544405821)]) (.cons c122839_0 (.cons c122839_1 (.cons c122839_2 (.cons c122839_3 (.cons c122839_4 (.cons c122839_5 (.cons c122839_6 (.cons c122839_7 (.nil))))))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(122836, 360), (122837, 720), (122839, 360)]

theorem segOK : checkSeg 20 perms 122836 122841 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 122836 122841 1440 1882840136400 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 1882840136400)
    (SegSum.cons (w := 360) h122836 (SegSum.cons (w := 720) h122837 (SegSum.cons (w := 360) h122839 (show SegSum (P.leaf 36) [] 0 from rfl)))) (by decide)

end RACert.S6N0.C0.S97
