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

namespace RACert.S6N0.C0.S100

open RACert RACert.Problem

theorem cover122847 : P.CoversSplit 26 10 122847 0xfffffffffffffafafffffffffffffafafffffffffffffa00fafafafac8c8c800fffffafafffffafafafafafafafafafafffffafafffffa00fafafafac8c8c800fffffffffffffafafffffffffffffafaffffffffcc00c800fafafafac800c800fffffafafffffafafafafafafafafafafffffafacc00c800fafafafac800c800 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c122847_0 : P.sumLeaves 26 125795328 171 = 337523298 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122847) (lo := 0) (len := 171) (W := 337523298) check rows elimOK (by decide) (by decide) cover122847 (by decide)
  decide +kernel

theorem c122847_1 : P.sumLeaves 26 125795499 140 = 458775192 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122847) (lo := 171) (len := 140) (W := 458775192) check rows elimOK (by decide) (by decide) cover122847 (by decide)
  decide +kernel

theorem c122847_2 : P.sumLeaves 26 125795639 127 = 542450773 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122847) (lo := 311) (len := 127) (W := 542450773) check rows elimOK (by decide) (by decide) cover122847 (by decide)
  decide +kernel

theorem c122847_3 : P.sumLeaves 26 125795766 129 = 717032132 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122847) (lo := 438) (len := 129) (W := 717032132) check rows elimOK (by decide) (by decide) cover122847 (by decide)
  decide +kernel

theorem c122847_4 : P.sumLeaves 26 125795895 126 = 603669667 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122847) (lo := 567) (len := 126) (W := 603669667) check rows elimOK (by decide) (by decide) cover122847 (by decide)
  decide +kernel

theorem c122847_5 : P.sumLeaves 26 125796021 137 = 840607702 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122847) (lo := 693) (len := 137) (W := 840607702) check rows elimOK (by decide) (by decide) cover122847 (by decide)
  decide +kernel

theorem c122847_6 : P.sumLeaves 26 125796158 110 = 655640367 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122847) (lo := 830) (len := 110) (W := 655640367) check rows elimOK (by decide) (by decide) cover122847 (by decide)
  decide +kernel

theorem c122847_7 : P.sumLeaves 26 125796268 84 = 865076877 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122847) (lo := 940) (len := 84) (W := 865076877) check rows elimOK (by decide) (by decide) cover122847 (by decide)
  decide +kernel

theorem h122847 : P.leaf 36 122847 = 5020776008 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(171, 337523298), (140, 458775192), (127, 542450773), (129, 717032132), (126, 603669667), (137, 840607702), (110, 655640367), (84, 865076877)]) (.cons c122847_0 (.cons c122847_1 (.cons c122847_2 (.cons c122847_3 (.cons c122847_4 (.cons c122847_5 (.cons c122847_6 (.cons c122847_7 (.nil))))))))) (by decide) (by decide))

theorem cover122866 : P.CoversSplit 26 10 122866 0xfffffffffffffafafafafafafafafafaffccffccffccfac8fac8fac8c8c8c8c8fffffafafffffafafafafafafafafafaffccfac8ffccfac8fac8fac8c8c8c8c8fffffffffffffafafafafafafafafafaffccffccccccc8c8fac8fac8c8c8c8c8fffffafafffffafafafafafafafafafaffccfac8ccccc8c8fac8fac8c8c8c8c8 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 1315, 1665]) (by decide +kernel)

theorem c122866_0 : P.sumLeaves 26 125814784 171 = 6735364 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122866) (lo := 0) (len := 171) (W := 6735364) check rows elimOK (by decide) (by decide) cover122866 (by decide)
  decide +kernel

theorem c122866_1 : P.sumLeaves 26 125814955 140 = 19065402 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122866) (lo := 171) (len := 140) (W := 19065402) check rows elimOK (by decide) (by decide) cover122866 (by decide)
  decide +kernel

theorem c122866_2 : P.sumLeaves 26 125815095 142 = 91569285 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122866) (lo := 311) (len := 142) (W := 91569285) check rows elimOK (by decide) (by decide) cover122866 (by decide)
  decide +kernel

theorem c122866_3 : P.sumLeaves 26 125815237 141 = 106947498 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122866) (lo := 453) (len := 141) (W := 106947498) check rows elimOK (by decide) (by decide) cover122866 (by decide)
  decide +kernel

theorem c122866_4 : P.sumLeaves 26 125815378 129 = 84591955 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122866) (lo := 594) (len := 129) (W := 84591955) check rows elimOK (by decide) (by decide) cover122866 (by decide)
  decide +kernel

theorem c122866_5 : P.sumLeaves 26 125815507 149 = 120935164 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122866) (lo := 723) (len := 149) (W := 120935164) check rows elimOK (by decide) (by decide) cover122866 (by decide)
  decide +kernel

theorem c122866_6 : P.sumLeaves 26 125815656 120 = 135780509 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122866) (lo := 872) (len := 120) (W := 135780509) check rows elimOK (by decide) (by decide) cover122866 (by decide)
  decide +kernel

theorem c122866_7 : P.sumLeaves 26 125815776 32 = 92044806 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122866) (lo := 992) (len := 32) (W := 92044806) check rows elimOK (by decide) (by decide) cover122866 (by decide)
  decide +kernel

theorem h122866 : P.leaf 36 122866 = 657669983 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(171, 6735364), (140, 19065402), (142, 91569285), (141, 106947498), (129, 84591955), (149, 120935164), (120, 135780509), (32, 92044806)]) (.cons c122866_0 (.cons c122866_1 (.cons c122866_2 (.cons c122866_3 (.cons c122866_4 (.cons c122866_5 (.cons c122866_6 (.cons c122866_7 (.nil))))))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(122847, 360), (122866, 720)]

theorem segOK : checkSeg 20 perms 122847 122867 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 122847 122867 1080 2281001750640 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 2281001750640)
    (SegSum.cons (w := 360) h122847 (SegSum.cons (w := 720) h122866 (show SegSum (P.leaf 36) [] 0 from rfl))) (by decide)

end RACert.S6N0.C0.S100
