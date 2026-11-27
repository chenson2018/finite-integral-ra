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

namespace RACert.S6N0.C0.S72

open RACert RACert.Problem

theorem cover90076 : P.CoversSplit 26 10 90076 0xffff0000fffc0504ffff0000fffc0500ffff0000fffc0500fafa0000c8c80000050505050504050400000000000000000505050505040500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 874, 922, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c90076_0 : P.sumLeaves 26 92237824 947 = 79654741 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90076) (lo := 0) (len := 947) (W := 79654741) check rows elimOK (by decide) (by decide) cover90076 (by decide)
  decide +kernel

theorem c90076_1 : P.sumLeaves 26 92238771 77 = 142416210 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90076) (lo := 947) (len := 77) (W := 142416210) check rows elimOK (by decide) (by decide) cover90076 (by decide)
  decide +kernel

theorem h90076 : P.leaf 36 90076 = 222070951 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(947, 79654741), (77, 142416210)]) (.cons c90076_0 (.cons c90076_1 (.nil))) (by decide) (by decide))

theorem cover90077 : P.CoversSplit 26 10 90077 0xffff0000fffc0504ffff0000fffc0500ffff0000fffc0500fafa0000c8c80000050505050504050400000000000000000505050505040500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 922, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c90077_0 : P.sumLeaves 26 92238848 947 = 183832405 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90077) (lo := 0) (len := 947) (W := 183832405) check rows elimOK (by decide) (by decide) cover90077 (by decide)
  decide +kernel

theorem c90077_1 : P.sumLeaves 26 92239795 77 = 272257236 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90077) (lo := 947) (len := 77) (W := 272257236) check rows elimOK (by decide) (by decide) cover90077 (by decide)
  decide +kernel

theorem h90077 : P.leaf 36 90077 = 456089641 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(947, 183832405), (77, 272257236)]) (.cons c90077_0 (.cons c90077_1 (.nil))) (by decide) (by decide))

theorem cover90078 : P.CoversSplit 26 10 90078 0xffff0000fffc0504ffff0000fffc0500ffff0000fffc0500fafa0000c8c800000505050505040504000000000000000005050505050405000000000000000000ffff0000ffcc0504ffff0000ffcc0500ffff0000cc000400fafa0000c80000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 874, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c90078_0 : P.sumLeaves 26 92239872 511 = 146528874 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90078) (lo := 0) (len := 511) (W := 146528874) check rows elimOK (by decide) (by decide) cover90078 (by decide)
  decide +kernel

theorem c90078_1 : P.sumLeaves 26 92240383 435 = 182328926 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90078) (lo := 511) (len := 435) (W := 182328926) check rows elimOK (by decide) (by decide) cover90078 (by decide)
  decide +kernel

theorem c90078_2 : P.sumLeaves 26 92240818 78 = 220497952 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90078) (lo := 946) (len := 78) (W := 220497952) check rows elimOK (by decide) (by decide) cover90078 (by decide)
  decide +kernel

theorem h90078 : P.leaf 36 90078 = 549355752 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(511, 146528874), (435, 182328926), (78, 220497952)]) (.cons c90078_0 (.cons c90078_1 (.cons c90078_2 (.nil)))) (by decide) (by decide))

theorem cover90079 : P.CoversSplit 26 10 90079 0xffff0000fffc0504ffff0000fffc0500ffff0000fffc0500fafa0000c8c800000505050505040504000000000000000005050505050405000000000000000000ffff0000ffcc0504ffff0000ffcc0500ffff0000cc000400fafa0000c80000000505050505040504000000000000000005050505040004000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c90079_0 : P.sumLeaves 26 92240896 471 = 156307198 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90079) (lo := 0) (len := 471) (W := 156307198) check rows elimOK (by decide) (by decide) cover90079 (by decide)
  decide +kernel

theorem c90079_1 : P.sumLeaves 26 92241367 419 = 333125531 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90079) (lo := 471) (len := 419) (W := 333125531) check rows elimOK (by decide) (by decide) cover90079 (by decide)
  decide +kernel

theorem c90079_2 : P.sumLeaves 26 92241786 134 = 508326490 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90079) (lo := 890) (len := 134) (W := 508326490) check rows elimOK (by decide) (by decide) cover90079 (by decide)
  decide +kernel

theorem h90079 : P.leaf 36 90079 = 997759219 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(471, 156307198), (419, 333125531), (134, 508326490)]) (.cons c90079_0 (.cons c90079_1 (.cons c90079_2 (.nil)))) (by decide) (by decide))

theorem cover90092 : P.CoversSplit 26 10 90092 0xfffffffffffcfaf8fffffffafffcfaf8fffffffffffcfac8fafafafac8c8c8c8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [874, 922, 923, 972, 979, 1266, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c90092_0 : P.sumLeaves 26 92254208 905 = 84252734 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90092) (lo := 0) (len := 905) (W := 84252734) check rows elimOK (by decide) (by decide) cover90092 (by decide)
  decide +kernel

theorem c90092_1 : P.sumLeaves 26 92255113 108 = 160688309 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90092) (lo := 905) (len := 108) (W := 160688309) check rows elimOK (by decide) (by decide) cover90092 (by decide)
  decide +kernel

theorem c90092_2 : P.sumLeaves 26 92255221 11 = 65044412 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90092) (lo := 1013) (len := 11) (W := 65044412) check rows elimOK (by decide) (by decide) cover90092 (by decide)
  decide +kernel

theorem h90092 : P.leaf 36 90092 = 309985455 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(905, 84252734), (108, 160688309), (11, 65044412)]) (.cons c90092_0 (.cons c90092_1 (.cons c90092_2 (.nil)))) (by decide) (by decide))

theorem cover90093 : P.CoversSplit 26 10 90093 0xfffffffffffcfaf8fffffffafffcfaf8fffffffffffcfac8fafafafac8c8c8c8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [922, 923, 972, 979, 1266, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c90093_0 : P.sumLeaves 26 92255232 905 = 217335749 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90093) (lo := 0) (len := 905) (W := 217335749) check rows elimOK (by decide) (by decide) cover90093 (by decide)
  decide +kernel

theorem c90093_1 : P.sumLeaves 26 92256137 108 = 341655008 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90093) (lo := 905) (len := 108) (W := 341655008) check rows elimOK (by decide) (by decide) cover90093 (by decide)
  decide +kernel

theorem c90093_2 : P.sumLeaves 26 92256245 11 = 88344944 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90093) (lo := 1013) (len := 11) (W := 88344944) check rows elimOK (by decide) (by decide) cover90093 (by decide)
  decide +kernel

theorem h90093 : P.leaf 36 90093 = 647335701 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(905, 217335749), (108, 341655008), (11, 88344944)]) (.cons c90093_0 (.cons c90093_1 (.cons c90093_2 (.nil)))) (by decide) (by decide))

theorem cover90094 : P.CoversSplit 26 10 90094 0xfffffffffffcfaf8fffffffafffcfaf8fffffffffffcfac8fafafafac8c8c8c80000000000000000000000000000000000000000000000000000000000000000ffffffffffccfac8fffffffaffccfac8ffffffffcc00c800fafafafac800c8000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [874, 922, 972, 979, 1266, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c90094_0 : P.sumLeaves 26 92256256 424 = 81109778 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90094) (lo := 0) (len := 424) (W := 81109778) check rows elimOK (by decide) (by decide) cover90094 (by decide)
  decide +kernel

theorem c90094_1 : P.sumLeaves 26 92256680 387 = 192387560 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90094) (lo := 424) (len := 387) (W := 192387560) check rows elimOK (by decide) (by decide) cover90094 (by decide)
  decide +kernel

theorem c90094_2 : P.sumLeaves 26 92257067 116 = 210938550 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90094) (lo := 811) (len := 116) (W := 210938550) check rows elimOK (by decide) (by decide) cover90094 (by decide)
  decide +kernel

theorem c90094_3 : P.sumLeaves 26 92257183 97 = 391892392 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90094) (lo := 927) (len := 97) (W := 391892392) check rows elimOK (by decide) (by decide) cover90094 (by decide)
  decide +kernel

theorem h90094 : P.leaf 36 90094 = 876328280 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(424, 81109778), (387, 192387560), (116, 210938550), (97, 391892392)]) (.cons c90094_0 (.cons c90094_1 (.cons c90094_2 (.cons c90094_3 (.nil))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(90076, 720), (90077, 720), (90078, 720), (90079, 720), (90092, 360), (90093, 360), (90094, 720)]

theorem segOK : checkSeg 20 perms 90076 90095 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 90076 90095 4320 2577790383120 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 2577790383120)
    (SegSum.cons (w := 720) h90076 (SegSum.cons (w := 720) h90077 (SegSum.cons (w := 720) h90078 (SegSum.cons (w := 720) h90079 (SegSum.cons (w := 360) h90092 (SegSum.cons (w := 360) h90093 (SegSum.cons (w := 720) h90094 (show SegSum (P.leaf 36) [] 0 from rfl)))))))) (by decide)

end RACert.S6N0.C0.S72
