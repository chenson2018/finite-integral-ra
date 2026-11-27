/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Atoms7.S6N0.C0.Actions

/-! Generated identity-class certificate for the product-row count. -/

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option Elab.async false

@[expose] public section

namespace RACert.S6N0.C0.S65

open RACert RACert.Problem

theorem cover90052 : P.CoversSplit 26 10 90052 0xff000000ff030501ff000000ff030500ff000000ff030500fa000000c8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 874, 922, 923, 972, 979, 1266, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f90052 (i : ℕ) := rowWeight keep4 twice4 i * P.leaf 26 (92213248 + i)

theorem c90052_0 : rowSum f90052 0 1024 = 1735428 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 90052) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover90052 (by decide)
  decide +kernel

theorem sum90052 : rowSum f90052 0 1024 = 1735428 :=
  c90052_0

theorem h90052 : P.leaf 36 90052 = 1735428 :=
  leaf_weighted (k := 26) (d := 10) (H := 90052) (keep := keep4) (twice := twice4) rows (by decide) (by decide) bal4 (invRow4 (H := 90052) (by decide) (by decide +kernel)) sum90052

theorem cover90053 : P.CoversSplit 26 10 90053 0xff000000ff030501ff000000ff030500ff000000ff030500fa000000c8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 922, 923, 972, 979, 1266, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f90053 (i : ℕ) := rowWeight keep4 twice4 i * P.leaf 26 (92214272 + i)

theorem c90053_0 : rowSum f90053 0 1024 = 90399838 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 90053) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover90053 (by decide)
  decide +kernel

theorem sum90053 : rowSum f90053 0 1024 = 90399838 :=
  c90053_0

theorem h90053 : P.leaf 36 90053 = 90399838 :=
  leaf_weighted (k := 26) (d := 10) (H := 90053) (keep := keep4) (twice := twice4) rows (by decide) (by decide) bal4 (invRow4 (H := 90053) (by decide) (by decide +kernel)) sum90053

theorem cover90054 : P.CoversSplit 26 10 90054 0xff000000ff030501ff000000ff030500ff000000ff030500fa000000c8000000000000000000000000000000000000000000000000000000000000000000000000000000333301010000000033330100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 874, 972, 979, 1266, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c90054_0 : P.sumLeaves 26 92215296 1024 = 13606316 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90054) (lo := 0) (len := 1024) (W := 13606316) check rows elimOK (by decide) (by decide) cover90054 (by decide)
  decide +kernel

theorem h90054 : P.leaf 36 90054 = 13606316 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 13606316)]) (.cons c90054_0 (.nil)) (by decide) (by decide))

theorem cover90055 : P.CoversSplit 26 10 90055 0xff000000ff030501ff000000ff030500ff000000ff030500fa000000c8000000000000000000000000000000000000000000000000000000000000000000000000000000333301010000000033330100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 972, 979, 1266, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c90055_0 : P.sumLeaves 26 92216320 1024 = 162593629 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90055) (lo := 0) (len := 1024) (W := 162593629) check rows elimOK (by decide) (by decide) cover90055 (by decide)
  decide +kernel

theorem h90055 : P.leaf 36 90055 = 162593629 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 162593629)]) (.cons c90055_0 (.nil)) (by decide) (by decide))

theorem cover90060 : P.CoversSplit 26 10 90060 0xffff0000fffc0504ffff0000fffc0500ffff0000fffc0500fafa0000c8c80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 874, 922, 923, 972, 979, 1266, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c90060_0 : P.sumLeaves 26 92221440 989 = 17630970 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90060) (lo := 0) (len := 989) (W := 17630970) check rows elimOK (by decide) (by decide) cover90060 (by decide)
  decide +kernel

theorem c90060_1 : P.sumLeaves 26 92222429 35 = 15552054 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90060) (lo := 989) (len := 35) (W := 15552054) check rows elimOK (by decide) (by decide) cover90060 (by decide)
  decide +kernel

theorem h90060 : P.leaf 36 90060 = 33183024 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(989, 17630970), (35, 15552054)]) (.cons c90060_0 (.cons c90060_1 (.nil))) (by decide) (by decide))

theorem cover90061 : P.CoversSplit 26 10 90061 0xffff0000fffc0504ffff0000fffc0500ffff0000fffc0500fafa0000c8c80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 922, 923, 972, 979, 1266, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c90061_0 : P.sumLeaves 26 92222464 989 = 157489055 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90061) (lo := 0) (len := 989) (W := 157489055) check rows elimOK (by decide) (by decide) cover90061 (by decide)
  decide +kernel

theorem c90061_1 : P.sumLeaves 26 92223453 35 = 85286112 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90061) (lo := 989) (len := 35) (W := 85286112) check rows elimOK (by decide) (by decide) cover90061 (by decide)
  decide +kernel

theorem h90061 : P.leaf 36 90061 = 242775167 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(989, 157489055), (35, 85286112)]) (.cons c90061_0 (.cons c90061_1 (.nil))) (by decide) (by decide))

theorem cover90062 : P.CoversSplit 26 10 90062 0xffff0000fffc0504ffff0000fffc0500ffff0000fffc0500fafa0000c8c800000000000000000000000000000000000000000000000000000000000000000000ffff0000ffcc0504ffff0000ffcc0500ffff0000cc000400fafa0000c80000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 874, 972, 979, 1266, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c90062_0 : P.sumLeaves 26 92223488 511 = 28054717 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90062) (lo := 0) (len := 511) (W := 28054717) check rows elimOK (by decide) (by decide) cover90062 (by decide)
  decide +kernel

theorem c90062_1 : P.sumLeaves 26 92223999 477 = 43373458 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90062) (lo := 511) (len := 477) (W := 43373458) check rows elimOK (by decide) (by decide) cover90062 (by decide)
  decide +kernel

theorem c90062_2 : P.sumLeaves 26 92224476 36 = 25391014 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90062) (lo := 988) (len := 36) (W := 25391014) check rows elimOK (by decide) (by decide) cover90062 (by decide)
  decide +kernel

theorem h90062 : P.leaf 36 90062 = 96819189 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(511, 28054717), (477, 43373458), (36, 25391014)]) (.cons c90062_0 (.cons c90062_1 (.cons c90062_2 (.nil)))) (by decide) (by decide))

theorem cover90063 : P.CoversSplit 26 10 90063 0xffff0000fffc0504ffff0000fffc0500ffff0000fffc0500fafa0000c8c800000000000000000000000000000000000000000000000000000000000000000000ffff0000ffcc0504ffff0000ffcc0500ffff0000cc000400fafa0000c80000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 972, 979, 1266, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c90063_0 : P.sumLeaves 26 92224512 511 = 139006792 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90063) (lo := 0) (len := 511) (W := 139006792) check rows elimOK (by decide) (by decide) cover90063 (by decide)
  decide +kernel

theorem c90063_1 : P.sumLeaves 26 92225023 477 = 303181552 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90063) (lo := 511) (len := 477) (W := 303181552) check rows elimOK (by decide) (by decide) cover90063 (by decide)
  decide +kernel

theorem c90063_2 : P.sumLeaves 26 92225500 36 = 132750948 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90063) (lo := 988) (len := 36) (W := 132750948) check rows elimOK (by decide) (by decide) cover90063 (by decide)
  decide +kernel

theorem h90063 : P.leaf 36 90063 = 574939292 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(511, 139006792), (477, 303181552), (36, 132750948)]) (.cons c90063_0 (.cons c90063_1 (.cons c90063_2 (.nil)))) (by decide) (by decide))

theorem cover90070 : P.CoversSplit 26 10 90070 0xff000000ff030501ff000000ff030500ff000000ff030500fa000000c8000000050005000501050100000000000000000500050005010500000000000000000000000000333301010000000033330100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 874, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f90070 (i : ℕ) := rowWeight keep4 twice4 i * P.leaf 26 (92231680 + i)

theorem c90070_0 : rowSum f90070 0 1024 = 136726445 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 90070) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover90070 (by decide)
  decide +kernel

theorem sum90070 : rowSum f90070 0 1024 = 136726445 :=
  c90070_0

theorem h90070 : P.leaf 36 90070 = 136726445 :=
  leaf_weighted (k := 26) (d := 10) (H := 90070) (keep := keep4) (twice := twice4) rows (by decide) (by decide) bal4 (invRow4 (H := 90070) (by decide) (by decide +kernel)) sum90070

theorem cover90071 : P.CoversSplit 26 10 90071 0xff000000ff030501ff000000ff030500ff000000ff030500fa000000c8000000050005000501050100000000000000000500050005010500000000000000000000000000333301010000000033330100000000000000000000000000000000000000000001010101000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f90071 (i : ℕ) := rowWeight keep4 twice4 i * P.leaf 26 (92232704 + i)

theorem c90071_0 : rowSum f90071 0 1024 = 268401241 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 90071) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover90071 (by decide)
  decide +kernel

theorem sum90071 : rowSum f90071 0 1024 = 268401241 :=
  c90071_0

theorem h90071 : P.leaf 36 90071 = 268401241 :=
  leaf_weighted (k := 26) (d := 10) (H := 90071) (keep := keep4) (twice := twice4) rows (by decide) (by decide) bal4 (invRow4 (H := 90071) (by decide) (by decide +kernel)) sum90071

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

def seg : List (ℕ × ℕ) := [(90052, 360), (90053, 360), (90054, 720), (90055, 720), (90060, 720), (90061, 720), (90062, 720), (90063, 720), (90070, 360), (90071, 360), (90076, 720), (90077, 720), (90078, 720)]

theorem segOK : checkSeg 20 perms 90052 90079 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 90052 90079 7920 1872046394640 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 1872046394640)
    (SegSum.cons (w := 360) h90052 (SegSum.cons (w := 360) h90053 (SegSum.cons (w := 720) h90054 (SegSum.cons (w := 720) h90055 (SegSum.cons (w := 720) h90060 (SegSum.cons (w := 720) h90061 (SegSum.cons (w := 720) h90062 (SegSum.cons (w := 720) h90063 (SegSum.cons (w := 360) h90070 (SegSum.cons (w := 360) h90071 (SegSum.cons (w := 720) h90076 (SegSum.cons (w := 720) h90077 (SegSum.cons (w := 720) h90078 (show SegSum (P.leaf 36) [] 0 from rfl)))))))))))))) (by decide)

end RACert.S6N0.C0.S65
