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

namespace RACert.S6N0.C0.S71

open RACert RACert.Problem

theorem cover90047 : P.CoversSplit 26 10 90047 0xffffffff00000000fffffffa00000000ffffffff00000030fafafafa00000000fffff0f000000000fafaf0f000000000fffff0f000000030fafaf0f00000000000000000000000000000000000000000003300330000000000320032000000000000000000000000000000000000000000330030000000000032003000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [538, 922, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c90047_0 : P.sumLeaves 26 92208128 749 = 133234104 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90047) (lo := 0) (len := 749) (W := 133234104) check rows elimOK (by decide) (by decide) cover90047 (by decide)
  decide +kernel

theorem c90047_1 : P.sumLeaves 26 92208877 200 = 361120772 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90047) (lo := 749) (len := 200) (W := 361120772) check rows elimOK (by decide) (by decide) cover90047 (by decide)
  decide +kernel

theorem c90047_2 : P.sumLeaves 26 92209077 75 = 266296764 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90047) (lo := 949) (len := 75) (W := 266296764) check rows elimOK (by decide) (by decide) cover90047 (by decide)
  decide +kernel

theorem h90047 : P.leaf 36 90047 = 760651640 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(749, 133234104), (200, 361120772), (75, 266296764)]) (.cons c90047_0 (.cons c90047_1 (.cons c90047_2 (.nil)))) (by decide) (by decide))

theorem cover90052 : P.CoversSplit 26 10 90052 0xff000000ff030501ff000000ff030500ff000000ff030500fa000000c8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 874, 922, 923, 972, 979, 1266, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c90052_0 : P.sumLeaves 26 92213248 1024 = 1735428 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90052) (lo := 0) (len := 1024) (W := 1735428) check rows elimOK (by decide) (by decide) cover90052 (by decide)
  decide +kernel

theorem h90052 : P.leaf 36 90052 = 1735428 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1735428)]) (.cons c90052_0 (.nil)) (by decide) (by decide))

theorem cover90053 : P.CoversSplit 26 10 90053 0xff000000ff030501ff000000ff030500ff000000ff030500fa000000c8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 922, 923, 972, 979, 1266, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c90053_0 : P.sumLeaves 26 92214272 1024 = 90399838 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90053) (lo := 0) (len := 1024) (W := 90399838) check rows elimOK (by decide) (by decide) cover90053 (by decide)
  decide +kernel

theorem h90053 : P.leaf 36 90053 = 90399838 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 90399838)]) (.cons c90053_0 (.nil)) (by decide) (by decide))

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

theorem c90070_0 : P.sumLeaves 26 92231680 988 = 91677545 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90070) (lo := 0) (len := 988) (W := 91677545) check rows elimOK (by decide) (by decide) cover90070 (by decide)
  decide +kernel

theorem c90070_1 : P.sumLeaves 26 92232668 36 = 45048900 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90070) (lo := 988) (len := 36) (W := 45048900) check rows elimOK (by decide) (by decide) cover90070 (by decide)
  decide +kernel

theorem h90070 : P.leaf 36 90070 = 136726445 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(988, 91677545), (36, 45048900)]) (.cons c90070_0 (.cons c90070_1 (.nil))) (by decide) (by decide))

theorem cover90071 : P.CoversSplit 26 10 90071 0xff000000ff030501ff000000ff030500ff000000ff030500fa000000c8000000050005000501050100000000000000000500050005010500000000000000000000000000333301010000000033330100000000000000000000000000000000000000000001010101000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c90071_0 : P.sumLeaves 26 92232704 984 = 178353473 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90071) (lo := 0) (len := 984) (W := 178353473) check rows elimOK (by decide) (by decide) cover90071 (by decide)
  decide +kernel

theorem c90071_1 : P.sumLeaves 26 92233688 40 = 90047768 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 90071) (lo := 984) (len := 40) (W := 90047768) check rows elimOK (by decide) (by decide) cover90071 (by decide)
  decide +kernel

theorem h90071 : P.leaf 36 90071 = 268401241 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(984, 178353473), (40, 90047768)]) (.cons c90071_0 (.cons c90071_1 (.nil))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(90047, 720), (90052, 360), (90053, 360), (90054, 720), (90055, 720), (90060, 720), (90061, 720), (90062, 720), (90063, 720), (90070, 360), (90071, 360)]

theorem segOK : checkSeg 20 perms 90047 90076 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 90047 90076 6480 1535903807760 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 1535903807760)
    (SegSum.cons (w := 720) h90047 (SegSum.cons (w := 360) h90052 (SegSum.cons (w := 360) h90053 (SegSum.cons (w := 720) h90054 (SegSum.cons (w := 720) h90055 (SegSum.cons (w := 720) h90060 (SegSum.cons (w := 720) h90061 (SegSum.cons (w := 720) h90062 (SegSum.cons (w := 720) h90063 (SegSum.cons (w := 360) h90070 (SegSum.cons (w := 360) h90071 (show SegSum (P.leaf 36) [] 0 from rfl)))))))))))) (by decide)

end RACert.S6N0.C0.S71
