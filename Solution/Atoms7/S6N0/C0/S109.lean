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

namespace RACert.S6N0.C0.S109

open RACert RACert.Problem

theorem cover228079 : P.CoversSplit 26 10 228079 0xfffffffffffffffffffffffafffffafa00000000000000000000000000300000fffffffffffffffffffff0f0fffff0f00000000000000000000000000030000000000000003300330000000000330032000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [587, 972, 979, 1266, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c228079_0 : P.sumLeaves 26 233552896 735 = 161543854 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 228079) (lo := 0) (len := 735) (W := 161543854) check rows elimOK (by decide) (by decide) cover228079 (by decide)
  decide +kernel

theorem c228079_1 : P.sumLeaves 26 233553631 228 = 513914016 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 228079) (lo := 735) (len := 228) (W := 513914016) check rows elimOK (by decide) (by decide) cover228079 (by decide)
  decide +kernel

theorem c228079_2 : P.sumLeaves 26 233553859 61 = 608840602 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 228079) (lo := 963) (len := 61) (W := 608840602) check rows elimOK (by decide) (by decide) cover228079 (by decide)
  decide +kernel

theorem h228079 : P.leaf 36 228079 = 1284298472 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(735, 161543854), (228, 513914016), (61, 608840602)]) (.cons c228079_0 (.cons c228079_1 (.cons c228079_2 (.nil)))) (by decide) (by decide))

theorem cover228094 : P.CoversSplit 26 10 228094 0xfffffffffffffffffffffffafffffafa00000000000000000000000000300000fffffffffffffffffffff0f0fffff0f00000000000000000000000000030000000000000003300330000000000330032000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [587, 874, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c228094_0 : P.sumLeaves 26 233568256 735 = 156107164 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 228094) (lo := 0) (len := 735) (W := 156107164) check rows elimOK (by decide) (by decide) cover228094 (by decide)
  decide +kernel

theorem c228094_1 : P.sumLeaves 26 233568991 228 = 618910718 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 228094) (lo := 735) (len := 228) (W := 618910718) check rows elimOK (by decide) (by decide) cover228094 (by decide)
  decide +kernel

theorem c228094_2 : P.sumLeaves 26 233569219 61 = 671507232 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 228094) (lo := 963) (len := 61) (W := 671507232) check rows elimOK (by decide) (by decide) cover228094 (by decide)
  decide +kernel

theorem h228094 : P.leaf 36 228094 = 1446525114 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(735, 156107164), (228, 618910718), (61, 671507232)]) (.cons c228094_0 (.cons c228094_1 (.cons c228094_2 (.nil)))) (by decide) (by decide))

theorem cover228095 : P.CoversSplit 26 10 228095 0xfffffffffffffffffffffffafffffafa00000000000000000000000000300000fffffffffffffffffffff0f0fffff0f00000000000000000000000000030000000000000003300330000000000330032000000000000000000000000000000000000000000330033000000000033003000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [587, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c228095_0 : P.sumLeaves 26 233569280 721 = 252007779 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 228095) (lo := 0) (len := 721) (W := 252007779) check rows elimOK (by decide) (by decide) cover228095 (by decide)
  decide +kernel

theorem c228095_1 : P.sumLeaves 26 233570001 228 = 916170152 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 228095) (lo := 721) (len := 228) (W := 916170152) check rows elimOK (by decide) (by decide) cover228095 (by decide)
  decide +kernel

theorem c228095_2 : P.sumLeaves 26 233570229 75 = 1364898104 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 228095) (lo := 949) (len := 75) (W := 1364898104) check rows elimOK (by decide) (by decide) cover228095 (by decide)
  decide +kernel

theorem h228095 : P.leaf 36 228095 = 2533076035 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(721, 252007779), (228, 916170152), (75, 1364898104)]) (.cons c228095_0 (.cons c228095_1 (.cons c228095_2 (.nil)))) (by decide) (by decide))

theorem cover228335 : P.CoversSplit 26 10 228335 0xfffffffffffffffffffffffafffffafafffffffffffcffccfffffafaffccfac8fffffffffffffffffffffafafffffafafffffffffffcffccfffffafaffccfac8fffffffffffffffffffffffafffffafaffffffffffccffccfffffafaffccfac80000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [972, 979, 1266, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c228335_0 : P.sumLeaves 26 233815040 375 = 266098132 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 228335) (lo := 0) (len := 375) (W := 266098132) check rows elimOK (by decide) (by decide) cover228335 (by decide)
  decide +kernel

theorem c228335_1 : P.sumLeaves 26 233815415 102 = 400891180 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 228335) (lo := 375) (len := 102) (W := 400891180) check rows elimOK (by decide) (by decide) cover228335 (by decide)
  decide +kernel

theorem c228335_2 : P.sumLeaves 26 233815517 117 = 397703585 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 228335) (lo := 477) (len := 117) (W := 397703585) check rows elimOK (by decide) (by decide) cover228335 (by decide)
  decide +kernel

theorem c228335_3 : P.sumLeaves 26 233815634 104 = 345550439 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 228335) (lo := 594) (len := 104) (W := 345550439) check rows elimOK (by decide) (by decide) cover228335 (by decide)
  decide +kernel

theorem c228335_4 : P.sumLeaves 26 233815738 109 = 545427820 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 228335) (lo := 698) (len := 109) (W := 545427820) check rows elimOK (by decide) (by decide) cover228335 (by decide)
  decide +kernel

theorem c228335_5 : P.sumLeaves 26 233815847 108 = 932547328 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 228335) (lo := 807) (len := 108) (W := 932547328) check rows elimOK (by decide) (by decide) cover228335 (by decide)
  decide +kernel

theorem c228335_6 : P.sumLeaves 26 233815955 98 = 1119724640 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 228335) (lo := 915) (len := 98) (W := 1119724640) check rows elimOK (by decide) (by decide) cover228335 (by decide)
  decide +kernel

theorem c228335_7 : P.sumLeaves 26 233816053 11 = 198049936 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 228335) (lo := 1013) (len := 11) (W := 198049936) check rows elimOK (by decide) (by decide) cover228335 (by decide)
  decide +kernel

theorem h228335 : P.leaf 36 228335 = 4205993060 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(375, 266098132), (102, 400891180), (117, 397703585), (104, 345550439), (109, 545427820), (108, 932547328), (98, 1119724640), (11, 198049936)]) (.cons c228335_0 (.cons c228335_1 (.cons c228335_2 (.cons c228335_3 (.cons c228335_4 (.cons c228335_5 (.cons c228335_6 (.cons c228335_7 (.nil))))))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(228079, 720), (228094, 360), (228095, 360), (228335, 180)]

theorem segOK : checkSeg 20 perms 228079 228351 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 228079 228351 1620 3114430064280 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 3114430064280)
    (SegSum.cons (w := 720) h228079 (SegSum.cons (w := 360) h228094 (SegSum.cons (w := 360) h228095 (SegSum.cons (w := 180) h228335 (show SegSum (P.leaf 36) [] 0 from rfl))))) (by decide)

end RACert.S6N0.C0.S109
