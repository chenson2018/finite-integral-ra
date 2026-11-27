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

namespace RACert.S6N0.C0.S143

open RACert RACert.Problem

theorem cover262143 : P.CoversSplit 26 10 262143 0xfffffffffffffffffffffffffffffafaffffffffffffffccfffffafaffccfac8fffffffffffffffffffffafafffffafaffffffffffffffccfffffafaffccfac8fffffffffffffffffffffffffffffafaffffffffffccffccfffffafaffccfac8fffffffffffffffffffffafafffffafaffffffffffccffccfffffafaffccfac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c262143_0 : P.sumLeaves 26 268434432 119 = 877073866 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 262143) (lo := 0) (len := 119) (W := 877073866) check rows elimOK (by decide) (by decide) cover262143 (by decide)
  decide +kernel

theorem c262143_1 : P.sumLeaves 26 268434551 104 = 1034210508 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 262143) (lo := 119) (len := 104) (W := 1034210508) check rows elimOK (by decide) (by decide) cover262143 (by decide)
  decide +kernel

theorem c262143_2 : P.sumLeaves 26 268434655 119 = 1509752082 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 262143) (lo := 223) (len := 119) (W := 1509752082) check rows elimOK (by decide) (by decide) cover262143 (by decide)
  decide +kernel

theorem c262143_3 : P.sumLeaves 26 268434774 100 = 1879125960 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 262143) (lo := 342) (len := 100) (W := 1879125960) check rows elimOK (by decide) (by decide) cover262143 (by decide)
  decide +kernel

theorem c262143_4 : P.sumLeaves 26 268434874 109 = 2096525166 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 262143) (lo := 442) (len := 109) (W := 2096525166) check rows elimOK (by decide) (by decide) cover262143 (by decide)
  decide +kernel

theorem c262143_5 : P.sumLeaves 26 268434983 106 = 1876348510 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 262143) (lo := 551) (len := 106) (W := 1876348510) check rows elimOK (by decide) (by decide) cover262143 (by decide)
  decide +kernel

theorem c262143_6 : P.sumLeaves 26 268435089 100 = 2027673638 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 262143) (lo := 657) (len := 100) (W := 2027673638) check rows elimOK (by decide) (by decide) cover262143 (by decide)
  decide +kernel

theorem c262143_7 : P.sumLeaves 26 268435189 115 = 2473737862 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 262143) (lo := 757) (len := 115) (W := 2473737862) check rows elimOK (by decide) (by decide) cover262143 (by decide)
  decide +kernel

theorem c262143_8 : P.sumLeaves 26 268435304 100 = 2653838762 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 262143) (lo := 872) (len := 100) (W := 2653838762) check rows elimOK (by decide) (by decide) cover262143 (by decide)
  decide +kernel

theorem c262143_9 : P.sumLeaves 26 268435404 52 = 1676269104 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 262143) (lo := 972) (len := 52) (W := 1676269104) check rows elimOK (by decide) (by decide) cover262143 (by decide)
  decide +kernel

theorem h262143 : P.leaf 36 262143 = 18104555458 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(119, 877073866), (104, 1034210508), (119, 1509752082), (100, 1879125960), (109, 2096525166), (106, 1876348510), (100, 2027673638), (115, 2473737862), (100, 2653838762), (52, 1676269104)]) (.cons c262143_0 (.cons c262143_1 (.cons c262143_2 (.cons c262143_3 (.cons c262143_4 (.cons c262143_5 (.cons c262143_6 (.cons c262143_7 (.cons c262143_8 (.cons c262143_9 (.nil))))))))))) (by decide) (by decide))

theorem cover520157 : P.CoversSplit 26 10 520157 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffafaffccfac8fffffffffffffffffffffafafffffafafffffffffffffffffffffafaffccfac8ffffffffffffffffffffffffffffffffffffffffffccffccfffffafaffccfac8fffffffffffffffffffffafafffffafaffffffffffccffccfffffafaffccfac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 881, 1658, 1665]) (by decide +kernel)

theorem c520157_0 : P.sumLeaves 26 532640768 119 = 747334636 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 520157) (lo := 0) (len := 119) (W := 747334636) check rows elimOK (by decide) (by decide) cover520157 (by decide)
  decide +kernel

theorem c520157_1 : P.sumLeaves 26 532640887 104 = 1000937080 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 520157) (lo := 119) (len := 104) (W := 1000937080) check rows elimOK (by decide) (by decide) cover520157 (by decide)
  decide +kernel

theorem c520157_2 : P.sumLeaves 26 532640991 119 = 1246218701 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 520157) (lo := 223) (len := 119) (W := 1246218701) check rows elimOK (by decide) (by decide) cover520157 (by decide)
  decide +kernel

theorem c520157_3 : P.sumLeaves 26 532641110 96 = 1304257940 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 520157) (lo := 342) (len := 96) (W := 1304257940) check rows elimOK (by decide) (by decide) cover520157 (by decide)
  decide +kernel

theorem c520157_4 : P.sumLeaves 26 532641206 109 = 1705592179 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 520157) (lo := 438) (len := 109) (W := 1705592179) check rows elimOK (by decide) (by decide) cover520157 (by decide)
  decide +kernel

theorem c520157_5 : P.sumLeaves 26 532641315 100 = 1296533093 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 520157) (lo := 547) (len := 100) (W := 1296533093) check rows elimOK (by decide) (by decide) cover520157 (by decide)
  decide +kernel

theorem c520157_6 : P.sumLeaves 26 532641415 102 = 1477555582 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 520157) (lo := 647) (len := 102) (W := 1477555582) check rows elimOK (by decide) (by decide) cover520157 (by decide)
  decide +kernel

theorem c520157_7 : P.sumLeaves 26 532641517 111 = 1736168001 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 520157) (lo := 749) (len := 111) (W := 1736168001) check rows elimOK (by decide) (by decide) cover520157 (by decide)
  decide +kernel

theorem c520157_8 : P.sumLeaves 26 532641628 96 = 1786834370 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 520157) (lo := 860) (len := 96) (W := 1786834370) check rows elimOK (by decide) (by decide) cover520157 (by decide)
  decide +kernel

theorem c520157_9 : P.sumLeaves 26 532641724 68 = 1743020960 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 520157) (lo := 956) (len := 68) (W := 1743020960) check rows elimOK (by decide) (by decide) cover520157 (by decide)
  decide +kernel

theorem h520157 : P.leaf 36 520157 = 14044452542 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(119, 747334636), (104, 1000937080), (119, 1246218701), (96, 1304257940), (109, 1705592179), (100, 1296533093), (102, 1477555582), (111, 1736168001), (96, 1786834370), (68, 1743020960)]) (.cons c520157_0 (.cons c520157_1 (.cons c520157_2 (.cons c520157_3 (.cons c520157_4 (.cons c520157_5 (.cons c520157_6 (.cons c520157_7 (.cons c520157_8 (.cons c520157_9 (.nil))))))))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(262143, 90), (520157, 30)]

theorem segOK : checkSeg 20 perms 262143 520159 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 262143 520159 120 2050743567480 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 2050743567480)
    (SegSum.cons (w := 90) h262143 (SegSum.cons (w := 30) h520157 (show SegSum (P.leaf 36) [] 0 from rfl))) (by decide)

end RACert.S6N0.C0.S143
