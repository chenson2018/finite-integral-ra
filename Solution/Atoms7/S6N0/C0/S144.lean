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

namespace RACert.S6N0.C0.S144

open RACert RACert.Problem

theorem cover520159 : P.CoversSplit 26 10 520159 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffafaffccfac8fffffffffffffffffffffafafffffafafffffffffffffffffffffafaffccfac8ffffffffffffffffffffffffffffffffffffffffffccffccfffffafaffccfac8fffffffffffffffffffffafafffffafaffffffffffccffccfffffafaffccfac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 881, 1658, 1665]) (by decide +kernel)

theorem c520159_0 : P.sumLeaves 26 532642816 119 = 1003034719 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 520159) (lo := 0) (len := 119) (W := 1003034719) check rows elimOK (by decide) (by decide) cover520159 (by decide)
  decide +kernel

theorem c520159_1 : P.sumLeaves 26 532642935 104 = 1366005230 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 520159) (lo := 119) (len := 104) (W := 1366005230) check rows elimOK (by decide) (by decide) cover520159 (by decide)
  decide +kernel

theorem c520159_2 : P.sumLeaves 26 532643039 119 = 1515229069 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 520159) (lo := 223) (len := 119) (W := 1515229069) check rows elimOK (by decide) (by decide) cover520159 (by decide)
  decide +kernel

theorem c520159_3 : P.sumLeaves 26 532643158 96 = 1583973025 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 520159) (lo := 342) (len := 96) (W := 1583973025) check rows elimOK (by decide) (by decide) cover520159 (by decide)
  decide +kernel

theorem c520159_4 : P.sumLeaves 26 532643254 109 = 2066385899 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 520159) (lo := 438) (len := 109) (W := 2066385899) check rows elimOK (by decide) (by decide) cover520159 (by decide)
  decide +kernel

theorem c520159_5 : P.sumLeaves 26 532643363 100 = 1576935127 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 520159) (lo := 547) (len := 100) (W := 1576935127) check rows elimOK (by decide) (by decide) cover520159 (by decide)
  decide +kernel

theorem c520159_6 : P.sumLeaves 26 532643463 102 = 1826207934 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 520159) (lo := 647) (len := 102) (W := 1826207934) check rows elimOK (by decide) (by decide) cover520159 (by decide)
  decide +kernel

theorem c520159_7 : P.sumLeaves 26 532643565 111 = 1930641910 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 520159) (lo := 749) (len := 111) (W := 1930641910) check rows elimOK (by decide) (by decide) cover520159 (by decide)
  decide +kernel

theorem c520159_8 : P.sumLeaves 26 532643676 96 = 1963589082 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 520159) (lo := 860) (len := 96) (W := 1963589082) check rows elimOK (by decide) (by decide) cover520159 (by decide)
  decide +kernel

theorem c520159_9 : P.sumLeaves 26 532643772 68 = 1920184714 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 520159) (lo := 956) (len := 68) (W := 1920184714) check rows elimOK (by decide) (by decide) cover520159 (by decide)
  decide +kernel

theorem h520159 : P.leaf 36 520159 = 16752186709 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(119, 1003034719), (104, 1366005230), (119, 1515229069), (96, 1583973025), (109, 2066385899), (100, 1576935127), (102, 1826207934), (111, 1930641910), (96, 1963589082), (68, 1920184714)]) (.cons c520159_0 (.cons c520159_1 (.cons c520159_2 (.cons c520159_3 (.cons c520159_4 (.cons c520159_5 (.cons c520159_6 (.cons c520159_7 (.cons c520159_8 (.cons c520159_9 (.nil))))))))))) (by decide) (by decide))

theorem cover520191 : P.CoversSplit 26 10 520191 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffafaffccfac8fffffffffffffffffffffafafffffafafffffffffffffffffffffafaffccfac8ffffffffffffffffffffffffffffffffffffffffffccffccfffffafaffccfac8fffffffffffffffffffffafafffffafaffffffffffccffccfffffafaffccfac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [881, 1658, 1665]) (by decide +kernel)

theorem c520191_0 : P.sumLeaves 26 532675584 119 = 1317088114 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 520191) (lo := 0) (len := 119) (W := 1317088114) check rows elimOK (by decide) (by decide) cover520191 (by decide)
  decide +kernel

theorem c520191_1 : P.sumLeaves 26 532675703 104 = 1659148763 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 520191) (lo := 119) (len := 104) (W := 1659148763) check rows elimOK (by decide) (by decide) cover520191 (by decide)
  decide +kernel

theorem c520191_2 : P.sumLeaves 26 532675807 119 = 1811280742 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 520191) (lo := 223) (len := 119) (W := 1811280742) check rows elimOK (by decide) (by decide) cover520191 (by decide)
  decide +kernel

theorem c520191_3 : P.sumLeaves 26 532675926 96 = 1896535084 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 520191) (lo := 342) (len := 96) (W := 1896535084) check rows elimOK (by decide) (by decide) cover520191 (by decide)
  decide +kernel

theorem c520191_4 : P.sumLeaves 26 532676022 109 = 2452217318 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 520191) (lo := 438) (len := 109) (W := 2452217318) check rows elimOK (by decide) (by decide) cover520191 (by decide)
  decide +kernel

theorem c520191_5 : P.sumLeaves 26 532676131 100 = 2079965321 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 520191) (lo := 547) (len := 100) (W := 2079965321) check rows elimOK (by decide) (by decide) cover520191 (by decide)
  decide +kernel

theorem c520191_6 : P.sumLeaves 26 532676231 102 = 2195060824 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 520191) (lo := 647) (len := 102) (W := 2195060824) check rows elimOK (by decide) (by decide) cover520191 (by decide)
  decide +kernel

theorem c520191_7 : P.sumLeaves 26 532676333 111 = 2408922208 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 520191) (lo := 749) (len := 111) (W := 2408922208) check rows elimOK (by decide) (by decide) cover520191 (by decide)
  decide +kernel

theorem c520191_8 : P.sumLeaves 26 532676444 96 = 2374631210 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 520191) (lo := 860) (len := 96) (W := 2374631210) check rows elimOK (by decide) (by decide) cover520191 (by decide)
  decide +kernel

theorem c520191_9 : P.sumLeaves 26 532676540 68 = 2220112276 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 520191) (lo := 956) (len := 68) (W := 2220112276) check rows elimOK (by decide) (by decide) cover520191 (by decide)
  decide +kernel

theorem h520191 : P.leaf 36 520191 = 20414961860 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(119, 1317088114), (104, 1659148763), (119, 1811280742), (96, 1896535084), (109, 2452217318), (100, 2079965321), (102, 2195060824), (111, 2408922208), (96, 2374631210), (68, 2220112276)]) (.cons c520191_0 (.cons c520191_1 (.cons c520191_2 (.cons c520191_3 (.cons c520191_4 (.cons c520191_5 (.cons c520191_6 (.cons c520191_7 (.cons c520191_8 (.cons c520191_9 (.nil))))))))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(520159, 120), (520191, 90)]

theorem segOK : checkSeg 20 perms 520159 524286 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 520159 524286 210 3847608972480 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 3847608972480)
    (SegSum.cons (w := 120) h520159 (SegSum.cons (w := 90) h520191 (show SegSum (P.leaf 36) [] 0 from rfl))) (by decide)

end RACert.S6N0.C0.S144
