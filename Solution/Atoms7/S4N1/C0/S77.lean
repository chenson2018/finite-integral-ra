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

namespace RACert.S4N1.C0.S77

open RACert RACert.Problem

theorem cover22374 : P.CoversSplit 24 10 22374 0xfffffffffafaaaaafffffffffafaaaaafffffffffafaaaaaffff000000000000cccccccc88888888cc00cc0088008800cccccccc88888888cc00000000000000fffffffffafaaaaa0000000000000000fffffffffafaaaaa00330000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 515, 522, 860, 916, 1202, 1210, 1251, 1259, 1601]) (by decide +kernel)

theorem c22374_0 : P.sumLeaves 24 22910976 500 = 7357170 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22374) (lo := 0) (len := 500) (W := 7357170) check rows elimOK (by decide) (by decide) cover22374 (by decide)
  decide +kernel

theorem c22374_1 : P.sumLeaves 24 22911476 341 = 11130149 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22374) (lo := 500) (len := 341) (W := 11130149) check rows elimOK (by decide) (by decide) cover22374 (by decide)
  decide +kernel

theorem c22374_2 : P.sumLeaves 24 22911817 115 = 14595663 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22374) (lo := 841) (len := 115) (W := 14595663) check rows elimOK (by decide) (by decide) cover22374 (by decide)
  decide +kernel

theorem c22374_3 : P.sumLeaves 24 22911932 68 = 22729778 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22374) (lo := 956) (len := 68) (W := 22729778) check rows elimOK (by decide) (by decide) cover22374 (by decide)
  decide +kernel

theorem h22374 : P.leaf 34 22374 = 55812760 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(500, 7357170), (341, 11130149), (115, 14595663), (68, 22729778)]) (.cons c22374_0 (.cons c22374_1 (.cons c22374_2 (.cons c22374_3 (.nil))))) (by decide) (by decide))

theorem cover22375 : P.CoversSplit 24 10 22375 0xfffffffffafaaaaafffffffffafaaaaafffffffffafaaaaaffff000000000000cccccccc88888888cc00cc0088008800cccccccc88888888cc00000000000000fffffffffafaaaaa0000000000000000fffffffffafaaaaa00330000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 522, 860, 916, 1202, 1210, 1251, 1259, 1601]) (by decide +kernel)

theorem c22375_0 : P.sumLeaves 24 22912000 500 = 18278228 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22375) (lo := 0) (len := 500) (W := 18278228) check rows elimOK (by decide) (by decide) cover22375 (by decide)
  decide +kernel

theorem c22375_1 : P.sumLeaves 24 22912500 341 = 27424754 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22375) (lo := 500) (len := 341) (W := 27424754) check rows elimOK (by decide) (by decide) cover22375 (by decide)
  decide +kernel

theorem c22375_2 : P.sumLeaves 24 22912841 115 = 33018404 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22375) (lo := 841) (len := 115) (W := 33018404) check rows elimOK (by decide) (by decide) cover22375 (by decide)
  decide +kernel

theorem c22375_3 : P.sumLeaves 24 22912956 68 = 50380280 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22375) (lo := 956) (len := 68) (W := 50380280) check rows elimOK (by decide) (by decide) cover22375 (by decide)
  decide +kernel

theorem h22375 : P.leaf 34 22375 = 129101666 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(500, 18278228), (341, 27424754), (115, 33018404), (68, 50380280)]) (.cons c22375_0 (.cons c22375_1 (.cons c22375_2 (.cons c22375_3 (.nil))))) (by decide) (by decide))

theorem cover22380 : P.CoversSplit 24 10 22380 0xcc00cc00c80088000000000000000000cc00cc00c80088000000000000000000cccccccc88808880cc00cc0088008800cccccccc88808880cc00000000000000cc00cc00c80088000000000000000000cc00cc00c800880000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 466, 473, 515, 522, 572, 916, 1210, 1251, 1601]) (ps := [(2, [465], [473])]) (by decide +kernel)

theorem c22380_0 : P.sumLeaves 24 22917120 891 = 4529308 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22380) (lo := 0) (len := 891) (W := 4529308) check rows elimOK (by decide) (by decide) cover22380 (by decide)
  decide +kernel

theorem c22380_1 : P.sumLeaves 24 22918011 133 = 5368132 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22380) (lo := 891) (len := 133) (W := 5368132) check rows elimOK (by decide) (by decide) cover22380 (by decide)
  decide +kernel

theorem h22380 : P.leaf 34 22380 = 9897440 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(891, 4529308), (133, 5368132)]) (.cons c22380_0 (.cons c22380_1 (.nil))) (by decide) (by decide))

theorem cover22381 : P.CoversSplit 24 10 22381 0xcc00cc00c80088000000000000000000cc00cc00c80088000000000000000000cc00cc00880088000000000000000000cc00cc00880088000000000000000000cc00cc00c80088000000000000000000cc00cc00c800880000000000000000000000000000000000003300330022002200000000000000000033000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 515, 522, 572, 860, 916, 1210, 1251, 1601]) (by decide +kernel)

theorem c22381_0 : P.sumLeaves 24 22918144 1024 = 20770908 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22381) (lo := 0) (len := 1024) (W := 20770908) check rows elimOK (by decide) (by decide) cover22381 (by decide)
  decide +kernel

theorem h22381 : P.leaf 34 22381 = 20770908 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 20770908)]) (.cons c22381_0 (.nil)) (by decide) (by decide))

theorem cover22382 : P.CoversSplit 24 10 22382 0xfffffffffafaaaaafffffffffafaaaaafffffffffafaaaaaffff000000000000cccccccc88888888cc00cc0088008800cccccccc88888888cc00000000000000fffffffffafaaaaa0000000000000000fffffffffafaaaaa00330000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 515, 522, 860, 916, 1202, 1210, 1251, 1259, 1601]) (by decide +kernel)

theorem c22382_0 : P.sumLeaves 24 22919168 500 = 10849864 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22382) (lo := 0) (len := 500) (W := 10849864) check rows elimOK (by decide) (by decide) cover22382 (by decide)
  decide +kernel

theorem c22382_1 : P.sumLeaves 24 22919668 341 = 19607928 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22382) (lo := 500) (len := 341) (W := 19607928) check rows elimOK (by decide) (by decide) cover22382 (by decide)
  decide +kernel

theorem c22382_2 : P.sumLeaves 24 22920009 115 = 26930546 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22382) (lo := 841) (len := 115) (W := 26930546) check rows elimOK (by decide) (by decide) cover22382 (by decide)
  decide +kernel

theorem c22382_3 : P.sumLeaves 24 22920124 68 = 37291372 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22382) (lo := 956) (len := 68) (W := 37291372) check rows elimOK (by decide) (by decide) cover22382 (by decide)
  decide +kernel

theorem h22382 : P.leaf 34 22382 = 94679710 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(500, 10849864), (341, 19607928), (115, 26930546), (68, 37291372)]) (.cons c22382_0 (.cons c22382_1 (.cons c22382_2 (.cons c22382_3 (.nil))))) (by decide) (by decide))

theorem cover22383 : P.CoversSplit 24 10 22383 0xfffffffffafaaaaafffffffffafaaaaafffffffffafaaaaaffff000000000000cccccccc88888888cc00cc0088008800cccccccc88888888cc00000000000000fffffffffafaaaaa0000000000000000fffffffffafaaaaa00330000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 522, 860, 916, 1202, 1210, 1251, 1259, 1601]) (by decide +kernel)

theorem c22383_0 : P.sumLeaves 24 22920192 500 = 25829336 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22383) (lo := 0) (len := 500) (W := 25829336) check rows elimOK (by decide) (by decide) cover22383 (by decide)
  decide +kernel

theorem c22383_1 : P.sumLeaves 24 22920692 341 = 40806556 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22383) (lo := 500) (len := 341) (W := 40806556) check rows elimOK (by decide) (by decide) cover22383 (by decide)
  decide +kernel

theorem c22383_2 : P.sumLeaves 24 22921033 115 = 51104371 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22383) (lo := 841) (len := 115) (W := 51104371) check rows elimOK (by decide) (by decide) cover22383 (by decide)
  decide +kernel

theorem c22383_3 : P.sumLeaves 24 22921148 68 = 76624934 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22383) (lo := 956) (len := 68) (W := 76624934) check rows elimOK (by decide) (by decide) cover22383 (by decide)
  decide +kernel

theorem h22383 : P.leaf 34 22383 = 194365197 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(500, 25829336), (341, 40806556), (115, 51104371), (68, 76624934)]) (.cons c22383_0 (.cons c22383_1 (.cons c22383_2 (.cons c22383_3 (.nil))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(22374, 24), (22375, 48), (22380, 48), (22381, 48), (22382, 48), (22383, 48)]

theorem segOK : checkSeg 16 perms 22374 22389 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 22374 22389 264 22882622448 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 22882622448)
    (SegSum.cons (w := 24) h22374 (SegSum.cons (w := 48) h22375 (SegSum.cons (w := 48) h22380 (SegSum.cons (w := 48) h22381 (SegSum.cons (w := 48) h22382 (SegSum.cons (w := 48) h22383 (show SegSum (P.leaf 34) [] 0 from rfl))))))) (by decide)

end RACert.S4N1.C0.S77
