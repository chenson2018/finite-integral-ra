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

namespace RACert.S6N0.C0.S89

open RACert RACert.Problem

theorem cover621310 : P.CoversSplit 26 10 621310 0xfffffffffffffafafffffffafffffafafffffffffffcfac8fffffffafffcfac8fffffafafffffafafffffafafffffafafffffafafffcfac8fffffafafffcfac8fffffffffffffafafffffffafffffafaffffffffccccc8c8fffffffaccccc8c80000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [587, 874, 972, 979, 1273, 1315, 1322]) (by decide +kernel)

theorem c621310_0 : P.sumLeaves 26 636221440 393 = 243112317 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 621310) (lo := 0) (len := 393) (W := 243112317) check rows elimOK (by decide) (by decide) cover621310 (by decide)
  decide +kernel

theorem c621310_1 : P.sumLeaves 26 636221833 103 = 400806474 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 621310) (lo := 393) (len := 103) (W := 400806474) check rows elimOK (by decide) (by decide) cover621310 (by decide)
  decide +kernel

theorem c621310_2 : P.sumLeaves 26 636221936 121 = 268778831 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 621310) (lo := 496) (len := 121) (W := 268778831) check rows elimOK (by decide) (by decide) cover621310 (by decide)
  decide +kernel

theorem c621310_3 : P.sumLeaves 26 636222057 109 = 256956121 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 621310) (lo := 617) (len := 109) (W := 256956121) check rows elimOK (by decide) (by decide) cover621310 (by decide)
  decide +kernel

theorem c621310_4 : P.sumLeaves 26 636222166 118 = 414866025 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 621310) (lo := 726) (len := 118) (W := 414866025) check rows elimOK (by decide) (by decide) cover621310 (by decide)
  decide +kernel

theorem c621310_5 : P.sumLeaves 26 636222284 104 = 530006140 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 621310) (lo := 844) (len := 104) (W := 530006140) check rows elimOK (by decide) (by decide) cover621310 (by decide)
  decide +kernel

theorem c621310_6 : P.sumLeaves 26 636222388 76 = 595175972 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 621310) (lo := 948) (len := 76) (W := 595175972) check rows elimOK (by decide) (by decide) cover621310 (by decide)
  decide +kernel

theorem h621310 : P.leaf 36 621310 = 2709701880 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(393, 243112317), (103, 400806474), (121, 268778831), (109, 256956121), (118, 414866025), (104, 530006140), (76, 595175972)]) (.cons c621310_0 (.cons c621310_1 (.cons c621310_2 (.cons c621310_3 (.cons c621310_4 (.cons c621310_5 (.cons c621310_6 (.nil)))))))) (by decide) (by decide))

theorem h243567 : P.leaf 36 243567 = 2709701880 :=
  orient93 (v := 621310) (by decide) (by decide +kernel) h621310

theorem cover359293 : P.CoversSplit 26 10 359293 0xfffffffffffffffffffffffafffffffafffffffffffcfffcfafafafafa00fa00fffffffffffffffffafaaaaafafaaaaafffffffffffcfffcfafaaaaafa00aa00fffffffffffffffffffffffafffffffaffffffffcc00cc00fafafafac800c8000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [579, 923, 972, 979, 1273, 1658, 1665]) (by decide +kernel)

noncomputable def f359293 (i : ℕ) := rowWeight keep12 twice12 i * P.leaf 26 (367916032 + i)

theorem c359293_0 : rowSum f359293 0 412 = 373548166 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 359293) (keep := keep12) (twice := twice12) check rows elimOK (by decide) (by decide) cover359293 (by decide)
  decide +kernel

theorem c359293_1 : rowSum f359293 412 98 = 899512992 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 359293) (keep := keep12) (twice := twice12) check rows elimOK (by decide) (by decide) cover359293 (by decide)
  decide +kernel

theorem c359293_2 : rowSum f359293 510 464 = 727300026 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 359293) (keep := keep12) (twice := twice12) check rows elimOK (by decide) (by decide) cover359293 (by decide)
  decide +kernel

theorem c359293_3 : rowSum f359293 974 50 = 399858824 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 359293) (keep := keep12) (twice := twice12) check rows elimOK (by decide) (by decide) cover359293 (by decide)
  decide +kernel

theorem sum359293 : rowSum f359293 0 1024 = 2400220008 :=
  rowSum_append (F := f359293) (lo := 0) (n := 412) (m := 612) (A := 373548166) (B := 2026671842) c359293_0 (rowSum_append (F := f359293) (lo := 412) (n := 98) (m := 514) (A := 899512992) (B := 1127158850) c359293_1 (rowSum_append (F := f359293) (lo := 510) (n := 464) (m := 50) (A := 727300026) (B := 399858824) c359293_2 (c359293_3)))

theorem h359293 : P.leaf 36 359293 = 2400220008 :=
  leaf_weighted (k := 26) (d := 10) (H := 359293) (keep := keep12) (twice := twice12) rows (by decide) (by decide) (bal12) (invRow12 (H := 359293) (by decide) (by decide +kernel)) sum359293

theorem h243579 : P.leaf 36 243579 = 2400220008 :=
  orient4 (v := 359293) (by decide) (by decide +kernel) h359293

theorem cover630763 : P.CoversSplit 26 10 630763 0xfffffffffffffafafffffafafffffafaf0f0f0f0f0c0f0c0f0f0f0f0f0c0f0c0fffffafafffffafafffffafafffffafaf0f0f0f0f0c0f0c0f0f0f0f0f0c0f0c0fffffffffffffafafffffafafffffafaf0f0f0f0f000f000f0f0f0f0f000f000fffffafafffffafafffffafafffffafaf0f0f0f0f000f000f0f0f0f0f000f000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 922, 929, 930, 1273, 1315]) (by decide +kernel)

theorem c630763_0 : P.sumLeaves 26 645901312 184 = 171649340 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 630763) (lo := 0) (len := 184) (W := 171649340) check rows elimOK (by decide) (by decide) cover630763 (by decide)
  decide +kernel

theorem c630763_1 : P.sumLeaves 26 645901496 172 = 284995106 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 630763) (lo := 184) (len := 172) (W := 284995106) check rows elimOK (by decide) (by decide) cover630763 (by decide)
  decide +kernel

theorem c630763_2 : P.sumLeaves 26 645901668 120 = 358516633 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 630763) (lo := 356) (len := 120) (W := 358516633) check rows elimOK (by decide) (by decide) cover630763 (by decide)
  decide +kernel

theorem c630763_3 : P.sumLeaves 26 645901788 170 = 482719151 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 630763) (lo := 476) (len := 170) (W := 482719151) check rows elimOK (by decide) (by decide) cover630763 (by decide)
  decide +kernel

theorem c630763_4 : P.sumLeaves 26 645901958 110 = 405300781 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 630763) (lo := 646) (len := 110) (W := 405300781) check rows elimOK (by decide) (by decide) cover630763 (by decide)
  decide +kernel

theorem c630763_5 : P.sumLeaves 26 645902068 173 = 450136912 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 630763) (lo := 756) (len := 173) (W := 450136912) check rows elimOK (by decide) (by decide) cover630763 (by decide)
  decide +kernel

theorem c630763_6 : P.sumLeaves 26 645902241 95 = 610437412 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 630763) (lo := 929) (len := 95) (W := 610437412) check rows elimOK (by decide) (by decide) cover630763 (by decide)
  decide +kernel

theorem h630763 : P.leaf 36 630763 = 2763755335 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(184, 171649340), (172, 284995106), (120, 358516633), (170, 482719151), (110, 405300781), (173, 450136912), (95, 610437412)]) (.cons c630763_0 (.cons c630763_1 (.cons c630763_2 (.cons c630763_3 (.cons c630763_4 (.cons c630763_5 (.cons c630763_6 (.nil)))))))) (by decide) (by decide))

theorem h243582 : P.leaf 36 243582 = 2763755335 :=
  orient84 (v := 630763) (by decide) (by decide +kernel) h630763

def seg : List (ℕ × ℕ) := [(243567, 720), (243579, 360), (243582, 720)]

theorem segOK : checkSeg 20 perms 243567 243583 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 243567 243583 1800 4804968397680 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 4804968397680)
    (SegSum.cons (w := 720) h243567 (SegSum.cons (w := 360) h243579 (SegSum.cons (w := 720) h243582 (show SegSum (P.leaf 36) [] 0 from rfl)))) (by decide)

end RACert.S6N0.C0.S89
