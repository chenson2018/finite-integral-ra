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

namespace RACert.S6N0.C0.S95

open RACert RACert.Problem

theorem cover227823 : P.CoversSplit 26 10 227823 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000400000000000000000000000000000000000000000100000000000000000000000000000000000000000020000000000000000000010000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f227823 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 26 (233290752 + i)

theorem c227823_0 : rowSum f227823 0 1024 = 19872568 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 227823) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover227823 (by decide)
  decide +kernel

theorem sum227823 : rowSum f227823 0 1024 = 19872568 :=
  c227823_0

theorem h227823 : P.leaf 36 227823 = 19872568 :=
  leaf_weighted (k := 26) (d := 10) (H := 227823) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 227823) (by decide) (by decide +kernel)) sum227823

theorem cover227839 : P.CoversSplit 26 10 227839 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000400000000000000000000000000000000000000000100000000000000000000000000000000000000000020000000000000000000010000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f227839 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 26 (233307136 + i)

theorem c227839_0 : rowSum f227839 0 1024 = 25393548 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 227839) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover227839 (by decide)
  decide +kernel

theorem sum227839 : rowSum f227839 0 1024 = 25393548 :=
  c227839_0

theorem h227839 : P.leaf 36 227839 = 25393548 :=
  leaf_weighted (k := 26) (d := 10) (H := 227839) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 227839) (by decide) (by decide +kernel)) sum227839

theorem cover228023 : P.CoversSplit 26 10 228023 0xcc00cc0000000000cc00cc000000000000000000000000000000000000000000cc00cc0000000000cc00c000000000000000000000000000000000000000000000000000000000000000000000000000000000000033003300000000003300300000000000000000000000000000000000000000003300330000000000330030 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 538, 587, 972, 979]) (by decide +kernel)

noncomputable def f228023 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 26 (233495552 + i)

theorem c228023_0 : rowSum f228023 0 1024 = 180460821 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 228023) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover228023 (by decide)
  decide +kernel

theorem sum228023 : rowSum f228023 0 1024 = 180460821 :=
  c228023_0

theorem h228023 : P.leaf 36 228023 = 180460821 :=
  leaf_weighted (k := 26) (d := 10) (H := 228023) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 228023) (by decide) (by decide +kernel)) sum228023

theorem cover228025 : P.CoversSplit 26 10 228025 0xf0f0f0f000000000f0f0f0f50000000000000000000000000000000000000030000000000000000000005050000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 587, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c228025_0 : P.sumLeaves 26 233497600 1024 = 143256860 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 228025) (lo := 0) (len := 1024) (W := 143256860) check rows elimOK (by decide) (by decide) cover228025 (by decide)
  decide +kernel

theorem h228025 : P.leaf 36 228025 = 143256860 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 143256860)]) (.cons c228025_0 (.nil)) (by decide) (by decide))

theorem cover228027 : P.CoversSplit 26 10 228027 0xf0f0f0f000000000f0f0f0f50000000000000000000000000000000000000030000000000000000000005050000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f228027 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 26 (233499648 + i)

theorem c228027_0 : rowSum f228027 0 1024 = 329127888 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 228027) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover228027 (by decide)
  decide +kernel

theorem sum228027 : rowSum f228027 0 1024 = 329127888 :=
  c228027_0

theorem h228027 : P.leaf 36 228027 = 329127888 :=
  leaf_weighted (k := 26) (d := 10) (H := 228027) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 228027) (by decide) (by decide +kernel)) sum228027

theorem cover228029 : P.CoversSplit 26 10 228029 0xffffffff00000000fffffffa0000000000000000000000000000000000000030ffffffff00000000fffff0f0000000000000000000000000000000000000003000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [538, 587, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c228029_0 : P.sumLeaves 26 233501696 998 = 224947572 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 228029) (lo := 0) (len := 998) (W := 224947572) check rows elimOK (by decide) (by decide) cover228029 (by decide)
  decide +kernel

theorem c228029_1 : P.sumLeaves 26 233502694 26 = 197077268 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 228029) (lo := 998) (len := 26) (W := 197077268) check rows elimOK (by decide) (by decide) cover228029 (by decide)
  decide +kernel

theorem h228029 : P.leaf 36 228029 = 422024840 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(998, 224947572), (26, 197077268)]) (.cons c228029_0 (.cons c228029_1 (.nil))) (by decide) (by decide))

theorem cover228031 : P.CoversSplit 26 10 228031 0xffffffff00000000fffffffa0000000000000000000000000000000000000030ffffffff00000000fffff0f0000000000000000000000000000000000000003000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [538, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f228031 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 26 (233503744 + i)

theorem c228031_0 : rowSum f228031 0 1024 = 857253246 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 228031) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover228031 (by decide)
  decide +kernel

theorem sum228031 : rowSum f228031 0 1024 = 857253246 :=
  c228031_0

theorem h228031 : P.leaf 36 228031 = 857253246 :=
  leaf_weighted (k := 26) (d := 10) (H := 228031) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 228031) (by decide) (by decide +kernel)) sum228031

theorem cover228047 : P.CoversSplit 26 10 228047 0xffff0000ffff0000ffff0000ffff050000000000000000000000000000300000000000000000000005050000050500000000000000000000000000000000000000000000003300000000000000330000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 587, 972, 979, 1266, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f228047 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 26 (233520128 + i)

theorem c228047_0 : rowSum f228047 0 1024 = 440773668 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 228047) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover228047 (by decide)
  decide +kernel

theorem sum228047 : rowSum f228047 0 1024 = 440773668 :=
  c228047_0

theorem h228047 : P.leaf 36 228047 = 440773668 :=
  leaf_weighted (k := 26) (d := 10) (H := 228047) (keep := keep2) (twice := twice2) rows (by decide) (by decide) bal2 (invRow2 (H := 228047) (by decide) (by decide +kernel)) sum228047

theorem cover228061 : P.CoversSplit 26 10 228061 0xffff0000ffff0000ffff0000ffff050000000000000000000000000000300000000000000000000005050000050500000000000000000000000000000000000000000000003300000000000000330000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 587, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c228061_0 : P.sumLeaves 26 233534464 1024 = 482145284 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 228061) (lo := 0) (len := 1024) (W := 482145284) check rows elimOK (by decide) (by decide) cover228061 (by decide)
  decide +kernel

theorem h228061 : P.leaf 36 228061 = 482145284 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 482145284)]) (.cons c228061_0 (.nil)) (by decide) (by decide))

theorem cover228063 : P.CoversSplit 26 10 228063 0xffff0000ffff0000ffff0000ffff050000000000000000000000000000300000000000000000000005050000050500000000000000000000000000000000000000000000003300000000000000330000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 587, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f228063 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 26 (233536512 + i)

theorem c228063_0 : rowSum f228063 0 1024 = 1013094401 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 228063) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover228063 (by decide)
  decide +kernel

theorem sum228063 : rowSum f228063 0 1024 = 1013094401 :=
  c228063_0

theorem h228063 : P.leaf 36 228063 = 1013094401 :=
  leaf_weighted (k := 26) (d := 10) (H := 228063) (keep := keep2) (twice := twice2) rows (by decide) (by decide) bal2 (invRow2 (H := 228063) (by decide) (by decide +kernel)) sum228063

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

noncomputable def f228094 (i : ℕ) := rowWeight keep3 twice3 i * P.leaf 26 (233568256 + i)

theorem c228094_0 : rowSum f228094 0 917 = 412170230 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 228094) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover228094 (by decide)
  decide +kernel

theorem c228094_1 : rowSum f228094 917 107 = 1034354884 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 228094) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover228094 (by decide)
  decide +kernel

theorem sum228094 : rowSum f228094 0 1024 = 1446525114 :=
  rowSum_append (F := f228094) (lo := 0) (n := 917) (m := 107) (A := 412170230) (B := 1034354884) c228094_0 (c228094_1)

theorem h228094 : P.leaf 36 228094 = 1446525114 :=
  leaf_weighted (k := 26) (d := 10) (H := 228094) (keep := keep3) (twice := twice3) rows (by decide) (by decide) bal3 (invRow3 (H := 228094) (by decide) (by decide +kernel)) sum228094

theorem cover228095 : P.CoversSplit 26 10 228095 0xfffffffffffffffffffffffafffffafa00000000000000000000000000300000fffffffffffffffffffff0f0fffff0f00000000000000000000000000030000000000000003300330000000000330032000000000000000000000000000000000000000000330033000000000033003000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [587, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f228095 (i : ℕ) := rowWeight keep3 twice3 i * P.leaf 26 (233569280 + i)

theorem c228095_0 : rowSum f228095 0 901 = 504375495 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 228095) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover228095 (by decide)
  decide +kernel

theorem c228095_1 : rowSum f228095 901 123 = 2028700540 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 228095) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover228095 (by decide)
  decide +kernel

theorem sum228095 : rowSum f228095 0 1024 = 2533076035 :=
  rowSum_append (F := f228095) (lo := 0) (n := 901) (m := 123) (A := 504375495) (B := 2028700540) c228095_0 (c228095_1)

theorem h228095 : P.leaf 36 228095 = 2533076035 :=
  leaf_weighted (k := 26) (d := 10) (H := 228095) (keep := keep3) (twice := twice3) rows (by decide) (by decide) bal3 (invRow3 (H := 228095) (by decide) (by decide +kernel)) sum228095

theorem cover228335 : P.CoversSplit 26 10 228335 0xfffffffffffffffffffffffafffffafafffffffffffcffccfffffafaffccfac8fffffffffffffffffffffafafffffafafffffffffffcffccfffffafaffccfac8fffffffffffffffffffffffafffffafaffffffffffccffccfffffafaffccfac80000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [972, 979, 1266, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f228335 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 26 (233815040 + i)

theorem c228335_0 : rowSum f228335 0 375 = 532196264 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 228335) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover228335 (by decide)
  decide +kernel

theorem c228335_1 : rowSum f228335 375 102 = 801782360 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 228335) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover228335 (by decide)
  decide +kernel

theorem c228335_2 : rowSum f228335 477 394 = 1424621556 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 228335) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover228335 (by decide)
  decide +kernel

theorem c228335_3 : rowSum f228335 871 153 = 1447392880 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 228335) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover228335 (by decide)
  decide +kernel

theorem sum228335 : rowSum f228335 0 1024 = 4205993060 :=
  rowSum_append (F := f228335) (lo := 0) (n := 375) (m := 649) (A := 532196264) (B := 3673796796) c228335_0 (rowSum_append (F := f228335) (lo := 375) (n := 102) (m := 547) (A := 801782360) (B := 2872014436) c228335_1 (rowSum_append (F := f228335) (lo := 477) (n := 394) (m := 153) (A := 1424621556) (B := 1447392880) c228335_2 (c228335_3)))

theorem h228335 : P.leaf 36 228335 = 4205993060 :=
  leaf_weighted (k := 26) (d := 10) (H := 228335) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 228335) (by decide) (by decide +kernel)) sum228335

def seg : List (ℕ × ℕ) := [(227823, 90), (227839, 60), (228023, 60), (228025, 720), (228027, 360), (228029, 720), (228031, 360), (228047, 360), (228061, 720), (228063, 360), (228079, 720), (228094, 360), (228095, 360), (228335, 180)]

theorem segOK : checkSeg 20 perms 227823 228351 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 227823 228351 5430 4833206999100 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 4833206999100)
    (SegSum.cons (w := 90) h227823 (SegSum.cons (w := 60) h227839 (SegSum.cons (w := 60) h228023 (SegSum.cons (w := 720) h228025 (SegSum.cons (w := 360) h228027 (SegSum.cons (w := 720) h228029 (SegSum.cons (w := 360) h228031 (SegSum.cons (w := 360) h228047 (SegSum.cons (w := 720) h228061 (SegSum.cons (w := 360) h228063 (SegSum.cons (w := 720) h228079 (SegSum.cons (w := 360) h228094 (SegSum.cons (w := 360) h228095 (SegSum.cons (w := 180) h228335 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))) (by decide)

end RACert.S6N0.C0.S95
