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

namespace RACert.S6N0.C0.S81

open RACert RACert.Problem

theorem cover228031 : P.CoversSplit 26 10 228031 0xffffffff00000000fffffffa0000000000000000000000000000000000000030ffffffff00000000fffff0f0000000000000000000000000000000000000003000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [538, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f228031 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 26 (233503744 + i)

theorem c228031_0 : rowSum f228031 0 1024 = 857253246 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 228031) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover228031 (by decide)
  decide +kernel

theorem sum228031 : rowSum f228031 0 1024 = 857253246 :=
  c228031_0

theorem h228031 : P.leaf 36 228031 = 857253246 :=
  leaf_weighted (k := 26) (d := 10) (H := 228031) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 228031) (by decide) (by decide +kernel)) sum228031

theorem cover228047 : P.CoversSplit 26 10 228047 0xffff0000ffff0000ffff0000ffff050000000000000000000000000000300000000000000000000005050000050500000000000000000000000000000000000000000000003300000000000000330000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 587, 972, 979, 1266, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f228047 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 26 (233520128 + i)

theorem c228047_0 : rowSum f228047 0 1024 = 440773668 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 228047) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover228047 (by decide)
  decide +kernel

theorem sum228047 : rowSum f228047 0 1024 = 440773668 :=
  c228047_0

theorem h228047 : P.leaf 36 228047 = 440773668 :=
  leaf_weighted (k := 26) (d := 10) (H := 228047) (keep := keep2) (twice := twice2) rows (by decide) (by decide) (bal2) (invRow2 (H := 228047) (by decide) (by decide +kernel)) sum228047

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
  leaf_weighted (k := 26) (d := 10) (H := 228063) (keep := keep2) (twice := twice2) rows (by decide) (by decide) (bal2) (invRow2 (H := 228063) (by decide) (by decide +kernel)) sum228063

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

theorem cover374270 : P.CoversSplit 26 10 374270 0xfffffffffffffffffffffefefffffefe00000000000000000000000000220022ffffffffffffffffaaaaa0a0aaaaa0a00000000000000000000000000022002000000000003300330000000000330032000000000000000000000000000000000000000000330033000000000022002000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [629, 636, 873, 1658, 1665]) (by decide +kernel)

noncomputable def f374270 (i : ℕ) := rowWeight keep3 twice3 i * P.leaf 26 (383252480 + i)

theorem c374270_0 : rowSum f374270 0 920 = 688350946 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 374270) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover374270 (by decide)
  decide +kernel

theorem c374270_1 : rowSum f374270 920 104 = 758174168 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 374270) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover374270 (by decide)
  decide +kernel

theorem sum374270 : rowSum f374270 0 1024 = 1446525114 :=
  rowSum_append (F := f374270) (lo := 0) (n := 920) (m := 104) (A := 688350946) (B := 758174168) c374270_0 (c374270_1)

theorem h374270 : P.leaf 36 374270 = 1446525114 :=
  leaf_weighted (k := 26) (d := 10) (H := 374270) (keep := keep3) (twice := twice3) rows (by decide) (by decide) (bal3) (invRow3 (H := 374270) (by decide) (by decide +kernel)) sum374270

theorem h228094 : P.leaf 36 228094 = 1446525114 :=
  orient4 (v := 374270) (by decide) (by decide +kernel) h374270

theorem cover374271 : P.CoversSplit 26 10 374271 0xfffffffffffffffffffffefefffffefe00000000000000000000000000220022ffffffffffffffffaaaaaaaaaaaaaaaa0000000000000000000000000022002200000000003300330000000000330032000000000000000000000000000000000000000000330033000000000022002200000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [629, 636, 1658, 1665]) (by decide +kernel)

noncomputable def f374271 (i : ℕ) := rowWeight keep3 twice3 i * P.leaf 26 (383253504 + i)

theorem c374271_0 : rowSum f374271 0 908 = 1119840219 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 374271) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover374271 (by decide)
  decide +kernel

theorem c374271_1 : rowSum f374271 908 116 = 1413235816 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 374271) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover374271 (by decide)
  decide +kernel

theorem sum374271 : rowSum f374271 0 1024 = 2533076035 :=
  rowSum_append (F := f374271) (lo := 0) (n := 908) (m := 116) (A := 1119840219) (B := 1413235816) c374271_0 (c374271_1)

theorem h374271 : P.leaf 36 374271 = 2533076035 :=
  leaf_weighted (k := 26) (d := 10) (H := 374271) (keep := keep3) (twice := twice3) rows (by decide) (by decide) (bal3) (invRow3 (H := 374271) (by decide) (by decide +kernel)) sum374271

theorem h228095 : P.leaf 36 228095 = 2533076035 :=
  orient4 (v := 374271) (by decide) (by decide +kernel) h374271

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
  leaf_weighted (k := 26) (d := 10) (H := 228335) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 228335) (by decide) (by decide +kernel)) sum228335

theorem cover818175 : P.CoversSplit 26 10 818175 0xffffffffffffffffffffaaaaffffaaaaffffffffccccccccffffaaaacccc8888ffffffffffffffffffffaaaaffffaaaaffffffffccccccccffffaaaacccc8888ffffffffffffffffffffaaaaffffaaaaffffffffccccccccffffaaaacccc8888ffffffffffffffffffffaaaaffffaaaaffffffffccccccccffffaaaacccc8888 :=
  coversSplit check rows (by decide) (by decide) (xs := [972, 979, 1265, 1273]) (by decide +kernel)

noncomputable def f818175 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 26 (837811200 + i)

theorem c818175_0 : rowSum f818175 0 241 = 1550142709 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 818175) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover818175 (by decide)
  decide +kernel

theorem c818175_1 : rowSum f818175 241 150 = 1852779858 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 818175) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover818175 (by decide)
  decide +kernel

theorem c818175_2 : rowSum f818175 391 108 = 2112416570 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 818175) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover818175 (by decide)
  decide +kernel

theorem c818175_3 : rowSum f818175 499 481 = 2241662812 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 818175) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover818175 (by decide)
  decide +kernel

theorem c818175_4 : rowSum f818175 980 44 = 636336336 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 818175) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover818175 (by decide)
  decide +kernel

theorem sum818175 : rowSum f818175 0 1024 = 8393338285 :=
  rowSum_append (F := f818175) (lo := 0) (n := 241) (m := 783) (A := 1550142709) (B := 6843195576) c818175_0 (rowSum_append (F := f818175) (lo := 241) (n := 150) (m := 633) (A := 1852779858) (B := 4990415718) c818175_1 (rowSum_append (F := f818175) (lo := 391) (n := 108) (m := 525) (A := 2112416570) (B := 2877999148) c818175_2 (rowSum_append (F := f818175) (lo := 499) (n := 481) (m := 44) (A := 2241662812) (B := 636336336) c818175_3 (c818175_4))))

theorem h818175 : P.leaf 36 818175 = 8393338285 :=
  leaf_weighted (k := 26) (d := 10) (H := 818175) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 818175) (by decide) (by decide +kernel)) sum818175

theorem h228351 : P.leaf 36 228351 = 8393338285 :=
  orient80 (v := 818175) (by decide) (by decide +kernel) h818175

def seg : List (ℕ × ℕ) := [(228031, 360), (228047, 360), (228061, 720), (228063, 360), (228079, 720), (228094, 360), (228095, 360), (228335, 180), (228351, 60)]

theorem segOK : checkSeg 20 perms 228031 228863 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 228031 228863 3480 4797178639260 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 4797178639260)
    (SegSum.cons (w := 360) h228031 (SegSum.cons (w := 360) h228047 (SegSum.cons (w := 720) h228061 (SegSum.cons (w := 360) h228063 (SegSum.cons (w := 720) h228079 (SegSum.cons (w := 360) h228094 (SegSum.cons (w := 360) h228095 (SegSum.cons (w := 180) h228335 (SegSum.cons (w := 60) h228351 (show SegSum (P.leaf 36) [] 0 from rfl)))))))))) (by decide)

end RACert.S6N0.C0.S81
