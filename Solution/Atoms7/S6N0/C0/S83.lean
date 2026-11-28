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

namespace RACert.S6N0.C0.S83

open RACert RACert.Problem

theorem cover376319 : P.CoversSplit 26 10 376319 0xfffffffffffffffffffffefefffffefe00000000000000000000000000220022ffffffffffffffffaaaaaaaaaaaaaaaa0000000000000000000000000022002200000000003300330000000000330032000000000000000000000000000000000000000000330033000000000022002200000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [629, 636, 1658, 1665]) (by decide +kernel)

noncomputable def f376319 (i : ℕ) := rowWeight keep3 twice3 i * P.leaf 26 (385350656 + i)

theorem c376319_0 : rowSum f376319 0 908 = 1160348285 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 376319) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover376319 (by decide)
  decide +kernel

theorem c376319_1 : rowSum f376319 908 116 = 1445555178 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 376319) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover376319 (by decide)
  decide +kernel

theorem sum376319 : rowSum f376319 0 1024 = 2605903463 :=
  rowSum_append (F := f376319) (lo := 0) (n := 908) (m := 116) (A := 1160348285) (B := 1445555178) c376319_0 (c376319_1)

theorem h376319 : P.leaf 36 376319 = 2605903463 :=
  leaf_weighted (k := 26) (d := 10) (H := 376319) (keep := keep3) (twice := twice3) rows (by decide) (by decide) (bal3) (invRow3 (H := 376319) (by decide) (by decide +kernel)) sum376319

theorem h229119 : P.leaf 36 229119 = 2605903463 :=
  orient4 (v := 376319) (by decide) (by decide +kernel) h376319

theorem cover229357 : P.CoversSplit 26 10 229357 0xfffffffffffffffffffffffafffffafafffffffffffcffccfffffafaffccfac8fffffffffffffffffffffafafffffafafffffffffffcffccfffffafaffccfac8fffffffffffffffffffffffafffffafaffffffffffccffccfffffafaffccfac80000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f229357 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 26 (234861568 + i)

theorem c229357_0 : rowSum f229357 0 375 = 568448920 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 229357) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover229357 (by decide)
  decide +kernel

theorem c229357_1 : rowSum f229357 375 102 = 820518114 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 229357) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover229357 (by decide)
  decide +kernel

theorem c229357_2 : rowSum f229357 477 394 = 1506346456 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 229357) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover229357 (by decide)
  decide +kernel

theorem c229357_3 : rowSum f229357 871 153 = 1460878800 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 229357) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover229357 (by decide)
  decide +kernel

theorem sum229357 : rowSum f229357 0 1024 = 4356192290 :=
  rowSum_append (F := f229357) (lo := 0) (n := 375) (m := 649) (A := 568448920) (B := 3787743370) c229357_0 (rowSum_append (F := f229357) (lo := 375) (n := 102) (m := 547) (A := 820518114) (B := 2967225256) c229357_1 (rowSum_append (F := f229357) (lo := 477) (n := 394) (m := 153) (A := 1506346456) (B := 1460878800) c229357_2 (c229357_3)))

theorem h229357 : P.leaf 36 229357 = 4356192290 :=
  leaf_weighted (k := 26) (d := 10) (H := 229357) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 229357) (by decide) (by decide +kernel)) sum229357

theorem cover229359 : P.CoversSplit 26 10 229359 0xfffffffffffffffffffffffafffffafafffffffffffcffccfffffafaffccfac8fffffffffffffffffffffafafffffafafffffffffffcffccfffffafaffccfac8fffffffffffffffffffffffafffffafaffffffffffccffccfffffafaffccfac80000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [972, 979, 1266, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f229359 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 26 (234863616 + i)

theorem c229359_0 : rowSum f229359 0 375 = 1104656816 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 229359) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover229359 (by decide)
  decide +kernel

theorem c229359_1 : rowSum f229359 375 102 = 1377121678 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 229359) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover229359 (by decide)
  decide +kernel

theorem c229359_2 : rowSum f229359 477 394 = 2362320240 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 229359) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover229359 (by decide)
  decide +kernel

theorem c229359_3 : rowSum f229359 871 153 = 2066805856 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 229359) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover229359 (by decide)
  decide +kernel

theorem sum229359 : rowSum f229359 0 1024 = 6910904590 :=
  rowSum_append (F := f229359) (lo := 0) (n := 375) (m := 649) (A := 1104656816) (B := 5806247774) c229359_0 (rowSum_append (F := f229359) (lo := 375) (n := 102) (m := 547) (A := 1377121678) (B := 4429126096) c229359_1 (rowSum_append (F := f229359) (lo := 477) (n := 394) (m := 153) (A := 2362320240) (B := 2066805856) c229359_2 (c229359_3)))

theorem h229359 : P.leaf 36 229359 = 6910904590 :=
  leaf_weighted (k := 26) (d := 10) (H := 229359) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 229359) (by decide) (by decide +kernel)) sum229359

theorem cover850943 : P.CoversSplit 26 10 850943 0xffffffffffffffffffffaaaaffffaaaaffffffffccccccccffffaaaacccc8888ffffffffffffffffffffaaaaffffaaaaffffffffccccccccffffaaaacccc8888ffffffffffffffffffffaaaaffffaaaaffffffffccccccccffffaaaacccc8888ffffffffffffffffffffaaaaffffaaaaffffffffccccccccffffaaaacccc8888 :=
  coversSplit check rows (by decide) (by decide) (xs := [1265, 1273]) (by decide +kernel)

noncomputable def f850943 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 26 (871365632 + i)

theorem c850943_0 : rowSum f850943 0 241 = 1636713215 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 850943) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover850943 (by decide)
  decide +kernel

theorem c850943_1 : rowSum f850943 241 150 = 1948875320 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 850943) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover850943 (by decide)
  decide +kernel

theorem c850943_2 : rowSum f850943 391 108 = 2215175676 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 850943) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover850943 (by decide)
  decide +kernel

theorem c850943_3 : rowSum f850943 499 481 = 2345691230 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 850943) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover850943 (by decide)
  decide +kernel

theorem c850943_4 : rowSum f850943 980 44 = 667579956 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 850943) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover850943 (by decide)
  decide +kernel

theorem sum850943 : rowSum f850943 0 1024 = 8814035397 :=
  rowSum_append (F := f850943) (lo := 0) (n := 241) (m := 783) (A := 1636713215) (B := 7177322182) c850943_0 (rowSum_append (F := f850943) (lo := 241) (n := 150) (m := 633) (A := 1948875320) (B := 5228446862) c850943_1 (rowSum_append (F := f850943) (lo := 391) (n := 108) (m := 525) (A := 2215175676) (B := 3013271186) c850943_2 (rowSum_append (F := f850943) (lo := 499) (n := 481) (m := 44) (A := 2345691230) (B := 667579956) c850943_3 (c850943_4))))

theorem h850943 : P.leaf 36 850943 = 8814035397 :=
  leaf_weighted (k := 26) (d := 10) (H := 850943) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 850943) (by decide) (by decide +kernel)) sum850943

theorem h229375 : P.leaf 36 229375 = 8814035397 :=
  orient80 (v := 850943) (by decide) (by decide +kernel) h850943

theorem cover827283 : P.CoversSplit 26 10 827283 0xfca8cc88a8a88888fc00c80000000000f0a00000a0800000f000000000000000fca8cc88a8a88888fc00c80000000000f0a00000a0800000f000000000000000fca8cc88a8a88888fc00c80000000000f0a00000a0800000f000000000000000fca8cc88a8a88888fc00c80000000000f0a00000a0800000f000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 482, 488, 489, 531, 537, 923, 929, 1266, 1272]) (by decide +kernel)

noncomputable def f827283 (i : ℕ) := rowWeight keep10 twice10 i * P.leaf 26 (847137792 + i)

theorem c827283_0 : rowSum f827283 0 1024 = 142059008 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 827283) (keep := keep10) (twice := twice10) check rows elimOK (by decide) (by decide) cover827283 (by decide)
  decide +kernel

theorem sum827283 : rowSum f827283 0 1024 = 142059008 :=
  c827283_0

theorem h827283 : P.leaf 36 827283 = 142059008 :=
  leaf_weighted (k := 26) (d := 10) (H := 827283) (keep := keep10) (twice := twice10) rows (by decide) (by decide) (bal10) (invRow10 (H := 827283) (by decide) (by decide +kernel)) sum827283

theorem h241500 : P.leaf 36 241500 = 142059008 :=
  orient80 (v := 827283) (by decide) (by decide +kernel) h827283

theorem cover827287 : P.CoversSplit 26 10 827287 0xffffccccffffccccff00c80000000000ffff0000ffcc0000ff00000000000000ffffccccffffccccff00c80000000000ffff0000ffcc0000ff00000000000000ffffccccffffccccff00c80000000000ffff0000ffcc0000ff00000000000000ffffccccffffccccff00c80000000000ffff0000ffcc0000ff00000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 531, 538, 923, 1266, 1272]) (by decide +kernel)

noncomputable def f827287 (i : ℕ) := rowWeight keep9 twice9 i * P.leaf 26 (847141888 + i)

theorem c827287_0 : rowSum f827287 0 501 = 284867248 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 827287) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover827287 (by decide)
  decide +kernel

theorem c827287_1 : rowSum f827287 501 457 = 341096906 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 827287) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover827287 (by decide)
  decide +kernel

theorem c827287_2 : rowSum f827287 958 66 = 65902336 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 827287) (keep := keep9) (twice := twice9) check rows elimOK (by decide) (by decide) cover827287 (by decide)
  decide +kernel

theorem sum827287 : rowSum f827287 0 1024 = 691866490 :=
  rowSum_append (F := f827287) (lo := 0) (n := 501) (m := 523) (A := 284867248) (B := 406999242) c827287_0 (rowSum_append (F := f827287) (lo := 501) (n := 457) (m := 66) (A := 341096906) (B := 65902336) c827287_1 (c827287_2))

theorem h827287 : P.leaf 36 827287 = 691866490 :=
  leaf_weighted (k := 26) (d := 10) (H := 827287) (keep := keep9) (twice := twice9) rows (by decide) (by decide) (bal9) (invRow9 (H := 827287) (by decide) (by decide +kernel)) sum827287

theorem h241501 : P.leaf 36 241501 = 691866490 :=
  orient80 (v := 827287) (by decide) (by decide +kernel) h827287

def seg : List (ℕ × ℕ) := [(229119, 360), (229357, 180), (229359, 180), (229375, 60), (241500, 15), (241501, 120)]

theorem segOK : checkSeg 20 perms 229119 241503 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 229119 241503 915 3580199672820 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 3580199672820)
    (SegSum.cons (w := 360) h229119 (SegSum.cons (w := 180) h229357 (SegSum.cons (w := 180) h229359 (SegSum.cons (w := 60) h229375 (SegSum.cons (w := 15) h241500 (SegSum.cons (w := 120) h241501 (show SegSum (P.leaf 36) [] 0 from rfl))))))) (by decide)

end RACert.S6N0.C0.S83
