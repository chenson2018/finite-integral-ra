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

namespace RACert.S4N1.C0.S34

open RACert RACert.Problem

theorem cover44387 : P.CoversSplit 24 10 44387 0xfffffffffafa0000ffff0000fafa0000ffff00000000fafaffff0000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00c80000000000000000000000cc0000000000c80000330000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [466, 515, 522, 572, 858, 865, 915, 1202, 1209, 1258, 1601]) (ps := [(19, [529], [1209])]) (by decide +kernel)

def k44387 : ℕ := 0x8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cefffffffffffffffff8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef
def t44387 : ℕ := 0x8ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce000000000000000008ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce

noncomputable def f44387 (i : ℕ) := rowWeight k44387 t44387 i * P.leaf 24 (45452288 + i)

theorem c44387_0 : rowSum f44387 0 320 = 0 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 44387) (keep := k44387) (twice := t44387) check rows elimOK (by decide) (by decide) cover44387 (by decide)
  decide +kernel

theorem contract44387_1 : P.leaf 30 710197 = 0 := by
  exact leaf_contract_zero (ss := [(19, 1, 529), (27, 1, 572), (29, 1, 915), (20, 1, 1266), (21, 0, 1272), (8, 0, 1658), (5, 1, 474), (4, 1, 425), (6, 1, 482), (14, 1, 482), (30, 1, 523)]) (q := 586) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c44387_1 : rowSum f44387 320 64 = 0 :=
  (rowSum_unit_block (P := P) (keep := k44387) (twice := t44387) (by decide +kernel)).trans ((leaf_eq_inner (k := 24) (d := 6) (H := 710197) rows (by decide) (by decide)).symm.trans contract44387_1)

theorem c44387_2 : rowSum f44387 384 640 = 8963653 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 44387) (keep := k44387) (twice := t44387) check rows elimOK (by decide) (by decide) cover44387 (by decide)
  decide +kernel

theorem sum44387 : rowSum f44387 0 1024 = 8963653 :=
  rowSum_append (F := f44387) (lo := 0) (n := 320) (m := 704) (A := 0) (B := 8963653) c44387_0 (rowSum_append (F := f44387) (lo := 320) (n := 64) (m := 640) (A := 0) (B := 8963653) c44387_1 (c44387_2))

theorem h44387 : P.leaf 34 44387 = 8963653 :=
  leaf_weighted (k := 24) (d := 10) (H := 44387) (keep := k44387) (twice := t44387) rows (by decide) (by decide) (balancedRows_of_check (by decide +kernel)) (invRow2 (H := 44387) (by decide) (by decide +kernel)) sum44387

theorem h6136 : P.leaf 34 6136 = 8963653 :=
  orient32 (v := 44387) (by decide) (by decide +kernel) h44387

theorem cover19407 : P.CoversSplit 24 10 19407 0xffffffff00000000ffffffff00000000a0a0000000000000a0a0000000000000cccccccc00000000000000000000000080800000000000000000000000000000ffffffff000000000000000000000000a0a005050000000000000000000000000000000000000000ffccaa880000000000000000000000008080040000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [515, 516, 522, 859, 879, 915, 1210, 1259, 1601]) (ps := [(8, [1609], [516]), (14, [1609], [859, 1266]), (17, [528, 565], [1259]), (18, [1210], [1264])]) (by decide +kernel)

theorem c19407_0 : P.sumLeaves 24 19872768 320 = 665690 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 19407) (lo := 0) (len := 320) (W := 665690) check rows elimOK (by decide) (by decide) cover19407 (by decide)
  decide +kernel

theorem contract19407_1 : P.leaf 30 310517 = 0 := by
  exact leaf_contract_zero (ss := [(17, 3, 536), (3, 1, 418), (31, 1, 879), (14, 0, 1266), (8, 0, 880), (5, 1, 433), (20, 1, 531), (21, 0, 537), (9, 1, 678), (12, 1, 825)]) (q := 923) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c19407_1 : P.sumLeaves 24 19873088 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 310517) rows (by decide) (by decide)).symm.trans contract19407_1

theorem c19407_2 : P.sumLeaves 24 19873152 614 = 13378219 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 19407) (lo := 384) (len := 614) (W := 13378219) check rows elimOK (by decide) (by decide) cover19407 (by decide)
  decide +kernel

theorem c19407_3 : P.sumLeaves 24 19873766 26 = 10568568 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 19407) (lo := 998) (len := 26) (W := 10568568) check rows elimOK (by decide) (by decide) cover19407 (by decide)
  decide +kernel

theorem h19407 : P.leaf 34 19407 = 24612477 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(320, 665690), (64, 0), (614, 13378219), (26, 10568568)]) (.cons c19407_0 (.cons c19407_1 (.cons c19407_2 (.cons c19407_3 (.nil))))) (by decide) (by decide))

theorem h6137 : P.leaf 34 6137 = 24612477 :=
  orient4 (v := 19407) (by decide) (by decide +kernel) h19407

theorem cover44915 : P.CoversSplit 24 10 44915 0xfffffffffafa0000fffffffffafa0000fffffffffafa0000fffffffffafa00000000000000000000000000000000000000000000000000000000000000000000cc00cc00c80000000000000000000000cc00cc008000000000330033002000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [474, 572, 915, 1202, 1209, 1258]) (ps := [(8, [1217], [572, 1272]), (14, [1217], [915, 1272])]) (by decide +kernel)

def k44915 : ℕ := 0x8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cefffffffffffffffffffffffffffffffff8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef8cef
def t44915 : ℕ := 0x8ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce0000000000000000000000000000000008ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce08ce

noncomputable def f44915 (i : ℕ) := rowWeight k44915 t44915 i * P.leaf 24 (45992960 + i)

theorem c44915_0 : rowSum f44915 0 256 = 0 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 44915) (keep := k44915) (twice := t44915) check rows elimOK (by decide) (by decide) cover44915 (by decide)
  decide +kernel

theorem contract44915_1 : P.leaf 30 718644 = 0 := by
  exact leaf_contract_zero (ss := [(16, 0, 1258), (27, 0, 1258), (7, 0, 572), (8, 0, 572), (6, 1, 482), (14, 1, 482), (19, 1, 578)]) (q := 586) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c44915_1 : rowSum f44915 256 64 = 0 :=
  (rowSum_unit_block (P := P) (keep := k44915) (twice := t44915) (by decide +kernel)).trans ((leaf_eq_inner (k := 24) (d := 6) (H := 718644) rows (by decide) (by decide)).symm.trans contract44915_1)

theorem contract44915_2 : P.leaf 30 718645 = 0 := by
  exact leaf_contract_zero (ss := [(27, 1, 572), (29, 1, 915), (8, 0, 1272), (6, 1, 482), (14, 1, 482)]) (q := 586) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c44915_2 : rowSum f44915 320 64 = 0 :=
  (rowSum_unit_block (P := P) (keep := k44915) (twice := t44915) (by decide +kernel)).trans ((leaf_eq_inner (k := 24) (d := 6) (H := 718645) rows (by decide) (by decide)).symm.trans contract44915_2)

theorem c44915_3 : rowSum f44915 384 608 = 39681172 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 44915) (keep := k44915) (twice := t44915) check rows elimOK (by decide) (by decide) cover44915 (by decide)
  decide +kernel

theorem c44915_4 : rowSum f44915 992 32 = 23268216 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 44915) (keep := k44915) (twice := t44915) check rows elimOK (by decide) (by decide) cover44915 (by decide)
  decide +kernel

theorem sum44915 : rowSum f44915 0 1024 = 62949388 :=
  rowSum_append (F := f44915) (lo := 0) (n := 256) (m := 768) (A := 0) (B := 62949388) c44915_0 (rowSum_append (F := f44915) (lo := 256) (n := 64) (m := 704) (A := 0) (B := 62949388) c44915_1 (rowSum_append (F := f44915) (lo := 320) (n := 64) (m := 640) (A := 0) (B := 62949388) c44915_2 (rowSum_append (F := f44915) (lo := 384) (n := 608) (m := 32) (A := 39681172) (B := 23268216) c44915_3 (c44915_4))))

theorem h44915 : P.leaf 34 44915 = 62949388 :=
  leaf_weighted (k := 24) (d := 10) (H := 44915) (keep := k44915) (twice := t44915) rows (by decide) (by decide) (balancedRows_of_check (by decide +kernel)) (invRow2 (H := 44915) (by decide) (by decide +kernel)) sum44915

theorem h6139 : P.leaf 34 6139 = 62949388 :=
  orient32 (v := 44915) (by decide) (by decide +kernel) h44915

theorem cover6140 : P.CoversSplit 24 10 6140 0xffffffffaaaaaaaaffffffffaaaaaaaaf5f5f5f500000000f5f5f5f500000000cccccccc88888888cccccccc88888888c4c4c4c400000000c4c4c4c400000000ff33ff33aa22aa22ff33ff33aa22aa22f531f53100000000f531f531000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 860, 867, 909, 916, 1202, 1258, 1601]) (by decide +kernel)

noncomputable def f6140 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (6287360 + i)

theorem c6140_0 : rowSum f6140 0 659 = 14853180 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 6140) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover6140 (by decide)
  decide +kernel

theorem c6140_1 : rowSum f6140 659 365 = 27779390 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 6140) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover6140 (by decide)
  decide +kernel

theorem sum6140 : rowSum f6140 0 1024 = 42632570 :=
  rowSum_append (F := f6140) (lo := 0) (n := 659) (m := 365) (A := 14853180) (B := 27779390) c6140_0 (c6140_1)

theorem h6140 : P.leaf 34 6140 = 42632570 :=
  leaf_weighted (k := 24) (d := 10) (H := 6140) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 6140) (by decide) (by decide +kernel)) sum6140

theorem cover19439 : P.CoversSplit 24 10 19439 0xffffffffaaaaaaaaffffffffaaaaaaaaffff000000000000ffff000000000000cccccccc88888888cccccccc88888888cccc000000000000cccc000000000000ffffffffaaaaaaaa0000000000000000ffff55550000000033330000000000000000000000000000330022002200220000000000000000003300110000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [515, 522, 859, 915, 1202, 1210, 1259, 1601]) (ps := [(17, [1251], [1259]), (18, [1210], [1264])]) (by decide +kernel)

theorem c19439_0 : P.sumLeaves 24 19905536 562 = 21756768 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 19439) (lo := 0) (len := 562) (W := 21756768) check rows elimOK (by decide) (by decide) cover19439 (by decide)
  decide +kernel

theorem c19439_1 : P.sumLeaves 24 19906098 335 = 34098650 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 19439) (lo := 562) (len := 335) (W := 34098650) check rows elimOK (by decide) (by decide) cover19439 (by decide)
  decide +kernel

theorem c19439_2 : P.sumLeaves 24 19906433 127 = 59364992 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 19439) (lo := 897) (len := 127) (W := 59364992) check rows elimOK (by decide) (by decide) cover19439 (by decide)
  decide +kernel

theorem h19439 : P.leaf 34 19439 = 115220410 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(562, 21756768), (335, 34098650), (127, 59364992)]) (.cons c19439_0 (.cons c19439_1 (.cons c19439_2 (.nil)))) (by decide) (by decide))

theorem h6141 : P.leaf 34 6141 = 115220410 :=
  orient4 (v := 19439) (by decide) (by decide +kernel) h19439

theorem cover6143 : P.CoversSplit 24 10 6143 0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaacccccccc88888888cccccccc88888888cccccccc88888888cccccccc88888888ffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaacccccccc88888888cccccccc88888888cccccccc88888888cccccccc88888888 :=
  coversSplit check rows (by decide) (by decide) (xs := [860, 916, 1202, 1258, 1601]) (by decide +kernel)

noncomputable def f6143 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (6290432 + i)

theorem c6143_0 : rowSum f6143 0 295 = 75033604 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 6143) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover6143 (by decide)
  decide +kernel

theorem c6143_1 : rowSum f6143 295 187 = 131417051 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 6143) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover6143 (by decide)
  decide +kernel

theorem c6143_2 : rowSum f6143 482 476 = 267533330 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 6143) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover6143 (by decide)
  decide +kernel

theorem c6143_3 : rowSum f6143 958 66 = 55805672 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 6143) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover6143 (by decide)
  decide +kernel

theorem sum6143 : rowSum f6143 0 1024 = 529789657 :=
  rowSum_append (F := f6143) (lo := 0) (n := 295) (m := 729) (A := 75033604) (B := 454756053) c6143_0 (rowSum_append (F := f6143) (lo := 295) (n := 187) (m := 542) (A := 131417051) (B := 323339002) c6143_1 (rowSum_append (F := f6143) (lo := 482) (n := 476) (m := 66) (A := 267533330) (B := 55805672) c6143_2 (c6143_3)))

theorem h6143 : P.leaf 34 6143 = 529789657 :=
  leaf_weighted (k := 24) (d := 10) (H := 6143) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 6143) (by decide) (by decide +kernel)) sum6143

theorem cover6340 : P.CoversSplit 24 10 6340 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 515, 516, 522, 523, 536, 566, 573, 858, 865, 916, 1202, 1258, 1272]) (by decide +kernel)

theorem h6340 : P.leaf 34 6340 = 1440 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 6340) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 6340) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover6340 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover6341 : P.CoversSplit 24 10 6341 0x8000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 515, 516, 522, 523, 536, 566, 573, 858, 865, 1202, 1258, 1272]) (by decide +kernel)

theorem h6341 : P.leaf 34 6341 = 8000 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 6341) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 6341) (weight := fun _ => 1) (xs := [720, 1023]) check rows elimOK (by decide) (by decide) cover6341 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover6343 : P.CoversSplit 24 10 6343 0x8000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 515, 516, 522, 523, 536, 566, 573, 858, 865, 1202, 1258, 1272]) (by decide +kernel)

theorem h6343 : P.leaf 34 6343 = 99392 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 6343) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 6343) (weight := fun _ => 1) (xs := [720, 1023]) check rows elimOK (by decide) (by decide) cover6343 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover6348 : P.CoversSplit 24 10 6348 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 515, 516, 522, 523, 536, 566, 573, 858, 859, 865, 916, 1202, 1258, 1272]) (by decide +kernel)

theorem h6348 : P.leaf 34 6348 = 22544 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 6348) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 6348) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover6348 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover6349 : P.CoversSplit 24 10 6349 0x8000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 515, 516, 522, 523, 536, 566, 573, 858, 859, 865, 1202, 1258, 1272]) (by decide +kernel)

theorem h6349 : P.leaf 34 6349 = 33984 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 6349) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 6349) (weight := fun _ => 1) (xs := [720, 1023]) check rows elimOK (by decide) (by decide) cover6349 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover6351 : P.CoversSplit 24 10 6351 0x8000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 515, 516, 522, 523, 536, 566, 573, 858, 865, 1202, 1258, 1272]) (by decide +kernel)

theorem h6351 : P.leaf 34 6351 = 200384 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 6351) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 6351) (weight := fun _ => 1) (xs := [720, 1023]) check rows elimOK (by decide) (by decide) cover6351 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover6356 : P.CoversSplit 24 10 6356 0xf000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 479, 536, 573, 858, 859, 865, 866, 879, 1202, 1259]) (by decide +kernel)

theorem h6356 : P.leaf 34 6356 = 15040 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 6356) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 6356) (weight := fun _ => 1) (xs := [1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover6356 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover6357 : P.CoversSplit 24 10 6357 0xff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 479, 516, 536, 573, 858, 859, 865, 879, 1202, 1209, 1210, 1251, 1259]) (ps := [(8, [1272], [475])]) (by decide +kernel)

theorem h6357 : P.leaf 34 6357 = 77192 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 6357) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 6357) (weight := fun _ => 1) (xs := [1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover6357 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover6358 : P.CoversSplit 24 10 6358 0xf0f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 479, 536, 573, 858, 865, 866, 879, 1202, 1210, 1259]) (by decide +kernel)

theorem h6358 : P.leaf 34 6358 = 257148 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 6358) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 6358) (weight := fun _ => 1) (xs := [1012, 1013, 1014, 1015, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover6358 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover6359 : P.CoversSplit 24 10 6359 0xffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [479, 516, 536, 573, 858, 859, 865, 866, 879, 916, 1202, 1209, 1210, 1251, 1259]) (ps := [(8, [1272], [1266])]) (by decide +kernel)

theorem h6359 : P.leaf 34 6359 = 1574512 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 6359) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 6359) (weight := fun _ => 1) (xs := [1008, 1009, 1010, 1011, 1012, 1013, 1014, 1015, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover6359 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover6364 : P.CoversSplit 24 10 6364 0xf000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 516, 536, 573, 858, 859, 865, 879, 1202, 1259, 1264]) (ps := [(8, [1272], [1266])]) (by decide +kernel)

theorem h6364 : P.leaf 34 6364 = 96120 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 6364) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 6364) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 6364) (weight := rowWeight keep1 twice1) (xs := [1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover6364 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover6365 : P.CoversSplit 24 10 6365 0xff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 516, 536, 573, 858, 859, 865, 879, 1202, 1209, 1210, 1251, 1259, 1264]) (ps := [(8, [1272], [1266])]) (by decide +kernel)

theorem h6365 : P.leaf 34 6365 = 490140 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 6365) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 6365) (weight := fun _ => 1) (xs := [1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover6365 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover6367 : P.CoversSplit 24 10 6367 0xffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [516, 536, 573, 858, 859, 865, 879, 916, 1202, 1209, 1210, 1251, 1259, 1264]) (ps := [(8, [1272], [1266])]) (by decide +kernel)

theorem h6367 : P.leaf 34 6367 = 3455320 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 6367) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 6367) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 6367) (weight := rowWeight keep1 twice1) (xs := [1008, 1009, 1010, 1011, 1012, 1013, 1014, 1015, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover6367 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover6372 : P.CoversSplit 24 10 6372 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [472]) (by decide +kernel)

theorem h6372 : P.leaf 34 6372 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 6372) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 6372) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover6372 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover6373 : P.CoversSplit 24 10 6373 0x8000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 472, 473, 515, 522, 573, 858, 865, 879, 1209, 1258, 1272]) (by decide +kernel)

theorem h6373 : P.leaf 34 6373 = 13336 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 6373) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 6373) (weight := fun _ => 1) (xs := [720, 1023]) check rows elimOK (by decide) (by decide) cover6373 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover6374 : P.CoversSplit 24 10 6374 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 465, 472, 515, 522, 524, 566, 573, 858, 859, 865, 879, 1209, 1258]) (by decide +kernel)

theorem h6374 : P.leaf 34 6374 = 65888 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 6374) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 6374) (weight := fun _ => 1) (xs := [720, 895, 1023]) check rows elimOK (by decide) (by decide) cover6374 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover6375 : P.CoversSplit 24 10 6375 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 515, 522, 524, 566, 573, 858, 865, 866, 879, 1209, 1258]) (by decide +kernel)

theorem h6375 : P.leaf 34 6375 = 246624 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 6375) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 6375) (weight := fun _ => 1) (xs := [592, 720, 895, 1023]) check rows elimOK (by decide) (by decide) cover6375 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover6376 : P.CoversSplit 24 10 6376 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [472]) (by decide +kernel)

theorem h6376 : P.leaf 34 6376 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 6376) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 6376) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover6376 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover6377 : P.CoversSplit 24 10 6377 0x8000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 472, 473, 515, 522, 573, 858, 865, 879, 1209, 1258, 1272]) (by decide +kernel)

theorem h6377 : P.leaf 34 6377 = 22416 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 6377) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 6377) (weight := fun _ => 1) (xs := [720, 1023]) check rows elimOK (by decide) (by decide) cover6377 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover6378 : P.CoversSplit 24 10 6378 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 465, 472, 515, 522, 524, 566, 573, 858, 859, 865, 879, 1209, 1258]) (by decide +kernel)

theorem h6378 : P.leaf 34 6378 = 75232 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 6378) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 6378) (weight := fun _ => 1) (xs := [720, 895, 1023]) check rows elimOK (by decide) (by decide) cover6378 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover6379 : P.CoversSplit 24 10 6379 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 515, 522, 524, 566, 573, 858, 865, 866, 879, 1209, 1258]) (by decide +kernel)

theorem h6379 : P.leaf 34 6379 = 419280 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 6379) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 6379) (weight := fun _ => 1) (xs := [592, 720, 895, 1023]) check rows elimOK (by decide) (by decide) cover6379 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover6380 : P.CoversSplit 24 10 6380 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [472]) (by decide +kernel)

theorem h6380 : P.leaf 34 6380 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 6380) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 6380) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover6380 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover6381 : P.CoversSplit 24 10 6381 0x8000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 472, 473, 515, 522, 573, 858, 865, 879, 1209, 1258, 1272]) (by decide +kernel)

theorem h6381 : P.leaf 34 6381 = 87696 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 6381) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 6381) (weight := fun _ => 1) (xs := [720, 1023]) check rows elimOK (by decide) (by decide) cover6381 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover6382 : P.CoversSplit 24 10 6382 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 465, 472, 515, 522, 524, 566, 573, 858, 859, 865, 879, 1209, 1258]) (by decide +kernel)

theorem h6382 : P.leaf 34 6382 = 216704 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 6382) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 6382) (weight := fun _ => 1) (xs := [720, 895, 1023]) check rows elimOK (by decide) (by decide) cover6382 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover6383 : P.CoversSplit 24 10 6383 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 515, 522, 524, 566, 573, 858, 865, 866, 879, 1209, 1258]) (by decide +kernel)

theorem h6383 : P.leaf 34 6383 = 684320 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 6383) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 6383) (weight := fun _ => 1) (xs := [592, 720, 895, 1023]) check rows elimOK (by decide) (by decide) cover6383 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover6388 : P.CoversSplit 24 10 6388 0xf0000000a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 573, 858, 859, 865, 866, 879, 916, 1202, 1210, 1259, 1264, 1308]) (by decide +kernel)

theorem h6388 : P.leaf 34 6388 = 35952 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 6388) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 6388) (weight := fun _ => 1) (xs := [989, 991, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover6388 (by decide) (by decide) (by decide +kernel)
  decide +kernel

def seg : List (ℕ × ℕ) := [(6136, 24), (6137, 48), (6139, 24), (6140, 24), (6141, 48), (6143, 24), (6340, 24), (6341, 48), (6343, 24), (6348, 12), (6349, 24), (6351, 12), (6356, 48), (6357, 48), (6358, 48), (6359, 48), (6364, 24), (6365, 48), (6367, 24), (6372, 48), (6373, 48), (6374, 48), (6375, 48), (6376, 48), (6377, 48), (6378, 48), (6379, 48), (6380, 48), (6381, 48), (6382, 48), (6383, 48), (6388, 48)]

theorem segOK : checkSeg 16 perms 6136 6389 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 6136 6389 1248 22473065328 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 22473065328)
    (SegSum.cons (w := 24) h6136 (SegSum.cons (w := 48) h6137 (SegSum.cons (w := 24) h6139 (SegSum.cons (w := 24) h6140 (SegSum.cons (w := 48) h6141 (SegSum.cons (w := 24) h6143 (SegSum.cons (w := 24) h6340 (SegSum.cons (w := 48) h6341 (SegSum.cons (w := 24) h6343 (SegSum.cons (w := 12) h6348 (SegSum.cons (w := 24) h6349 (SegSum.cons (w := 12) h6351 (SegSum.cons (w := 48) h6356 (SegSum.cons (w := 48) h6357 (SegSum.cons (w := 48) h6358 (SegSum.cons (w := 48) h6359 (SegSum.cons (w := 24) h6364 (SegSum.cons (w := 48) h6365 (SegSum.cons (w := 24) h6367 (SegSum.cons (w := 48) h6372 (SegSum.cons (w := 48) h6373 (SegSum.cons (w := 48) h6374 (SegSum.cons (w := 48) h6375 (SegSum.cons (w := 48) h6376 (SegSum.cons (w := 48) h6377 (SegSum.cons (w := 48) h6378 (SegSum.cons (w := 48) h6379 (SegSum.cons (w := 48) h6380 (SegSum.cons (w := 48) h6381 (SegSum.cons (w := 48) h6382 (SegSum.cons (w := 48) h6383 (SegSum.cons (w := 48) h6388 (show SegSum (P.leaf 34) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S4N1.C0.S34
