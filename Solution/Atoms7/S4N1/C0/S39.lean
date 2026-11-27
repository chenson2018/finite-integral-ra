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

namespace RACert.S4N1.C0.S39

open RACert RACert.Problem

theorem cover6139 : P.CoversSplit 24 10 6139 0xffffffffa0a0a0a0ffffffffa0a0a0a0ffffffffa0a0a0a0ffffffffa0a0a0a0cc00cc0080008000cc00cc0080008000cc00cc0080008000cc00cc0080008000ffffffffa0a0a0a0ffffffffa0a0a0a0ffffffffa0a0a0a0ffffffffa0a0a0a0cc00cc0080008000cc00cc0080008000cc00cc0080008000cc00cc0080008000 :=
  coversSplit check rows (by decide) (by decide) (xs := [860, 916, 1202, 1258, 1601]) (by decide +kernel)

noncomputable def f6139 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (6286336 + i)

theorem c6139_0 : rowSum f6139 0 429 = 10473264 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 6139) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover6139 (by decide)
  decide +kernel

theorem c6139_1 : rowSum f6139 429 523 = 36795100 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 6139) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover6139 (by decide)
  decide +kernel

theorem c6139_2 : rowSum f6139 952 72 = 15681024 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 6139) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover6139 (by decide)
  decide +kernel

theorem sum6139 : rowSum f6139 0 1024 = 62949388 :=
  rowSum_append (F := f6139) (lo := 0) (n := 429) (m := 595) (A := 10473264) (B := 52476124) c6139_0 (rowSum_append (F := f6139) (lo := 429) (n := 523) (m := 72) (A := 36795100) (B := 15681024) c6139_1 (c6139_2))

theorem h6139 : P.leaf 34 6139 = 62949388 :=
  leaf_weighted (k := 24) (d := 10) (H := 6139) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 6139) (by decide) (by decide +kernel)) sum6139

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
  leaf_weighted (k := 24) (d := 10) (H := 6140) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 6140) (by decide) (by decide +kernel)) sum6140

theorem cover6141 : P.CoversSplit 24 10 6141 0xffffffffaaaaaaaaffffffffaaaaaaaaffffffff00000000ffffffff00000000cccccccc88888888cccccccc88888888cccccccc00000000cccccccc00000000ff33ff33aa22aa22ff33ff33aa22aa22ff33ff3300000000ff33ff33000000000033003300000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 860, 909, 916, 1202, 1258, 1601, 1609]) (by decide +kernel)

theorem c6141_0 : P.sumLeaves 24 6288384 461 = 12337284 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6141) (lo := 0) (len := 461) (W := 12337284) check rows elimOK (by decide) (by decide) cover6141 (by decide)
  decide +kernel

theorem c6141_1 : P.sumLeaves 24 6288845 277 = 19692868 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6141) (lo := 461) (len := 277) (W := 19692868) check rows elimOK (by decide) (by decide) cover6141 (by decide)
  decide +kernel

theorem c6141_2 : P.sumLeaves 24 6289122 190 = 30491612 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6141) (lo := 738) (len := 190) (W := 30491612) check rows elimOK (by decide) (by decide) cover6141 (by decide)
  decide +kernel

theorem c6141_3 : P.sumLeaves 24 6289312 96 = 52698646 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6141) (lo := 928) (len := 96) (W := 52698646) check rows elimOK (by decide) (by decide) cover6141 (by decide)
  decide +kernel

theorem h6141 : P.leaf 34 6141 = 115220410 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(461, 12337284), (277, 19692868), (190, 30491612), (96, 52698646)]) (.cons c6141_0 (.cons c6141_1 (.cons c6141_2 (.cons c6141_3 (.nil))))) (by decide) (by decide))

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
  leaf_weighted (k := 24) (d := 10) (H := 6143) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 6143) (by decide) (by decide +kernel)) sum6143

theorem cover6340 : P.CoversSplit 24 10 6340 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 515, 516, 522, 523, 536, 566, 573, 858, 865, 916, 1202, 1258, 1272]) (by decide +kernel)

theorem c6340_0 : P.sumLeaves 24 6492160 1024 = 1440 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6340) (lo := 0) (len := 1024) (W := 1440) check rows elimOK (by decide) (by decide) cover6340 (by decide)
  decide +kernel

theorem h6340 : P.leaf 34 6340 = 1440 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1440)]) (.cons c6340_0 (.nil)) (by decide) (by decide))

theorem cover6341 : P.CoversSplit 24 10 6341 0x8000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 515, 516, 522, 523, 536, 566, 573, 858, 865, 1202, 1258, 1272]) (by decide +kernel)

theorem c6341_0 : P.sumLeaves 24 6493184 1024 = 8000 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6341) (lo := 0) (len := 1024) (W := 8000) check rows elimOK (by decide) (by decide) cover6341 (by decide)
  decide +kernel

theorem h6341 : P.leaf 34 6341 = 8000 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 8000)]) (.cons c6341_0 (.nil)) (by decide) (by decide))

theorem cover6343 : P.CoversSplit 24 10 6343 0x8000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 515, 516, 522, 523, 536, 566, 573, 858, 865, 1202, 1258, 1272]) (by decide +kernel)

theorem c6343_0 : P.sumLeaves 24 6495232 1024 = 99392 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6343) (lo := 0) (len := 1024) (W := 99392) check rows elimOK (by decide) (by decide) cover6343 (by decide)
  decide +kernel

theorem h6343 : P.leaf 34 6343 = 99392 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 99392)]) (.cons c6343_0 (.nil)) (by decide) (by decide))

theorem cover6348 : P.CoversSplit 24 10 6348 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 515, 516, 522, 523, 536, 566, 573, 858, 859, 865, 916, 1202, 1258, 1272]) (by decide +kernel)

theorem c6348_0 : P.sumLeaves 24 6500352 1024 = 22544 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6348) (lo := 0) (len := 1024) (W := 22544) check rows elimOK (by decide) (by decide) cover6348 (by decide)
  decide +kernel

theorem h6348 : P.leaf 34 6348 = 22544 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 22544)]) (.cons c6348_0 (.nil)) (by decide) (by decide))

theorem cover6349 : P.CoversSplit 24 10 6349 0x8000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 515, 516, 522, 523, 536, 566, 573, 858, 859, 865, 1202, 1258, 1272]) (by decide +kernel)

theorem c6349_0 : P.sumLeaves 24 6501376 1024 = 33984 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6349) (lo := 0) (len := 1024) (W := 33984) check rows elimOK (by decide) (by decide) cover6349 (by decide)
  decide +kernel

theorem h6349 : P.leaf 34 6349 = 33984 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 33984)]) (.cons c6349_0 (.nil)) (by decide) (by decide))

theorem cover6351 : P.CoversSplit 24 10 6351 0x8000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 515, 516, 522, 523, 536, 566, 573, 858, 865, 1202, 1258, 1272]) (by decide +kernel)

theorem c6351_0 : P.sumLeaves 24 6503424 1024 = 200384 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6351) (lo := 0) (len := 1024) (W := 200384) check rows elimOK (by decide) (by decide) cover6351 (by decide)
  decide +kernel

theorem h6351 : P.leaf 34 6351 = 200384 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 200384)]) (.cons c6351_0 (.nil)) (by decide) (by decide))

theorem cover6356 : P.CoversSplit 24 10 6356 0xf000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 479, 536, 573, 858, 859, 865, 866, 879, 1202, 1259]) (by decide +kernel)

theorem c6356_0 : P.sumLeaves 24 6508544 1024 = 15040 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6356) (lo := 0) (len := 1024) (W := 15040) check rows elimOK (by decide) (by decide) cover6356 (by decide)
  decide +kernel

theorem h6356 : P.leaf 34 6356 = 15040 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 15040)]) (.cons c6356_0 (.nil)) (by decide) (by decide))

theorem cover6357 : P.CoversSplit 24 10 6357 0xff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 479, 516, 536, 573, 858, 859, 865, 879, 1202, 1209, 1210, 1251, 1259]) (ps := [(8, [1272], [475])]) (by decide +kernel)

theorem c6357_0 : P.sumLeaves 24 6509568 1024 = 77192 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6357) (lo := 0) (len := 1024) (W := 77192) check rows elimOK (by decide) (by decide) cover6357 (by decide)
  decide +kernel

theorem h6357 : P.leaf 34 6357 = 77192 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 77192)]) (.cons c6357_0 (.nil)) (by decide) (by decide))

theorem cover6358 : P.CoversSplit 24 10 6358 0xf0f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 479, 536, 573, 858, 865, 866, 879, 1202, 1210, 1259]) (by decide +kernel)

theorem c6358_0 : P.sumLeaves 24 6510592 1024 = 257148 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6358) (lo := 0) (len := 1024) (W := 257148) check rows elimOK (by decide) (by decide) cover6358 (by decide)
  decide +kernel

theorem h6358 : P.leaf 34 6358 = 257148 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 257148)]) (.cons c6358_0 (.nil)) (by decide) (by decide))

theorem cover6359 : P.CoversSplit 24 10 6359 0xffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [479, 516, 536, 573, 858, 859, 865, 866, 879, 916, 1202, 1209, 1210, 1251, 1259]) (ps := [(8, [1272], [1266])]) (by decide +kernel)

theorem c6359_0 : P.sumLeaves 24 6511616 1024 = 1574512 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6359) (lo := 0) (len := 1024) (W := 1574512) check rows elimOK (by decide) (by decide) cover6359 (by decide)
  decide +kernel

theorem h6359 : P.leaf 34 6359 = 1574512 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1574512)]) (.cons c6359_0 (.nil)) (by decide) (by decide))

theorem cover6364 : P.CoversSplit 24 10 6364 0xf000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 516, 536, 573, 858, 859, 865, 879, 1202, 1259, 1264]) (ps := [(8, [1272], [1266])]) (by decide +kernel)

noncomputable def f6364 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (6516736 + i)

theorem c6364_0 : rowSum f6364 0 1024 = 96120 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 6364) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover6364 (by decide)
  decide +kernel

theorem sum6364 : rowSum f6364 0 1024 = 96120 :=
  c6364_0

theorem h6364 : P.leaf 34 6364 = 96120 :=
  leaf_weighted (k := 24) (d := 10) (H := 6364) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 6364) (by decide) (by decide +kernel)) sum6364

theorem cover6365 : P.CoversSplit 24 10 6365 0xff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 516, 536, 573, 858, 859, 865, 879, 1202, 1209, 1210, 1251, 1259, 1264]) (ps := [(8, [1272], [1266])]) (by decide +kernel)

theorem c6365_0 : P.sumLeaves 24 6517760 1024 = 490140 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6365) (lo := 0) (len := 1024) (W := 490140) check rows elimOK (by decide) (by decide) cover6365 (by decide)
  decide +kernel

theorem h6365 : P.leaf 34 6365 = 490140 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 490140)]) (.cons c6365_0 (.nil)) (by decide) (by decide))

theorem cover6367 : P.CoversSplit 24 10 6367 0xffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [516, 536, 573, 858, 859, 865, 879, 916, 1202, 1209, 1210, 1251, 1259, 1264]) (ps := [(8, [1272], [1266])]) (by decide +kernel)

noncomputable def f6367 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (6519808 + i)

theorem c6367_0 : rowSum f6367 0 1024 = 3455320 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 6367) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover6367 (by decide)
  decide +kernel

theorem sum6367 : rowSum f6367 0 1024 = 3455320 :=
  c6367_0

theorem h6367 : P.leaf 34 6367 = 3455320 :=
  leaf_weighted (k := 24) (d := 10) (H := 6367) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 6367) (by decide) (by decide +kernel)) sum6367

theorem cover6372 : P.CoversSplit 24 10 6372 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [472]) (by decide +kernel)

theorem c6372_0 : P.sumLeaves 24 6524928 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6372) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover6372 (by decide)
  decide +kernel

theorem h6372 : P.leaf 34 6372 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c6372_0 (.nil)) (by decide) (by decide))

theorem cover6373 : P.CoversSplit 24 10 6373 0x8000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 472, 473, 515, 522, 573, 858, 865, 879, 1209, 1258, 1272]) (by decide +kernel)

theorem c6373_0 : P.sumLeaves 24 6525952 1024 = 13336 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6373) (lo := 0) (len := 1024) (W := 13336) check rows elimOK (by decide) (by decide) cover6373 (by decide)
  decide +kernel

theorem h6373 : P.leaf 34 6373 = 13336 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 13336)]) (.cons c6373_0 (.nil)) (by decide) (by decide))

theorem cover6374 : P.CoversSplit 24 10 6374 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 465, 472, 515, 522, 524, 566, 573, 858, 859, 865, 879, 1209, 1258]) (by decide +kernel)

theorem c6374_0 : P.sumLeaves 24 6526976 1024 = 65888 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6374) (lo := 0) (len := 1024) (W := 65888) check rows elimOK (by decide) (by decide) cover6374 (by decide)
  decide +kernel

theorem h6374 : P.leaf 34 6374 = 65888 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 65888)]) (.cons c6374_0 (.nil)) (by decide) (by decide))

theorem cover6375 : P.CoversSplit 24 10 6375 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 515, 522, 524, 566, 573, 858, 865, 866, 879, 1209, 1258]) (by decide +kernel)

theorem c6375_0 : P.sumLeaves 24 6528000 1024 = 246624 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6375) (lo := 0) (len := 1024) (W := 246624) check rows elimOK (by decide) (by decide) cover6375 (by decide)
  decide +kernel

theorem h6375 : P.leaf 34 6375 = 246624 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 246624)]) (.cons c6375_0 (.nil)) (by decide) (by decide))

theorem cover6376 : P.CoversSplit 24 10 6376 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [472]) (by decide +kernel)

theorem c6376_0 : P.sumLeaves 24 6529024 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6376) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover6376 (by decide)
  decide +kernel

theorem h6376 : P.leaf 34 6376 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c6376_0 (.nil)) (by decide) (by decide))

theorem cover6377 : P.CoversSplit 24 10 6377 0x8000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 472, 473, 515, 522, 573, 858, 865, 879, 1209, 1258, 1272]) (by decide +kernel)

theorem c6377_0 : P.sumLeaves 24 6530048 1024 = 22416 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6377) (lo := 0) (len := 1024) (W := 22416) check rows elimOK (by decide) (by decide) cover6377 (by decide)
  decide +kernel

theorem h6377 : P.leaf 34 6377 = 22416 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 22416)]) (.cons c6377_0 (.nil)) (by decide) (by decide))

theorem cover6378 : P.CoversSplit 24 10 6378 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 465, 472, 515, 522, 524, 566, 573, 858, 859, 865, 879, 1209, 1258]) (by decide +kernel)

theorem c6378_0 : P.sumLeaves 24 6531072 1024 = 75232 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6378) (lo := 0) (len := 1024) (W := 75232) check rows elimOK (by decide) (by decide) cover6378 (by decide)
  decide +kernel

theorem h6378 : P.leaf 34 6378 = 75232 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 75232)]) (.cons c6378_0 (.nil)) (by decide) (by decide))

theorem cover6379 : P.CoversSplit 24 10 6379 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 515, 522, 524, 566, 573, 858, 865, 866, 879, 1209, 1258]) (by decide +kernel)

theorem c6379_0 : P.sumLeaves 24 6532096 1024 = 419280 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6379) (lo := 0) (len := 1024) (W := 419280) check rows elimOK (by decide) (by decide) cover6379 (by decide)
  decide +kernel

theorem h6379 : P.leaf 34 6379 = 419280 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 419280)]) (.cons c6379_0 (.nil)) (by decide) (by decide))

theorem cover6380 : P.CoversSplit 24 10 6380 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [472]) (by decide +kernel)

theorem c6380_0 : P.sumLeaves 24 6533120 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6380) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover6380 (by decide)
  decide +kernel

theorem h6380 : P.leaf 34 6380 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c6380_0 (.nil)) (by decide) (by decide))

theorem cover6381 : P.CoversSplit 24 10 6381 0x8000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 472, 473, 515, 522, 573, 858, 865, 879, 1209, 1258, 1272]) (by decide +kernel)

theorem c6381_0 : P.sumLeaves 24 6534144 1024 = 87696 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6381) (lo := 0) (len := 1024) (W := 87696) check rows elimOK (by decide) (by decide) cover6381 (by decide)
  decide +kernel

theorem h6381 : P.leaf 34 6381 = 87696 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 87696)]) (.cons c6381_0 (.nil)) (by decide) (by decide))

theorem cover6382 : P.CoversSplit 24 10 6382 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 465, 472, 515, 522, 524, 566, 573, 858, 859, 865, 879, 1209, 1258]) (by decide +kernel)

theorem c6382_0 : P.sumLeaves 24 6535168 1024 = 216704 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6382) (lo := 0) (len := 1024) (W := 216704) check rows elimOK (by decide) (by decide) cover6382 (by decide)
  decide +kernel

theorem h6382 : P.leaf 34 6382 = 216704 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 216704)]) (.cons c6382_0 (.nil)) (by decide) (by decide))

theorem cover6383 : P.CoversSplit 24 10 6383 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 515, 522, 524, 566, 573, 858, 865, 866, 879, 1209, 1258]) (by decide +kernel)

theorem c6383_0 : P.sumLeaves 24 6536192 1024 = 684320 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6383) (lo := 0) (len := 1024) (W := 684320) check rows elimOK (by decide) (by decide) cover6383 (by decide)
  decide +kernel

theorem h6383 : P.leaf 34 6383 = 684320 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 684320)]) (.cons c6383_0 (.nil)) (by decide) (by decide))

theorem cover6388 : P.CoversSplit 24 10 6388 0xf0000000a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 573, 858, 859, 865, 866, 879, 916, 1202, 1210, 1259, 1264, 1308]) (by decide +kernel)

theorem c6388_0 : P.sumLeaves 24 6541312 1024 = 35952 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6388) (lo := 0) (len := 1024) (W := 35952) check rows elimOK (by decide) (by decide) cover6388 (by decide)
  decide +kernel

theorem h6388 : P.leaf 34 6388 = 35952 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 35952)]) (.cons c6388_0 (.nil)) (by decide) (by decide))

theorem cover6389 : P.CoversSplit 24 10 6389 0xff00ff00af000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 573, 858, 865, 866, 879, 1202, 1209, 1210, 1217, 1259, 1308]) (by decide +kernel)

theorem c6389_0 : P.sumLeaves 24 6542336 1024 = 165132 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6389) (lo := 0) (len := 1024) (W := 165132) check rows elimOK (by decide) (by decide) cover6389 (by decide)
  decide +kernel

theorem h6389 : P.leaf 34 6389 = 165132 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 165132)]) (.cons c6389_0 (.nil)) (by decide) (by decide))

theorem cover6390 : P.CoversSplit 24 10 6390 0xf0f00000a0a500000000000000000000f0f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 573, 858, 859, 865, 866, 879, 1202, 1210, 1259]) (by decide +kernel)

theorem c6390_0 : P.sumLeaves 24 6543360 1024 = 1036068 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6390) (lo := 0) (len := 1024) (W := 1036068) check rows elimOK (by decide) (by decide) cover6390 (by decide)
  decide +kernel

theorem h6390 : P.leaf 34 6390 = 1036068 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1036068)]) (.cons c6390_0 (.nil)) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(6139, 24), (6140, 24), (6141, 48), (6143, 24), (6340, 24), (6341, 48), (6343, 24), (6348, 12), (6349, 24), (6351, 12), (6356, 48), (6357, 48), (6358, 48), (6359, 48), (6364, 24), (6365, 48), (6367, 24), (6372, 48), (6373, 48), (6374, 48), (6375, 48), (6376, 48), (6377, 48), (6378, 48), (6379, 48), (6380, 48), (6381, 48), (6382, 48), (6383, 48), (6388, 48), (6389, 48), (6390, 48)]

theorem segOK : checkSeg 16 perms 6139 6391 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 6139 6391 1272 21134196360 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 21134196360)
    (SegSum.cons (w := 24) h6139 (SegSum.cons (w := 24) h6140 (SegSum.cons (w := 48) h6141 (SegSum.cons (w := 24) h6143 (SegSum.cons (w := 24) h6340 (SegSum.cons (w := 48) h6341 (SegSum.cons (w := 24) h6343 (SegSum.cons (w := 12) h6348 (SegSum.cons (w := 24) h6349 (SegSum.cons (w := 12) h6351 (SegSum.cons (w := 48) h6356 (SegSum.cons (w := 48) h6357 (SegSum.cons (w := 48) h6358 (SegSum.cons (w := 48) h6359 (SegSum.cons (w := 24) h6364 (SegSum.cons (w := 48) h6365 (SegSum.cons (w := 24) h6367 (SegSum.cons (w := 48) h6372 (SegSum.cons (w := 48) h6373 (SegSum.cons (w := 48) h6374 (SegSum.cons (w := 48) h6375 (SegSum.cons (w := 48) h6376 (SegSum.cons (w := 48) h6377 (SegSum.cons (w := 48) h6378 (SegSum.cons (w := 48) h6379 (SegSum.cons (w := 48) h6380 (SegSum.cons (w := 48) h6381 (SegSum.cons (w := 48) h6382 (SegSum.cons (w := 48) h6383 (SegSum.cons (w := 48) h6388 (SegSum.cons (w := 48) h6389 (SegSum.cons (w := 48) h6390 (show SegSum (P.leaf 34) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S4N1.C0.S39
