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

namespace RACert.S4N1.C0.S38

open RACert RACert.Problem

theorem cover6131 : P.CoversSplit 24 10 6131 0xffffffffa0a0a0a0ffffffffa0a0a0a0ffffffffa0a0a0a0ffffffffa0a0a0a0cc00cc0080008000cc00cc0080008000cc00cc0080008000cc00cc0080008000ffffffffa0a0a0a0ffffffffa0a0a0a0ffffffffa0a0a0a0ffffffffa0a0a0a0cc00cc0080008000cc00cc0080008000cc00cc0080008000cc00cc0080008000 :=
  coversSplit check rows (by decide) (by decide) (xs := [860, 916, 1202, 1258, 1601]) (by decide +kernel)

noncomputable def f6131 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (6278144 + i)

theorem c6131_0 : rowSum f6131 0 429 = 4658980 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 6131) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover6131 (by decide)
  decide +kernel

theorem c6131_1 : rowSum f6131 429 523 = 15681824 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 6131) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover6131 (by decide)
  decide +kernel

theorem c6131_2 : rowSum f6131 952 72 = 7522688 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 6131) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover6131 (by decide)
  decide +kernel

theorem sum6131 : rowSum f6131 0 1024 = 27863492 :=
  rowSum_append (F := f6131) (lo := 0) (n := 429) (m := 595) (A := 4658980) (B := 23204512) c6131_0 (rowSum_append (F := f6131) (lo := 429) (n := 523) (m := 72) (A := 15681824) (B := 7522688) c6131_1 (c6131_2))

theorem h6131 : P.leaf 34 6131 = 27863492 :=
  leaf_weighted (k := 24) (d := 10) (H := 6131) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 6131) (by decide) (by decide +kernel)) sum6131

theorem cover6132 : P.CoversSplit 24 10 6132 0xffffffffaaaaaaaaffffffffaaaaaaaaf5f5f5f500000000f5f5f5f500000000cccccccc88888888cccccccc88888888c4c4c4c400000000c4c4c4c400000000ff33ff33aa22aa22ff33ff33aa22aa22f531f53100000000f531f531000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 860, 867, 909, 916, 1202, 1258, 1601]) (by decide +kernel)

noncomputable def f6132 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (6279168 + i)

theorem c6132_0 : rowSum f6132 0 659 = 2520254 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 6132) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover6132 (by decide)
  decide +kernel

theorem c6132_1 : rowSum f6132 659 365 = 5076145 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 6132) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover6132 (by decide)
  decide +kernel

theorem sum6132 : rowSum f6132 0 1024 = 7596399 :=
  rowSum_append (F := f6132) (lo := 0) (n := 659) (m := 365) (A := 2520254) (B := 5076145) c6132_0 (c6132_1)

theorem h6132 : P.leaf 34 6132 = 7596399 :=
  leaf_weighted (k := 24) (d := 10) (H := 6132) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 6132) (by decide) (by decide +kernel)) sum6132

theorem cover6133 : P.CoversSplit 24 10 6133 0xffffffffaaaaaaaaffffffffaaaaaaaaffffffff00000000ffffffff00000000cccccccc88888888cccccccc88888888cccccccc00000000cccccccc00000000ff33ff33aa22aa22ff33ff33aa22aa22ff33ff3300000000ff33ff33000000000033003300000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 860, 909, 916, 1202, 1258, 1601, 1609]) (by decide +kernel)

theorem c6133_0 : P.sumLeaves 24 6280192 461 = 5761752 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6133) (lo := 0) (len := 461) (W := 5761752) check rows elimOK (by decide) (by decide) cover6133 (by decide)
  decide +kernel

theorem c6133_1 : P.sumLeaves 24 6280653 277 = 10959334 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6133) (lo := 461) (len := 277) (W := 10959334) check rows elimOK (by decide) (by decide) cover6133 (by decide)
  decide +kernel

theorem c6133_2 : P.sumLeaves 24 6280930 190 = 18310215 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6133) (lo := 738) (len := 190) (W := 18310215) check rows elimOK (by decide) (by decide) cover6133 (by decide)
  decide +kernel

theorem c6133_3 : P.sumLeaves 24 6281120 96 = 30476980 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6133) (lo := 928) (len := 96) (W := 30476980) check rows elimOK (by decide) (by decide) cover6133 (by decide)
  decide +kernel

theorem h6133 : P.leaf 34 6133 = 65508281 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(461, 5761752), (277, 10959334), (190, 18310215), (96, 30476980)]) (.cons c6133_0 (.cons c6133_1 (.cons c6133_2 (.cons c6133_3 (.nil))))) (by decide) (by decide))

theorem cover6135 : P.CoversSplit 24 10 6135 0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaacccccccc88888888cccccccc88888888cccccccc88888888cccccccc88888888ffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaacccccccc88888888cccccccc88888888cccccccc88888888cccccccc88888888 :=
  coversSplit check rows (by decide) (by decide) (xs := [860, 916, 1202, 1258, 1601]) (by decide +kernel)

noncomputable def f6135 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (6282240 + i)

theorem c6135_0 : rowSum f6135 0 295 = 9837648 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 6135) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover6135 (by decide)
  decide +kernel

theorem c6135_1 : rowSum f6135 295 187 = 55259488 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 6135) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover6135 (by decide)
  decide +kernel

theorem c6135_2 : rowSum f6135 482 476 = 124321259 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 6135) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover6135 (by decide)
  decide +kernel

theorem c6135_3 : rowSum f6135 958 66 = 32695316 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 6135) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover6135 (by decide)
  decide +kernel

theorem sum6135 : rowSum f6135 0 1024 = 222113711 :=
  rowSum_append (F := f6135) (lo := 0) (n := 295) (m := 729) (A := 9837648) (B := 212276063) c6135_0 (rowSum_append (F := f6135) (lo := 295) (n := 187) (m := 542) (A := 55259488) (B := 157016575) c6135_1 (rowSum_append (F := f6135) (lo := 482) (n := 476) (m := 66) (A := 124321259) (B := 32695316) c6135_2 (c6135_3)))

theorem h6135 : P.leaf 34 6135 = 222113711 :=
  leaf_weighted (k := 24) (d := 10) (H := 6135) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 6135) (by decide) (by decide +kernel)) sum6135

theorem cover6136 : P.CoversSplit 24 10 6136 0xffffffffa0a0a0a0ffffffffa0a0a0a0f0f0f0f000000000f0f0f0f000000000cc00cc0080008000cc00cc0080008000c000c00000000000c000c00000000000ff00ff00a000a000ff00ff00a000a000ffffffff00000000ffffffff000000000000000000000000000000000000000000000000888888880000000088888888 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 860, 916, 1202, 1258, 1601]) (ps := [(12, [860, 867, 909], [860, 867, 909]), (14, [874, 923], [860, 916])]) (by decide +kernel)

noncomputable def f6136 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (6283264 + i)

theorem c6136_0 : rowSum f6136 0 735 = 3293423 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 6136) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover6136 (by decide)
  decide +kernel

theorem c6136_1 : rowSum f6136 735 289 = 5670230 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 6136) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover6136 (by decide)
  decide +kernel

theorem sum6136 : rowSum f6136 0 1024 = 8963653 :=
  rowSum_append (F := f6136) (lo := 0) (n := 735) (m := 289) (A := 3293423) (B := 5670230) c6136_0 (c6136_1)

theorem h6136 : P.leaf 34 6136 = 8963653 :=
  leaf_weighted (k := 24) (d := 10) (H := 6136) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 6136) (by decide) (by decide +kernel)) sum6136

theorem cover6137 : P.CoversSplit 24 10 6137 0xffffffffa0a0a0a0ffffffffa0a0a0a0ffffffff00000000ffffffff00000000cc00cc0080008000cc00cc0080008000cc00cc0000000000cc00cc0000000000ff00ff00a000a000ff00ff00a000a000ffffffff00000000ffffffff0000000000ff00ff0080008000cc00cc0080008000cc00cc0000000000cc00cc00000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 860, 916, 1202, 1258, 1601, 1609]) (ps := [(12, [860, 867], [909, 916]), (14, [923], [916])]) (by decide +kernel)

theorem c6137_0 : P.sumLeaves 24 6284288 372 = 1301442 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6137) (lo := 0) (len := 372) (W := 1301442) check rows elimOK (by decide) (by decide) cover6137 (by decide)
  decide +kernel

theorem c6137_1 : P.sumLeaves 24 6284660 436 = 5809043 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6137) (lo := 372) (len := 436) (W := 5809043) check rows elimOK (by decide) (by decide) cover6137 (by decide)
  decide +kernel

theorem c6137_2 : P.sumLeaves 24 6285096 157 = 9269476 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6137) (lo := 808) (len := 157) (W := 9269476) check rows elimOK (by decide) (by decide) cover6137 (by decide)
  decide +kernel

theorem c6137_3 : P.sumLeaves 24 6285253 59 = 8232516 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6137) (lo := 965) (len := 59) (W := 8232516) check rows elimOK (by decide) (by decide) cover6137 (by decide)
  decide +kernel

theorem h6137 : P.leaf 34 6137 = 24612477 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(372, 1301442), (436, 5809043), (157, 9269476), (59, 8232516)]) (.cons c6137_0 (.cons c6137_1 (.cons c6137_2 (.cons c6137_3 (.nil))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(6131, 24), (6132, 24), (6133, 48), (6135, 24), (6136, 24), (6137, 48)]

theorem segOK : checkSeg 16 perms 6131 6139 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 6131 6139 192 10722690504 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 10722690504)
    (SegSum.cons (w := 24) h6131 (SegSum.cons (w := 24) h6132 (SegSum.cons (w := 48) h6133 (SegSum.cons (w := 24) h6135 (SegSum.cons (w := 24) h6136 (SegSum.cons (w := 48) h6137 (show SegSum (P.leaf 34) [] 0 from rfl))))))) (by decide)

end RACert.S4N1.C0.S38
