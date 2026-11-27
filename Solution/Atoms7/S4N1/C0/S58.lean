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

namespace RACert.S4N1.C0.S58

open RACert RACert.Problem

theorem cover8127 : P.CoversSplit 24 10 8127 0xfffffffff5f5a0a0fffffffff5f5a0a0fffffffff5f5a0a0fffffffff5f5a0a0ccffccff80008000cc00cc0080008000ccffccff80008000cc00cc0080008000fffffffff5f5a0a0fffffffff5f5a0a000000000000000000000000000000000ccffccff80008000cc00cc008000800000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [517, 916, 1202, 1209, 1210, 1217, 1258, 1308, 1601]) (by decide +kernel)

noncomputable def f8127 (i : ℕ) := rowWeight keep4 twice4 i * P.leaf 24 (8322048 + i)

theorem c8127_0 : rowSum f8127 0 476 = 48185690 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 8127) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover8127 (by decide)
  decide +kernel

theorem c8127_1 : rowSum f8127 476 483 = 173507120 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 8127) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover8127 (by decide)
  decide +kernel

theorem c8127_2 : rowSum f8127 959 65 = 47978282 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 8127) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover8127 (by decide)
  decide +kernel

theorem sum8127 : rowSum f8127 0 1024 = 269671092 :=
  rowSum_append (F := f8127) (lo := 0) (n := 476) (m := 548) (A := 48185690) (B := 221485402) c8127_0 (rowSum_append (F := f8127) (lo := 476) (n := 483) (m := 65) (A := 173507120) (B := 47978282) c8127_1 (c8127_2))

theorem h8127 : P.leaf 34 8127 = 269671092 :=
  leaf_weighted (k := 24) (d := 10) (H := 8127) (keep := keep4) (twice := twice4) rows (by decide) (by decide) bal4 (invRow4 (H := 8127) (by decide) (by decide +kernel)) sum8127

theorem cover8147 : P.CoversSplit 24 10 8147 0xfffffffff5f5a0a0fffffffff5f5a0a0fffffffff5f5a0a0fffffffff5f5a0a0ccffccff80008000cc00cc0080008000ccffccff80008000cc00cc0080008000fffffffff5f5a0a0fffffffff5f5a0a0ffffffffa0a0a0a0ffffffffa0a0a0a0ccffccff80008000cc00cc0080008000cc00cc0080008000cc00cc0080008000 :=
  coversProjected check rows (by decide) (by decide) (xs := [516, 916, 1202, 1209, 1210, 1217, 1258, 1259, 1601, 1609]) (ps := [(8, [1609], [1266]), (14, [1217], [1266])]) (by decide +kernel)

noncomputable def f8147 (i : ℕ) := rowWeight keep5 twice5 i * P.leaf 24 (8342528 + i)

theorem c8147_0 : rowSum f8147 0 402 = 1641398 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 8147) (keep := keep5) (twice := twice5) check rows elimOK (by decide) (by decide) cover8147 (by decide)
  decide +kernel

theorem c8147_1 : rowSum f8147 402 285 = 23886874 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 8147) (keep := keep5) (twice := twice5) check rows elimOK (by decide) (by decide) cover8147 (by decide)
  decide +kernel

theorem c8147_2 : rowSum f8147 687 337 = 38794056 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 8147) (keep := keep5) (twice := twice5) check rows elimOK (by decide) (by decide) cover8147 (by decide)
  decide +kernel

theorem sum8147 : rowSum f8147 0 1024 = 64322328 :=
  rowSum_append (F := f8147) (lo := 0) (n := 402) (m := 622) (A := 1641398) (B := 62680930) c8147_0 (rowSum_append (F := f8147) (lo := 402) (n := 285) (m := 337) (A := 23886874) (B := 38794056) c8147_1 (c8147_2))

theorem h8147 : P.leaf 34 8147 = 64322328 :=
  leaf_weighted (k := 24) (d := 10) (H := 8147) (keep := keep5) (twice := twice5) rows (by decide) (by decide) bal5 (invRow5 (H := 8147) (by decide) (by decide +kernel)) sum8147

theorem cover8148 : P.CoversSplit 24 10 8148 0xfffffffff0a0a0a0fffffffff0a0a0a0aaaaafaa00000000aaaaafaa00000000cc88cc8880008000cc00cc008000800088888c880000000088008c0000000000ff00ff00f000a000ff22ff22f020a020aa00af0000000000aa22af22000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 516, 916, 1202, 1210, 1259, 1601]) (ps := [(2, [473, 475], [472]), (6, [465, 479], [472])]) (by decide +kernel)

noncomputable def f8148 (i : ℕ) := rowWeight keep5 twice5 i * P.leaf 24 (8343552 + i)

theorem c8148_0 : rowSum f8148 0 943 = 3567496 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 8148) (keep := keep5) (twice := twice5) check rows elimOK (by decide) (by decide) cover8148 (by decide)
  decide +kernel

theorem c8148_1 : rowSum f8148 943 81 = 2680832 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 8148) (keep := keep5) (twice := twice5) check rows elimOK (by decide) (by decide) cover8148 (by decide)
  decide +kernel

theorem sum8148 : rowSum f8148 0 1024 = 6248328 :=
  rowSum_append (F := f8148) (lo := 0) (n := 943) (m := 81) (A := 3567496) (B := 2680832) c8148_0 (c8148_1)

theorem h8148 : P.leaf 34 8148 = 6248328 :=
  leaf_weighted (k := 24) (d := 10) (H := 8148) (keep := keep5) (twice := twice5) rows (by decide) (by decide) bal5 (invRow5 (H := 8148) (by decide) (by decide +kernel)) sum8148

theorem cover8149 : P.CoversSplit 24 10 8149 0xfffffffff5f5a0a0fffffffff5f5a0a0fffffffff5f5a0a0fffffffff5f5a0a0ccffccff80008000cc00cc0080008000ccffccff80008000cc00cc0080008000ff00ff00f500a000ff33ff33f531a020ff00ff0000000000ff33ff33000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 516, 916, 1202, 1209, 1210, 1217, 1258, 1259, 1601]) (ps := [(8, [615], [1266])]) (by decide +kernel)

theorem c8149_0 : P.sumLeaves 24 8344576 256 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8149) (lo := 0) (len := 256) (W := 0) check rows elimOK (by decide) (by decide) cover8149 (by decide)
  decide +kernel

theorem contract8149_1 : P.leaf 30 130388 = 0 := by
  exact leaf_contract_zero (ss := [(2, 1, 475), (8, 0, 1266), (31, 1, 615), (14, 0, 1266), (5, 1, 433), (21, 1, 482), (20, 1, 488), (9, 7, 629), (12, 1, 825), (15, 13, 972)]) (q := 1272) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c8149_1 : P.sumLeaves 24 8344832 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 130388) rows (by decide) (by decide)).symm.trans contract8149_1

theorem contract8149_2 : P.leaf 30 130389 = 0 := by
  exact leaf_contract_zero (ss := [(2, 1, 475), (29, 1, 916), (8, 0, 1266), (31, 1, 615), (14, 0, 1266), (5, 1, 433), (21, 1, 482), (20, 1, 488), (9, 7, 629), (12, 1, 825), (15, 13, 972)]) (q := 1272) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c8149_2 : P.sumLeaves 24 8344896 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 130389) rows (by decide) (by decide)).symm.trans contract8149_2

theorem c8149_3 : P.sumLeaves 24 8344960 271 = 13918056 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8149) (lo := 384) (len := 271) (W := 13918056) check rows elimOK (by decide) (by decide) cover8149 (by decide)
  decide +kernel

theorem c8149_4 : P.sumLeaves 24 8345231 205 = 15976175 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8149) (lo := 655) (len := 205) (W := 15976175) check rows elimOK (by decide) (by decide) cover8149 (by decide)
  decide +kernel

theorem c8149_5 : P.sumLeaves 24 8345436 128 = 30429094 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8149) (lo := 860) (len := 128) (W := 30429094) check rows elimOK (by decide) (by decide) cover8149 (by decide)
  decide +kernel

theorem c8149_6 : P.sumLeaves 24 8345564 36 = 31304412 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8149) (lo := 988) (len := 36) (W := 31304412) check rows elimOK (by decide) (by decide) cover8149 (by decide)
  decide +kernel

theorem h8149 : P.leaf 34 8149 = 91627737 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(256, 0), (64, 0), (64, 0), (271, 13918056), (205, 15976175), (128, 30429094), (36, 31304412)]) (.cons c8149_0 (.cons c8149_1 (.cons c8149_2 (.cons c8149_3 (.cons c8149_4 (.cons c8149_5 (.cons c8149_6 (.nil)))))))) (by decide) (by decide))

theorem cover8151 : P.CoversSplit 24 10 8151 0xfffffffff5f5a0a0fffffffff5f5a0a0fffffffff5f5a0a0fffffffff5f5a0a0ccffccff80008000cc00cc0080008000ccffccff80008000cc00cc0080008000fffffffff5f5a0a0fffffffff5f5a0a0ffffffff00000000ffffffff00000000ccffccff80008000cc00cc008000800000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [516, 916, 1202, 1209, 1210, 1217, 1258, 1259, 1601, 1609]) (ps := [(8, [615, 1609], [1266]), (14, [965], [1266])]) (by decide +kernel)

noncomputable def f8151 (i : ℕ) := rowWeight keep5 twice5 i * P.leaf 24 (8346624 + i)

theorem c8151_0 : rowSum f8151 0 424 = 9838386 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 8151) (keep := keep5) (twice := twice5) check rows elimOK (by decide) (by decide) cover8151 (by decide)
  decide +kernel

theorem c8151_1 : rowSum f8151 424 329 = 102251836 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 8151) (keep := keep5) (twice := twice5) check rows elimOK (by decide) (by decide) cover8151 (by decide)
  decide +kernel

theorem c8151_2 : rowSum f8151 753 271 = 110464132 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 8151) (keep := keep5) (twice := twice5) check rows elimOK (by decide) (by decide) cover8151 (by decide)
  decide +kernel

theorem sum8151 : rowSum f8151 0 1024 = 222554354 :=
  rowSum_append (F := f8151) (lo := 0) (n := 424) (m := 600) (A := 9838386) (B := 212715968) c8151_0 (rowSum_append (F := f8151) (lo := 424) (n := 329) (m := 271) (A := 102251836) (B := 110464132) c8151_1 (c8151_2))

theorem h8151 : P.leaf 34 8151 = 222554354 :=
  leaf_weighted (k := 24) (d := 10) (H := 8151) (keep := keep5) (twice := twice5) rows (by decide) (by decide) bal5 (invRow5 (H := 8151) (by decide) (by decide +kernel)) sum8151

theorem cover8152 : P.CoversSplit 24 10 8152 0xfffffffff0a0a0a0fffffffff0a0a0a0aaaaaaaa0000a0a0aaaaaaaa00000000cc88cc8880008000cc00cc008000800088888888000080008800880000000000ff00ff00f000a000ff00ff00f000a000aa00aa000000a000aa00aa00000000000000000000000000cc0000008000000000000000000000008800000000008000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 516, 916, 1202, 1210, 1259, 1601]) (ps := [(2, [473, 487], [472]), (5, [523], [516]), (6, [465, 467], [472]), (8, [537, 558], [516, 1266]), (12, [909], [916]), (14, [509, 923], [916, 1266])]) (by decide +kernel)

noncomputable def f8152 (i : ℕ) := rowWeight keep5 twice5 i * P.leaf 24 (8347648 + i)

theorem c8152_0 : rowSum f8152 0 945 = 4839289 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 8152) (keep := keep5) (twice := twice5) check rows elimOK (by decide) (by decide) cover8152 (by decide)
  decide +kernel

theorem c8152_1 : rowSum f8152 945 79 = 5255688 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 8152) (keep := keep5) (twice := twice5) check rows elimOK (by decide) (by decide) cover8152 (by decide)
  decide +kernel

theorem sum8152 : rowSum f8152 0 1024 = 10094977 :=
  rowSum_append (F := f8152) (lo := 0) (n := 945) (m := 79) (A := 4839289) (B := 5255688) c8152_0 (c8152_1)

theorem h8152 : P.leaf 34 8152 = 10094977 :=
  leaf_weighted (k := 24) (d := 10) (H := 8152) (keep := keep5) (twice := twice5) rows (by decide) (by decide) bal5 (invRow5 (H := 8152) (by decide) (by decide +kernel)) sum8152

theorem cover8153 : P.CoversSplit 24 10 8153 0xfffffffff5f5a0a0fffffffff5f5a0a0fffffffff5f5a0a0fffffffff5f5a0a0ccffccff80008000cc00cc0080008000ccffccff80008000cc00cc0080008000ff00ff00f500a000ff00ff00f500a000ff00ff00a000a000ff00ff00a000a0000000000000000000cc000000800000000000000000000000cc00000080000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 516, 916, 1202, 1209, 1210, 1217, 1258, 1259, 1601]) (ps := [(8, [558], [1266]), (12, [867], [916]), (14, [923, 1217], [916, 1266])]) (by decide +kernel)

theorem contract8153_0 : P.leaf 30 130448 = 0 := by
  exact leaf_contract_zero (ss := [(2, 1, 487), (5, 1, 523), (18, 11, 921), (29, 1, 1259), (12, 0, 916), (6, 1, 818), (10, 1, 803), (30, 1, 867), (14, 1, 965), (8, 1, 537), (17, 1, 537), (3, 1, 536), (15, 1, 930), (19, 1, 930)]) (q := 1266) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c8153_0 : P.sumLeaves 24 8348672 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 130448) rows (by decide) (by decide)).symm.trans contract8153_0

theorem c8153_1 : P.sumLeaves 24 8348736 64 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8153) (lo := 64) (len := 64) (W := 0) check rows elimOK (by decide) (by decide) cover8153 (by decide)
  decide +kernel

theorem contract8153_2 : P.leaf 30 130450 = 8560 := by
  exact leaf_contract_factors (k := 30) (b := 16) (H := 130450) (ss := [(2, 1, 487), (5, 1, 523), (3, 1, 536), (18, 11, 921), (11, 1, 923), (14, 1, 923), (29, 1, 1259), (12, 0, 916), (10, 1, 803), (6, 1, 818), (30, 1, 867), (19, 1, 965), (15, 1, 930), (27, 1, 1601)]) (ids := [2, 5, 6, 7, 11, 14, 15, 18, 19, 20, 21, 22, 24, 26, 29, 23]) (cs := [1, 1, 2, 1, 1, 3, 4, 5, 1, 1, 0, 6, 1, 1, 7, 8, 1, 1, 9, 10, 11, 12, 13, 17, 14, 1, 15, 1, 1, 16]) (bs := [15, 1]) (W := 8560) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c8153_2 : P.sumLeaves 24 8348800 64 = 8560 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 130450) rows (by decide) (by decide)).symm.trans contract8153_2

theorem c8153_3 : P.sumLeaves 24 8348864 64 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8153) (lo := 192) (len := 64) (W := 0) check rows elimOK (by decide) (by decide) cover8153 (by decide)
  decide +kernel

theorem contract8153_4 : P.leaf 30 130452 = 0 := by
  exact leaf_contract_zero (ss := [(2, 1, 487), (5, 1, 523), (8, 0, 1266), (14, 0, 537), (20, 1, 482), (21, 0, 488), (29, 1, 558), (12, 1, 825), (31, 1, 1217)]) (q := 1272) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c8153_4 : P.sumLeaves 24 8348928 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 130452) rows (by decide) (by decide)).symm.trans contract8153_4

theorem contract8153_5 : P.leaf 30 130453 = 0 := by
  exact leaf_contract_zero (ss := [(2, 1, 487), (29, 1, 916), (8, 0, 1266), (14, 0, 537), (5, 1, 433), (20, 1, 482), (21, 0, 488), (12, 1, 825), (31, 1, 1217)]) (q := 1272) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c8153_5 : P.sumLeaves 24 8348992 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 130453) rows (by decide) (by decide)).symm.trans contract8153_5

theorem c8153_6 : P.sumLeaves 24 8349056 352 = 6092569 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8153) (lo := 384) (len := 352) (W := 6092569) check rows elimOK (by decide) (by decide) cover8153 (by decide)
  decide +kernel

theorem c8153_7 : P.sumLeaves 24 8349408 136 = 5733916 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8153) (lo := 736) (len := 136) (W := 5733916) check rows elimOK (by decide) (by decide) cover8153 (by decide)
  decide +kernel

theorem c8153_8 : P.sumLeaves 24 8349544 128 = 11839476 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8153) (lo := 872) (len := 128) (W := 11839476) check rows elimOK (by decide) (by decide) cover8153 (by decide)
  decide +kernel

theorem c8153_9 : P.sumLeaves 24 8349672 24 = 9120748 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8153) (lo := 1000) (len := 24) (W := 9120748) check rows elimOK (by decide) (by decide) cover8153 (by decide)
  decide +kernel

theorem h8153 : P.leaf 34 8153 = 32795269 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(64, 0), (64, 0), (64, 8560), (64, 0), (64, 0), (64, 0), (352, 6092569), (136, 5733916), (128, 11839476), (24, 9120748)]) (.cons c8153_0 (.cons c8153_1 (.cons c8153_2 (.cons c8153_3 (.cons c8153_4 (.cons c8153_5 (.cons c8153_6 (.cons c8153_7 (.cons c8153_8 (.cons c8153_9 (.nil))))))))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(8127, 24), (8147, 12), (8148, 24), (8149, 48), (8151, 24), (8152, 24), (8153, 48)]

theorem segOK : checkSeg 16 perms 8127 8155 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 8127 8155 204 18949822248 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 18949822248)
    (SegSum.cons (w := 24) h8127 (SegSum.cons (w := 12) h8147 (SegSum.cons (w := 24) h8148 (SegSum.cons (w := 48) h8149 (SegSum.cons (w := 24) h8151 (SegSum.cons (w := 24) h8152 (SegSum.cons (w := 48) h8153 (show SegSum (P.leaf 34) [] 0 from rfl)))))))) (by decide)

end RACert.S4N1.C0.S58
