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

namespace RACert.S4N1.C0.S59

open RACert RACert.Problem

theorem cover8155 : P.CoversSplit 24 10 8155 0xfffffffff5f5a0a0fffffffff5f5a0a0fffffffff5f5a0a0fffffffff5f5a0a0ccffccff80008000cc00cc0080008000ccffccff80008000cc00cc0080008000fffffffff5f5a0a0fffffffff5f5a0a0ffffffffa0a0a0a0ffffffffa0a0a0a0ccffccff80008000cc00cc0080008000cc00cc0080008000cc00cc0080008000 :=
  coversProjected check rows (by decide) (by decide) (xs := [516, 916, 1202, 1209, 1210, 1217, 1258, 1259, 1601, 1609]) (ps := [(8, [1609], [1266]), (14, [1217], [1266])]) (by decide +kernel)

noncomputable def f8155 (i : ℕ) := rowWeight keep5 twice5 i * P.leaf 24 (8350720 + i)

theorem c8155_0 : rowSum f8155 0 402 = 3345938 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 8155) (keep := keep5) (twice := twice5) check rows elimOK (by decide) (by decide) cover8155 (by decide)
  decide +kernel

theorem c8155_1 : rowSum f8155 402 285 = 31135602 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 8155) (keep := keep5) (twice := twice5) check rows elimOK (by decide) (by decide) cover8155 (by decide)
  decide +kernel

theorem c8155_2 : rowSum f8155 687 337 = 56076156 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 8155) (keep := keep5) (twice := twice5) check rows elimOK (by decide) (by decide) cover8155 (by decide)
  decide +kernel

theorem sum8155 : rowSum f8155 0 1024 = 90557696 :=
  rowSum_append (F := f8155) (lo := 0) (n := 402) (m := 622) (A := 3345938) (B := 87211758) c8155_0 (rowSum_append (F := f8155) (lo := 402) (n := 285) (m := 337) (A := 31135602) (B := 56076156) c8155_1 (c8155_2))

theorem h8155 : P.leaf 34 8155 = 90557696 :=
  leaf_weighted (k := 24) (d := 10) (H := 8155) (keep := keep5) (twice := twice5) rows (by decide) (by decide) bal5 (invRow5 (H := 8155) (by decide) (by decide +kernel)) sum8155

theorem cover8156 : P.CoversSplit 24 10 8156 0xfffffffff0a0a0a0fffffffff0a0a0a0aaaaafaf00000000aaaaafaf00000000cc88cc8880008000cc00cc008000800088888c880000000088008c0000000000ff00ff00f000a000ff33ff33f020a020aa00af0000000000aa22af23000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 516, 916, 1202, 1210, 1259, 1601]) (ps := [(2, [473], [472]), (6, [465], [472])]) (by decide +kernel)

noncomputable def f8156 (i : ℕ) := rowWeight keep5 twice5 i * P.leaf 24 (8351744 + i)

theorem c8156_0 : rowSum f8156 0 933 = 32808198 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 8156) (keep := keep5) (twice := twice5) check rows elimOK (by decide) (by decide) cover8156 (by decide)
  decide +kernel

theorem c8156_1 : rowSum f8156 933 91 = 32448400 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 8156) (keep := keep5) (twice := twice5) check rows elimOK (by decide) (by decide) cover8156 (by decide)
  decide +kernel

theorem sum8156 : rowSum f8156 0 1024 = 65256598 :=
  rowSum_append (F := f8156) (lo := 0) (n := 933) (m := 91) (A := 32808198) (B := 32448400) c8156_0 (c8156_1)

theorem h8156 : P.leaf 34 8156 = 65256598 :=
  leaf_weighted (k := 24) (d := 10) (H := 8156) (keep := keep5) (twice := twice5) rows (by decide) (by decide) bal5 (invRow5 (H := 8156) (by decide) (by decide +kernel)) sum8156

theorem cover8157 : P.CoversSplit 24 10 8157 0xfffffffff5f5a0a0fffffffff5f5a0a0fffffffff5f5a0a0fffffffff5f5a0a0ccffccff80008000cc00cc0080008000ccffccff80008000cc00cc0080008000ff00ff00f500a000ff33ff33f531a020ff00ff00a000a000ff33ff33a020a0200000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 516, 916, 1202, 1209, 1210, 1217, 1258, 1259, 1601]) (ps := [(14, [1217], [916, 1266])]) (by decide +kernel)

theorem c8157_0 : P.sumLeaves 24 8352768 256 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8157) (lo := 0) (len := 256) (W := 0) check rows elimOK (by decide) (by decide) cover8157 (by decide)
  decide +kernel

theorem contract8157_1 : P.leaf 30 130516 = 0 := by
  exact leaf_contract_zero (ss := [(8, 0, 1266), (14, 0, 1266), (5, 1, 433), (20, 1, 531), (21, 1, 537), (9, 7, 629), (12, 1, 825), (15, 13, 972), (31, 1, 1217)]) (q := 1272) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c8157_1 : P.sumLeaves 24 8353024 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 130516) rows (by decide) (by decide)).symm.trans contract8157_1

theorem contract8157_2 : P.leaf 30 130517 = 0 := by
  exact leaf_contract_zero (ss := [(29, 1, 916), (8, 0, 1266), (14, 0, 1266), (5, 1, 433), (20, 1, 531), (21, 1, 537), (9, 7, 629), (12, 1, 825), (15, 13, 972), (31, 1, 1217)]) (q := 1272) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c8157_2 : P.sumLeaves 24 8353088 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 130517) rows (by decide) (by decide)).symm.trans contract8157_2

theorem c8157_3 : P.sumLeaves 24 8353152 271 = 27624151 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8157) (lo := 384) (len := 271) (W := 27624151) check rows elimOK (by decide) (by decide) cover8157 (by decide)
  decide +kernel

theorem c8157_4 : P.sumLeaves 24 8353423 205 = 29965433 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8157) (lo := 655) (len := 205) (W := 29965433) check rows elimOK (by decide) (by decide) cover8157 (by decide)
  decide +kernel

theorem c8157_5 : P.sumLeaves 24 8353628 128 = 54146450 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8157) (lo := 860) (len := 128) (W := 54146450) check rows elimOK (by decide) (by decide) cover8157 (by decide)
  decide +kernel

theorem c8157_6 : P.sumLeaves 24 8353756 36 = 47995260 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8157) (lo := 988) (len := 36) (W := 47995260) check rows elimOK (by decide) (by decide) cover8157 (by decide)
  decide +kernel

theorem h8157 : P.leaf 34 8157 = 159731294 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(256, 0), (64, 0), (64, 0), (271, 27624151), (205, 29965433), (128, 54146450), (36, 47995260)]) (.cons c8157_0 (.cons c8157_1 (.cons c8157_2 (.cons c8157_3 (.cons c8157_4 (.cons c8157_5 (.cons c8157_6 (.nil)))))))) (by decide) (by decide))

theorem cover8159 : P.CoversSplit 24 10 8159 0xfffffffff5f5a0a0fffffffff5f5a0a0fffffffff5f5a0a0fffffffff5f5a0a0ccffccff80008000cc00cc0080008000ccffccff80008000cc00cc0080008000fffffffff5f5a0a0fffffffff5f5a0a0ffffffffa0a0a0a0ffffffffa0a0a0a0ccffccff80008000cc00cc0080008000cc00cc0080008000cc00cc0080008000 :=
  coversProjected check rows (by decide) (by decide) (xs := [516, 916, 1202, 1209, 1210, 1217, 1258, 1259, 1601, 1609]) (ps := [(8, [1609], [1266]), (14, [1217], [1266])]) (by decide +kernel)

noncomputable def f8159 (i : ℕ) := rowWeight keep5 twice5 i * P.leaf 24 (8354816 + i)

theorem c8159_0 : rowSum f8159 0 402 = 19187370 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 8159) (keep := keep5) (twice := twice5) check rows elimOK (by decide) (by decide) cover8159 (by decide)
  decide +kernel

theorem c8159_1 : rowSum f8159 402 285 = 120609810 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 8159) (keep := keep5) (twice := twice5) check rows elimOK (by decide) (by decide) cover8159 (by decide)
  decide +kernel

theorem c8159_2 : rowSum f8159 687 337 = 181819157 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 8159) (keep := keep5) (twice := twice5) check rows elimOK (by decide) (by decide) cover8159 (by decide)
  decide +kernel

theorem sum8159 : rowSum f8159 0 1024 = 321616337 :=
  rowSum_append (F := f8159) (lo := 0) (n := 402) (m := 622) (A := 19187370) (B := 302428967) c8159_0 (rowSum_append (F := f8159) (lo := 402) (n := 285) (m := 337) (A := 120609810) (B := 181819157) c8159_1 (c8159_2))

theorem h8159 : P.leaf 34 8159 = 321616337 :=
  leaf_weighted (k := 24) (d := 10) (H := 8159) (keep := keep5) (twice := twice5) rows (by decide) (by decide) bal5 (invRow5 (H := 8159) (by decide) (by decide +kernel)) sum8159

theorem cover8162 : P.CoversSplit 24 10 8162 0xaaaa0000abab0a0a0000000000000000aaaa0000abab0a0a00000000000000000000000000000000000000000000000000000000000000000000000000000000aaaa0000abab0a0a0000000000000000aaaa0000aaaa0a0a00000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 515, 522, 523, 565, 916, 1217, 1258, 1259, 1264]) (by decide +kernel)

theorem c8162_0 : P.sumLeaves 24 8357888 1024 = 4513270 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8162) (lo := 0) (len := 1024) (W := 4513270) check rows elimOK (by decide) (by decide) cover8162 (by decide)
  decide +kernel

theorem h8162 : P.leaf 34 8162 = 4513270 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 4513270)]) (.cons c8162_0 (.nil)) (by decide) (by decide))

theorem cover8163 : P.CoversSplit 24 10 8163 0xfffffffffefeaaaa0000000000000000fffffffffefeaaaa00000000000000000000000000000000000000000000000000000000000000000000000000000000fffffffffefeaaaa0000000000000000fffffffffafaaaaa00000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 522, 523, 916, 1209, 1210, 1217, 1258, 1259, 1264]) (by decide +kernel)

theorem c8163_0 : P.sumLeaves 24 8358912 502 = 11731645 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8163) (lo := 0) (len := 502) (W := 11731645) check rows elimOK (by decide) (by decide) cover8163 (by decide)
  decide +kernel

theorem c8163_1 : P.sumLeaves 24 8359414 500 = 35718180 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8163) (lo := 502) (len := 500) (W := 35718180) check rows elimOK (by decide) (by decide) cover8163 (by decide)
  decide +kernel

theorem c8163_2 : P.sumLeaves 24 8359914 22 = 23183866 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8163) (lo := 1002) (len := 22) (W := 23183866) check rows elimOK (by decide) (by decide) cover8163 (by decide)
  decide +kernel

theorem h8163 : P.leaf 34 8163 = 70633691 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(502, 11731645), (500, 35718180), (22, 23183866)]) (.cons c8163_0 (.cons c8163_1 (.cons c8163_2 (.nil)))) (by decide) (by decide))

theorem cover8164 : P.CoversSplit 24 10 8164 0x8888000088888888000000000000000088880000888888880000000000000000000000000000000000000000000000000000000000000000000000000000000088000000880088000000000000000000880000008800880000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 515, 522, 524, 566, 916, 1210, 1259]) (by decide +kernel)

theorem c8164_0 : P.sumLeaves 24 8359936 1024 = 3202160 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8164) (lo := 0) (len := 1024) (W := 3202160) check rows elimOK (by decide) (by decide) cover8164 (by decide)
  decide +kernel

theorem h8164 : P.leaf 34 8164 = 3202160 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 3202160)]) (.cons c8164_0 (.nil)) (by decide) (by decide))

theorem cover8165 : P.CoversSplit 24 10 8165 0xcccccccccccc88880000000000000000cccccccccccc888800000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00cc0088000000000000000000cc00cc00c800880000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 515, 522, 524, 566, 916, 1209, 1210, 1217, 1259]) (by decide +kernel)

theorem c8165_0 : P.sumLeaves 24 8360960 1024 = 33690424 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8165) (lo := 0) (len := 1024) (W := 33690424) check rows elimOK (by decide) (by decide) cover8165 (by decide)
  decide +kernel

theorem h8165 : P.leaf 34 8165 = 33690424 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 33690424)]) (.cons c8165_0 (.nil)) (by decide) (by decide))

theorem cover8166 : P.CoversSplit 24 10 8166 0xaaaa0000abab0a0a0000000000000000aaaa0000abab0a0a00000000000000000000000000000000000000000000000000000000000000000000000000000000aaaa0000abab0a0a0000000000000000aaaa0000aaaa0a0a00000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 515, 522, 524, 566, 1217, 1258, 1259, 1264]) (by decide +kernel)

theorem c8166_0 : P.sumLeaves 24 8361984 1024 = 47134573 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8166) (lo := 0) (len := 1024) (W := 47134573) check rows elimOK (by decide) (by decide) cover8166 (by decide)
  decide +kernel

theorem h8166 : P.leaf 34 8166 = 47134573 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 47134573)]) (.cons c8166_0 (.nil)) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(8155, 24), (8156, 24), (8157, 48), (8159, 24), (8162, 24), (8163, 48), (8164, 48), (8165, 48), (8166, 48)]

theorem segOK : checkSeg 16 perms 8155 8167 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 8155 8167 336 26657476440 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 26657476440)
    (SegSum.cons (w := 24) h8155 (SegSum.cons (w := 24) h8156 (SegSum.cons (w := 48) h8157 (SegSum.cons (w := 24) h8159 (SegSum.cons (w := 24) h8162 (SegSum.cons (w := 48) h8163 (SegSum.cons (w := 48) h8164 (SegSum.cons (w := 48) h8165 (SegSum.cons (w := 48) h8166 (show SegSum (P.leaf 34) [] 0 from rfl)))))))))) (by decide)

end RACert.S4N1.C0.S59
