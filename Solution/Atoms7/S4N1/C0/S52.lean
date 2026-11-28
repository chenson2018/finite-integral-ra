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

namespace RACert.S4N1.C0.S52

open RACert RACert.Problem

theorem cover8159 : P.CoversSplit 24 10 8159 0xfffffffff5f5a0a0fffffffff5f5a0a0fffffffff5f5a0a0fffffffff5f5a0a0ccffccff80008000cc00cc0080008000ccffccff80008000cc00cc0080008000fffffffff5f5a0a0fffffffff5f5a0a0ffffffffa0a0a0a0ffffffffa0a0a0a0ccffccff80008000cc00cc0080008000cc00cc0080008000cc00cc0080008000 :=
  coversProjected check rows (by decide) (by decide) (xs := [516, 916, 1202, 1209, 1210, 1217, 1258, 1259, 1601, 1609]) (ps := [(8, [1609], [1266]), (14, [1217], [1266])]) (by decide +kernel)

def k8159 : ℕ := 0x8aef000000000000ffff8aef0000000000000000000000000000000000000000ffffffff8aef0000ffffffffffff8aef00000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def t8159 : ℕ := 0x8ae000000000000ffff08ae0000000000000000000000000000000000000000ffffffff08ae0000ffffffffffff08ae00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000

noncomputable def f8159 (i : ℕ) := rowWeight k8159 t8159 i * P.leaf 24 (8354816 + i)

theorem contract8159_0 : P.leaf 30 130544 = 0 := by
  exact leaf_contract_zero (ss := [(3, 1, 536), (29, 1, 1259), (8, 0, 1266), (5, 1, 622), (14, 0, 1266), (20, 1, 531), (21, 1, 537), (9, 7, 629), (12, 1, 825), (15, 13, 972), (31, 1, 1217)]) (q := 1272) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c8159_0 : rowSum f8159 0 64 = 0 :=
  (rowSum_unit_block (P := P) (keep := k8159) (twice := t8159) (by decide +kernel)).trans ((leaf_eq_inner (k := 24) (d := 6) (H := 130544) rows (by decide) (by decide)).symm.trans contract8159_0)

theorem contract8159_1 : P.leaf 30 130545 = 0 := by
  exact leaf_contract_zero (ss := [(3, 1, 536), (8, 0, 1266), (5, 1, 622), (14, 0, 1266), (20, 1, 531), (21, 1, 537), (9, 7, 629), (12, 1, 825), (15, 13, 972), (31, 1, 1217)]) (q := 1272) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c8159_1 : rowSum f8159 64 64 = 0 :=
  (rowSum_unit_block (P := P) (keep := k8159) (twice := t8159) (by decide +kernel)).trans ((leaf_eq_inner (k := 24) (d := 6) (H := 130545) rows (by decide) (by decide)).symm.trans contract8159_1)

theorem c8159_2 : rowSum f8159 128 128 = 16923132 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 8159) (keep := k8159) (twice := t8159) check rows elimOK (by decide) (by decide) cover8159 (by decide)
  decide +kernel

theorem contract8159_3 : P.leaf 30 130548 = 0 := by
  exact leaf_contract_zero (ss := [(8, 0, 1266), (14, 0, 1266), (5, 1, 433), (20, 1, 531), (21, 1, 537), (9, 7, 629), (12, 1, 825), (15, 13, 972), (31, 1, 1217)]) (q := 1272) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c8159_3 : rowSum f8159 256 64 = 0 :=
  (rowSum_unit_block (P := P) (keep := k8159) (twice := t8159) (by decide +kernel)).trans ((leaf_eq_inner (k := 24) (d := 6) (H := 130548) rows (by decide) (by decide)).symm.trans contract8159_3)

theorem contract8159_4 : P.leaf 30 130549 = 0 := by
  exact leaf_contract_zero (ss := [(8, 0, 1266), (14, 0, 1266), (5, 1, 433), (20, 1, 531), (21, 1, 537), (9, 7, 629), (12, 1, 825), (15, 13, 972), (31, 1, 1217)]) (q := 1272) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c8159_4 : rowSum f8159 320 64 = 0 :=
  (rowSum_unit_block (P := P) (keep := k8159) (twice := t8159) (by decide +kernel)).trans ((leaf_eq_inner (k := 24) (d := 6) (H := 130549) rows (by decide) (by decide)).symm.trans contract8159_4)

theorem c8159_5 : rowSum f8159 384 271 = 117804292 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 8159) (keep := k8159) (twice := t8159) check rows elimOK (by decide) (by decide) cover8159 (by decide)
  decide +kernel

theorem c8159_6 : rowSum f8159 655 369 = 186888913 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 8159) (keep := k8159) (twice := t8159) check rows elimOK (by decide) (by decide) cover8159 (by decide)
  decide +kernel

theorem sum8159 : rowSum f8159 0 1024 = 321616337 :=
  rowSum_append (F := f8159) (lo := 0) (n := 64) (m := 960) (A := 0) (B := 321616337) c8159_0 (rowSum_append (F := f8159) (lo := 64) (n := 64) (m := 896) (A := 0) (B := 321616337) c8159_1 (rowSum_append (F := f8159) (lo := 128) (n := 128) (m := 768) (A := 16923132) (B := 304693205) c8159_2 (rowSum_append (F := f8159) (lo := 256) (n := 64) (m := 704) (A := 0) (B := 304693205) c8159_3 (rowSum_append (F := f8159) (lo := 320) (n := 64) (m := 640) (A := 0) (B := 304693205) c8159_4 (rowSum_append (F := f8159) (lo := 384) (n := 271) (m := 369) (A := 117804292) (B := 186888913) c8159_5 (c8159_6))))))

theorem h8159 : P.leaf 34 8159 = 321616337 :=
  leaf_weighted (k := 24) (d := 10) (H := 8159) (keep := k8159) (twice := t8159) rows (by decide) (by decide) (balancedRows_of_check (by decide +kernel)) (invRow5 (H := 8159) (by decide) (by decide +kernel)) sum8159

theorem cover20380 : P.CoversSplit 24 10 20380 0xaa00aa0000000000aa00aa0000000000aa00aa0000000000aa00aa00000000000000000000000000000000000000000000000000000000000000000000000000aa00aa0000000000aa00aa0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 472, 473, 516, 528, 916, 921]) (ps := [(8, [531], [1266])]) (by decide +kernel)

noncomputable def f20380 (i : ℕ) := rowWeight keep5 twice5 i * P.leaf 24 (20869120 + i)

theorem c20380_0 : rowSum f20380 0 1024 = 4513270 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 20380) (keep := keep5) (twice := twice5) check rows elimOK (by decide) (by decide) cover20380 (by decide)
  decide +kernel

theorem sum20380 : rowSum f20380 0 1024 = 4513270 :=
  c20380_0

theorem h20380 : P.leaf 34 20380 = 4513270 :=
  leaf_weighted (k := 24) (d := 10) (H := 20380) (keep := keep5) (twice := twice5) rows (by decide) (by decide) (bal5) (invRow5 (H := 20380) (by decide) (by decide +kernel)) sum20380

theorem h8162 : P.leaf 34 8162 = 4513270 :=
  orient4 (v := 20380) (by decide) (by decide +kernel) h20380

theorem cover20381 : P.CoversSplit 24 10 20381 0xff00ff00f000aa00ff00ff00f000aa00ff00ff00f000aa00ff00ff00f000aa000000000000000000000000000000000000000000000000000000000000000000ff00ff00f000aa00ff00ff00f000aa00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 516, 916, 921, 1202, 1210, 1308]) (ps := [(14, [923], [1266])]) (by decide +kernel)

theorem c20381_0 : P.sumLeaves 24 20870144 905 = 31690801 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 20381) (lo := 0) (len := 905) (W := 31690801) check rows elimOK (by decide) (by decide) cover20381 (by decide)
  decide +kernel

theorem c20381_1 : P.sumLeaves 24 20871049 119 = 38942890 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 20381) (lo := 905) (len := 119) (W := 38942890) check rows elimOK (by decide) (by decide) cover20381 (by decide)
  decide +kernel

theorem h20381 : P.leaf 34 20381 = 70633691 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(905, 31690801), (119, 38942890)]) (.cons c20381_0 (.cons c20381_1 (.nil))) (by decide) (by decide))

theorem h8163 : P.leaf 34 8163 = 70633691 :=
  orient4 (v := 20381) (by decide) (by decide +kernel) h20381

theorem cover20396 : P.CoversSplit 24 10 20396 0x8800000088008000880000008800800088000000000000008800000000000000000000000000000000000000000000000000000000000000000000000000000088000000880080000000000000000000880000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 472, 473, 515, 517, 522, 916, 1202, 1259]) (by decide +kernel)

theorem h20396 : P.leaf 34 20396 = 3202160 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 20396) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 20396) (weight := fun _ => 1) (xs := [379, 383, 463, 475, 479, 507, 511, 827, 831, 891, 895, 911, 923, 927, 955, 959, 975, 987, 991, 1019, 1023]) check rows elimOK (by decide) (by decide) cover20396 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h8164 : P.leaf 34 8164 = 3202160 :=
  orient4 (v := 20396) (by decide) (by decide +kernel) h20396

theorem cover52527 : P.CoversSplit 24 10 52527 0xff00fa00fe00f0000000000000000000ff00fa00fe00f0000000000000000000000000000000000000000000000000000000000000000000000000000000000088008800880080000000000000000000880088008800800000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 522, 529, 572, 858, 865, 915, 921, 1202]) (by decide +kernel)

theorem c52527_0 : P.sumLeaves 24 53787648 1024 = 33690424 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 52527) (lo := 0) (len := 1024) (W := 33690424) check rows elimOK (by decide) (by decide) cover52527 (by decide)
  decide +kernel

theorem h52527 : P.leaf 34 52527 = 33690424 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 33690424)]) (.cons c52527_0 (.nil)) (by decide) (by decide))

theorem h8165 : P.leaf 34 8165 = 33690424 :=
  orient5 (v := 52527) (by decide) (by decide +kernel) h52527

theorem cover8166 : P.CoversSplit 24 10 8166 0xaaaa0000abab0a0a0000000000000000aaaa0000abab0a0a00000000000000000000000000000000000000000000000000000000000000000000000000000000aaaa0000abab0a0a0000000000000000aaaa0000aaaa0a0a00000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 515, 522, 524, 566, 1217, 1258, 1259, 1264]) (by decide +kernel)

theorem c8166_0 : P.sumLeaves 24 8361984 1024 = 47134573 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8166) (lo := 0) (len := 1024) (W := 47134573) check rows elimOK (by decide) (by decide) cover8166 (by decide)
  decide +kernel

theorem h8166 : P.leaf 34 8166 = 47134573 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 47134573)]) (.cons c8166_0 (.nil)) (by decide) (by decide))

theorem cover20413 : P.CoversSplit 24 10 20413 0xff00ff00fa00a000ff00ff00fa00a000ff00ff00fa00a000ff00ff00fa00a0000000000000000000000000000000000000000000000000000000000000000000ff00ff00fa00a000ff00ff00fa00a000ff00ff00fa00a000ff00ff00fa00a0000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 517, 916, 921, 1202, 1210]) (by decide +kernel)

theorem c20413_0 : P.sumLeaves 24 20902912 781 = 38843794 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 20413) (lo := 0) (len := 781) (W := 38843794) check rows elimOK (by decide) (by decide) cover20413 (by decide)
  decide +kernel

theorem c20413_1 : P.sumLeaves 24 20903693 243 = 122826265 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 20413) (lo := 781) (len := 243) (W := 122826265) check rows elimOK (by decide) (by decide) cover20413 (by decide)
  decide +kernel

theorem h20413 : P.leaf 34 20413 = 161670059 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(781, 38843794), (243, 122826265)]) (.cons c20413_0 (.cons c20413_1 (.nil))) (by decide) (by decide))

theorem h8167 : P.leaf 34 8167 = 161670059 :=
  orient4 (v := 20413) (by decide) (by decide +kernel) h20413

theorem cover20428 : P.CoversSplit 24 10 20428 0x8800880080008000880088008000800088008800000000008800880000000000000000000000000000000000000000000000000000000000000000000000000088008800800080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 472, 473, 516, 522, 916, 1202, 1259]) (ps := [(14, [923], [1266])]) (by decide +kernel)

theorem h20428 : P.leaf 34 20428 = 2979408 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 20428) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 20428) (weight := fun _ => 1) (xs := [463, 479, 491, 495, 507, 511, 811, 815, 827, 831, 875, 879, 891, 895, 911, 927, 939, 943, 955, 959, 975, 991, 1003, 1007, 1019, 1023]) check rows elimOK (by decide) (by decide) cover20428 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h8168 : P.leaf 34 8168 = 2979408 :=
  orient4 (v := 20428) (by decide) (by decide +kernel) h20428

theorem cover20429 : P.CoversSplit 24 10 20429 0xcc00cc00c0008000cc00cc00c0008000cc00cc00c0008000cc00cc00c00080000000000000000000000000000000000000000000000000000000000000000000cc00cc00c00080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 515, 522, 916, 921, 1202, 1259, 1308]) (ps := [(14, [923], [1266])]) (by decide +kernel)

theorem c20429_0 : P.sumLeaves 24 20919296 1024 = 23120980 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 20429) (lo := 0) (len := 1024) (W := 23120980) check rows elimOK (by decide) (by decide) cover20429 (by decide)
  decide +kernel

theorem h20429 : P.leaf 34 20429 = 23120980 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 23120980)]) (.cons c20429_0 (.nil)) (by decide) (by decide))

theorem h8169 : P.leaf 34 8169 = 23120980 :=
  orient4 (v := 20429) (by decide) (by decide +kernel) h20429

theorem cover8170 : P.CoversSplit 24 10 8170 0xaaaa0000abab0a0a0000000000000000aaaa0000abab0a0a00000000000000000000000000000000000000000000000000000000000000000000000000000000aaaa0000abab0a0a0000000000000000aaaa0000aaaa0a0a00000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 515, 522, 523, 565, 916, 1217, 1258, 1259, 1264]) (by decide +kernel)

theorem c8170_0 : P.sumLeaves 24 8366080 1024 = 23802297 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8170) (lo := 0) (len := 1024) (W := 23802297) check rows elimOK (by decide) (by decide) cover8170 (by decide)
  decide +kernel

theorem h8170 : P.leaf 34 8170 = 23802297 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 23802297)]) (.cons c8170_0 (.nil)) (by decide) (by decide))

theorem cover20445 : P.CoversSplit 24 10 20445 0xff00ff00f000a000ff00ff00f000a000ff00ff00f000a000ff00ff00f000a0000000000000000000000000000000000000000000000000000000000000000000ff00ff00f000a000ff00ff00f000a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 516, 916, 921, 1202, 1210, 1308]) (ps := [(14, [923], [1266])]) (by decide +kernel)

theorem c20445_0 : P.sumLeaves 24 20935680 938 = 48572739 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 20445) (lo := 0) (len := 938) (W := 48572739) check rows elimOK (by decide) (by decide) cover20445 (by decide)
  decide +kernel

theorem c20445_1 : P.sumLeaves 24 20936618 86 = 48785864 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 20445) (lo := 938) (len := 86) (W := 48785864) check rows elimOK (by decide) (by decide) cover20445 (by decide)
  decide +kernel

theorem h20445 : P.leaf 34 20445 = 97358603 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(938, 48572739), (86, 48785864)]) (.cons c20445_0 (.cons c20445_1 (.nil))) (by decide) (by decide))

theorem h8171 : P.leaf 34 8171 = 97358603 :=
  orient4 (v := 20445) (by decide) (by decide +kernel) h20445

theorem cover8172 : P.CoversSplit 24 10 8172 0x8888000088888888000000000000000088880000888888880000000000000000000000000000000000000000000000000000000000000000000000000000000088000000880088000000000000000000880000008800880000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 515, 522, 916, 1210, 1259]) (by decide +kernel)

theorem c8172_0 : P.sumLeaves 24 8368128 1024 = 11556010 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8172) (lo := 0) (len := 1024) (W := 11556010) check rows elimOK (by decide) (by decide) cover8172 (by decide)
  decide +kernel

theorem h8172 : P.leaf 34 8172 = 11556010 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 11556010)]) (.cons c8172_0 (.nil)) (by decide) (by decide))

theorem cover20461 : P.CoversSplit 24 10 20461 0xcc00cc00c8008800cc00cc00c8008800cc00cc00c8008800cc00cc00c80088000000000000000000000000000000000000000000000000000000000000000000cc00cc00c80088000000000000000000cc00cc00c800880000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 515, 522, 916, 921, 1202, 1259]) (by decide +kernel)

theorem c20461_0 : P.sumLeaves 24 20952064 1024 = 53952794 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 20461) (lo := 0) (len := 1024) (W := 53952794) check rows elimOK (by decide) (by decide) cover20461 (by decide)
  decide +kernel

theorem h20461 : P.leaf 34 20461 = 53952794 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 53952794)]) (.cons c20461_0 (.nil)) (by decide) (by decide))

theorem h8173 : P.leaf 34 8173 = 53952794 :=
  orient4 (v := 20461) (by decide) (by decide +kernel) h20461

theorem cover8174 : P.CoversSplit 24 10 8174 0xaaaa0000abab0a0a0000000000000000aaaa0000abab0a0a00000000000000000000000000000000000000000000000000000000000000000000000000000000aaaa0000abab0a0a0000000000000000aaaa0000aaaa0a0a00000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 515, 522, 1217, 1258, 1259, 1264]) (by decide +kernel)

theorem c8174_0 : P.sumLeaves 24 8370176 1024 = 81205089 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8174) (lo := 0) (len := 1024) (W := 81205089) check rows elimOK (by decide) (by decide) cover8174 (by decide)
  decide +kernel

theorem h8174 : P.leaf 34 8174 = 81205089 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 81205089)]) (.cons c8174_0 (.nil)) (by decide) (by decide))

theorem cover20477 : P.CoversSplit 24 10 20477 0xff00ff00fa00aa00ff00ff00fa00aa00ff00ff00fa00aa00ff00ff00fa00aa000000000000000000000000000000000000000000000000000000000000000000ff00ff00fa00aa00ff00ff00fa00aa00ff00ff00fa00aa00ff00ff00fa00aa000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 916, 921, 1202, 1210]) (by decide +kernel)

theorem c20477_0 : P.sumLeaves 24 20968448 504 = 43739879 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 20477) (lo := 0) (len := 504) (W := 43739879) check rows elimOK (by decide) (by decide) cover20477 (by decide)
  decide +kernel

theorem c20477_1 : P.sumLeaves 24 20968952 496 = 138746008 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 20477) (lo := 504) (len := 496) (W := 138746008) check rows elimOK (by decide) (by decide) cover20477 (by decide)
  decide +kernel

theorem c20477_2 : P.sumLeaves 24 20969448 24 = 45443504 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 20477) (lo := 1000) (len := 24) (W := 45443504) check rows elimOK (by decide) (by decide) cover20477 (by decide)
  decide +kernel

theorem h20477 : P.leaf 34 20477 = 227929391 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(504, 43739879), (496, 138746008), (24, 45443504)]) (.cons c20477_0 (.cons c20477_1 (.cons c20477_2 (.nil)))) (by decide) (by decide))

theorem h8175 : P.leaf 34 8175 = 227929391 :=
  orient4 (v := 20477) (by decide) (by decide +kernel) h20477

def seg : List (ℕ × ℕ) := [(8159, 24), (8162, 24), (8163, 48), (8164, 48), (8165, 48), (8166, 48), (8167, 48), (8168, 48), (8169, 48), (8170, 48), (8171, 48), (8172, 48), (8173, 48), (8174, 48), (8175, 48)]

theorem segOK : checkSeg 16 perms 8159 8179 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 8159 8179 672 48062413560 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 48062413560)
    (SegSum.cons (w := 24) h8159 (SegSum.cons (w := 24) h8162 (SegSum.cons (w := 48) h8163 (SegSum.cons (w := 48) h8164 (SegSum.cons (w := 48) h8165 (SegSum.cons (w := 48) h8166 (SegSum.cons (w := 48) h8167 (SegSum.cons (w := 48) h8168 (SegSum.cons (w := 48) h8169 (SegSum.cons (w := 48) h8170 (SegSum.cons (w := 48) h8171 (SegSum.cons (w := 48) h8172 (SegSum.cons (w := 48) h8173 (SegSum.cons (w := 48) h8174 (SegSum.cons (w := 48) h8175 (show SegSum (P.leaf 34) [] 0 from rfl)))))))))))))))) (by decide)

end RACert.S4N1.C0.S52
