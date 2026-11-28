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

namespace RACert.S4N1.C0.S51

open RACert RACert.Problem

theorem cover28067 : P.CoversSplit 24 10 28067 0xaa000000aa0000000000000000000000aa000000000000000000000000000000aa000000aa0000000000000000000000aa000000000000000000000000000000aa000000aa0000000000000000000000aa0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [466, 515, 517, 522, 858, 865, 1202, 1210, 1259, 1601]) (by decide +kernel)

noncomputable def f28067 (i : ℕ) := rowWeight keep5 twice5 i * P.leaf 24 (28740608 + i)

theorem c28067_0 : rowSum f28067 0 1024 = 6248328 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 28067) (keep := keep5) (twice := twice5) check rows elimOK (by decide) (by decide) cover28067 (by decide)
  decide +kernel

theorem sum28067 : rowSum f28067 0 1024 = 6248328 :=
  c28067_0

theorem h28067 : P.leaf 34 28067 = 6248328 :=
  leaf_weighted (k := 24) (d := 10) (H := 28067) (keep := keep5) (twice := twice5) rows (by decide) (by decide) (bal5) (invRow5 (H := 28067) (by decide) (by decide +kernel)) sum28067

theorem h8148 : P.leaf 34 8148 = 6248328 :=
  orient32 (v := 28067) (by decide) (by decide +kernel) h28067

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

def k8151 : ℕ := 0x8aef000000000000ffff8aef0000000000000000000000000000000000000000ffffffff8aef0000ffffffffffff8aef00000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8aef0000ffffffffffff8aef
def t8151 : ℕ := 0x8ae000000000000ffff08ae0000000000000000000000000000000000000000ffffffff08ae0000ffffffffffff08ae00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff0000000008ae000000000000ffff08ae

noncomputable def f8151 (i : ℕ) := rowWeight k8151 t8151 i * P.leaf 24 (8346624 + i)

theorem c8151_0 : rowSum f8151 0 256 = 2665840 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 8151) (keep := k8151) (twice := t8151) check rows elimOK (by decide) (by decide) cover8151 (by decide)
  decide +kernel

theorem contract8151_1 : P.leaf 30 130420 = 0 := by
  exact leaf_contract_zero (ss := [(8, 0, 1266), (31, 1, 615), (14, 0, 1266), (5, 1, 433), (21, 1, 482), (20, 1, 488), (9, 7, 629), (12, 1, 825), (15, 13, 972)]) (q := 1272) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c8151_1 : rowSum f8151 256 64 = 0 :=
  (rowSum_unit_block (P := P) (keep := k8151) (twice := t8151) (by decide +kernel)).trans ((leaf_eq_inner (k := 24) (d := 6) (H := 130420) rows (by decide) (by decide)).symm.trans contract8151_1)

theorem contract8151_2 : P.leaf 30 130421 = 0 := by
  exact leaf_contract_zero (ss := [(8, 0, 1266), (31, 1, 615), (14, 0, 1266), (5, 1, 433), (21, 1, 482), (20, 1, 488), (9, 7, 629), (12, 1, 825), (15, 13, 972)]) (q := 1272) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c8151_2 : rowSum f8151 320 64 = 0 :=
  (rowSum_unit_block (P := P) (keep := k8151) (twice := t8151) (by decide +kernel)).trans ((leaf_eq_inner (k := 24) (d := 6) (H := 130421) rows (by decide) (by decide)).symm.trans contract8151_2)

theorem c8151_3 : rowSum f8151 384 271 = 89615640 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 8151) (keep := k8151) (twice := t8151) check rows elimOK (by decide) (by decide) cover8151 (by decide)
  decide +kernel

theorem c8151_4 : rowSum f8151 655 369 = 130272874 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 8151) (keep := k8151) (twice := t8151) check rows elimOK (by decide) (by decide) cover8151 (by decide)
  decide +kernel

theorem sum8151 : rowSum f8151 0 1024 = 222554354 :=
  rowSum_append (F := f8151) (lo := 0) (n := 256) (m := 768) (A := 2665840) (B := 219888514) c8151_0 (rowSum_append (F := f8151) (lo := 256) (n := 64) (m := 704) (A := 0) (B := 219888514) c8151_1 (rowSum_append (F := f8151) (lo := 320) (n := 64) (m := 640) (A := 0) (B := 219888514) c8151_2 (rowSum_append (F := f8151) (lo := 384) (n := 271) (m := 369) (A := 89615640) (B := 130272874) c8151_3 (c8151_4))))

theorem h8151 : P.leaf 34 8151 = 222554354 :=
  leaf_weighted (k := 24) (d := 10) (H := 8151) (keep := k8151) (twice := t8151) rows (by decide) (by decide) (balancedRows_of_check (by decide +kernel)) (invRow5 (H := 8151) (by decide) (by decide +kernel)) sum8151

theorem cover44451 : P.CoversSplit 24 10 44451 0xfffffffff0f0a0a0ffff0000f0f00000ffff000000000000ffff000000000000cccccccc80008000cc00000080000000cccc000040000000cc00000000000000fffffffff0f0a0a00000000000000000ffff55550000000000ff0000000000000000000000800000000000000000000000000000004000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [466, 515, 517, 522, 858, 865, 915, 1202, 1209, 1258, 1601]) (ps := [(16, [615], [1251]), (19, [965], [1264])]) (by decide +kernel)

noncomputable def f44451 (i : ℕ) := rowWeight keep5 twice5 i * P.leaf 24 (45517824 + i)

theorem c44451_0 : rowSum f44451 0 954 = 6054217 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 44451) (keep := keep5) (twice := twice5) check rows elimOK (by decide) (by decide) cover44451 (by decide)
  decide +kernel

theorem c44451_1 : rowSum f44451 954 70 = 4040760 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 44451) (keep := keep5) (twice := twice5) check rows elimOK (by decide) (by decide) cover44451 (by decide)
  decide +kernel

theorem sum44451 : rowSum f44451 0 1024 = 10094977 :=
  rowSum_append (F := f44451) (lo := 0) (n := 954) (m := 70) (A := 6054217) (B := 4040760) c44451_0 (c44451_1)

theorem h44451 : P.leaf 34 44451 = 10094977 :=
  leaf_weighted (k := 24) (d := 10) (H := 44451) (keep := keep5) (twice := twice5) rows (by decide) (by decide) (bal5) (invRow5 (H := 44451) (by decide) (by decide +kernel)) sum44451

theorem h8152 : P.leaf 34 8152 = 10094977 :=
  orient32 (v := 44451) (by decide) (by decide +kernel) h44451

theorem cover52047 : P.CoversSplit 24 10 52047 0xfffffffffa000000fffffffffa0000008c8c8c8c080000008c8c8c8c08000000ffccffccfa00000033003300320000008c8c8c8c08000000000000000000000088aa88aa8800000088aa88aa88000000888888880800000088888888080000000080008000000000000000000000000000880088000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [515, 516, 522, 523, 565, 572, 859, 879, 915, 1202, 1601]) (ps := [(14, [929], [866])]) (by decide +kernel)

theorem c52047_0 : P.sumLeaves 24 53296128 758 = 7260799 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 52047) (lo := 0) (len := 758) (W := 7260799) check rows elimOK (by decide) (by decide) cover52047 (by decide)
  decide +kernel

theorem c52047_1 : P.sumLeaves 24 53296886 250 = 20167470 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 52047) (lo := 758) (len := 250) (W := 20167470) check rows elimOK (by decide) (by decide) cover52047 (by decide)
  decide +kernel

theorem c52047_2 : P.sumLeaves 24 53297136 16 = 5367000 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 52047) (lo := 1008) (len := 16) (W := 5367000) check rows elimOK (by decide) (by decide) cover52047 (by decide)
  decide +kernel

theorem h52047 : P.leaf 34 52047 = 32795269 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(758, 7260799), (250, 20167470), (16, 5367000)]) (.cons c52047_0 (.cons c52047_1 (.cons c52047_2 (.nil)))) (by decide) (by decide))

theorem h8153 : P.leaf 34 8153 = 32795269 :=
  orient5 (v := 52047) (by decide) (by decide +kernel) h52047

theorem cover44979 : P.CoversSplit 24 10 44979 0xfffffffff0f0a0a0fffffffff0f0a0a0fffffffff0f0a0a0fffffffff0f0a0a0cccccccc80008000cc00cc0080008000cccccccc80008000cc00cc0080008000fffffffff0f0a0a0fffffffff0f0a0a0ffffffff00000000ffffffff00000000cccccccc80008000cc00cc008000800000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [517, 915, 1202, 1209, 1258, 1601]) (ps := [(8, [615, 1609], [1272]), (14, [965], [1272])]) (by decide +kernel)

def k44979 : ℕ := 0x8aef000000000000ffff8aef0000000000000000000000000000000000000000ffffffff8aef0000ffffffffffff8aef00000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8aef0000ffffffffffff8aef
def t44979 : ℕ := 0x8ae000000000000ffff08ae0000000000000000000000000000000000000000ffffffff08ae0000ffffffffffff08ae00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff0000000008ae000000000000ffff08ae

noncomputable def f44979 (i : ℕ) := rowWeight k44979 t44979 i * P.leaf 24 (46058496 + i)

theorem c44979_0 : rowSum f44979 0 256 = 1577178 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 44979) (keep := k44979) (twice := t44979) check rows elimOK (by decide) (by decide) cover44979 (by decide)
  decide +kernel

theorem contract44979_1 : P.leaf 30 719668 = 0 := by
  exact leaf_contract_zero (ss := [(8, 0, 1272), (6, 1, 488), (14, 1, 488), (9, 1, 482)]) (q := 531) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c44979_1 : rowSum f44979 256 64 = 0 :=
  (rowSum_unit_block (P := P) (keep := k44979) (twice := t44979) (by decide +kernel)).trans ((leaf_eq_inner (k := 24) (d := 6) (H := 719668) rows (by decide) (by decide)).symm.trans contract44979_1)

theorem contract44979_2 : P.leaf 30 719669 = 0 := by
  exact leaf_contract_zero (ss := [(8, 0, 1272), (6, 1, 488), (14, 1, 488), (9, 1, 482)]) (q := 531) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c44979_2 : rowSum f44979 320 64 = 0 :=
  (rowSum_unit_block (P := P) (keep := k44979) (twice := t44979) (by decide +kernel)).trans ((leaf_eq_inner (k := 24) (d := 6) (H := 719669) rows (by decide) (by decide)).symm.trans contract44979_2)

theorem c44979_3 : rowSum f44979 384 318 = 39909512 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 44979) (keep := k44979) (twice := t44979) check rows elimOK (by decide) (by decide) cover44979 (by decide)
  decide +kernel

theorem c44979_4 : rowSum f44979 702 322 = 49071006 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 44979) (keep := k44979) (twice := t44979) check rows elimOK (by decide) (by decide) cover44979 (by decide)
  decide +kernel

theorem sum44979 : rowSum f44979 0 1024 = 90557696 :=
  rowSum_append (F := f44979) (lo := 0) (n := 256) (m := 768) (A := 1577178) (B := 88980518) c44979_0 (rowSum_append (F := f44979) (lo := 256) (n := 64) (m := 704) (A := 0) (B := 88980518) c44979_1 (rowSum_append (F := f44979) (lo := 320) (n := 64) (m := 640) (A := 0) (B := 88980518) c44979_2 (rowSum_append (F := f44979) (lo := 384) (n := 318) (m := 322) (A := 39909512) (B := 49071006) c44979_3 (c44979_4))))

theorem h44979 : P.leaf 34 44979 = 90557696 :=
  leaf_weighted (k := 24) (d := 10) (H := 44979) (keep := k44979) (twice := t44979) rows (by decide) (by decide) (balancedRows_of_check (by decide +kernel)) (invRow5 (H := 44979) (by decide) (by decide +kernel)) sum44979

theorem h8155 : P.leaf 34 8155 = 90557696 :=
  orient32 (v := 44979) (by decide) (by decide +kernel) h44979

theorem cover8156 : P.CoversSplit 24 10 8156 0xfffffffff0a0a0a0fffffffff0a0a0a0aaaaafaf00000000aaaaafaf00000000cc88cc8880008000cc00cc008000800088888c880000000088008c0000000000ff00ff00f000a000ff33ff33f020a020aa00af0000000000aa22af23000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 516, 916, 1202, 1210, 1259, 1601]) (ps := [(2, [473], [472]), (6, [465], [472])]) (by decide +kernel)

def k8156 : ℕ := 0x8aef000000000000ffff8aef0000000000000000000000000000000000000000ffffffff8aef0000ffffffffffff8aef00000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8aef0000ffffffffffff8aef
def t8156 : ℕ := 0x8ae000000000000ffff08ae0000000000000000000000000000000000000000ffffffff08ae0000ffffffffffff08ae00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff0000000008ae000000000000ffff08ae

noncomputable def f8156 (i : ℕ) := rowWeight k8156 t8156 i * P.leaf 24 (8351744 + i)

theorem c8156_0 : rowSum f8156 0 256 = 0 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 8156) (keep := k8156) (twice := t8156) check rows elimOK (by decide) (by decide) cover8156 (by decide)
  decide +kernel

theorem contract8156_1 : P.leaf 30 130500 = 0 := by
  exact leaf_contract_zero (ss := [(8, 0, 1266), (20, 1, 531), (21, 1, 537), (14, 0, 1266), (5, 1, 433), (9, 7, 629), (12, 1, 825), (15, 13, 972), (31, 1, 1217)]) (q := 1272) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c8156_1 : rowSum f8156 256 64 = 0 :=
  (rowSum_unit_block (P := P) (keep := k8156) (twice := t8156) (by decide +kernel)).trans ((leaf_eq_inner (k := 24) (d := 6) (H := 130500) rows (by decide) (by decide)).symm.trans contract8156_1)

theorem contract8156_2 : P.leaf 30 130501 = 0 := by
  exact leaf_contract_zero (ss := [(29, 1, 916), (8, 0, 1266), (20, 1, 531), (21, 1, 537), (14, 0, 1266), (5, 1, 433), (9, 7, 629), (12, 1, 825), (15, 13, 972), (31, 1, 1217)]) (q := 1272) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c8156_2 : rowSum f8156 320 64 = 0 :=
  (rowSum_unit_block (P := P) (keep := k8156) (twice := t8156) (by decide +kernel)).trans ((leaf_eq_inner (k := 24) (d := 6) (H := 130501) rows (by decide) (by decide)).symm.trans contract8156_2)

theorem c8156_3 : rowSum f8156 384 569 = 37893478 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 8156) (keep := k8156) (twice := t8156) check rows elimOK (by decide) (by decide) cover8156 (by decide)
  decide +kernel

theorem c8156_4 : rowSum f8156 953 71 = 27363120 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 8156) (keep := k8156) (twice := t8156) check rows elimOK (by decide) (by decide) cover8156 (by decide)
  decide +kernel

theorem sum8156 : rowSum f8156 0 1024 = 65256598 :=
  rowSum_append (F := f8156) (lo := 0) (n := 256) (m := 768) (A := 0) (B := 65256598) c8156_0 (rowSum_append (F := f8156) (lo := 256) (n := 64) (m := 704) (A := 0) (B := 65256598) c8156_1 (rowSum_append (F := f8156) (lo := 320) (n := 64) (m := 640) (A := 0) (B := 65256598) c8156_2 (rowSum_append (F := f8156) (lo := 384) (n := 569) (m := 71) (A := 37893478) (B := 27363120) c8156_3 (c8156_4))))

theorem h8156 : P.leaf 34 8156 = 65256598 :=
  leaf_weighted (k := 24) (d := 10) (H := 8156) (keep := k8156) (twice := t8156) rows (by decide) (by decide) (balancedRows_of_check (by decide +kernel)) (invRow5 (H := 8156) (by decide) (by decide +kernel)) sum8156

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

def seg : List (ℕ × ℕ) := [(8148, 24), (8149, 48), (8151, 24), (8152, 24), (8153, 48), (8155, 24), (8156, 24), (8157, 48)]

theorem segOK : checkSeg 16 perms 8148 8159 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 8148 8159 264 23112493272 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 23112493272)
    (SegSum.cons (w := 24) h8148 (SegSum.cons (w := 48) h8149 (SegSum.cons (w := 24) h8151 (SegSum.cons (w := 24) h8152 (SegSum.cons (w := 48) h8153 (SegSum.cons (w := 24) h8155 (SegSum.cons (w := 24) h8156 (SegSum.cons (w := 48) h8157 (show SegSum (P.leaf 34) [] 0 from rfl))))))))) (by decide)

end RACert.S4N1.C0.S51
