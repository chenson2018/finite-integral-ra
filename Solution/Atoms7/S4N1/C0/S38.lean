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

theorem cover6893 : P.CoversSplit 24 10 6893 0xcccc0000000000000000000000000000cccc00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 515, 522, 573, 879, 916, 1202, 1209, 1210, 1251, 1259, 1308]) (by decide +kernel)

theorem h6893 : P.leaf 34 6893 = 3498400 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 6893) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 6893) (weight := fun _ => 1) (xs := [506, 507, 510, 511, 882, 883, 886, 887, 890, 891, 894, 895, 1010, 1011, 1014, 1015, 1018, 1019, 1022, 1023]) check rows elimOK (by decide) (by decide) cover6893 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover6894 : P.CoversSplit 24 10 6894 0xaaaa0000000000000000000000000000a0a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000088000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 515, 522, 573, 859, 879, 916, 1210, 1251, 1259, 1264, 1308]) (by decide +kernel)

theorem h6894 : P.leaf 34 6894 = 3433432 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 6894) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 6894) (weight := fun _ => 1) (xs := [507, 511, 885, 887, 893, 895, 1009, 1011, 1013, 1015, 1017, 1019, 1021, 1023]) check rows elimOK (by decide) (by decide) cover6894 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover6895 : P.CoversSplit 24 10 6895 0xffff0000000000000000000000000000ffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 522, 573, 879, 916, 1202, 1209, 1210, 1251, 1259, 1264, 1308]) (by decide +kernel)

theorem c6895_0 : P.sumLeaves 24 7060480 1024 = 12446536 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6895) (lo := 0) (len := 1024) (W := 12446536) check rows elimOK (by decide) (by decide) cover6895 (by decide)
  decide +kernel

theorem h6895 : P.leaf 34 6895 = 12446536 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 12446536)]) (.cons c6895_0 (.nil)) (by decide) (by decide))

theorem cover18094 : P.CoversSplit 24 10 18094 0xaa000000aa000000aa000000aa00000088000000000000008800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 515, 517, 522, 524, 566, 573, 872, 916, 921, 1202, 1217]) (by decide +kernel)

theorem h18094 : P.leaf 34 18094 = 1535580 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 18094) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 18094) (weight := fun _ => 1) (xs := [827, 831, 891, 895, 921, 923, 925, 927, 953, 955, 957, 959, 985, 987, 989, 991, 1017, 1019, 1021, 1023]) check rows elimOK (by decide) (by decide) cover18094 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h6900 : P.leaf 34 6900 = 1535580 :=
  orient4 (v := 18094) (by decide) (by decide +kernel) h18094

theorem cover18095 : P.CoversSplit 24 10 18095 0xff00ff00fa000000ff00ff00fa0000008c008c00000000008c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 517, 522, 524, 566, 573, 860, 872, 916, 921, 1202, 1217, 1251]) (by decide +kernel)

theorem c18095_0 : P.sumLeaves 24 18529280 1024 = 8054696 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 18095) (lo := 0) (len := 1024) (W := 8054696) check rows elimOK (by decide) (by decide) cover18095 (by decide)
  decide +kernel

theorem h18095 : P.leaf 34 18095 = 8054696 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 8054696)]) (.cons c18095_0 (.nil)) (by decide) (by decide))

theorem h6901 : P.leaf 34 6901 = 8054696 :=
  orient4 (v := 18095) (by decide) (by decide +kernel) h18095

theorem cover36662 : P.CoversSplit 24 10 36662 0xff00ff00f0000000ff00ff00f0000000aa00aa0000000000aa00aa00000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 480, 517, 572, 915, 921, 1202, 1209, 1258]) (ps := [(8, [531], [517]), (14, [510, 965], [1272])]) (by decide +kernel)

theorem c36662_0 : P.sumLeaves 24 37541888 1024 = 6524040 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 36662) (lo := 0) (len := 1024) (W := 6524040) check rows elimOK (by decide) (by decide) cover36662 (by decide)
  decide +kernel

theorem h36662 : P.leaf 34 36662 = 6524040 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 6524040)]) (.cons c36662_0 (.nil)) (by decide) (by decide))

theorem h6902 : P.leaf 34 6902 = 6524040 :=
  orient5 (v := 36662) (by decide) (by decide +kernel) h36662

theorem cover18111 : P.CoversSplit 24 10 18111 0xff00ff00fa000000ff00ff00fa000000ff00ff0000000000ff000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00c80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [517, 524, 566, 573, 872, 916, 921, 1202, 1217, 1251, 1259]) (ps := [(14, [958, 965], [1217, 1266])]) (by decide +kernel)

theorem c18111_0 : P.sumLeaves 24 18545664 1024 = 18264462 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 18111) (lo := 0) (len := 1024) (W := 18264462) check rows elimOK (by decide) (by decide) cover18111 (by decide)
  decide +kernel

theorem h18111 : P.leaf 34 18111 = 18264462 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 18264462)]) (.cons c18111_0 (.nil)) (by decide) (by decide))

theorem h6903 : P.leaf 34 6903 = 18264462 :=
  orient4 (v := 18111) (by decide) (by decide +kernel) h18111

theorem cover18126 : P.CoversSplit 24 10 18126 0xa000a000a0000000a000a000a0000000a000a00000000000a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 515, 516, 522, 536, 916, 921, 1202, 1210, 1251]) (by decide +kernel)

theorem h18126 : P.leaf 34 18126 = 1008218 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 18126) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 18126) (weight := fun _ => 1) (xs := [829, 831, 877, 879, 893, 895, 925, 927, 941, 943, 957, 959, 989, 991, 1005, 1007, 1021, 1023]) check rows elimOK (by decide) (by decide) cover18126 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h6904 : P.leaf 34 6904 = 1008218 :=
  orient4 (v := 18126) (by decide) (by decide +kernel) h18126

theorem cover18127 : P.CoversSplit 24 10 18127 0xff00ff00f0000000ff00ff00f0000000ff00ff0000000000ff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 522, 536, 860, 916, 921, 1202, 1210, 1217, 1251]) (by decide +kernel)

theorem c18127_0 : P.sumLeaves 24 18562048 1024 = 13008168 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 18127) (lo := 0) (len := 1024) (W := 13008168) check rows elimOK (by decide) (by decide) cover18127 (by decide)
  decide +kernel

theorem h18127 : P.leaf 34 18127 = 13008168 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 13008168)]) (.cons c18127_0 (.nil)) (by decide) (by decide))

theorem h6905 : P.leaf 34 6905 = 13008168 :=
  orient4 (v := 18127) (by decide) (by decide +kernel) h18127

theorem cover18142 : P.CoversSplit 24 10 18142 0xff00ff00f0000000ff00ff00f0000000aa00af0000000000aa00af00000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 516, 536, 573, 860, 916, 921, 1202, 1210, 1259]) (ps := [(14, [965], [1266])]) (by decide +kernel)

theorem c18142_0 : P.sumLeaves 24 18577408 1024 = 10163050 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 18142) (lo := 0) (len := 1024) (W := 10163050) check rows elimOK (by decide) (by decide) cover18142 (by decide)
  decide +kernel

theorem h18142 : P.leaf 34 18142 = 10163050 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 10163050)]) (.cons c18142_0 (.nil)) (by decide) (by decide))

theorem h6906 : P.leaf 34 6906 = 10163050 :=
  orient4 (v := 18142) (by decide) (by decide +kernel) h18142

theorem cover18143 : P.CoversSplit 24 10 18143 0xff00ff00f0000000ff00ff00f0000000ff00ff0000000000ff00ff00000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [516, 536, 573, 860, 916, 921, 1202, 1210, 1217, 1259, 1308]) (ps := [(14, [965], [1266])]) (by decide +kernel)

theorem c18143_0 : P.sumLeaves 24 18578432 1024 = 26296248 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 18143) (lo := 0) (len := 1024) (W := 26296248) check rows elimOK (by decide) (by decide) cover18143 (by decide)
  decide +kernel

theorem h18143 : P.leaf 34 18143 = 26296248 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 26296248)]) (.cons c18143_0 (.nil)) (by decide) (by decide))

theorem h6907 : P.leaf 34 6907 = 26296248 :=
  orient4 (v := 18143) (by decide) (by decide +kernel) h18143

theorem cover6908 : P.CoversSplit 24 10 6908 0xffffffffa8a800000000000000000000f0f0f5f50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00880000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 573, 859, 879, 916, 1202, 1210, 1259, 1264, 1308]) (ps := [(2, [465], [466])]) (by decide +kernel)

theorem c6908_0 : P.sumLeaves 24 7073792 1024 = 11812900 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6908) (lo := 0) (len := 1024) (W := 11812900) check rows elimOK (by decide) (by decide) cover6908 (by decide)
  decide +kernel

theorem h6908 : P.leaf 34 6908 = 11812900 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 11812900)]) (.cons c6908_0 (.nil)) (by decide) (by decide))

theorem cover18159 : P.CoversSplit 24 10 18159 0xff00ff00fa000000ff00ff00fa000000ff00ff00fa000000ff000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00c80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [515, 522, 573, 860, 916, 921, 1202, 1210, 1251, 1259]) (ps := [(14, [965], [1266])]) (by decide +kernel)

theorem c18159_0 : P.sumLeaves 24 18594816 1024 = 22772084 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 18159) (lo := 0) (len := 1024) (W := 22772084) check rows elimOK (by decide) (by decide) cover18159 (by decide)
  decide +kernel

theorem h18159 : P.leaf 34 18159 = 22772084 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 22772084)]) (.cons c18159_0 (.nil)) (by decide) (by decide))

theorem h6909 : P.leaf 34 6909 = 22772084 :=
  orient4 (v := 18159) (by decide) (by decide +kernel) h18159

theorem cover6910 : P.CoversSplit 24 10 6910 0xffffffffafaf00000000000000000000f0f0f5f50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc008c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 573, 859, 879, 916, 1202, 1209, 1210, 1259, 1264, 1308]) (by decide +kernel)

theorem c6910_0 : P.sumLeaves 24 7075840 1024 = 25797358 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6910) (lo := 0) (len := 1024) (W := 25797358) check rows elimOK (by decide) (by decide) cover6910 (by decide)
  decide +kernel

theorem h6910 : P.leaf 34 6910 = 25797358 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 25797358)]) (.cons c6910_0 (.nil)) (by decide) (by decide))

theorem cover6911 : P.CoversSplit 24 10 6911 0xffffffffafaf00000000000000000000ffffffffafaf000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc008c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [573, 859, 879, 916, 1202, 1209, 1210, 1217, 1259, 1264, 1308]) (by decide +kernel)

theorem c6911_0 : P.sumLeaves 24 7076864 1021 = 39643814 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6911) (lo := 0) (len := 1021) (W := 39643814) check rows elimOK (by decide) (by decide) cover6911 (by decide)
  decide +kernel

theorem c6911_1 : P.sumLeaves 24 7077885 3 = 3486588 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6911) (lo := 1021) (len := 3) (W := 3486588) check rows elimOK (by decide) (by decide) cover6911 (by decide)
  decide +kernel

theorem h6911 : P.leaf 34 6911 = 43130402 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1021, 39643814), (3, 3486588)]) (.cons c6911_0 (.cons c6911_1 (.nil))) (by decide) (by decide))

theorem cover18199 : P.CoversSplit 24 10 18199 0xfffffffff0000a00fffffffff0000a00ffffffff00000800ffff0000000000008888888880000800220022002000020088888888000008002200000000000000fffffffff0000a00ffff0000f0000000ffffffff00000000ffff0000000000000000000000000000200000002000000000000000800000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [516, 517, 523, 529, 572, 872, 909, 915, 1202, 1217, 1251, 1264, 1308, 1601, 1609]) (by decide +kernel)

def k18199 : ℕ := 0x8aef000000000000ffff8aef0000000000000000000000000000000000000000ffffffff8aef0000ffffffffffff8aef00000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8aef0000ffffffffffff8aef
def t18199 : ℕ := 0x8ae000000000000ffff08ae0000000000000000000000000000000000000000ffffffff08ae0000ffffffffffff08ae00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff0000000008ae000000000000ffff08ae

noncomputable def f18199 (i : ℕ) := rowWeight k18199 t18199 i * P.leaf 24 (18635776 + i)

theorem c18199_0 : rowSum f18199 0 256 = 1544 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 18199) (keep := k18199) (twice := t18199) check rows elimOK (by decide) (by decide) cover18199 (by decide)
  decide +kernel

theorem contract18199_1 : P.leaf 30 291188 = 0 := by
  exact leaf_contract_zero (ss := [(30, 1, 1251), (31, 1, 1251), (8, 0, 1266), (5, 1, 524), (14, 1, 531)]) (q := 586) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c18199_1 : rowSum f18199 256 64 = 0 :=
  (rowSum_unit_block (P := P) (keep := k18199) (twice := t18199) (by decide +kernel)).trans ((leaf_eq_inner (k := 24) (d := 6) (H := 291188) rows (by decide) (by decide)).symm.trans contract18199_1)

theorem contract18199_2 : P.leaf 30 291189 = 0 := by
  exact leaf_contract_zero (ss := [(8, 0, 1266), (14, 1, 531)]) (q := 586) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c18199_2 : rowSum f18199 320 64 = 0 :=
  (rowSum_unit_block (P := P) (keep := k18199) (twice := t18199) (by decide +kernel)).trans ((leaf_eq_inner (k := 24) (d := 6) (H := 291189) rows (by decide) (by decide)).symm.trans contract18199_2)

theorem c18199_3 : rowSum f18199 384 573 = 6421712 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 18199) (keep := k18199) (twice := t18199) check rows elimOK (by decide) (by decide) cover18199 (by decide)
  decide +kernel

theorem c18199_4 : rowSum f18199 957 67 = 2771828 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 18199) (keep := k18199) (twice := t18199) check rows elimOK (by decide) (by decide) cover18199 (by decide)
  decide +kernel

theorem sum18199 : rowSum f18199 0 1024 = 9195084 :=
  rowSum_append (F := f18199) (lo := 0) (n := 256) (m := 768) (A := 1544) (B := 9193540) c18199_0 (rowSum_append (F := f18199) (lo := 256) (n := 64) (m := 704) (A := 0) (B := 9193540) c18199_1 (rowSum_append (F := f18199) (lo := 320) (n := 64) (m := 640) (A := 0) (B := 9193540) c18199_2 (rowSum_append (F := f18199) (lo := 384) (n := 573) (m := 67) (A := 6421712) (B := 2771828) c18199_3 (c18199_4))))

theorem h18199 : P.leaf 34 18199 = 9195084 :=
  leaf_weighted (k := 24) (d := 10) (H := 18199) (keep := k18199) (twice := t18199) rows (by decide) (by decide) (balancedRows_of_check (by decide +kernel)) (invRow5 (H := 18199) (by decide) (by decide +kernel)) sum18199

theorem h6963 : P.leaf 34 6963 = 9195084 :=
  orient4 (v := 18199) (by decide) (by decide +kernel) h18199

theorem cover25795 : P.CoversSplit 24 10 25795 0xf0000000f00000000000000000000000f0000000000000000000000000000000f0000000f00000000000000000000000f0000000000000000000000000000000f0000000f00000000000000000000000f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [466, 515, 516, 522, 573, 858, 865, 1210, 1259]) (by decide +kernel)

noncomputable def f25795 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (26414080 + i)

theorem c25795_0 : rowSum f25795 0 1024 = 798666 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 25795) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover25795 (by decide)
  decide +kernel

theorem sum25795 : rowSum f25795 0 1024 = 798666 :=
  c25795_0

theorem h25795 : P.leaf 34 25795 = 798666 :=
  leaf_weighted (k := 24) (d := 10) (H := 25795) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 25795) (by decide) (by decide +kernel)) sum25795

theorem h6964 : P.leaf 34 6964 = 798666 :=
  orient32 (v := 25795) (by decide) (by decide +kernel) h25795

theorem cover25811 : P.CoversSplit 24 10 25811 0xfffffffff0f0a0a0fffffffff0f0a0a0ffff000000000000ffff000000000000ff00ff00f000a000cc00cc00c0008000ff00000000000000cc00000000000000fffffffff0f0a0a00000000000000000ffff0f0f0000000000ff0000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [516, 573, 858, 860, 865, 915, 1202, 1210, 1259, 1601]) (ps := [(17, [1251], [1259])]) (by decide +kernel)

noncomputable def f25811 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (26430464 + i)

theorem c25811_0 : rowSum f25811 0 933 = 3817481 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 25811) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover25811 (by decide)
  decide +kernel

theorem c25811_1 : rowSum f25811 933 91 = 3774572 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 25811) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover25811 (by decide)
  decide +kernel

theorem sum25811 : rowSum f25811 0 1024 = 7592053 :=
  rowSum_append (F := f25811) (lo := 0) (n := 933) (m := 91) (A := 3817481) (B := 3774572) c25811_0 (c25811_1)

theorem h25811 : P.leaf 34 25811 = 7592053 :=
  leaf_weighted (k := 24) (d := 10) (H := 25811) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 25811) (by decide) (by decide +kernel)) sum25811

theorem h6965 : P.leaf 34 6965 = 7592053 :=
  orient32 (v := 25811) (by decide) (by decide +kernel) h25811

theorem cover26307 : P.CoversSplit 24 10 26307 0xfffffffff0f0a0a0fffffffff0f0a0a0ffffffff00000000ffff000000000000ff00ff00f000a000cc00cc00c0008000ff00ff0000000000cc00000000000000fffffffff0f0a0a0ffff0000f0f00000ffffffff00000000ffff0000000000000000000000000000000000000000000000000000100000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [515, 516, 522, 573, 860, 915, 1202, 1217, 1251, 1259, 1264, 1308, 1601, 1609]) (ps := [(8, [524, 565, 615], [1217, 1609])]) (by decide +kernel)

noncomputable def f26307 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (26938368 + i)

theorem c26307_0 : rowSum f26307 0 670 = 5081900 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 26307) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover26307 (by decide)
  decide +kernel

theorem c26307_1 : rowSum f26307 670 354 = 6132622 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 26307) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover26307 (by decide)
  decide +kernel

theorem sum26307 : rowSum f26307 0 1024 = 11214522 :=
  rowSum_append (F := f26307) (lo := 0) (n := 670) (m := 354) (A := 5081900) (B := 6132622) c26307_0 (c26307_1)

theorem h26307 : P.leaf 34 26307 = 11214522 :=
  leaf_weighted (k := 24) (d := 10) (H := 26307) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 26307) (by decide) (by decide +kernel)) sum26307

theorem h6966 : P.leaf 34 6966 = 11214522 :=
  orient32 (v := 26307) (by decide) (by decide +kernel) h26307

theorem cover26323 : P.CoversSplit 24 10 26323 0xfffffffff0f0a0a0fffffffff0f0a0a0ffffffff00000000ffffffff00000000ff00ff00f000a000cc00cc00c0008000ff00ff0000000000cc00cc0000000000fffffffff0f0a0a0fffffffff0f0a0a0ffffffff00000000ffffffff000000000000000000000000000000000000000000000000100000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [516, 573, 860, 915, 1202, 1217, 1259, 1308, 1601, 1609]) (ps := [(8, [537, 580, 615], [1217, 1609])]) (by decide +kernel)

noncomputable def f26323 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (26954752 + i)

theorem c26323_0 : rowSum f26323 0 483 = 7375839 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 26323) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover26323 (by decide)
  decide +kernel

theorem c26323_1 : rowSum f26323 483 541 = 23248079 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 26323) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover26323 (by decide)
  decide +kernel

theorem sum26323 : rowSum f26323 0 1024 = 30623918 :=
  rowSum_append (F := f26323) (lo := 0) (n := 483) (m := 541) (A := 7375839) (B := 23248079) c26323_0 (c26323_1)

theorem h26323 : P.leaf 34 26323 = 30623918 :=
  leaf_weighted (k := 24) (d := 10) (H := 26323) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 26323) (by decide) (by decide +kernel)) sum26323

theorem h6967 : P.leaf 34 6967 = 30623918 :=
  orient32 (v := 26323) (by decide) (by decide +kernel) h26323

def seg : List (ℕ × ℕ) := [(6893, 48), (6894, 48), (6895, 48), (6900, 48), (6901, 48), (6902, 48), (6903, 48), (6904, 48), (6905, 48), (6906, 48), (6907, 48), (6908, 48), (6909, 48), (6910, 48), (6911, 48), (6963, 6), (6964, 24), (6965, 24), (6966, 24), (6967, 24)]

theorem segOK : checkSeg 16 perms 6893 6972 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 6893 6972 822 11232457872 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 11232457872)
    (SegSum.cons (w := 48) h6893 (SegSum.cons (w := 48) h6894 (SegSum.cons (w := 48) h6895 (SegSum.cons (w := 48) h6900 (SegSum.cons (w := 48) h6901 (SegSum.cons (w := 48) h6902 (SegSum.cons (w := 48) h6903 (SegSum.cons (w := 48) h6904 (SegSum.cons (w := 48) h6905 (SegSum.cons (w := 48) h6906 (SegSum.cons (w := 48) h6907 (SegSum.cons (w := 48) h6908 (SegSum.cons (w := 48) h6909 (SegSum.cons (w := 48) h6910 (SegSum.cons (w := 48) h6911 (SegSum.cons (w := 6) h6963 (SegSum.cons (w := 24) h6964 (SegSum.cons (w := 24) h6965 (SegSum.cons (w := 24) h6966 (SegSum.cons (w := 24) h6967 (show SegSum (P.leaf 34) [] 0 from rfl))))))))))))))))))))) (by decide)

end RACert.S4N1.C0.S38
