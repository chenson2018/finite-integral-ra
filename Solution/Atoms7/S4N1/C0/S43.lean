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

namespace RACert.S4N1.C0.S43

open RACert RACert.Problem

theorem cover6895 : P.CoversSplit 24 10 6895 0xffff0000000000000000000000000000ffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 522, 573, 879, 916, 1202, 1209, 1210, 1251, 1259, 1264, 1308]) (by decide +kernel)

theorem c6895_0 : P.sumLeaves 24 7060480 448 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6895) (lo := 0) (len := 448) (W := 0) check rows elimOK (by decide) (by decide) cover6895 (by decide)
  decide +kernel

theorem contract6895_1 : P.leaf 30 110327 = 227680 := by
  exact leaf_contract_factors (k := 30) (b := 20) (H := 110327) (ss := [(18, 1, 524), (27, 1, 573), (29, 1, 916), (14, 1, 923), (8, 1, 580), (30, 1, 1251), (31, 1, 1210), (16, 1, 1265), (20, 1, 1657), (21, 1, 1658)]) (ids := [0, 1, 2, 3, 4, 7, 8, 9, 10, 11, 13, 15, 17, 20, 21, 24, 26, 5, 22, 23]) (cs := [2, 3, 4, 5, 6, 19, 1, 7, 8, 9, 10, 11, 1, 12, 1, 13, 1, 14, 1, 1, 15, 16, 20, 21, 17, 1, 18, 1, 1, 1]) (bs := [17, 3]) (W := 227680) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c6895_1 : P.sumLeaves 24 7060928 64 = 227680 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 110327) rows (by decide) (by decide)).symm.trans contract6895_1

theorem c6895_2 : P.sumLeaves 24 7060992 512 = 12218856 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6895) (lo := 512) (len := 512) (W := 12218856) check rows elimOK (by decide) (by decide) cover6895 (by decide)
  decide +kernel

theorem h6895 : P.leaf 34 6895 = 12446536 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(448, 0), (64, 227680), (512, 12218856)]) (.cons c6895_0 (.cons c6895_1 (.cons c6895_2 (.nil)))) (by decide) (by decide))

theorem cover6900 : P.CoversSplit 24 10 6900 0xffffffffa8a800000000000000000000f0f0f0f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 475, 573, 859, 879, 1202, 1210, 1259, 1264]) (ps := [(2, [465, 479], [466]), (14, [880], [859])]) (by decide +kernel)

theorem c6900_0 : P.sumLeaves 24 7065600 1024 = 1535580 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6900) (lo := 0) (len := 1024) (W := 1535580) check rows elimOK (by decide) (by decide) cover6900 (by decide)
  decide +kernel

theorem h6900 : P.leaf 34 6900 = 1535580 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1535580)]) (.cons c6900_0 (.nil)) (by decide) (by decide))

theorem cover6901 : P.CoversSplit 24 10 6901 0xffffffffafaf00000000000000000000ffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 475, 573, 859, 879, 1202, 1209, 1210, 1259, 1264]) (by decide +kernel)

theorem c6901_0 : P.sumLeaves 24 7066624 1024 = 8054696 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6901) (lo := 0) (len := 1024) (W := 8054696) check rows elimOK (by decide) (by decide) cover6901 (by decide)
  decide +kernel

theorem h6901 : P.leaf 34 6901 = 8054696 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 8054696)]) (.cons c6901_0 (.nil)) (by decide) (by decide))

theorem cover6902 : P.CoversSplit 24 10 6902 0xffffffffafaf00000000000000000000f0f0f0f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc008c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 475, 573, 859, 916, 1202, 1209, 1210, 1259, 1264, 1308]) (ps := [(14, [880], [859])]) (by decide +kernel)

theorem c6902_0 : P.sumLeaves 24 7067648 1024 = 6524040 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6902) (lo := 0) (len := 1024) (W := 6524040) check rows elimOK (by decide) (by decide) cover6902 (by decide)
  decide +kernel

theorem h6902 : P.leaf 34 6902 = 6524040 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 6524040)]) (.cons c6902_0 (.nil)) (by decide) (by decide))

theorem cover6903 : P.CoversSplit 24 10 6903 0xffffffffafaf00000000000000000000ffffffffafaf000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc008c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [475, 573, 859, 916, 1202, 1209, 1210, 1217, 1259, 1264, 1308]) (by decide +kernel)

theorem c6903_0 : P.sumLeaves 24 7068672 1021 = 16553594 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6903) (lo := 0) (len := 1021) (W := 16553594) check rows elimOK (by decide) (by decide) cover6903 (by decide)
  decide +kernel

theorem c6903_1 : P.sumLeaves 24 7069693 3 = 1710868 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6903) (lo := 1021) (len := 3) (W := 1710868) check rows elimOK (by decide) (by decide) cover6903 (by decide)
  decide +kernel

theorem h6903 : P.leaf 34 6903 = 18264462 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1021, 16553594), (3, 1710868)]) (.cons c6903_0 (.cons c6903_1 (.nil))) (by decide) (by decide))

theorem cover6904 : P.CoversSplit 24 10 6904 0xffffffffa8a800000000000000000000f0f0f4f4000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 487, 859, 879, 916, 1202, 1210, 1259, 1264]) (ps := [(2, [465, 467], [466])]) (by decide +kernel)

theorem c6904_0 : P.sumLeaves 24 7069696 1024 = 1008218 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6904) (lo := 0) (len := 1024) (W := 1008218) check rows elimOK (by decide) (by decide) cover6904 (by decide)
  decide +kernel

theorem h6904 : P.leaf 34 6904 = 1008218 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1008218)]) (.cons c6904_0 (.nil)) (by decide) (by decide))

theorem cover6905 : P.CoversSplit 24 10 6905 0xffffffffafaf00000000000000000000ffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 487, 859, 879, 916, 1202, 1209, 1210, 1259, 1264]) (by decide +kernel)

theorem c6905_0 : P.sumLeaves 24 7070720 1024 = 13008168 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6905) (lo := 0) (len := 1024) (W := 13008168) check rows elimOK (by decide) (by decide) cover6905 (by decide)
  decide +kernel

theorem h6905 : P.leaf 34 6905 = 13008168 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 13008168)]) (.cons c6905_0 (.nil)) (by decide) (by decide))

theorem cover6906 : P.CoversSplit 24 10 6906 0xffffffffafaf00000000000000000000f0f0f5f50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc008c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 487, 573, 859, 916, 1202, 1209, 1210, 1259, 1264, 1308]) (by decide +kernel)

theorem c6906_0 : P.sumLeaves 24 7071744 1024 = 10163050 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6906) (lo := 0) (len := 1024) (W := 10163050) check rows elimOK (by decide) (by decide) cover6906 (by decide)
  decide +kernel

theorem h6906 : P.leaf 34 6906 = 10163050 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 10163050)]) (.cons c6906_0 (.nil)) (by decide) (by decide))

theorem cover6907 : P.CoversSplit 24 10 6907 0xffffffffafaf00000000000000000000ffffffffafaf000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc008c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [487, 573, 859, 916, 1202, 1209, 1210, 1217, 1259, 1264, 1308]) (by decide +kernel)

theorem c6907_0 : P.sumLeaves 24 7072768 1021 = 23581952 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6907) (lo := 0) (len := 1021) (W := 23581952) check rows elimOK (by decide) (by decide) cover6907 (by decide)
  decide +kernel

theorem c6907_1 : P.sumLeaves 24 7073789 3 = 2714296 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6907) (lo := 1021) (len := 3) (W := 2714296) check rows elimOK (by decide) (by decide) cover6907 (by decide)
  decide +kernel

theorem h6907 : P.leaf 34 6907 = 26296248 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1021, 23581952), (3, 2714296)]) (.cons c6907_0 (.cons c6907_1 (.nil))) (by decide) (by decide))

theorem cover6908 : P.CoversSplit 24 10 6908 0xffffffffa8a800000000000000000000f0f0f5f50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00880000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 573, 859, 879, 916, 1202, 1210, 1259, 1264, 1308]) (ps := [(2, [465], [466])]) (by decide +kernel)

theorem c6908_0 : P.sumLeaves 24 7073792 1024 = 11812900 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6908) (lo := 0) (len := 1024) (W := 11812900) check rows elimOK (by decide) (by decide) cover6908 (by decide)
  decide +kernel

theorem h6908 : P.leaf 34 6908 = 11812900 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 11812900)]) (.cons c6908_0 (.nil)) (by decide) (by decide))

theorem cover6909 : P.CoversSplit 24 10 6909 0xffffffffafaf00000000000000000000ffffffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc008c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 573, 859, 879, 916, 1202, 1209, 1210, 1259, 1264, 1308]) (by decide +kernel)

theorem c6909_0 : P.sumLeaves 24 7074816 1024 = 22772084 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6909) (lo := 0) (len := 1024) (W := 22772084) check rows elimOK (by decide) (by decide) cover6909 (by decide)
  decide +kernel

theorem h6909 : P.leaf 34 6909 = 22772084 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 22772084)]) (.cons c6909_0 (.nil)) (by decide) (by decide))

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

theorem cover6963 : P.CoversSplit 24 10 6963 0xffffffffa5a5a0a0ffffffffa5a5a0a0ffffffff00000000ffffffff00000000cc33cc3380008000cc00cc0080008000cc33cc3300000000cc00cc0000000000ffffffffa5a5a0a0ffffffffa5a5a0a0ffffffffa5a5a0a0ffffffffa5a5a0a000000000000000000000000000000000cc33cc3380008000cc00cc0080008000 :=
  coversProjected check rows (by decide) (by decide) (xs := [517, 572, 859, 916, 1202, 1209, 1217, 1258, 1259, 1601, 1609]) (ps := [(8, [531, 586], [1217, 1609])]) (by decide +kernel)

noncomputable def f6963 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (7130112 + i)

theorem c6963_0 : rowSum f6963 0 437 = 776440 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 6963) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover6963 (by decide)
  decide +kernel

theorem c6963_1 : rowSum f6963 437 511 = 3362628 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 6963) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover6963 (by decide)
  decide +kernel

theorem c6963_2 : rowSum f6963 948 76 = 5056016 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 6963) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover6963 (by decide)
  decide +kernel

theorem sum6963 : rowSum f6963 0 1024 = 9195084 :=
  rowSum_append (F := f6963) (lo := 0) (n := 437) (m := 587) (A := 776440) (B := 8418644) c6963_0 (rowSum_append (F := f6963) (lo := 437) (n := 511) (m := 76) (A := 3362628) (B := 5056016) c6963_1 (c6963_2))

theorem h6963 : P.leaf 34 6963 = 9195084 :=
  leaf_weighted (k := 24) (d := 10) (H := 6963) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 6963) (by decide) (by decide +kernel)) sum6963

theorem cover6964 : P.CoversSplit 24 10 6964 0xfca9fca9a0a0a0a0fca9fca9a0a0a0a0a0a0a0a000000000a0a0a0a000000000cc00cc0080008000cc00cc008000800080008000000000008000800000000000cc00cc0080008000cc21cc21802080208000cc00000000008020cc21000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 508, 517, 529, 572, 859, 916, 1202, 1258, 1259, 1601]) (ps := [(8, [475, 531], [517]), (14, [880], [859])]) (by decide +kernel)

noncomputable def f6964 (i : ℕ) := rowWeight keep3 twice3 i * P.leaf 24 (7131136 + i)

theorem c6964_0 : rowSum f6964 0 1003 = 514778 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 6964) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover6964 (by decide)
  decide +kernel

theorem c6964_1 : rowSum f6964 1003 21 = 283888 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 6964) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover6964 (by decide)
  decide +kernel

theorem sum6964 : rowSum f6964 0 1024 = 798666 :=
  rowSum_append (F := f6964) (lo := 0) (n := 1003) (m := 21) (A := 514778) (B := 283888) c6964_0 (c6964_1)

theorem h6964 : P.leaf 34 6964 = 798666 :=
  leaf_weighted (k := 24) (d := 10) (H := 6964) (keep := keep3) (twice := twice3) rows (by decide) (by decide) bal3 (invRow3 (H := 6964) (by decide) (by decide +kernel)) sum6964

theorem cover6965 : P.CoversSplit 24 10 6965 0xffffffffa5a5a0a0ffffffffa5a5a0a0ffffffff00000000ffffffff00000000cc33cc3380008000cc00cc0080008000cc33cc3300000000cc00cc0000000000cc00cc0084008000cc33cc3384218020cc00cc0000000000cc33cc33000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 517, 529, 572, 859, 916, 1202, 1209, 1258, 1259, 1601]) (by decide +kernel)

noncomputable def f6965 (i : ℕ) := rowWeight keep3 twice3 i * P.leaf 24 (7132160 + i)

theorem c6965_0 : rowSum f6965 0 817 = 1651823 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 6965) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover6965 (by decide)
  decide +kernel

theorem c6965_1 : rowSum f6965 817 207 = 5940230 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 6965) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover6965 (by decide)
  decide +kernel

theorem sum6965 : rowSum f6965 0 1024 = 7592053 :=
  rowSum_append (F := f6965) (lo := 0) (n := 817) (m := 207) (A := 1651823) (B := 5940230) c6965_0 (c6965_1)

theorem h6965 : P.leaf 34 6965 = 7592053 :=
  leaf_weighted (k := 24) (d := 10) (H := 6965) (keep := keep3) (twice := twice3) rows (by decide) (by decide) bal3 (invRow3 (H := 6965) (by decide) (by decide +kernel)) sum6965

def seg : List (ℕ × ℕ) := [(6895, 48), (6900, 48), (6901, 48), (6902, 48), (6903, 48), (6904, 48), (6905, 48), (6906, 48), (6907, 48), (6908, 48), (6909, 48), (6910, 48), (6911, 48), (6963, 6), (6964, 24), (6965, 24)]

theorem segOK : checkSeg 16 perms 6895 6966 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 6895 6966 678 9895607376 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 9895607376)
    (SegSum.cons (w := 48) h6895 (SegSum.cons (w := 48) h6900 (SegSum.cons (w := 48) h6901 (SegSum.cons (w := 48) h6902 (SegSum.cons (w := 48) h6903 (SegSum.cons (w := 48) h6904 (SegSum.cons (w := 48) h6905 (SegSum.cons (w := 48) h6906 (SegSum.cons (w := 48) h6907 (SegSum.cons (w := 48) h6908 (SegSum.cons (w := 48) h6909 (SegSum.cons (w := 48) h6910 (SegSum.cons (w := 48) h6911 (SegSum.cons (w := 6) h6963 (SegSum.cons (w := 24) h6964 (SegSum.cons (w := 24) h6965 (show SegSum (P.leaf 34) [] 0 from rfl))))))))))))))))) (by decide)

end RACert.S4N1.C0.S43
