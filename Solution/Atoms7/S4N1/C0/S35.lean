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

namespace RACert.S4N1.C0.S35

open RACert RACert.Problem

theorem cover5983 : P.CoversSplit 24 10 5983 0xffffffffa0a0a0a0ffffffffa0a0a0a0ffffffff0000a0a0ffffffff0000a0a0cc00cc0080008000cc00cc0080008000cc00cc0000008000cc00cc0000008000ffffffffa0a0a0a0ffffffffa0a0a0a0ffffffffa0a0a0a0ffffffffa0a0a0a00000000000000000cc00cc0080008000cc00cc0080008000cc00cc0080008000 :=
  coversSplit check rows (by decide) (by decide) (xs := [516, 572, 1202, 1217, 1258, 1259, 1601, 1609]) (by decide +kernel)

noncomputable def f5983 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (6126592 + i)

theorem c5983_0 : rowSum f5983 0 439 = 3264258 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 5983) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover5983 (by decide)
  decide +kernel

theorem c5983_1 : rowSum f5983 439 572 = 43361005 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 5983) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover5983 (by decide)
  decide +kernel

theorem c5983_2 : rowSum f5983 1011 13 = 8864848 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 5983) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover5983 (by decide)
  decide +kernel

theorem sum5983 : rowSum f5983 0 1024 = 55490111 :=
  rowSum_append (F := f5983) (lo := 0) (n := 439) (m := 585) (A := 3264258) (B := 52225853) c5983_0 (rowSum_append (F := f5983) (lo := 439) (n := 572) (m := 13) (A := 43361005) (B := 8864848) c5983_1 (c5983_2))

theorem h5983 : P.leaf 34 5983 = 55490111 :=
  leaf_weighted (k := 24) (d := 10) (H := 5983) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 5983) (by decide) (by decide +kernel)) sum5983

theorem h5984 : P.leaf 34 5984 = 8320 := by
  exact leaf_contract_factors (k := 34) (b := 17) (H := 5984) (ss := [(27, 6, 466), (2, 1, 468), (6, 1, 472), (29, 1, 473), (15, 1, 487), (14, 1, 558), (30, 1, 1251), (26, 1, 515), (31, 1, 1251), (12, 1, 909), (5, 1, 411), (3, 1, 409), (4, 1, 410), (10, 1, 458), (11, 1, 459), (32, 1, 522), (34, 1, 1259)]) (ids := [5, 6, 7, 11, 14, 15, 16, 17, 18, 19, 21, 22, 26, 31, 33, 20, 23]) (cs := [1, 1, 1, 1, 1, 2, 3, 4, 1, 1, 1, 5, 1, 1, 6, 7, 8, 9, 10, 11, 17, 12, 13, 18, 1, 1, 14, 1, 1, 1, 1, 15, 1, 16]) (bs := [15, 2]) (W := 8320) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem cover5985 : P.CoversSplit 24 10 5985 0xcc000000000000000000000000000000cc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 515, 522, 523, 572, 860, 916, 1202, 1209, 1258, 1259]) (ps := [(14, [558], [1272])]) (by decide +kernel)

theorem c5985_0 : P.sumLeaves 24 6128640 448 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5985) (lo := 0) (len := 448) (W := 0) check rows elimOK (by decide) (by decide) cover5985 (by decide)
  decide +kernel

theorem contract5985_1 : P.leaf 30 95767 = 36232 := by
  exact leaf_contract_factors (k := 30) (b := 19) (H := 95767) (ss := [(27, 1, 473), (29, 1, 473), (6, 1, 474), (2, 1, 475), (12, 1, 478), (15, 1, 487), (30, 1, 523), (14, 1, 558), (18, 1, 923), (31, 1, 1209), (19, 1, 1272)]) (ids := [1, 2, 3, 5, 6, 7, 8, 9, 11, 14, 15, 18, 19, 20, 21, 22, 24, 26, 23]) (cs := [1, 2, 3, 4, 1, 5, 6, 7, 8, 9, 1, 10, 1, 1, 11, 12, 1, 1, 13, 14, 15, 16, 17, 20, 18, 1, 19, 1, 1, 1]) (bs := [18, 1]) (W := 36232) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c5985_1 : P.sumLeaves 24 6129088 64 = 36232 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 95767) rows (by decide) (by decide)).symm.trans contract5985_1

theorem c5985_2 : P.sumLeaves 24 6129152 320 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5985) (lo := 512) (len := 320) (W := 0) check rows elimOK (by decide) (by decide) cover5985 (by decide)
  decide +kernel

theorem contract5985_3 : P.leaf 30 95773 = 67144 := by
  exact leaf_contract_factors (k := 30) (b := 19) (H := 95773) (ss := [(27, 1, 473), (29, 1, 473), (6, 1, 474), (2, 1, 475), (12, 1, 478), (15, 1, 487), (30, 1, 523), (4, 1, 529), (14, 1, 558), (16, 1, 874), (31, 1, 909)]) (ids := [1, 3, 5, 6, 7, 8, 9, 11, 15, 16, 17, 18, 19, 20, 21, 22, 24, 26, 23]) (cs := [1, 2, 1, 3, 1, 4, 5, 6, 7, 8, 1, 9, 1, 1, 1, 10, 11, 12, 13, 14, 15, 16, 17, 20, 18, 1, 19, 1, 1, 1]) (bs := [18, 1]) (W := 67144) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c5985_3 : P.sumLeaves 24 6129472 64 = 67144 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 95773) rows (by decide) (by decide)).symm.trans contract5985_3

theorem c5985_4 : P.sumLeaves 24 6129536 128 = 112952 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5985) (lo := 896) (len := 128) (W := 112952) check rows elimOK (by decide) (by decide) cover5985 (by decide)
  decide +kernel

theorem h5985 : P.leaf 34 5985 = 216328 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(448, 0), (64, 36232), (320, 0), (64, 67144), (128, 112952)]) (.cons c5985_0 (.cons c5985_1 (.cons c5985_2 (.cons c5985_3 (.cons c5985_4 (.nil)))))) (by decide) (by decide))

theorem cover5986 : P.CoversSplit 24 10 5986 0xaaaa0000000000000000000000000000a0a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000aaaa0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 515, 522, 523, 565, 860, 916, 1209, 1251, 1259, 1264]) (ps := [(14, [874, 1266], [860, 1272])]) (by decide +kernel)

theorem c5986_0 : P.sumLeaves 24 6129664 448 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5986) (lo := 0) (len := 448) (W := 0) check rows elimOK (by decide) (by decide) cover5986 (by decide)
  decide +kernel

theorem contract5986_1 : P.leaf 30 95783 = 17152 := by
  exact leaf_contract_factors (k := 30) (b := 18) (H := 95783) (ss := [(2, 1, 453), (5, 1, 453), (3, 1, 409), (6, 1, 478), (12, 1, 460), (30, 19, 523), (19, 1, 529), (14, 1, 923), (8, 1, 586), (18, 1, 923), (31, 1, 1209), (26, 1, 515)]) (ids := [2, 5, 7, 8, 9, 11, 13, 14, 15, 18, 19, 21, 23, 25, 26, 27, 20, 22]) (cs := [1, 1, 2, 1, 1, 3, 1, 4, 5, 6, 1, 7, 1, 8, 9, 10, 1, 1, 11, 12, 18, 13, 19, 14, 1, 15, 16, 17, 1, 1]) (bs := [16, 2]) (W := 17152) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c5986_1 : P.sumLeaves 24 6130112 64 = 17152 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 95783) rows (by decide) (by decide)).symm.trans contract5986_1

theorem c5986_2 : P.sumLeaves 24 6130176 320 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5986) (lo := 512) (len := 320) (W := 0) check rows elimOK (by decide) (by decide) cover5986 (by decide)
  decide +kernel

theorem contract5986_3 : P.leaf 30 95789 = 19776 := by
  exact leaf_contract_factors (k := 30) (b := 18) (H := 95789) (ss := [(2, 1, 453), (5, 1, 453), (3, 1, 409), (6, 1, 478), (12, 1, 460), (30, 1, 523), (4, 1, 529), (14, 1, 874), (16, 1, 874), (31, 1, 1209), (26, 1, 515), (28, 1, 860)]) (ids := [5, 6, 7, 8, 9, 11, 13, 15, 16, 17, 18, 19, 21, 23, 25, 27, 20, 22]) (cs := [1, 1, 1, 1, 1, 2, 3, 4, 5, 6, 1, 7, 1, 8, 1, 9, 10, 11, 12, 13, 18, 14, 19, 15, 1, 16, 1, 17, 1, 1]) (bs := [16, 2]) (W := 19776) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c5986_3 : P.sumLeaves 24 6130496 64 = 19776 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 95789) rows (by decide) (by decide)).symm.trans contract5986_3

theorem c5986_4 : P.sumLeaves 24 6130560 128 = 66864 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5986) (lo := 896) (len := 128) (W := 66864) check rows elimOK (by decide) (by decide) cover5986 (by decide)
  decide +kernel

theorem h5986 : P.leaf 34 5986 = 103792 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(448, 0), (64, 17152), (320, 0), (64, 19776), (128, 66864)]) (.cons c5986_0 (.cons c5986_1 (.cons c5986_2 (.cons c5986_3 (.cons c5986_4 (.nil)))))) (by decide) (by decide))

theorem cover5987 : P.CoversSplit 24 10 5987 0xffff0000000000000000000000000000ffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [515, 522, 523, 572, 860, 916, 1202, 1209, 1259, 1264]) (ps := [(14, [1266], [1272])]) (by decide +kernel)

theorem c5987_0 : P.sumLeaves 24 6130688 1024 = 1864711 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5987) (lo := 0) (len := 1024) (W := 1864711) check rows elimOK (by decide) (by decide) cover5987 (by decide)
  decide +kernel

theorem h5987 : P.leaf 34 5987 = 1864711 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1864711)]) (.cons c5987_0 (.nil)) (by decide) (by decide))

theorem cover5988 : P.CoversSplit 24 10 5988 0x8800000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000088000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 515, 522, 524, 572, 860, 916, 1202, 1209, 1251, 1258, 1259]) (ps := [(14, [1266], [1272])]) (by decide +kernel)

theorem c5988_0 : P.sumLeaves 24 6131712 1024 = 102696 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5988) (lo := 0) (len := 1024) (W := 102696) check rows elimOK (by decide) (by decide) cover5988 (by decide)
  decide +kernel

theorem h5988 : P.leaf 34 5988 = 102696 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 102696)]) (.cons c5988_0 (.nil)) (by decide) (by decide))

theorem cover5989 : P.CoversSplit 24 10 5989 0xcc000000000000000000000000000000cc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 515, 522, 524, 572, 860, 916, 1202, 1209, 1251, 1258, 1259]) (ps := [(14, [1266], [1272])]) (by decide +kernel)

theorem c5989_0 : P.sumLeaves 24 6132736 1024 = 1098124 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5989) (lo := 0) (len := 1024) (W := 1098124) check rows elimOK (by decide) (by decide) cover5989 (by decide)
  decide +kernel

theorem h5989 : P.leaf 34 5989 = 1098124 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1098124)]) (.cons c5989_0 (.nil)) (by decide) (by decide))

theorem cover5990 : P.CoversSplit 24 10 5990 0xaaaa0000000000000000000000000000a0a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000aaaa0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 515, 522, 524, 860, 916, 1209, 1251, 1259, 1264]) (ps := [(14, [1266], [1272])]) (by decide +kernel)

theorem c5990_0 : P.sumLeaves 24 6133760 1024 = 2628004 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5990) (lo := 0) (len := 1024) (W := 2628004) check rows elimOK (by decide) (by decide) cover5990 (by decide)
  decide +kernel

theorem h5990 : P.leaf 34 5990 = 2628004 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 2628004)]) (.cons c5990_0 (.nil)) (by decide) (by decide))

theorem cover5991 : P.CoversSplit 24 10 5991 0xffff0000000000000000000000000000ffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [515, 522, 524, 860, 916, 1202, 1209, 1251, 1258, 1259, 1264]) (ps := [(14, [1266], [1272])]) (by decide +kernel)

theorem c5991_0 : P.sumLeaves 24 6134784 1024 = 12279259 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5991) (lo := 0) (len := 1024) (W := 12279259) check rows elimOK (by decide) (by decide) cover5991 (by decide)
  decide +kernel

theorem h5991 : P.leaf 34 5991 = 12279259 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 12279259)]) (.cons c5991_0 (.nil)) (by decide) (by decide))

theorem cover5992 : P.CoversSplit 24 10 5992 0x8800000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000088000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 515, 522, 523, 565, 572, 860, 916, 1202, 1209, 1251, 1258, 1259]) (ps := [(14, [558], [860, 1272])]) (by decide +kernel)

theorem c5992_0 : P.sumLeaves 24 6135808 1024 = 101824 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5992) (lo := 0) (len := 1024) (W := 101824) check rows elimOK (by decide) (by decide) cover5992 (by decide)
  decide +kernel

theorem h5992 : P.leaf 34 5992 = 101824 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 101824)]) (.cons c5992_0 (.nil)) (by decide) (by decide))

theorem cover5993 : P.CoversSplit 24 10 5993 0xcc000000000000000000000000000000cc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 515, 522, 523, 572, 860, 916, 1202, 1209, 1258, 1259]) (ps := [(14, [558], [1272])]) (by decide +kernel)

theorem c5993_0 : P.sumLeaves 24 6136832 1024 = 637104 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5993) (lo := 0) (len := 1024) (W := 637104) check rows elimOK (by decide) (by decide) cover5993 (by decide)
  decide +kernel

theorem h5993 : P.leaf 34 5993 = 637104 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 637104)]) (.cons c5993_0 (.nil)) (by decide) (by decide))

theorem cover5994 : P.CoversSplit 24 10 5994 0xaaaa0000000000000000000000000000a0a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000aaaa0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 515, 522, 523, 565, 860, 916, 1209, 1251, 1259, 1264]) (ps := [(14, [874, 1266], [860, 1272])]) (by decide +kernel)

theorem c5994_0 : P.sumLeaves 24 6137856 1024 = 739236 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5994) (lo := 0) (len := 1024) (W := 739236) check rows elimOK (by decide) (by decide) cover5994 (by decide)
  decide +kernel

theorem h5994 : P.leaf 34 5994 = 739236 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 739236)]) (.cons c5994_0 (.nil)) (by decide) (by decide))

theorem cover5995 : P.CoversSplit 24 10 5995 0xffff0000000000000000000000000000ffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [515, 522, 523, 572, 860, 916, 1202, 1209, 1259, 1264]) (ps := [(14, [1266], [1272])]) (by decide +kernel)

theorem c5995_0 : P.sumLeaves 24 6138880 1024 = 4168548 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5995) (lo := 0) (len := 1024) (W := 4168548) check rows elimOK (by decide) (by decide) cover5995 (by decide)
  decide +kernel

theorem h5995 : P.leaf 34 5995 = 4168548 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 4168548)]) (.cons c5995_0 (.nil)) (by decide) (by decide))

theorem cover5996 : P.CoversSplit 24 10 5996 0x8800000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000088000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 515, 522, 572, 860, 916, 1202, 1209, 1251, 1258, 1259]) (ps := [(14, [1266], [1272])]) (by decide +kernel)

theorem c5996_0 : P.sumLeaves 24 6139904 1024 = 383572 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5996) (lo := 0) (len := 1024) (W := 383572) check rows elimOK (by decide) (by decide) cover5996 (by decide)
  decide +kernel

theorem h5996 : P.leaf 34 5996 = 383572 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 383572)]) (.cons c5996_0 (.nil)) (by decide) (by decide))

theorem cover5997 : P.CoversSplit 24 10 5997 0xcc000000000000000000000000000000cc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 515, 522, 572, 860, 916, 1202, 1209, 1251, 1258, 1259]) (ps := [(14, [1266], [1272])]) (by decide +kernel)

theorem c5997_0 : P.sumLeaves 24 6140928 1024 = 2813462 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5997) (lo := 0) (len := 1024) (W := 2813462) check rows elimOK (by decide) (by decide) cover5997 (by decide)
  decide +kernel

theorem h5997 : P.leaf 34 5997 = 2813462 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 2813462)]) (.cons c5997_0 (.nil)) (by decide) (by decide))

theorem cover5998 : P.CoversSplit 24 10 5998 0xaaaa0000000000000000000000000000a0a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000aaaa0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 515, 522, 860, 916, 1209, 1251, 1259, 1264]) (ps := [(14, [1266], [1272])]) (by decide +kernel)

theorem c5998_0 : P.sumLeaves 24 6141952 1024 = 4213278 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5998) (lo := 0) (len := 1024) (W := 4213278) check rows elimOK (by decide) (by decide) cover5998 (by decide)
  decide +kernel

theorem h5998 : P.leaf 34 5998 = 4213278 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 4213278)]) (.cons c5998_0 (.nil)) (by decide) (by decide))

theorem cover5999 : P.CoversSplit 24 10 5999 0xffff0000000000000000000000000000ffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [515, 522, 860, 916, 1202, 1209, 1251, 1258, 1259, 1264]) (ps := [(14, [1266], [1272])]) (by decide +kernel)

theorem c5999_0 : P.sumLeaves 24 6142976 1024 = 17251744 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5999) (lo := 0) (len := 1024) (W := 17251744) check rows elimOK (by decide) (by decide) cover5999 (by decide)
  decide +kernel

theorem h5999 : P.leaf 34 5999 = 17251744 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 17251744)]) (.cons c5999_0 (.nil)) (by decide) (by decide))

theorem cover6000 : P.CoversSplit 24 10 6000 0xf8c8f8c8a080a080f8c8f8c8a080a080f0c0f0c000000000f0c0f0c000000000c800c80080008000c800c80080008000c000c00000000000c000c00000000000c800c80080008000c800c80080008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 572, 860, 916, 1202, 1209, 1258, 1601]) (ps := [(2, [465], [466]), (5, [565], [572]), (8, [586, 1217], [572, 1272, 1609]), (12, [866, 867, 909], [860, 867, 909]), (14, [558], [860, 916, 1272])]) (by decide +kernel)

theorem c6000_0 : P.sumLeaves 24 6144000 384 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6000) (lo := 0) (len := 384) (W := 0) check rows elimOK (by decide) (by decide) cover6000 (by decide)
  decide +kernel

theorem contract6000_1 : P.leaf 30 96006 = 5824 := by
  exact leaf_contract_factors (k := 30) (b := 15) (H := 96006) (ss := [(2, 1, 468), (6, 1, 474), (15, 1, 487), (14, 1, 558), (8, 1, 586), (27, 1, 572), (19, 1, 586), (12, 1, 867), (5, 1, 411), (3, 1, 409), (4, 1, 410), (10, 1, 458), (11, 1, 459), (29, 1, 916), (18, 1, 923)]) (ids := [5, 7, 11, 14, 15, 18, 19, 22, 24, 26, 28, 29, 20, 21, 23]) (cs := [1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 4, 1, 1, 5, 6, 1, 1, 7, 8, 14, 15, 9, 16, 10, 1, 11, 1, 12, 13]) (bs := [12, 3]) (W := 5824) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c6000_1 : P.sumLeaves 24 6144384 64 = 5824 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 96006) rows (by decide) (by decide)).symm.trans contract6000_1

theorem contract6000_2 : P.leaf 30 96007 = 5824 := by
  exact leaf_contract_factors (k := 30) (b := 15) (H := 96007) (ss := [(2, 1, 468), (6, 1, 474), (15, 1, 487), (14, 1, 558), (27, 1, 572), (8, 1, 586), (19, 1, 586), (12, 1, 867), (5, 1, 411), (3, 1, 409), (4, 1, 410), (10, 1, 458), (11, 1, 459), (29, 1, 916), (18, 1, 923)]) (ids := [5, 7, 11, 14, 15, 18, 19, 22, 24, 26, 28, 29, 20, 21, 23]) (cs := [1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 4, 1, 1, 5, 6, 1, 1, 7, 8, 14, 15, 9, 16, 10, 1, 11, 1, 12, 13]) (bs := [12, 3]) (W := 5824) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c6000_2 : P.sumLeaves 24 6144448 64 = 5824 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 96007) rows (by decide) (by decide)).symm.trans contract6000_2

theorem contract6000_3 : P.leaf 30 96008 = 2048 := by
  exact leaf_contract_factors (k := 30) (b := 13) (H := 96008) (ss := [(2, 1, 468), (6, 1, 474), (15, 1, 487), (14, 1, 558), (5, 1, 572), (3, 1, 409), (4, 1, 410), (10, 1, 458), (11, 1, 459), (12, 1, 460), (27, 1, 572), (19, 1, 578), (16, 1, 874), (18, 1, 879), (31, 1, 909), (28, 1, 860), (29, 1, 916)]) (ids := [5, 6, 7, 11, 15, 18, 19, 22, 24, 28, 20, 21, 23]) (cs := [1, 1, 1, 1, 1, 2, 3, 4, 1, 1, 1, 5, 1, 1, 1, 6, 1, 1, 7, 8, 12, 13, 9, 14, 10, 1, 1, 1, 11, 1]) (bs := [10, 3]) (W := 2048) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c6000_3 : P.sumLeaves 24 6144512 64 = 2048 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 96008) rows (by decide) (by decide)).symm.trans contract6000_3

theorem contract6000_4 : P.leaf 30 96009 = 2048 := by
  exact leaf_contract_factors (k := 30) (b := 13) (H := 96009) (ss := [(2, 1, 468), (6, 1, 474), (15, 1, 487), (14, 1, 558), (19, 1, 578), (12, 1, 867), (5, 1, 411), (3, 1, 409), (4, 1, 410), (10, 1, 458), (11, 1, 459), (16, 1, 874), (18, 1, 879), (31, 1, 909), (28, 1, 860), (29, 1, 916), (27, 1, 1601)]) (ids := [5, 6, 7, 11, 15, 18, 19, 22, 24, 28, 20, 21, 23]) (cs := [1, 1, 1, 1, 1, 2, 3, 4, 1, 1, 1, 5, 1, 1, 1, 6, 1, 1, 7, 8, 12, 13, 9, 14, 10, 1, 1, 1, 11, 1]) (bs := [10, 3]) (W := 2048) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c6000_4 : P.sumLeaves 24 6144576 64 = 2048 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 96009) rows (by decide) (by decide)).symm.trans contract6000_4

theorem contract6000_5 : P.leaf 30 96010 = 6720 := by
  exact leaf_contract_factors (k := 30) (b := 16) (H := 96010) (ss := [(2, 1, 468), (6, 1, 474), (15, 1, 487), (14, 1, 558), (5, 1, 572), (3, 1, 409), (4, 1, 410), (10, 1, 458), (11, 1, 459), (12, 1, 460), (27, 1, 572), (19, 1, 578), (18, 1, 879), (29, 1, 916)]) (ids := [5, 6, 7, 11, 14, 15, 18, 19, 22, 24, 26, 28, 29, 20, 21, 23]) (cs := [1, 1, 1, 1, 1, 2, 3, 4, 1, 1, 1, 5, 1, 1, 6, 7, 1, 1, 8, 9, 15, 16, 10, 17, 11, 1, 12, 1, 13, 14]) (bs := [13, 3]) (W := 6720) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c6000_5 : P.sumLeaves 24 6144640 64 = 6720 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 96010) rows (by decide) (by decide)).symm.trans contract6000_5

theorem contract6000_6 : P.leaf 30 96011 = 6720 := by
  exact leaf_contract_factors (k := 30) (b := 16) (H := 96011) (ss := [(2, 1, 468), (6, 1, 474), (15, 1, 487), (14, 1, 558), (19, 1, 578), (12, 1, 867), (5, 1, 411), (3, 1, 409), (4, 1, 410), (10, 1, 458), (11, 1, 459), (18, 1, 879), (29, 1, 916), (27, 1, 1601)]) (ids := [5, 6, 7, 11, 14, 15, 18, 19, 22, 24, 26, 28, 29, 20, 21, 23]) (cs := [1, 1, 1, 1, 1, 2, 3, 4, 1, 1, 1, 5, 1, 1, 6, 7, 1, 1, 8, 9, 15, 16, 10, 17, 11, 1, 12, 1, 13, 14]) (bs := [13, 3]) (W := 6720) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c6000_6 : P.sumLeaves 24 6144704 64 = 6720 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 96011) rows (by decide) (by decide)).symm.trans contract6000_6

theorem contract6000_7 : P.leaf 30 96012 = 16640 := by
  exact leaf_contract_factors (k := 30) (b := 17) (H := 96012) (ss := [(2, 1, 468), (6, 1, 474), (15, 1, 487), (14, 1, 558), (12, 1, 867), (5, 1, 411), (3, 1, 409), (4, 1, 410), (10, 1, 458), (11, 1, 459), (16, 1, 874), (31, 1, 909), (28, 1, 860)]) (ids := [5, 6, 7, 11, 15, 16, 17, 18, 19, 22, 23, 24, 25, 27, 28, 20, 21]) (cs := [1, 1, 1, 1, 1, 2, 3, 4, 1, 1, 1, 5, 1, 1, 1, 6, 7, 8, 9, 10, 17, 18, 11, 12, 13, 14, 1, 15, 16, 1]) (bs := [15, 2]) (W := 16640) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c6000_7 : P.sumLeaves 24 6144768 64 = 16640 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 96012) rows (by decide) (by decide)).symm.trans contract6000_7

theorem contract6000_8 : P.leaf 30 96013 = 16640 := by
  exact leaf_contract_factors (k := 30) (b := 17) (H := 96013) (ss := [(2, 1, 468), (6, 1, 474), (15, 1, 487), (14, 1, 558), (12, 1, 867), (5, 1, 411), (3, 1, 409), (4, 1, 410), (10, 1, 458), (11, 1, 459), (16, 1, 874), (31, 1, 909), (28, 1, 860)]) (ids := [5, 6, 7, 11, 15, 16, 17, 18, 19, 22, 23, 24, 25, 27, 28, 20, 21]) (cs := [1, 1, 1, 1, 1, 2, 3, 4, 1, 1, 1, 5, 1, 1, 1, 6, 7, 8, 9, 10, 17, 18, 11, 12, 13, 14, 1, 15, 16, 1]) (bs := [15, 2]) (W := 16640) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c6000_8 : P.sumLeaves 24 6144832 64 = 16640 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 96013) rows (by decide) (by decide)).symm.trans contract6000_8

theorem contract6000_9 : P.leaf 30 96014 = 46976 := by
  exact leaf_contract_factors (k := 30) (b := 20) (H := 96014) (ss := [(2, 1, 468), (6, 1, 474), (15, 1, 487), (14, 1, 558), (12, 1, 867), (5, 1, 411), (3, 1, 409), (4, 1, 410), (10, 1, 458), (11, 1, 459)]) (ids := [5, 6, 7, 11, 14, 15, 16, 17, 18, 19, 22, 23, 24, 25, 26, 27, 28, 29, 20, 21]) (cs := [1, 1, 1, 1, 1, 2, 3, 4, 1, 1, 1, 5, 1, 1, 6, 7, 8, 9, 10, 11, 20, 21, 12, 13, 14, 15, 16, 17, 18, 19]) (bs := [18, 2]) (W := 46976) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c6000_9 : P.sumLeaves 24 6144896 64 = 46976 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 96014) rows (by decide) (by decide)).symm.trans contract6000_9

theorem contract6000_10 : P.leaf 30 96015 = 47168 := by
  exact leaf_contract_factors (k := 30) (b := 20) (H := 96015) (ss := [(2, 1, 468), (6, 1, 474), (15, 1, 487), (14, 1, 558), (12, 1, 867), (5, 1, 411), (3, 1, 409), (4, 1, 410), (10, 1, 458), (11, 1, 459)]) (ids := [5, 6, 7, 11, 14, 15, 16, 17, 18, 19, 22, 24, 25, 26, 27, 28, 29, 20, 21, 23]) (cs := [1, 1, 1, 1, 1, 2, 3, 4, 1, 1, 1, 5, 1, 1, 6, 7, 8, 9, 10, 11, 19, 20, 12, 21, 13, 14, 15, 16, 17, 18]) (bs := [17, 3]) (W := 47168) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c6000_10 : P.sumLeaves 24 6144960 64 = 47168 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 96015) rows (by decide) (by decide)).symm.trans contract6000_10

theorem h6000 : P.leaf 34 6000 = 156608 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(384, 0), (64, 5824), (64, 5824), (64, 2048), (64, 2048), (64, 6720), (64, 6720), (64, 16640), (64, 16640), (64, 46976), (64, 47168)]) (.cons c6000_0 (.cons c6000_1 (.cons c6000_2 (.cons c6000_3 (.cons c6000_4 (.cons c6000_5 (.cons c6000_6 (.cons c6000_7 (.cons c6000_8 (.cons c6000_9 (.cons c6000_10 (.nil)))))))))))) (by decide) (by decide))

theorem cover6001 : P.CoversSplit 24 10 6001 0xffffffffa0a0a0a0ffccffcca080a080ffffffff00000000ffccffcc00000000cc00cc0080008000cc00cc0080008000cc00cc0000000000cc00cc0000000000cc00cc0080008000cc00cc0080008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 572, 860, 916, 1202, 1258, 1601]) (ps := [(5, [523], [572]), (8, [586], [572, 1609]), (12, [478], [909, 916]), (14, [558], [916, 1272])]) (by decide +kernel)

theorem c6001_0 : P.sumLeaves 24 6145024 384 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6001) (lo := 0) (len := 384) (W := 0) check rows elimOK (by decide) (by decide) cover6001 (by decide)
  decide +kernel

theorem contract6001_1 : P.leaf 30 96022 = 103184 := by
  exact leaf_contract_factors (k := 30) (b := 20) (H := 96022) (ss := [(6, 1, 474), (2, 1, 475), (12, 1, 478), (15, 1, 487), (14, 1, 558), (8, 1, 586), (27, 1, 572), (19, 1, 586), (29, 1, 916), (18, 1, 923)]) (ids := [1, 2, 3, 5, 7, 8, 9, 11, 14, 15, 18, 19, 20, 22, 24, 26, 28, 29, 21, 23]) (cs := [1, 2, 3, 4, 1, 5, 1, 6, 7, 8, 1, 9, 1, 1, 10, 11, 1, 1, 12, 13, 14, 20, 15, 21, 16, 1, 17, 1, 18, 19]) (bs := [18, 2]) (W := 103184) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c6001_1 : P.sumLeaves 24 6145408 64 = 103184 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 96022) rows (by decide) (by decide)).symm.trans contract6001_1

theorem contract6001_2 : P.leaf 30 96023 = 156944 := by
  exact leaf_contract_factors (k := 30) (b := 20) (H := 96023) (ss := [(6, 1, 474), (2, 1, 475), (12, 1, 478), (15, 1, 487), (14, 1, 558), (27, 1, 572), (8, 1, 586), (19, 1, 586), (29, 1, 916), (18, 1, 923)]) (ids := [1, 2, 3, 5, 7, 8, 9, 11, 14, 15, 18, 19, 20, 22, 24, 26, 28, 29, 21, 23]) (cs := [1, 2, 3, 4, 1, 5, 1, 6, 7, 8, 1, 9, 1, 1, 10, 11, 1, 1, 12, 13, 14, 20, 15, 21, 16, 1, 17, 1, 18, 19]) (bs := [18, 2]) (W := 156944) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c6001_2 : P.sumLeaves 24 6145472 64 = 156944 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 96023) rows (by decide) (by decide)).symm.trans contract6001_2

theorem contract6001_3 : P.leaf 30 96024 = 42944 := by
  exact leaf_contract_factors (k := 30) (b := 18) (H := 96024) (ss := [(6, 1, 474), (2, 1, 475), (12, 1, 478), (15, 1, 487), (14, 1, 558), (5, 1, 572), (27, 1, 572), (19, 1, 578), (16, 1, 874), (31, 1, 909), (29, 1, 916), (18, 1, 921)]) (ids := [1, 2, 5, 6, 7, 9, 11, 15, 18, 19, 20, 21, 22, 24, 26, 28, 8, 23]) (cs := [1, 2, 3, 1, 1, 4, 5, 6, 18, 7, 1, 8, 1, 1, 1, 9, 1, 1, 10, 11, 12, 13, 14, 19, 15, 1, 16, 1, 17, 1]) (bs := [16, 2]) (W := 42944) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c6001_3 : P.sumLeaves 24 6145536 64 = 42944 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 96024) rows (by decide) (by decide)).symm.trans contract6001_3

theorem contract6001_4 : P.leaf 30 96025 = 78104 := by
  exact leaf_contract_factors (k := 30) (b := 19) (H := 96025) (ss := [(6, 1, 474), (2, 1, 475), (12, 1, 478), (15, 1, 487), (14, 1, 558), (19, 1, 578), (16, 1, 874), (31, 1, 909), (29, 1, 916), (18, 1, 921), (27, 1, 1601)]) (ids := [1, 2, 3, 5, 6, 7, 8, 9, 11, 15, 18, 19, 20, 21, 22, 24, 26, 28, 23]) (cs := [1, 2, 3, 4, 1, 5, 6, 7, 8, 9, 1, 10, 1, 1, 1, 11, 1, 1, 12, 13, 14, 15, 16, 20, 17, 1, 18, 1, 19, 1]) (bs := [18, 1]) (W := 78104) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c6001_4 : P.sumLeaves 24 6145600 64 = 78104 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 96025) rows (by decide) (by decide)).symm.trans contract6001_4

theorem c6001_5 : P.sumLeaves 24 6145664 310 = 1311368 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6001) (lo := 640) (len := 310) (W := 1311368) check rows elimOK (by decide) (by decide) cover6001 (by decide)
  decide +kernel

theorem c6001_6 : P.sumLeaves 24 6145974 74 = 1537020 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6001) (lo := 950) (len := 74) (W := 1537020) check rows elimOK (by decide) (by decide) cover6001 (by decide)
  decide +kernel

theorem h6001 : P.leaf 34 6001 = 3229564 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(384, 0), (64, 103184), (64, 156944), (64, 42944), (64, 78104), (310, 1311368), (74, 1537020)]) (.cons c6001_0 (.cons c6001_1 (.cons c6001_2 (.cons c6001_3 (.cons c6001_4 (.cons c6001_5 (.cons c6001_6 (.nil)))))))) (by decide) (by decide))

theorem cover6002 : P.CoversSplit 24 10 6002 0xfffffafaa0a0a0a0fffffafaa0a0a0a0f0f0f0f00f0f0000f0f0f0f00f0f0000cc00c80080008000cc00c80080008000c000c00000000000c000c00000000000fffffafaa0a0a0a0fffffafaa0a0a0a0fffffafa00000000fffffafa000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 572, 860, 916, 1202, 1209, 1217, 1258, 1601, 1609]) (ps := [(8, [586, 1217], [1272, 1609]), (12, [478], [860, 867]), (14, [874], [860])]) (by decide +kernel)

theorem c6002_0 : P.sumLeaves 24 6146048 256 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6002) (lo := 0) (len := 256) (W := 0) check rows elimOK (by decide) (by decide) cover6002 (by decide)
  decide +kernel

theorem contract6002_1 : P.leaf 30 96036 = 0 := by
  exact leaf_contract_zero (ss := [(2, 1, 453), (5, 1, 453), (6, 1, 478), (12, 1, 460), (8, 0, 1272), (14, 1, 482), (7, 1, 488), (28, 1, 509)]) (q := 586) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c6002_1 : P.sumLeaves 24 6146304 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 96036) rows (by decide) (by decide)).symm.trans contract6002_1

theorem contract6002_2 : P.leaf 30 96037 = 0 := by
  exact leaf_contract_zero (ss := [(2, 1, 453), (5, 1, 453), (6, 1, 478), (12, 1, 460), (8, 0, 1272), (14, 1, 482), (7, 1, 488), (28, 1, 509)]) (q := 586) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c6002_2 : P.sumLeaves 24 6146368 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 96037) rows (by decide) (by decide)).symm.trans contract6002_2

theorem c6002_3 : P.sumLeaves 24 6146432 382 = 546140 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6002) (lo := 384) (len := 382) (W := 546140) check rows elimOK (by decide) (by decide) cover6002 (by decide)
  decide +kernel

theorem c6002_4 : P.sumLeaves 24 6146814 230 = 1345016 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6002) (lo := 766) (len := 230) (W := 1345016) check rows elimOK (by decide) (by decide) cover6002 (by decide)
  decide +kernel

theorem c6002_5 : P.sumLeaves 24 6147044 28 = 881072 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6002) (lo := 996) (len := 28) (W := 881072) check rows elimOK (by decide) (by decide) cover6002 (by decide)
  decide +kernel

theorem h6002 : P.leaf 34 6002 = 2772228 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(256, 0), (64, 0), (64, 0), (382, 546140), (230, 1345016), (28, 881072)]) (.cons c6002_0 (.cons c6002_1 (.cons c6002_2 (.cons c6002_3 (.cons c6002_4 (.cons c6002_5 (.nil))))))) (by decide) (by decide))

theorem cover6003 : P.CoversSplit 24 10 6003 0xffffffffa0a0a0a0ffffffffa0a0a0a0ffffffffa0a0a0a0ffffffffa0a0a0a0cc00cc0080008000cc00cc0080008000cc00cc0080008000cc00cc0080008000ffffffffa0a0a0a0ffffffffa0a0a0a0ffffffffa0a0a0a0ffffffffa0a0a0a000000000000000000000000000000000cc00cc0080008000cc00cc0080008000 :=
  coversProjected check rows (by decide) (by decide) (xs := [572, 860, 916, 1202, 1258, 1601, 1609]) (ps := [(8, [586], [1609])]) (by decide +kernel)

theorem contract6003_0 : P.leaf 30 96048 = 0 := by
  exact leaf_contract_zero (ss := [(6, 1, 474), (2, 1, 475), (12, 1, 478), (5, 1, 572), (27, 1, 572), (4, 1, 578), (8, 1, 622), (19, 1, 586), (9, 1, 587), (10, 1, 872), (14, 1, 874), (16, 1, 874), (29, 1, 916), (11, 1, 921), (13, 1, 922), (18, 1, 922)]) (q := 1272) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c6003_0 : P.sumLeaves 24 6147072 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 96048) rows (by decide) (by decide)).symm.trans contract6003_0

theorem contract6003_1 : P.leaf 30 96049 = 0 := by
  exact leaf_contract_zero (ss := [(6, 1, 474), (2, 1, 475), (12, 1, 478), (4, 1, 578), (10, 1, 872), (29, 1, 916), (11, 1, 921), (14, 1, 965), (8, 1, 586), (19, 1, 586), (16, 1, 874), (13, 1, 922), (18, 1, 922)]) (q := 1272) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c6003_1 : P.sumLeaves 24 6147136 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 96049) rows (by decide) (by decide)).symm.trans contract6003_1

theorem c6003_2 : P.sumLeaves 24 6147200 128 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6003) (lo := 128) (len := 128) (W := 0) check rows elimOK (by decide) (by decide) cover6003 (by decide)
  decide +kernel

theorem contract6003_3 : P.leaf 30 96052 = 0 := by
  exact leaf_contract_zero (ss := [(6, 1, 478), (12, 1, 478), (8, 0, 1272), (14, 1, 482), (7, 1, 488)]) (q := 586) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c6003_3 : P.sumLeaves 24 6147328 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 96052) rows (by decide) (by decide)).symm.trans contract6003_3

theorem contract6003_4 : P.leaf 30 96053 = 0 := by
  exact leaf_contract_zero (ss := [(6, 1, 478), (12, 1, 478), (8, 0, 1272), (14, 1, 482), (7, 1, 488)]) (q := 586) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c6003_4 : P.sumLeaves 24 6147392 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 96053) rows (by decide) (by decide)).symm.trans contract6003_4

theorem c6003_5 : P.sumLeaves 24 6147456 250 = 1482112 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6003) (lo := 384) (len := 250) (W := 1482112) check rows elimOK (by decide) (by decide) cover6003 (by decide)
  decide +kernel

theorem c6003_6 : P.sumLeaves 24 6147706 254 = 2866136 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6003) (lo := 634) (len := 254) (W := 2866136) check rows elimOK (by decide) (by decide) cover6003 (by decide)
  decide +kernel

theorem c6003_7 : P.sumLeaves 24 6147960 136 = 6586822 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6003) (lo := 888) (len := 136) (W := 6586822) check rows elimOK (by decide) (by decide) cover6003 (by decide)
  decide +kernel

theorem h6003 : P.leaf 34 6003 = 10935070 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(64, 0), (64, 0), (128, 0), (64, 0), (64, 0), (250, 1482112), (254, 2866136), (136, 6586822)]) (.cons c6003_0 (.cons c6003_1 (.cons c6003_2 (.cons c6003_3 (.cons c6003_4 (.cons c6003_5 (.cons c6003_6 (.cons c6003_7 (.nil))))))))) (by decide) (by decide))

theorem cover6004 : P.CoversSplit 24 10 6004 0xffffffffa8a8a0a0ffffffffa8a8a0a0f4f4f4f400000000f4f4f4f400000000cc00cc0080008000cc00cc0080008000c400c40000000000c400c40000000000cc00cc0088008000cc30cc3088208020c400c40000000000c430c430000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 572, 860, 867, 909, 916, 1202, 1209, 1258, 1601]) (ps := [(2, [465, 468, 475], [466])]) (by decide +kernel)

theorem c6004_0 : P.sumLeaves 24 6148096 256 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6004) (lo := 0) (len := 256) (W := 0) check rows elimOK (by decide) (by decide) cover6004 (by decide)
  decide +kernel

theorem contract6004_1 : P.leaf 30 96068 = 0 := by
  exact leaf_contract_zero (ss := [(2, 1, 468), (6, 1, 480), (31, 1, 909), (8, 0, 1272), (20, 1, 580), (21, 1, 586), (5, 1, 622), (4, 1, 410), (11, 1, 459), (10, 1, 458), (14, 1, 1266), (9, 1, 629), (28, 1, 860), (29, 1, 916), (27, 1, 572)]) (q := 1272) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c6004_1 : P.sumLeaves 24 6148352 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 96068) rows (by decide) (by decide)).symm.trans contract6004_1

theorem contract6004_2 : P.leaf 30 96069 = 0 := by
  exact leaf_contract_zero (ss := [(2, 1, 468), (6, 1, 480), (27, 1, 572), (31, 1, 909), (29, 1, 916), (8, 0, 1272), (20, 1, 580), (21, 1, 586), (5, 1, 622), (4, 1, 410), (11, 1, 459), (10, 1, 458), (14, 1, 1266), (9, 1, 629), (28, 1, 860)]) (q := 1272) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c6004_2 : P.sumLeaves 24 6148416 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 96069) rows (by decide) (by decide)).symm.trans contract6004_2

theorem c6004_3 : P.sumLeaves 24 6148480 508 = 545254 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6004) (lo := 384) (len := 508) (W := 545254) check rows elimOK (by decide) (by decide) cover6004 (by decide)
  decide +kernel

theorem c6004_4 : P.sumLeaves 24 6148988 132 = 1395335 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6004) (lo := 892) (len := 132) (W := 1395335) check rows elimOK (by decide) (by decide) cover6004 (by decide)
  decide +kernel

theorem h6004 : P.leaf 34 6004 = 1940589 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(256, 0), (64, 0), (64, 0), (508, 545254), (132, 1395335)]) (.cons c6004_0 (.cons c6004_1 (.cons c6004_2 (.cons c6004_3 (.cons c6004_4 (.nil)))))) (by decide) (by decide))

theorem cover6005 : P.CoversSplit 24 10 6005 0xffffffffaaaaa0a0ffffffffaaaaa0a0ffffffff00000000ffffffff00000000cc00cc0080008000cc00cc0080008000cc00cc0000000000cc00cc0000000000cc00cc0088008000cc33cc3388228020cc00cc0000000000cc33cc33000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 572, 860, 909, 916, 1202, 1209, 1258, 1601]) (by decide +kernel)

theorem c6005_0 : P.sumLeaves 24 6149120 256 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6005) (lo := 0) (len := 256) (W := 0) check rows elimOK (by decide) (by decide) cover6005 (by decide)
  decide +kernel

theorem contract6005_1 : P.leaf 30 96084 = 0 := by
  exact leaf_contract_zero (ss := [(2, 1, 475), (6, 1, 480), (31, 1, 909), (8, 0, 1272), (20, 1, 580), (21, 1, 586), (5, 1, 622), (14, 1, 1266), (9, 1, 629), (29, 1, 916), (27, 1, 572)]) (q := 1272) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c6005_1 : P.sumLeaves 24 6149376 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 96084) rows (by decide) (by decide)).symm.trans contract6005_1

theorem contract6005_2 : P.leaf 30 96085 = 0 := by
  exact leaf_contract_zero (ss := [(2, 1, 475), (6, 1, 480), (27, 1, 572), (31, 1, 909), (29, 1, 916), (8, 0, 1272), (20, 1, 580), (21, 1, 586), (5, 1, 622), (14, 1, 1266), (9, 1, 629)]) (q := 1272) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c6005_2 : P.sumLeaves 24 6149440 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 96085) rows (by decide) (by decide)).symm.trans contract6005_2

theorem c6005_3 : P.sumLeaves 24 6149504 443 = 4376930 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6005) (lo := 384) (len := 443) (W := 4376930) check rows elimOK (by decide) (by decide) cover6005 (by decide)
  decide +kernel

theorem c6005_4 : P.sumLeaves 24 6149947 168 = 11034444 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6005) (lo := 827) (len := 168) (W := 11034444) check rows elimOK (by decide) (by decide) cover6005 (by decide)
  decide +kernel

theorem c6005_5 : P.sumLeaves 24 6150115 29 = 8071122 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6005) (lo := 995) (len := 29) (W := 8071122) check rows elimOK (by decide) (by decide) cover6005 (by decide)
  decide +kernel

theorem h6005 : P.leaf 34 6005 = 23482496 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(256, 0), (64, 0), (64, 0), (443, 4376930), (168, 11034444), (29, 8071122)]) (.cons c6005_0 (.cons c6005_1 (.cons c6005_2 (.cons c6005_3 (.cons c6005_4 (.cons c6005_5 (.nil))))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(5983, 12), (5984, 48), (5985, 48), (5986, 48), (5987, 48), (5988, 48), (5989, 48), (5990, 48), (5991, 48), (5992, 48), (5993, 48), (5994, 48), (5995, 48), (5996, 48), (5997, 48), (5998, 48), (5999, 48), (6000, 48), (6001, 48), (6002, 48), (6003, 48), (6004, 48), (6005, 48)]

theorem segOK : checkSeg 16 perms 5983 6006 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 5983 6006 1068 5039956068 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 5039956068)
    (SegSum.cons (w := 12) h5983 (SegSum.cons (w := 48) h5984 (SegSum.cons (w := 48) h5985 (SegSum.cons (w := 48) h5986 (SegSum.cons (w := 48) h5987 (SegSum.cons (w := 48) h5988 (SegSum.cons (w := 48) h5989 (SegSum.cons (w := 48) h5990 (SegSum.cons (w := 48) h5991 (SegSum.cons (w := 48) h5992 (SegSum.cons (w := 48) h5993 (SegSum.cons (w := 48) h5994 (SegSum.cons (w := 48) h5995 (SegSum.cons (w := 48) h5996 (SegSum.cons (w := 48) h5997 (SegSum.cons (w := 48) h5998 (SegSum.cons (w := 48) h5999 (SegSum.cons (w := 48) h6000 (SegSum.cons (w := 48) h6001 (SegSum.cons (w := 48) h6002 (SegSum.cons (w := 48) h6003 (SegSum.cons (w := 48) h6004 (SegSum.cons (w := 48) h6005 (show SegSum (P.leaf 34) [] 0 from rfl)))))))))))))))))))))))) (by decide)

end RACert.S4N1.C0.S35
