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

namespace RACert.S4N1.C0.S15

open RACert RACert.Problem

theorem cover1928 : P.CoversSplit 24 10 1928 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [509]) (by decide +kernel)

theorem c1928_0 : P.sumLeaves 24 1974272 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1928) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1928 (by decide)
  decide +kernel

theorem h1928 : P.leaf 34 1928 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1928_0 (.nil)) (by decide) (by decide))

theorem cover1929 : P.CoversSplit 24 10 1929 0x8800000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000088000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 474, 515, 517, 522, 528, 565, 915, 1209, 1609]) (ps := [(14, [874, 929], [860, 1266])]) (by decide +kernel)

theorem c1929_0 : P.sumLeaves 24 1975296 1024 = 20912 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1929) (lo := 0) (len := 1024) (W := 20912) check rows elimOK (by decide) (by decide) cover1929 (by decide)
  decide +kernel

theorem h1929 : P.leaf 34 1929 = 20912 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 20912)]) (.cons c1929_0 (.nil)) (by decide) (by decide))

theorem cover1930 : P.CoversSplit 24 10 1930 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [509]) (by decide +kernel)

theorem c1930_0 : P.sumLeaves 24 1976320 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1930) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1930 (by decide)
  decide +kernel

theorem h1930 : P.leaf 34 1930 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1930_0 (.nil)) (by decide) (by decide))

theorem cover1931 : P.CoversSplit 24 10 1931 0xaaaa0000000000000000000000000000a0a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000aaaa0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [515, 516, 517, 522, 528, 565, 916, 1209, 1258]) (ps := [(14, [874, 965], [860, 1266])]) (by decide +kernel)

theorem c1931_0 : P.sumLeaves 24 1977344 448 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1931) (lo := 0) (len := 448) (W := 0) check rows elimOK (by decide) (by decide) cover1931 (by decide)
  decide +kernel

theorem contract1931_1 : P.leaf 30 30903 = 46592 := by
  apply (leaf_contract (k := 30) (b := 17) (H := 30903) (ss := [(12, 1, 486), (3, 1, 502), (5, 1, 502), (26, 1, 528), (31, 1, 517), (11, 1, 901), (14, 1, 923), (18, 1, 923), (19, 1, 965), (30, 1, 1209), (16, 1, 1265), (17, 1, 1273), (15, 1, 930)]) (ids := [0, 2, 4, 5, 6, 7, 8, 11, 18, 19, 20, 21, 22, 23, 25, 26, 27]) (cs := [2, 1, 3, 1, 4, 5, 6, 7, 8, 1, 1, 9, 1, 1, 1, 1, 1, 1, 10, 11, 12, 13, 14, 15, 1, 16, 17, 18, 1, 1]) check rows (by decide) (by decide +kernel) (by decide +kernel)).trans
  decide +kernel

theorem c1931_1 : P.sumLeaves 24 1977792 64 = 46592 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 30903) rows (by decide) (by decide)).symm.trans contract1931_1

theorem c1931_2 : P.sumLeaves 24 1977856 320 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1931) (lo := 512) (len := 320) (W := 0) check rows elimOK (by decide) (by decide) cover1931 (by decide)
  decide +kernel

theorem contract1931_3 : P.leaf 30 30909 = 4608 := by
  exact leaf_contract_factors (k := 30) (b := 13) (H := 30909) (ss := [(31, 12, 486), (3, 1, 502), (5, 1, 502), (12, 1, 509), (26, 1, 528), (16, 1, 529), (7, 1, 530), (8, 1, 615), (17, 1, 537), (11, 1, 818), (14, 1, 874), (28, 1, 860), (30, 1, 1209), (18, 1, 1265), (19, 1, 1273), (20, 1, 1314), (21, 1, 1315)]) (ids := [4, 8, 13, 21, 0, 2, 7, 11, 20, 22, 23, 25, 27]) (cs := [6, 1, 7, 1, 2, 1, 1, 8, 3, 1, 1, 9, 1, 4, 1, 1, 1, 1, 1, 1, 10, 5, 11, 12, 1, 13, 1, 14, 1, 1]) (bs := [4, 9]) (W := 4608) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1931_3 : P.sumLeaves 24 1978176 64 = 4608 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 30909) rows (by decide) (by decide)).symm.trans contract1931_3

theorem c1931_4 : P.sumLeaves 24 1978240 128 = 235520 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1931) (lo := 896) (len := 128) (W := 235520) check rows elimOK (by decide) (by decide) cover1931 (by decide)
  decide +kernel

theorem h1931 : P.leaf 34 1931 = 286720 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(448, 0), (64, 46592), (320, 0), (64, 4608), (128, 235520)]) (.cons c1931_0 (.cons c1931_1 (.cons c1931_2 (.cons c1931_3 (.cons c1931_4 (.nil)))))) (by decide) (by decide))

theorem cover1932 : P.CoversSplit 24 10 1932 0x8000000000000000000000000000000080000000000000000000000000000000000000000000000000200000000000000000000000000000002000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 508, 515, 516, 522, 860, 872, 915, 1209, 1258, 1259]) (ps := [(14, [923], [1266])]) (by decide +kernel)

theorem c1932_0 : P.sumLeaves 24 1978368 1024 = 11832 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1932) (lo := 0) (len := 1024) (W := 11832) check rows elimOK (by decide) (by decide) cover1932 (by decide)
  decide +kernel

theorem h1932 : P.leaf 34 1932 = 11832 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 11832)]) (.cons c1932_0 (.nil)) (by decide) (by decide))

theorem cover1933 : P.CoversSplit 24 10 1933 0x8800000000000000000000000000000080000000000000000000000000000000000000000000000000220000000000000000000000000000002000000000000088000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 515, 517, 522, 528, 860, 915, 1209, 1609]) (ps := [(14, [923], [1266])]) (by decide +kernel)

theorem c1933_0 : P.sumLeaves 24 1979392 1024 = 207936 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1933) (lo := 0) (len := 1024) (W := 207936) check rows elimOK (by decide) (by decide) cover1933 (by decide)
  decide +kernel

theorem h1933 : P.leaf 34 1933 = 207936 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 207936)]) (.cons c1933_0 (.nil)) (by decide) (by decide))

theorem cover1934 : P.CoversSplit 24 10 1934 0xa0a00000000000000000000000000000a0a000000000000000000000000000000000000000000000008000000000000000000000000000000080000000000000a0a00000000000000000000000000000a0a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 515, 516, 522, 860, 872, 916, 1209, 1210, 1258, 1259]) (ps := [(16, [468], [1258])]) (by decide +kernel)

theorem c1934_0 : P.sumLeaves 24 1980416 320 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1934) (lo := 0) (len := 320) (W := 0) check rows elimOK (by decide) (by decide) cover1934 (by decide)
  decide +kernel

theorem contract1934_1 : P.leaf 30 30949 = 1472 := by
  exact leaf_contract_factors (k := 30) (b := 13) (H := 30949) (ss := [(16, 1, 468), (3, 1, 486), (8, 1, 537), (12, 1, 867), (31, 1, 872), (5, 1, 418), (2, 1, 409), (4, 1, 417), (26, 1, 465), (28, 1, 465), (30, 1, 515), (7, 1, 530), (18, 1, 1265), (14, 0, 1266), (10, 1, 811), (21, 0, 874), (20, 1, 880)]) (ids := [4, 7, 9, 11, 13, 15, 17, 21, 23, 25, 27, 20, 22]) (cs := [1, 1, 1, 1, 2, 1, 1, 3, 1, 4, 1, 5, 0, 6, 1, 7, 1, 8, 1, 0, 13, 9, 14, 10, 1, 11, 1, 12, 1, 1]) (bs := [11, 2]) (W := 1472) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1934_1 : P.sumLeaves 24 1980736 64 = 1472 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 30949) rows (by decide) (by decide)).symm.trans contract1934_1

theorem c1934_2 : P.sumLeaves 24 1980800 64 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1934) (lo := 384) (len := 64) (W := 0) check rows elimOK (by decide) (by decide) cover1934 (by decide)
  decide +kernel

theorem contract1934_3 : P.leaf 30 30951 = 25600 := by
  exact leaf_contract_factors (k := 30) (b := 17) (H := 30951) (ss := [(3, 1, 486), (12, 1, 867), (31, 1, 872), (5, 1, 418), (2, 1, 409), (4, 1, 417), (26, 1, 465), (28, 1, 465), (30, 1, 515), (18, 1, 1266), (16, 1, 1265), (19, 1, 1272), (17, 1, 1273)]) (ids := [4, 5, 6, 7, 8, 9, 11, 12, 13, 18, 19, 21, 22, 23, 25, 27, 20]) (cs := [1, 1, 1, 1, 2, 3, 4, 5, 6, 7, 1, 8, 9, 10, 1, 1, 1, 1, 11, 12, 18, 13, 14, 15, 1, 16, 1, 17, 1, 1]) (bs := [16, 1]) (W := 25600) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1934_3 : P.sumLeaves 24 1980864 64 = 25600 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 30951) rows (by decide) (by decide)).symm.trans contract1934_3

theorem c1934_4 : P.sumLeaves 24 1980928 320 = 2160 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1934) (lo := 512) (len := 320) (W := 2160) check rows elimOK (by decide) (by decide) cover1934 (by decide)
  decide +kernel

theorem contract1934_5 : P.leaf 30 30957 = 2432 := by
  exact leaf_contract_factors (k := 30) (b := 12) (H := 30957) (ss := [(16, 1, 468), (3, 1, 486), (8, 1, 537), (12, 1, 867), (31, 1, 872), (5, 1, 418), (2, 1, 409), (4, 1, 417), (26, 1, 465), (28, 1, 465), (30, 1, 515), (7, 1, 530), (14, 1, 874), (18, 1, 1265), (17, 1, 1266), (19, 1, 1273), (20, 1, 1314), (21, 1, 1315)]) (ids := [4, 8, 9, 13, 21, 7, 11, 20, 22, 23, 25, 27]) (cs := [1, 1, 1, 1, 2, 1, 1, 7, 3, 4, 1, 8, 1, 5, 1, 1, 1, 1, 1, 1, 9, 6, 10, 11, 1, 12, 1, 13, 1, 1]) (bs := [5, 7]) (W := 2432) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1934_5 : P.sumLeaves 24 1981248 64 = 2432 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 30957) rows (by decide) (by decide)).symm.trans contract1934_5

theorem c1934_6 : P.sumLeaves 24 1981312 128 = 114880 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1934) (lo := 896) (len := 128) (W := 114880) check rows elimOK (by decide) (by decide) cover1934 (by decide)
  decide +kernel

theorem h1934 : P.leaf 34 1934 = 146544 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(320, 0), (64, 1472), (64, 0), (64, 25600), (320, 2160), (64, 2432), (128, 114880)]) (.cons c1934_0 (.cons c1934_1 (.cons c1934_2 (.cons c1934_3 (.cons c1934_4 (.cons c1934_5 (.cons c1934_6 (.nil)))))))) (by decide) (by decide))

theorem cover1935 : P.CoversSplit 24 10 1935 0xaaaa0000000000000000000000000000a0a000000000000000000000000000000000000000000000008800000000000000000000000000000080000000000000aaaa0000000000000000000000000000a0a000000000000000000000000000000000000000000000008800000000000000000000000000000080000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [515, 517, 522, 528, 860, 916, 1209, 1258, 1259]) (ps := [(16, [566], [1258])]) (by decide +kernel)

theorem c1935_0 : P.sumLeaves 24 1981440 320 = 30064 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1935) (lo := 0) (len := 320) (W := 30064) check rows elimOK (by decide) (by decide) cover1935 (by decide)
  decide +kernel

theorem contract1935_1 : P.leaf 30 30965 = 0 := by
  exact leaf_contract_zero (ss := [(3, 1, 523), (26, 1, 528), (31, 1, 528), (16, 1, 529), (7, 1, 530), (8, 1, 615), (28, 1, 860), (12, 1, 867), (14, 1, 874), (30, 1, 1209), (18, 1, 1265)]) (q := 1266) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c1935_1 : P.sumLeaves 24 1981760 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 30965) rows (by decide) (by decide)).symm.trans contract1935_1

theorem c1935_2 : P.sumLeaves 24 1981824 448 = 463640 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1935) (lo := 384) (len := 448) (W := 463640) check rows elimOK (by decide) (by decide) cover1935 (by decide)
  decide +kernel

theorem contract1935_3 : P.leaf 30 30973 = 17024 := by
  exact leaf_contract_factors (k := 30) (b := 15) (H := 30973) (ss := [(3, 1, 523), (26, 1, 528), (31, 1, 528), (16, 1, 529), (7, 1, 530), (8, 1, 615), (28, 1, 860), (12, 1, 867), (14, 1, 874), (30, 1, 1209), (18, 1, 1265), (17, 1, 1266), (19, 1, 1273), (20, 1, 1314), (21, 1, 1315)]) (ids := [0, 2, 3, 4, 8, 9, 20, 21, 25, 27, 7, 11, 13, 22, 23]) (cs := [2, 1, 3, 4, 5, 1, 1, 12, 6, 7, 1, 13, 1, 14, 1, 1, 1, 1, 1, 1, 8, 9, 15, 16, 1, 10, 1, 11, 1, 1]) (bs := [10, 5]) (W := 17024) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1935_3 : P.sumLeaves 24 1982272 64 = 17024 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 30973) rows (by decide) (by decide)).symm.trans contract1935_3

theorem c1935_4 : P.sumLeaves 24 1982336 128 = 1535616 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1935) (lo := 896) (len := 128) (W := 1535616) check rows elimOK (by decide) (by decide) cover1935 (by decide)
  decide +kernel

theorem h1935 : P.leaf 34 1935 = 2046344 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(320, 30064), (64, 0), (448, 463640), (64, 17024), (128, 1535616)]) (.cons c1935_0 (.cons c1935_1 (.cons c1935_2 (.cons c1935_3 (.cons c1935_4 (.nil)))))) (by decide) (by decide))

theorem cover1939 : P.CoversSplit 24 10 1939 0xaaaa000000000000aaaa000000000000a0a0000000000000a0a0000000000000aa000000000000000000000000000000a0000000000000000000000000000000aaaa000000000000aaaa000000000000aaaa000000000000aaaa000000000000aa00000000000000000000000000000088000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [468, 517, 528, 915, 916, 1209, 1258]) (ps := [(14, [874, 1609], [860, 1266])]) (by decide +kernel)

theorem c1939_0 : P.sumLeaves 24 1985536 192 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1939) (lo := 0) (len := 192) (W := 0) check rows elimOK (by decide) (by decide) cover1939 (by decide)
  decide +kernel

theorem contract1939_1 : P.leaf 30 31027 = 2448 := by
  apply (leaf_contract (k := 30) (b := 14) (H := 31027) (ss := [(31, 1, 468), (6, 1, 478), (12, 1, 478), (2, 1, 480), (3, 1, 523), (26, 1, 528), (11, 1, 818), (29, 1, 916), (14, 1, 923), (18, 1, 923), (13, 1, 922), (19, 1, 929), (15, 1, 930), (30, 1, 1209), (16, 1, 1265), (17, 1, 1273)]) (ids := [2, 3, 5, 6, 7, 8, 18, 19, 20, 21, 22, 23, 25, 26]) (cs := [1, 1, 2, 3, 1, 4, 5, 6, 7, 1, 1, 1, 1, 1, 1, 1, 1, 1, 8, 9, 10, 11, 12, 13, 1, 14, 15, 1, 1, 1]) check rows (by decide) (by decide +kernel) (by decide +kernel)).trans
  decide +kernel

theorem c1939_1 : P.sumLeaves 24 1985728 64 = 2448 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 31027) rows (by decide) (by decide)).symm.trans contract1939_1

theorem contract1939_2 : P.leaf 30 31028 = 400 := by
  apply (leaf_contract (k := 30) (b := 14) (H := 31028) (ss := [(31, 1, 468), (6, 1, 478), (12, 1, 478), (5, 1, 523), (26, 1, 528), (11, 1, 818), (30, 1, 1209), (16, 1, 1258), (7, 1, 530), (13, 1, 922), (18, 1, 922), (8, 0, 1266), (14, 0, 531), (20, 1, 628), (10, 1, 811), (21, 0, 874)]) (ids := [0, 1, 2, 7, 13, 15, 17, 20, 21, 22, 23, 25, 26, 27]) (cs := [2, 3, 4, 1, 1, 1, 0, 5, 1, 1, 1, 1, 0, 6, 1, 7, 1, 8, 1, 0, 9, 10, 11, 12, 1, 13, 14, 15, 1, 1]) check rows (by decide) (by decide +kernel) (by decide +kernel)).trans
  decide +kernel

theorem c1939_2 : P.sumLeaves 24 1985792 64 = 400 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 31028) rows (by decide) (by decide)).symm.trans contract1939_2

theorem c1939_3 : P.sumLeaves 24 1985856 128 = 24722 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1939) (lo := 320) (len := 128) (W := 24722) check rows elimOK (by decide) (by decide) cover1939 (by decide)
  decide +kernel

theorem contract1939_4 : P.leaf 30 31031 = 34368 := by
  apply (leaf_contract (k := 30) (b := 17) (H := 31031) (ss := [(31, 1, 468), (6, 1, 478), (12, 1, 478), (26, 1, 528), (11, 1, 818), (14, 1, 923), (18, 1, 923), (19, 1, 929), (30, 1, 1209), (16, 1, 1265), (13, 1, 922), (17, 1, 1273), (15, 1, 930)]) (ids := [0, 1, 2, 3, 5, 6, 7, 8, 18, 19, 20, 21, 22, 23, 25, 26, 27]) (cs := [2, 3, 4, 5, 1, 6, 7, 8, 9, 1, 1, 1, 1, 1, 1, 1, 1, 1, 10, 11, 12, 13, 14, 15, 1, 16, 17, 18, 1, 1]) check rows (by decide) (by decide +kernel) (by decide +kernel)).trans
  decide +kernel

theorem c1939_4 : P.sumLeaves 24 1985984 64 = 34368 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 31031) rows (by decide) (by decide)).symm.trans contract1939_4

theorem c1939_5 : P.sumLeaves 24 1986048 256 = 14208 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1939) (lo := 512) (len := 256) (W := 14208) check rows elimOK (by decide) (by decide) cover1939 (by decide)
  decide +kernel

theorem contract1939_6 : P.leaf 30 31036 = 2112 := by
  exact leaf_contract_factors (k := 30) (b := 12) (H := 31036) (ss := [(31, 1, 468), (6, 1, 478), (12, 1, 478), (5, 1, 523), (26, 1, 528), (8, 1, 531), (16, 1, 531), (7, 1, 530), (17, 1, 537), (9, 1, 538), (11, 1, 818), (14, 1, 874), (28, 1, 860), (30, 1, 1209), (18, 1, 1265), (19, 1, 1273), (20, 1, 1314), (21, 1, 1315)]) (ids := [0, 1, 2, 20, 23, 25, 27, 8, 13, 11, 21, 22]) (cs := [2, 3, 4, 1, 1, 1, 1, 1, 9, 1, 1, 11, 1, 10, 1, 1, 1, 1, 1, 1, 5, 12, 13, 6, 1, 7, 1, 8, 1, 1]) (bs := [7, 2, 3]) (W := 2112) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1939_6 : P.sumLeaves 24 1986304 64 = 2112 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 31036) rows (by decide) (by decide)).symm.trans contract1939_6

theorem contract1939_7 : P.leaf 30 31037 = 3072 := by
  exact leaf_contract_factors (k := 30) (b := 13) (H := 31037) (ss := [(31, 1, 468), (6, 1, 478), (12, 1, 478), (26, 1, 528), (8, 1, 531), (16, 1, 531), (7, 1, 530), (17, 1, 537), (9, 1, 538), (11, 1, 818), (14, 1, 874), (28, 1, 860), (30, 1, 1209), (18, 1, 1265), (19, 1, 1273), (20, 1, 1314), (21, 1, 1315)]) (ids := [0, 1, 2, 3, 8, 13, 20, 27, 11, 21, 22, 23, 25]) (cs := [2, 3, 4, 5, 1, 1, 1, 1, 6, 1, 1, 10, 1, 7, 1, 1, 1, 1, 1, 1, 8, 11, 12, 13, 1, 14, 1, 9, 1, 1]) (bs := [8, 5]) (W := 3072) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1939_7 : P.sumLeaves 24 1986368 64 = 3072 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 31037) rows (by decide) (by decide)).symm.trans contract1939_7

theorem c1939_8 : P.sumLeaves 24 1986432 128 = 272256 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1939) (lo := 896) (len := 128) (W := 272256) check rows elimOK (by decide) (by decide) cover1939 (by decide)
  decide +kernel

theorem h1939 : P.leaf 34 1939 = 353586 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(192, 0), (64, 2448), (64, 400), (128, 24722), (64, 34368), (256, 14208), (64, 2112), (64, 3072), (128, 272256)]) (.cons c1939_0 (.cons c1939_1 (.cons c1939_2 (.cons c1939_3 (.cons c1939_4 (.cons c1939_5 (.cons c1939_6 (.cons c1939_7 (.cons c1939_8 (.nil)))))))))) (by decide) (by decide))

theorem cover1940 : P.CoversSplit 24 10 1940 0xaa00000000000000aa00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000aa00000000000000aa00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 468, 473, 475, 479, 516, 559, 867, 872, 915, 916, 1209, 1258]) (by decide +kernel)

theorem c1940_0 : P.sumLeaves 24 1986560 384 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1940) (lo := 0) (len := 384) (W := 0) check rows elimOK (by decide) (by decide) cover1940 (by decide)
  decide +kernel

theorem contract1940_1 : P.leaf 30 31046 = 2880 := by
  exact leaf_contract_factors (k := 30) (b := 14) (H := 31046) (ss := [(29, 2, 475), (26, 1, 479), (2, 1, 480), (16, 3, 486), (3, 1, 509), (5, 1, 524), (31, 1, 516), (11, 1, 901), (6, 1, 458), (10, 1, 458), (12, 1, 818), (13, 1, 922), (18, 1, 922), (14, 1, 929), (19, 1, 929), (30, 1, 1209)]) (ids := [2, 5, 6, 7, 13, 15, 18, 19, 20, 22, 23, 25, 26, 21]) (cs := [1, 1, 2, 1, 1, 3, 4, 5, 1, 1, 1, 1, 1, 6, 1, 7, 1, 1, 8, 9, 10, 15, 11, 12, 1, 13, 14, 1, 1, 1]) (bs := [13, 1]) (W := 2880) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1940_1 : P.sumLeaves 24 1986944 64 = 2880 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 31046) rows (by decide) (by decide)).symm.trans contract1940_1

theorem contract1940_2 : P.leaf 30 31047 = 4608 := by
  exact leaf_contract_factors (k := 30) (b := 14) (H := 31047) (ss := [(29, 2, 475), (26, 1, 479), (2, 1, 480), (16, 3, 486), (3, 1, 509), (31, 1, 872), (11, 1, 901), (6, 1, 458), (10, 1, 458), (12, 1, 818), (13, 1, 922), (18, 1, 922), (14, 1, 929), (19, 1, 929), (30, 1, 1209), (17, 1, 1273)]) (ids := [2, 3, 5, 6, 7, 13, 18, 19, 20, 22, 23, 25, 26, 21]) (cs := [1, 1, 2, 3, 1, 4, 5, 6, 1, 1, 1, 1, 1, 7, 1, 1, 1, 1, 8, 9, 10, 15, 11, 12, 1, 13, 14, 1, 1, 1]) (bs := [13, 1]) (W := 4608) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1940_2 : P.sumLeaves 24 1987008 64 = 4608 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 31047) rows (by decide) (by decide)).symm.trans contract1940_2

theorem c1940_3 : P.sumLeaves 24 1987072 384 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1940) (lo := 512) (len := 384) (W := 0) check rows elimOK (by decide) (by decide) cover1940 (by decide)
  decide +kernel

theorem contract1940_4 : P.leaf 30 31054 = 18144 := by
  exact leaf_contract_factors (k := 30) (b := 18) (H := 31054) (ss := [(29, 1, 475), (26, 1, 479), (16, 3, 486), (3, 1, 509), (5, 1, 524), (2, 1, 409), (31, 1, 516), (11, 1, 901), (6, 1, 458), (10, 1, 458), (12, 1, 818), (30, 1, 1209)]) (ids := [2, 5, 6, 7, 11, 12, 13, 15, 16, 17, 18, 19, 20, 22, 23, 25, 26, 21]) (cs := [1, 1, 2, 1, 1, 3, 4, 5, 1, 1, 1, 6, 7, 8, 1, 9, 10, 11, 12, 13, 14, 19, 15, 16, 1, 17, 18, 1, 1, 1]) (bs := [17, 1]) (W := 18144) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1940_4 : P.sumLeaves 24 1987456 64 = 18144 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 31054) rows (by decide) (by decide)).symm.trans contract1940_4

theorem c1940_5 : P.sumLeaves 24 1987520 64 = 30208 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1940) (lo := 960) (len := 64) (W := 30208) check rows elimOK (by decide) (by decide) cover1940 (by decide)
  decide +kernel

theorem h1940 : P.leaf 34 1940 = 55840 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(384, 0), (64, 2880), (64, 4608), (384, 0), (64, 18144), (64, 30208)]) (.cons c1940_0 (.cons c1940_1 (.cons c1940_2 (.cons c1940_3 (.cons c1940_4 (.cons c1940_5 (.nil))))))) (by decide) (by decide))

theorem cover1941 : P.CoversSplit 24 10 1941 0xaa00000000000000aa00000000000000a000000000000000a0000000000000000000000000000000000000000000000000000000000000000000000000000000aa00000000000000aa00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [468, 473, 475, 516, 517, 528, 559, 860, 915, 916, 1209, 1258]) (ps := [(14, [923], [1266])]) (by decide +kernel)

theorem c1941_0 : P.sumLeaves 24 1987584 384 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1941) (lo := 0) (len := 384) (W := 0) check rows elimOK (by decide) (by decide) cover1941 (by decide)
  decide +kernel

theorem contract1941_1 : P.leaf 30 31062 = 26880 := by
  exact leaf_contract_factors (k := 30) (b := 17) (H := 31062) (ss := [(29, 2, 475), (2, 1, 480), (5, 1, 524), (26, 1, 528), (31, 1, 517), (11, 1, 901), (12, 1, 818), (14, 1, 929), (19, 1, 929), (18, 1, 965), (13, 1, 922), (30, 1, 1209), (16, 1, 1265)]) (ids := [2, 4, 5, 6, 7, 8, 13, 15, 18, 19, 20, 21, 22, 23, 25, 26, 1]) (cs := [1, 18, 2, 1, 3, 4, 5, 6, 7, 1, 1, 1, 1, 8, 1, 9, 1, 1, 10, 11, 12, 13, 14, 15, 1, 16, 17, 1, 1, 1]) (bs := [16, 1]) (W := 26880) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1941_1 : P.sumLeaves 24 1987968 64 = 26880 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 31062) rows (by decide) (by decide)).symm.trans contract1941_1

theorem contract1941_2 : P.leaf 30 31063 = 32256 := by
  apply (leaf_contract (k := 30) (b := 17) (H := 31063) (ss := [(29, 2, 475), (2, 1, 480), (26, 1, 528), (31, 1, 528), (11, 1, 901), (12, 1, 818), (14, 1, 929), (19, 1, 929), (18, 1, 965), (13, 1, 922), (30, 1, 1209), (16, 1, 1265), (17, 1, 1273)]) (ids := [1, 2, 3, 4, 5, 6, 7, 8, 13, 18, 19, 20, 21, 22, 23, 25, 26]) (cs := [1, 2, 3, 4, 5, 6, 7, 8, 9, 1, 1, 1, 1, 10, 1, 1, 1, 1, 11, 12, 13, 14, 15, 16, 1, 17, 18, 1, 1, 1]) check rows (by decide) (by decide +kernel) (by decide +kernel)).trans
  decide +kernel

theorem c1941_2 : P.sumLeaves 24 1988032 64 = 32256 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 31063) rows (by decide) (by decide)).symm.trans contract1941_2

theorem c1941_3 : P.sumLeaves 24 1988096 512 = 421676 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1941) (lo := 512) (len := 512) (W := 421676) check rows elimOK (by decide) (by decide) cover1941 (by decide)
  decide +kernel

theorem h1941 : P.leaf 34 1941 = 480812 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(384, 0), (64, 26880), (64, 32256), (512, 421676)]) (.cons c1941_0 (.cons c1941_1 (.cons c1941_2 (.cons c1941_3 (.nil))))) (by decide) (by decide))

theorem cover1942 : P.CoversSplit 24 10 1942 0xaaaa000000000000aaaa00000000000000000000000000000000000000000000aa88000000000000000000000000000000000000000000000000000000000000aaaa000000000000aaaa000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 468, 479, 516, 867, 872, 915, 916, 1209, 1258]) (by decide +kernel)

theorem c1942_0 : P.sumLeaves 24 1988608 1024 = 805796 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1942) (lo := 0) (len := 1024) (W := 805796) check rows elimOK (by decide) (by decide) cover1942 (by decide)
  decide +kernel

theorem h1942 : P.leaf 34 1942 = 805796 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 805796)]) (.cons c1942_0 (.nil)) (by decide) (by decide))

theorem cover1943 : P.CoversSplit 24 10 1943 0xaaaa000000000000aaaa000000000000a0a0000000000000a0a0000000000000aa880000000000000000000000000000a0800000000000000000000000000000aaaa000000000000aaaa00000000000000000000000000000000000000000000aa88000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [468, 516, 517, 528, 860, 915, 916, 1209, 1258]) (ps := [(8, [1609], [1266]), (14, [965], [1266])]) (by decide +kernel)

theorem c1943_0 : P.sumLeaves 24 1989632 768 = 668704 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1943) (lo := 0) (len := 768) (W := 668704) check rows elimOK (by decide) (by decide) cover1943 (by decide)
  decide +kernel

theorem contract1943_1 : P.leaf 30 31100 = 9568 := by
  exact leaf_contract_factors (k := 30) (b := 15) (H := 31100) (ss := [(31, 1, 468), (5, 1, 524), (26, 1, 528), (8, 1, 531), (16, 1, 531), (7, 1, 530), (17, 1, 615), (9, 1, 538), (28, 1, 860), (14, 1, 874), (30, 1, 1209), (18, 1, 1265), (19, 1, 1273), (20, 1, 1314), (21, 1, 1315)]) (ids := [0, 1, 2, 4, 8, 9, 10, 11, 13, 20, 21, 23, 25, 27, 22]) (cs := [2, 3, 4, 1, 5, 1, 1, 1, 6, 7, 8, 9, 1, 10, 1, 1, 1, 1, 1, 1, 11, 12, 16, 13, 1, 14, 1, 15, 1, 1]) (bs := [14, 1]) (W := 9568) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1943_1 : P.sumLeaves 24 1990400 64 = 9568 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 31100) rows (by decide) (by decide)).symm.trans contract1943_1

theorem contract1943_2 : P.leaf 30 31101 = 14288 := by
  exact leaf_contract_factors (k := 30) (b := 16) (H := 31101) (ss := [(31, 1, 468), (26, 1, 528), (8, 1, 531), (16, 1, 531), (7, 1, 530), (17, 1, 615), (9, 1, 538), (28, 1, 860), (14, 1, 874), (30, 1, 1209), (18, 1, 1265), (19, 1, 1273), (20, 1, 1314), (21, 1, 1315)]) (ids := [0, 1, 2, 3, 4, 8, 9, 10, 11, 13, 20, 21, 25, 27, 22, 23]) (cs := [2, 3, 4, 5, 6, 1, 1, 1, 7, 8, 9, 10, 1, 11, 1, 1, 1, 1, 1, 1, 12, 13, 16, 17, 1, 14, 1, 15, 1, 1]) (bs := [14, 2]) (W := 14288) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1943_2 : P.sumLeaves 24 1990464 64 = 14288 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 31101) rows (by decide) (by decide)).symm.trans contract1943_2

theorem c1943_3 : P.sumLeaves 24 1990528 128 = 2088528 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1943) (lo := 896) (len := 128) (W := 2088528) check rows elimOK (by decide) (by decide) cover1943 (by decide)
  decide +kernel

theorem h1943 : P.leaf 34 1943 = 2781088 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(768, 668704), (64, 9568), (64, 14288), (128, 2088528)]) (.cons c1943_0 (.cons c1943_1 (.cons c1943_2 (.cons c1943_3 (.nil))))) (by decide) (by decide))

theorem cover1944 : P.CoversSplit 24 10 1944 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [509]) (by decide +kernel)

theorem c1944_0 : P.sumLeaves 24 1990656 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1944) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1944 (by decide)
  decide +kernel

theorem h1944 : P.leaf 34 1944 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1944_0 (.nil)) (by decide) (by decide))

theorem cover1945 : P.CoversSplit 24 10 1945 0xaa00000000000000aa00000000000000a000000000000000a0000000000000000000000000000000000000000000000000000000000000000000000000000000aa00000000000000aa00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 474, 516, 517, 528, 915, 1209, 1258]) (ps := [(8, [615], [1266]), (14, [874, 923], [558, 860])]) (by decide +kernel)

theorem c1945_0 : P.sumLeaves 24 1991680 384 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1945) (lo := 0) (len := 384) (W := 0) check rows elimOK (by decide) (by decide) cover1945 (by decide)
  decide +kernel

theorem contract1945_1 : P.leaf 30 31126 = 23296 := by
  exact leaf_contract_factors (k := 30) (b := 17) (H := 31126) (ss := [(29, 2, 474), (12, 1, 486), (5, 1, 523), (26, 1, 528), (31, 1, 517), (11, 1, 901), (14, 1, 923), (2, 1, 487), (18, 1, 923), (19, 1, 965), (15, 1, 930), (30, 1, 1209), (17, 1, 1273)]) (ids := [2, 4, 5, 6, 7, 8, 11, 14, 18, 19, 20, 21, 22, 23, 25, 26, 1]) (cs := [1, 18, 2, 1, 3, 4, 5, 6, 7, 1, 1, 8, 1, 1, 9, 1, 1, 1, 10, 11, 12, 13, 14, 15, 1, 16, 17, 1, 1, 1]) (bs := [16, 1]) (W := 23296) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1945_1 : P.sumLeaves 24 1992064 64 = 23296 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 31126) rows (by decide) (by decide)).symm.trans contract1945_1

theorem contract1945_2 : P.leaf 30 31127 = 28032 := by
  apply (leaf_contract (k := 30) (b := 17) (H := 31127) (ss := [(29, 2, 474), (12, 1, 486), (26, 1, 528), (31, 1, 528), (11, 1, 901), (2, 1, 915), (14, 1, 923), (18, 1, 923), (19, 1, 965), (15, 1, 930), (30, 1, 1209), (16, 1, 1265), (17, 1, 1273)]) (ids := [1, 2, 3, 4, 5, 6, 7, 8, 11, 18, 19, 20, 21, 22, 23, 25, 26]) (cs := [1, 2, 3, 4, 5, 6, 7, 8, 9, 1, 1, 10, 1, 1, 1, 1, 1, 1, 11, 12, 13, 14, 15, 16, 1, 17, 18, 1, 1, 1]) check rows (by decide) (by decide +kernel) (by decide +kernel)).trans
  decide +kernel

theorem c1945_2 : P.sumLeaves 24 1992128 64 = 28032 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 31127) rows (by decide) (by decide)).symm.trans contract1945_2

theorem c1945_3 : P.sumLeaves 24 1992192 512 = 303536 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1945) (lo := 512) (len := 512) (W := 303536) check rows elimOK (by decide) (by decide) cover1945 (by decide)
  decide +kernel

theorem h1945 : P.leaf 34 1945 = 354864 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(384, 0), (64, 23296), (64, 28032), (512, 303536)]) (.cons c1945_0 (.cons c1945_1 (.cons c1945_2 (.cons c1945_3 (.nil))))) (by decide) (by decide))

theorem cover1946 : P.CoversSplit 24 10 1946 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [509]) (by decide +kernel)

theorem c1946_0 : P.sumLeaves 24 1992704 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1946) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1946 (by decide)
  decide +kernel

theorem h1946 : P.leaf 34 1946 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1946_0 (.nil)) (by decide) (by decide))

theorem cover1947 : P.CoversSplit 24 10 1947 0xaaaa000000000000aaaa000000000000a0a0000000000000a0a0000000000000aa000000000000000000000000000000a0000000000000000000000000000000aaaa000000000000aaaa00000000000000000000000000000000000000000000aa00000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [516, 517, 528, 915, 916, 1209, 1258]) (ps := [(8, [615], [1266]), (14, [874], [860])]) (by decide +kernel)

theorem c1947_0 : P.sumLeaves 24 1993728 192 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1947) (lo := 0) (len := 192) (W := 0) check rows elimOK (by decide) (by decide) cover1947 (by decide)
  decide +kernel

theorem contract1947_1 : P.leaf 30 31155 = 7952 := by
  apply (leaf_contract (k := 30) (b := 16) (H := 31155) (ss := [(12, 1, 486), (2, 1, 487), (3, 1, 523), (26, 1, 528), (31, 1, 528), (11, 1, 901), (29, 1, 916), (14, 1, 923), (18, 1, 923), (19, 1, 965), (15, 1, 930), (30, 1, 1209), (16, 1, 1265), (17, 1, 1273)]) (ids := [2, 3, 4, 5, 6, 7, 8, 11, 18, 19, 20, 21, 22, 23, 25, 26]) (cs := [1, 1, 2, 3, 4, 5, 6, 7, 8, 1, 1, 9, 1, 1, 1, 1, 1, 1, 10, 11, 12, 13, 14, 15, 1, 16, 17, 1, 1, 1]) check rows (by decide) (by decide +kernel) (by decide +kernel)).trans
  decide +kernel

theorem c1947_1 : P.sumLeaves 24 1993920 64 = 7952 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 31155) rows (by decide) (by decide)).symm.trans contract1947_1

theorem c1947_2 : P.sumLeaves 24 1993984 512 = 228320 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1947) (lo := 256) (len := 512) (W := 228320) check rows elimOK (by decide) (by decide) cover1947 (by decide)
  decide +kernel

theorem contract1947_3 : P.leaf 30 31164 = 6624 := by
  exact leaf_contract_factors (k := 30) (b := 14) (H := 31164) (ss := [(31, 12, 486), (12, 1, 509), (5, 1, 523), (26, 1, 528), (8, 1, 531), (16, 1, 531), (7, 1, 530), (17, 1, 537), (11, 1, 818), (14, 1, 874), (28, 1, 860), (30, 1, 1209), (18, 1, 1265), (19, 1, 1273), (20, 1, 1314), (21, 1, 1315)]) (ids := [0, 1, 2, 20, 23, 25, 27, 4, 8, 13, 21, 7, 11, 22]) (cs := [2, 3, 4, 1, 9, 1, 1, 13, 10, 1, 1, 14, 1, 11, 1, 1, 1, 1, 1, 1, 5, 12, 15, 6, 1, 7, 1, 8, 1, 1]) (bs := [7, 4, 3]) (W := 6624) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1947_3 : P.sumLeaves 24 1994496 64 = 6624 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 31164) rows (by decide) (by decide)).symm.trans contract1947_3

theorem contract1947_4 : P.leaf 30 31165 = 9920 := by
  exact leaf_contract_factors (k := 30) (b := 15) (H := 31165) (ss := [(31, 12, 486), (12, 1, 509), (26, 1, 528), (8, 1, 531), (16, 1, 531), (7, 1, 530), (17, 1, 537), (11, 1, 818), (14, 1, 874), (28, 1, 860), (30, 1, 1209), (18, 1, 1265), (19, 1, 1273), (20, 1, 1314), (21, 1, 1315)]) (ids := [0, 1, 2, 3, 4, 8, 13, 20, 27, 7, 11, 21, 22, 23, 25]) (cs := [2, 3, 4, 5, 6, 1, 1, 11, 7, 1, 1, 12, 1, 8, 1, 1, 1, 1, 1, 1, 9, 13, 14, 15, 1, 16, 1, 10, 1, 1]) (bs := [9, 6]) (W := 9920) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1947_4 : P.sumLeaves 24 1994560 64 = 9920 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 31165) rows (by decide) (by decide)).symm.trans contract1947_4

theorem c1947_5 : P.sumLeaves 24 1994624 128 = 838576 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1947) (lo := 896) (len := 128) (W := 838576) check rows elimOK (by decide) (by decide) cover1947 (by decide)
  decide +kernel

theorem h1947 : P.leaf 34 1947 = 1091392 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(192, 0), (64, 7952), (512, 228320), (64, 6624), (64, 9920), (128, 838576)]) (.cons c1947_0 (.cons c1947_1 (.cons c1947_2 (.cons c1947_3 (.cons c1947_4 (.cons c1947_5 (.nil))))))) (by decide) (by decide))

theorem cover1948 : P.CoversSplit 24 10 1948 0xaa00000000000000aa22000000000000a000000000000000a0000000000000000000000000000000000000000000000000000000000000000000000000000000aa00000000000000aa22000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 508, 516, 860, 867, 872, 915, 1209, 1251, 1258]) (ps := [(8, [537], [1266]), (14, [874], [915])]) (by decide +kernel)

theorem c1948_0 : P.sumLeaves 24 1994752 448 = 17420 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1948) (lo := 0) (len := 448) (W := 17420) check rows elimOK (by decide) (by decide) cover1948 (by decide)
  decide +kernel

theorem contract1948_1 : P.leaf 30 31175 = 21984 := by
  exact leaf_contract_factors (k := 30) (b := 18) (H := 31175) (ss := [(3, 1, 486), (31, 1, 872), (11, 1, 901), (12, 1, 818), (6, 1, 459), (29, 1, 915), (30, 1, 1251), (26, 1, 516), (18, 1, 1266), (16, 1, 1265), (19, 1, 1272), (17, 1, 1273)]) (ids := [0, 2, 3, 5, 6, 7, 8, 11, 12, 13, 18, 19, 20, 21, 22, 25, 26, 23]) (cs := [2, 1, 3, 4, 1, 5, 6, 7, 8, 1, 1, 9, 10, 11, 1, 1, 1, 1, 12, 13, 14, 15, 16, 19, 1, 17, 18, 1, 1, 1]) (bs := [17, 1]) (W := 21984) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1948_1 : P.sumLeaves 24 1995200 64 = 21984 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 31175) rows (by decide) (by decide)).symm.trans contract1948_1

theorem c1948_2 : P.sumLeaves 24 1995264 512 = 195036 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1948) (lo := 512) (len := 512) (W := 195036) check rows elimOK (by decide) (by decide) cover1948 (by decide)
  decide +kernel

theorem h1948 : P.leaf 34 1948 = 234440 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(448, 17420), (64, 21984), (512, 195036)]) (.cons c1948_0 (.cons c1948_1 (.cons c1948_2 (.nil)))) (by decide) (by decide))

theorem cover1949 : P.CoversSplit 24 10 1949 0xaa00000000000000aa22000000000000a000000000000000a0000000000000000000000000000000000000000000000000000000000000000000000000000000aa00000000000000aa22000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 516, 517, 528, 860, 915, 1209, 1258]) (ps := [(8, [615], [1266]), (14, [874], [915])]) (by decide +kernel)

theorem c1949_0 : P.sumLeaves 24 1995776 1024 = 2054128 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1949) (lo := 0) (len := 1024) (W := 2054128) check rows elimOK (by decide) (by decide) cover1949 (by decide)
  decide +kernel

theorem h1949 : P.leaf 34 1949 = 2054128 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 2054128)]) (.cons c1949_0 (.nil)) (by decide) (by decide))

theorem cover1950 : P.CoversSplit 24 10 1950 0xaaaa000000000000aaaa000000000000a0a0000000000000a0a0000000000000aa880000000000000000000000000000a0800000000000000000000000000000aaaa000000000000aaaa000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 516, 860, 867, 872, 915, 916, 1209, 1251, 1258]) (ps := [(8, [537], [1266])]) (by decide +kernel)

theorem c1950_0 : P.sumLeaves 24 1996800 768 = 645704 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1950) (lo := 0) (len := 768) (W := 645704) check rows elimOK (by decide) (by decide) cover1950 (by decide)
  decide +kernel

theorem contract1950_1 : P.leaf 30 31212 = 10632 := by
  exact leaf_contract_factors (k := 30) (b := 16) (H := 31212) (ss := [(16, 1, 468), (3, 1, 486), (8, 1, 531), (31, 1, 872), (26, 1, 516), (7, 1, 530), (28, 1, 860), (14, 1, 874), (30, 1, 1209), (18, 1, 1265), (17, 1, 1266), (19, 1, 1273), (20, 1, 1314), (21, 1, 1315)]) (ids := [0, 2, 3, 4, 7, 8, 9, 10, 11, 13, 20, 21, 23, 25, 27, 22]) (cs := [2, 1, 3, 4, 5, 1, 1, 6, 7, 8, 9, 10, 1, 11, 1, 1, 1, 1, 1, 1, 12, 13, 17, 14, 1, 15, 1, 16, 1, 1]) (bs := [15, 1]) (W := 10632) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1950_1 : P.sumLeaves 24 1997568 64 = 10632 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 31212) rows (by decide) (by decide)).symm.trans contract1950_1

theorem contract1950_2 : P.leaf 30 31213 = 16544 := by
  exact leaf_contract_factors (k := 30) (b := 16) (H := 31213) (ss := [(16, 1, 468), (3, 1, 486), (8, 1, 531), (31, 1, 872), (26, 1, 516), (7, 1, 530), (28, 1, 860), (14, 1, 874), (30, 1, 1209), (18, 1, 1265), (17, 1, 1266), (19, 1, 1273), (20, 1, 1314), (21, 1, 1315)]) (ids := [0, 2, 3, 4, 7, 8, 9, 10, 11, 13, 20, 21, 25, 27, 22, 23]) (cs := [2, 1, 3, 4, 5, 1, 1, 6, 7, 8, 9, 10, 1, 11, 1, 1, 1, 1, 1, 1, 12, 13, 16, 17, 1, 14, 1, 15, 1, 1]) (bs := [14, 2]) (W := 16544) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1950_2 : P.sumLeaves 24 1997632 64 = 16544 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 31213) rows (by decide) (by decide)).symm.trans contract1950_2

theorem c1950_3 : P.sumLeaves 24 1997696 128 = 1883780 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1950) (lo := 896) (len := 128) (W := 1883780) check rows elimOK (by decide) (by decide) cover1950 (by decide)
  decide +kernel

theorem h1950 : P.leaf 34 1950 = 2556660 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(768, 645704), (64, 10632), (64, 16544), (128, 1883780)]) (.cons c1950_0 (.cons c1950_1 (.cons c1950_2 (.cons c1950_3 (.nil))))) (by decide) (by decide))

theorem cover1951 : P.CoversSplit 24 10 1951 0xaaaa000000000000aaaa000000000000a0a0000000000000a0a0000000000000aa880000000000000000000000000000a0800000000000000000000000000000aaaa000000000000aaaa00000000000000000000000000000000000000000000aa88000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [516, 517, 528, 860, 915, 916, 1209, 1258]) (ps := [(8, [615], [1266])]) (by decide +kernel)

theorem c1951_0 : P.sumLeaves 24 1997824 768 = 2839028 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1951) (lo := 0) (len := 768) (W := 2839028) check rows elimOK (by decide) (by decide) cover1951 (by decide)
  decide +kernel

theorem contract1951_1 : P.leaf 30 31228 = 27648 := by
  exact leaf_contract_factors (k := 30) (b := 17) (H := 31228) (ss := [(26, 1, 528), (31, 1, 528), (8, 1, 531), (16, 1, 531), (7, 1, 530), (28, 1, 860), (14, 1, 874), (30, 1, 1209), (18, 1, 1265), (17, 1, 1266), (19, 1, 1273), (20, 1, 1314), (21, 1, 1315)]) (ids := [0, 1, 2, 3, 4, 7, 8, 9, 10, 11, 13, 20, 21, 23, 25, 27, 22]) (cs := [2, 3, 4, 5, 6, 1, 1, 7, 8, 9, 10, 11, 1, 12, 1, 1, 1, 1, 1, 1, 13, 14, 18, 15, 1, 16, 1, 17, 1, 1]) (bs := [16, 1]) (W := 27648) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1951_1 : P.sumLeaves 24 1998592 64 = 27648 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 31228) rows (by decide) (by decide)).symm.trans contract1951_1

theorem contract1951_2 : P.leaf 30 31229 = 35744 := by
  exact leaf_contract_factors (k := 30) (b := 17) (H := 31229) (ss := [(26, 1, 528), (31, 1, 528), (8, 1, 531), (16, 1, 531), (7, 1, 530), (28, 1, 860), (14, 1, 874), (30, 1, 1209), (18, 1, 1265), (17, 1, 1266), (19, 1, 1273), (20, 1, 1314), (21, 1, 1315)]) (ids := [0, 1, 2, 3, 4, 7, 8, 9, 10, 11, 13, 20, 21, 25, 27, 22, 23]) (cs := [2, 3, 4, 5, 6, 1, 1, 7, 8, 9, 10, 11, 1, 12, 1, 1, 1, 1, 1, 1, 13, 14, 17, 18, 1, 15, 1, 16, 1, 1]) (bs := [15, 2]) (W := 35744) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1951_2 : P.sumLeaves 24 1998656 64 = 35744 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 31229) rows (by decide) (by decide)).symm.trans contract1951_2

theorem c1951_3 : P.sumLeaves 24 1998720 128 = 6089310 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1951) (lo := 896) (len := 128) (W := 6089310) check rows elimOK (by decide) (by decide) cover1951 (by decide)
  decide +kernel

theorem h1951 : P.leaf 34 1951 = 8991730 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(768, 2839028), (64, 27648), (64, 35744), (128, 6089310)]) (.cons c1951_0 (.cons c1951_1 (.cons c1951_2 (.cons c1951_3 (.nil))))) (by decide) (by decide))

theorem cover1956 : P.CoversSplit 24 10 1956 0x8800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000088000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 468, 473, 475, 508, 515, 522, 524, 566, 872, 915]) (by decide +kernel)

theorem c1956_0 : P.sumLeaves 24 2002944 1024 = 31040 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1956) (lo := 0) (len := 1024) (W := 31040) check rows elimOK (by decide) (by decide) cover1956 (by decide)
  decide +kernel

theorem h1956 : P.leaf 34 1956 = 31040 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 31040)]) (.cons c1956_0 (.nil)) (by decide) (by decide))

theorem cover1957 : P.CoversSplit 24 10 1957 0xcc000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [468, 473, 475, 515, 517, 522, 566, 860, 872, 915, 916, 1209, 1251, 1308]) (by decide +kernel)

theorem c1957_0 : P.sumLeaves 24 2003968 448 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1957) (lo := 0) (len := 448) (W := 0) check rows elimOK (by decide) (by decide) cover1957 (by decide)
  decide +kernel

theorem contract1957_1 : P.leaf 30 31319 = 29848 := by
  exact leaf_contract_factors (k := 30) (b := 17) (H := 31319) (ss := [(27, 1, 473), (29, 1, 473), (2, 1, 475), (3, 1, 524), (12, 1, 867), (31, 1, 872), (11, 1, 901), (14, 1, 929), (19, 1, 929), (18, 1, 965), (13, 1, 922), (30, 1, 1209), (16, 1, 1265)]) (ids := [2, 3, 4, 6, 7, 8, 13, 15, 18, 19, 20, 21, 22, 23, 24, 26, 5]) (cs := [1, 1, 2, 3, 4, 18, 5, 6, 7, 1, 1, 1, 1, 8, 1, 9, 1, 1, 10, 11, 12, 13, 14, 15, 16, 1, 17, 1, 1, 1]) (bs := [16, 1]) (W := 29848) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1957_1 : P.sumLeaves 24 2004416 64 = 29848 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 31319) rows (by decide) (by decide)).symm.trans contract1957_1

theorem c1957_2 : P.sumLeaves 24 2004480 512 = 227536 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1957) (lo := 512) (len := 512) (W := 227536) check rows elimOK (by decide) (by decide) cover1957 (by decide)
  decide +kernel

theorem h1957 : P.leaf 34 1957 = 257384 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(448, 0), (64, 29848), (512, 227536)]) (.cons c1957_0 (.cons c1957_1 (.cons c1957_2 (.nil)))) (by decide) (by decide))

theorem cover1958 : P.CoversSplit 24 10 1958 0xaaaa0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000aaaa0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 468, 515, 522, 524, 566, 860, 872, 916, 1202, 1258]) (by decide +kernel)

theorem c1958_0 : P.sumLeaves 24 2004992 1024 = 547192 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1958) (lo := 0) (len := 1024) (W := 547192) check rows elimOK (by decide) (by decide) cover1958 (by decide)
  decide +kernel

theorem h1958 : P.leaf 34 1958 = 547192 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 547192)]) (.cons c1958_0 (.nil)) (by decide) (by decide))

theorem cover1959 : P.CoversSplit 24 10 1959 0xffff0000000000000000000000000000a0a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [468, 515, 517, 522, 524, 566, 860, 872, 915, 916, 1209, 1251, 1258, 1259, 1308]) (by decide +kernel)

theorem c1959_0 : P.sumLeaves 24 2006016 832 = 264248 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1959) (lo := 0) (len := 832) (W := 264248) check rows elimOK (by decide) (by decide) cover1959 (by decide)
  decide +kernel

theorem contract1959_1 : P.leaf 30 31357 = 60352 := by
  exact leaf_contract_factors (k := 30) (b := 19) (H := 31357) (ss := [(31, 1, 468), (16, 1, 529), (12, 1, 867), (14, 1, 874), (8, 1, 531), (26, 1, 517), (28, 1, 860), (30, 1, 1209), (18, 1, 1265), (20, 1, 1314), (21, 1, 1315)]) (ids := [0, 1, 2, 3, 4, 7, 8, 9, 11, 13, 15, 17, 20, 21, 25, 27, 5, 22, 23]) (cs := [2, 3, 4, 5, 6, 18, 1, 7, 8, 9, 1, 10, 1, 11, 1, 12, 1, 13, 1, 1, 14, 15, 19, 20, 1, 16, 1, 17, 1, 1]) (bs := [16, 3]) (W := 60352) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1959_1 : P.sumLeaves 24 2006848 64 = 60352 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 31357) rows (by decide) (by decide)).symm.trans contract1959_1

theorem c1959_2 : P.sumLeaves 24 2006912 128 = 1656952 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1959) (lo := 896) (len := 128) (W := 1656952) check rows elimOK (by decide) (by decide) cover1959 (by decide)
  decide +kernel

theorem h1959 : P.leaf 34 1959 = 1981552 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(832, 264248), (64, 60352), (128, 1656952)]) (.cons c1959_0 (.cons c1959_1 (.cons c1959_2 (.nil)))) (by decide) (by decide))

theorem cover1960 : P.CoversSplit 24 10 1960 0x8800000000000000000000000000000000000000000000000000000000000000000000000000000000220000000000000000000000000000000000000000000088000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 508, 515, 517, 522, 565, 860, 872, 915, 1202, 1259, 1308]) (ps := [(14, [874], [486])]) (by decide +kernel)

theorem c1960_0 : P.sumLeaves 24 2007040 1024 = 28394 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1960) (lo := 0) (len := 1024) (W := 28394) check rows elimOK (by decide) (by decide) cover1960 (by decide)
  decide +kernel

theorem h1960 : P.leaf 34 1960 = 28394 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 28394)]) (.cons c1960_0 (.nil)) (by decide) (by decide))

theorem cover1961 : P.CoversSplit 24 10 1961 0xcc000000000000000000000000000000800000000000000000000000000000000000000000000000003300000000000000000000000000000020000000000000cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 515, 517, 522, 565, 860, 872, 915, 1209, 1251, 1308, 1609]) (ps := [(14, [874], [860])]) (by decide +kernel)

theorem c1961_0 : P.sumLeaves 24 2008064 448 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1961) (lo := 0) (len := 448) (W := 0) check rows elimOK (by decide) (by decide) cover1961 (by decide)
  decide +kernel

theorem contract1961_1 : P.leaf 30 31383 = 31732 := by
  exact leaf_contract_factors (k := 30) (b := 17) (H := 31383) (ss := [(27, 1, 473), (29, 1, 473), (2, 1, 474), (3, 1, 524), (12, 1, 867), (31, 1, 872), (11, 1, 901), (14, 1, 923), (18, 1, 923), (19, 1, 965), (15, 1, 930), (30, 1, 1209), (16, 1, 1265)]) (ids := [2, 3, 4, 5, 6, 7, 8, 11, 15, 18, 19, 20, 21, 22, 24, 26, 23]) (cs := [1, 1, 2, 3, 4, 5, 6, 7, 8, 1, 1, 9, 1, 1, 1, 10, 1, 1, 11, 12, 13, 14, 15, 18, 16, 1, 17, 1, 1, 1]) (bs := [16, 1]) (W := 31732) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1961_1 : P.sumLeaves 24 2008512 64 = 31732 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 31383) rows (by decide) (by decide)).symm.trans contract1961_1

theorem c1961_2 : P.sumLeaves 24 2008576 512 = 245570 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1961) (lo := 512) (len := 512) (W := 245570) check rows elimOK (by decide) (by decide) cover1961 (by decide)
  decide +kernel

theorem h1961 : P.leaf 34 1961 = 277302 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(448, 0), (64, 31732), (512, 245570)]) (.cons c1961_0 (.cons c1961_1 (.cons c1961_2 (.nil)))) (by decide) (by decide))

theorem cover1962 : P.CoversSplit 24 10 1962 0xaaaa0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000aaaa0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 515, 517, 522, 565, 860, 872, 916, 1202, 1258, 1259, 1308]) (ps := [(14, [874], [486])]) (by decide +kernel)

theorem c1962_0 : P.sumLeaves 24 2009088 1024 = 242720 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1962) (lo := 0) (len := 1024) (W := 242720) check rows elimOK (by decide) (by decide) cover1962 (by decide)
  decide +kernel

theorem h1962 : P.leaf 34 1962 = 242720 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 242720)]) (.cons c1962_0 (.nil)) (by decide) (by decide))

theorem cover1963 : P.CoversSplit 24 10 1963 0xffff0000000000000000000000000000a0a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [515, 517, 522, 565, 860, 872, 916, 1209, 1251, 1258, 1259, 1308]) (ps := [(14, [874], [860]), (16, [529], [1258])]) (by decide +kernel)

theorem c1963_0 : P.sumLeaves 24 2010112 832 = 208720 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1963) (lo := 0) (len := 832) (W := 208720) check rows elimOK (by decide) (by decide) cover1963 (by decide)
  decide +kernel

theorem contract1963_1 : P.leaf 30 31421 = 55488 := by
  exact leaf_contract_factors (k := 30) (b := 18) (H := 31421) (ss := [(16, 1, 529), (12, 1, 867), (31, 1, 486), (11, 1, 818), (14, 1, 874), (8, 1, 531), (26, 1, 517), (28, 1, 860), (30, 1, 1209), (18, 1, 1265), (20, 1, 1314), (21, 1, 1315)]) (ids := [0, 1, 2, 3, 4, 5, 7, 8, 13, 15, 17, 20, 21, 27, 11, 22, 23, 25]) (cs := [2, 3, 4, 5, 6, 7, 1, 8, 9, 1, 1, 16, 1, 10, 1, 11, 1, 12, 1, 1, 13, 14, 17, 18, 1, 19, 1, 15, 1, 1]) (bs := [14, 4]) (W := 55488) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1963_1 : P.sumLeaves 24 2010944 64 = 55488 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 31421) rows (by decide) (by decide)).symm.trans contract1963_1

theorem c1963_2 : P.sumLeaves 24 2011008 128 = 1043552 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1963) (lo := 896) (len := 128) (W := 1043552) check rows elimOK (by decide) (by decide) cover1963 (by decide)
  decide +kernel

theorem h1963 : P.leaf 34 1963 = 1307760 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(832, 208720), (64, 55488), (128, 1043552)]) (.cons c1963_0 (.cons c1963_1 (.cons c1963_2 (.nil)))) (by decide) (by decide))

theorem cover1964 : P.CoversSplit 24 10 1964 0x8800000000000000000000000000000080000000000000000000000000000000000000000000000000220000000000000000000000000000002000000000000088000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 508, 515, 517, 522, 860, 872, 915, 1202, 1259, 1308]) (by decide +kernel)

theorem c1964_0 : P.sumLeaves 24 2011136 1024 = 153545 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1964) (lo := 0) (len := 1024) (W := 153545) check rows elimOK (by decide) (by decide) cover1964 (by decide)
  decide +kernel

theorem h1964 : P.leaf 34 1964 = 153545 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 153545)]) (.cons c1964_0 (.nil)) (by decide) (by decide))

theorem cover1965 : P.CoversSplit 24 10 1965 0xcc000000000000000000000000000000800000000000000000000000000000000000000000000000003300000000000000000000000000000020000000000000cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 515, 517, 522, 860, 872, 915, 1209, 1251, 1308, 1609]) (by decide +kernel)

theorem c1965_0 : P.sumLeaves 24 2012160 1024 = 1326904 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1965) (lo := 0) (len := 1024) (W := 1326904) check rows elimOK (by decide) (by decide) cover1965 (by decide)
  decide +kernel

theorem h1965 : P.leaf 34 1965 = 1326904 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1326904)]) (.cons c1965_0 (.nil)) (by decide) (by decide))

theorem cover1966 : P.CoversSplit 24 10 1966 0xaaaa0000000000000000000000000000a0a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000aaaa0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 515, 517, 522, 860, 872, 916, 1202, 1258, 1259, 1308]) (ps := [(16, [468], [1258])]) (by decide +kernel)

theorem c1966_0 : P.sumLeaves 24 2013184 832 = 273728 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1966) (lo := 0) (len := 832) (W := 273728) check rows elimOK (by decide) (by decide) cover1966 (by decide)
  decide +kernel

theorem contract1966_1 : P.leaf 30 31469 = 68928 := by
  exact leaf_contract_factors (k := 30) (b := 19) (H := 31469) (ss := [(16, 1, 468), (12, 1, 867), (31, 1, 872), (26, 1, 515), (30, 1, 515), (28, 1, 860), (14, 1, 874), (18, 1, 1265), (20, 1, 1314), (21, 1, 1315), (8, 1, 531)]) (ids := [0, 1, 2, 3, 4, 7, 8, 9, 13, 15, 17, 20, 21, 25, 27, 5, 11, 22, 23]) (cs := [2, 3, 4, 5, 6, 17, 1, 7, 8, 9, 1, 18, 1, 10, 1, 11, 1, 12, 1, 1, 13, 14, 19, 20, 1, 15, 1, 16, 1, 1]) (bs := [15, 4]) (W := 68928) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1966_1 : P.sumLeaves 24 2014016 64 = 68928 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 31469) rows (by decide) (by decide)).symm.trans contract1966_1

theorem c1966_2 : P.sumLeaves 24 2014080 128 = 1189584 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1966) (lo := 896) (len := 128) (W := 1189584) check rows elimOK (by decide) (by decide) cover1966 (by decide)
  decide +kernel

theorem h1966 : P.leaf 34 1966 = 1532240 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(832, 273728), (64, 68928), (128, 1189584)]) (.cons c1966_0 (.cons c1966_1 (.cons c1966_2 (.nil)))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(1928, 48), (1929, 48), (1930, 48), (1931, 48), (1932, 48), (1933, 48), (1934, 48), (1935, 48), (1939, 12), (1940, 48), (1941, 48), (1942, 48), (1943, 48), (1944, 48), (1945, 48), (1946, 48), (1947, 48), (1948, 48), (1949, 48), (1950, 48), (1951, 48), (1956, 48), (1957, 48), (1958, 48), (1959, 48), (1960, 24), (1961, 24), (1962, 48), (1963, 48), (1964, 48), (1965, 48), (1966, 48)]

theorem segOK : checkSeg 16 perms 1928 1967 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 1928 1967 1452 1427933736 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 1427933736)
    (SegSum.cons (w := 48) h1928 (SegSum.cons (w := 48) h1929 (SegSum.cons (w := 48) h1930 (SegSum.cons (w := 48) h1931 (SegSum.cons (w := 48) h1932 (SegSum.cons (w := 48) h1933 (SegSum.cons (w := 48) h1934 (SegSum.cons (w := 48) h1935 (SegSum.cons (w := 12) h1939 (SegSum.cons (w := 48) h1940 (SegSum.cons (w := 48) h1941 (SegSum.cons (w := 48) h1942 (SegSum.cons (w := 48) h1943 (SegSum.cons (w := 48) h1944 (SegSum.cons (w := 48) h1945 (SegSum.cons (w := 48) h1946 (SegSum.cons (w := 48) h1947 (SegSum.cons (w := 48) h1948 (SegSum.cons (w := 48) h1949 (SegSum.cons (w := 48) h1950 (SegSum.cons (w := 48) h1951 (SegSum.cons (w := 48) h1956 (SegSum.cons (w := 48) h1957 (SegSum.cons (w := 48) h1958 (SegSum.cons (w := 48) h1959 (SegSum.cons (w := 24) h1960 (SegSum.cons (w := 24) h1961 (SegSum.cons (w := 48) h1962 (SegSum.cons (w := 48) h1963 (SegSum.cons (w := 48) h1964 (SegSum.cons (w := 48) h1965 (SegSum.cons (w := 48) h1966 (show SegSum (P.leaf 34) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S4N1.C0.S15
