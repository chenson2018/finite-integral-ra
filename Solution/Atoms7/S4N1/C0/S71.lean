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

namespace RACert.S4N1.C0.S71

open RACert RACert.Problem

theorem cover21877 : P.CoversSplit 24 10 21877 0xcc00cc00c8008000cc00cc00c8008000cc00cc00c8008000cc00cc00c8008000cc00cc0088008000cc00cc0088008000cc00cc0088008000cc00cc0088008000cc00cc00c8008000cc000000c8000000cc00cc00c8008000cc000000c80000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 572, 858, 860, 909, 916, 1202, 1210, 1264, 1601]) (by decide +kernel)

theorem c21877_0 : P.sumLeaves 24 22402048 862 = 4540100 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21877) (lo := 0) (len := 862) (W := 4540100) check rows elimOK (by decide) (by decide) cover21877 (by decide)
  decide +kernel

theorem c21877_1 : P.sumLeaves 24 22402910 162 = 5048516 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21877) (lo := 862) (len := 162) (W := 5048516) check rows elimOK (by decide) (by decide) cover21877 (by decide)
  decide +kernel

theorem h21877 : P.leaf 34 21877 = 9588616 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(862, 4540100), (162, 5048516)]) (.cons c21877_0 (.cons c21877_1 (.nil))) (by decide) (by decide))

theorem cover21879 : P.CoversSplit 24 10 21879 0xfffffffffafaaaaafffffffffafaaaaafffffffffafaaaaafffffffffafaaaaacccccccc88888888cc00cc0088008800cccccccc88888888cc00cc0088008800fffffffffafaaaaaffff0000fafa0000fffffffffafaaaaaffff0000fafa00000000000000000000cc00000088000000cccc000080800000cc00000080000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [572, 858, 860, 865, 916, 1202, 1210, 1264, 1601, 1609]) (ps := [(8, [1217], [1272])]) (by decide +kernel)

theorem contract21879_0 : P.leaf 30 350064 = 48 := by
  exact leaf_contract_factors (k := 30) (b := 6) (H := 350064) (ss := [(4, 1, 578), (11, 1, 921), (30, 1, 1264), (29, 27, 1601), (27, 1, 572), (2, 1, 475), (8, 0, 1609), (5, 1, 622), (21, 1, 1266), (31, 20, 1272), (14, 0, 1609), (20, 1, 488), (9, 7, 629), (13, 1, 922), (7, 1, 628), (18, 1, 922), (12, 0, 965), (6, 1, 803), (28, 1, 852), (25, 1, 915), (15, 1, 930), (19, 1, 930), (16, 1, 1314), (17, 1, 1315)]) (ids := [8, 21, 1, 20, 22, 24]) (cs := [1, 4, 1, 1, 1, 1, 0, 1, 2, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 5, 3, 6, 1, 7, 1, 1, 1, 1, 1]) (bs := [2, 4]) (W := 48) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c21879_0 : P.sumLeaves 24 22404096 64 = 48 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 350064) rows (by decide) (by decide)).symm.trans contract21879_0

theorem c21879_1 : P.sumLeaves 24 22404160 64 = 4134 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21879) (lo := 64) (len := 64) (W := 4134) check rows elimOK (by decide) (by decide) cover21879 (by decide)
  decide +kernel

theorem contract21879_2 : P.leaf 30 350066 = 320 := by
  exact leaf_contract_factors (k := 30) (b := 9) (H := 350066) (ss := [(4, 1, 578), (11, 1, 921), (30, 1, 1264), (29, 27, 1601), (27, 1, 572), (2, 1, 475), (8, 0, 1609), (5, 1, 580), (14, 0, 1609), (21, 1, 923), (20, 1, 929), (13, 1, 922), (18, 1, 922), (12, 0, 965), (6, 1, 803), (10, 0, 825), (23, 1, 817), (28, 1, 852), (25, 1, 915), (15, 1, 930), (19, 1, 930)]) (ids := [22, 24, 29, 1, 5, 7, 14, 15, 20]) (cs := [1, 5, 1, 1, 1, 6, 0, 7, 0, 1, 0, 1, 0, 1, 8, 9, 1, 1, 1, 1, 10, 1, 2, 1, 3, 1, 1, 1, 1, 4]) (bs := [3, 6]) (W := 320) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c21879_2 : P.sumLeaves 24 22404224 64 = 320 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 350066) rows (by decide) (by decide)).symm.trans contract21879_2

theorem c21879_3 : P.sumLeaves 24 22404288 244 = 11768336 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21879) (lo := 192) (len := 244) (W := 11768336) check rows elimOK (by decide) (by decide) cover21879 (by decide)
  decide +kernel

theorem c21879_4 : P.sumLeaves 24 22404532 198 = 20501204 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21879) (lo := 436) (len := 198) (W := 20501204) check rows elimOK (by decide) (by decide) cover21879 (by decide)
  decide +kernel

theorem c21879_5 : P.sumLeaves 24 22404730 207 = 20221929 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21879) (lo := 634) (len := 207) (W := 20221929) check rows elimOK (by decide) (by decide) cover21879 (by decide)
  decide +kernel

theorem c21879_6 : P.sumLeaves 24 22404937 115 = 35875516 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21879) (lo := 841) (len := 115) (W := 35875516) check rows elimOK (by decide) (by decide) cover21879 (by decide)
  decide +kernel

theorem c21879_7 : P.sumLeaves 24 22405052 68 = 41183000 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21879) (lo := 956) (len := 68) (W := 41183000) check rows elimOK (by decide) (by decide) cover21879 (by decide)
  decide +kernel

theorem h21879 : P.leaf 34 21879 = 129554487 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(64, 48), (64, 4134), (64, 320), (244, 11768336), (198, 20501204), (207, 20221929), (115, 35875516), (68, 41183000)]) (.cons c21879_0 (.cons c21879_1 (.cons c21879_2 (.cons c21879_3 (.cons c21879_4 (.cons c21879_5 (.cons c21879_6 (.cons c21879_7 (.nil))))))))) (by decide) (by decide))

theorem cover21884 : P.CoversSplit 24 10 21884 0xc0000000c0008000c0000000c0008000c000000040000000c000000040000000c0c0000080808080c000000080008000c000000000000000c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 466, 473, 572, 858, 860, 865, 867, 909, 916, 1202, 1210, 1601]) (by decide +kernel)

theorem c21884_0 : P.sumLeaves 24 22409216 1024 = 3610180 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21884) (lo := 0) (len := 1024) (W := 3610180) check rows elimOK (by decide) (by decide) cover21884 (by decide)
  decide +kernel

theorem h21884 : P.leaf 34 21884 = 3610180 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 3610180)]) (.cons c21884_0 (.nil)) (by decide) (by decide))

theorem cover21885 : P.CoversSplit 24 10 21885 0xcc00cc00c8008000cc00cc00c8008000cc00cc00c8008000cc00cc00c8008000cc00cc0088008000cc00cc0088008000cc00cc0088008000cc00cc0088008000cc00cc00c8008000cc000000c8000000cc00cc00c8008000cc000000c80000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 572, 858, 860, 909, 916, 1202, 1210, 1264, 1601]) (by decide +kernel)

theorem c21885_0 : P.sumLeaves 24 22410240 862 = 13612658 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21885) (lo := 0) (len := 862) (W := 13612658) check rows elimOK (by decide) (by decide) cover21885 (by decide)
  decide +kernel

theorem c21885_1 : P.sumLeaves 24 22411102 162 = 15469188 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21885) (lo := 862) (len := 162) (W := 15469188) check rows elimOK (by decide) (by decide) cover21885 (by decide)
  decide +kernel

theorem h21885 : P.leaf 34 21885 = 29081846 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(862, 13612658), (162, 15469188)]) (.cons c21885_0 (.cons c21885_1 (.nil))) (by decide) (by decide))

theorem cover21886 : P.CoversSplit 24 10 21886 0xf0f00000f0f00000f0f00000f0f00000f0f0000050500000f0f0000050500000c0c0000080800000c000000080000000c0c0000000000000c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 572, 858, 860, 865, 867, 916, 1202, 1210, 1601]) (by decide +kernel)

theorem c21886_0 : P.sumLeaves 24 22411264 1024 = 20827198 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21886) (lo := 0) (len := 1024) (W := 20827198) check rows elimOK (by decide) (by decide) cover21886 (by decide)
  decide +kernel

theorem h21886 : P.leaf 34 21886 = 20827198 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 20827198)]) (.cons c21886_0 (.nil)) (by decide) (by decide))

theorem cover21887 : P.CoversSplit 24 10 21887 0xfffffffffafaaaaafffffffffafaaaaafffffffffafaaaaafffffffffafaaaaacccccccc88888888cc00cc0088008800cccccccc88888888cc00cc0088008800fffffffffafaaaaaffff0000fafa0000fffffffffafaaaaaffff0000fafa00000000000000000000cc00000088000000cccc000080800000cc00000080000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [572, 858, 860, 865, 916, 1202, 1210, 1264, 1601, 1609]) (ps := [(8, [1217], [1272])]) (by decide +kernel)

theorem contract21887_0 : P.leaf 30 350192 = 688 := by
  apply (leaf_contract (k := 30) (b := 14) (H := 350192) (ss := [(4, 1, 578), (11, 1, 921), (30, 1, 1264), (29, 27, 1601), (27, 1, 572), (8, 0, 1609), (5, 1, 622), (21, 1, 1266), (31, 20, 1272), (14, 0, 1609), (20, 1, 580), (9, 7, 629), (12, 1, 825), (15, 13, 972), (17, 16, 1315), (19, 18, 1658)]) (ids := [0, 1, 4, 5, 8, 11, 14, 16, 20, 21, 22, 23, 24, 26]) (cs := [2, 3, 1, 1, 4, 5, 0, 5, 6, 1, 1, 7, 0, 7, 8, 8, 9, 9, 1, 1, 10, 11, 12, 13, 14, 1, 15, 1, 1, 1]) check rows (by decide) (by decide +kernel) (by decide +kernel)).trans
  decide +kernel

theorem c21887_0 : P.sumLeaves 24 22412288 64 = 688 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 350192) rows (by decide) (by decide)).symm.trans contract21887_0

theorem c21887_1 : P.sumLeaves 24 22412352 64 = 27756 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21887) (lo := 64) (len := 64) (W := 27756) check rows elimOK (by decide) (by decide) cover21887 (by decide)
  decide +kernel

theorem contract21887_2 : P.leaf 30 350194 = 29628 := by
  exact leaf_contract_factors (k := 30) (b := 17) (H := 350194) (ss := [(4, 1, 578), (11, 1, 921), (30, 1, 1264), (29, 27, 1601), (27, 1, 572), (8, 0, 1609), (5, 1, 580), (14, 0, 1609), (21, 1, 923), (20, 1, 929), (12, 1, 965), (15, 1, 972), (18, 1, 1658)]) (ids := [0, 1, 4, 5, 8, 11, 14, 17, 20, 21, 22, 23, 24, 26, 29, 7, 15]) (cs := [2, 3, 1, 1, 4, 5, 0, 17, 6, 1, 1, 7, 0, 1, 8, 18, 1, 9, 1, 1, 10, 11, 12, 13, 14, 1, 15, 1, 1, 16]) (bs := [15, 2]) (W := 29628) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c21887_2 : P.sumLeaves 24 22412416 64 = 29628 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 350194) rows (by decide) (by decide)).symm.trans contract21887_2

theorem c21887_3 : P.sumLeaves 24 22412480 244 = 17280548 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21887) (lo := 192) (len := 244) (W := 17280548) check rows elimOK (by decide) (by decide) cover21887 (by decide)
  decide +kernel

theorem c21887_4 : P.sumLeaves 24 22412724 198 = 32703300 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21887) (lo := 436) (len := 198) (W := 32703300) check rows elimOK (by decide) (by decide) cover21887 (by decide)
  decide +kernel

theorem c21887_5 : P.sumLeaves 24 22412922 207 = 46139252 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21887) (lo := 634) (len := 207) (W := 46139252) check rows elimOK (by decide) (by decide) cover21887 (by decide)
  decide +kernel

theorem c21887_6 : P.sumLeaves 24 22413129 115 = 69734833 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21887) (lo := 841) (len := 115) (W := 69734833) check rows elimOK (by decide) (by decide) cover21887 (by decide)
  decide +kernel

theorem c21887_7 : P.sumLeaves 24 22413244 68 = 69893388 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21887) (lo := 956) (len := 68) (W := 69893388) check rows elimOK (by decide) (by decide) cover21887 (by decide)
  decide +kernel

theorem h21887 : P.leaf 34 21887 = 235809393 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(64, 688), (64, 27756), (64, 29628), (244, 17280548), (198, 32703300), (207, 46139252), (115, 69734833), (68, 69893388)]) (.cons c21887_0 (.cons c21887_1 (.cons c21887_2 (.cons c21887_3 (.cons c21887_4 (.cons c21887_5 (.cons c21887_6 (.cons c21887_7 (.nil))))))))) (by decide) (by decide))

theorem cover21932 : P.CoversSplit 24 10 21932 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [508]) (by decide +kernel)

theorem c21932_0 : P.sumLeaves 24 22458368 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21932) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover21932 (by decide)
  decide +kernel

theorem h21932 : P.leaf 34 21932 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c21932_0 (.nil)) (by decide) (by decide))

theorem cover21933 : P.CoversSplit 24 10 21933 0xa0a00000b0ba0000a0a00000b0ba0000a0a0000000000505a0a00000000005048080000080880000808000008088000080800000000004048080000000000404a0000000b00000000000000000000000a00000000000050000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 515, 517, 522, 858, 860, 865, 916, 1202, 1210, 1259, 1601]) (ps := [(14, [867], [916]), (17, [1259], [1251])]) (by decide +kernel)

theorem c21933_0 : P.sumLeaves 24 22459392 1024 = 2566997 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21933) (lo := 0) (len := 1024) (W := 2566997) check rows elimOK (by decide) (by decide) cover21933 (by decide)
  decide +kernel

theorem h21933 : P.leaf 34 21933 = 2566997 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 2566997)]) (.cons c21933_0 (.nil)) (by decide) (by decide))

theorem cover21934 : P.CoversSplit 24 10 21934 0xa0a00000a0a00000a0a00000a0a00000a0a0000000000000a0a00000000000008080000080800000800000008000000080800000000000008000000000000000a0a00000a0a000000000000000000000a0a000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 515, 517, 522, 858, 860, 865, 916, 1259, 1601]) (by decide +kernel)

theorem c21934_0 : P.sumLeaves 24 22460416 320 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21934) (lo := 0) (len := 320) (W := 0) check rows elimOK (by decide) (by decide) cover21934 (by decide)
  decide +kernel

theorem contract21934_1 : P.leaf 30 350949 = 0 := by
  exact leaf_contract_zero (ss := [(3, 1, 508), (14, 0, 867), (21, 0, 874), (8, 1, 531), (18, 1, 879), (20, 1, 880), (29, 15, 909)]) (q := 1266) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c21934_1 : P.sumLeaves 24 22460736 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 350949) rows (by decide) (by decide)).symm.trans contract21934_1

theorem c21934_2 : P.sumLeaves 24 22460800 640 = 1514160 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21934) (lo := 384) (len := 640) (W := 1514160) check rows elimOK (by decide) (by decide) cover21934 (by decide)
  decide +kernel

theorem h21934 : P.leaf 34 21934 = 1514160 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(320, 0), (64, 0), (640, 1514160)]) (.cons c21934_0 (.cons c21934_1 (.cons c21934_2 (.nil)))) (by decide) (by decide))

theorem cover21935 : P.CoversSplit 24 10 21935 0xa0a00000a0a00000a0a00000a0a00000a0a0000000000505a0a00000000005048080000080800000808000008080000080800000000004048080000000000404a0a00000a0a000000000000000000000a0a000000000050500200000000000010000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [515, 517, 522, 858, 860, 916, 1259, 1601]) (ps := [(17, [1259], [1251])]) (by decide +kernel)

theorem c21935_0 : P.sumLeaves 24 22461440 1024 = 5598256 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21935) (lo := 0) (len := 1024) (W := 5598256) check rows elimOK (by decide) (by decide) cover21935 (by decide)
  decide +kernel

theorem h21935 : P.leaf 34 21935 = 5598256 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 5598256)]) (.cons c21935_0 (.nil)) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(21877, 24), (21879, 24), (21884, 48), (21885, 48), (21886, 48), (21887, 48), (21932, 48), (21933, 48), (21934, 48), (21935, 48)]

theorem segOK : checkSeg 16 perms 21877 21948 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 21877 21948 432 17691819912 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 17691819912)
    (SegSum.cons (w := 24) h21877 (SegSum.cons (w := 24) h21879 (SegSum.cons (w := 48) h21884 (SegSum.cons (w := 48) h21885 (SegSum.cons (w := 48) h21886 (SegSum.cons (w := 48) h21887 (SegSum.cons (w := 48) h21932 (SegSum.cons (w := 48) h21933 (SegSum.cons (w := 48) h21934 (SegSum.cons (w := 48) h21935 (show SegSum (P.leaf 34) [] 0 from rfl))))))))))) (by decide)

end RACert.S4N1.C0.S71
