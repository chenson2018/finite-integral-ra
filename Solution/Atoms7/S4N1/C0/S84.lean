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

namespace RACert.S4N1.C0.S84

open RACert RACert.Problem

theorem cover23871 : P.CoversSplit 24 10 23871 0xfffffffffafaa0a0fffffffffafaa0a0fffffffffafaa0a0ffff000000000000cccccccc88888080cc00cc0088008000cccccccc88888080cc00000000000000fffffffffafaa0a0ffff0000fafa0000fffffffffafaa0a0ffff0000000000000000000000000000cc0000008800000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [517, 572, 858, 865, 1202, 1210, 1251, 1259, 1264, 1308, 1601, 1609]) (by decide +kernel)

theorem c23871_0 : P.sumLeaves 24 24443904 128 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23871) (lo := 0) (len := 128) (W := 0) check rows elimOK (by decide) (by decide) cover23871 (by decide)
  decide +kernel

theorem contract23871_1 : P.leaf 30 381938 = 14496 := by
  exact leaf_contract_factors (k := 30) (b := 16) (H := 381938) (ss := [(4, 1, 578), (11, 1, 921), (30, 1, 1264), (18, 1, 1308), (29, 27, 1601), (27, 1, 572), (8, 0, 1609), (5, 3, 524), (3, 1, 580), (14, 0, 1609), (9, 1, 629), (21, 1, 629), (20, 1, 678), (16, 1, 1265)]) (ids := [0, 4, 5, 8, 10, 13, 15, 17, 21, 22, 23, 24, 26, 29, 11, 20]) (cs := [2, 1, 1, 1, 3, 4, 0, 1, 5, 1, 6, 16, 0, 7, 1, 8, 1, 9, 1, 1, 17, 10, 11, 12, 13, 1, 14, 1, 1, 15]) (bs := [14, 2]) (W := 14496) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c23871_1 : P.sumLeaves 24 24444032 64 = 14496 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 381938) rows (by decide) (by decide)).symm.trans contract23871_1

theorem c23871_2 : P.sumLeaves 24 24444096 273 = 26476897 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23871) (lo := 192) (len := 273) (W := 26476897) check rows elimOK (by decide) (by decide) cover23871 (by decide)
  decide +kernel

theorem c23871_3 : P.sumLeaves 24 24444369 290 = 41112563 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23871) (lo := 465) (len := 290) (W := 41112563) check rows elimOK (by decide) (by decide) cover23871 (by decide)
  decide +kernel

theorem c23871_4 : P.sumLeaves 24 24444659 182 = 68630778 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23871) (lo := 755) (len := 182) (W := 68630778) check rows elimOK (by decide) (by decide) cover23871 (by decide)
  decide +kernel

theorem c23871_5 : P.sumLeaves 24 24444841 87 = 108432403 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23871) (lo := 937) (len := 87) (W := 108432403) check rows elimOK (by decide) (by decide) cover23871 (by decide)
  decide +kernel

theorem h23871 : P.leaf 34 23871 = 244667137 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(128, 0), (64, 14496), (273, 26476897), (290, 41112563), (182, 68630778), (87, 108432403)]) (.cons c23871_0 (.cons c23871_1 (.cons c23871_2 (.cons c23871_3 (.cons c23871_4 (.cons c23871_5 (.nil))))))) (by decide) (by decide))

theorem cover23916 : P.CoversSplit 24 10 23916 0xcc00cc00c80080000000000000000000cc000000000000000000000000000000ccc0ccc088808080cc00cc0088008000ccc0000040400000cc00000040000000cc00cc00c80080000000000000000000cc0044000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 515, 522, 572, 858, 865, 1210, 1601]) (by decide +kernel)

theorem c23916_0 : P.sumLeaves 24 24489984 1024 = 5542664 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23916) (lo := 0) (len := 1024) (W := 5542664) check rows elimOK (by decide) (by decide) cover23916 (by decide)
  decide +kernel

theorem h23916 : P.leaf 34 23916 = 5542664 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 5542664)]) (.cons c23916_0 (.nil)) (by decide) (by decide))

theorem cover23917 : P.CoversSplit 24 10 23917 0xcc00cc00c80080000000000000000000cc000000000000000000000000000000cc00cc00880080000000000000000000cc000000400000000000000000000000cc00cc00c80080000000000000000000cc0044000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 515, 522, 572, 858, 865, 916, 1202, 1210, 1601]) (by decide +kernel)

theorem c23917_0 : P.sumLeaves 24 24491008 1024 = 8933112 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23917) (lo := 0) (len := 1024) (W := 8933112) check rows elimOK (by decide) (by decide) cover23917 (by decide)
  decide +kernel

theorem h23917 : P.leaf 34 23917 = 8933112 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 8933112)]) (.cons c23917_0 (.nil)) (by decide) (by decide))

theorem cover23918 : P.CoversSplit 24 10 23918 0xccccccccc8c888880000000000000000cccc0000000040400000000000000000ccc0ccc088808880cc00cc0088008800ccc0000040404040cc00000040004000ccccccccc8c888880000000000000000cccc00000000404000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 515, 522, 572, 858, 865, 1202, 1210, 1259, 1601]) (ps := [(18, [879], [1210])]) (by decide +kernel)

theorem c23918_0 : P.sumLeaves 24 24492032 979 = 18393236 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23918) (lo := 0) (len := 979) (W := 18393236) check rows elimOK (by decide) (by decide) cover23918 (by decide)
  decide +kernel

theorem c23918_1 : P.sumLeaves 24 24493011 45 = 17197182 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23918) (lo := 979) (len := 45) (W := 17197182) check rows elimOK (by decide) (by decide) cover23918 (by decide)
  decide +kernel

theorem h23918 : P.leaf 34 23918 = 35590418 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(979, 18393236), (45, 17197182)]) (.cons c23918_0 (.cons c23918_1 (.nil))) (by decide) (by decide))

theorem cover23919 : P.CoversSplit 24 10 23919 0xccccccccc8c888880000000000000000cccc0000000040400000000000000000cccccccc888888880000000000000000cccc0000404040400000000000000000ccccccccc8c888880000000000000000cccc44440000404000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 522, 572, 858, 865, 1202, 1210, 1259, 1601]) (by decide +kernel)

theorem c23919_0 : P.sumLeaves 24 24493056 994 = 39960692 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23919) (lo := 0) (len := 994) (W := 39960692) check rows elimOK (by decide) (by decide) cover23919 (by decide)
  decide +kernel

theorem c23919_1 : P.sumLeaves 24 24494050 30 = 18146182 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23919) (lo := 994) (len := 30) (W := 18146182) check rows elimOK (by decide) (by decide) cover23919 (by decide)
  decide +kernel

theorem h23919 : P.leaf 34 23919 = 58106874 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(994, 39960692), (30, 18146182)]) (.cons c23919_0 (.cons c23919_1 (.nil))) (by decide) (by decide))

theorem cover23934 : P.CoversSplit 24 10 23934 0xfffffffffafaaaaafffffffffafaaaaafffffffffafaaaaafffffffffafaaaaaccc0ccc088808880cc00cc0088008800ccc0ccc088808880cc00cc0088008800fffffffffafaaaaaffff0000fafa0000fffffffffafaaaaaffff0000fafa00000000000000000000cc00000088000000ccc0000080800000cc00000080000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 572, 858, 865, 1202, 1210, 1259, 1264, 1601, 1609]) (ps := [(8, [1217], [1609])]) (by decide +kernel)

theorem contract23934_0 : P.leaf 30 382944 = 352 := by
  exact leaf_contract_factors (k := 30) (b := 9) (H := 382944) (ss := [(4, 1, 578), (10, 1, 865), (29, 1, 865), (18, 1, 867), (11, 1, 921), (30, 1, 1264), (27, 1, 1601), (8, 0, 1609), (5, 1, 622), (21, 1, 1266), (20, 1, 1272), (14, 0, 1609), (9, 7, 629), (12, 1, 825), (13, 1, 971), (7, 1, 628), (15, 1, 972), (31, 1, 1217), (16, 1, 1314), (17, 1, 1315), (19, 1, 1658)]) (ids := [0, 1, 4, 23, 20, 21, 22, 24, 26]) (cs := [2, 3, 1, 1, 4, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 6, 7, 8, 5, 9, 1, 10, 1, 1, 1]) (bs := [4, 5]) (W := 352) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c23934_0 : P.sumLeaves 24 24508416 64 = 352 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 382944) rows (by decide) (by decide)).symm.trans contract23934_0

theorem c23934_1 : P.sumLeaves 24 24508480 64 = 28356 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23934) (lo := 64) (len := 64) (W := 28356) check rows elimOK (by decide) (by decide) cover23934 (by decide)
  decide +kernel

theorem contract23934_2 : P.leaf 30 382946 = 27404 := by
  apply (leaf_contract (k := 30) (b := 18) (H := 382946) (ss := [(4, 1, 578), (10, 1, 865), (29, 1, 865), (18, 1, 867), (11, 1, 921), (30, 1, 1264), (27, 1, 1601), (8, 0, 1609), (5, 1, 580), (14, 0, 1609), (21, 1, 923), (20, 1, 929)]) (ids := [0, 1, 4, 5, 7, 10, 11, 13, 14, 15, 17, 20, 21, 22, 23, 24, 26, 29]) (cs := [2, 3, 1, 1, 4, 5, 0, 6, 1, 1, 7, 8, 0, 9, 10, 11, 1, 12, 1, 1, 13, 14, 15, 16, 17, 1, 18, 1, 1, 19]) check rows (by decide) (by decide +kernel) (by decide +kernel)).trans
  decide +kernel

theorem c23934_2 : P.sumLeaves 24 24508544 64 = 27404 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 382946) rows (by decide) (by decide)).symm.trans contract23934_2

theorem c23934_3 : P.sumLeaves 24 24508608 244 = 18235310 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23934) (lo := 192) (len := 244) (W := 18235310) check rows elimOK (by decide) (by decide) cover23934 (by decide)
  decide +kernel

theorem c23934_4 : P.sumLeaves 24 24508852 231 = 35853012 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23934) (lo := 436) (len := 231) (W := 35853012) check rows elimOK (by decide) (by decide) cover23934 (by decide)
  decide +kernel

theorem c23934_5 : P.sumLeaves 24 24509083 193 = 42487010 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23934) (lo := 667) (len := 193) (W := 42487010) check rows elimOK (by decide) (by decide) cover23934 (by decide)
  decide +kernel

theorem c23934_6 : P.sumLeaves 24 24509276 117 = 89125807 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23934) (lo := 860) (len := 117) (W := 89125807) check rows elimOK (by decide) (by decide) cover23934 (by decide)
  decide +kernel

theorem c23934_7 : P.sumLeaves 24 24509393 47 = 68422006 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23934) (lo := 977) (len := 47) (W := 68422006) check rows elimOK (by decide) (by decide) cover23934 (by decide)
  decide +kernel

theorem h23934 : P.leaf 34 23934 = 254179257 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(64, 352), (64, 28356), (64, 27404), (244, 18235310), (231, 35853012), (193, 42487010), (117, 89125807), (47, 68422006)]) (.cons c23934_0 (.cons c23934_1 (.cons c23934_2 (.cons c23934_3 (.cons c23934_4 (.cons c23934_5 (.cons c23934_6 (.cons c23934_7 (.nil))))))))) (by decide) (by decide))

theorem cover23935 : P.CoversSplit 24 10 23935 0xfffffffffafaaaaafffffffffafaaaaafffffffffafaaaaafffffffffafaaaaacccccccc88888888cc00cc0088008800cccccccc88888888cc00cc0088008800fffffffffafaaaaaffff0000fafa0000fffffffffafaaaaaffff0000fafa00000000000000000000cc00000088000000cccc000080800000cc00000080000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [572, 858, 865, 1202, 1210, 1259, 1264, 1601, 1609]) (ps := [(8, [1217], [1609])]) (by decide +kernel)

theorem contract23935_0 : P.leaf 30 382960 = 912 := by
  apply (leaf_contract (k := 30) (b := 14) (H := 382960) (ss := [(4, 1, 578), (11, 1, 921), (30, 1, 1264), (29, 27, 1601), (27, 1, 572), (8, 0, 1609), (5, 1, 622), (21, 1, 1266), (20, 1, 1272), (14, 0, 1609), (9, 7, 629), (12, 1, 825), (15, 13, 972), (31, 1, 1217), (17, 16, 1315), (19, 18, 1658)]) (ids := [0, 1, 4, 5, 8, 11, 14, 16, 20, 21, 22, 23, 24, 26]) (cs := [2, 3, 1, 1, 4, 5, 0, 5, 6, 1, 1, 7, 0, 7, 8, 8, 9, 9, 1, 1, 10, 11, 12, 13, 14, 1, 15, 1, 1, 1]) check rows (by decide) (by decide +kernel) (by decide +kernel)).trans
  decide +kernel

theorem c23935_0 : P.sumLeaves 24 24509440 64 = 912 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 382960) rows (by decide) (by decide)).symm.trans contract23935_0

theorem c23935_1 : P.sumLeaves 24 24509504 337 = 24425680 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23935) (lo := 64) (len := 337) (W := 24425680) check rows elimOK (by decide) (by decide) cover23935 (by decide)
  decide +kernel

theorem c23935_2 : P.sumLeaves 24 24509841 194 = 58390979 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23935) (lo := 401) (len := 194) (W := 58390979) check rows elimOK (by decide) (by decide) cover23935 (by decide)
  decide +kernel

theorem c23935_3 : P.sumLeaves 24 24510035 225 = 62429349 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23935) (lo := 595) (len := 225) (W := 62429349) check rows elimOK (by decide) (by decide) cover23935 (by decide)
  decide +kernel

theorem c23935_4 : P.sumLeaves 24 24510260 120 = 113784721 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23935) (lo := 820) (len := 120) (W := 113784721) check rows elimOK (by decide) (by decide) cover23935 (by decide)
  decide +kernel

theorem c23935_5 : P.sumLeaves 24 24510380 84 = 144394414 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23935) (lo := 940) (len := 84) (W := 144394414) check rows elimOK (by decide) (by decide) cover23935 (by decide)
  decide +kernel

theorem h23935 : P.leaf 34 23935 = 403426055 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(64, 912), (337, 24425680), (194, 58390979), (225, 62429349), (120, 113784721), (84, 144394414)]) (.cons c23935_0 (.cons c23935_1 (.cons c23935_2 (.cons c23935_3 (.cons c23935_4 (.cons c23935_5 (.nil))))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(23871, 48), (23916, 24), (23917, 24), (23918, 48), (23919, 48), (23934, 24), (23935, 24)]

theorem segOK : checkSeg 16 perms 23871 23972 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 23871 23972 240 32371438704 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 32371438704)
    (SegSum.cons (w := 48) h23871 (SegSum.cons (w := 24) h23916 (SegSum.cons (w := 24) h23917 (SegSum.cons (w := 48) h23918 (SegSum.cons (w := 48) h23919 (SegSum.cons (w := 24) h23934 (SegSum.cons (w := 24) h23935 (show SegSum (P.leaf 34) [] 0 from rfl)))))))) (by decide)

end RACert.S4N1.C0.S84
