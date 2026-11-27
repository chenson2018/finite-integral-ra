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

namespace RACert.S4N1.C0.S37

open RACert RACert.Problem

theorem cover6012 : P.CoversSplit 24 10 6012 0xffffffffa8a8a0a0ffffffffa8a8a0a0f5f5f5f500000000f5f5f5f500000000cc00cc0080008000cc00cc0080008000c400c40000000000c400c40000000000cc00cc0088008000cc33cc3388208020c400c40000000000c431c431000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 572, 860, 867, 909, 916, 1202, 1209, 1258, 1601]) (ps := [(2, [465], [466])]) (by decide +kernel)

theorem c6012_0 : P.sumLeaves 24 6156288 256 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6012) (lo := 0) (len := 256) (W := 0) check rows elimOK (by decide) (by decide) cover6012 (by decide)
  decide +kernel

theorem contract6012_1 : P.leaf 30 96196 = 0 := by
  exact leaf_contract_zero (ss := [(31, 1, 909), (8, 0, 1272), (20, 1, 580), (21, 1, 586), (5, 1, 622), (14, 1, 1266), (28, 1, 860), (29, 1, 916), (27, 1, 572)]) (q := 1272) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c6012_1 : P.sumLeaves 24 6156544 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 96196) rows (by decide) (by decide)).symm.trans contract6012_1

theorem contract6012_2 : P.leaf 30 96197 = 0 := by
  exact leaf_contract_zero (ss := [(27, 1, 572), (31, 1, 909), (29, 1, 916), (8, 0, 1272), (20, 1, 580), (21, 1, 586), (5, 1, 622), (14, 1, 1266), (28, 1, 860)]) (q := 1272) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c6012_2 : P.sumLeaves 24 6156608 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 96197) rows (by decide) (by decide)).symm.trans contract6012_2

theorem c6012_3 : P.sumLeaves 24 6156672 492 = 3920163 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6012) (lo := 384) (len := 492) (W := 3920163) check rows elimOK (by decide) (by decide) cover6012 (by decide)
  decide +kernel

theorem c6012_4 : P.sumLeaves 24 6157164 144 = 10314920 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6012) (lo := 876) (len := 144) (W := 10314920) check rows elimOK (by decide) (by decide) cover6012 (by decide)
  decide +kernel

theorem c6012_5 : P.sumLeaves 24 6157308 4 = 1711352 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6012) (lo := 1020) (len := 4) (W := 1711352) check rows elimOK (by decide) (by decide) cover6012 (by decide)
  decide +kernel

theorem h6012 : P.leaf 34 6012 = 15946435 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(256, 0), (64, 0), (64, 0), (492, 3920163), (144, 10314920), (4, 1711352)]) (.cons c6012_0 (.cons c6012_1 (.cons c6012_2 (.cons c6012_3 (.cons c6012_4 (.cons c6012_5 (.nil))))))) (by decide) (by decide))

theorem cover6013 : P.CoversSplit 24 10 6013 0xffffffffaaaaa0a0ffffffffaaaaa0a0ffffffff00000000ffffffff00000000cc00cc0080008000cc00cc0080008000cc00cc0000000000cc00cc0000000000cc00cc0088008000cc33cc3388228020cc00cc0000000000cc33cc33000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 572, 860, 909, 916, 1202, 1209, 1258, 1601]) (by decide +kernel)

theorem c6013_0 : P.sumLeaves 24 6157312 256 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6013) (lo := 0) (len := 256) (W := 0) check rows elimOK (by decide) (by decide) cover6013 (by decide)
  decide +kernel

theorem contract6013_1 : P.leaf 30 96212 = 0 := by
  exact leaf_contract_zero (ss := [(31, 1, 909), (8, 0, 1272), (20, 1, 580), (21, 1, 586), (5, 1, 622), (14, 1, 1266), (29, 1, 916), (27, 1, 572)]) (q := 1272) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c6013_1 : P.sumLeaves 24 6157568 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 96212) rows (by decide) (by decide)).symm.trans contract6013_1

theorem contract6013_2 : P.leaf 30 96213 = 0 := by
  exact leaf_contract_zero (ss := [(27, 1, 572), (31, 1, 909), (29, 1, 916), (8, 0, 1272), (20, 1, 580), (21, 1, 586), (5, 1, 622), (14, 1, 1266)]) (q := 1272) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c6013_2 : P.sumLeaves 24 6157632 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 96213) rows (by decide) (by decide)).symm.trans contract6013_2

theorem c6013_3 : P.sumLeaves 24 6157696 443 = 8285132 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6013) (lo := 384) (len := 443) (W := 8285132) check rows elimOK (by decide) (by decide) cover6013 (by decide)
  decide +kernel

theorem c6013_4 : P.sumLeaves 24 6158139 168 = 18131320 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6013) (lo := 827) (len := 168) (W := 18131320) check rows elimOK (by decide) (by decide) cover6013 (by decide)
  decide +kernel

theorem c6013_5 : P.sumLeaves 24 6158307 29 = 12262810 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6013) (lo := 995) (len := 29) (W := 12262810) check rows elimOK (by decide) (by decide) cover6013 (by decide)
  decide +kernel

theorem h6013 : P.leaf 34 6013 = 38679262 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(256, 0), (64, 0), (64, 0), (443, 8285132), (168, 18131320), (29, 12262810)]) (.cons c6013_0 (.cons c6013_1 (.cons c6013_2 (.cons c6013_3 (.cons c6013_4 (.cons c6013_5 (.nil))))))) (by decide) (by decide))

theorem cover6014 : P.CoversSplit 24 10 6014 0xffffffffaaaaa0a0ffffffffaaaaa0a0f5f5f5f505050000f5f5f5f505050000cc00cc0080008000cc00cc0080008000c400c40000000000c400c40000000000ffffffffaaaaa0a0ffffffffaaaaa0a0f5f5f5f500000000f5f5f5f5000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 572, 860, 867, 916, 1202, 1209, 1217, 1258, 1601]) (by decide +kernel)

theorem c6014_0 : P.sumLeaves 24 6158336 256 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6014) (lo := 0) (len := 256) (W := 0) check rows elimOK (by decide) (by decide) cover6014 (by decide)
  decide +kernel

theorem contract6014_1 : P.leaf 30 96228 = 0 := by
  exact leaf_contract_zero (ss := [(8, 0, 1272), (5, 1, 622), (14, 1, 1266)]) (q := 1272) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c6014_1 : P.sumLeaves 24 6158592 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 96228) rows (by decide) (by decide)).symm.trans contract6014_1

theorem contract6014_2 : P.leaf 30 96229 = 0 := by
  exact leaf_contract_zero (ss := [(8, 0, 1272), (5, 1, 622), (14, 1, 1266)]) (q := 1272) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c6014_2 : P.sumLeaves 24 6158656 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 96229) rows (by decide) (by decide)).symm.trans contract6014_2

theorem c6014_3 : P.sumLeaves 24 6158720 239 = 6051472 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6014) (lo := 384) (len := 239) (W := 6051472) check rows elimOK (by decide) (by decide) cover6014 (by decide)
  decide +kernel

theorem c6014_4 : P.sumLeaves 24 6158959 309 = 13393572 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6014) (lo := 623) (len := 309) (W := 13393572) check rows elimOK (by decide) (by decide) cover6014 (by decide)
  decide +kernel

theorem c6014_5 : P.sumLeaves 24 6159268 92 = 29297896 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6014) (lo := 932) (len := 92) (W := 29297896) check rows elimOK (by decide) (by decide) cover6014 (by decide)
  decide +kernel

theorem h6014 : P.leaf 34 6014 = 48742940 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(256, 0), (64, 0), (64, 0), (239, 6051472), (309, 13393572), (92, 29297896)]) (.cons c6014_0 (.cons c6014_1 (.cons c6014_2 (.cons c6014_3 (.cons c6014_4 (.cons c6014_5 (.nil))))))) (by decide) (by decide))

theorem cover6015 : P.CoversSplit 24 10 6015 0xffffffffaaaaa0a0ffffffffaaaaa0a0ffffffffaaaaa0a0ffffffffaaaaa0a0cc00cc0080008000cc00cc0080008000cc00cc0080008000cc00cc0080008000ffffffffaaaaa0a0ffffffffaaaaa0a0ffffffffa0a0a0a0ffffffffa0a0a0a00000000000000000cc00cc0080008000cc00cc0080008000cc00cc0080008000 :=
  coversProjected check rows (by decide) (by decide) (xs := [572, 860, 916, 1202, 1209, 1258, 1601, 1609]) (ps := [(8, [1217], [1272])]) (by decide +kernel)

theorem contract6015_0 : P.leaf 30 96240 = 0 := by
  exact leaf_contract_zero (ss := [(4, 1, 578), (10, 1, 872), (11, 1, 921), (27, 1, 1258), (8, 0, 1272), (5, 1, 622), (14, 1, 1266)]) (q := 1272) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c6015_0 : P.sumLeaves 24 6159360 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 96240) rows (by decide) (by decide)).symm.trans contract6015_0

theorem contract6015_1 : P.leaf 30 96241 = 0 := by
  exact leaf_contract_zero (ss := [(4, 1, 578), (10, 1, 872), (11, 1, 921), (8, 0, 1272), (5, 1, 622), (14, 1, 1266)]) (q := 1272) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c6015_1 : P.sumLeaves 24 6159424 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 96241) rows (by decide) (by decide)).symm.trans contract6015_1

theorem contract6015_2 : P.leaf 30 96242 = 12000 := by
  exact leaf_contract_factors (k := 30) (b := 15) (H := 96242) (ss := [(4, 1, 578), (10, 1, 872), (11, 1, 921), (27, 1, 1258), (29, 1, 1601), (8, 0, 1609), (5, 1, 580), (14, 0, 1609), (12, 1, 929), (15, 1, 972), (21, 1, 972), (20, 1, 1021), (30, 1, 1266), (19, 1, 1272), (18, 1, 1658)]) (ids := [0, 1, 4, 5, 11, 14, 20, 22, 23, 24, 26, 29, 7, 15, 21]) (cs := [2, 3, 1, 1, 4, 5, 0, 14, 1, 1, 1, 6, 0, 1, 7, 15, 1, 1, 1, 1, 8, 16, 9, 10, 11, 1, 12, 1, 1, 13]) (bs := [12, 3]) (W := 12000) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c6015_2 : P.sumLeaves 24 6159488 64 = 12000 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 96242) rows (by decide) (by decide)).symm.trans contract6015_2

theorem c6015_3 : P.sumLeaves 24 6159552 64 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6015) (lo := 192) (len := 64) (W := 0) check rows elimOK (by decide) (by decide) cover6015 (by decide)
  decide +kernel

theorem contract6015_4 : P.leaf 30 96244 = 0 := by
  exact leaf_contract_zero (ss := [(8, 0, 1272), (5, 1, 622), (14, 1, 1266)]) (q := 1272) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c6015_4 : P.sumLeaves 24 6159616 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 96244) rows (by decide) (by decide)).symm.trans contract6015_4

theorem contract6015_5 : P.leaf 30 96245 = 0 := by
  exact leaf_contract_zero (ss := [(8, 0, 1272), (5, 1, 622), (14, 1, 1266)]) (q := 1272) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c6015_5 : P.sumLeaves 24 6159680 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 96245) rows (by decide) (by decide)).symm.trans contract6015_5

theorem c6015_6 : P.sumLeaves 24 6159744 190 = 15596483 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6015) (lo := 384) (len := 190) (W := 15596483) check rows elimOK (by decide) (by decide) cover6015 (by decide)
  decide +kernel

theorem c6015_7 : P.sumLeaves 24 6159934 298 = 30602398 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6015) (lo := 574) (len := 298) (W := 30602398) check rows elimOK (by decide) (by decide) cover6015 (by decide)
  decide +kernel

theorem c6015_8 : P.sumLeaves 24 6160232 136 = 70320218 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6015) (lo := 872) (len := 136) (W := 70320218) check rows elimOK (by decide) (by decide) cover6015 (by decide)
  decide +kernel

theorem c6015_9 : P.sumLeaves 24 6160368 16 = 19733706 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6015) (lo := 1008) (len := 16) (W := 19733706) check rows elimOK (by decide) (by decide) cover6015 (by decide)
  decide +kernel

theorem h6015 : P.leaf 34 6015 = 136264805 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(64, 0), (64, 0), (64, 12000), (64, 0), (64, 0), (64, 0), (190, 15596483), (298, 30602398), (136, 70320218), (16, 19733706)]) (.cons c6015_0 (.cons c6015_1 (.cons c6015_2 (.cons c6015_3 (.cons c6015_4 (.cons c6015_5 (.cons c6015_6 (.cons c6015_7 (.cons c6015_8 (.cons c6015_9 (.nil))))))))))) (by decide) (by decide))

theorem h6112 : P.leaf 34 6112 = 23648 := by
  apply (leaf_contract (k := 34) (b := 20) (H := 6112) (ss := [(6, 1, 466), (2, 1, 468), (30, 1, 1251), (31, 1, 1251), (26, 1, 515), (12, 1, 909), (5, 1, 411), (3, 1, 409), (4, 1, 410), (10, 1, 458), (11, 1, 459), (32, 1, 1264), (27, 1, 522), (34, 1, 1259)]) (ids := [5, 6, 7, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 26, 27, 31, 33]) (cs := [1, 1, 1, 1, 1, 2, 3, 4, 1, 1, 1, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 1, 1, 18, 19, 1, 1, 1, 20, 1, 21]) check rows (by decide) (by decide +kernel) (by decide +kernel)).trans
  decide +kernel

theorem cover6113 : P.CoversSplit 24 10 6113 0xcccc0000000000000000000000000000cccc00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000cc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 515, 522, 523, 860, 916, 1202, 1209, 1251, 1259]) (ps := [(14, [923, 1266], [916])]) (by decide +kernel)

theorem c6113_0 : P.sumLeaves 24 6259712 1024 = 676930 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6113) (lo := 0) (len := 1024) (W := 676930) check rows elimOK (by decide) (by decide) cover6113 (by decide)
  decide +kernel

theorem h6113 : P.leaf 34 6113 = 676930 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 676930)]) (.cons c6113_0 (.nil)) (by decide) (by decide))

theorem cover6115 : P.CoversSplit 24 10 6115 0xffff0000000000000000000000000000ffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffff0000000000000000000000000000ffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 522, 523, 860, 916, 1202, 1209, 1251, 1258, 1259, 1264]) (by decide +kernel)

noncomputable def f6115 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (6261760 + i)

theorem c6115_0 : rowSum f6115 0 1024 = 6465310 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 6115) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover6115 (by decide)
  decide +kernel

theorem sum6115 : rowSum f6115 0 1024 = 6465310 :=
  c6115_0

theorem h6115 : P.leaf 34 6115 = 6465310 :=
  leaf_weighted (k := 24) (d := 10) (H := 6115) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 6115) (by decide) (by decide +kernel)) sum6115

theorem cover6116 : P.CoversSplit 24 10 6116 0x8888000000000000000000000000000080800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000088000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 515, 522, 524, 566, 860, 916, 1202, 1209, 1258, 1259]) (by decide +kernel)

noncomputable def f6116 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (6262784 + i)

theorem c6116_0 : rowSum f6116 0 1024 = 375448 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 6116) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover6116 (by decide)
  decide +kernel

theorem sum6116 : rowSum f6116 0 1024 = 375448 :=
  c6116_0

theorem h6116 : P.leaf 34 6116 = 375448 :=
  leaf_weighted (k := 24) (d := 10) (H := 6116) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 6116) (by decide) (by decide +kernel)) sum6116

theorem cover6117 : P.CoversSplit 24 10 6117 0xcccc0000000000000000000000000000cccc00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000cc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 515, 522, 524, 566, 860, 916, 1202, 1209, 1251, 1259]) (by decide +kernel)

theorem c6117_0 : P.sumLeaves 24 6263808 1024 = 6530130 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6117) (lo := 0) (len := 1024) (W := 6530130) check rows elimOK (by decide) (by decide) cover6117 (by decide)
  decide +kernel

theorem h6117 : P.leaf 34 6117 = 6530130 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 6530130)]) (.cons c6117_0 (.nil)) (by decide) (by decide))

theorem cover6119 : P.CoversSplit 24 10 6119 0xffff0000000000000000000000000000ffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffff0000000000000000000000000000ffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 522, 524, 566, 860, 916, 1202, 1209, 1251, 1258, 1259, 1264]) (by decide +kernel)

noncomputable def f6119 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (6265856 + i)

theorem c6119_0 : rowSum f6119 0 1024 = 34885870 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 6119) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover6119 (by decide)
  decide +kernel

theorem sum6119 : rowSum f6119 0 1024 = 34885870 :=
  c6119_0

theorem h6119 : P.leaf 34 6119 = 34885870 :=
  leaf_weighted (k := 24) (d := 10) (H := 6119) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 6119) (by decide) (by decide +kernel)) sum6119

theorem cover6120 : P.CoversSplit 24 10 6120 0x8888000000000000000000000000000080800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000088000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 515, 522, 523, 565, 860, 916, 1202, 1209, 1258, 1259]) (ps := [(14, [874, 923, 1266], [860, 916])]) (by decide +kernel)

noncomputable def f6120 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (6266880 + i)

theorem c6120_0 : rowSum f6120 0 1024 = 405440 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 6120) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover6120 (by decide)
  decide +kernel

theorem sum6120 : rowSum f6120 0 1024 = 405440 :=
  c6120_0

theorem h6120 : P.leaf 34 6120 = 405440 :=
  leaf_weighted (k := 24) (d := 10) (H := 6120) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 6120) (by decide) (by decide +kernel)) sum6120

theorem cover6121 : P.CoversSplit 24 10 6121 0xcccc0000000000000000000000000000cccc00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000cc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 515, 522, 523, 860, 916, 1202, 1209, 1251, 1259]) (ps := [(14, [923, 1266], [916])]) (by decide +kernel)

theorem c6121_0 : P.sumLeaves 24 6267904 1024 = 3319646 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6121) (lo := 0) (len := 1024) (W := 3319646) check rows elimOK (by decide) (by decide) cover6121 (by decide)
  decide +kernel

theorem h6121 : P.leaf 34 6121 = 3319646 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 3319646)]) (.cons c6121_0 (.nil)) (by decide) (by decide))

theorem cover6123 : P.CoversSplit 24 10 6123 0xffff0000000000000000000000000000ffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffff0000000000000000000000000000ffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 522, 523, 860, 916, 1202, 1209, 1251, 1258, 1259, 1264]) (by decide +kernel)

noncomputable def f6123 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (6269952 + i)

theorem c6123_0 : rowSum f6123 0 1024 = 13534872 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 6123) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover6123 (by decide)
  decide +kernel

theorem sum6123 : rowSum f6123 0 1024 = 13534872 :=
  c6123_0

theorem h6123 : P.leaf 34 6123 = 13534872 :=
  leaf_weighted (k := 24) (d := 10) (H := 6123) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 6123) (by decide) (by decide +kernel)) sum6123

theorem cover6124 : P.CoversSplit 24 10 6124 0x8888000000000000000000000000000080800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000088000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 515, 522, 860, 916, 1202, 1209, 1258, 1259]) (by decide +kernel)

noncomputable def f6124 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (6270976 + i)

theorem c6124_0 : rowSum f6124 0 1024 = 1413952 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 6124) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover6124 (by decide)
  decide +kernel

theorem sum6124 : rowSum f6124 0 1024 = 1413952 :=
  c6124_0

theorem h6124 : P.leaf 34 6124 = 1413952 :=
  leaf_weighted (k := 24) (d := 10) (H := 6124) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 6124) (by decide) (by decide +kernel)) sum6124

theorem cover6125 : P.CoversSplit 24 10 6125 0xcccc0000000000000000000000000000cccc00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000cc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 515, 522, 860, 916, 1202, 1209, 1251, 1259]) (by decide +kernel)

theorem c6125_0 : P.sumLeaves 24 6272000 1024 = 11640168 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6125) (lo := 0) (len := 1024) (W := 11640168) check rows elimOK (by decide) (by decide) cover6125 (by decide)
  decide +kernel

theorem h6125 : P.leaf 34 6125 = 11640168 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 11640168)]) (.cons c6125_0 (.nil)) (by decide) (by decide))

theorem cover6127 : P.CoversSplit 24 10 6127 0xffff0000000000000000000000000000ffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffff0000000000000000000000000000ffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 522, 860, 916, 1202, 1209, 1251, 1258, 1259, 1264]) (by decide +kernel)

noncomputable def f6127 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (6274048 + i)

theorem c6127_0 : rowSum f6127 0 1024 = 51935302 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 6127) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover6127 (by decide)
  decide +kernel

theorem sum6127 : rowSum f6127 0 1024 = 51935302 :=
  c6127_0

theorem h6127 : P.leaf 34 6127 = 51935302 :=
  leaf_weighted (k := 24) (d := 10) (H := 6127) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 6127) (by decide) (by decide +kernel)) sum6127

theorem cover6128 : P.CoversSplit 24 10 6128 0xfac8fac8a080a080fac8fac8a080a080f0c0f0c000000000f0c0f0c000000000c800c80080008000c800c80080008000c000c00000000000c000c00000000000fa00fa00a000a000fa00fa00a000a000fac8fac800000000fac8fac8000000000000000000000000000000000000000000000000888888880000000088888888 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 860, 916, 1202, 1258, 1601]) (ps := [(12, [860, 866, 867, 908, 909], [860, 867, 909]), (14, [874, 923], [860, 916])]) (by decide +kernel)

theorem contract6128_0 : P.leaf 30 98048 = 16 := by
  exact leaf_contract_factors (k := 30) (b := 4) (H := 98048) (ss := [(2, 1, 468), (12, 0, 867), (10, 0, 460), (11, 0, 458), (14, 6, 811), (15, 1, 852), (30, 25, 865), (25, 19, 866), (16, 0, 872), (31, 0, 872), (22, 1, 419), (18, 0, 873), (20, 0, 873), (21, 0, 874), (19, 17, 908), (6, 1, 951), (3, 0, 458), (4, 0, 409), (5, 0, 409), (17, 0, 517), (24, 0, 515), (26, 1, 1210), (27, 1, 1258), (8, 7, 1314), (7, 1, 488), (9, 1, 1322)]) (ids := [11, 21, 26, 27]) (cs := [1, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 2, 1, 1, 0, 0, 0, 0, 0, 0, 1, 3, 0, 0, 1, 1, 4, 5, 0, 0]) (bs := [0, 4]) (W := 16) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c6128_0 : P.sumLeaves 24 6275072 64 = 16 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 98048) rows (by decide) (by decide)).symm.trans contract6128_0

theorem contract6128_1 : P.leaf 30 98049 = 0 := by
  exact leaf_contract_zero (ss := [(2, 1, 468), (12, 0, 867), (10, 0, 460), (11, 0, 458), (14, 6, 811), (15, 1, 852), (19, 1, 866), (16, 0, 872), (31, 0, 872), (22, 1, 419), (4, 1, 529), (3, 1, 409), (5, 1, 412), (6, 0, 458), (26, 1, 465), (27, 1, 473), (7, 1, 481), (8, 1, 482), (23, 1, 809), (18, 0, 873), (20, 0, 873), (21, 0, 874), (17, 1, 881)]) (q := 951) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c6128_1 : P.sumLeaves 24 6275136 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 98049) rows (by decide) (by decide)).symm.trans contract6128_1

theorem c6128_2 : P.sumLeaves 24 6275200 256 = 27552 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6128) (lo := 128) (len := 256) (W := 27552) check rows elimOK (by decide) (by decide) cover6128 (by decide)
  decide +kernel

theorem contract6128_3 : P.leaf 30 98054 = 31232 := by
  exact leaf_contract_factors (k := 30) (b := 19) (H := 98054) (ss := [(2, 1, 468), (12, 1, 867), (5, 1, 411), (3, 1, 409), (4, 1, 410), (6, 1, 458), (10, 1, 458), (11, 1, 459), (14, 1, 923), (29, 1, 916), (18, 1, 923)]) (ids := [5, 6, 7, 11, 13, 14, 15, 17, 18, 19, 22, 23, 24, 25, 26, 28, 29, 20, 21]) (cs := [1, 1, 1, 1, 1, 2, 3, 4, 1, 1, 1, 5, 1, 6, 7, 8, 1, 9, 10, 11, 19, 20, 12, 13, 14, 15, 16, 1, 17, 18]) (bs := [17, 2]) (W := 31232) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c6128_3 : P.sumLeaves 24 6275456 64 = 31232 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 98054) rows (by decide) (by decide)).symm.trans contract6128_3

theorem contract6128_4 : P.leaf 30 98055 = 31232 := by
  exact leaf_contract_factors (k := 30) (b := 19) (H := 98055) (ss := [(2, 1, 468), (12, 1, 867), (5, 1, 411), (3, 1, 409), (4, 1, 410), (6, 1, 458), (10, 1, 458), (11, 1, 459), (14, 1, 923), (29, 1, 916), (18, 1, 923)]) (ids := [5, 6, 7, 11, 13, 14, 15, 17, 18, 19, 22, 24, 25, 26, 28, 29, 20, 21, 23]) (cs := [1, 1, 1, 1, 1, 2, 3, 4, 1, 1, 1, 5, 1, 6, 7, 8, 1, 9, 10, 11, 18, 19, 12, 20, 13, 14, 15, 1, 16, 17]) (bs := [16, 3]) (W := 31232) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c6128_4 : P.sumLeaves 24 6275520 64 = 31232 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 98055) rows (by decide) (by decide)).symm.trans contract6128_4

theorem contract6128_5 : P.leaf 30 98056 = 5120 := by
  exact leaf_contract_factors (k := 30) (b := 15) (H := 98056) (ss := [(2, 1, 468), (12, 1, 867), (5, 1, 411), (3, 1, 409), (4, 1, 410), (6, 1, 458), (10, 1, 458), (11, 1, 459), (14, 1, 874), (16, 1, 874), (18, 1, 879), (31, 1, 909), (28, 1, 860), (29, 1, 916), (27, 1, 1258)]) (ids := [5, 6, 7, 11, 13, 15, 17, 18, 19, 22, 24, 28, 20, 21, 23]) (cs := [1, 1, 1, 1, 1, 2, 3, 4, 1, 1, 1, 5, 1, 6, 1, 7, 1, 8, 9, 10, 14, 15, 11, 16, 12, 1, 1, 1, 13, 1]) (bs := [12, 3]) (W := 5120) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c6128_5 : P.sumLeaves 24 6275584 64 = 5120 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 98056) rows (by decide) (by decide)).symm.trans contract6128_5

theorem contract6128_6 : P.leaf 30 98057 = 5120 := by
  exact leaf_contract_factors (k := 30) (b := 15) (H := 98057) (ss := [(2, 1, 468), (12, 1, 867), (5, 1, 411), (3, 1, 409), (4, 1, 410), (6, 1, 458), (10, 1, 458), (11, 1, 459), (14, 1, 874), (16, 1, 874), (18, 1, 879), (31, 1, 909), (28, 1, 860), (29, 1, 916), (27, 1, 1601)]) (ids := [5, 6, 7, 11, 13, 15, 17, 18, 19, 22, 24, 28, 20, 21, 23]) (cs := [1, 1, 1, 1, 1, 2, 3, 4, 1, 1, 1, 5, 1, 6, 1, 7, 1, 8, 9, 10, 14, 15, 11, 16, 12, 1, 1, 1, 13, 1]) (bs := [12, 3]) (W := 5120) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c6128_6 : P.sumLeaves 24 6275648 64 = 5120 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 98057) rows (by decide) (by decide)).symm.trans contract6128_6

theorem contract6128_7 : P.leaf 30 98058 = 18176 := by
  exact leaf_contract_factors (k := 30) (b := 19) (H := 98058) (ss := [(2, 1, 468), (12, 1, 867), (5, 1, 411), (3, 1, 409), (4, 1, 410), (6, 1, 458), (10, 1, 458), (11, 1, 459), (18, 1, 879), (29, 1, 916), (27, 1, 1258)]) (ids := [5, 6, 7, 11, 12, 13, 14, 15, 17, 18, 19, 21, 22, 23, 24, 26, 28, 29, 20]) (cs := [1, 1, 1, 1, 1, 2, 3, 4, 1, 1, 1, 5, 6, 7, 8, 9, 1, 10, 11, 12, 20, 13, 14, 15, 16, 1, 17, 1, 18, 19]) (bs := [18, 1]) (W := 18176) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c6128_7 : P.sumLeaves 24 6275712 64 = 18176 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 98058) rows (by decide) (by decide)).symm.trans contract6128_7

theorem contract6128_8 : P.leaf 30 98059 = 18176 := by
  exact leaf_contract_factors (k := 30) (b := 19) (H := 98059) (ss := [(2, 1, 468), (12, 1, 867), (5, 1, 411), (3, 1, 409), (4, 1, 410), (6, 1, 458), (10, 1, 458), (11, 1, 459), (18, 1, 879), (29, 1, 916), (27, 1, 1601)]) (ids := [5, 6, 7, 11, 12, 13, 14, 15, 17, 18, 19, 21, 22, 24, 26, 28, 29, 20, 23]) (cs := [1, 1, 1, 1, 1, 2, 3, 4, 1, 1, 1, 5, 6, 7, 8, 9, 1, 10, 11, 12, 19, 13, 14, 20, 15, 1, 16, 1, 17, 18]) (bs := [17, 2]) (W := 18176) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c6128_8 : P.sumLeaves 24 6275776 64 = 18176 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 98059) rows (by decide) (by decide)).symm.trans contract6128_8

theorem contract6128_9 : P.leaf 30 98060 = 26112 := by
  exact leaf_contract_factors (k := 30) (b := 18) (H := 98060) (ss := [(2, 1, 468), (12, 1, 867), (5, 1, 411), (3, 1, 409), (4, 1, 410), (6, 1, 458), (10, 1, 458), (11, 1, 459), (14, 1, 874), (16, 1, 874), (31, 1, 909), (28, 1, 860)]) (ids := [5, 6, 7, 11, 13, 15, 16, 17, 18, 19, 22, 23, 24, 25, 27, 28, 20, 21]) (cs := [1, 1, 1, 1, 1, 2, 3, 4, 1, 1, 1, 5, 1, 6, 1, 7, 8, 9, 10, 11, 18, 19, 12, 13, 14, 15, 1, 16, 17, 1]) (bs := [16, 2]) (W := 26112) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c6128_9 : P.sumLeaves 24 6275840 64 = 26112 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 98060) rows (by decide) (by decide)).symm.trans contract6128_9

theorem contract6128_10 : P.leaf 30 98061 = 26112 := by
  exact leaf_contract_factors (k := 30) (b := 18) (H := 98061) (ss := [(2, 1, 468), (12, 1, 867), (5, 1, 411), (3, 1, 409), (4, 1, 410), (6, 1, 458), (10, 1, 458), (11, 1, 459), (14, 1, 874), (16, 1, 874), (31, 1, 909), (28, 1, 860)]) (ids := [5, 6, 7, 11, 13, 15, 16, 17, 18, 19, 22, 23, 24, 25, 27, 28, 20, 21]) (cs := [1, 1, 1, 1, 1, 2, 3, 4, 1, 1, 1, 5, 1, 6, 1, 7, 8, 9, 10, 11, 18, 19, 12, 13, 14, 15, 1, 16, 17, 1]) (bs := [16, 2]) (W := 26112) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c6128_10 : P.sumLeaves 24 6275904 64 = 26112 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 98061) rows (by decide) (by decide)).symm.trans contract6128_10

theorem c6128_11 : P.sumLeaves 24 6275968 128 = 193056 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6128) (lo := 896) (len := 128) (W := 193056) check rows elimOK (by decide) (by decide) cover6128 (by decide)
  decide +kernel

theorem h6128 : P.leaf 34 6128 = 381904 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(64, 16), (64, 0), (256, 27552), (64, 31232), (64, 31232), (64, 5120), (64, 5120), (64, 18176), (64, 18176), (64, 26112), (64, 26112), (128, 193056)]) (.cons c6128_0 (.cons c6128_1 (.cons c6128_2 (.cons c6128_3 (.cons c6128_4 (.cons c6128_5 (.cons c6128_6 (.cons c6128_7 (.cons c6128_8 (.cons c6128_9 (.cons c6128_10 (.cons c6128_11 (.nil))))))))))))) (by decide) (by decide))

theorem cover6129 : P.CoversSplit 24 10 6129 0xffffffffa0a0a0a0ffccffcca080a080ffffffff00000000ffccffcc00000000cc00cc0080008000cc00cc0080008000cc00cc0000000000cc00cc0000000000ff00ff00a000a000ff00ff00a000a000ffffffff00000000ffccffcc0000000000ff00ff0080008000cc00cc0080008000cc00cc0000000000cc00cc00000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 860, 916, 1202, 1258, 1601, 1609]) (ps := [(12, [478], [909, 916]), (14, [923], [916])]) (by decide +kernel)

theorem contract6129_0 : P.leaf 30 98064 = 12224 := by
  exact leaf_contract_factors (k := 30) (b := 17) (H := 98064) (ss := [(2, 1, 475), (6, 1, 478), (12, 1, 478), (31, 1, 909), (29, 0, 916), (27, 1, 473), (18, 11, 921), (11, 1, 965), (25, 1, 915), (14, 1, 965), (8, 1, 1609), (16, 1, 874), (13, 1, 922)]) (ids := [1, 2, 3, 5, 7, 8, 13, 15, 17, 18, 19, 20, 22, 24, 26, 28, 21]) (cs := [1, 2, 3, 4, 1, 5, 1, 6, 7, 1, 1, 1, 1, 8, 1, 9, 1, 10, 11, 12, 13, 18, 14, 1, 15, 1, 16, 0, 17, 1]) (bs := [16, 1]) (W := 12224) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c6129_0 : P.sumLeaves 24 6276096 64 = 12224 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 98064) rows (by decide) (by decide)).symm.trans contract6129_0

theorem contract6129_1 : P.leaf 30 98065 = 27648 := by
  exact leaf_contract_factors (k := 30) (b := 18) (H := 98065) (ss := [(2, 1, 475), (6, 1, 478), (12, 1, 478), (31, 1, 909), (29, 0, 916), (18, 11, 921), (11, 1, 965), (14, 1, 965), (8, 1, 1609), (16, 1, 874), (13, 1, 922), (27, 1, 1609)]) (ids := [1, 2, 3, 5, 7, 8, 13, 15, 17, 18, 19, 20, 22, 23, 24, 26, 28, 21]) (cs := [1, 2, 3, 4, 1, 5, 1, 6, 7, 1, 1, 1, 1, 8, 1, 9, 1, 10, 11, 12, 13, 19, 14, 15, 16, 1, 17, 0, 18, 1]) (bs := [17, 1]) (W := 27648) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c6129_1 : P.sumLeaves 24 6276160 64 = 27648 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 98065) rows (by decide) (by decide)).symm.trans contract6129_1

theorem c6129_2 : P.sumLeaves 24 6276224 312 = 724320 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6129) (lo := 128) (len := 312) (W := 724320) check rows elimOK (by decide) (by decide) cover6129 (by decide)
  decide +kernel

theorem c6129_3 : P.sumLeaves 24 6276536 432 = 2695416 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6129) (lo := 440) (len := 432) (W := 2695416) check rows elimOK (by decide) (by decide) cover6129 (by decide)
  decide +kernel

theorem c6129_4 : P.sumLeaves 24 6276968 152 = 5050211 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6129) (lo := 872) (len := 152) (W := 5050211) check rows elimOK (by decide) (by decide) cover6129 (by decide)
  decide +kernel

theorem h6129 : P.leaf 34 6129 = 8509819 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(64, 12224), (64, 27648), (312, 724320), (432, 2695416), (152, 5050211)]) (.cons c6129_0 (.cons c6129_1 (.cons c6129_2 (.cons c6129_3 (.cons c6129_4 (.nil)))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(6012, 48), (6013, 48), (6014, 48), (6015, 48), (6112, 24), (6113, 48), (6115, 24), (6116, 24), (6117, 48), (6119, 24), (6120, 24), (6121, 48), (6123, 24), (6124, 24), (6125, 48), (6127, 24), (6128, 24), (6129, 48)]

theorem segOK : checkSeg 16 perms 6012 6131 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 6012 6131 648 15601008384 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 15601008384)
    (SegSum.cons (w := 48) h6012 (SegSum.cons (w := 48) h6013 (SegSum.cons (w := 48) h6014 (SegSum.cons (w := 48) h6015 (SegSum.cons (w := 24) h6112 (SegSum.cons (w := 48) h6113 (SegSum.cons (w := 24) h6115 (SegSum.cons (w := 24) h6116 (SegSum.cons (w := 48) h6117 (SegSum.cons (w := 24) h6119 (SegSum.cons (w := 24) h6120 (SegSum.cons (w := 48) h6121 (SegSum.cons (w := 24) h6123 (SegSum.cons (w := 24) h6124 (SegSum.cons (w := 48) h6125 (SegSum.cons (w := 24) h6127 (SegSum.cons (w := 24) h6128 (SegSum.cons (w := 48) h6129 (show SegSum (P.leaf 34) [] 0 from rfl))))))))))))))))))) (by decide)

end RACert.S4N1.C0.S37
