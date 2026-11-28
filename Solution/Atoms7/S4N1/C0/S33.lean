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

namespace RACert.S4N1.C0.S33

open RACert RACert.Problem

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

theorem c6015_2 : P.sumLeaves 24 6159488 128 = 12000 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6015) (lo := 128) (len := 128) (W := 12000) check rows elimOK (by decide) (by decide) cover6015 (by decide)
  decide +kernel

theorem contract6015_3 : P.leaf 30 96244 = 0 := by
  exact leaf_contract_zero (ss := [(8, 0, 1272), (5, 1, 622), (14, 1, 1266)]) (q := 1272) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c6015_3 : P.sumLeaves 24 6159616 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 96244) rows (by decide) (by decide)).symm.trans contract6015_3

theorem contract6015_4 : P.leaf 30 96245 = 0 := by
  exact leaf_contract_zero (ss := [(8, 0, 1272), (5, 1, 622), (14, 1, 1266)]) (q := 1272) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c6015_4 : P.sumLeaves 24 6159680 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 96245) rows (by decide) (by decide)).symm.trans contract6015_4

theorem c6015_5 : P.sumLeaves 24 6159744 190 = 15596483 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6015) (lo := 384) (len := 190) (W := 15596483) check rows elimOK (by decide) (by decide) cover6015 (by decide)
  decide +kernel

theorem c6015_6 : P.sumLeaves 24 6159934 298 = 30602398 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6015) (lo := 574) (len := 298) (W := 30602398) check rows elimOK (by decide) (by decide) cover6015 (by decide)
  decide +kernel

theorem c6015_7 : P.sumLeaves 24 6160232 136 = 70320218 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6015) (lo := 872) (len := 136) (W := 70320218) check rows elimOK (by decide) (by decide) cover6015 (by decide)
  decide +kernel

theorem c6015_8 : P.sumLeaves 24 6160368 16 = 19733706 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6015) (lo := 1008) (len := 16) (W := 19733706) check rows elimOK (by decide) (by decide) cover6015 (by decide)
  decide +kernel

theorem h6015 : P.leaf 34 6015 = 136264805 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(64, 0), (64, 0), (128, 12000), (64, 0), (64, 0), (190, 15596483), (298, 30602398), (136, 70320218), (16, 19733706)]) (.cons c6015_0 (.cons c6015_1 (.cons c6015_2 (.cons c6015_3 (.cons c6015_4 (.cons c6015_5 (.cons c6015_6 (.cons c6015_7 (.cons c6015_8 (.nil)))))))))) (by decide) (by decide))

theorem cover11618 : P.CoversSplit 24 10 11618 0x8000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [417, 465, 466, 515, 522, 523, 565, 572, 858, 865, 1209, 1210, 1258, 1266]) (ps := [(5, [453], [474])]) (by decide +kernel)

theorem h11618 : P.leaf 34 11618 = 23648 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 11618) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 11618) (weight := fun _ => 1) (xs := [511, 895, 1023]) check rows elimOK (by decide) (by decide) cover11618 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h6112 : P.leaf 34 6112 = 23648 :=
  orient32 (v := 11618) (by decide) (by decide +kernel) h11618

theorem cover19341 : P.CoversSplit 24 10 19341 0x8800880000000000880088000000000080000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000088008800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 515, 516, 522, 528, 859, 916, 921, 1210, 1259]) (ps := [(14, [923], [1266])]) (by decide +kernel)

theorem h19341 : P.leaf 34 19341 = 676930 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 19341) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 19341) (weight := fun _ => 1) (xs := [491, 495, 507, 511, 831, 895, 939, 943, 955, 959, 1003, 1007, 1019, 1023]) check rows elimOK (by decide) (by decide) cover19341 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h6113 : P.leaf 34 6113 = 676930 :=
  orient4 (v := 19341) (by decide) (by decide +kernel) h19341

theorem cover6115 : P.CoversSplit 24 10 6115 0xffff0000000000000000000000000000ffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffff0000000000000000000000000000ffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 522, 523, 860, 916, 1202, 1209, 1251, 1258, 1259, 1264]) (by decide +kernel)

noncomputable def f6115 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (6261760 + i)

theorem c6115_0 : rowSum f6115 0 1024 = 6465310 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 6115) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover6115 (by decide)
  decide +kernel

theorem sum6115 : rowSum f6115 0 1024 = 6465310 :=
  c6115_0

theorem h6115 : P.leaf 34 6115 = 6465310 :=
  leaf_weighted (k := 24) (d := 10) (H := 6115) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 6115) (by decide) (by decide +kernel)) sum6115

theorem cover6116 : P.CoversSplit 24 10 6116 0x8888000000000000000000000000000080800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000088000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 515, 522, 524, 566, 860, 916, 1202, 1209, 1258, 1259]) (by decide +kernel)

theorem h6116 : P.leaf 34 6116 = 375448 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 6116) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 6116) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 6116) (weight := rowWeight keep0 twice0) (xs := [383, 507, 511, 887, 895, 1011, 1015, 1019, 1023]) check rows elimOK (by decide) (by decide) cover6116 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover6117 : P.CoversSplit 24 10 6117 0xcccc0000000000000000000000000000cccc00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000cc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 515, 522, 524, 566, 860, 916, 1202, 1209, 1251, 1259]) (by decide +kernel)

theorem h6117 : P.leaf 34 6117 = 6530130 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 6117) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 6117) (weight := fun _ => 1) (xs := [378, 379, 382, 383, 506, 507, 510, 511, 882, 883, 886, 887, 890, 891, 894, 895, 1010, 1011, 1014, 1015, 1018, 1019, 1022, 1023]) check rows elimOK (by decide) (by decide) cover6117 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover6119 : P.CoversSplit 24 10 6119 0xffff0000000000000000000000000000ffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffff0000000000000000000000000000ffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 522, 524, 566, 860, 916, 1202, 1209, 1251, 1258, 1259, 1264]) (by decide +kernel)

noncomputable def f6119 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (6265856 + i)

theorem c6119_0 : rowSum f6119 0 1024 = 34885870 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 6119) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover6119 (by decide)
  decide +kernel

theorem sum6119 : rowSum f6119 0 1024 = 34885870 :=
  c6119_0

theorem h6119 : P.leaf 34 6119 = 34885870 :=
  leaf_weighted (k := 24) (d := 10) (H := 6119) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 6119) (by decide) (by decide +kernel)) sum6119

theorem cover6120 : P.CoversSplit 24 10 6120 0x8888000000000000000000000000000080800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000088000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 515, 522, 523, 565, 860, 916, 1202, 1209, 1258, 1259]) (ps := [(14, [874, 923, 1266], [860, 916])]) (by decide +kernel)

theorem h6120 : P.leaf 34 6120 = 405440 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 6120) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 6120) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 6120) (weight := rowWeight keep0 twice0) (xs := [383, 507, 511, 887, 895, 1011, 1015, 1019, 1023]) check rows elimOK (by decide) (by decide) cover6120 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover6121 : P.CoversSplit 24 10 6121 0xcccc0000000000000000000000000000cccc00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000cc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 515, 522, 523, 860, 916, 1202, 1209, 1251, 1259]) (ps := [(14, [923, 1266], [916])]) (by decide +kernel)

theorem h6121 : P.leaf 34 6121 = 3319646 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 6121) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 6121) (weight := fun _ => 1) (xs := [378, 379, 382, 383, 506, 507, 510, 511, 882, 883, 886, 887, 890, 891, 894, 895, 1010, 1011, 1014, 1015, 1018, 1019, 1022, 1023]) check rows elimOK (by decide) (by decide) cover6121 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover6123 : P.CoversSplit 24 10 6123 0xffff0000000000000000000000000000ffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffff0000000000000000000000000000ffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 522, 523, 860, 916, 1202, 1209, 1251, 1258, 1259, 1264]) (by decide +kernel)

noncomputable def f6123 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (6269952 + i)

theorem c6123_0 : rowSum f6123 0 1024 = 13534872 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 6123) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover6123 (by decide)
  decide +kernel

theorem sum6123 : rowSum f6123 0 1024 = 13534872 :=
  c6123_0

theorem h6123 : P.leaf 34 6123 = 13534872 :=
  leaf_weighted (k := 24) (d := 10) (H := 6123) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 6123) (by decide) (by decide +kernel)) sum6123

theorem cover6124 : P.CoversSplit 24 10 6124 0x8888000000000000000000000000000080800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000088000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 515, 522, 860, 916, 1202, 1209, 1258, 1259]) (by decide +kernel)

theorem h6124 : P.leaf 34 6124 = 1413952 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 6124) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 6124) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 6124) (weight := rowWeight keep0 twice0) (xs := [383, 507, 511, 887, 895, 1011, 1015, 1019, 1023]) check rows elimOK (by decide) (by decide) cover6124 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover6125 : P.CoversSplit 24 10 6125 0xcccc0000000000000000000000000000cccc00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000cc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 515, 522, 860, 916, 1202, 1209, 1251, 1259]) (by decide +kernel)

theorem h6125 : P.leaf 34 6125 = 11640168 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 6125) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 6125) (weight := fun _ => 1) (xs := [378, 379, 382, 383, 506, 507, 510, 511, 882, 883, 886, 887, 890, 891, 894, 895, 1010, 1011, 1014, 1015, 1018, 1019, 1022, 1023]) check rows elimOK (by decide) (by decide) cover6125 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover6127 : P.CoversSplit 24 10 6127 0xffff0000000000000000000000000000ffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffff0000000000000000000000000000ffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 522, 860, 916, 1202, 1209, 1251, 1258, 1259, 1264]) (by decide +kernel)

noncomputable def f6127 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (6274048 + i)

theorem c6127_0 : rowSum f6127 0 1024 = 51935302 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 6127) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover6127 (by decide)
  decide +kernel

theorem sum6127 : rowSum f6127 0 1024 = 51935302 :=
  c6127_0

theorem h6127 : P.leaf 34 6127 = 51935302 :=
  leaf_weighted (k := 24) (d := 10) (H := 6127) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 6127) (by decide) (by decide +kernel)) sum6127

theorem cover11619 : P.CoversSplit 24 10 11619 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 515, 522, 523, 565, 572, 858, 865, 1209, 1210, 1217, 1258, 1266, 1651]) (by decide +kernel)

theorem h11619 : P.leaf 34 11619 = 381904 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 11619) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 11619) (weight := fun _ => 1) (xs := [511, 592, 720, 895, 1023]) check rows elimOK (by decide) (by decide) cover11619 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h6128 : P.leaf 34 6128 = 381904 :=
  orient32 (v := 11619) (by decide) (by decide +kernel) h11619

theorem cover11635 : P.CoversSplit 24 10 11635 0xffff0000fffa00000000000000000000ffff0000fffa000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000cc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [480, 572, 858, 866, 867, 908, 915, 1217, 1258, 1264, 1308]) (by decide +kernel)

theorem c11635_0 : P.sumLeaves 24 11914240 1024 = 8509819 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 11635) (lo := 0) (len := 1024) (W := 8509819) check rows elimOK (by decide) (by decide) cover11635 (by decide)
  decide +kernel

theorem h11635 : P.leaf 34 11635 = 8509819 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 8509819)]) (.cons c11635_0 (.nil)) (by decide) (by decide))

theorem h6129 : P.leaf 34 6129 = 8509819 :=
  orient32 (v := 11635) (by decide) (by decide +kernel) h11635

theorem cover12147 : P.CoversSplit 24 10 12147 0xffffffffffff00000000000000000000ffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00cc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [474, 572, 915, 1209, 1217, 1258, 1264, 1308]) (by decide +kernel)

noncomputable def f12147 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 24 (12438528 + i)

theorem c12147_0 : rowSum f12147 0 1024 = 27863492 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 12147) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover12147 (by decide)
  decide +kernel

theorem sum12147 : rowSum f12147 0 1024 = 27863492 :=
  c12147_0

theorem h12147 : P.leaf 34 12147 = 27863492 :=
  leaf_weighted (k := 24) (d := 10) (H := 12147) (keep := keep2) (twice := twice2) rows (by decide) (by decide) (bal2) (invRow2 (H := 12147) (by decide) (by decide +kernel)) sum12147

theorem h6131 : P.leaf 34 6131 = 27863492 :=
  orient32 (v := 12147) (by decide) (by decide +kernel) h12147

theorem cover28003 : P.CoversSplit 24 10 28003 0xcc00cc00c800c8000000000000000000cc000000000000000000000000000000cc00cc00c800c8000000000000000000cc000000000000000000000000000000cc00cc00c800c8000000000000000000cc0004000000000000000000000000000000000000000000003300000032000000000000000000000033000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [466, 515, 522, 572, 858, 865, 1202, 1210, 1601]) (by decide +kernel)

noncomputable def f28003 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 24 (28675072 + i)

theorem c28003_0 : rowSum f28003 0 1024 = 7596399 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 28003) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover28003 (by decide)
  decide +kernel

theorem sum28003 : rowSum f28003 0 1024 = 7596399 :=
  c28003_0

theorem h28003 : P.leaf 34 28003 = 7596399 :=
  leaf_weighted (k := 24) (d := 10) (H := 28003) (keep := keep2) (twice := twice2) rows (by decide) (by decide) (bal2) (invRow2 (H := 28003) (by decide) (by decide +kernel)) sum28003

theorem h6132 : P.leaf 34 6132 = 7596399 :=
  orient32 (v := 28003) (by decide) (by decide +kernel) h28003

theorem cover19375 : P.CoversSplit 24 10 19375 0xffffffffaaaaa0a0ffffffffaaaaa0a0ffff000000000000ffff000000000000cccccccc88888080cccccccc88888080cccc000000000000cccc000000000000ffffffffaaaaa0a00000000000000000ffff55550000000033330000000000000000000000000000330000002200000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [515, 522, 859, 915, 1202, 1210, 1259, 1308, 1601]) (ps := [(17, [1251], [1259]), (18, [1210, 1308], [1264])]) (by decide +kernel)

theorem c19375_0 : P.sumLeaves 24 19840000 638 = 12003756 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 19375) (lo := 0) (len := 638) (W := 12003756) check rows elimOK (by decide) (by decide) cover19375 (by decide)
  decide +kernel

theorem c19375_1 : P.sumLeaves 24 19840638 296 = 19909350 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 19375) (lo := 638) (len := 296) (W := 19909350) check rows elimOK (by decide) (by decide) cover19375 (by decide)
  decide +kernel

theorem c19375_2 : P.sumLeaves 24 19840934 90 = 33595175 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 19375) (lo := 934) (len := 90) (W := 33595175) check rows elimOK (by decide) (by decide) cover19375 (by decide)
  decide +kernel

theorem h19375 : P.leaf 34 19375 = 65508281 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(638, 12003756), (296, 19909350), (90, 33595175)]) (.cons c19375_0 (.cons c19375_1 (.cons c19375_2 (.nil)))) (by decide) (by decide))

theorem h6133 : P.leaf 34 6133 = 65508281 :=
  orient4 (v := 19375) (by decide) (by decide +kernel) h19375

theorem cover28531 : P.CoversSplit 24 10 28531 0xfffffffffafafafafffffffffafafafafffffffffafafafafffffffffafafafaffccffccfac8fac80000000000000000ffccffccfac8fac80000000000000000fffffffffafafafaffff0000fafa0000ffffffff00000000ffff00000000000000000000000000000000000000000000ffcc0000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [572, 915, 1202, 1210, 1259, 1264, 1308, 1601, 1609]) (by decide +kernel)

noncomputable def f28531 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 24 (29215744 + i)

theorem c28531_0 : rowSum f28531 0 603 = 42592714 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 28531) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover28531 (by decide)
  decide +kernel

theorem c28531_1 : rowSum f28531 603 272 = 56775325 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 28531) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover28531 (by decide)
  decide +kernel

theorem c28531_2 : rowSum f28531 875 149 = 122745672 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 28531) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover28531 (by decide)
  decide +kernel

theorem sum28531 : rowSum f28531 0 1024 = 222113711 :=
  rowSum_append (F := f28531) (lo := 0) (n := 603) (m := 421) (A := 42592714) (B := 179520997) c28531_0 (rowSum_append (F := f28531) (lo := 603) (n := 272) (m := 149) (A := 56775325) (B := 122745672) c28531_1 (c28531_2))

theorem h28531 : P.leaf 34 28531 = 222113711 :=
  leaf_weighted (k := 24) (d := 10) (H := 28531) (keep := keep2) (twice := twice2) rows (by decide) (by decide) (bal2) (invRow2 (H := 28531) (by decide) (by decide +kernel)) sum28531

theorem h6135 : P.leaf 34 6135 = 222113711 :=
  orient32 (v := 28531) (by decide) (by decide +kernel) h28531

def seg : List (ℕ × ℕ) := [(6014, 48), (6015, 48), (6112, 24), (6113, 48), (6115, 24), (6116, 24), (6117, 48), (6119, 24), (6120, 24), (6121, 48), (6123, 24), (6124, 24), (6125, 48), (6127, 24), (6128, 24), (6129, 48), (6131, 24), (6132, 24), (6133, 48), (6135, 24)]

theorem segOK : checkSeg 16 perms 6014 6136 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 6014 6136 672 22305138864 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 22305138864)
    (SegSum.cons (w := 48) h6014 (SegSum.cons (w := 48) h6015 (SegSum.cons (w := 24) h6112 (SegSum.cons (w := 48) h6113 (SegSum.cons (w := 24) h6115 (SegSum.cons (w := 24) h6116 (SegSum.cons (w := 48) h6117 (SegSum.cons (w := 24) h6119 (SegSum.cons (w := 24) h6120 (SegSum.cons (w := 48) h6121 (SegSum.cons (w := 24) h6123 (SegSum.cons (w := 24) h6124 (SegSum.cons (w := 48) h6125 (SegSum.cons (w := 24) h6127 (SegSum.cons (w := 24) h6128 (SegSum.cons (w := 48) h6129 (SegSum.cons (w := 24) h6131 (SegSum.cons (w := 24) h6132 (SegSum.cons (w := 48) h6133 (SegSum.cons (w := 24) h6135 (show SegSum (P.leaf 34) [] 0 from rfl))))))))))))))))))))) (by decide)

end RACert.S4N1.C0.S33
