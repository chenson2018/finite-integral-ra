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

namespace RACert.S4N1.C0.S4

open RACert RACert.Problem

theorem cover735 : P.CoversSplit 24 10 735 0xf0000000000000000000000000000000a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [516, 536, 573, 859, 860, 867, 871, 916, 921, 1210, 1251, 1259, 1264]) (ps := [(14, [958], [1266])]) (by decide +kernel)

theorem h735 : P.leaf 34 735 = 928432 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 735) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 735) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 735) (weight := rowWeight keep1 twice1) (xs := [510, 511, 893, 895, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover735 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover996 : P.CoversSplit 24 10 996 0x8000000000000000000000000000000080000000000000000000000000000000000000001111111100000000111100000000000011111010000000001111000080000000000000000000000000000000800000000000000000000000000000000000000011111111000000001100000000000000100010000000000010000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 508, 515, 522, 524, 566, 860, 872, 1217, 1609]) (ps := [(16, [958], [566])]) (by decide +kernel)

noncomputable def f996 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (1019904 + i)

theorem c996_0 : rowSum f996 0 1024 = 274748 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 996) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover996 (by decide)
  decide +kernel

theorem sum996 : rowSum f996 0 1024 = 274748 :=
  c996_0

theorem h996 : P.leaf 34 996 = 274748 :=
  leaf_weighted (k := 24) (d := 10) (H := 996) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 996) (by decide) (by decide +kernel)) sum996

theorem h748 : P.leaf 34 748 = 274748 :=
  orient24 (v := 996) (by decide) (by decide +kernel) h996

theorem cover749 : P.CoversSplit 24 10 749 0xcc000000000000000000000000000000cc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 515, 522, 573, 859, 872, 879, 1209, 1308]) (ps := [(18, [475], [1210])]) (by decide +kernel)

theorem h749 : P.leaf 34 749 = 571888 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 749) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 749) (weight := fun _ => 1) (xs := [506, 507, 510, 511, 890, 891, 894, 895, 1018, 1019, 1022, 1023]) check rows elimOK (by decide) (by decide) cover749 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover750 : P.CoversSplit 24 10 750 0xa0000000000005000000000000000000a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 515, 522, 573, 859, 872, 916, 921, 1217, 1258, 1308]) (ps := [(16, [1308], [1258])]) (by decide +kernel)

theorem h750 : P.leaf 34 750 = 535636 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 750) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 750) (weight := fun _ => 1) (xs := [458, 511, 893, 895, 968, 970, 1021, 1023]) check rows elimOK (by decide) (by decide) cover750 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover751 : P.CoversSplit 24 10 751 0xff000000000050000000000000000000ff0000000000500000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [515, 522, 573, 859, 879, 916, 921, 1209, 1258, 1308]) (ps := [(16, [1308], [1258]), (18, [524], [1210])]) (by decide +kernel)

theorem h751 : P.leaf 34 751 = 2725592 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 751) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 751) (weight := fun _ => 1) (xs := [462, 506, 507, 510, 511, 844, 846, 888, 889, 890, 891, 892, 893, 894, 895, 972, 974, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover751 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover36466 : P.CoversSplit 24 10 36466 0xcc00c800c8000000cc00c800c8000000cc00c800c8000000cc00c800c80000000000000000000000000000000000000000000000000000000000000000000000cc00c800c80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 474, 572, 578, 915, 921, 1202, 1209, 1258, 1308]) (ps := [(8, [622], [1272])]) (by decide +kernel)

noncomputable def f36466 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 24 (37341184 + i)

theorem c36466_0 : rowSum f36466 0 1024 = 2757680 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 36466) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover36466 (by decide)
  decide +kernel

theorem sum36466 : rowSum f36466 0 1024 = 2757680 :=
  c36466_0

theorem h36466 : P.leaf 34 36466 = 2757680 :=
  leaf_weighted (k := 24) (d := 10) (H := 36466) (keep := keep2) (twice := twice2) rows (by decide) (by decide) (bal2) (invRow2 (H := 36466) (by decide) (by decide +kernel)) sum36466

theorem h766 : P.leaf 34 766 = 2757680 :=
  orient5 (v := 36466) (by decide) (by decide +kernel) h36466

theorem cover36467 : P.CoversSplit 24 10 36467 0xcc00cc00c8000000cc00cc00c8000000cc00cc00c8000000cc00cc00c80000000000000000000000000000000000000000000000000000000000000000000000cc00cc00c80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [474, 572, 578, 915, 921, 1202, 1209, 1258, 1308]) (ps := [(8, [622], [1272])]) (by decide +kernel)

noncomputable def f36467 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 24 (37342208 + i)

theorem c36467_0 : rowSum f36467 0 1024 = 12163224 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 36467) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover36467 (by decide)
  decide +kernel

theorem sum36467 : rowSum f36467 0 1024 = 12163224 :=
  c36467_0

theorem h36467 : P.leaf 34 36467 = 12163224 :=
  leaf_weighted (k := 24) (d := 10) (H := 36467) (keep := keep2) (twice := twice2) rows (by decide) (by decide) (bal2) (invRow2 (H := 36467) (by decide) (by decide +kernel)) sum36467

theorem h767 : P.leaf 34 767 = 12163224 :=
  orient5 (v := 36467) (by decide) (by decide +kernel) h36467

theorem cover1004 : P.CoversSplit 24 10 1004 0x8000000000000000000000000000000080000000000000000000000000000000000000001111111100000000111111110000000011111010000000001111101080000000000000000000000000000000800000000000000000000000000000000000000011111111000000001100110000000000100010000000000010001000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 508, 515, 522, 859, 872, 1217, 1609]) (by decide +kernel)

noncomputable def f1004 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (1028096 + i)

theorem c1004_0 : rowSum f1004 0 1024 = 1651870 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 1004) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover1004 (by decide)
  decide +kernel

theorem sum1004 : rowSum f1004 0 1024 = 1651870 :=
  c1004_0

theorem h1004 : P.leaf 34 1004 = 1651870 :=
  leaf_weighted (k := 24) (d := 10) (H := 1004) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 1004) (by decide) (by decide +kernel)) sum1004

theorem cover1005 : P.CoversSplit 24 10 1005 0xcc000000000000000000000000000000cc0000000000000000000000000000000000000000000000003300000000000000000000000000000033000000000000cc004400000000000000000000000000cc0044000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 515, 522, 859, 872, 915, 1209, 1609]) (by decide +kernel)

theorem h1005 : P.leaf 34 1005 = 4653604 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1005) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1005) (weight := fun _ => 1) (xs := [362, 366, 378, 379, 382, 383, 490, 494, 506, 507, 510, 511, 560, 561, 564, 565, 688, 689, 692, 693, 890, 891, 894, 895, 1018, 1019, 1022, 1023]) check rows elimOK (by decide) (by decide) cover1005 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1007 : P.CoversSplit 24 10 1007 0xffff0000000050500000000000000000ffff00000000505033330000000010100000000010001000330000001000100000000000100010003300000010001000ffff5555000050500000000000000000ffff55550000505033331111000010100000000010001000330011001000100000000000100010003300110010001000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 522, 859, 915, 1209, 1258]) (by decide +kernel)

noncomputable def f1007 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (1031168 + i)

theorem c1007_0 : rowSum f1007 0 1024 = 28338415 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 1007) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover1007 (by decide)
  decide +kernel

theorem sum1007 : rowSum f1007 0 1024 = 28338415 :=
  c1007_0

theorem h1007 : P.leaf 34 1007 = 28338415 :=
  leaf_weighted (k := 24) (d := 10) (H := 1007) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 1007) (by decide) (by decide +kernel)) sum1007

theorem cover1023 : P.CoversSplit 24 10 1023 0xfffffffffafaaaaafffffffffafaaaaafffffffffafaaaaafffffffffafaaaaaffccffcc88888888cccccccc88888888ffccffcc88888888cccccccc88888888fffffffffafaaaaafffffffffafaaaaafffffffffafaaaaafffffffffafaaaaaffccffcc88888888cccccccc88888888ffccffcc88888888cccccccc88888888 :=
  coversSplit check rows (by decide) (by decide) (xs := [859, 915, 1209, 1258]) (by decide +kernel)

noncomputable def f1023 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (1047552 + i)

theorem c1023_0 : rowSum f1023 0 246 = 32867030 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 1023) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover1023 (by decide)
  decide +kernel

theorem c1023_1 : rowSum f1023 246 200 = 67029152 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 1023) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover1023 (by decide)
  decide +kernel

theorem c1023_2 : rowSum f1023 446 314 = 135575161 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 1023) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover1023 (by decide)
  decide +kernel

theorem c1023_3 : rowSum f1023 760 264 = 104213439 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 1023) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover1023 (by decide)
  decide +kernel

theorem sum1023 : rowSum f1023 0 1024 = 339684782 :=
  rowSum_append (F := f1023) (lo := 0) (n := 246) (m := 778) (A := 32867030) (B := 306817752) c1023_0 (rowSum_append (F := f1023) (lo := 246) (n := 200) (m := 578) (A := 67029152) (B := 239788600) c1023_1 (rowSum_append (F := f1023) (lo := 446) (n := 314) (m := 264) (A := 135575161) (B := 104213439) c1023_2 (c1023_3)))

theorem h1023 : P.leaf 34 1023 = 339684782 :=
  leaf_weighted (k := 24) (d := 10) (H := 1023) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 1023) (by decide) (by decide +kernel)) sum1023

theorem cover2084 : P.CoversSplit 24 10 2084 0x80008000000080000000000000000000800080000000840000000000000000000000000000000000002000000020000000000000000000000020000000210000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 475, 515, 517, 522, 572, 858, 859, 916, 1202, 1208, 1209]) (by decide +kernel)

theorem h2084 : P.leaf 34 2084 = 15620 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 2084) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 2084) (weight := fun _ => 1) (xs := [16, 21, 53, 149, 181, 330, 335, 367, 383, 463, 495, 511]) check rows elimOK (by decide) (by decide) cover2084 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h1060 : P.leaf 34 1060 = 15620 :=
  orient4 (v := 2084) (by decide) (by decide +kernel) h2084

theorem cover1061 : P.CoversSplit 24 10 1061 0x8000cc000000000000000000000000008000c4000000000000000000000000000000000000000000003300000000000000000000000000000031000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 475, 515, 517, 522, 572, 858, 860, 865, 1202, 1208, 1301]) (by decide +kernel)

theorem h1061 : P.leaf 34 1061 = 114044 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1061) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1061) (weight := fun _ => 1) (xs := [48, 52, 53, 176, 177, 180, 181, 362, 366, 367, 383, 490, 491, 494, 495, 511]) check rows elimOK (by decide) (by decide) cover1061 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1062 : P.CoversSplit 24 10 1062 0x80000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 515, 517, 522, 524, 565, 572, 858, 860, 865, 916, 1202, 1301]) (ps := [(5, [425], [475])]) (by decide +kernel)

theorem h1062 : P.leaf 34 1062 = 80 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1062) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1062) (weight := fun _ => 1) (xs := [383, 511]) check rows elimOK (by decide) (by decide) cover1062 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1063 : P.CoversSplit 24 10 1063 0x80000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [417, 515, 517, 522, 524, 565, 572, 858, 860, 865, 1202, 1301]) (ps := [(5, [425], [475])]) (by decide +kernel)

theorem h1063 : P.leaf 34 1063 = 832 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1063) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1063) (weight := fun _ => 1) (xs := [383, 511]) check rows elimOK (by decide) (by decide) cover1063 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1068 : P.CoversSplit 24 10 1068 0x8000cc00000000000000000000000000800084000000000000000000000000000000000000000000003300000000000000000000000000000021000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 515, 517, 522, 524, 572, 858, 860, 915, 1202, 1208]) (by decide +kernel)

theorem h1068 : P.leaf 34 1068 = 128928 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 1068) (keep := keep2) (twice := twice2) rows (by decide) (by decide) bal2 (invRow2 (H := 1068) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1068) (weight := rowWeight keep2 twice2) (xs := [48, 53, 176, 177, 180, 181, 362, 367, 383, 490, 491, 494, 495, 511]) check rows elimOK (by decide) (by decide) cover1068 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1069 : P.CoversSplit 24 10 1069 0x8000cc00000000000000000000000000800084000000000000000000000000000000000000000000003300000000000000000000000000000021000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 515, 517, 522, 524, 572, 858, 860, 865, 1202, 1208, 1301]) (by decide +kernel)

theorem h1069 : P.leaf 34 1069 = 423256 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 1069) (keep := keep2) (twice := twice2) rows (by decide) (by decide) bal2 (invRow2 (H := 1069) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1069) (weight := rowWeight keep2 twice2) (xs := [48, 53, 176, 177, 180, 181, 362, 367, 383, 490, 491, 494, 495, 511]) check rows elimOK (by decide) (by decide) cover1069 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1070 : P.CoversSplit 24 10 1070 0x80000000000000000000000000000000800000000000000000000000000000000000000000000000002100000000000000000000000000000021000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 515, 517, 522, 524, 565, 572, 858, 865, 915, 1202, 1301]) (by decide +kernel)

theorem h1070 : P.leaf 34 1070 = 1525 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1070) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1070) (weight := fun _ => 1) (xs := [48, 53, 176, 181, 383, 511]) check rows elimOK (by decide) (by decide) cover1070 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1071 : P.CoversSplit 24 10 1071 0x80000000000000000000000000000000800000000000000000000000000000000000000000000000002100000000000000000000000000000021000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 515, 517, 522, 524, 565, 572, 858, 865, 1202, 1301]) (by decide +kernel)

theorem h1071 : P.leaf 34 1071 = 4994 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1071) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1071) (weight := fun _ => 1) (xs := [48, 53, 176, 181, 383, 511]) check rows elimOK (by decide) (by decide) cover1071 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1076 : P.CoversSplit 24 10 1076 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [559]) (by decide +kernel)

theorem h1076 : P.leaf 34 1076 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1076) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1076) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1076 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1077 : P.CoversSplit 24 10 1077 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [559]) (by decide +kernel)

theorem h1077 : P.leaf 34 1077 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1077) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1077) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1077 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1078 : P.CoversSplit 24 10 1078 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem h1078 : P.leaf 34 1078 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1078) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1078) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1078 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1079 : P.CoversSplit 24 10 1079 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem h1079 : P.leaf 34 1079 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1079) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1079) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1079 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1082 : P.CoversSplit 24 10 1082 0xc0000000000000000000000000000000800000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 517, 529, 572, 573, 858, 865, 867, 915, 1251, 1258, 1259]) (ps := [(15, [509], [916])]) (by decide +kernel)

theorem h1082 : P.leaf 34 1082 = 700 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1082) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1082) (weight := fun _ => 1) (xs := [304, 383, 510, 511]) check rows elimOK (by decide) (by decide) cover1082 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1083 : P.CoversSplit 24 10 1083 0xcc0000000000000000000000000000008c0000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [517, 529, 572, 573, 858, 860, 865, 867, 915, 1251, 1258, 1259]) (ps := [(16, [871], [1258])]) (by decide +kernel)

theorem h1083 : P.leaf 34 1083 = 3120 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1083) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1083) (weight := fun _ => 1) (xs := [309, 378, 379, 383, 506, 507, 510, 511]) check rows elimOK (by decide) (by decide) cover1083 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1084 : P.CoversSplit 24 10 1084 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem h1084 : P.leaf 34 1084 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1084) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1084) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1084 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1085 : P.CoversSplit 24 10 1085 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem h1085 : P.leaf 34 1085 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1085) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1085) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1085 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1086 : P.CoversSplit 24 10 1086 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem h1086 : P.leaf 34 1086 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1086) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1086) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1086 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1087 : P.CoversSplit 24 10 1087 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem h1087 : P.leaf 34 1087 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1087) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1087) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1087 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1092 : P.CoversSplit 24 10 1092 0x80008000000080000000000000000000800080000000040000000000000000000000000000000000002000000020000000000000000000000020000000010000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 475, 515, 516, 522, 572, 573, 858, 860, 916, 1202, 1208, 1209]) (by decide +kernel)

theorem h1092 : P.leaf 34 1092 = 23036 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1092) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1092) (weight := fun _ => 1) (xs := [16, 53, 149, 181, 330, 367, 383, 463, 495, 511]) check rows elimOK (by decide) (by decide) cover1092 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1093 : P.CoversSplit 24 10 1093 0x8000cc000000800000000000000000008000cc000000800000000000000000000000000000000000003300000020000000000000000000000033000000200000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 475, 515, 516, 522, 572, 858, 865, 1202, 1208, 1209]) (by decide +kernel)

theorem h1093 : P.leaf 34 1093 = 453312 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 1093) (keep := keep3) (twice := twice3) rows (by decide) (by decide) bal3 (invRow3 (H := 1093) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1093) (weight := rowWeight keep3 twice3) (xs := [21, 48, 49, 52, 53, 149, 176, 177, 180, 181, 335, 362, 363, 366, 367, 383, 463, 490, 491, 494, 495, 511]) check rows elimOK (by decide) (by decide) cover1093 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1094 : P.CoversSplit 24 10 1094 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [565]) (by decide +kernel)

theorem h1094 : P.leaf 34 1094 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1094) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1094) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1094 (by decide) (by decide) (by decide +kernel)
  decide +kernel

def seg : List (ℕ × ℕ) := [(735, 24), (748, 24), (749, 24), (750, 48), (751, 48), (766, 24), (767, 24), (1004, 4), (1005, 12), (1007, 12), (1023, 4), (1060, 24), (1061, 24), (1062, 48), (1063, 48), (1068, 24), (1069, 24), (1070, 24), (1071, 24), (1076, 24), (1077, 24), (1078, 48), (1079, 48), (1082, 24), (1083, 24), (1084, 48), (1085, 48), (1086, 48), (1087, 48), (1092, 8), (1093, 8), (1094, 24)]

theorem segOK : checkSeg 16 perms 735 1095 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 735 1095 912 2338960156 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 2338960156)
    (SegSum.cons (w := 24) h735 (SegSum.cons (w := 24) h748 (SegSum.cons (w := 24) h749 (SegSum.cons (w := 48) h750 (SegSum.cons (w := 48) h751 (SegSum.cons (w := 24) h766 (SegSum.cons (w := 24) h767 (SegSum.cons (w := 4) h1004 (SegSum.cons (w := 12) h1005 (SegSum.cons (w := 12) h1007 (SegSum.cons (w := 4) h1023 (SegSum.cons (w := 24) h1060 (SegSum.cons (w := 24) h1061 (SegSum.cons (w := 48) h1062 (SegSum.cons (w := 48) h1063 (SegSum.cons (w := 24) h1068 (SegSum.cons (w := 24) h1069 (SegSum.cons (w := 24) h1070 (SegSum.cons (w := 24) h1071 (SegSum.cons (w := 24) h1076 (SegSum.cons (w := 24) h1077 (SegSum.cons (w := 48) h1078 (SegSum.cons (w := 48) h1079 (SegSum.cons (w := 24) h1082 (SegSum.cons (w := 24) h1083 (SegSum.cons (w := 48) h1084 (SegSum.cons (w := 48) h1085 (SegSum.cons (w := 48) h1086 (SegSum.cons (w := 48) h1087 (SegSum.cons (w := 8) h1092 (SegSum.cons (w := 8) h1093 (SegSum.cons (w := 24) h1094 (show SegSum (P.leaf 34) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S4N1.C0.S4
