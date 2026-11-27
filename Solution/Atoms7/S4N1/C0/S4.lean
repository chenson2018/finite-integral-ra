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

noncomputable def f735 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (752640 + i)

theorem c735_0 : rowSum f735 0 1024 = 928432 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 735) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover735 (by decide)
  decide +kernel

theorem sum735 : rowSum f735 0 1024 = 928432 :=
  c735_0

theorem h735 : P.leaf 34 735 = 928432 :=
  leaf_weighted (k := 24) (d := 10) (H := 735) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 735) (by decide) (by decide +kernel)) sum735

theorem cover748 : P.CoversSplit 24 10 748 0x8000000000000000000000000000000080000000000000000000000000000000000000001111111100000000110011000000000011111010000000001100100080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 508, 515, 522, 573, 859, 872, 1217, 1308, 1651]) (by decide +kernel)

theorem c748_0 : P.sumLeaves 24 765952 1024 = 274748 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 748) (lo := 0) (len := 1024) (W := 274748) check rows elimOK (by decide) (by decide) cover748 (by decide)
  decide +kernel

theorem h748 : P.leaf 34 748 = 274748 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 274748)]) (.cons c748_0 (.nil)) (by decide) (by decide))

theorem cover749 : P.CoversSplit 24 10 749 0xcc000000000000000000000000000000cc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 515, 522, 573, 859, 872, 879, 1209, 1308]) (ps := [(18, [475], [1210])]) (by decide +kernel)

theorem c749_0 : P.sumLeaves 24 766976 448 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 749) (lo := 0) (len := 448) (W := 0) check rows elimOK (by decide) (by decide) cover749 (by decide)
  decide +kernel

theorem contract749_1 : P.leaf 30 11991 = 25712 := by
  exact leaf_contract_factors (k := 30) (b := 19) (H := 11991) (ss := [(27, 1, 473), (29, 1, 473), (18, 1, 475), (12, 1, 866), (11, 1, 818), (31, 1, 872), (13, 1, 922), (14, 1, 923), (30, 1, 1210), (16, 1, 1265), (20, 1, 1657)]) (ids := [0, 1, 2, 3, 4, 5, 6, 7, 8, 13, 15, 17, 19, 20, 21, 22, 24, 26, 23]) (cs := [2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 1, 1, 1, 11, 1, 12, 1, 13, 1, 14, 15, 16, 17, 20, 18, 1, 19, 1, 1, 1]) (bs := [18, 1]) (W := 25712) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c749_1 : P.sumLeaves 24 767424 64 = 25712 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 11991) rows (by decide) (by decide)).symm.trans contract749_1

theorem c749_2 : P.sumLeaves 24 767488 512 = 546176 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 749) (lo := 512) (len := 512) (W := 546176) check rows elimOK (by decide) (by decide) cover749 (by decide)
  decide +kernel

theorem h749 : P.leaf 34 749 = 571888 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(448, 0), (64, 25712), (512, 546176)]) (.cons c749_0 (.cons c749_1 (.cons c749_2 (.nil)))) (by decide) (by decide))

theorem cover750 : P.CoversSplit 24 10 750 0xa0000000000005000000000000000000a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 515, 522, 573, 859, 872, 916, 921, 1217, 1258, 1308]) (ps := [(16, [1308], [1258])]) (by decide +kernel)

theorem c750_0 : P.sumLeaves 24 768000 1024 = 535636 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 750) (lo := 0) (len := 1024) (W := 535636) check rows elimOK (by decide) (by decide) cover750 (by decide)
  decide +kernel

theorem h750 : P.leaf 34 750 = 535636 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 535636)]) (.cons c750_0 (.nil)) (by decide) (by decide))

theorem cover751 : P.CoversSplit 24 10 751 0xff000000000050000000000000000000ff0000000000500000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [515, 522, 573, 859, 879, 916, 921, 1209, 1258, 1308]) (ps := [(16, [1308], [1258]), (18, [524], [1210])]) (by decide +kernel)

theorem c751_0 : P.sumLeaves 24 769024 1024 = 2725592 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 751) (lo := 0) (len := 1024) (W := 2725592) check rows elimOK (by decide) (by decide) cover751 (by decide)
  decide +kernel

theorem h751 : P.leaf 34 751 = 2725592 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 2725592)]) (.cons c751_0 (.nil)) (by decide) (by decide))

theorem cover766 : P.CoversSplit 24 10 766 0xf500f500550000000000000000000000f500f5005500000000000000000000000000000000000000000000000000000000000000000000000000000000000000c000c000440000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 573, 859, 866, 916, 921, 1209, 1217, 1259, 1264, 1308]) (ps := [(14, [874], [859])]) (by decide +kernel)

theorem c766_0 : P.sumLeaves 24 784384 1024 = 2757680 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 766) (lo := 0) (len := 1024) (W := 2757680) check rows elimOK (by decide) (by decide) cover766 (by decide)
  decide +kernel

theorem h766 : P.leaf 34 766 = 2757680 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 2757680)]) (.cons c766_0 (.nil)) (by decide) (by decide))

theorem cover767 : P.CoversSplit 24 10 767 0xff00ff00fa0000000000000000000000ff00ff00fa00000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00c80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [573, 859, 867, 916, 921, 1209, 1210, 1259, 1264, 1308]) (by decide +kernel)

theorem c767_0 : P.sumLeaves 24 785408 1024 = 12163224 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 767) (lo := 0) (len := 1024) (W := 12163224) check rows elimOK (by decide) (by decide) cover767 (by decide)
  decide +kernel

theorem h767 : P.leaf 34 767 = 12163224 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 12163224)]) (.cons c767_0 (.nil)) (by decide) (by decide))

theorem cover1004 : P.CoversSplit 24 10 1004 0x8000000000000000000000000000000080000000000000000000000000000000000000001111111100000000111111110000000011111010000000001111101080000000000000000000000000000000800000000000000000000000000000000000000011111111000000001100110000000000100010000000000010001000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 508, 515, 522, 859, 872, 1217, 1609]) (by decide +kernel)

noncomputable def f1004 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (1028096 + i)

theorem c1004_0 : rowSum f1004 0 1024 = 1651870 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 1004) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover1004 (by decide)
  decide +kernel

theorem sum1004 : rowSum f1004 0 1024 = 1651870 :=
  c1004_0

theorem h1004 : P.leaf 34 1004 = 1651870 :=
  leaf_weighted (k := 24) (d := 10) (H := 1004) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 1004) (by decide) (by decide +kernel)) sum1004

theorem cover1005 : P.CoversSplit 24 10 1005 0xcc000000000000000000000000000000cc0000000000000000000000000000000000000000000000003300000000000000000000000000000033000000000000cc004400000000000000000000000000cc0044000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 515, 522, 859, 872, 915, 1209, 1609]) (by decide +kernel)

theorem c1005_0 : P.sumLeaves 24 1029120 1024 = 4653604 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1005) (lo := 0) (len := 1024) (W := 4653604) check rows elimOK (by decide) (by decide) cover1005 (by decide)
  decide +kernel

theorem h1005 : P.leaf 34 1005 = 4653604 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 4653604)]) (.cons c1005_0 (.nil)) (by decide) (by decide))

theorem cover1007 : P.CoversSplit 24 10 1007 0xffff0000000050500000000000000000ffff00000000505033330000000010100000000010001000330000001000100000000000100010003300000010001000ffff5555000050500000000000000000ffff55550000505033331111000010100000000010001000330011001000100000000000100010003300110010001000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 522, 859, 915, 1209, 1258]) (by decide +kernel)

noncomputable def f1007 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (1031168 + i)

theorem c1007_0 : rowSum f1007 0 1024 = 28338415 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 1007) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover1007 (by decide)
  decide +kernel

theorem sum1007 : rowSum f1007 0 1024 = 28338415 :=
  c1007_0

theorem h1007 : P.leaf 34 1007 = 28338415 :=
  leaf_weighted (k := 24) (d := 10) (H := 1007) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 1007) (by decide) (by decide +kernel)) sum1007

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
  leaf_weighted (k := 24) (d := 10) (H := 1023) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 1023) (by decide) (by decide +kernel)) sum1023

theorem cover1060 : P.CoversSplit 24 10 1060 0x8000cc000000000000000000000000008000c4000000000000000000000000000000000000000000003300000000000000000000000000000031000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 475, 515, 517, 522, 572, 858, 860, 916, 1202, 1208]) (by decide +kernel)

theorem c1060_0 : P.sumLeaves 24 1085440 320 = 7770 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1060) (lo := 0) (len := 320) (W := 7770) check rows elimOK (by decide) (by decide) cover1060 (by decide)
  decide +kernel

theorem contract1060_1 : P.leaf 30 16965 = 134 := by
  exact leaf_contract_factors (k := 30) (b := 16) (H := 16965) (ss := [(8, 0, 468), (27, 1, 473), (29, 1, 473), (19, 11, 474), (18, 4, 487), (30, 11, 523), (21, 0, 531), (20, 1, 537), (11, 4, 558), (5, 1, 601), (31, 1, 615), (14, 0, 629), (16, 3, 486), (26, 9, 510)]) (ids := [0, 1, 2, 4, 5, 7, 8, 10, 11, 13, 15, 20, 21, 22, 26, 23]) (cs := [2, 3, 4, 1, 5, 6, 0, 7, 8, 4, 9, 10, 0, 11, 3, 12, 4, 4, 1, 0, 13, 14, 15, 17, 7, 1, 16, 1, 4, 1]) (bs := [15, 1]) (W := 134) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1060_1 : P.sumLeaves 24 1085760 64 = 134 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 16965) rows (by decide) (by decide)).symm.trans contract1060_1

theorem c1060_2 : P.sumLeaves 24 1085824 640 = 7716 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1060) (lo := 384) (len := 640) (W := 7716) check rows elimOK (by decide) (by decide) cover1060 (by decide)
  decide +kernel

theorem h1060 : P.leaf 34 1060 = 15620 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(320, 7770), (64, 134), (640, 7716)]) (.cons c1060_0 (.cons c1060_1 (.cons c1060_2 (.nil)))) (by decide) (by decide))

theorem cover1061 : P.CoversSplit 24 10 1061 0x8000cc000000000000000000000000008000c4000000000000000000000000000000000000000000003300000000000000000000000000000031000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 475, 515, 517, 522, 572, 858, 860, 865, 1202, 1208, 1301]) (by decide +kernel)

theorem c1061_0 : P.sumLeaves 24 1086464 1024 = 114044 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1061) (lo := 0) (len := 1024) (W := 114044) check rows elimOK (by decide) (by decide) cover1061 (by decide)
  decide +kernel

theorem h1061 : P.leaf 34 1061 = 114044 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 114044)]) (.cons c1061_0 (.nil)) (by decide) (by decide))

theorem h1062 : P.leaf 34 1062 = 80 := by
  exact leaf_contract_factors (k := 34) (b := 8) (H := 1062) (ss := [(32, 10, 466), (33, 8, 468), (10, 3, 472), (30, 19, 523), (35, 0, 524), (34, 5, 475), (5, 1, 425), (12, 1, 480), (3, 1, 458), (6, 1, 458), (16, 1, 486), (27, 1, 522), (18, 1, 536), (4, 1, 426), (19, 1, 565), (26, 1, 515), (9, 1, 510), (7, 1, 579), (11, 1, 809), (28, 1, 858), (29, 1, 865), (13, 1, 922), (15, 1, 930), (31, 1, 1202), (17, 1, 1273), (20, 1, 1657)]) (ids := [0, 6, 12, 19, 20, 21, 22, 23]) (cs := [2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 5, 6, 7, 8, 9, 1, 1, 1, 1, 1, 1, 1, 3, 1, 0]) (bs := [4, 4]) (W := 80) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem h1063 : P.leaf 34 1063 = 832 := by
  exact leaf_contract_factors (k := 34) (b := 12) (H := 1063) (ss := [(30, 19, 523), (35, 0, 524), (34, 5, 475), (5, 1, 425), (12, 1, 480), (27, 1, 522), (32, 1, 522), (18, 1, 536), (4, 1, 426), (19, 1, 565), (26, 1, 515), (7, 1, 579), (9, 1, 587), (11, 1, 817), (28, 1, 858), (29, 1, 865), (13, 1, 922), (15, 1, 930), (31, 1, 1202), (16, 1, 1265), (17, 1, 1273), (20, 1, 1657)]) (ids := [0, 1, 4, 6, 8, 12, 19, 31, 20, 21, 22, 23]) (cs := [2, 3, 1, 1, 4, 1, 5, 1, 6, 1, 1, 1, 7, 1, 1, 1, 1, 1, 1, 8, 10, 11, 12, 13, 1, 1, 1, 1, 1, 1, 1, 9, 1, 0]) (bs := [8, 4]) (W := 832) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem cover1068 : P.CoversSplit 24 10 1068 0x8000cc00000000000000000000000000800084000000000000000000000000000000000000000000003300000000000000000000000000000021000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 515, 517, 522, 524, 572, 858, 860, 915, 1202, 1208]) (by decide +kernel)

noncomputable def f1068 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 24 (1093632 + i)

theorem c1068_0 : rowSum f1068 0 1024 = 128928 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 1068) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover1068 (by decide)
  decide +kernel

theorem sum1068 : rowSum f1068 0 1024 = 128928 :=
  c1068_0

theorem h1068 : P.leaf 34 1068 = 128928 :=
  leaf_weighted (k := 24) (d := 10) (H := 1068) (keep := keep2) (twice := twice2) rows (by decide) (by decide) bal2 (invRow2 (H := 1068) (by decide) (by decide +kernel)) sum1068

theorem cover1069 : P.CoversSplit 24 10 1069 0x8000cc00000000000000000000000000800084000000000000000000000000000000000000000000003300000000000000000000000000000021000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 515, 517, 522, 524, 572, 858, 860, 865, 1202, 1208, 1301]) (by decide +kernel)

noncomputable def f1069 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 24 (1094656 + i)

theorem c1069_0 : rowSum f1069 0 1024 = 423256 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 1069) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover1069 (by decide)
  decide +kernel

theorem sum1069 : rowSum f1069 0 1024 = 423256 :=
  c1069_0

theorem h1069 : P.leaf 34 1069 = 423256 :=
  leaf_weighted (k := 24) (d := 10) (H := 1069) (keep := keep2) (twice := twice2) rows (by decide) (by decide) bal2 (invRow2 (H := 1069) (by decide) (by decide +kernel)) sum1069

theorem cover1070 : P.CoversSplit 24 10 1070 0x80000000000000000000000000000000800000000000000000000000000000000000000000000000002100000000000000000000000000000021000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 515, 517, 522, 524, 565, 572, 858, 865, 915, 1202, 1301]) (by decide +kernel)

theorem c1070_0 : P.sumLeaves 24 1095680 1024 = 1525 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1070) (lo := 0) (len := 1024) (W := 1525) check rows elimOK (by decide) (by decide) cover1070 (by decide)
  decide +kernel

theorem h1070 : P.leaf 34 1070 = 1525 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1525)]) (.cons c1070_0 (.nil)) (by decide) (by decide))

theorem cover1071 : P.CoversSplit 24 10 1071 0x80000000000000000000000000000000800000000000000000000000000000000000000000000000002100000000000000000000000000000021000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 515, 517, 522, 524, 565, 572, 858, 865, 1202, 1301]) (by decide +kernel)

theorem c1071_0 : P.sumLeaves 24 1096704 1024 = 4994 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1071) (lo := 0) (len := 1024) (W := 4994) check rows elimOK (by decide) (by decide) cover1071 (by decide)
  decide +kernel

theorem h1071 : P.leaf 34 1071 = 4994 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 4994)]) (.cons c1071_0 (.nil)) (by decide) (by decide))

theorem cover1076 : P.CoversSplit 24 10 1076 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [559]) (by decide +kernel)

theorem c1076_0 : P.sumLeaves 24 1101824 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1076) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1076 (by decide)
  decide +kernel

theorem h1076 : P.leaf 34 1076 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1076_0 (.nil)) (by decide) (by decide))

theorem cover1077 : P.CoversSplit 24 10 1077 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [559]) (by decide +kernel)

theorem c1077_0 : P.sumLeaves 24 1102848 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1077) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1077 (by decide)
  decide +kernel

theorem h1077 : P.leaf 34 1077 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1077_0 (.nil)) (by decide) (by decide))

theorem cover1078 : P.CoversSplit 24 10 1078 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem c1078_0 : P.sumLeaves 24 1103872 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1078) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1078 (by decide)
  decide +kernel

theorem h1078 : P.leaf 34 1078 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1078_0 (.nil)) (by decide) (by decide))

theorem cover1079 : P.CoversSplit 24 10 1079 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem c1079_0 : P.sumLeaves 24 1104896 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1079) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1079 (by decide)
  decide +kernel

theorem h1079 : P.leaf 34 1079 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1079_0 (.nil)) (by decide) (by decide))

theorem cover1082 : P.CoversSplit 24 10 1082 0xc0000000000000000000000000000000800000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 517, 529, 572, 573, 858, 865, 867, 915, 1251, 1258, 1259]) (ps := [(15, [509], [916])]) (by decide +kernel)

theorem c1082_0 : P.sumLeaves 24 1107968 1024 = 700 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1082) (lo := 0) (len := 1024) (W := 700) check rows elimOK (by decide) (by decide) cover1082 (by decide)
  decide +kernel

theorem h1082 : P.leaf 34 1082 = 700 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 700)]) (.cons c1082_0 (.nil)) (by decide) (by decide))

theorem cover1083 : P.CoversSplit 24 10 1083 0xcc0000000000000000000000000000008c0000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [517, 529, 572, 573, 858, 860, 865, 867, 915, 1251, 1258, 1259]) (ps := [(16, [871], [1258])]) (by decide +kernel)

theorem c1083_0 : P.sumLeaves 24 1108992 448 = 112 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1083) (lo := 0) (len := 448) (W := 112) check rows elimOK (by decide) (by decide) cover1083 (by decide)
  decide +kernel

theorem contract1083_1 : P.leaf 30 17335 = 3008 := by
  exact leaf_contract_factors (k := 30) (b := 12) (H := 17335) (ss := [(5, 1, 474), (12, 1, 487), (31, 1, 529), (27, 1, 572), (8, 1, 580), (18, 1, 580), (7, 1, 579), (19, 1, 586), (9, 1, 587), (11, 1, 818), (29, 1, 915), (13, 1, 922), (14, 1, 923), (15, 1, 930), (30, 1, 1209), (16, 1, 1265), (17, 1, 1273), (20, 1, 1657)]) (ids := [0, 1, 2, 8, 20, 26, 4, 19, 21, 22, 23, 24]) (cs := [2, 3, 4, 1, 8, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 9, 6, 10, 11, 12, 13, 1, 7, 1, 1, 1]) (bs := [6, 6]) (W := 3008) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1083_1 : P.sumLeaves 24 1109440 64 = 3008 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 17335) rows (by decide) (by decide)).symm.trans contract1083_1

theorem c1083_2 : P.sumLeaves 24 1109504 512 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1083) (lo := 512) (len := 512) (W := 0) check rows elimOK (by decide) (by decide) cover1083 (by decide)
  decide +kernel

theorem h1083 : P.leaf 34 1083 = 3120 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(448, 112), (64, 3008), (512, 0)]) (.cons c1083_0 (.cons c1083_1 (.cons c1083_2 (.nil)))) (by decide) (by decide))

theorem cover1084 : P.CoversSplit 24 10 1084 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem c1084_0 : P.sumLeaves 24 1110016 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1084) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1084 (by decide)
  decide +kernel

theorem h1084 : P.leaf 34 1084 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1084_0 (.nil)) (by decide) (by decide))

theorem cover1085 : P.CoversSplit 24 10 1085 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem c1085_0 : P.sumLeaves 24 1111040 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1085) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1085 (by decide)
  decide +kernel

theorem h1085 : P.leaf 34 1085 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1085_0 (.nil)) (by decide) (by decide))

theorem cover1086 : P.CoversSplit 24 10 1086 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem c1086_0 : P.sumLeaves 24 1112064 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1086) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1086 (by decide)
  decide +kernel

theorem h1086 : P.leaf 34 1086 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1086_0 (.nil)) (by decide) (by decide))

theorem cover1087 : P.CoversSplit 24 10 1087 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [909]) (by decide +kernel)

theorem c1087_0 : P.sumLeaves 24 1113088 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1087) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1087 (by decide)
  decide +kernel

theorem h1087 : P.leaf 34 1087 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1087_0 (.nil)) (by decide) (by decide))

theorem cover1092 : P.CoversSplit 24 10 1092 0x80008000000080000000000000000000800080000000040000000000000000000000000000000000002000000020000000000000000000000020000000010000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 475, 515, 516, 522, 572, 573, 858, 860, 916, 1202, 1208, 1209]) (by decide +kernel)

theorem c1092_0 : P.sumLeaves 24 1118208 1024 = 23036 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1092) (lo := 0) (len := 1024) (W := 23036) check rows elimOK (by decide) (by decide) cover1092 (by decide)
  decide +kernel

theorem h1092 : P.leaf 34 1092 = 23036 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 23036)]) (.cons c1092_0 (.nil)) (by decide) (by decide))

theorem cover1093 : P.CoversSplit 24 10 1093 0x8000cc000000800000000000000000008000cc000000800000000000000000000000000000000000003300000020000000000000000000000033000000200000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 475, 515, 516, 522, 572, 858, 865, 1202, 1208, 1209]) (by decide +kernel)

noncomputable def f1093 (i : ℕ) := rowWeight keep3 twice3 i * P.leaf 24 (1119232 + i)

theorem c1093_0 : rowSum f1093 0 1024 = 453312 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 1093) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover1093 (by decide)
  decide +kernel

theorem sum1093 : rowSum f1093 0 1024 = 453312 :=
  c1093_0

theorem h1093 : P.leaf 34 1093 = 453312 :=
  leaf_weighted (k := 24) (d := 10) (H := 1093) (keep := keep3) (twice := twice3) rows (by decide) (by decide) bal3 (invRow3 (H := 1093) (by decide) (by decide +kernel)) sum1093

theorem cover1094 : P.CoversSplit 24 10 1094 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [565]) (by decide +kernel)

theorem c1094_0 : P.sumLeaves 24 1120256 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1094) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1094 (by decide)
  decide +kernel

theorem h1094 : P.leaf 34 1094 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1094_0 (.nil)) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(735, 24), (748, 24), (749, 24), (750, 48), (751, 48), (766, 24), (767, 24), (1004, 4), (1005, 12), (1007, 12), (1023, 4), (1060, 24), (1061, 24), (1062, 48), (1063, 48), (1068, 24), (1069, 24), (1070, 24), (1071, 24), (1076, 24), (1077, 24), (1078, 48), (1079, 48), (1082, 24), (1083, 24), (1084, 48), (1085, 48), (1086, 48), (1087, 48), (1092, 8), (1093, 8), (1094, 24)]

theorem segOK : checkSeg 16 perms 735 1095 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 735 1095 912 2338960156 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 2338960156)
    (SegSum.cons (w := 24) h735 (SegSum.cons (w := 24) h748 (SegSum.cons (w := 24) h749 (SegSum.cons (w := 48) h750 (SegSum.cons (w := 48) h751 (SegSum.cons (w := 24) h766 (SegSum.cons (w := 24) h767 (SegSum.cons (w := 4) h1004 (SegSum.cons (w := 12) h1005 (SegSum.cons (w := 12) h1007 (SegSum.cons (w := 4) h1023 (SegSum.cons (w := 24) h1060 (SegSum.cons (w := 24) h1061 (SegSum.cons (w := 48) h1062 (SegSum.cons (w := 48) h1063 (SegSum.cons (w := 24) h1068 (SegSum.cons (w := 24) h1069 (SegSum.cons (w := 24) h1070 (SegSum.cons (w := 24) h1071 (SegSum.cons (w := 24) h1076 (SegSum.cons (w := 24) h1077 (SegSum.cons (w := 48) h1078 (SegSum.cons (w := 48) h1079 (SegSum.cons (w := 24) h1082 (SegSum.cons (w := 24) h1083 (SegSum.cons (w := 48) h1084 (SegSum.cons (w := 48) h1085 (SegSum.cons (w := 48) h1086 (SegSum.cons (w := 48) h1087 (SegSum.cons (w := 8) h1092 (SegSum.cons (w := 8) h1093 (SegSum.cons (w := 24) h1094 (show SegSum (P.leaf 34) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S4N1.C0.S4
