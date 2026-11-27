/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Atoms7.S6N0.C0.Actions

/-! Generated identity-class certificate for the product-row count. -/

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option Elab.async false

@[expose] public section

namespace RACert.S6N0.C0.S22

open RACert RACert.Problem

theorem cover13119 : P.CoversSplit 26 10 13119 0xffff555000001010000000000000000033301110000010101100110000001000555550500000101055555050000010101110101000001010110010000000100033331110333310100000000000000000330011003300100011001100110010001111101011111010111110101111101011001000110010001100100011001000 :=
  coversSplit check rows (by decide) (by decide) (xs := [538, 579, 873, 930, 972, 979, 1265, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f13119 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 26 (13433856 + i)

theorem c13119_0 : rowSum f13119 0 1024 = 1087652 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 13119) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover13119 (by decide)
  decide +kernel

theorem sum13119 : rowSum f13119 0 1024 = 1087652 :=
  c13119_0

theorem h13119 : P.leaf 36 13119 = 1087652 :=
  leaf_weighted (k := 26) (d := 10) (H := 13119) (keep := keep2) (twice := twice2) rows (by decide) (by decide) bal2 (invRow2 (H := 13119) (by decide) (by decide +kernel)) sum13119

theorem cover13168 : P.CoversSplit 26 10 13168 0xa0000000a0000000000000000000000000000000000000000000000000000000000040000000400000004000000040000000000000000000000000000000000000000000000000000000000000000000800000008000000000000000000000000000000000000000000000000000000000004000000040000000400000004000 :=
  coversProjected check rows (by decide) (by decide) (xs := [489, 579, 873, 930, 972, 979, 1265, 1273, 1315, 1322, 1665]) (ps := [(7, [489], [474]), (16, [1273], [867])]) (by decide +kernel)

theorem c13168_0 : P.sumLeaves 26 13484032 960 = 81 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13168) (lo := 0) (len := 960) (W := 81) check rows elimOK (by decide) (by decide) cover13168 (by decide)
  decide +kernel

theorem contract13168_1 : P.leaf 32 210703 = 1024 := by
  exact leaf_contract_factors (k := 32) (b := 10) (H := 210703) (ss := [(2, 1, 466), (28, 7, 474), (9, 7, 480), (7, 1, 579), (15, 1, 473), (30, 1, 481), (10, 1, 809), (3, 1, 409), (6, 1, 412), (11, 1, 459), (4, 1, 410), (5, 1, 411), (12, 1, 460), (13, 1, 461), (20, 1, 572), (19, 1, 865), (16, 1, 867), (14, 1, 858), (17, 1, 859), (32, 1, 872), (21, 1, 916), (31, 1, 930)]) (ids := [6, 16, 20, 21, 22, 23, 24, 25, 27, 31]) (cs := [1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 5, 6, 7, 8, 9, 1, 10, 1, 1, 1, 11]) (bs := [0, 10]) (W := 1024) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c13168_1 : P.sumLeaves 26 13484992 64 = 1024 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 210703) rows (by decide) (by decide)).symm.trans contract13168_1

theorem h13168 : P.leaf 36 13168 = 1105 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(960, 81), (64, 1024)]) (.cons c13168_0 (.cons c13168_1 (.nil))) (by decide) (by decide))

theorem cover13169 : P.CoversSplit 26 10 13169 0xa0000000a0000000000000000000000000000000000000000000000000000000000050000000400000005000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [481, 489, 579, 873, 930, 972, 979, 1273, 1315, 1322, 1665]) (ps := [(11, [879], [930])]) (by decide +kernel)

theorem c13169_0 : P.sumLeaves 26 13485056 960 = 3856 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13169) (lo := 0) (len := 960) (W := 3856) check rows elimOK (by decide) (by decide) cover13169 (by decide)
  decide +kernel

theorem contract13169_1 : P.leaf 32 210719 = 13568 := by
  exact leaf_contract_factors (k := 32) (b := 15) (H := 210719) (ss := [(28, 7, 474), (2, 1, 475), (9, 7, 480), (7, 1, 579), (15, 1, 473), (30, 1, 481), (10, 1, 809), (11, 1, 459), (12, 1, 460), (13, 1, 818), (19, 1, 865), (20, 1, 572), (16, 1, 867), (32, 1, 872), (17, 1, 874), (21, 1, 916), (31, 1, 930)]) (ids := [1, 2, 3, 4, 6, 12, 16, 20, 22, 27, 31, 21, 23, 24, 25]) (cs := [1, 2, 3, 4, 5, 1, 6, 1, 1, 1, 1, 1, 7, 1, 1, 1, 8, 1, 1, 1, 9, 13, 10, 14, 15, 16, 1, 11, 1, 1, 1, 12]) (bs := [11, 4]) (W := 13568) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c13169_1 : P.sumLeaves 26 13486016 64 = 13568 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 210719) rows (by decide) (by decide)).symm.trans contract13169_1

theorem h13169 : P.leaf 36 13169 = 17424 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(960, 3856), (64, 13568)]) (.cons c13169_0 (.cons c13169_1 (.nil))) (by decide) (by decide))

theorem h13170 : P.leaf 36 13170 = 16320 := by
  exact leaf_contract_factors (k := 36) (b := 20) (H := 13170) (ss := [(2, 1, 467), (19, 10, 866), (35, 16, 867), (10, 1, 872), (7, 1, 461), (13, 1, 461), (11, 1, 809), (12, 1, 810), (5, 1, 411), (37, 17, 874), (16, 1, 879), (14, 1, 859), (17, 1, 859), (21, 1, 929), (31, 1, 930), (20, 1, 1258)]) (ids := [1, 2, 4, 6, 7, 13, 16, 20, 22, 23, 24, 25, 26, 27, 28, 30, 31, 32, 34, 21]) (cs := [1, 2, 3, 1, 4, 1, 5, 6, 1, 1, 1, 1, 1, 7, 1, 1, 8, 1, 1, 1, 9, 21, 10, 11, 12, 13, 14, 15, 16, 1, 17, 18, 19, 1, 20, 1]) (bs := [19, 1]) (W := 16320) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem cover13171 : P.CoversSplit 26 10 13171 0xa0000000a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [481, 489, 579, 873, 930, 972, 979, 1273, 1315, 1665]) (ps := [(12, [880], [979])]) (by decide +kernel)

theorem c13171_0 : P.sumLeaves 26 13487104 960 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13171) (lo := 0) (len := 960) (W := 0) check rows elimOK (by decide) (by decide) cover13171 (by decide)
  decide +kernel

theorem contract13171_1 : P.leaf 32 210751 = 117664 := by
  exact leaf_contract_factors (k := 32) (b := 18) (H := 210751) (ss := [(28, 1, 481), (30, 1, 481), (2, 1, 482), (19, 10, 866), (16, 1, 867), (10, 1, 872), (32, 1, 873), (17, 1, 874), (12, 1, 810), (13, 1, 825), (11, 1, 818), (21, 1, 929), (31, 1, 930), (20, 1, 1258)]) (ids := [1, 2, 3, 4, 5, 6, 7, 12, 13, 16, 20, 21, 22, 27, 31, 23, 24, 25]) (cs := [1, 2, 3, 4, 5, 6, 7, 8, 1, 1, 1, 1, 9, 10, 1, 1, 11, 1, 1, 1, 12, 13, 14, 17, 18, 19, 1, 15, 1, 1, 1, 16]) (bs := [15, 3]) (W := 117664) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c13171_1 : P.sumLeaves 26 13488064 64 = 117664 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 210751) rows (by decide) (by decide)).symm.trans contract13171_1

theorem h13171 : P.leaf 36 13171 = 117664 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(960, 0), (64, 117664)]) (.cons c13171_0 (.cons c13171_1 (.nil))) (by decide) (by decide))

theorem cover13174 : P.CoversSplit 26 10 13174 0xff005500ff004000000000000000000000000000000000000000000000000000550050005500400000005000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [489, 579, 873, 879, 880, 930, 1265, 1315, 1322, 1658]) (ps := [(16, [867], [1265])]) (by decide +kernel)

theorem c13174_0 : P.sumLeaves 26 13490176 704 = 16448 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13174) (lo := 0) (len := 704) (W := 16448) check rows elimOK (by decide) (by decide) cover13174 (by decide)
  decide +kernel

theorem contract13174_1 : P.leaf 32 210795 = 23568 := by
  exact leaf_contract_factors (k := 32) (b := 19) (H := 210795) (ss := [(2, 1, 482), (10, 1, 866), (7, 1, 461), (13, 1, 461), (11, 1, 809), (12, 1, 810), (16, 1, 867), (14, 1, 859), (17, 1, 859), (31, 1, 930), (21, 0, 1658), (9, 0, 1609), (28, 0, 1658)]) (ids := [1, 2, 3, 4, 6, 13, 16, 17, 18, 20, 23, 24, 27, 28, 30, 31, 21, 22, 25]) (cs := [1, 2, 3, 4, 5, 1, 6, 0, 1, 1, 1, 1, 1, 7, 1, 1, 8, 9, 10, 0, 11, 18, 19, 12, 13, 20, 0, 14, 15, 1, 16, 17]) (bs := [16, 3]) (W := 23568) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c13174_1 : P.sumLeaves 26 13490880 64 = 23568 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 210795) rows (by decide) (by decide)).symm.trans contract13174_1

theorem c13174_2 : P.sumLeaves 26 13490944 256 = 208400 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13174) (lo := 768) (len := 256) (W := 208400) check rows elimOK (by decide) (by decide) cover13174 (by decide)
  decide +kernel

theorem h13174 : P.leaf 36 13174 = 248416 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(704, 16448), (64, 23568), (256, 208400)]) (.cons c13174_0 (.cons c13174_1 (.cons c13174_2 (.nil)))) (by decide) (by decide))

theorem cover13175 : P.CoversSplit 26 10 13175 0xff005500ff004000000000000000000000000000000000000000000000000000550050005500400000005000000040000000000000000000000000000000000000000000000000000000000000000000330011000000000000001100000000000000000000000000000000000000000011001000000000000000100000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [489, 579, 873, 930, 972, 979, 1265, 1273, 1315, 1322, 1658, 1665]) (ps := [(16, [867], [1265])]) (by decide +kernel)

theorem c13175_0 : P.sumLeaves 26 13491200 320 = 1968 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13175) (lo := 0) (len := 320) (W := 1968) check rows elimOK (by decide) (by decide) cover13175 (by decide)
  decide +kernel

theorem contract13175_1 : P.leaf 32 210805 = 12082 := by
  exact leaf_contract_factors (k := 32) (b := 19) (H := 210805) (ss := [(4, 1, 580), (5, 1, 586), (10, 1, 866), (16, 1, 867), (17, 1, 874), (13, 1, 923), (29, 0, 930), (33, 1, 1273), (31, 1, 1665), (11, 0, 930), (7, 0, 818), (12, 0, 979), (23, 1, 817)]) (ids := [0, 1, 4, 6, 7, 12, 13, 16, 17, 18, 19, 20, 22, 23, 24, 26, 28, 30, 25]) (cs := [2, 3, 1, 1, 4, 0, 5, 6, 1, 0, 0, 1, 7, 8, 1, 1, 9, 10, 11, 12, 13, 1, 14, 15, 16, 20, 17, 0, 18, 1, 19, 1]) (bs := [18, 1]) (W := 12082) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c13175_1 : P.sumLeaves 26 13491520 64 = 12082 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 210805) rows (by decide) (by decide)).symm.trans contract13175_1

theorem c13175_2 : P.sumLeaves 26 13491584 640 = 841736 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13175) (lo := 384) (len := 640) (W := 841736) check rows elimOK (by decide) (by decide) cover13175 (by decide)
  decide +kernel

theorem h13175 : P.leaf 36 13175 = 855786 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(320, 1968), (64, 12082), (640, 841736)]) (.cons c13175_0 (.cons c13175_1 (.cons c13175_2 (.nil)))) (by decide) (by decide))

theorem cover13177 : P.CoversSplit 26 10 13177 0xa0a00000a0a000000000000000000000a0a000008080000000000000000000000000505000004040000050500000404000005050000040400000500000004000a0a00000808000000000000000000000a00000008000000000000000000000000000505000004040000050500000404000005000000040000000500000004000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 579, 873, 930, 972, 979, 1273, 1315, 1322, 1665]) (by decide +kernel)

theorem c13177_0 : P.sumLeaves 26 13493248 128 = 1648 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13177) (lo := 0) (len := 128) (W := 1648) check rows elimOK (by decide) (by decide) cover13177 (by decide)
  decide +kernel

theorem contract13177_1 : P.leaf 32 210834 = 1152 := by
  exact leaf_contract_factors (k := 32) (b := 13) (H := 210834) (ss := [(22, 1, 433), (28, 7, 474), (9, 7, 480), (2, 1, 482), (32, 0, 579), (4, 1, 580), (7, 0, 579), (10, 0, 459), (13, 0, 459), (19, 0, 473), (21, 0, 473), (23, 1, 811), (11, 1, 879), (12, 1, 880), (8, 1, 1217), (15, 1, 1259), (30, 1, 1315), (5, 1, 629), (3, 1, 537)]) (ids := [4, 12, 14, 15, 16, 18, 22, 25, 27, 29, 31, 23, 24]) (cs := [1, 1, 1, 1, 2, 0, 1, 0, 0, 1, 1, 0, 3, 1, 4, 5, 6, 0, 7, 0, 1, 1, 8, 13, 14, 9, 0, 10, 1, 11, 0, 12]) (bs := [11, 2]) (W := 1152) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c13177_1 : P.sumLeaves 26 13493376 64 = 1152 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 210834) rows (by decide) (by decide)).symm.trans contract13177_1

theorem contract13177_2 : P.leaf 32 210835 = 1424 := by
  exact leaf_contract_factors (k := 32) (b := 13) (H := 210835) (ss := [(22, 1, 433), (28, 7, 474), (9, 7, 480), (2, 1, 482), (4, 1, 580), (5, 1, 629), (3, 1, 537), (19, 10, 866), (32, 10, 872), (11, 1, 879), (12, 1, 880), (13, 7, 825), (7, 0, 923), (10, 0, 459), (21, 0, 473), (23, 1, 811), (8, 1, 1217), (15, 1, 1259), (30, 1, 1315)]) (ids := [4, 12, 14, 15, 16, 18, 22, 25, 27, 29, 31, 23, 24]) (cs := [1, 1, 1, 1, 2, 0, 1, 0, 0, 1, 1, 0, 3, 1, 4, 5, 6, 0, 7, 0, 1, 1, 8, 13, 14, 9, 0, 10, 1, 11, 0, 12]) (bs := [11, 2]) (W := 1424) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c13177_2 : P.sumLeaves 26 13493440 64 = 1424 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 210835) rows (by decide) (by decide)).symm.trans contract13177_2

theorem c13177_3 : P.sumLeaves 26 13493504 192 = 10880 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13177) (lo := 256) (len := 192) (W := 10880) check rows elimOK (by decide) (by decide) cover13177 (by decide)
  decide +kernel

theorem contract13177_4 : P.leaf 32 210839 = 30432 := by
  exact leaf_contract_factors (k := 32) (b := 17) (H := 210839) (ss := [(28, 7, 474), (9, 7, 480), (7, 1, 481), (30, 1, 481), (2, 1, 482), (15, 1, 473), (4, 1, 580), (11, 1, 459), (10, 1, 809), (12, 1, 460), (13, 1, 818), (19, 1, 865), (20, 1, 572), (32, 1, 872), (21, 1, 916)]) (ids := [1, 3, 4, 6, 12, 14, 15, 16, 20, 22, 25, 27, 29, 31, 21, 23, 24]) (cs := [1, 2, 1, 3, 4, 1, 5, 1, 1, 1, 1, 1, 6, 1, 7, 8, 9, 1, 1, 1, 10, 16, 11, 17, 18, 12, 1, 13, 1, 14, 1, 15]) (bs := [14, 3]) (W := 30432) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c13177_4 : P.sumLeaves 26 13493696 64 = 30432 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 210839) rows (by decide) (by decide)).symm.trans contract13177_4

theorem c13177_5 : P.sumLeaves 26 13493760 64 = 720 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13177) (lo := 512) (len := 64) (W := 720) check rows elimOK (by decide) (by decide) cover13177 (by decide)
  decide +kernel

theorem contract13177_6 : P.leaf 32 210841 = 1856 := by
  exact leaf_contract_factors (k := 32) (b := 13) (H := 210841) (ss := [(28, 7, 474), (2, 1, 475), (9, 7, 480), (5, 1, 586), (19, 10, 866), (32, 10, 872), (11, 1, 879), (12, 1, 880), (13, 0, 923), (7, 0, 818), (10, 0, 459), (21, 0, 473), (22, 1, 426), (23, 1, 811), (8, 1, 1210), (15, 1, 1259), (4, 1, 573), (3, 1, 536), (30, 1, 1315)]) (ids := [4, 12, 14, 15, 16, 18, 22, 25, 27, 31, 23, 24, 29]) (cs := [1, 1, 1, 1, 2, 0, 1, 0, 0, 1, 1, 0, 3, 1, 4, 5, 6, 0, 7, 0, 1, 1, 8, 12, 13, 9, 0, 10, 1, 14, 0, 11]) (bs := [10, 3]) (W := 1856) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c13177_6 : P.sumLeaves 26 13493824 64 = 1856 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 210841) rows (by decide) (by decide)).symm.trans contract13177_6

theorem contract13177_7 : P.leaf 32 210842 = 10192 := by
  exact leaf_contract_factors (k := 32) (b := 19) (H := 210842) (ss := [(28, 7, 474), (9, 7, 480), (32, 0, 579), (19, 10, 866), (10, 0, 872), (7, 0, 809), (13, 0, 459), (21, 0, 473), (23, 1, 811), (11, 1, 879), (12, 1, 880), (15, 1, 1259), (30, 1, 1315)]) (ids := [0, 1, 2, 3, 4, 6, 12, 14, 15, 16, 18, 20, 22, 25, 27, 29, 31, 23, 24]) (cs := [2, 3, 4, 5, 6, 0, 7, 0, 0, 1, 1, 0, 8, 1, 9, 10, 11, 0, 12, 0, 13, 1, 14, 19, 20, 15, 0, 16, 1, 17, 0, 18]) (bs := [17, 2]) (W := 10192) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c13177_7 : P.sumLeaves 26 13493888 64 = 10192 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 210842) rows (by decide) (by decide)).symm.trans contract13177_7

theorem contract13177_8 : P.leaf 32 210843 = 18024 := by
  exact leaf_contract_factors (k := 32) (b := 19) (H := 210843) (ss := [(28, 7, 474), (9, 7, 480), (19, 10, 866), (32, 10, 872), (11, 1, 879), (12, 1, 880), (13, 0, 923), (7, 0, 818), (10, 0, 459), (21, 0, 473), (23, 1, 811), (15, 1, 1259), (30, 1, 1315)]) (ids := [0, 1, 2, 3, 4, 6, 12, 14, 15, 16, 18, 20, 22, 25, 27, 29, 31, 23, 24]) (cs := [2, 3, 4, 5, 6, 0, 7, 0, 0, 1, 1, 0, 8, 1, 9, 10, 11, 0, 12, 0, 13, 1, 14, 19, 20, 15, 0, 16, 1, 17, 0, 18]) (bs := [17, 2]) (W := 18024) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c13177_8 : P.sumLeaves 26 13493952 64 = 18024 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 210843) rows (by decide) (by decide)).symm.trans contract13177_8

theorem c13177_9 : P.sumLeaves 26 13494016 64 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13177) (lo := 768) (len := 64) (W := 0) check rows elimOK (by decide) (by decide) cover13177 (by decide)
  decide +kernel

theorem contract13177_10 : P.leaf 32 210845 = 30432 := by
  exact leaf_contract_factors (k := 32) (b := 17) (H := 210845) (ss := [(28, 7, 474), (2, 1, 475), (9, 7, 480), (7, 1, 481), (15, 1, 473), (30, 1, 481), (5, 1, 586), (12, 1, 460), (20, 1, 572), (10, 1, 809), (11, 1, 459), (13, 1, 818), (19, 1, 865), (32, 1, 872), (21, 1, 916)]) (ids := [1, 2, 4, 6, 12, 14, 15, 16, 20, 22, 25, 27, 29, 31, 21, 23, 24]) (cs := [1, 2, 3, 1, 4, 1, 5, 1, 1, 1, 1, 1, 6, 1, 7, 8, 9, 1, 1, 1, 10, 16, 11, 17, 18, 12, 1, 13, 1, 14, 1, 15]) (bs := [14, 3]) (W := 30432) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c13177_10 : P.sumLeaves 26 13494080 64 = 30432 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 210845) rows (by decide) (by decide)).symm.trans contract13177_10

theorem c13177_11 : P.sumLeaves 26 13494144 64 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13177) (lo := 896) (len := 64) (W := 0) check rows elimOK (by decide) (by decide) cover13177 (by decide)
  decide +kernel

theorem contract13177_12 : P.leaf 32 210847 = 88320 := by
  exact leaf_contract_factors (k := 32) (b := 19) (H := 210847) (ss := [(28, 7, 474), (9, 7, 480), (7, 1, 481), (30, 1, 481), (10, 1, 809), (11, 1, 459), (12, 1, 460), (13, 1, 818), (15, 1, 865), (19, 1, 865), (20, 1, 572), (32, 1, 872), (21, 1, 916)]) (ids := [0, 1, 2, 3, 4, 6, 12, 14, 15, 16, 20, 22, 25, 27, 29, 31, 21, 23, 24]) (cs := [2, 3, 4, 5, 6, 1, 7, 1, 1, 1, 1, 1, 8, 1, 9, 10, 11, 1, 1, 1, 12, 18, 13, 19, 20, 14, 1, 15, 1, 16, 1, 17]) (bs := [16, 3]) (W := 88320) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c13177_12 : P.sumLeaves 26 13494208 64 = 88320 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 210847) rows (by decide) (by decide)).symm.trans contract13177_12

theorem h13177 : P.leaf 36 13177 = 195080 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(128, 1648), (64, 1152), (64, 1424), (192, 10880), (64, 30432), (64, 720), (64, 1856), (64, 10192), (64, 18024), (64, 0), (64, 30432), (64, 0), (64, 88320)]) (.cons c13177_0 (.cons c13177_1 (.cons c13177_2 (.cons c13177_3 (.cons c13177_4 (.cons c13177_5 (.cons c13177_6 (.cons c13177_7 (.cons c13177_8 (.cons c13177_9 (.cons c13177_10 (.cons c13177_11 (.cons c13177_12 (.nil)))))))))))))) (by decide) (by decide))

theorem cover13179 : P.CoversSplit 26 10 13179 0xa0a00000a0a000000000000000000000a0a000008080000000000000000000000000000000000000000000000000000000000000000000000000000000000000a0a00000808000000000000000000000a00000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 579, 873, 930, 972, 979, 1273, 1315, 1322]) (by decide +kernel)

theorem c13179_0 : P.sumLeaves 26 13495296 1024 = 2002260 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13179) (lo := 0) (len := 1024) (W := 2002260) check rows elimOK (by decide) (by decide) cover13179 (by decide)
  decide +kernel

theorem h13179 : P.leaf 36 13179 = 2002260 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 2002260)]) (.cons c13179_0 (.nil)) (by decide) (by decide))

theorem cover13183 : P.CoversSplit 26 10 13183 0xffff5550ffff40400000000000000000fffc5550cccc404044005500440040005555505055554040555550505555404055545050444440404400500044004000ffff5550cccc40400000000000000000ff005500cc00400044005500440040005555505044444040555550504444404055005000440040004400500044004000 :=
  coversProjected check rows (by decide) (by decide) (xs := [579, 873, 930, 972, 979, 1265, 1273, 1315, 1322, 1658, 1665]) (ps := [(16, [1273], [1265])]) (by decide +kernel)

theorem contract13183_0 : P.leaf 32 210928 = 11984 := by
  exact leaf_contract_factors (k := 32) (b := 20) (H := 210928) (ss := [(22, 1, 433), (2, 1, 482), (3, 1, 537), (4, 1, 580), (5, 1, 586), (7, 1, 825), (10, 1, 866), (13, 1, 923), (8, 1, 1217), (28, 0, 1265), (31, 1, 1665), (6, 1, 636)]) (ids := [7, 9, 10, 12, 13, 14, 15, 16, 17, 18, 19, 21, 23, 24, 27, 28, 30, 31, 22, 25]) (cs := [1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 4, 1, 5, 6, 7, 8, 9, 10, 11, 12, 1, 13, 20, 14, 15, 21, 0, 16, 17, 1, 18, 19]) (bs := [18, 2]) (W := 11984) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c13183_0 : P.sumLeaves 26 13499392 64 = 11984 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 210928) rows (by decide) (by decide)).symm.trans contract13183_0

theorem contract13183_1 : P.leaf 32 210929 = 12792 := by
  exact leaf_contract_factors (k := 32) (b := 18) (H := 210929) (ss := [(22, 1, 433), (2, 1, 482), (3, 1, 537), (4, 1, 580), (5, 1, 586), (7, 1, 825), (10, 1, 866), (13, 1, 923), (8, 1, 1217), (21, 0, 1658), (9, 0, 1609), (28, 0, 1658), (31, 1, 1665), (6, 1, 587)]) (ids := [9, 10, 12, 13, 14, 15, 16, 17, 18, 21, 23, 24, 27, 28, 30, 31, 22, 25]) (cs := [1, 1, 1, 1, 1, 1, 1, 0, 1, 2, 3, 1, 4, 5, 6, 7, 8, 9, 10, 0, 1, 11, 18, 12, 13, 19, 0, 14, 15, 1, 16, 17]) (bs := [16, 2]) (W := 12792) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c13183_1 : P.sumLeaves 26 13499456 64 = 12792 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 210929) rows (by decide) (by decide)).symm.trans contract13183_1

theorem c13183_2 : P.sumLeaves 26 13499520 414 = 4968294 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13183) (lo := 128) (len := 414) (W := 4968294) check rows elimOK (by decide) (by decide) cover13183 (by decide)
  decide +kernel

theorem c13183_3 : P.sumLeaves 26 13499934 345 = 3868920 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13183) (lo := 542) (len := 345) (W := 3868920) check rows elimOK (by decide) (by decide) cover13183 (by decide)
  decide +kernel

theorem c13183_4 : P.sumLeaves 26 13500279 137 = 9028048 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13183) (lo := 887) (len := 137) (W := 9028048) check rows elimOK (by decide) (by decide) cover13183 (by decide)
  decide +kernel

theorem h13183 : P.leaf 36 13183 = 17890038 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(64, 11984), (64, 12792), (414, 4968294), (345, 3868920), (137, 9028048)]) (.cons c13183_0 (.cons c13183_1 (.cons c13183_2 (.cons c13183_3 (.cons c13183_4 (.nil)))))) (by decide) (by decide))

theorem cover13296 : P.CoversSplit 26 10 13296 0xf0000000f0000000f0000000f0000000000000000000000000000000000000000000aa00000088000000aa00000088000000000000000000000000000000000000000000000000000000000000000000c0c00000c0c0000080800000808000000000000000000000000000000000000000008888000088880000888800008888 :=
  coversProjected check rows (by decide) (by decide) (xs := [481, 489, 873, 930, 972, 979, 1265, 1273, 1322, 1658]) (ps := [(16, [1273], [867]), (19, [1265], [908])]) (by decide +kernel)

theorem contract13296_0 : P.leaf 32 212736 = 120 := by
  apply (leaf_contract (k := 32) (b := 13) (H := 212736) (ss := [(22, 1, 433), (2, 1, 466), (19, 10, 866), (16, 0, 867), (17, 0, 858), (32, 10, 872), (11, 0, 879), (10, 0, 459), (12, 0, 458), (13, 0, 458), (6, 3, 531), (5, 4, 565), (7, 0, 809), (8, 1, 465), (9, 1, 473), (28, 1, 481), (29, 1, 489), (21, 0, 865), (26, 20, 922)]) (ids := [1, 2, 12, 13, 16, 18, 21, 22, 23, 25, 28, 29, 31]) (cs := [1, 2, 3, 3, 2, 0, 1, 1, 0, 0, 0, 0, 4, 5, 0, 0, 6, 0, 7, 0, 1, 8, 9, 10, 7, 11, 1, 1, 12, 13, 0, 14]) check rows (by decide) (by decide +kernel) (by decide +kernel)).trans
  decide +kernel

theorem c13296_0 : P.sumLeaves 26 13615104 64 = 120 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 212736) rows (by decide) (by decide)).symm.trans contract13296_0

theorem contract13296_1 : P.leaf 32 212737 = 195 := by
  apply (leaf_contract (k := 32) (b := 12) (H := 212737) (ss := [(22, 1, 433), (2, 1, 466), (4, 1, 580), (5, 1, 411), (3, 1, 537), (6, 1, 412), (19, 10, 866), (16, 0, 867), (17, 0, 858), (32, 10, 872), (11, 0, 879), (7, 0, 459), (12, 0, 458), (13, 0, 458), (10, 0, 459), (8, 1, 465), (9, 1, 473), (28, 1, 481), (29, 1, 489), (21, 0, 865)]) (ids := [12, 13, 16, 18, 21, 22, 23, 24, 25, 28, 29, 31]) (cs := [1, 1, 1, 1, 1, 0, 1, 1, 0, 0, 0, 0, 2, 3, 0, 0, 4, 0, 5, 0, 1, 6, 7, 8, 9, 10, 1, 1, 11, 12, 0, 13]) check rows (by decide) (by decide +kernel) (by decide +kernel)).trans
  decide +kernel

theorem c13296_1 : P.sumLeaves 26 13615168 64 = 195 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 212737) rows (by decide) (by decide)).symm.trans contract13296_1

theorem c13296_2 : P.sumLeaves 26 13615232 128 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13296) (lo := 128) (len := 128) (W := 0) check rows elimOK (by decide) (by decide) cover13296 (by decide)
  decide +kernel

theorem contract13296_3 : P.leaf 32 212740 = 0 := by
  exact leaf_contract_zero (ss := [(2, 1, 466), (19, 10, 866), (16, 0, 867), (17, 0, 858), (32, 10, 872), (10, 1, 873), (3, 1, 409), (6, 1, 412), (7, 1, 459), (11, 1, 459), (4, 1, 410), (5, 1, 411), (12, 1, 460), (13, 1, 461), (14, 0, 858), (8, 1, 465), (29, 1, 468), (30, 1, 873)]) (q := 879) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c13296_3 : P.sumLeaves 26 13615360 64 = 0 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 212740) rows (by decide) (by decide)).symm.trans contract13296_3

theorem contract13296_4 : P.leaf 32 212741 = 0 := by
  exact leaf_contract_zero (ss := [(2, 1, 466), (19, 10, 866), (16, 0, 867), (17, 0, 858), (32, 10, 872), (10, 1, 873), (3, 1, 409), (6, 1, 412), (7, 1, 459), (11, 1, 459), (4, 1, 410), (5, 1, 411), (12, 1, 460), (13, 1, 461), (14, 0, 858), (8, 1, 465), (29, 1, 468), (30, 1, 873)]) (q := 879) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c13296_4 : P.sumLeaves 26 13615424 64 = 0 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 212741) rows (by decide) (by decide)).symm.trans contract13296_4

theorem c13296_5 : P.sumLeaves 26 13615488 256 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13296) (lo := 384) (len := 256) (W := 0) check rows elimOK (by decide) (by decide) cover13296 (by decide)
  decide +kernel

theorem contract13296_6 : P.leaf 32 212746 = 0 := by
  exact leaf_contract_zero (ss := [(2, 1, 466), (19, 10, 866), (16, 1, 867), (14, 1, 859), (17, 1, 859), (32, 10, 872), (11, 1, 879), (4, 1, 410), (5, 1, 411), (7, 1, 458), (10, 1, 458), (3, 1, 409), (6, 1, 412), (12, 1, 460), (13, 1, 461), (15, 1, 865), (30, 1, 873), (21, 1, 916)]) (q := 923) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c13296_6 : P.sumLeaves 26 13615744 64 = 0 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 212746) rows (by decide) (by decide)).symm.trans contract13296_6

theorem contract13296_7 : P.leaf 32 212747 = 0 := by
  exact leaf_contract_zero (ss := [(2, 1, 466), (19, 10, 866), (16, 1, 867), (14, 1, 859), (17, 1, 859), (32, 10, 872), (11, 1, 879), (4, 1, 410), (5, 1, 411), (7, 1, 458), (10, 1, 458), (3, 1, 409), (6, 1, 412), (12, 1, 460), (13, 1, 461), (15, 1, 865), (30, 1, 873), (21, 1, 916)]) (q := 923) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c13296_7 : P.sumLeaves 26 13615808 64 = 0 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 212747) rows (by decide) (by decide)).symm.trans contract13296_7

theorem c13296_8 : P.sumLeaves 26 13615872 128 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13296) (lo := 768) (len := 128) (W := 0) check rows elimOK (by decide) (by decide) cover13296 (by decide)
  decide +kernel

theorem contract13296_9 : P.leaf 32 212750 = 8192 := by
  exact leaf_contract_factors (k := 32) (b := 13) (H := 212750) (ss := [(2, 1, 466), (19, 10, 866), (16, 1, 867), (14, 1, 859), (17, 1, 859), (32, 10, 872), (10, 1, 873), (3, 1, 409), (6, 1, 412), (7, 1, 459), (11, 1, 459), (4, 1, 410), (5, 1, 411), (12, 1, 460), (13, 1, 461), (15, 1, 865), (30, 1, 873), (21, 1, 916), (31, 1, 930)]) (ids := [6, 7, 16, 18, 20, 21, 22, 23, 24, 25, 26, 27, 31]) (cs := [1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 5, 1, 6, 7, 8, 9, 10, 11, 12, 13, 1, 1, 1, 14]) (bs := [0, 13]) (W := 8192) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c13296_9 : P.sumLeaves 26 13616000 64 = 8192 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 212750) rows (by decide) (by decide)).symm.trans contract13296_9

theorem contract13296_10 : P.leaf 32 212751 = 8192 := by
  exact leaf_contract_factors (k := 32) (b := 13) (H := 212751) (ss := [(2, 1, 466), (19, 10, 866), (16, 1, 867), (14, 1, 859), (17, 1, 859), (32, 10, 872), (10, 1, 873), (3, 1, 409), (6, 1, 412), (7, 1, 459), (11, 1, 459), (4, 1, 410), (5, 1, 411), (12, 1, 460), (13, 1, 461), (15, 1, 865), (30, 1, 873), (21, 1, 916), (31, 1, 930)]) (ids := [6, 7, 16, 18, 20, 21, 22, 23, 24, 25, 26, 27, 31]) (cs := [1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 5, 1, 6, 7, 8, 9, 10, 11, 12, 13, 1, 1, 1, 14]) (bs := [0, 13]) (W := 8192) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c13296_10 : P.sumLeaves 26 13616064 64 = 8192 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 212751) rows (by decide) (by decide)).symm.trans contract13296_10

theorem h13296 : P.leaf 36 13296 = 16699 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(64, 120), (64, 195), (128, 0), (64, 0), (64, 0), (256, 0), (64, 0), (64, 0), (128, 0), (64, 8192), (64, 8192)]) (.cons c13296_0 (.cons c13296_1 (.cons c13296_2 (.cons c13296_3 (.cons c13296_4 (.cons c13296_5 (.cons c13296_6 (.cons c13296_7 (.cons c13296_8 (.cons c13296_9 (.cons c13296_10 (.nil)))))))))))) (by decide) (by decide))

theorem h13297 : P.leaf 36 13297 = 182272 := by
  exact leaf_contract_factors (k := 36) (b := 22) (H := 13297) (ss := [(2, 1, 475), (19, 1, 866), (16, 1, 867), (32, 1, 872), (17, 1, 874), (11, 1, 879), (7, 1, 460), (12, 1, 460), (10, 1, 809), (13, 1, 818), (15, 1, 916), (21, 1, 916), (36, 1, 923), (30, 1, 873)]) (ids := [1, 2, 3, 4, 6, 7, 12, 16, 18, 20, 22, 25, 26, 27, 29, 31, 32, 33, 35, 21, 23, 24]) (cs := [1, 2, 3, 4, 5, 1, 6, 7, 1, 1, 1, 1, 8, 1, 1, 1, 9, 1, 10, 1, 11, 21, 12, 22, 23, 13, 14, 15, 1, 16, 1, 17, 18, 19, 1, 20]) (bs := [19, 3]) (W := 182272) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem cover13299 : P.CoversSplit 26 10 13299 0xf0000000f0000000f0000000f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [481, 489, 873, 930, 972, 979, 1265, 1273, 1315, 1322, 1658, 1665]) (ps := [(12, [880], [979]), (13, [923], [972])]) (by decide +kernel)

theorem c13299_0 : P.sumLeaves 26 13618176 896 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13299) (lo := 0) (len := 896) (W := 0) check rows elimOK (by decide) (by decide) cover13299 (by decide)
  decide +kernel

theorem contract13299_1 : P.leaf 32 212798 = 253424 := by
  exact leaf_contract_factors (k := 32) (b := 20) (H := 212798) (ss := [(2, 1, 482), (19, 1, 866), (16, 1, 867), (30, 1, 873), (32, 1, 873), (17, 1, 874), (12, 1, 880), (10, 1, 810), (13, 1, 825), (11, 1, 818), (21, 1, 929), (31, 1, 930)]) (ids := [1, 2, 3, 4, 5, 6, 7, 12, 13, 16, 18, 20, 21, 22, 23, 26, 27, 31, 24, 25]) (cs := [1, 2, 3, 4, 5, 6, 7, 8, 1, 1, 1, 1, 9, 10, 1, 1, 11, 1, 12, 1, 13, 14, 15, 16, 20, 21, 17, 18, 1, 1, 1, 19]) (bs := [18, 2]) (W := 253424) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c13299_1 : P.sumLeaves 26 13619072 64 = 253424 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 212798) rows (by decide) (by decide)).symm.trans contract13299_1

theorem contract13299_2 : P.leaf 32 212799 = 351392 := by
  exact leaf_contract_factors (k := 32) (b := 20) (H := 212799) (ss := [(2, 1, 482), (19, 1, 866), (16, 1, 867), (30, 1, 873), (32, 1, 873), (17, 1, 874), (12, 1, 880), (10, 1, 810), (13, 1, 825), (11, 1, 818), (21, 1, 929), (31, 1, 930)]) (ids := [1, 2, 3, 4, 5, 7, 12, 13, 16, 18, 20, 21, 22, 23, 26, 27, 31, 6, 24, 25]) (cs := [1, 2, 3, 4, 5, 6, 19, 7, 1, 1, 1, 1, 8, 9, 1, 1, 10, 1, 11, 1, 12, 13, 14, 15, 20, 21, 16, 17, 1, 1, 1, 18]) (bs := [17, 3]) (W := 351392) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c13299_2 : P.sumLeaves 26 13619136 64 = 351392 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 212799) rows (by decide) (by decide)).symm.trans contract13299_2

theorem h13299 : P.leaf 36 13299 = 604816 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(896, 0), (64, 253424), (64, 351392)]) (.cons c13299_0 (.cons c13299_1 (.cons c13299_2 (.nil)))) (by decide) (by decide))

theorem cover13302 : P.CoversSplit 26 10 13302 0xff00ff00ff00c800ff00aa00ff00880000000000000000000000000000000000ff00f000ff00c000aa00a000aa0080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 873, 879, 880, 930, 1265, 1315, 1322, 1658]) (by decide +kernel)

theorem c13302_0 : P.sumLeaves 26 13621248 640 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13302) (lo := 0) (len := 640) (W := 0) check rows elimOK (by decide) (by decide) cover13302 (by decide)
  decide +kernel

theorem contract13302_1 : P.leaf 32 212842 = 190256 := by
  exact leaf_contract_factors (k := 32) (b := 21) (H := 212842) (ss := [(2, 1, 482), (10, 1, 866), (7, 1, 461), (13, 1, 461), (11, 1, 809), (12, 1, 810), (16, 1, 867), (14, 1, 859), (17, 1, 859), (31, 1, 930), (28, 1, 1658)]) (ids := [1, 2, 3, 4, 6, 7, 13, 16, 17, 18, 19, 20, 23, 24, 27, 28, 30, 31, 21, 22, 25]) (cs := [1, 2, 3, 4, 5, 1, 6, 7, 1, 1, 1, 1, 1, 8, 1, 1, 9, 10, 11, 12, 13, 20, 21, 14, 15, 22, 1, 16, 17, 1, 18, 19]) (bs := [18, 3]) (W := 190256) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c13302_1 : P.sumLeaves 26 13621888 64 = 190256 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 212842) rows (by decide) (by decide)).symm.trans contract13302_1

theorem c13302_2 : P.sumLeaves 26 13621952 320 = 1878864 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13302) (lo := 704) (len := 320) (W := 1878864) check rows elimOK (by decide) (by decide) cover13302 (by decide)
  decide +kernel

theorem h13302 : P.leaf 36 13302 = 2069120 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(640, 0), (64, 190256), (320, 1878864)]) (.cons c13302_0 (.cons c13302_1 (.cons c13302_2 (.nil)))) (by decide) (by decide))

theorem cover13303 : P.CoversSplit 26 10 13303 0xff00ff00ff00c800ff00aa00ff00880000000000000000000000000000000000ff00f000ff00c000aa00a000aa0080000000000000000000000000000000000000000000000000000000000000000000330033000000000022002200000000000000000000000000000000000000000033003000000000002200200000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 873, 930, 972, 979, 1265, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c13303_0 : P.sumLeaves 26 13622272 64 = 2352 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13303) (lo := 0) (len := 64) (W := 2352) check rows elimOK (by decide) (by decide) cover13303 (by decide)
  decide +kernel

theorem contract13303_1 : P.leaf 32 212849 = 2952 := by
  exact leaf_contract_factors (k := 32) (b := 13) (H := 212849) (ss := [(22, 1, 433), (2, 1, 482), (3, 1, 537), (4, 1, 580), (5, 1, 629), (16, 1, 867), (17, 1, 874), (13, 1, 923), (12, 7, 825), (29, 0, 930), (8, 1, 1217), (33, 1, 1273), (6, 1, 636), (9, 1, 1609), (31, 1, 1665), (11, 0, 930), (7, 0, 818), (10, 1, 461), (23, 1, 817)]) (ids := [12, 13, 16, 17, 19, 22, 24, 26, 28, 30, 18, 23, 25]) (cs := [1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 0, 1, 2, 3, 1, 1, 4, 5, 12, 6, 1, 1, 7, 13, 8, 14, 9, 0, 10, 1, 11, 1]) (bs := [10, 3]) (W := 2952) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c13303_1 : P.sumLeaves 26 13622336 64 = 2952 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 212849) rows (by decide) (by decide)).symm.trans contract13303_1

theorem c13303_2 : P.sumLeaves 26 13622400 896 = 12810515 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13303) (lo := 128) (len := 896) (W := 12810515) check rows elimOK (by decide) (by decide) cover13303 (by decide)
  decide +kernel

theorem h13303 : P.leaf 36 13303 = 12815819 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(64, 2352), (64, 2952), (896, 12810515)]) (.cons c13303_0 (.cons c13303_1 (.cons c13303_2 (.nil)))) (by decide) (by decide))

theorem cover13311 : P.CoversSplit 26 10 13311 0xfffffffaffffc8c8ffffaaaaffff8888fffcfff8ccccc8c8aa88aa8888888888fffffafaffffc8c8aaaaaaaaaaaa8888fffcfaf8ccccc8c8aa88aa8888888888fffffffaccccc8c8ffffaaaacccc8888ffccffc8ccccc8c8aa88aa8888888888fffffafaccccc8c8aaaaaaaa88888888ffccfac8ccccc8c8aa88aa8888888888 :=
  coversSplit check rows (by decide) (by decide) (xs := [873, 930, 972, 979, 1265, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f13311 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 26 (13630464 + i)

theorem c13311_0 : rowSum f13311 0 346 = 85379052 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 13311) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover13311 (by decide)
  decide +kernel

theorem c13311_1 : rowSum f13311 346 155 = 360558528 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 13311) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover13311 (by decide)
  decide +kernel

theorem c13311_2 : rowSum f13311 501 523 = 471761382 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 13311) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover13311 (by decide)
  decide +kernel

theorem sum13311 : rowSum f13311 0 1024 = 917698962 :=
  rowSum_append (F := f13311) (lo := 0) (n := 346) (m := 678) (A := 85379052) (B := 832319910) c13311_0 (rowSum_append (F := f13311) (lo := 346) (n := 155) (m := 523) (A := 360558528) (B := 471761382) c13311_1 (c13311_2))

theorem h13311 : P.leaf 36 13311 = 917698962 :=
  leaf_weighted (k := 26) (d := 10) (H := 13311) (keep := keep2) (twice := twice2) rows (by decide) (by decide) bal2 (invRow2 (H := 13311) (by decide) (by decide +kernel)) sum13311

theorem cover13526 : P.CoversSplit 26 10 13526 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c13526_0 : P.sumLeaves 26 13850624 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13526) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13526 (by decide)
  decide +kernel

theorem h13526 : P.leaf 36 13526 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13526_0 (.nil)) (by decide) (by decide))

theorem cover13527 : P.CoversSplit 26 10 13527 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c13527_0 : P.sumLeaves 26 13851648 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13527) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13527 (by decide)
  decide +kernel

theorem h13527 : P.leaf 36 13527 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13527_0 (.nil)) (by decide) (by decide))

theorem cover13532 : P.CoversSplit 26 10 13532 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c13532_0 : P.sumLeaves 26 13856768 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13532) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13532 (by decide)
  decide +kernel

theorem h13532 : P.leaf 36 13532 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13532_0 (.nil)) (by decide) (by decide))

theorem cover13533 : P.CoversSplit 26 10 13533 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c13533_0 : P.sumLeaves 26 13857792 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13533) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13533 (by decide)
  decide +kernel

theorem h13533 : P.leaf 36 13533 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13533_0 (.nil)) (by decide) (by decide))

theorem cover13535 : P.CoversSplit 26 10 13535 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c13535_0 : P.sumLeaves 26 13859840 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13535) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13535 (by decide)
  decide +kernel

theorem h13535 : P.leaf 36 13535 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13535_0 (.nil)) (by decide) (by decide))

theorem cover13542 : P.CoversSplit 26 10 13542 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c13542_0 : P.sumLeaves 26 13867008 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13542) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13542 (by decide)
  decide +kernel

theorem h13542 : P.leaf 36 13542 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13542_0 (.nil)) (by decide) (by decide))

theorem cover13543 : P.CoversSplit 26 10 13543 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c13543_0 : P.sumLeaves 26 13868032 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13543) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13543 (by decide)
  decide +kernel

theorem h13543 : P.leaf 36 13543 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13543_0 (.nil)) (by decide) (by decide))

theorem cover13544 : P.CoversSplit 26 10 13544 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c13544_0 : P.sumLeaves 26 13869056 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13544) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13544 (by decide)
  decide +kernel

theorem h13544 : P.leaf 36 13544 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13544_0 (.nil)) (by decide) (by decide))

theorem cover13545 : P.CoversSplit 26 10 13545 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c13545_0 : P.sumLeaves 26 13870080 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13545) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13545 (by decide)
  decide +kernel

theorem h13545 : P.leaf 36 13545 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13545_0 (.nil)) (by decide) (by decide))

theorem cover13546 : P.CoversSplit 26 10 13546 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c13546_0 : P.sumLeaves 26 13871104 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13546) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13546 (by decide)
  decide +kernel

theorem h13546 : P.leaf 36 13546 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13546_0 (.nil)) (by decide) (by decide))

theorem cover13547 : P.CoversSplit 26 10 13547 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c13547_0 : P.sumLeaves 26 13872128 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13547) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13547 (by decide)
  decide +kernel

theorem h13547 : P.leaf 36 13547 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13547_0 (.nil)) (by decide) (by decide))

theorem cover13550 : P.CoversSplit 26 10 13550 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c13550_0 : P.sumLeaves 26 13875200 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13550) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13550 (by decide)
  decide +kernel

theorem h13550 : P.leaf 36 13550 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13550_0 (.nil)) (by decide) (by decide))

theorem cover13551 : P.CoversSplit 26 10 13551 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c13551_0 : P.sumLeaves 26 13876224 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13551) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13551 (by decide)
  decide +kernel

theorem h13551 : P.leaf 36 13551 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13551_0 (.nil)) (by decide) (by decide))

theorem cover13558 : P.CoversSplit 26 10 13558 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c13558_0 : P.sumLeaves 26 13883392 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13558) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13558 (by decide)
  decide +kernel

theorem h13558 : P.leaf 36 13558 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13558_0 (.nil)) (by decide) (by decide))

theorem cover13559 : P.CoversSplit 26 10 13559 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c13559_0 : P.sumLeaves 26 13884416 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13559) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13559 (by decide)
  decide +kernel

theorem h13559 : P.leaf 36 13559 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13559_0 (.nil)) (by decide) (by decide))

theorem cover13560 : P.CoversSplit 26 10 13560 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c13560_0 : P.sumLeaves 26 13885440 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 13560) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover13560 (by decide)
  decide +kernel

theorem h13560 : P.leaf 36 13560 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c13560_0 (.nil)) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(13119, 90), (13168, 180), (13169, 360), (13170, 360), (13171, 720), (13174, 180), (13175, 360), (13177, 180), (13179, 360), (13183, 180), (13296, 90), (13297, 360), (13299, 360), (13302, 180), (13303, 360), (13311, 90), (13526, 360), (13527, 360), (13532, 180), (13533, 360), (13535, 180), (13542, 360), (13543, 360), (13544, 360), (13545, 360), (13546, 720), (13547, 720), (13550, 360), (13551, 360), (13558, 720), (13559, 720), (13560, 720)]

theorem segOK : checkSeg 20 perms 13119 13561 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 13119 13561 11610 92387783790 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 92387783790)
    (SegSum.cons (w := 90) h13119 (SegSum.cons (w := 180) h13168 (SegSum.cons (w := 360) h13169 (SegSum.cons (w := 360) h13170 (SegSum.cons (w := 720) h13171 (SegSum.cons (w := 180) h13174 (SegSum.cons (w := 360) h13175 (SegSum.cons (w := 180) h13177 (SegSum.cons (w := 360) h13179 (SegSum.cons (w := 180) h13183 (SegSum.cons (w := 90) h13296 (SegSum.cons (w := 360) h13297 (SegSum.cons (w := 360) h13299 (SegSum.cons (w := 180) h13302 (SegSum.cons (w := 360) h13303 (SegSum.cons (w := 90) h13311 (SegSum.cons (w := 360) h13526 (SegSum.cons (w := 360) h13527 (SegSum.cons (w := 180) h13532 (SegSum.cons (w := 360) h13533 (SegSum.cons (w := 180) h13535 (SegSum.cons (w := 360) h13542 (SegSum.cons (w := 360) h13543 (SegSum.cons (w := 360) h13544 (SegSum.cons (w := 360) h13545 (SegSum.cons (w := 720) h13546 (SegSum.cons (w := 720) h13547 (SegSum.cons (w := 360) h13550 (SegSum.cons (w := 360) h13551 (SegSum.cons (w := 720) h13558 (SegSum.cons (w := 720) h13559 (SegSum.cons (w := 720) h13560 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S22
