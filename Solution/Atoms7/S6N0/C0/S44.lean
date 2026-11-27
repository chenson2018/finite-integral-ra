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

namespace RACert.S6N0.C0.S44

open RACert RACert.Problem

theorem cover78719 : P.CoversSplit 26 10 78719 0xfffffffafffffafa0000000000000000fffcfff8fffcc8c855545550550040005555505055555050555550505555505055545050555440405554505055004000fffffffafffffafa0000000000000000ffccffc8cc00c80055445540440040005555505055555050555550505555505055445040440040005544504044004000 :=
  coversSplit check rows (by decide) (by decide) (xs := [579, 873, 930, 972, 979, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f78719 (i : ℕ) := rowWeight keep3 twice3 i * P.leaf 26 (80608256 + i)

theorem c78719_0 : rowSum f78719 0 490 = 44626216 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 78719) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover78719 (by decide)
  decide +kernel

theorem c78719_1 : rowSum f78719 490 402 = 63717172 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 78719) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover78719 (by decide)
  decide +kernel

theorem c78719_2 : rowSum f78719 892 132 = 80325160 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 78719) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover78719 (by decide)
  decide +kernel

theorem sum78719 : rowSum f78719 0 1024 = 188668548 :=
  rowSum_append (F := f78719) (lo := 0) (n := 490) (m := 534) (A := 44626216) (B := 144042332) c78719_0 (rowSum_append (F := f78719) (lo := 490) (n := 402) (m := 132) (A := 63717172) (B := 80325160) c78719_1 (c78719_2))

theorem h78719 : P.leaf 36 78719 = 188668548 :=
  leaf_weighted (k := 26) (d := 10) (H := 78719) (keep := keep3) (twice := twice3) rows (by decide) (by decide) bal3 (invRow3 (H := 78719) (by decide) (by decide +kernel)) sum78719

theorem cover78727 : P.CoversSplit 26 10 78727 0xcc00000000000000cc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 538, 930, 972, 979, 1266, 1315, 1658, 1665]) (by decide +kernel)

theorem c78727_0 : P.sumLeaves 26 80616448 896 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78727) (lo := 0) (len := 896) (W := 0) check rows elimOK (by decide) (by decide) cover78727 (by decide)
  decide +kernel

theorem contract78727_1 : P.leaf 32 1259646 = 40376 := by
  exact leaf_contract_factors (k := 32) (b := 16) (H := 1259646) (ss := [(29, 1, 489), (31, 1, 489), (3, 1, 524), (33, 1, 538), (16, 1, 867), (8, 1, 516), (17, 1, 516), (14, 1, 858), (11, 1, 879), (12, 1, 880), (13, 1, 825), (18, 1, 1210), (6, 1, 419), (21, 1, 1272), (19, 1, 1259), (32, 1, 1315)]) (ids := [0, 2, 3, 5, 7, 8, 13, 18, 20, 21, 23, 24, 26, 28, 22, 25]) (cs := [2, 1, 3, 4, 1, 5, 1, 6, 7, 1, 1, 1, 1, 8, 1, 1, 1, 1, 9, 1, 10, 11, 16, 12, 13, 17, 14, 1, 15, 1, 1, 1]) (bs := [14, 2]) (W := 40376) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c78727_1 : P.sumLeaves 26 80617344 64 = 40376 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1259646) rows (by decide) (by decide)).symm.trans contract78727_1

theorem contract78727_2 : P.leaf 32 1259647 = 43512 := by
  exact leaf_contract_factors (k := 32) (b := 16) (H := 1259647) (ss := [(29, 1, 489), (31, 1, 489), (3, 1, 524), (33, 1, 538), (16, 1, 867), (8, 1, 516), (17, 1, 516), (14, 1, 858), (11, 1, 879), (12, 1, 880), (13, 1, 825), (18, 1, 1210), (6, 1, 419), (21, 1, 1272), (19, 1, 1259), (32, 1, 1315)]) (ids := [0, 2, 3, 7, 13, 18, 20, 23, 24, 26, 28, 5, 8, 21, 22, 25]) (cs := [2, 1, 3, 4, 1, 13, 1, 5, 14, 1, 1, 1, 1, 6, 1, 1, 1, 1, 7, 1, 8, 15, 16, 9, 10, 17, 11, 1, 12, 1, 1, 1]) (bs := [11, 3, 2]) (W := 43512) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c78727_2 : P.sumLeaves 26 80617408 64 = 43512 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1259647) rows (by decide) (by decide)).symm.trans contract78727_2

theorem h78727 : P.leaf 36 78727 = 83888 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(896, 0), (64, 40376), (64, 43512)]) (.cons c78727_0 (.cons c78727_1 (.cons c78727_2 (.nil)))) (by decide) (by decide))

theorem h78729 : P.leaf 36 78729 = 16384 := by
  exact leaf_contract_factors (k := 36) (b := 14) (H := 78729) (ss := [(16, 1, 466), (17, 1, 467), (11, 1, 472), (7, 1, 460), (12, 1, 460), (8, 1, 515), (3, 1, 524), (4, 1, 417), (5, 1, 418), (33, 1, 536), (10, 1, 809), (13, 1, 818), (14, 1, 858), (36, 1, 923), (21, 1, 929), (18, 1, 1210), (19, 1, 1259), (15, 1, 916), (35, 1, 1273), (32, 1, 1315), (30, 1, 972), (37, 1, 1322)]) (ids := [0, 4, 7, 18, 20, 21, 22, 23, 24, 25, 26, 27, 29, 32]) (cs := [2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 6, 7, 8, 9, 10, 11, 12, 13, 1, 14, 1, 1, 15, 1, 1, 1]) (bs := [0, 14]) (W := 16384) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem h78731 : P.leaf 36 78731 = 89600 := by
  exact leaf_contract_factors (k := 36) (b := 17) (H := 78731) (ss := [(12, 1, 479), (3, 1, 524), (33, 1, 537), (16, 1, 867), (8, 1, 516), (17, 1, 516), (5, 1, 418), (14, 1, 858), (11, 1, 879), (10, 1, 810), (21, 1, 929), (18, 1, 1210), (19, 1, 1259), (36, 1, 1266), (13, 1, 825), (35, 1, 1273), (32, 1, 1315), (30, 1, 972), (37, 1, 1322)]) (ids := [0, 2, 4, 5, 7, 13, 18, 20, 23, 27, 21, 22, 24, 25, 26, 29, 32]) (cs := [2, 1, 3, 1, 4, 5, 1, 6, 1, 1, 1, 1, 1, 7, 1, 1, 1, 1, 8, 1, 9, 12, 13, 10, 14, 15, 16, 11, 1, 17, 1, 1, 18, 1, 1, 1]) (bs := [10, 7]) (W := 89600) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem cover78734 : P.CoversSplit 26 10 78734 0xffff000000000000ffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cccc0000cccc080888880000888808080000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [530, 538, 873, 930, 979, 1266, 1273, 1315, 1322, 1658]) (ps := [(11, [930], [879])]) (by decide +kernel)

theorem c78734_0 : P.sumLeaves 26 80623616 256 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78734) (lo := 0) (len := 256) (W := 0) check rows elimOK (by decide) (by decide) cover78734 (by decide)
  decide +kernel

theorem contract78734_1 : P.leaf 32 1259748 = 800 := by
  apply (leaf_contract (k := 32) (b := 18) (H := 1259748) (ss := [(3, 1, 472), (16, 0, 867), (14, 0, 515), (17, 0, 465), (18, 0, 465), (8, 0, 858), (7, 1, 458), (9, 1, 522), (28, 1, 530), (29, 1, 538), (11, 0, 879), (12, 0, 809), (26, 20, 1265), (21, 1, 1272)]) (ids := [0, 2, 3, 4, 8, 11, 13, 17, 18, 20, 21, 22, 23, 25, 28, 29, 30, 31]) (cs := [2, 1, 3, 4, 5, 1, 0, 1, 6, 0, 0, 7, 0, 8, 0, 0, 0, 9, 10, 1, 11, 12, 13, 14, 10, 15, 1, 1, 16, 17, 18, 19]) check rows (by decide) (by decide +kernel) (by decide +kernel)).trans
  decide +kernel

theorem c78734_1 : P.sumLeaves 26 80623872 64 = 800 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1259748) rows (by decide) (by decide)).symm.trans contract78734_1

theorem c78734_2 : P.sumLeaves 26 80623936 576 = 1534 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78734) (lo := 320) (len := 576) (W := 1534) check rows elimOK (by decide) (by decide) cover78734 (by decide)
  decide +kernel

theorem contract78734_3 : P.leaf 32 1259758 = 26112 := by
  exact leaf_contract_factors (k := 32) (b := 15) (H := 1259758) (ss := [(3, 1, 472), (16, 1, 867), (4, 1, 417), (5, 1, 418), (8, 1, 465), (14, 1, 465), (2, 1, 409), (6, 1, 419), (17, 1, 516), (18, 1, 517), (11, 1, 879), (10, 1, 810), (12, 1, 810), (21, 1, 1272), (33, 1, 1273), (19, 1, 1259), (32, 1, 1315)]) (ids := [7, 13, 18, 23, 24, 26, 27, 28, 5, 11, 20, 21, 22, 25, 29]) (cs := [1, 1, 1, 1, 1, 10, 1, 2, 1, 1, 1, 11, 1, 3, 1, 1, 1, 1, 4, 1, 12, 13, 14, 5, 6, 15, 7, 8, 9, 16, 1, 1]) (bs := [8, 7]) (W := 26112) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c78734_3 : P.sumLeaves 26 80624512 64 = 26112 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1259758) rows (by decide) (by decide)).symm.trans contract78734_3

theorem contract78734_4 : P.leaf 32 1259759 = 28160 := by
  exact leaf_contract_factors (k := 32) (b := 15) (H := 1259759) (ss := [(3, 1, 472), (16, 1, 867), (4, 1, 417), (5, 1, 418), (8, 1, 465), (14, 1, 465), (2, 1, 409), (6, 1, 419), (17, 1, 516), (18, 1, 517), (11, 1, 879), (10, 1, 810), (12, 1, 810), (21, 1, 1272), (33, 1, 1273), (19, 1, 1259), (32, 1, 1315)]) (ids := [7, 13, 18, 23, 24, 26, 27, 28, 5, 11, 20, 21, 22, 25, 29]) (cs := [1, 1, 1, 1, 1, 10, 1, 2, 1, 1, 1, 11, 1, 3, 1, 1, 1, 1, 4, 1, 12, 13, 14, 5, 6, 15, 7, 8, 9, 16, 1, 1]) (bs := [8, 7]) (W := 28160) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c78734_4 : P.sumLeaves 26 80624576 64 = 28160 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1259759) rows (by decide) (by decide)).symm.trans contract78734_4

theorem h78734 : P.leaf 36 78734 = 56606 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(256, 0), (64, 800), (576, 1534), (64, 26112), (64, 28160)]) (.cons c78734_0 (.cons c78734_1 (.cons c78734_2 (.cons c78734_3 (.cons c78734_4 (.nil)))))) (by decide) (by decide))

theorem cover78735 : P.CoversSplit 26 10 78735 0xffff000000000000ffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffcc0a0800000000aa880a080000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [530, 538, 930, 979, 1266, 1273, 1315, 1322, 1658]) (ps := [(16, [867], [1273])]) (by decide +kernel)

theorem c78735_0 : P.sumLeaves 26 80624640 896 = 217440 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78735) (lo := 0) (len := 896) (W := 217440) check rows elimOK (by decide) (by decide) cover78735 (by decide)
  decide +kernel

theorem contract78735_1 : P.leaf 32 1259774 = 358144 := by
  exact leaf_contract_factors (k := 32) (b := 20) (H := 1259774) (ss := [(3, 1, 524), (16, 1, 867), (8, 1, 516), (17, 1, 516), (14, 1, 858), (11, 1, 879), (12, 1, 880), (18, 1, 1210), (21, 1, 1272), (33, 1, 1273), (19, 1, 1259), (32, 1, 1315)]) (ids := [0, 2, 3, 4, 5, 7, 8, 11, 13, 18, 20, 21, 23, 24, 26, 27, 28, 29, 22, 25]) (cs := [2, 1, 3, 4, 5, 6, 1, 7, 8, 1, 1, 9, 1, 10, 1, 1, 1, 1, 11, 1, 12, 13, 20, 14, 15, 21, 16, 17, 18, 19, 1, 1]) (bs := [18, 2]) (W := 358144) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c78735_1 : P.sumLeaves 26 80625536 64 = 358144 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1259774) rows (by decide) (by decide)).symm.trans contract78735_1

theorem contract78735_2 : P.leaf 32 1259775 = 390720 := by
  exact leaf_contract_factors (k := 32) (b := 20) (H := 1259775) (ss := [(3, 1, 524), (16, 1, 867), (8, 1, 516), (17, 1, 516), (14, 1, 858), (11, 1, 879), (12, 1, 880), (18, 1, 1210), (21, 1, 1272), (33, 1, 1273), (19, 1, 1259), (32, 1, 1315)]) (ids := [0, 2, 3, 4, 5, 7, 8, 11, 13, 18, 20, 21, 23, 24, 26, 27, 28, 29, 22, 25]) (cs := [2, 1, 3, 4, 5, 6, 1, 7, 8, 1, 1, 9, 1, 10, 1, 1, 1, 1, 11, 1, 12, 13, 20, 14, 15, 21, 16, 17, 18, 19, 1, 1]) (bs := [18, 2]) (W := 390720) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c78735_2 : P.sumLeaves 26 80625600 64 = 390720 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1259775) rows (by decide) (by decide)).symm.trans contract78735_2

theorem h78735 : P.leaf 36 78735 = 966304 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(896, 217440), (64, 358144), (64, 390720)]) (.cons c78735_0 (.cons c78735_1 (.cons c78735_2 (.nil)))) (by decide) (by decide))

theorem cover78740 : P.CoversSplit 26 10 78740 0xcc00000000000000cc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000333300003300000022220000220000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [467, 489, 538, 923, 930, 979, 1658, 1665]) (by decide +kernel)

theorem c78740_0 : P.sumLeaves 26 80629760 256 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78740) (lo := 0) (len := 256) (W := 0) check rows elimOK (by decide) (by decide) cover78740 (by decide)
  decide +kernel

theorem contract78740_1 : P.leaf 32 1259844 = 4576 := by
  apply (leaf_contract (k := 32) (b := 17) (H := 1259844) (ss := [(32, 1, 467), (29, 7, 468), (15, 1, 472), (2, 1, 475), (8, 7, 486), (3, 1, 531), (16, 0, 867), (17, 0, 858), (7, 0, 859), (11, 0, 458), (12, 0, 461), (28, 1, 530), (26, 1, 922), (20, 1, 1265), (21, 1, 1272)]) (ids := [2, 3, 4, 7, 8, 11, 12, 16, 17, 20, 21, 22, 23, 25, 28, 29, 31]) (cs := [1, 1, 2, 3, 4, 0, 0, 5, 6, 0, 0, 7, 8, 1, 0, 0, 9, 10, 1, 1, 11, 12, 13, 14, 1, 15, 1, 0, 16, 17, 1, 18]) check rows (by decide) (by decide +kernel) (by decide +kernel)).trans
  decide +kernel

theorem c78740_1 : P.sumLeaves 26 80630016 64 = 4576 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1259844) rows (by decide) (by decide)).symm.trans contract78740_1

theorem c78740_2 : P.sumLeaves 26 80630080 576 = 17056 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78740) (lo := 320) (len := 576) (W := 17056) check rows elimOK (by decide) (by decide) cover78740 (by decide)
  decide +kernel

theorem contract78740_3 : P.leaf 32 1259854 = 5608 := by
  exact leaf_contract_factors (k := 32) (b := 14) (H := 1259854) (ss := [(32, 1, 467), (29, 7, 468), (15, 1, 472), (2, 1, 475), (8, 7, 486), (7, 1, 489), (14, 1, 465), (31, 1, 489), (3, 1, 531), (10, 1, 458), (33, 1, 538), (11, 1, 809), (13, 1, 461), (12, 1, 810), (16, 1, 858), (18, 1, 517), (17, 1, 859), (21, 1, 916)]) (ids := [2, 3, 4, 7, 17, 18, 20, 23, 24, 26, 28, 21, 22, 25]) (cs := [1, 1, 2, 3, 4, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 7, 1, 8, 13, 14, 9, 10, 15, 11, 1, 12, 1, 1, 1]) (bs := [11, 3]) (W := 5608) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c78740_3 : P.sumLeaves 26 80630656 64 = 5608 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1259854) rows (by decide) (by decide)).symm.trans contract78740_3

theorem contract78740_4 : P.leaf 32 1259855 = 7928 := by
  exact leaf_contract_factors (k := 32) (b := 14) (H := 1259855) (ss := [(32, 1, 467), (29, 7, 468), (15, 1, 472), (2, 1, 475), (8, 7, 486), (7, 1, 489), (14, 1, 465), (31, 1, 489), (3, 1, 531), (10, 1, 458), (33, 1, 538), (11, 1, 809), (13, 1, 461), (12, 1, 810), (16, 1, 858), (18, 1, 517), (17, 1, 859), (21, 1, 916)]) (ids := [2, 3, 4, 7, 17, 18, 20, 23, 24, 26, 28, 21, 22, 25]) (cs := [1, 1, 2, 3, 4, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 7, 1, 8, 13, 14, 9, 10, 15, 11, 1, 12, 1, 1, 1]) (bs := [11, 3]) (W := 7928) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c78740_4 : P.sumLeaves 26 80630720 64 = 7928 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1259855) rows (by decide) (by decide)).symm.trans contract78740_4

theorem h78740 : P.leaf 36 78740 = 35168 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(256, 0), (64, 4576), (576, 17056), (64, 5608), (64, 7928)]) (.cons c78740_0 (.cons c78740_1 (.cons c78740_2 (.cons c78740_3 (.cons c78740_4 (.nil)))))) (by decide) (by decide))

theorem cover78741 : P.CoversSplit 26 10 78741 0xcc00000000000000cc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 538, 873, 923, 930, 972, 979, 1315, 1658, 1665]) (by decide +kernel)

theorem c78741_0 : P.sumLeaves 26 80630784 896 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78741) (lo := 0) (len := 896) (W := 0) check rows elimOK (by decide) (by decide) cover78741 (by decide)
  decide +kernel

theorem contract78741_1 : P.leaf 32 1259870 = 18816 := by
  exact leaf_contract_factors (k := 32) (b := 16) (H := 1259870) (ss := [(2, 1, 475), (29, 1, 489), (31, 1, 489), (3, 1, 531), (33, 1, 538), (16, 1, 867), (14, 1, 859), (17, 1, 859), (11, 1, 879), (12, 1, 880), (10, 1, 809), (13, 1, 825), (18, 1, 1217), (21, 1, 1272), (15, 1, 916), (32, 1, 1315)]) (ids := [2, 3, 4, 5, 6, 7, 17, 18, 20, 23, 24, 26, 28, 21, 22, 25]) (cs := [1, 1, 2, 3, 4, 5, 6, 7, 1, 1, 1, 1, 1, 1, 1, 1, 1, 8, 9, 1, 10, 15, 16, 11, 12, 17, 13, 1, 14, 1, 1, 1]) (bs := [13, 3]) (W := 18816) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c78741_1 : P.sumLeaves 26 80631680 64 = 18816 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1259870) rows (by decide) (by decide)).symm.trans contract78741_1

theorem contract78741_2 : P.leaf 32 1259871 = 31440 := by
  exact leaf_contract_factors (k := 32) (b := 16) (H := 1259871) (ss := [(2, 1, 475), (29, 1, 489), (31, 1, 489), (3, 1, 531), (33, 1, 538), (16, 1, 867), (14, 1, 859), (17, 1, 859), (11, 1, 879), (12, 1, 880), (10, 1, 809), (13, 1, 825), (18, 1, 1217), (21, 1, 1272), (15, 1, 916), (32, 1, 1315)]) (ids := [2, 3, 4, 5, 6, 7, 17, 18, 20, 23, 26, 28, 21, 22, 24, 25]) (cs := [1, 1, 2, 3, 4, 5, 6, 7, 1, 1, 1, 1, 1, 1, 1, 1, 1, 8, 9, 1, 10, 14, 15, 11, 16, 17, 12, 1, 13, 1, 1, 1]) (bs := [12, 4]) (W := 31440) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c78741_2 : P.sumLeaves 26 80631744 64 = 31440 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1259871) rows (by decide) (by decide)).symm.trans contract78741_2

theorem h78741 : P.leaf 36 78741 = 50256 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(896, 0), (64, 18816), (64, 31440)]) (.cons c78741_0 (.cons c78741_1 (.cons c78741_2 (.nil)))) (by decide) (by decide))

theorem cover78742 : P.CoversSplit 26 10 78742 0xcc00000000000000cc00000000000000000000000000000000000000000000000c0000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000333300003300030022220000220002000000000000000000000000000000000003030000030000000202000002000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 538, 873, 930, 972, 979, 1315, 1658, 1665]) (by decide +kernel)

theorem c78742_0 : P.sumLeaves 26 80631808 64 = 440 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78742) (lo := 0) (len := 64) (W := 440) check rows elimOK (by decide) (by decide) cover78742 (by decide)
  decide +kernel

theorem contract78742_1 : P.leaf 32 1259873 = 1089 := by
  apply (leaf_contract (k := 32) (b := 14) (H := 1259873) (ss := [(22, 1, 433), (29, 7, 468), (2, 1, 482), (8, 7, 486), (3, 1, 531), (4, 1, 580), (5, 1, 629), (16, 0, 867), (7, 0, 858), (11, 0, 458), (12, 0, 461), (17, 0, 465), (21, 1, 1272), (30, 0, 1315), (14, 1, 873), (32, 1, 873), (18, 0, 1315), (9, 1, 1609)]) (ids := [4, 8, 11, 13, 17, 18, 21, 22, 23, 24, 25, 26, 29, 31]) (cs := [1, 1, 1, 1, 2, 0, 0, 1, 3, 0, 0, 4, 1, 5, 0, 0, 0, 6, 7, 1, 1, 8, 9, 10, 11, 12, 13, 0, 0, 14, 1, 15]) check rows (by decide) (by decide +kernel) (by decide +kernel)).trans
  decide +kernel

theorem c78742_1 : P.sumLeaves 26 80631872 64 = 1089 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1259873) rows (by decide) (by decide)).symm.trans contract78742_1

theorem c78742_2 : P.sumLeaves 26 80631936 768 = 116229 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78742) (lo := 128) (len := 768) (W := 116229) check rows elimOK (by decide) (by decide) cover78742 (by decide)
  decide +kernel

theorem contract78742_3 : P.leaf 32 1259886 = 23024 := by
  exact leaf_contract_factors (k := 32) (b := 16) (H := 1259886) (ss := [(29, 7, 468), (8, 7, 486), (7, 1, 489), (31, 1, 489), (3, 1, 531), (10, 1, 458), (33, 1, 538), (11, 1, 809), (13, 1, 461), (12, 1, 810), (14, 1, 858), (16, 1, 858), (18, 1, 517), (17, 1, 859), (21, 1, 1272), (32, 1, 1315)]) (ids := [0, 2, 3, 4, 7, 13, 17, 18, 20, 23, 24, 26, 28, 21, 22, 25]) (cs := [2, 1, 3, 4, 5, 1, 1, 6, 1, 1, 1, 1, 1, 7, 1, 1, 1, 8, 9, 1, 10, 15, 16, 11, 12, 17, 13, 1, 14, 1, 1, 1]) (bs := [13, 3]) (W := 23024) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c78742_3 : P.sumLeaves 26 80632704 64 = 23024 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1259886) rows (by decide) (by decide)).symm.trans contract78742_3

theorem contract78742_4 : P.leaf 32 1259887 = 32120 := by
  exact leaf_contract_factors (k := 32) (b := 16) (H := 1259887) (ss := [(29, 7, 468), (8, 7, 486), (7, 1, 489), (31, 1, 489), (3, 1, 531), (10, 1, 458), (33, 1, 538), (11, 1, 809), (13, 1, 461), (12, 1, 810), (14, 1, 858), (16, 1, 858), (18, 1, 517), (17, 1, 859), (21, 1, 1272), (32, 1, 1315)]) (ids := [0, 2, 3, 4, 7, 13, 17, 18, 20, 23, 24, 26, 28, 21, 22, 25]) (cs := [2, 1, 3, 4, 5, 1, 1, 6, 1, 1, 1, 1, 1, 7, 1, 1, 1, 8, 9, 1, 10, 15, 16, 11, 12, 17, 13, 1, 14, 1, 1, 1]) (bs := [13, 3]) (W := 32120) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c78742_4 : P.sumLeaves 26 80632768 64 = 32120 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1259887) rows (by decide) (by decide)).symm.trans contract78742_4

theorem h78742 : P.leaf 36 78742 = 172902 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(64, 440), (64, 1089), (768, 116229), (64, 23024), (64, 32120)]) (.cons c78742_0 (.cons c78742_1 (.cons c78742_2 (.cons c78742_3 (.cons c78742_4 (.nil)))))) (by decide) (by decide))

theorem cover78743 : P.CoversSplit 26 10 78743 0xcc00000000000000cc00000000000000000000000000000000000000000000000c0000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 538, 873, 930, 972, 979, 1315, 1658, 1665]) (by decide +kernel)

theorem c78743_0 : P.sumLeaves 26 80632832 896 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78743) (lo := 0) (len := 896) (W := 0) check rows elimOK (by decide) (by decide) cover78743 (by decide)
  decide +kernel

theorem contract78743_1 : P.leaf 32 1259902 = 185156 := by
  exact leaf_contract_factors (k := 32) (b := 19) (H := 1259902) (ss := [(29, 1, 489), (31, 1, 489), (3, 1, 531), (33, 1, 538), (16, 1, 867), (14, 1, 859), (17, 1, 859), (11, 1, 879), (12, 1, 880), (13, 1, 825), (18, 1, 1217), (21, 1, 1272), (32, 1, 1315)]) (ids := [0, 2, 3, 4, 5, 6, 7, 8, 13, 17, 18, 20, 21, 23, 24, 26, 28, 22, 25]) (cs := [2, 1, 3, 4, 5, 6, 7, 8, 9, 1, 1, 1, 1, 10, 1, 1, 1, 11, 12, 1, 13, 14, 19, 15, 16, 20, 17, 1, 18, 1, 1, 1]) (bs := [17, 2]) (W := 185156) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c78743_1 : P.sumLeaves 26 80633728 64 = 185156 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1259902) rows (by decide) (by decide)).symm.trans contract78743_1

theorem contract78743_2 : P.leaf 32 1259903 = 268352 := by
  exact leaf_contract_factors (k := 32) (b := 19) (H := 1259903) (ss := [(29, 1, 489), (31, 1, 489), (3, 1, 531), (33, 1, 538), (16, 1, 867), (14, 1, 859), (17, 1, 859), (11, 1, 879), (12, 1, 880), (13, 1, 825), (18, 1, 1217), (21, 1, 1272), (32, 1, 1315)]) (ids := [0, 2, 3, 4, 5, 6, 7, 13, 17, 18, 20, 23, 24, 26, 28, 8, 21, 22, 25]) (cs := [2, 1, 3, 4, 5, 6, 7, 8, 17, 1, 1, 1, 1, 9, 1, 1, 1, 10, 11, 1, 12, 18, 19, 13, 14, 20, 15, 1, 16, 1, 1, 1]) (bs := [15, 4]) (W := 268352) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c78743_2 : P.sumLeaves 26 80633792 64 = 268352 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1259903) rows (by decide) (by decide)).symm.trans contract78743_2

theorem h78743 : P.leaf 36 78743 = 453508 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(896, 0), (64, 185156), (64, 268352)]) (.cons c78743_0 (.cons c78743_1 (.cons c78743_2 (.nil)))) (by decide) (by decide))

theorem h78745 : P.leaf 36 78745 = 108256 := by
  exact leaf_contract_factors (k := 36) (b := 19) (H := 78745) (ss := [(17, 1, 467), (3, 1, 531), (33, 1, 537), (11, 1, 879), (7, 1, 460), (12, 1, 460), (10, 1, 809), (13, 1, 818), (36, 1, 923), (21, 1, 929), (18, 1, 1217), (32, 1, 1315), (30, 1, 972), (14, 1, 859), (37, 1, 1322), (35, 1, 1273), (16, 1, 1210)]) (ids := [0, 2, 3, 4, 6, 7, 13, 17, 18, 20, 23, 26, 27, 29, 32, 21, 22, 24, 25]) (cs := [2, 1, 3, 4, 5, 1, 6, 7, 1, 1, 1, 1, 1, 8, 1, 1, 1, 9, 10, 1, 11, 17, 18, 12, 19, 20, 13, 14, 1, 15, 1, 1, 16, 1, 1, 1]) (bs := [15, 4]) (W := 108256) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem cover78747 : P.CoversSplit 26 10 78747 0xf0f0000000000000f0f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [481, 530, 538, 615, 873, 930, 972, 979, 1273, 1315, 1322, 1658]) (ps := [(17, [874], [1322])]) (by decide +kernel)

theorem c78747_0 : P.sumLeaves 26 80636928 896 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78747) (lo := 0) (len := 896) (W := 0) check rows elimOK (by decide) (by decide) cover78747 (by decide)
  decide +kernel

theorem contract78747_1 : P.leaf 32 1259966 = 171072 := by
  exact leaf_contract_factors (k := 32) (b := 19) (H := 1259966) (ss := [(3, 1, 531), (33, 1, 537), (17, 1, 874), (11, 1, 879), (10, 1, 810), (12, 1, 810), (13, 1, 825), (21, 1, 929), (18, 1, 1217), (16, 1, 1210), (14, 1, 859), (32, 1, 1315), (30, 1, 972)]) (ids := [0, 2, 3, 4, 5, 6, 7, 13, 17, 18, 20, 23, 26, 27, 29, 21, 22, 24, 25]) (cs := [2, 1, 3, 4, 5, 6, 7, 8, 1, 1, 1, 1, 1, 9, 1, 1, 1, 10, 11, 1, 12, 17, 18, 13, 19, 20, 14, 15, 1, 16, 1, 1]) (bs := [15, 4]) (W := 171072) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c78747_1 : P.sumLeaves 26 80637824 64 = 171072 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1259966) rows (by decide) (by decide)).symm.trans contract78747_1

theorem contract78747_2 : P.leaf 32 1259967 = 181568 := by
  exact leaf_contract_factors (k := 32) (b := 19) (H := 1259967) (ss := [(3, 1, 531), (33, 1, 537), (17, 1, 874), (11, 1, 879), (10, 1, 810), (12, 1, 810), (13, 1, 825), (21, 1, 929), (18, 1, 1217), (16, 1, 1210), (14, 1, 859), (32, 1, 1315), (30, 1, 972)]) (ids := [0, 2, 3, 4, 5, 6, 7, 13, 17, 18, 20, 23, 26, 27, 29, 21, 22, 24, 25]) (cs := [2, 1, 3, 4, 5, 6, 7, 8, 1, 1, 1, 1, 1, 9, 1, 1, 1, 10, 11, 1, 12, 17, 18, 13, 19, 20, 14, 15, 1, 16, 1, 1]) (bs := [15, 4]) (W := 181568) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c78747_2 : P.sumLeaves 26 80637888 64 = 181568 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1259967) rows (by decide) (by decide)).symm.trans contract78747_2

theorem h78747 : P.leaf 36 78747 = 352640 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(896, 0), (64, 171072), (64, 181568)]) (.cons c78747_0 (.cons c78747_1 (.cons c78747_2 (.nil)))) (by decide) (by decide))

theorem h78748 : P.leaf 36 78748 = 125312 := by
  exact leaf_contract_factors (k := 36) (b := 18) (H := 78748) (ss := [(32, 1, 467), (15, 1, 472), (3, 1, 531), (35, 1, 867), (37, 17, 874), (11, 1, 879), (10, 1, 810), (12, 1, 810), (17, 1, 880), (8, 1, 465), (14, 1, 465), (2, 1, 409), (18, 1, 517), (16, 1, 858), (36, 1, 923), (21, 1, 1272), (13, 1, 818), (33, 1, 1273)]) (ids := [2, 3, 4, 7, 17, 18, 20, 23, 24, 26, 27, 28, 32, 5, 21, 22, 25, 29]) (cs := [1, 1, 2, 3, 4, 15, 1, 5, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 7, 1, 8, 16, 17, 9, 10, 18, 11, 12, 13, 19, 1, 1, 14, 1, 1, 1]) (bs := [13, 5]) (W := 125312) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem cover78749 : P.CoversSplit 26 10 78749 0xffff000000000000ffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003300030000000000220002000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [530, 538, 873, 923, 930, 972, 979, 1273, 1315, 1322, 1658]) (ps := [(17, [874], [1322])]) (by decide +kernel)

theorem c78749_0 : P.sumLeaves 26 80638976 320 = 9120 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78749) (lo := 0) (len := 320) (W := 9120) check rows elimOK (by decide) (by decide) cover78749 (by decide)
  decide +kernel

theorem contract78749_1 : P.leaf 32 1259989 = 22864 := by
  exact leaf_contract_factors (k := 32) (b := 18) (H := 1259989) (ss := [(2, 1, 475), (3, 1, 531), (17, 1, 874), (11, 1, 879), (12, 1, 880), (10, 1, 809), (31, 1, 930), (18, 1, 1217), (21, 1, 1272), (13, 1, 818), (15, 1, 916), (29, 0, 1273), (33, 0, 1322), (27, 1, 587)]) (ids := [2, 3, 6, 7, 12, 14, 17, 18, 20, 23, 24, 26, 28, 30, 4, 5, 21, 22]) (cs := [1, 1, 2, 3, 16, 17, 4, 5, 1, 1, 1, 1, 6, 1, 7, 1, 1, 8, 9, 1, 10, 18, 19, 11, 12, 1, 13, 0, 14, 1, 15, 0]) (bs := [14, 4]) (W := 22864) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c78749_1 : P.sumLeaves 26 80639296 64 = 22864 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1259989) rows (by decide) (by decide)).symm.trans contract78749_1

theorem c78749_2 : P.sumLeaves 26 80639360 512 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78749) (lo := 384) (len := 512) (W := 0) check rows elimOK (by decide) (by decide) cover78749 (by decide)
  decide +kernel

theorem contract78749_3 : P.leaf 32 1259998 = 165120 := by
  exact leaf_contract_factors (k := 32) (b := 20) (H := 1259998) (ss := [(3, 1, 531), (17, 1, 874), (11, 1, 879), (12, 1, 880), (10, 1, 809), (18, 1, 1217), (16, 1, 1210), (14, 1, 859), (21, 1, 1272), (13, 1, 818), (33, 1, 1273), (32, 1, 1315)]) (ids := [0, 2, 3, 4, 5, 6, 7, 13, 17, 18, 20, 23, 24, 26, 27, 28, 29, 21, 22, 25]) (cs := [2, 1, 3, 4, 5, 6, 7, 8, 1, 1, 1, 1, 1, 9, 1, 1, 1, 10, 11, 1, 12, 19, 20, 13, 14, 21, 15, 16, 17, 18, 1, 1]) (bs := [17, 3]) (W := 165120) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c78749_3 : P.sumLeaves 26 80639872 64 = 165120 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1259998) rows (by decide) (by decide)).symm.trans contract78749_3

theorem contract78749_4 : P.leaf 32 1259999 = 221312 := by
  exact leaf_contract_factors (k := 32) (b := 20) (H := 1259999) (ss := [(3, 1, 531), (17, 1, 874), (11, 1, 879), (12, 1, 880), (10, 1, 809), (18, 1, 1217), (16, 1, 1210), (14, 1, 859), (21, 1, 1272), (13, 1, 818), (33, 1, 1273), (32, 1, 1315)]) (ids := [0, 2, 3, 4, 5, 6, 7, 13, 17, 18, 20, 23, 24, 26, 27, 28, 29, 21, 22, 25]) (cs := [2, 1, 3, 4, 5, 6, 7, 8, 1, 1, 1, 1, 1, 9, 1, 1, 1, 10, 11, 1, 12, 19, 20, 13, 14, 21, 15, 16, 17, 18, 1, 1]) (bs := [17, 3]) (W := 221312) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c78749_4 : P.sumLeaves 26 80639936 64 = 221312 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1259999) rows (by decide) (by decide)).symm.trans contract78749_4

theorem h78749 : P.leaf 36 78749 = 418416 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(320, 9120), (64, 22864), (512, 0), (64, 165120), (64, 221312)]) (.cons c78749_0 (.cons c78749_1 (.cons c78749_2 (.cons c78749_3 (.cons c78749_4 (.nil)))))) (by decide) (by decide))

theorem h78750 : P.leaf 36 78750 = 641480 := by
  exact leaf_contract_factors (k := 36) (b := 23) (H := 78750) (ss := [(3, 1, 531), (35, 1, 867), (37, 17, 874), (11, 1, 879), (10, 1, 810), (12, 1, 810), (17, 1, 880), (8, 1, 465), (14, 1, 465), (18, 1, 517), (16, 1, 858), (21, 1, 1272), (33, 1, 1273)]) (ids := [0, 2, 3, 4, 5, 7, 11, 13, 17, 18, 20, 23, 24, 26, 27, 28, 29, 30, 32, 34, 21, 22, 25]) (cs := [2, 1, 3, 4, 5, 6, 1, 7, 1, 1, 1, 8, 1, 9, 1, 1, 1, 10, 11, 1, 12, 22, 23, 13, 14, 24, 15, 16, 17, 18, 19, 1, 20, 1, 21, 1]) (bs := [20, 3]) (W := 641480) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem cover78751 : P.CoversSplit 26 10 78751 0xffff000000000000ffff000000000000000000000000000000000000000000000f0f0a0a000000000a0a0a0a000000000000000000000000000000000000000000000000000000000000000000000000000000003300030000000000220002000000000000000000000000000000000000000000030002000000000002000200 :=
  coversProjected check rows (by decide) (by decide) (xs := [530, 538, 873, 930, 972, 979, 1273, 1315, 1322, 1658]) (ps := [(17, [874], [1322])]) (by decide +kernel)

theorem c78751_0 : P.sumLeaves 26 80641024 1024 = 3286513 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78751) (lo := 0) (len := 1024) (W := 3286513) check rows elimOK (by decide) (by decide) cover78751 (by decide)
  decide +kernel

theorem h78751 : P.leaf 36 78751 = 3286513 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 3286513)]) (.cons c78751_0 (.nil)) (by decide) (by decide))

theorem cover78774 : P.CoversSplit 26 10 78774 0xcc00cc0000000000cc00cc000000000000000000000000000000000000000000cc00c0000000000088008000000000000000000000000000000000000000000000000000000000000000000000000000333333303300300022222220220020000000000000000000000000000000000033333030330030002222202022002000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 538, 873, 930, 972, 979, 1315, 1658, 1665]) (by decide +kernel)

noncomputable def f78774 (i : ℕ) := rowWeight keep3 twice3 i * P.leaf 26 (80664576 + i)

theorem c78774_0 : rowSum f78774 0 1024 = 932856 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 78774) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover78774 (by decide)
  decide +kernel

theorem sum78774 : rowSum f78774 0 1024 = 932856 :=
  c78774_0

theorem h78774 : P.leaf 36 78774 = 932856 :=
  leaf_weighted (k := 26) (d := 10) (H := 78774) (keep := keep3) (twice := twice3) rows (by decide) (by decide) bal3 (invRow3 (H := 78774) (by decide) (by decide +kernel)) sum78774

theorem cover78775 : P.CoversSplit 26 10 78775 0xcc00cc0000000000cc00cc000000000000000000000000000000000000000000cc00c0000000000088008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 538, 873, 930, 972, 979, 1658, 1665]) (by decide +kernel)

noncomputable def f78775 (i : ℕ) := rowWeight keep3 twice3 i * P.leaf 26 (80665600 + i)

theorem c78775_0 : rowSum f78775 0 1024 = 3683424 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 78775) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover78775 (by decide)
  decide +kernel

theorem sum78775 : rowSum f78775 0 1024 = 3683424 :=
  c78775_0

theorem h78775 : P.leaf 36 78775 = 3683424 :=
  leaf_weighted (k := 26) (d := 10) (H := 78775) (keep := keep3) (twice := twice3) rows (by decide) (by decide) bal3 (invRow3 (H := 78775) (by decide) (by decide +kernel)) sum78775

theorem cover78776 : P.CoversSplit 26 10 78776 0xf0f0f0f500000000f0f0f0f50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 867, 873, 874, 923, 972, 1273]) (by decide +kernel)

theorem c78776_0 : P.sumLeaves 26 80666624 1024 = 102032 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78776) (lo := 0) (len := 1024) (W := 102032) check rows elimOK (by decide) (by decide) cover78776 (by decide)
  decide +kernel

theorem h78776 : P.leaf 36 78776 = 102032 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 102032)]) (.cons c78776_0 (.nil)) (by decide) (by decide))

theorem cover78777 : P.CoversSplit 26 10 78777 0xf0f0f0f500000000f0f0f0f50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000300030003000300020002000200020000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 923, 930, 972, 979, 1273, 1315, 1322, 1658]) (by decide +kernel)

theorem c78777_0 : P.sumLeaves 26 80667648 1024 = 1079392 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78777) (lo := 0) (len := 1024) (W := 1079392) check rows elimOK (by decide) (by decide) cover78777 (by decide)
  decide +kernel

theorem h78777 : P.leaf 36 78777 = 1079392 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1079392)]) (.cons c78777_0 (.nil)) (by decide) (by decide))

theorem cover78778 : P.CoversSplit 26 10 78778 0xf0f0f0f500000000f0f0f0f50000000000000000000000000000000000000000000050500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 867, 873, 874, 972, 1273, 1658]) (by decide +kernel)

theorem c78778_0 : P.sumLeaves 26 80668672 1024 = 703914 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78778) (lo := 0) (len := 1024) (W := 703914) check rows elimOK (by decide) (by decide) cover78778 (by decide)
  decide +kernel

theorem h78778 : P.leaf 36 78778 = 703914 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 703914)]) (.cons c78778_0 (.nil)) (by decide) (by decide))

theorem cover78779 : P.CoversSplit 26 10 78779 0xf0f0f0f500000000f0f0f0f50000000000000000000000000000000000000000000050500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000300030003000300020002000200020000000000000000000000000000000000000001000000010000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 873, 930, 972, 979, 1273, 1315, 1322, 1658]) (by decide +kernel)

theorem c78779_0 : P.sumLeaves 26 80669696 1024 = 3267486 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78779) (lo := 0) (len := 1024) (W := 3267486) check rows elimOK (by decide) (by decide) cover78779 (by decide)
  decide +kernel

theorem h78779 : P.leaf 36 78779 = 3267486 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 3267486)]) (.cons c78779_0 (.nil)) (by decide) (by decide))

theorem cover78782 : P.CoversSplit 26 10 78782 0xfffffffa00000000fffffffa0000000000000000000000000000000000000000fffff0f000000000aaaaa0a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [538, 867, 873, 874, 972, 1273, 1658]) (by decide +kernel)

theorem c78782_0 : P.sumLeaves 26 80672768 1024 = 4236932 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78782) (lo := 0) (len := 1024) (W := 4236932) check rows elimOK (by decide) (by decide) cover78782 (by decide)
  decide +kernel

theorem h78782 : P.leaf 36 78782 = 4236932 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 4236932)]) (.cons c78782_0 (.nil)) (by decide) (by decide))

theorem cover78783 : P.CoversSplit 26 10 78783 0xfffffffa00000000fffffffa0000000000000000000000000000000000000000fffff0f000000000aaaaa0a0000000000000000000000000000000000000000000000000000000000000000000000000330033003300300022002200220020000000000000000000000000000000000033003000330030002200200022002000 :=
  coversSplit check rows (by decide) (by decide) (xs := [538, 873, 930, 972, 979, 1273, 1315, 1322, 1658]) (by decide +kernel)

theorem contract78783_0 : P.leaf 32 1260528 = 17984 := by
  exact leaf_contract_factors (k := 32) (b := 19) (H := 1260528) (ss := [(22, 1, 433), (2, 1, 482), (3, 1, 531), (4, 1, 580), (7, 1, 825), (11, 1, 879), (12, 1, 880), (29, 0, 1273), (31, 1, 930), (6, 1, 636), (9, 1, 1609), (28, 1, 1658), (5, 1, 629)]) (ids := [6, 8, 11, 12, 13, 14, 15, 16, 17, 18, 19, 21, 22, 25, 28, 30, 31, 23, 24]) (cs := [1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 4, 5, 6, 7, 8, 9, 10, 11, 12, 1, 13, 14, 19, 20, 15, 1, 0, 16, 1, 17, 18]) (bs := [17, 2]) (W := 17984) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c78783_0 : P.sumLeaves 26 80673792 64 = 17984 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1260528) rows (by decide) (by decide)).symm.trans contract78783_0

theorem c78783_1 : P.sumLeaves 26 80673856 893 = 16334078 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78783) (lo := 64) (len := 893) (W := 16334078) check rows elimOK (by decide) (by decide) cover78783 (by decide)
  decide +kernel

theorem c78783_2 : P.sumLeaves 26 80674749 67 = 12474242 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78783) (lo := 957) (len := 67) (W := 12474242) check rows elimOK (by decide) (by decide) cover78783 (by decide)
  decide +kernel

theorem h78783 : P.leaf 36 78783 = 28826304 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(64, 17984), (893, 16334078), (67, 12474242)]) (.cons c78783_0 (.cons c78783_1 (.cons c78783_2 (.nil)))) (by decide) (by decide))

theorem cover78793 : P.CoversSplit 26 10 78793 0xf0f00000f0f00005f0f00000f0f00005f0f00000f0f00000a0a00000a08000000000000000000000000000000000000000000000000000000000000000000000f0f00000f0f00005f0f00000f0f00005f000000000000000a0000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 923, 930, 972, 979, 1273, 1315, 1658, 1665]) (by decide +kernel)

theorem c78793_0 : P.sumLeaves 26 80684032 320 = 832 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78793) (lo := 0) (len := 320) (W := 832) check rows elimOK (by decide) (by decide) cover78793 (by decide)
  decide +kernel

theorem contract78793_1 : P.leaf 32 1260693 = 1728 := by
  exact leaf_contract_factors (k := 32) (b := 13) (H := 1260693) (ss := [(16, 1, 466), (17, 1, 467), (11, 1, 472), (7, 1, 460), (12, 1, 460), (2, 1, 475), (8, 1, 515), (3, 1, 524), (10, 1, 809), (13, 1, 818), (14, 1, 858), (21, 1, 929), (31, 1, 930), (15, 1, 916), (30, 1, 972), (18, 1, 1210), (19, 1, 1259), (33, 1, 1273), (32, 1, 1315)]) (ids := [2, 3, 7, 18, 20, 25, 26, 27, 4, 21, 22, 23, 24]) (cs := [1, 1, 2, 3, 10, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 6, 11, 12, 13, 14, 7, 8, 9, 1, 1, 1, 1]) (bs := [8, 5]) (W := 1728) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c78793_1 : P.sumLeaves 26 80684352 64 = 1728 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1260693) rows (by decide) (by decide)).symm.trans contract78793_1

theorem contract78793_2 : P.leaf 32 1260694 = 6144 := by
  exact leaf_contract_factors (k := 32) (b := 19) (H := 1260694) (ss := [(16, 1, 466), (17, 1, 467), (11, 1, 472), (7, 1, 460), (12, 1, 460), (2, 1, 482), (8, 1, 515), (3, 1, 531), (10, 1, 809), (13, 1, 818), (14, 1, 858), (21, 1, 929), (18, 1, 1210)]) (ids := [2, 3, 4, 7, 13, 17, 18, 20, 23, 24, 25, 26, 27, 28, 29, 30, 31, 21, 22]) (cs := [1, 1, 2, 3, 4, 1, 1, 5, 1, 1, 1, 1, 1, 6, 1, 1, 1, 7, 8, 1, 9, 19, 20, 10, 11, 12, 13, 14, 15, 16, 17, 18]) (bs := [17, 2]) (W := 6144) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c78793_2 : P.sumLeaves 26 80684416 64 = 6144 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1260694) rows (by decide) (by decide)).symm.trans contract78793_2

theorem contract78793_3 : P.leaf 32 1260695 = 7200 := by
  exact leaf_contract_factors (k := 32) (b := 19) (H := 1260695) (ss := [(16, 1, 466), (17, 1, 467), (11, 1, 472), (7, 1, 460), (12, 1, 460), (2, 1, 482), (8, 1, 515), (3, 1, 531), (10, 1, 809), (13, 1, 818), (14, 1, 858), (21, 1, 929), (18, 1, 1210)]) (ids := [2, 3, 4, 7, 13, 17, 18, 20, 23, 24, 25, 26, 27, 28, 29, 30, 31, 21, 22]) (cs := [1, 1, 2, 3, 4, 1, 1, 5, 1, 1, 1, 1, 1, 6, 1, 1, 1, 7, 8, 1, 9, 19, 20, 10, 11, 12, 13, 14, 15, 16, 17, 18]) (bs := [17, 2]) (W := 7200) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c78793_3 : P.sumLeaves 26 80684480 64 = 7200 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1260695) rows (by decide) (by decide)).symm.trans contract78793_3

theorem c78793_4 : P.sumLeaves 26 80684544 256 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78793) (lo := 512) (len := 256) (W := 0) check rows elimOK (by decide) (by decide) cover78793 (by decide)
  decide +kernel

theorem contract78793_5 : P.leaf 32 1260700 = 4416 := by
  exact leaf_contract_factors (k := 32) (b := 16) (H := 1260700) (ss := [(16, 1, 466), (17, 1, 467), (11, 1, 472), (7, 1, 460), (12, 1, 460), (2, 1, 475), (8, 1, 515), (3, 1, 524), (10, 1, 809), (13, 1, 818), (14, 1, 858), (21, 1, 929), (18, 1, 1210), (28, 1, 1658), (30, 1, 972), (32, 1, 1315)]) (ids := [2, 3, 4, 7, 13, 17, 18, 20, 23, 25, 27, 29, 31, 21, 22, 24]) (cs := [1, 1, 2, 3, 4, 1, 1, 5, 1, 1, 1, 1, 1, 6, 1, 1, 1, 7, 8, 1, 9, 15, 16, 10, 17, 11, 1, 12, 1, 13, 1, 14]) (bs := [13, 3]) (W := 4416) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c78793_5 : P.sumLeaves 26 80684800 64 = 4416 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1260700) rows (by decide) (by decide)).symm.trans contract78793_5

theorem contract78793_6 : P.leaf 32 1260701 = 8928 := by
  exact leaf_contract_factors (k := 32) (b := 19) (H := 1260701) (ss := [(16, 1, 466), (17, 1, 467), (11, 1, 472), (7, 1, 460), (12, 1, 460), (2, 1, 475), (8, 1, 515), (3, 1, 524), (10, 1, 809), (13, 1, 818), (14, 1, 858), (21, 1, 929), (18, 1, 1210)]) (ids := [2, 3, 4, 7, 13, 17, 18, 20, 23, 24, 25, 26, 27, 28, 29, 30, 31, 21, 22]) (cs := [1, 1, 2, 3, 4, 1, 1, 5, 1, 1, 1, 1, 1, 6, 1, 1, 1, 7, 8, 1, 9, 19, 20, 10, 11, 12, 13, 14, 15, 16, 17, 18]) (bs := [17, 2]) (W := 8928) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c78793_6 : P.sumLeaves 26 80684864 64 = 8928 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1260701) rows (by decide) (by decide)).symm.trans contract78793_6

theorem c78793_7 : P.sumLeaves 26 80684928 128 = 70560 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78793) (lo := 896) (len := 128) (W := 70560) check rows elimOK (by decide) (by decide) cover78793 (by decide)
  decide +kernel

theorem h78793 : P.leaf 36 78793 = 99808 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(320, 832), (64, 1728), (64, 6144), (64, 7200), (256, 0), (64, 4416), (64, 8928), (128, 70560)]) (.cons c78793_0 (.cons c78793_1 (.cons c78793_2 (.cons c78793_3 (.cons c78793_4 (.cons c78793_5 (.cons c78793_6 (.cons c78793_7 (.nil))))))))) (by decide) (by decide))

theorem cover78795 : P.CoversSplit 26 10 78795 0xf0f00000f0f00005f0f00000f0f00005f0f00000f0f00000a0a00000a08000000000000000000000000000000000000000000000000000000000000000000000f0f00000f0f00005f0f00000f0f00005f000000000000000a0000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 930, 972, 979, 1266, 1273, 1315, 1658, 1665]) (by decide +kernel)

theorem c78795_0 : P.sumLeaves 26 80686080 320 = 4672 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78795) (lo := 0) (len := 320) (W := 4672) check rows elimOK (by decide) (by decide) cover78795 (by decide)
  decide +kernel

theorem contract78795_1 : P.leaf 32 1260725 = 8656 := by
  exact leaf_contract_factors (k := 32) (b := 16) (H := 1260725) (ss := [(12, 1, 479), (2, 1, 482), (3, 1, 524), (13, 1, 825), (16, 1, 867), (8, 1, 516), (17, 1, 516), (14, 1, 858), (21, 1, 929), (31, 1, 979), (30, 1, 972), (18, 1, 1210), (33, 1, 1273), (19, 1, 1259), (32, 1, 1315), (10, 1, 810)]) (ids := [2, 3, 5, 7, 9, 13, 18, 20, 23, 24, 25, 26, 27, 4, 21, 22]) (cs := [1, 1, 2, 3, 15, 4, 1, 5, 1, 6, 1, 1, 1, 7, 1, 1, 1, 1, 8, 1, 9, 16, 17, 10, 11, 12, 13, 14, 1, 1, 1, 1]) (bs := [13, 3]) (W := 8656) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c78795_1 : P.sumLeaves 26 80686400 64 = 8656 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1260725) rows (by decide) (by decide)).symm.trans contract78795_1

theorem c78795_2 : P.sumLeaves 26 80686464 384 = 122972 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78795) (lo := 384) (len := 384) (W := 122972) check rows elimOK (by decide) (by decide) cover78795 (by decide)
  decide +kernel

theorem contract78795_3 : P.leaf 32 1260732 = 43712 := by
  exact leaf_contract_factors (k := 32) (b := 19) (H := 1260732) (ss := [(12, 1, 479), (3, 1, 524), (13, 1, 825), (16, 1, 867), (8, 1, 516), (17, 1, 516), (14, 1, 858), (21, 1, 929), (18, 1, 1210), (28, 1, 1658), (30, 1, 972), (32, 1, 1315), (10, 1, 810)]) (ids := [0, 2, 3, 4, 5, 7, 9, 13, 17, 18, 20, 23, 25, 27, 29, 31, 21, 22, 24]) (cs := [2, 1, 3, 4, 5, 6, 1, 7, 1, 8, 1, 1, 1, 9, 1, 1, 1, 10, 11, 1, 12, 18, 19, 13, 20, 14, 1, 15, 1, 16, 1, 17]) (bs := [16, 3]) (W := 43712) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c78795_3 : P.sumLeaves 26 80686848 64 = 43712 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1260732) rows (by decide) (by decide)).symm.trans contract78795_3

theorem c78795_4 : P.sumLeaves 26 80686912 192 = 557284 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78795) (lo := 832) (len := 192) (W := 557284) check rows elimOK (by decide) (by decide) cover78795 (by decide)
  decide +kernel

theorem h78795 : P.leaf 36 78795 = 737296 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(320, 4672), (64, 8656), (384, 122972), (64, 43712), (192, 557284)]) (.cons c78795_0 (.cons c78795_1 (.cons c78795_2 (.cons c78795_3 (.cons c78795_4 (.nil)))))) (by decide) (by decide))

theorem cover78798 : P.CoversSplit 26 10 78798 0xffff0000ffff0500ffff0000ffff050000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 873, 879, 880, 972, 1266, 1315]) (by decide +kernel)

theorem c78798_0 : P.sumLeaves 26 80689152 1024 = 1002640 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78798) (lo := 0) (len := 1024) (W := 1002640) check rows elimOK (by decide) (by decide) cover78798 (by decide)
  decide +kernel

theorem h78798 : P.leaf 36 78798 = 1002640 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1002640)]) (.cons c78798_0 (.nil)) (by decide) (by decide))

theorem cover78799 : P.CoversSplit 26 10 78799 0xffff0000ffff0500ffff0000ffff0500fffc0000fffc0000aaa80000aa8800000000000000000000000000000000000000000000000000000000000000000000ffff0000ffff0500ffff0000ffff0500ffcc000000000000aa880000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 930, 972, 979, 1266, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c78799_0 : P.sumLeaves 26 80690176 827 = 3471542 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78799) (lo := 0) (len := 827) (W := 3471542) check rows elimOK (by decide) (by decide) cover78799 (by decide)
  decide +kernel

theorem c78799_1 : P.sumLeaves 26 80691003 194 = 7143982 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78799) (lo := 827) (len := 194) (W := 7143982) check rows elimOK (by decide) (by decide) cover78799 (by decide)
  decide +kernel

theorem c78799_2 : P.sumLeaves 26 80691197 3 = 434624 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78799) (lo := 1021) (len := 3) (W := 434624) check rows elimOK (by decide) (by decide) cover78799 (by decide)
  decide +kernel

theorem h78799 : P.leaf 36 78799 = 11050148 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(827, 3471542), (194, 7143982), (3, 434624)]) (.cons c78799_0 (.cons c78799_1 (.cons c78799_2 (.nil)))) (by decide) (by decide))

theorem cover78811 : P.CoversSplit 26 10 78811 0xf0f00000f0f00005f0f00000f0f00005f0f00000f0f00000a0a00000a08000000000000000000000000000000000000000000000000000000000000000000000f0f00000f0f00005f0f00000f0f00005f000000000000000a0000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 873, 930, 972, 979, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f78811 (i : ℕ) := rowWeight keep3 twice3 i * P.leaf 26 (80702464 + i)

theorem c78811_0 : rowSum f78811 0 1024 = 4833370 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 78811) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover78811 (by decide)
  decide +kernel

theorem sum78811 : rowSum f78811 0 1024 = 4833370 :=
  c78811_0

theorem h78811 : P.leaf 36 78811 = 4833370 :=
  leaf_weighted (k := 26) (d := 10) (H := 78811) (keep := keep3) (twice := twice3) rows (by decide) (by decide) bal3 (invRow3 (H := 78811) (by decide) (by decide +kernel)) sum78811

theorem h78812 : P.leaf 36 78812 = 901968 := by
  exact leaf_contract_factors (k := 36) (b := 22) (H := 78812) (ss := [(32, 1, 467), (15, 1, 472), (35, 1, 867), (37, 17, 874), (11, 1, 879), (10, 1, 810), (12, 1, 810), (17, 1, 880), (14, 1, 858), (16, 1, 858), (36, 1, 923), (18, 1, 1217), (21, 1, 1272), (13, 1, 818)]) (ids := [0, 1, 2, 3, 4, 5, 6, 7, 17, 18, 20, 23, 24, 25, 26, 27, 28, 29, 31, 32, 21, 22]) (cs := [2, 3, 4, 5, 6, 7, 8, 9, 1, 1, 1, 1, 1, 1, 1, 1, 1, 10, 11, 1, 12, 22, 23, 13, 14, 15, 16, 17, 18, 19, 1, 20, 21, 1, 1, 1]) (bs := [20, 2]) (W := 901968) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem cover78813 : P.CoversSplit 26 10 78813 0xffff0000ffff0500ffff0000ffff0500fffc0000fffc0000aaa80000aa8800000000000000000000000000000000000000000000000000000000000000000000ffff0000ffff0500ffff0000ffff0500ff00000000000000aa000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 873, 923, 930, 972, 979, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c78813_0 : P.sumLeaves 26 80704512 853 = 1680860 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78813) (lo := 0) (len := 853) (W := 1680860) check rows elimOK (by decide) (by decide) cover78813 (by decide)
  decide +kernel

theorem c78813_1 : P.sumLeaves 26 80705365 171 = 5301751 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78813) (lo := 853) (len := 171) (W := 5301751) check rows elimOK (by decide) (by decide) cover78813 (by decide)
  decide +kernel

theorem h78813 : P.leaf 36 78813 = 6982611 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(853, 1680860), (171, 5301751)]) (.cons c78813_0 (.cons c78813_1 (.nil))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(78719, 180), (78727, 360), (78729, 360), (78731, 720), (78734, 360), (78735, 360), (78740, 120), (78741, 360), (78742, 360), (78743, 720), (78745, 720), (78747, 720), (78748, 720), (78749, 720), (78750, 720), (78751, 720), (78774, 180), (78775, 180), (78776, 360), (78777, 360), (78778, 720), (78779, 720), (78782, 360), (78783, 360), (78793, 180), (78795, 720), (78798, 360), (78799, 360), (78811, 360), (78812, 360), (78813, 360)]

theorem segOK : checkSeg 20 perms 78719 78814 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 78719 78814 14160 63876463080 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 63876463080)
    (SegSum.cons (w := 180) h78719 (SegSum.cons (w := 360) h78727 (SegSum.cons (w := 360) h78729 (SegSum.cons (w := 720) h78731 (SegSum.cons (w := 360) h78734 (SegSum.cons (w := 360) h78735 (SegSum.cons (w := 120) h78740 (SegSum.cons (w := 360) h78741 (SegSum.cons (w := 360) h78742 (SegSum.cons (w := 720) h78743 (SegSum.cons (w := 720) h78745 (SegSum.cons (w := 720) h78747 (SegSum.cons (w := 720) h78748 (SegSum.cons (w := 720) h78749 (SegSum.cons (w := 720) h78750 (SegSum.cons (w := 720) h78751 (SegSum.cons (w := 180) h78774 (SegSum.cons (w := 180) h78775 (SegSum.cons (w := 360) h78776 (SegSum.cons (w := 360) h78777 (SegSum.cons (w := 720) h78778 (SegSum.cons (w := 720) h78779 (SegSum.cons (w := 360) h78782 (SegSum.cons (w := 360) h78783 (SegSum.cons (w := 180) h78793 (SegSum.cons (w := 720) h78795 (SegSum.cons (w := 360) h78798 (SegSum.cons (w := 360) h78799 (SegSum.cons (w := 360) h78811 (SegSum.cons (w := 360) h78812 (SegSum.cons (w := 360) h78813 (show SegSum (P.leaf 36) [] 0 from rfl)))))))))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S44
