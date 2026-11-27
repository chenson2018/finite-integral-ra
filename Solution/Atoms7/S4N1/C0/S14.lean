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

namespace RACert.S4N1.C0.S14

open RACert RACert.Problem

theorem cover1763 : P.CoversSplit 24 10 1763 0xff000000000000000000000000000000ff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [475, 515, 523, 524, 565, 566, 573, 860, 921, 1202, 1209, 1251, 1258, 1259, 1308]) (by decide +kernel)

theorem c1763_0 : P.sumLeaves 24 1805312 448 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1763) (lo := 0) (len := 448) (W := 0) check rows elimOK (by decide) (by decide) cover1763 (by decide)
  decide +kernel

theorem contract1763_1 : P.leaf 30 28215 = 6144 := by
  exact leaf_contract_factors (k := 30) (b := 14) (H := 28215) (ss := [(6, 1, 478), (12, 1, 478), (30, 18, 524), (18, 1, 536), (27, 1, 573), (11, 1, 818), (29, 1, 921), (13, 1, 922), (14, 1, 923), (8, 1, 580), (19, 1, 929), (15, 1, 930), (31, 1, 1209), (16, 1, 1265), (20, 1, 1657), (21, 1, 1658)]) (ids := [0, 1, 2, 3, 7, 8, 20, 26, 5, 15, 21, 22, 23, 24]) (cs := [2, 3, 4, 5, 1, 10, 1, 6, 7, 1, 1, 1, 1, 1, 1, 11, 1, 1, 1, 1, 8, 12, 13, 14, 15, 1, 9, 1, 1, 1]) (bs := [8, 6]) (W := 6144) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1763_1 : P.sumLeaves 24 1805760 64 = 6144 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 28215) rows (by decide) (by decide)).symm.trans contract1763_1

theorem c1763_2 : P.sumLeaves 24 1805824 320 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1763) (lo := 512) (len := 320) (W := 0) check rows elimOK (by decide) (by decide) cover1763 (by decide)
  decide +kernel

theorem contract1763_3 : P.leaf 30 28221 = 38592 := by
  exact leaf_contract_factors (k := 30) (b := 19) (H := 28221) (ss := [(6, 1, 478), (12, 1, 478), (30, 1, 524), (4, 1, 566), (11, 1, 818), (14, 1, 874), (16, 1, 874), (29, 1, 916), (31, 1, 1209), (18, 1, 1265), (17, 1, 1266)]) (ids := [0, 1, 3, 5, 6, 7, 8, 11, 13, 17, 18, 19, 20, 22, 24, 25, 26, 21, 23]) (cs := [2, 3, 1, 4, 1, 5, 6, 7, 8, 1, 1, 9, 1, 10, 1, 1, 1, 11, 12, 13, 14, 19, 15, 20, 16, 17, 18, 1, 1, 1]) (bs := [17, 2]) (W := 38592) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1763_3 : P.sumLeaves 24 1806144 64 = 38592 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 28221) rows (by decide) (by decide)).symm.trans contract1763_3

theorem c1763_4 : P.sumLeaves 24 1806208 128 = 187520 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1763) (lo := 896) (len := 128) (W := 187520) check rows elimOK (by decide) (by decide) cover1763 (by decide)
  decide +kernel

theorem h1763 : P.leaf 34 1763 = 232256 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(448, 0), (64, 6144), (320, 0), (64, 38592), (128, 187520)]) (.cons c1763_0 (.cons c1763_1 (.cons c1763_2 (.cons c1763_3 (.cons c1763_4 (.nil)))))) (by decide) (by decide))

theorem h1764 : P.leaf 34 1764 = 13824 := by
  exact leaf_contract_factors (k := 34) (b := 19) (H := 1764) (ss := [(6, 1, 466), (26, 1, 472), (35, 1, 475), (13, 1, 480), (27, 1, 508), (30, 1, 524), (14, 1, 559), (18, 1, 487), (12, 1, 867), (10, 1, 458), (11, 1, 459), (31, 1, 872), (29, 1, 916), (34, 1, 915), (32, 1, 522)]) (ids := [0, 1, 2, 3, 5, 6, 7, 13, 14, 15, 17, 18, 19, 20, 22, 26, 31, 21, 23]) (cs := [2, 3, 4, 5, 1, 6, 7, 8, 1, 1, 1, 1, 1, 9, 10, 11, 1, 12, 13, 14, 15, 19, 16, 20, 1, 1, 17, 1, 1, 1, 1, 18, 1, 1]) (bs := [17, 2]) (W := 13824) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem cover1765 : P.CoversSplit 24 10 1765 0xcc000000000000000000000000000000cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 475, 515, 522, 524, 573, 860, 872, 915, 916]) (by decide +kernel)

theorem c1765_0 : P.sumLeaves 24 1807360 832 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1765) (lo := 0) (len := 832) (W := 0) check rows elimOK (by decide) (by decide) cover1765 (by decide)
  decide +kernel

theorem contract1765_1 : P.leaf 30 28253 = 38592 := by
  exact leaf_contract_factors (k := 30) (b := 18) (H := 28253) (ss := [(27, 1, 473), (29, 1, 473), (13, 1, 480), (30, 1, 524), (4, 1, 536), (18, 1, 487), (14, 1, 559), (12, 1, 867), (11, 1, 818), (31, 1, 872), (16, 1, 1265), (17, 1, 1266)]) (ids := [0, 1, 3, 4, 6, 7, 8, 13, 17, 18, 19, 20, 22, 24, 26, 5, 21, 23]) (cs := [2, 3, 1, 4, 5, 17, 6, 7, 8, 1, 1, 1, 1, 9, 1, 1, 1, 10, 11, 12, 13, 18, 14, 19, 15, 1, 16, 1, 1, 1]) (bs := [15, 3]) (W := 38592) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1765_1 : P.sumLeaves 24 1808192 64 = 38592 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 28253) rows (by decide) (by decide)).symm.trans contract1765_1

theorem c1765_2 : P.sumLeaves 24 1808256 128 = 166976 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1765) (lo := 896) (len := 128) (W := 166976) check rows elimOK (by decide) (by decide) cover1765 (by decide)
  decide +kernel

theorem h1765 : P.leaf 34 1765 = 205568 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(832, 0), (64, 38592), (128, 166976)]) (.cons c1765_0 (.cons c1765_1 (.cons c1765_2 (.nil)))) (by decide) (by decide))

theorem cover1766 : P.CoversSplit 24 10 1766 0xaa000000000000000000000000000000a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000088000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 475, 515, 522, 524, 566, 573, 860, 915, 916, 921, 1209, 1258, 1259, 1308]) (by decide +kernel)

theorem c1766_0 : P.sumLeaves 24 1808384 1024 = 244352 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1766) (lo := 0) (len := 1024) (W := 244352) check rows elimOK (by decide) (by decide) cover1766 (by decide)
  decide +kernel

theorem h1766 : P.leaf 34 1766 = 244352 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 244352)]) (.cons c1766_0 (.nil)) (by decide) (by decide))

theorem cover1767 : P.CoversSplit 24 10 1767 0xff000000000000000000000000000000ff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [475, 515, 522, 524, 566, 573, 860, 915, 916, 921, 1202, 1209, 1251, 1258, 1259, 1308]) (by decide +kernel)

theorem c1767_0 : P.sumLeaves 24 1809408 448 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1767) (lo := 0) (len := 448) (W := 0) check rows elimOK (by decide) (by decide) cover1767 (by decide)
  decide +kernel

theorem contract1767_1 : P.leaf 30 28279 = 36032 := by
  exact leaf_contract_factors (k := 30) (b := 17) (H := 28279) (ss := [(30, 18, 524), (18, 1, 536), (27, 1, 573), (12, 1, 867), (29, 1, 916), (13, 1, 922), (14, 1, 923), (8, 1, 580), (19, 1, 929), (31, 1, 1209), (16, 1, 1265), (20, 1, 1657), (21, 1, 1658)]) (ids := [0, 1, 2, 3, 4, 7, 8, 9, 13, 20, 21, 24, 26, 5, 15, 22, 23]) (cs := [2, 3, 4, 5, 6, 15, 1, 7, 8, 9, 1, 1, 1, 10, 1, 16, 1, 1, 1, 1, 11, 12, 17, 18, 13, 1, 14, 1, 1, 1]) (bs := [13, 4]) (W := 36032) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1767_1 : P.sumLeaves 24 1809856 64 = 36032 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 28279) rows (by decide) (by decide)).symm.trans contract1767_1

theorem c1767_2 : P.sumLeaves 24 1809920 512 = 1553424 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1767) (lo := 512) (len := 512) (W := 1553424) check rows elimOK (by decide) (by decide) cover1767 (by decide)
  decide +kernel

theorem h1767 : P.leaf 34 1767 = 1589456 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(448, 0), (64, 36032), (512, 1553424)]) (.cons c1767_0 (.cons c1767_1 (.cons c1767_2 (.nil)))) (by decide) (by decide))

theorem h1768 : P.leaf 34 1768 = 20336 := by
  exact leaf_contract_factors (k := 34) (b := 21) (H := 1768) (ss := [(6, 1, 466), (26, 1, 472), (18, 1, 475), (35, 14, 487), (27, 1, 508), (15, 1, 558), (12, 1, 803), (11, 1, 459), (31, 1, 909), (30, 1, 515), (29, 1, 915), (34, 1, 915), (32, 1, 522)]) (ids := [0, 1, 2, 3, 5, 6, 7, 8, 11, 12, 14, 15, 17, 18, 19, 20, 21, 22, 26, 31, 23]) (cs := [2, 3, 4, 5, 1, 6, 7, 8, 9, 1, 1, 10, 11, 1, 12, 13, 1, 14, 15, 16, 17, 18, 19, 22, 1, 1, 20, 1, 1, 1, 1, 21, 1, 11]) (bs := [20, 1]) (W := 20336) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem cover1769 : P.CoversSplit 24 10 1769 0xcc000000000000000000000000000000cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 515, 522, 523, 573, 860, 872, 915, 1209, 1251, 1308, 1651]) (ps := [(14, [923], [487])]) (by decide +kernel)

theorem c1769_0 : P.sumLeaves 24 1811456 832 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1769) (lo := 0) (len := 832) (W := 0) check rows elimOK (by decide) (by decide) cover1769 (by decide)
  decide +kernel

theorem contract1769_1 : P.leaf 30 28317 = 30208 := by
  exact leaf_contract_factors (k := 30) (b := 17) (H := 28317) (ss := [(27, 1, 473), (29, 1, 473), (18, 1, 475), (14, 1, 487), (4, 1, 536), (2, 1, 410), (15, 1, 558), (12, 1, 867), (11, 1, 818), (31, 1, 872), (16, 1, 874), (30, 1, 1209), (17, 1, 1266)]) (ids := [1, 3, 4, 5, 6, 7, 8, 11, 17, 18, 19, 20, 21, 22, 24, 26, 23]) (cs := [1, 2, 1, 3, 4, 5, 6, 7, 8, 1, 1, 9, 1, 1, 1, 1, 1, 10, 11, 12, 13, 14, 15, 18, 16, 1, 17, 1, 1, 1]) (bs := [16, 1]) (W := 30208) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1769_1 : P.sumLeaves 24 1812288 64 = 30208 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 28317) rows (by decide) (by decide)).symm.trans contract1769_1

theorem c1769_2 : P.sumLeaves 24 1812352 128 = 124416 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1769) (lo := 896) (len := 128) (W := 124416) check rows elimOK (by decide) (by decide) cover1769 (by decide)
  decide +kernel

theorem h1769 : P.leaf 34 1769 = 154624 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(832, 0), (64, 30208), (128, 124416)]) (.cons c1769_0 (.cons c1769_1 (.cons c1769_2 (.nil)))) (by decide) (by decide))

theorem cover1770 : P.CoversSplit 24 10 1770 0xaa000000000000000000000000000000a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000088000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 515, 522, 523, 565, 573, 860, 872, 921, 1209, 1258, 1259, 1308]) (ps := [(14, [874], [860])]) (by decide +kernel)

theorem c1770_0 : P.sumLeaves 24 1812480 1024 = 151720 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1770) (lo := 0) (len := 1024) (W := 151720) check rows elimOK (by decide) (by decide) cover1770 (by decide)
  decide +kernel

theorem h1770 : P.leaf 34 1770 = 151720 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 151720)]) (.cons c1770_0 (.nil)) (by decide) (by decide))

theorem cover1771 : P.CoversSplit 24 10 1771 0xff000000000000000000000000000000ff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 522, 523, 565, 573, 860, 921, 1202, 1209, 1251, 1258, 1259, 1308]) (by decide +kernel)

theorem c1771_0 : P.sumLeaves 24 1813504 448 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1771) (lo := 0) (len := 448) (W := 0) check rows elimOK (by decide) (by decide) cover1771 (by decide)
  decide +kernel

theorem contract1771_1 : P.leaf 30 28343 = 15872 := by
  exact leaf_contract_factors (k := 30) (b := 15) (H := 28343) (ss := [(18, 1, 524), (27, 1, 573), (12, 1, 867), (11, 1, 818), (29, 1, 921), (13, 1, 922), (14, 1, 923), (8, 1, 580), (19, 1, 965), (15, 1, 930), (30, 1, 1251), (31, 1, 1209), (16, 1, 1265), (20, 1, 1657), (21, 1, 1658)]) (ids := [0, 1, 2, 3, 7, 8, 20, 26, 4, 5, 15, 21, 22, 23, 24]) (cs := [2, 3, 4, 5, 10, 11, 1, 6, 7, 1, 1, 1, 1, 1, 1, 12, 1, 1, 1, 1, 8, 13, 14, 15, 16, 1, 9, 1, 1, 1]) (bs := [8, 7]) (W := 15872) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1771_1 : P.sumLeaves 24 1813952 64 = 15872 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 28343) rows (by decide) (by decide)).symm.trans contract1771_1

theorem c1771_2 : P.sumLeaves 24 1814016 512 = 644160 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1771) (lo := 512) (len := 512) (W := 644160) check rows elimOK (by decide) (by decide) cover1771 (by decide)
  decide +kernel

theorem h1771 : P.leaf 34 1771 = 660032 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(448, 0), (64, 15872), (512, 644160)]) (.cons c1771_0 (.cons c1771_1 (.cons c1771_2 (.nil)))) (by decide) (by decide))

theorem cover1772 : P.CoversSplit 24 10 1772 0x8800000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000088000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 508, 515, 522, 573, 860, 872, 915, 1202, 1308]) (by decide +kernel)

theorem c1772_0 : P.sumLeaves 24 1814528 1024 = 99880 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1772) (lo := 0) (len := 1024) (W := 99880) check rows elimOK (by decide) (by decide) cover1772 (by decide)
  decide +kernel

theorem h1772 : P.leaf 34 1772 = 99880 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 99880)]) (.cons c1772_0 (.nil)) (by decide) (by decide))

theorem cover1773 : P.CoversSplit 24 10 1773 0xcc000000000000000000000000000000cc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 515, 522, 573, 860, 872, 915, 1209, 1251, 1308, 1651]) (by decide +kernel)

theorem c1773_0 : P.sumLeaves 24 1815552 448 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1773) (lo := 0) (len := 448) (W := 0) check rows elimOK (by decide) (by decide) cover1773 (by decide)
  decide +kernel

theorem contract1773_1 : P.leaf 30 28375 = 34272 := by
  exact leaf_contract_factors (k := 30) (b := 19) (H := 28375) (ss := [(27, 1, 473), (29, 1, 473), (18, 1, 475), (12, 1, 867), (11, 1, 818), (31, 1, 872), (13, 1, 922), (14, 1, 923), (30, 1, 1251), (16, 1, 1265), (20, 1, 1657)]) (ids := [0, 1, 2, 3, 4, 5, 6, 7, 8, 13, 15, 17, 19, 20, 21, 22, 24, 26, 23]) (cs := [2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 1, 1, 1, 11, 1, 12, 1, 13, 1, 14, 15, 16, 17, 20, 18, 1, 19, 1, 1, 1]) (bs := [18, 1]) (W := 34272) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1773_1 : P.sumLeaves 24 1816000 64 = 34272 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 28375) rows (by decide) (by decide)).symm.trans contract1773_1

theorem c1773_2 : P.sumLeaves 24 1816064 512 = 770304 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1773) (lo := 512) (len := 512) (W := 770304) check rows elimOK (by decide) (by decide) cover1773 (by decide)
  decide +kernel

theorem h1773 : P.leaf 34 1773 = 804576 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(448, 0), (64, 34272), (512, 770304)]) (.cons c1773_0 (.cons c1773_1 (.cons c1773_2 (.nil)))) (by decide) (by decide))

theorem cover1774 : P.CoversSplit 24 10 1774 0xaa000000000000000000000000000000a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000088000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 515, 522, 573, 860, 872, 916, 921, 1209, 1258, 1259, 1308]) (by decide +kernel)

theorem c1774_0 : P.sumLeaves 24 1816576 1024 = 856696 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1774) (lo := 0) (len := 1024) (W := 856696) check rows elimOK (by decide) (by decide) cover1774 (by decide)
  decide +kernel

theorem h1774 : P.leaf 34 1774 = 856696 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 856696)]) (.cons c1774_0 (.nil)) (by decide) (by decide))

theorem cover1775 : P.CoversSplit 24 10 1775 0xff000000000000000000000000000000ff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 522, 573, 860, 916, 921, 1202, 1209, 1251, 1258, 1259, 1308]) (by decide +kernel)

theorem c1775_0 : P.sumLeaves 24 1817600 448 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1775) (lo := 0) (len := 448) (W := 0) check rows elimOK (by decide) (by decide) cover1775 (by decide)
  decide +kernel

theorem contract1775_1 : P.leaf 30 28407 = 57920 := by
  exact leaf_contract_factors (k := 30) (b := 18) (H := 28407) (ss := [(18, 1, 524), (27, 1, 573), (12, 1, 867), (29, 1, 916), (13, 1, 922), (14, 1, 923), (8, 1, 580), (30, 1, 1251), (31, 1, 1209), (16, 1, 1265), (20, 1, 1657), (21, 1, 1658)]) (ids := [0, 1, 2, 3, 4, 7, 8, 9, 13, 15, 17, 20, 21, 24, 26, 5, 22, 23]) (cs := [2, 3, 4, 5, 6, 17, 1, 7, 8, 9, 1, 1, 1, 10, 1, 11, 1, 12, 1, 1, 13, 14, 18, 19, 15, 1, 16, 1, 1, 1]) (bs := [15, 3]) (W := 57920) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1775_1 : P.sumLeaves 24 1818048 64 = 57920 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 28407) rows (by decide) (by decide)).symm.trans contract1775_1

theorem c1775_2 : P.sumLeaves 24 1818112 512 = 3075704 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1775) (lo := 512) (len := 512) (W := 3075704) check rows elimOK (by decide) (by decide) cover1775 (by decide)
  decide +kernel

theorem h1775 : P.leaf 34 1775 = 3133624 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(448, 0), (64, 57920), (512, 3075704)]) (.cons c1775_0 (.cons c1775_1 (.cons c1775_2 (.nil)))) (by decide) (by decide))

theorem cover1779 : P.CoversSplit 24 10 1779 0xff00ff00a00000000000000000000000ff00ff00a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [475, 573, 860, 921, 1202, 1210, 1259, 1308]) (by decide +kernel)

theorem c1779_0 : P.sumLeaves 24 1821696 448 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1779) (lo := 0) (len := 448) (W := 0) check rows elimOK (by decide) (by decide) cover1779 (by decide)
  decide +kernel

theorem contract1779_1 : P.leaf 30 28471 = 15128 := by
  exact leaf_contract_factors (k := 30) (b := 16) (H := 28471) (ss := [(6, 1, 478), (12, 1, 478), (27, 1, 573), (8, 1, 580), (18, 1, 580), (11, 1, 818), (29, 1, 921), (13, 1, 922), (14, 1, 923), (19, 1, 929), (15, 1, 930), (16, 1, 1265), (20, 1, 1657), (21, 1, 1658)]) (ids := [0, 1, 2, 3, 5, 7, 8, 15, 20, 22, 24, 26, 28, 29, 21, 23]) (cs := [2, 3, 4, 5, 1, 6, 1, 7, 8, 1, 1, 1, 1, 1, 1, 9, 1, 1, 1, 1, 10, 16, 11, 17, 12, 1, 13, 1, 14, 15]) (bs := [14, 2]) (W := 15128) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1779_1 : P.sumLeaves 24 1822144 64 = 15128 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 28471) rows (by decide) (by decide)).symm.trans contract1779_1

theorem c1779_2 : P.sumLeaves 24 1822208 512 = 630280 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1779) (lo := 512) (len := 512) (W := 630280) check rows elimOK (by decide) (by decide) cover1779 (by decide)
  decide +kernel

theorem h1779 : P.leaf 34 1779 = 645408 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(448, 0), (64, 15128), (512, 630280)]) (.cons c1779_0 (.cons c1779_1 (.cons c1779_2 (.nil)))) (by decide) (by decide))

theorem cover1780 : P.CoversSplit 24 10 1780 0xfc00fc00000000000000000000000000f400f400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 475, 508, 573, 860, 872, 915, 916, 1259, 1264]) (by decide +kernel)

theorem c1780_0 : P.sumLeaves 24 1822720 1024 = 210400 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1780) (lo := 0) (len := 1024) (W := 210400) check rows elimOK (by decide) (by decide) cover1780 (by decide)
  decide +kernel

theorem h1780 : P.leaf 34 1780 = 210400 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 210400)]) (.cons c1780_0 (.nil)) (by decide) (by decide))

theorem cover1781 : P.CoversSplit 24 10 1781 0xff00ff00000000000000000000000000ff00ff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 475, 573, 860, 872, 915, 916, 1259, 1264]) (by decide +kernel)

theorem c1781_0 : P.sumLeaves 24 1823744 1024 = 1491880 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1781) (lo := 0) (len := 1024) (W := 1491880) check rows elimOK (by decide) (by decide) cover1781 (by decide)
  decide +kernel

theorem h1781 : P.leaf 34 1781 = 1491880 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1491880)]) (.cons c1781_0 (.nil)) (by decide) (by decide))

theorem cover1782 : P.CoversSplit 24 10 1782 0xff00ff00aa0000000000000000000000f500f5000500000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00880000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 475, 573, 860, 915, 916, 921, 1202, 1210, 1217, 1259, 1308]) (by decide +kernel)

theorem c1782_0 : P.sumLeaves 24 1824768 1024 = 1634200 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1782) (lo := 0) (len := 1024) (W := 1634200) check rows elimOK (by decide) (by decide) cover1782 (by decide)
  decide +kernel

theorem h1782 : P.leaf 34 1782 = 1634200 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1634200)]) (.cons c1782_0 (.nil)) (by decide) (by decide))

theorem cover1783 : P.CoversSplit 24 10 1783 0xff00ff00aa0000000000000000000000ff00ff00aa00000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00880000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [475, 573, 860, 915, 916, 921, 1202, 1210, 1259, 1308]) (by decide +kernel)

theorem c1783_0 : P.sumLeaves 24 1825792 1024 = 5587628 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1783) (lo := 0) (len := 1024) (W := 5587628) check rows elimOK (by decide) (by decide) cover1783 (by decide)
  decide +kernel

theorem h1783 : P.leaf 34 1783 = 5587628 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 5587628)]) (.cons c1783_0 (.nil)) (by decide) (by decide))

theorem cover1784 : P.CoversSplit 24 10 1784 0xfc00fc00000000000000000000000000f000f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 508, 573, 860, 872, 915, 1258, 1259, 1264, 1308]) (ps := [(14, [487, 923], [487, 860])]) (by decide +kernel)

theorem c1784_0 : P.sumLeaves 24 1826816 832 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1784) (lo := 0) (len := 832) (W := 0) check rows elimOK (by decide) (by decide) cover1784 (by decide)
  decide +kernel

theorem contract1784_1 : P.leaf 30 28557 = 28672 := by
  exact leaf_contract_factors (k := 30) (b := 17) (H := 28557) (ss := [(18, 1, 475), (14, 1, 487), (2, 1, 486), (15, 1, 558), (12, 1, 867), (6, 1, 459), (11, 1, 459), (4, 1, 410), (31, 1, 872), (28, 1, 860), (16, 1, 874), (29, 1, 915), (17, 1, 1266)]) (ids := [1, 3, 5, 6, 7, 8, 11, 17, 18, 19, 20, 21, 22, 24, 25, 28, 23]) (cs := [1, 2, 1, 3, 1, 4, 5, 6, 7, 1, 1, 8, 1, 1, 1, 1, 1, 9, 10, 11, 12, 13, 14, 18, 15, 16, 1, 1, 17, 1]) (bs := [16, 1]) (W := 28672) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1784_1 : P.sumLeaves 24 1827648 64 = 28672 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 28557) rows (by decide) (by decide)).symm.trans contract1784_1

theorem c1784_2 : P.sumLeaves 24 1827712 128 = 133904 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1784) (lo := 896) (len := 128) (W := 133904) check rows elimOK (by decide) (by decide) cover1784 (by decide)
  decide +kernel

theorem h1784 : P.leaf 34 1784 = 162576 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(832, 0), (64, 28672), (128, 133904)]) (.cons c1784_0 (.cons c1784_1 (.cons c1784_2 (.nil)))) (by decide) (by decide))

theorem cover1785 : P.CoversSplit 24 10 1785 0xff00ff00000000000000000000000000ff00ff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 573, 860, 872, 915, 1258, 1259, 1264, 1308]) (ps := [(14, [923], [487])]) (by decide +kernel)

theorem c1785_0 : P.sumLeaves 24 1827840 1024 = 1069824 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1785) (lo := 0) (len := 1024) (W := 1069824) check rows elimOK (by decide) (by decide) cover1785 (by decide)
  decide +kernel

theorem h1785 : P.leaf 34 1785 = 1069824 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1069824)]) (.cons c1785_0 (.nil)) (by decide) (by decide))

theorem cover1786 : P.CoversSplit 24 10 1786 0xff00ff00a00000000000000000000000f000f0000f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 573, 860, 872, 921, 1202, 1210, 1217, 1259, 1308]) (ps := [(12, [867], [860]), (14, [874], [860])]) (by decide +kernel)

theorem c1786_0 : P.sumLeaves 24 1828864 448 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1786) (lo := 0) (len := 448) (W := 0) check rows elimOK (by decide) (by decide) cover1786 (by decide)
  decide +kernel

theorem contract1786_1 : P.leaf 30 28583 = 24544 := by
  exact leaf_contract_factors (k := 30) (b := 17) (H := 28583) (ss := [(27, 1, 573), (8, 1, 580), (18, 1, 580), (12, 1, 867), (11, 1, 818), (29, 1, 921), (13, 1, 922), (14, 1, 923), (19, 1, 965), (15, 1, 930), (16, 1, 1265), (20, 1, 1657), (21, 1, 1658)]) (ids := [0, 1, 2, 3, 4, 5, 7, 8, 15, 20, 22, 24, 26, 28, 29, 21, 23]) (cs := [2, 3, 4, 5, 6, 7, 1, 8, 9, 1, 1, 1, 1, 1, 1, 10, 1, 1, 1, 1, 11, 17, 12, 18, 13, 1, 14, 1, 15, 16]) (bs := [15, 2]) (W := 24544) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1786_1 : P.sumLeaves 24 1829312 64 = 24544 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 28583) rows (by decide) (by decide)).symm.trans contract1786_1

theorem c1786_2 : P.sumLeaves 24 1829376 512 = 895272 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1786) (lo := 512) (len := 512) (W := 895272) check rows elimOK (by decide) (by decide) cover1786 (by decide)
  decide +kernel

theorem h1786 : P.leaf 34 1786 = 919816 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(448, 0), (64, 24544), (512, 895272)]) (.cons c1786_0 (.cons c1786_1 (.cons c1786_2 (.nil)))) (by decide) (by decide))

theorem cover1787 : P.CoversSplit 24 10 1787 0xff00ff00a00000000000000000000000ff00ff00a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [573, 860, 915, 921, 1202, 1210, 1259, 1308]) (by decide +kernel)

theorem c1787_0 : P.sumLeaves 24 1829888 448 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1787) (lo := 0) (len := 448) (W := 0) check rows elimOK (by decide) (by decide) cover1787 (by decide)
  decide +kernel

theorem contract1787_1 : P.leaf 30 28599 = 34368 := by
  exact leaf_contract_factors (k := 30) (b := 17) (H := 28599) (ss := [(27, 1, 573), (8, 1, 580), (18, 1, 580), (12, 1, 867), (11, 1, 818), (29, 1, 921), (13, 1, 922), (14, 1, 923), (19, 1, 965), (15, 1, 930), (16, 1, 1265), (20, 1, 1657), (21, 1, 1658)]) (ids := [0, 1, 2, 3, 4, 5, 7, 8, 15, 20, 22, 24, 26, 28, 29, 21, 23]) (cs := [2, 3, 4, 5, 6, 7, 1, 8, 9, 1, 1, 1, 1, 1, 1, 10, 1, 1, 1, 1, 11, 17, 12, 18, 13, 1, 14, 1, 15, 16]) (bs := [15, 2]) (W := 34368) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1787_1 : P.sumLeaves 24 1830336 64 = 34368 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 28599) rows (by decide) (by decide)).symm.trans contract1787_1

theorem c1787_2 : P.sumLeaves 24 1830400 512 = 1893504 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1787) (lo := 512) (len := 512) (W := 1893504) check rows elimOK (by decide) (by decide) cover1787 (by decide)
  decide +kernel

theorem h1787 : P.leaf 34 1787 = 1927872 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(448, 0), (64, 34368), (512, 1893504)]) (.cons c1787_0 (.cons c1787_1 (.cons c1787_2 (.nil)))) (by decide) (by decide))

theorem cover1788 : P.CoversSplit 24 10 1788 0xfc00fc00000000000000000000000000f400f4000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 508, 573, 860, 867, 872, 915, 1258, 1259, 1264, 1308]) (by decide +kernel)

theorem c1788_0 : P.sumLeaves 24 1830912 448 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1788) (lo := 0) (len := 448) (W := 0) check rows elimOK (by decide) (by decide) cover1788 (by decide)
  decide +kernel

theorem contract1788_1 : P.leaf 30 28615 = 18496 := by
  exact leaf_contract_factors (k := 30) (b := 17) (H := 28615) (ss := [(18, 1, 475), (27, 1, 573), (8, 1, 580), (31, 1, 872), (11, 1, 901), (6, 1, 459), (12, 1, 818), (29, 1, 915), (13, 1, 922), (14, 1, 923), (16, 1, 1265), (20, 1, 1657), (21, 1, 1658)]) (ids := [0, 1, 2, 3, 7, 8, 13, 15, 17, 20, 22, 24, 26, 28, 5, 21, 23]) (cs := [2, 3, 4, 5, 1, 16, 1, 6, 7, 1, 1, 1, 1, 8, 1, 9, 1, 10, 1, 1, 11, 17, 12, 18, 13, 1, 14, 1, 15, 1]) (bs := [14, 3]) (W := 18496) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1788_1 : P.sumLeaves 24 1831360 64 = 18496 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 28615) rows (by decide) (by decide)).symm.trans contract1788_1

theorem c1788_2 : P.sumLeaves 24 1831424 512 = 855912 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1788) (lo := 512) (len := 512) (W := 855912) check rows elimOK (by decide) (by decide) cover1788 (by decide)
  decide +kernel

theorem h1788 : P.leaf 34 1788 = 874408 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(448, 0), (64, 18496), (512, 855912)]) (.cons c1788_0 (.cons c1788_1 (.cons c1788_2 (.nil)))) (by decide) (by decide))

theorem cover1789 : P.CoversSplit 24 10 1789 0xff00ff00000000000000000000000000ff00ff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 573, 860, 867, 872, 915, 1258, 1259, 1264, 1308]) (by decide +kernel)

theorem c1789_0 : P.sumLeaves 24 1831936 448 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1789) (lo := 0) (len := 448) (W := 0) check rows elimOK (by decide) (by decide) cover1789 (by decide)
  decide +kernel

theorem contract1789_1 : P.leaf 30 28631 = 47616 := by
  exact leaf_contract_factors (k := 30) (b := 18) (H := 28631) (ss := [(18, 1, 475), (27, 1, 573), (8, 1, 580), (31, 1, 872), (11, 1, 901), (12, 1, 818), (29, 1, 915), (13, 1, 922), (14, 1, 923), (16, 1, 1265), (20, 1, 1657), (21, 1, 1658)]) (ids := [0, 1, 2, 3, 4, 7, 8, 13, 15, 17, 20, 22, 24, 26, 28, 5, 21, 23]) (cs := [2, 3, 4, 5, 6, 17, 1, 7, 8, 1, 1, 1, 1, 9, 1, 10, 1, 11, 1, 1, 12, 18, 13, 19, 14, 1, 15, 1, 16, 1]) (bs := [15, 3]) (W := 47616) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1789_1 : P.sumLeaves 24 1832384 64 = 47616 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 28631) rows (by decide) (by decide)).symm.trans contract1789_1

theorem c1789_2 : P.sumLeaves 24 1832448 512 = 3104728 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1789) (lo := 512) (len := 512) (W := 3104728) check rows elimOK (by decide) (by decide) cover1789 (by decide)
  decide +kernel

theorem h1789 : P.leaf 34 1789 = 3152344 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(448, 0), (64, 47616), (512, 3104728)]) (.cons c1789_0 (.cons c1789_1 (.cons c1789_2 (.nil)))) (by decide) (by decide))

theorem cover1790 : P.CoversSplit 24 10 1790 0xff00ff00aa0000000000000000000000f500f5000500000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00880000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 573, 860, 867, 916, 921, 1202, 1210, 1217, 1259, 1308]) (by decide +kernel)

theorem c1790_0 : P.sumLeaves 24 1832960 1024 = 5682202 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1790) (lo := 0) (len := 1024) (W := 5682202) check rows elimOK (by decide) (by decide) cover1790 (by decide)
  decide +kernel

theorem h1790 : P.leaf 34 1790 = 5682202 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 5682202)]) (.cons c1790_0 (.nil)) (by decide) (by decide))

theorem cover1791 : P.CoversSplit 24 10 1791 0xff00ff00aa0000000000000000000000ff00ff00aa00000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00880000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [573, 860, 867, 916, 921, 1202, 1210, 1259, 1308]) (by decide +kernel)

theorem c1791_0 : P.sumLeaves 24 1833984 1024 = 11970716 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1791) (lo := 0) (len := 1024) (W := 11970716) check rows elimOK (by decide) (by decide) cover1791 (by decide)
  decide +kernel

theorem h1791 : P.leaf 34 1791 = 11970716 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 11970716)]) (.cons c1791_0 (.nil)) (by decide) (by decide))

theorem cover1921 : P.CoversSplit 24 10 1921 0x8800000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000088000000000000000000000000000000880000000000000000aa0000000000000000000000000000000000000000000000000000000000000088000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [468, 473, 517, 522, 528, 565, 915, 1209, 1609]) (ps := [(14, [874], [558, 860])]) (by decide +kernel)

theorem c1921_0 : P.sumLeaves 24 1967104 256 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1921) (lo := 0) (len := 256) (W := 0) check rows elimOK (by decide) (by decide) cover1921 (by decide)
  decide +kernel

theorem contract1921_1 : P.leaf 30 30740 = 82 := by
  exact leaf_contract_factors (k := 30) (b := 12) (H := 30740) (ss := [(31, 1, 468), (29, 2, 474), (6, 1, 478), (12, 1, 478), (2, 0, 522), (3, 0, 410), (13, 0, 480), (14, 0, 480), (16, 0, 481), (15, 0, 487), (17, 0, 489), (26, 1, 528), (11, 1, 818), (8, 0, 874), (5, 1, 433), (21, 0, 874), (20, 1, 433), (30, 1, 1209)]) (ids := [2, 5, 7, 16, 17, 20, 23, 25, 8, 21, 22, 26]) (cs := [0, 0, 2, 1, 1, 3, 0, 4, 10, 1, 1, 0, 0, 0, 0, 0, 5, 6, 1, 0, 7, 11, 12, 8, 1, 9, 13, 0, 1, 1]) (bs := [8, 4]) (W := 82) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1921_1 : P.sumLeaves 24 1967360 64 = 82 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 30740) rows (by decide) (by decide)).symm.trans contract1921_1

theorem c1921_2 : P.sumLeaves 24 1967424 704 = 6368 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1921) (lo := 320) (len := 704) (W := 6368) check rows elimOK (by decide) (by decide) cover1921 (by decide)
  decide +kernel

theorem h1921 : P.leaf 34 1921 = 6450 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(256, 0), (64, 82), (704, 6368)]) (.cons c1921_0 (.cons c1921_1 (.cons c1921_2 (.nil)))) (by decide) (by decide))

theorem cover1923 : P.CoversSplit 24 10 1923 0xaaaa0000000000000000000000000000a0a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000aaaa0000000000000000000000000000aaaa00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [468, 517, 522, 528, 565, 916, 1209, 1258]) (ps := [(14, [874], [860])]) (by decide +kernel)

theorem c1923_0 : P.sumLeaves 24 1969152 320 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1923) (lo := 0) (len := 320) (W := 0) check rows elimOK (by decide) (by decide) cover1923 (by decide)
  decide +kernel

theorem contract1923_1 : P.leaf 30 30773 = 280 := by
  apply (leaf_contract (k := 30) (b := 13) (H := 30773) (ss := [(31, 1, 468), (6, 1, 478), (12, 1, 478), (3, 1, 523), (5, 1, 418), (26, 1, 528), (16, 1, 529), (7, 1, 530), (11, 1, 818), (13, 1, 922), (18, 1, 922), (30, 1, 1209), (14, 0, 1266), (10, 1, 811), (8, 0, 874), (20, 1, 628), (21, 0, 874)]) (ids := [0, 2, 7, 13, 15, 17, 20, 21, 22, 23, 25, 26, 27]) (cs := [2, 1, 3, 1, 1, 1, 0, 4, 1, 1, 1, 1, 0, 5, 1, 6, 1, 7, 1, 0, 8, 9, 10, 11, 1, 12, 13, 14, 1, 1]) check rows (by decide) (by decide +kernel) (by decide +kernel)).trans
  decide +kernel

theorem c1923_1 : P.sumLeaves 24 1969472 64 = 280 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 30773) rows (by decide) (by decide)).symm.trans contract1923_1

theorem c1923_2 : P.sumLeaves 24 1969536 64 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1923) (lo := 384) (len := 64) (W := 0) check rows elimOK (by decide) (by decide) cover1923 (by decide)
  decide +kernel

theorem contract1923_3 : P.leaf 30 30775 = 18176 := by
  exact leaf_contract_factors (k := 30) (b := 15) (H := 30775) (ss := [(31, 1, 468), (6, 1, 478), (12, 1, 478), (3, 1, 523), (5, 1, 418), (26, 1, 528), (11, 1, 818), (14, 1, 923), (18, 1, 923), (19, 1, 929), (30, 1, 1209), (16, 1, 1265), (13, 1, 922), (17, 1, 1273), (15, 1, 930)]) (ids := [2, 5, 6, 7, 8, 18, 19, 20, 21, 22, 23, 25, 26, 0, 27]) (cs := [15, 1, 2, 1, 1, 3, 4, 5, 6, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7, 8, 9, 10, 11, 12, 1, 13, 14, 16, 1, 1]) (bs := [13, 2]) (W := 18176) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1923_3 : P.sumLeaves 24 1969600 64 = 18176 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 30775) rows (by decide) (by decide)).symm.trans contract1923_3

theorem c1923_4 : P.sumLeaves 24 1969664 320 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1923) (lo := 512) (len := 320) (W := 0) check rows elimOK (by decide) (by decide) cover1923 (by decide)
  decide +kernel

theorem contract1923_5 : P.leaf 30 30781 = 1536 := by
  exact leaf_contract_factors (k := 30) (b := 11) (H := 30781) (ss := [(31, 1, 468), (6, 1, 478), (12, 1, 478), (3, 1, 523), (5, 1, 418), (26, 1, 528), (16, 1, 529), (7, 1, 530), (11, 1, 818), (14, 1, 874), (8, 1, 531), (17, 1, 537), (9, 1, 538), (28, 1, 860), (30, 1, 1209), (18, 1, 1265), (19, 1, 1273), (20, 1, 1314), (21, 1, 1315)]) (ids := [8, 13, 0, 2, 11, 20, 21, 22, 23, 25, 27]) (cs := [4, 1, 5, 1, 1, 1, 1, 1, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 1, 1, 7, 8, 9, 10, 1, 11, 1, 12, 1, 1]) (bs := [2, 9]) (W := 1536) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1923_5 : P.sumLeaves 24 1969984 64 = 1536 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 30781) rows (by decide) (by decide)).symm.trans contract1923_5

theorem c1923_6 : P.sumLeaves 24 1970048 128 = 81920 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1923) (lo := 896) (len := 128) (W := 81920) check rows elimOK (by decide) (by decide) cover1923 (by decide)
  decide +kernel

theorem h1923 : P.leaf 34 1923 = 101912 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(320, 0), (64, 280), (64, 0), (64, 18176), (320, 0), (64, 1536), (128, 81920)]) (.cons c1923_0 (.cons c1923_1 (.cons c1923_2 (.cons c1923_3 (.cons c1923_4 (.cons c1923_5 (.cons c1923_6 (.nil)))))))) (by decide) (by decide))

theorem h1924 : P.leaf 34 1924 = 3584 := by
  exact leaf_contract_factors (k := 34) (b := 16) (H := 1924) (ss := [(6, 1, 466), (33, 1, 468), (26, 1, 472), (16, 3, 486), (3, 1, 509), (10, 1, 458), (32, 1, 524), (27, 1, 522), (11, 1, 818), (12, 1, 818), (31, 1, 909), (5, 1, 418), (2, 1, 409), (4, 1, 417), (28, 1, 465), (29, 1, 473), (30, 1, 515), (34, 1, 915)]) (ids := [5, 6, 7, 11, 12, 13, 15, 16, 17, 18, 19, 22, 33, 20, 21, 23]) (cs := [1, 1, 1, 1, 1, 2, 3, 4, 1, 1, 1, 5, 6, 7, 1, 8, 9, 10, 11, 12, 15, 16, 13, 17, 1, 1, 1, 1, 1, 1, 1, 1, 1, 14]) (bs := [13, 3]) (W := 3584) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem cover1925 : P.CoversSplit 24 10 1925 0x8800000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000088000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [468, 473, 475, 515, 517, 522, 528, 566, 860, 915, 916, 1209, 1609]) (ps := [(14, [923], [1266])]) (by decide +kernel)

theorem c1925_0 : P.sumLeaves 24 1971200 1024 = 28112 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1925) (lo := 0) (len := 1024) (W := 28112) check rows elimOK (by decide) (by decide) cover1925 (by decide)
  decide +kernel

theorem h1925 : P.leaf 34 1925 = 28112 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 28112)]) (.cons c1925_0 (.nil)) (by decide) (by decide))

theorem h1926 : P.leaf 34 1926 = 58336 := by
  exact leaf_contract_factors (k := 34) (b := 21) (H := 1926) (ss := [(33, 1, 468), (26, 1, 479), (16, 3, 486), (3, 1, 509), (32, 1, 524), (31, 12, 909), (12, 1, 1209), (5, 1, 418), (2, 1, 409), (4, 1, 417), (28, 1, 465), (30, 1, 515), (34, 1, 1258)]) (ids := [4, 5, 6, 7, 8, 9, 11, 12, 13, 15, 16, 17, 18, 19, 21, 22, 23, 25, 27, 33, 20]) (cs := [1, 1, 1, 1, 2, 3, 4, 5, 6, 7, 1, 8, 9, 10, 1, 11, 12, 13, 14, 15, 22, 16, 17, 18, 1, 19, 1, 20, 1, 1, 1, 1, 1, 21]) (bs := [20, 1]) (W := 58336) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem cover1927 : P.CoversSplit 24 10 1927 0xaaaa0000000000000000000000000000a0a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000aaaa0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [468, 515, 517, 522, 528, 566, 860, 915, 916, 1209, 1258, 1259]) (ps := [(3, [502], [524]), (14, [965], [1266])]) (by decide +kernel)

theorem c1927_0 : P.sumLeaves 24 1973248 448 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1927) (lo := 0) (len := 448) (W := 0) check rows elimOK (by decide) (by decide) cover1927 (by decide)
  decide +kernel

theorem contract1927_1 : P.leaf 30 30839 = 73040 := by
  apply (leaf_contract (k := 30) (b := 18) (H := 30839) (ss := [(3, 1, 502), (5, 1, 502), (26, 1, 528), (31, 1, 517), (12, 1, 867), (14, 1, 929), (19, 1, 929), (18, 1, 965), (30, 1, 1209), (16, 1, 1265), (13, 1, 922), (17, 1, 1273)]) (ids := [0, 2, 4, 5, 6, 7, 8, 9, 13, 18, 19, 20, 21, 22, 23, 25, 26, 27]) (cs := [2, 1, 3, 1, 4, 5, 6, 7, 8, 9, 1, 1, 1, 10, 1, 1, 1, 1, 11, 12, 13, 14, 15, 16, 1, 17, 18, 19, 1, 1]) check rows (by decide) (by decide +kernel) (by decide +kernel)).trans
  decide +kernel

theorem c1927_1 : P.sumLeaves 24 1973696 64 = 73040 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 30839) rows (by decide) (by decide)).symm.trans contract1927_1

theorem c1927_2 : P.sumLeaves 24 1973760 320 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1927) (lo := 512) (len := 320) (W := 0) check rows elimOK (by decide) (by decide) cover1927 (by decide)
  decide +kernel

theorem contract1927_3 : P.leaf 30 30845 = 4880 := by
  exact leaf_contract_factors (k := 30) (b := 13) (H := 30845) (ss := [(31, 1, 468), (3, 1, 502), (5, 1, 419), (26, 1, 528), (16, 1, 529), (7, 1, 530), (28, 1, 860), (12, 1, 867), (14, 1, 874), (8, 1, 531), (17, 1, 615), (9, 1, 538), (30, 1, 1209), (18, 1, 1265), (19, 1, 1273), (20, 1, 1314), (21, 1, 1315)]) (ids := [0, 2, 4, 8, 9, 13, 21, 25, 27, 11, 20, 22, 23]) (cs := [2, 1, 3, 1, 4, 1, 1, 1, 5, 6, 1, 11, 1, 7, 1, 1, 1, 1, 1, 1, 12, 8, 13, 14, 1, 9, 1, 10, 1, 1]) (bs := [9, 4]) (W := 4880) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1927_3 : P.sumLeaves 24 1974080 64 = 4880 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 30845) rows (by decide) (by decide)).symm.trans contract1927_3

theorem c1927_4 : P.sumLeaves 24 1974144 128 = 432352 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1927) (lo := 896) (len := 128) (W := 432352) check rows elimOK (by decide) (by decide) cover1927 (by decide)
  decide +kernel

theorem h1927 : P.leaf 34 1927 = 510272 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(448, 0), (64, 73040), (320, 0), (64, 4880), (128, 432352)]) (.cons c1927_0 (.cons c1927_1 (.cons c1927_2 (.cons c1927_3 (.cons c1927_4 (.nil)))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(1763, 48), (1764, 48), (1765, 48), (1766, 48), (1767, 48), (1768, 48), (1769, 48), (1770, 48), (1771, 48), (1772, 48), (1773, 48), (1774, 48), (1775, 48), (1779, 24), (1780, 48), (1781, 48), (1782, 48), (1783, 48), (1784, 48), (1785, 48), (1786, 48), (1787, 48), (1788, 48), (1789, 48), (1790, 48), (1791, 48), (1921, 12), (1923, 24), (1924, 48), (1925, 48), (1926, 48), (1927, 48)]

theorem segOK : checkSeg 16 perms 1763 1928 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 1763 1928 1452 2103666552 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 2103666552)
    (SegSum.cons (w := 48) h1763 (SegSum.cons (w := 48) h1764 (SegSum.cons (w := 48) h1765 (SegSum.cons (w := 48) h1766 (SegSum.cons (w := 48) h1767 (SegSum.cons (w := 48) h1768 (SegSum.cons (w := 48) h1769 (SegSum.cons (w := 48) h1770 (SegSum.cons (w := 48) h1771 (SegSum.cons (w := 48) h1772 (SegSum.cons (w := 48) h1773 (SegSum.cons (w := 48) h1774 (SegSum.cons (w := 48) h1775 (SegSum.cons (w := 24) h1779 (SegSum.cons (w := 48) h1780 (SegSum.cons (w := 48) h1781 (SegSum.cons (w := 48) h1782 (SegSum.cons (w := 48) h1783 (SegSum.cons (w := 48) h1784 (SegSum.cons (w := 48) h1785 (SegSum.cons (w := 48) h1786 (SegSum.cons (w := 48) h1787 (SegSum.cons (w := 48) h1788 (SegSum.cons (w := 48) h1789 (SegSum.cons (w := 48) h1790 (SegSum.cons (w := 48) h1791 (SegSum.cons (w := 12) h1921 (SegSum.cons (w := 24) h1923 (SegSum.cons (w := 48) h1924 (SegSum.cons (w := 48) h1925 (SegSum.cons (w := 48) h1926 (SegSum.cons (w := 48) h1927 (show SegSum (P.leaf 34) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S4N1.C0.S14
