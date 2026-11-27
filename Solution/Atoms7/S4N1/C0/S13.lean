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

namespace RACert.S4N1.C0.S13

open RACert RACert.Problem

theorem cover1724 : P.CoversSplit 24 10 1724 0xfc000000000000000000000000000000a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 508, 517, 524, 566, 573, 860, 872, 915, 1209, 1251, 1258, 1259, 1264, 1308]) (ps := [(8, [531], [517])]) (by decide +kernel)

theorem c1724_0 : P.sumLeaves 24 1765376 448 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1724) (lo := 0) (len := 448) (W := 0) check rows elimOK (by decide) (by decide) cover1724 (by decide)
  decide +kernel

theorem contract1724_1 : P.leaf 30 27591 = 5088 := by
  exact leaf_contract_factors (k := 30) (b := 15) (H := 27591) (ss := [(18, 11, 475), (11, 1, 559), (8, 1, 580), (27, 1, 573), (6, 1, 459), (12, 1, 818), (31, 1, 872), (29, 1, 915), (13, 1, 922), (14, 1, 923), (30, 1, 1251), (16, 1, 1265), (19, 1, 1272), (20, 1, 1657), (21, 1, 1658)]) (ids := [0, 1, 2, 3, 7, 8, 13, 15, 20, 24, 26, 5, 21, 22, 23]) (cs := [2, 3, 4, 5, 1, 13, 1, 6, 7, 1, 1, 1, 1, 8, 1, 9, 1, 1, 1, 1, 10, 14, 15, 16, 11, 1, 12, 1, 1, 1]) (bs := [11, 4]) (W := 5088) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1724_1 : P.sumLeaves 24 1765824 64 = 5088 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 27591) rows (by decide) (by decide)).symm.trans contract1724_1

theorem c1724_2 : P.sumLeaves 24 1765888 512 = 109728 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1724) (lo := 512) (len := 512) (W := 109728) check rows elimOK (by decide) (by decide) cover1724 (by decide)
  decide +kernel

theorem h1724 : P.leaf 34 1724 = 114816 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(448, 0), (64, 5088), (512, 109728)]) (.cons c1724_0 (.cons c1724_1 (.cons c1724_2 (.nil)))) (by decide) (by decide))

theorem cover1725 : P.CoversSplit 24 10 1725 0xff000000000000000000000000000000a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 517, 524, 566, 573, 860, 872, 915, 1209, 1251, 1258, 1259, 1264, 1308]) (ps := [(8, [531], [517])]) (by decide +kernel)

theorem c1725_0 : P.sumLeaves 24 1766400 448 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1725) (lo := 0) (len := 448) (W := 0) check rows elimOK (by decide) (by decide) cover1725 (by decide)
  decide +kernel

theorem contract1725_1 : P.leaf 30 27607 = 21504 := by
  exact leaf_contract_factors (k := 30) (b := 16) (H := 27607) (ss := [(18, 11, 475), (11, 1, 559), (8, 1, 580), (27, 1, 573), (12, 1, 818), (31, 1, 872), (29, 1, 915), (13, 1, 922), (14, 1, 923), (30, 1, 1251), (16, 1, 1265), (19, 1, 1272), (20, 1, 1657), (21, 1, 1658)]) (ids := [0, 1, 2, 3, 7, 8, 13, 20, 26, 4, 5, 15, 21, 22, 23, 24]) (cs := [2, 3, 4, 5, 11, 12, 1, 6, 7, 1, 1, 1, 1, 8, 1, 13, 1, 1, 1, 1, 9, 14, 15, 16, 17, 1, 10, 1, 1, 1]) (bs := [9, 7]) (W := 21504) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1725_1 : P.sumLeaves 24 1766848 64 = 21504 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 27607) rows (by decide) (by decide)).symm.trans contract1725_1

theorem c1725_2 : P.sumLeaves 24 1766912 512 = 661120 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1725) (lo := 512) (len := 512) (W := 661120) check rows elimOK (by decide) (by decide) cover1725 (by decide)
  decide +kernel

theorem h1725 : P.leaf 34 1725 = 682624 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(448, 0), (64, 21504), (512, 661120)]) (.cons c1725_0 (.cons c1725_1 (.cons c1725_2 (.nil)))) (by decide) (by decide))

theorem cover1726 : P.CoversSplit 24 10 1726 0xff000000000000000000000000000000a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 517, 524, 566, 573, 860, 872, 916, 921, 1209, 1251, 1259, 1308]) (ps := [(8, [531], [517])]) (by decide +kernel)

theorem c1726_0 : P.sumLeaves 24 1767424 448 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1726) (lo := 0) (len := 448) (W := 0) check rows elimOK (by decide) (by decide) cover1726 (by decide)
  decide +kernel

theorem contract1726_1 : P.leaf 30 27623 = 27600 := by
  exact leaf_contract_factors (k := 30) (b := 18) (H := 27623) (ss := [(8, 1, 580), (27, 1, 573), (18, 1, 580), (31, 1, 872), (29, 1, 916), (13, 1, 922), (14, 1, 923), (30, 1, 1251), (16, 1, 1265), (19, 1, 1272), (20, 1, 1657), (21, 1, 1658)]) (ids := [0, 1, 2, 3, 4, 5, 7, 8, 9, 10, 13, 15, 20, 21, 24, 26, 22, 23]) (cs := [2, 3, 4, 5, 6, 7, 1, 8, 9, 10, 11, 1, 1, 12, 1, 13, 1, 1, 1, 1, 14, 15, 18, 19, 16, 1, 17, 1, 1, 1]) (bs := [16, 2]) (W := 27600) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1726_1 : P.sumLeaves 24 1767872 64 = 27600 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 27623) rows (by decide) (by decide)).symm.trans contract1726_1

theorem c1726_2 : P.sumLeaves 24 1767936 512 = 770560 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1726) (lo := 512) (len := 512) (W := 770560) check rows elimOK (by decide) (by decide) cover1726 (by decide)
  decide +kernel

theorem h1726 : P.leaf 34 1726 = 798160 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(448, 0), (64, 27600), (512, 770560)]) (.cons c1726_0 (.cons c1726_1 (.cons c1726_2 (.nil)))) (by decide) (by decide))

theorem cover1727 : P.CoversSplit 24 10 1727 0xff000000000000000000000000000000a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [517, 524, 566, 573, 860, 872, 916, 921, 1209, 1251, 1259, 1308]) (ps := [(8, [531], [517])]) (by decide +kernel)

theorem c1727_0 : P.sumLeaves 24 1768448 448 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1727) (lo := 0) (len := 448) (W := 0) check rows elimOK (by decide) (by decide) cover1727 (by decide)
  decide +kernel

theorem contract1727_1 : P.leaf 30 27639 = 62816 := by
  exact leaf_contract_factors (k := 30) (b := 18) (H := 27639) (ss := [(8, 1, 580), (27, 1, 573), (18, 1, 580), (31, 1, 872), (29, 1, 916), (13, 1, 922), (14, 1, 923), (30, 1, 1251), (16, 1, 1265), (19, 1, 1272), (20, 1, 1657), (21, 1, 1658)]) (ids := [0, 1, 2, 3, 4, 5, 7, 8, 9, 10, 13, 20, 21, 24, 26, 15, 22, 23]) (cs := [2, 3, 4, 5, 6, 7, 1, 8, 9, 10, 11, 1, 1, 12, 1, 17, 1, 1, 1, 1, 13, 14, 18, 19, 15, 1, 16, 1, 1, 1]) (bs := [15, 3]) (W := 62816) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1727_1 : P.sumLeaves 24 1768896 64 = 62816 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 27639) rows (by decide) (by decide)).symm.trans contract1727_1

theorem c1727_2 : P.sumLeaves 24 1768960 512 = 1951760 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1727) (lo := 512) (len := 512) (W := 1951760) check rows elimOK (by decide) (by decide) cover1727 (by decide)
  decide +kernel

theorem h1727 : P.leaf 34 1727 = 2014576 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(448, 0), (64, 62816), (512, 1951760)]) (.cons c1727_0 (.cons c1727_1 (.cons c1727_2 (.nil)))) (by decide) (by decide))

theorem h1730 : P.leaf 34 1730 = 5376 := by
  exact leaf_contract_factors (k := 34) (b := 16) (H := 1730) (ss := [(2, 1, 453), (3, 1, 417), (5, 1, 412), (4, 1, 417), (6, 1, 467), (12, 1, 460), (34, 1, 475), (15, 1, 486), (14, 1, 509), (32, 1, 523), (30, 18, 524), (35, 1, 536), (18, 1, 566), (26, 1, 465), (28, 1, 465), (11, 1, 818), (29, 1, 916), (31, 1, 1209)]) (ids := [5, 6, 7, 8, 11, 14, 15, 17, 18, 19, 21, 23, 25, 31, 20, 22]) (cs := [1, 1, 1, 1, 1, 2, 3, 4, 5, 1, 1, 6, 1, 1, 7, 8, 1, 9, 10, 11, 16, 12, 17, 13, 1, 14, 1, 1, 1, 1, 1, 15, 1, 1]) (bs := [14, 2]) (W := 5376) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem cover1731 : P.CoversSplit 24 10 1731 0xff000000000000000000000000000000ff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [475, 515, 516, 523, 536, 566, 860, 921, 1202, 1209]) (by decide +kernel)

theorem c1731_0 : P.sumLeaves 24 1772544 832 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1731) (lo := 0) (len := 832) (W := 0) check rows elimOK (by decide) (by decide) cover1731 (by decide)
  decide +kernel

theorem contract1731_1 : P.leaf 30 27709 = 12992 := by
  exact leaf_contract_factors (k := 30) (b := 17) (H := 27709) (ss := [(6, 1, 478), (12, 1, 478), (30, 18, 524), (18, 4, 566), (11, 1, 818), (14, 1, 874), (8, 1, 537), (17, 1, 537), (16, 1, 874), (29, 1, 916), (4, 1, 1251), (31, 1, 1209), (19, 1, 1273)]) (ids := [0, 1, 3, 5, 7, 8, 11, 13, 18, 19, 20, 24, 25, 26, 21, 22, 23]) (cs := [2, 3, 1, 4, 1, 5, 1, 6, 7, 1, 1, 8, 1, 9, 1, 1, 1, 1, 10, 11, 12, 16, 17, 18, 13, 14, 15, 1, 1, 1]) (bs := [14, 3]) (W := 12992) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1731_1 : P.sumLeaves 24 1773376 64 = 12992 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 27709) rows (by decide) (by decide)).symm.trans contract1731_1

theorem c1731_2 : P.sumLeaves 24 1773440 128 = 76576 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1731) (lo := 896) (len := 128) (W := 76576) check rows elimOK (by decide) (by decide) cover1731 (by decide)
  decide +kernel

theorem h1731 : P.leaf 34 1731 = 89568 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(832, 0), (64, 12992), (128, 76576)]) (.cons c1731_0 (.cons c1731_1 (.cons c1731_2 (.nil)))) (by decide) (by decide))

theorem h1732 : P.leaf 34 1732 = 2336 := by
  exact leaf_contract_factors (k := 34) (b := 16) (H := 1732) (ss := [(6, 1, 466), (26, 1, 472), (35, 1, 475), (13, 1, 480), (27, 1, 508), (30, 18, 524), (33, 1, 536), (14, 1, 559), (18, 1, 487), (17, 1, 565), (12, 1, 867), (10, 1, 458), (11, 1, 459), (31, 1, 872), (28, 1, 465), (29, 1, 916), (34, 1, 915), (32, 1, 522)]) (ids := [0, 1, 2, 3, 5, 6, 7, 13, 14, 17, 18, 19, 20, 22, 21, 23]) (cs := [2, 3, 4, 5, 1, 6, 7, 8, 1, 1, 1, 1, 1, 9, 10, 1, 1, 11, 12, 13, 14, 16, 15, 17, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) (bs := [14, 2]) (W := 2336) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem cover1733 : P.CoversSplit 24 10 1733 0xcc00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 475, 515, 522, 536, 566, 573, 860, 872, 915, 916]) (by decide +kernel)

theorem c1733_0 : P.sumLeaves 24 1774592 960 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1733) (lo := 0) (len := 960) (W := 0) check rows elimOK (by decide) (by decide) cover1733 (by decide)
  decide +kernel

theorem contract1733_1 : P.leaf 30 27743 = 47904 := by
  exact leaf_contract_factors (k := 30) (b := 20) (H := 27743) (ss := [(27, 1, 473), (29, 1, 473), (13, 1, 480), (30, 18, 524), (14, 1, 559), (18, 1, 487), (17, 1, 565), (12, 1, 867), (11, 1, 818), (31, 1, 872)]) (ids := [0, 1, 2, 3, 4, 5, 6, 7, 8, 13, 14, 17, 18, 19, 20, 22, 24, 26, 21, 23]) (cs := [2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 1, 1, 1, 11, 12, 1, 1, 13, 14, 15, 16, 20, 17, 21, 18, 1, 19, 1, 1, 1]) (bs := [18, 2]) (W := 47904) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1733_1 : P.sumLeaves 24 1775552 64 = 47904 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 27743) rows (by decide) (by decide)).symm.trans contract1733_1

theorem h1733 : P.leaf 34 1733 = 47904 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(960, 0), (64, 47904)]) (.cons c1733_0 (.cons c1733_1 (.nil))) (by decide) (by decide))

theorem cover1734 : P.CoversSplit 24 10 1734 0xa0000000000000000000000000000000a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 475, 515, 516, 522, 536, 566, 860, 915, 916, 921, 1209, 1210, 1258, 1259]) (by decide +kernel)

theorem c1734_0 : P.sumLeaves 24 1775616 1024 = 49568 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1734) (lo := 0) (len := 1024) (W := 49568) check rows elimOK (by decide) (by decide) cover1734 (by decide)
  decide +kernel

theorem h1734 : P.leaf 34 1734 = 49568 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 49568)]) (.cons c1734_0 (.nil)) (by decide) (by decide))

theorem cover1735 : P.CoversSplit 24 10 1735 0xff000000000000000000000000000000ff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [475, 515, 522, 536, 566, 573, 860, 915, 916, 921, 1202, 1209, 1258, 1259]) (by decide +kernel)

theorem c1735_0 : P.sumLeaves 24 1776640 1024 = 938160 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1735) (lo := 0) (len := 1024) (W := 938160) check rows elimOK (by decide) (by decide) cover1735 (by decide)
  decide +kernel

theorem h1735 : P.leaf 34 1735 = 938160 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 938160)]) (.cons c1735_0 (.nil)) (by decide) (by decide))

theorem h1736 : P.leaf 34 1736 = 3824 := by
  exact leaf_contract_factors (k := 34) (b := 17) (H := 1736) (ss := [(6, 1, 466), (26, 1, 472), (18, 1, 475), (35, 14, 487), (27, 1, 508), (14, 1, 509), (29, 1, 474), (32, 1, 523), (33, 1, 536), (15, 1, 486), (17, 1, 565), (12, 1, 803), (11, 1, 459), (31, 1, 872), (28, 1, 465), (30, 1, 515), (34, 1, 915)]) (ids := [0, 1, 2, 3, 5, 6, 7, 8, 11, 14, 17, 18, 19, 20, 21, 23, 22]) (cs := [2, 3, 4, 5, 1, 6, 7, 8, 9, 1, 1, 10, 1, 1, 11, 1, 1, 12, 13, 14, 15, 16, 18, 17, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]) (bs := [16, 1]) (W := 3824) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem h1737 : P.leaf 34 1737 = 30768 := by
  apply (leaf_contract (k := 34) (b := 20) (H := 1737) (ss := [(18, 1, 475), (35, 14, 487), (33, 14, 536), (29, 15, 558), (32, 17, 565), (31, 1, 872), (11, 1, 901), (12, 1, 901), (14, 1, 929), (15, 1, 474), (17, 1, 522), (27, 1, 473), (34, 1, 915), (30, 1, 1209)]) (ids := [0, 1, 2, 3, 4, 5, 6, 7, 8, 11, 14, 17, 18, 19, 20, 21, 22, 23, 24, 26]) (cs := [2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 1, 11, 1, 1, 12, 1, 1, 13, 14, 15, 16, 17, 18, 19, 20, 1, 21, 1, 1, 1, 1, 1, 1, 1]) check rows (by decide) (by decide +kernel) (by decide +kernel)).trans
  decide +kernel

theorem cover1738 : P.CoversSplit 24 10 1738 0xa0000000000000000000000000000000a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 515, 516, 522, 523, 536, 860, 921, 1202, 1209, 1210]) (by decide +kernel)

theorem c1738_0 : P.sumLeaves 24 1779712 1024 = 20312 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1738) (lo := 0) (len := 1024) (W := 20312) check rows elimOK (by decide) (by decide) cover1738 (by decide)
  decide +kernel

theorem h1738 : P.leaf 34 1738 = 20312 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 20312)]) (.cons c1738_0 (.nil)) (by decide) (by decide))

theorem cover1739 : P.CoversSplit 24 10 1739 0xff000000000000000000000000000000ff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 516, 522, 523, 536, 860, 921, 1202, 1209]) (by decide +kernel)

theorem c1739_0 : P.sumLeaves 24 1780736 832 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1739) (lo := 0) (len := 832) (W := 0) check rows elimOK (by decide) (by decide) cover1739 (by decide)
  decide +kernel

theorem contract1739_1 : P.leaf 30 27837 = 30272 := by
  exact leaf_contract_factors (k := 30) (b := 18) (H := 27837) (ss := [(18, 1, 524), (4, 1, 566), (12, 1, 867), (11, 1, 818), (14, 1, 874), (8, 1, 537), (17, 1, 537), (16, 1, 874), (29, 1, 916), (30, 1, 1251), (31, 1, 1209), (19, 1, 1273)]) (ids := [0, 1, 3, 4, 5, 7, 8, 11, 13, 18, 20, 24, 25, 26, 19, 21, 22, 23]) (cs := [2, 3, 1, 4, 5, 6, 1, 7, 8, 1, 1, 9, 1, 10, 1, 1, 1, 1, 11, 16, 12, 17, 18, 19, 13, 14, 15, 1, 1, 1]) (bs := [14, 4]) (W := 30272) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1739_1 : P.sumLeaves 24 1781568 64 = 30272 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 27837) rows (by decide) (by decide)).symm.trans contract1739_1

theorem c1739_2 : P.sumLeaves 24 1781632 128 = 223936 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1739) (lo := 896) (len := 128) (W := 223936) check rows elimOK (by decide) (by decide) cover1739 (by decide)
  decide +kernel

theorem h1739 : P.leaf 34 1739 = 254208 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(832, 0), (64, 30272), (128, 223936)]) (.cons c1739_0 (.cons c1739_1 (.cons c1739_2 (.nil)))) (by decide) (by decide))

theorem h1740 : P.leaf 34 1740 = 14160 := by
  exact leaf_contract_factors (k := 34) (b := 20) (H := 1740) (ss := [(6, 1, 466), (26, 1, 472), (27, 1, 508), (18, 1, 524), (35, 33, 536), (17, 1, 565), (11, 1, 901), (12, 1, 901), (31, 1, 909), (28, 1, 465), (30, 1, 515), (29, 1, 915), (34, 1, 915), (32, 1, 522)]) (ids := [0, 1, 2, 3, 5, 6, 7, 8, 11, 12, 13, 14, 17, 18, 19, 20, 21, 31, 22, 23]) (cs := [2, 3, 4, 5, 1, 6, 7, 8, 9, 1, 1, 10, 11, 12, 13, 1, 1, 14, 15, 16, 17, 18, 20, 21, 1, 1, 1, 1, 1, 1, 1, 19, 1, 19]) (bs := [18, 2]) (W := 14160) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem cover1741 : P.CoversSplit 24 10 1741 0xcc00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 515, 522, 536, 573, 860, 872, 915, 1209, 1251, 1651]) (ps := [(14, [929], [1266])]) (by decide +kernel)

theorem c1741_0 : P.sumLeaves 24 1782784 1024 = 169600 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1741) (lo := 0) (len := 1024) (W := 169600) check rows elimOK (by decide) (by decide) cover1741 (by decide)
  decide +kernel

theorem h1741 : P.leaf 34 1741 = 169600 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 169600)]) (.cons c1741_0 (.nil)) (by decide) (by decide))

theorem cover1742 : P.CoversSplit 24 10 1742 0xa0000000000000000000000000000000a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 515, 516, 522, 536, 860, 916, 921, 1202, 1209, 1210, 1258, 1259]) (by decide +kernel)

theorem c1742_0 : P.sumLeaves 24 1783808 1024 = 181952 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1742) (lo := 0) (len := 1024) (W := 181952) check rows elimOK (by decide) (by decide) cover1742 (by decide)
  decide +kernel

theorem h1742 : P.leaf 34 1742 = 181952 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 181952)]) (.cons c1742_0 (.nil)) (by decide) (by decide))

theorem cover1743 : P.CoversSplit 24 10 1743 0xff000000000000000000000000000000ff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 522, 536, 860, 916, 921, 1202, 1209, 1258, 1259]) (by decide +kernel)

theorem c1743_0 : P.sumLeaves 24 1784832 1024 = 1686904 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1743) (lo := 0) (len := 1024) (W := 1686904) check rows elimOK (by decide) (by decide) cover1743 (by decide)
  decide +kernel

theorem h1743 : P.leaf 34 1743 = 1686904 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1686904)]) (.cons c1743_0 (.nil)) (by decide) (by decide))

theorem cover1747 : P.CoversSplit 24 10 1747 0xff00ff00a00000000000000000000000ff00ff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00800000000000000000000000cc00cc008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [475, 516, 573, 860, 921, 1202, 1210, 1217, 1259]) (by decide +kernel)

theorem c1747_0 : P.sumLeaves 24 1788928 320 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1747) (lo := 0) (len := 320) (W := 0) check rows elimOK (by decide) (by decide) cover1747 (by decide)
  decide +kernel

theorem contract1747_1 : P.leaf 30 27957 = 0 := by
  exact leaf_contract_zero (ss := [(6, 1, 478), (12, 1, 478), (27, 1, 573), (11, 1, 901), (29, 1, 921), (8, 0, 1266), (14, 1, 482), (7, 1, 488)]) (q := 537) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c1747_1 : P.sumLeaves 24 1789248 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 27957) rows (by decide) (by decide)).symm.trans contract1747_1

theorem c1747_2 : P.sumLeaves 24 1789312 64 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1747) (lo := 384) (len := 64) (W := 0) check rows elimOK (by decide) (by decide) cover1747 (by decide)
  decide +kernel

theorem contract1747_3 : P.leaf 30 27959 = 6784 := by
  exact leaf_contract_factors (k := 30) (b := 15) (H := 27959) (ss := [(6, 1, 478), (12, 1, 478), (27, 1, 573), (8, 1, 580), (18, 1, 580), (11, 1, 818), (29, 1, 921), (13, 1, 922), (14, 1, 923), (19, 1, 929), (15, 1, 930), (16, 1, 1265), (17, 1, 1273), (20, 1, 1657), (21, 1, 1658)]) (ids := [0, 1, 2, 3, 5, 7, 8, 20, 22, 24, 26, 28, 29, 21, 23]) (cs := [2, 3, 4, 5, 1, 6, 1, 7, 8, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 9, 15, 10, 16, 11, 1, 12, 1, 13, 14]) (bs := [13, 2]) (W := 6784) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1747_3 : P.sumLeaves 24 1789376 64 = 6784 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 27959) rows (by decide) (by decide)).symm.trans contract1747_3

theorem c1747_4 : P.sumLeaves 24 1789440 512 = 302432 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1747) (lo := 512) (len := 512) (W := 302432) check rows elimOK (by decide) (by decide) cover1747 (by decide)
  decide +kernel

theorem h1747 : P.leaf 34 1747 = 309216 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(320, 0), (64, 0), (64, 0), (64, 6784), (512, 302432)]) (.cons c1747_0 (.cons c1747_1 (.cons c1747_2 (.cons c1747_3 (.cons c1747_4 (.nil)))))) (by decide) (by decide))

theorem cover1748 : P.CoversSplit 24 10 1748 0xfc00fc00000000000000000000000000a000a400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 475, 508, 516, 536, 573, 860, 872, 915, 916, 1259, 1264]) (by decide +kernel)

theorem c1748_0 : P.sumLeaves 24 1789952 1024 = 53776 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1748) (lo := 0) (len := 1024) (W := 53776) check rows elimOK (by decide) (by decide) cover1748 (by decide)
  decide +kernel

theorem h1748 : P.leaf 34 1748 = 53776 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 53776)]) (.cons c1748_0 (.nil)) (by decide) (by decide))

theorem cover1749 : P.CoversSplit 24 10 1749 0xff00ff00000000000000000000000000ff00ff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 475, 516, 536, 573, 860, 872, 915, 916, 1259, 1264]) (by decide +kernel)

theorem c1749_0 : P.sumLeaves 24 1790976 1024 = 897488 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1749) (lo := 0) (len := 1024) (W := 897488) check rows elimOK (by decide) (by decide) cover1749 (by decide)
  decide +kernel

theorem h1749 : P.leaf 34 1749 = 897488 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 897488)]) (.cons c1749_0 (.nil)) (by decide) (by decide))

theorem cover1750 : P.CoversSplit 24 10 1750 0xff00ff00a00000000000000000000000a000a5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 475, 516, 573, 860, 915, 916, 921, 1202, 1210, 1259]) (ps := [(14, [965], [860, 1266])]) (by decide +kernel)

theorem c1750_0 : P.sumLeaves 24 1792000 448 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1750) (lo := 0) (len := 448) (W := 0) check rows elimOK (by decide) (by decide) cover1750 (by decide)
  decide +kernel

theorem contract1750_1 : P.leaf 30 28007 = 23360 := by
  exact leaf_contract_factors (k := 30) (b := 19) (H := 28007) (ss := [(27, 1, 573), (8, 1, 580), (18, 1, 580), (29, 1, 916), (13, 1, 922), (14, 1, 923), (19, 1, 929), (16, 1, 1265), (17, 1, 1273), (20, 1, 1657), (21, 1, 1658)]) (ids := [0, 1, 2, 3, 4, 5, 7, 8, 9, 10, 13, 20, 21, 22, 24, 26, 28, 29, 23]) (cs := [2, 3, 4, 5, 6, 7, 1, 8, 9, 10, 11, 1, 1, 12, 1, 1, 1, 1, 1, 1, 13, 14, 15, 20, 16, 1, 17, 1, 18, 19]) (bs := [18, 1]) (W := 23360) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1750_1 : P.sumLeaves 24 1792448 64 = 23360 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 28007) rows (by decide) (by decide)).symm.trans contract1750_1

theorem c1750_2 : P.sumLeaves 24 1792512 512 = 676356 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1750) (lo := 512) (len := 512) (W := 676356) check rows elimOK (by decide) (by decide) cover1750 (by decide)
  decide +kernel

theorem h1750 : P.leaf 34 1750 = 699716 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(448, 0), (64, 23360), (512, 676356)]) (.cons c1750_0 (.cons c1750_1 (.cons c1750_2 (.nil)))) (by decide) (by decide))

theorem cover1751 : P.CoversSplit 24 10 1751 0xff00ff00a00000000000000000000000ff00ff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [475, 516, 573, 860, 915, 916, 921, 1202, 1210, 1217, 1259]) (ps := [(14, [965], [1217, 1266])]) (by decide +kernel)

theorem c1751_0 : P.sumLeaves 24 1793024 448 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1751) (lo := 0) (len := 448) (W := 0) check rows elimOK (by decide) (by decide) cover1751 (by decide)
  decide +kernel

theorem contract1751_1 : P.leaf 30 28023 = 46718 := by
  exact leaf_contract_factors (k := 30) (b := 19) (H := 28023) (ss := [(27, 1, 573), (8, 1, 580), (18, 1, 580), (29, 1, 916), (13, 1, 922), (14, 1, 923), (19, 1, 929), (16, 1, 1265), (17, 1, 1273), (20, 1, 1657), (21, 1, 1658)]) (ids := [0, 1, 2, 3, 4, 5, 7, 8, 9, 10, 13, 20, 21, 22, 24, 26, 28, 29, 23]) (cs := [2, 3, 4, 5, 6, 7, 1, 8, 9, 10, 11, 1, 1, 12, 1, 1, 1, 1, 1, 1, 13, 14, 15, 20, 16, 1, 17, 1, 18, 19]) (bs := [18, 1]) (W := 46718) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1751_1 : P.sumLeaves 24 1793472 64 = 46718 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 28023) rows (by decide) (by decide)).symm.trans contract1751_1

theorem c1751_2 : P.sumLeaves 24 1793536 512 = 3335642 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1751) (lo := 512) (len := 512) (W := 3335642) check rows elimOK (by decide) (by decide) cover1751 (by decide)
  decide +kernel

theorem h1751 : P.leaf 34 1751 = 3382360 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(448, 0), (64, 46718), (512, 3335642)]) (.cons c1751_0 (.cons c1751_1 (.cons c1751_2 (.nil)))) (by decide) (by decide))

theorem cover1752 : P.CoversSplit 24 10 1752 0xfc00fc00000000000000000000000000a000a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 474, 508, 516, 536, 573, 860, 872, 915, 1258, 1259, 1264]) (ps := [(8, [537], [516]), (14, [487, 509], [487, 860])]) (by decide +kernel)

theorem c1752_0 : P.sumLeaves 24 1794048 832 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1752) (lo := 0) (len := 832) (W := 0) check rows elimOK (by decide) (by decide) cover1752 (by decide)
  decide +kernel

theorem contract1752_1 : P.leaf 30 28045 = 8448 := by
  exact leaf_contract_factors (k := 30) (b := 14) (H := 28045) (ss := [(6, 1, 467), (29, 1, 474), (18, 1, 475), (15, 2, 486), (14, 1, 487), (31, 1, 536), (8, 1, 537), (26, 1, 516), (17, 1, 537), (2, 1, 558), (12, 1, 803), (11, 1, 459), (4, 1, 410), (28, 1, 860), (16, 1, 874), (19, 1, 1273)]) (ids := [1, 3, 5, 7, 11, 18, 20, 25, 8, 19, 21, 22, 23, 28]) (cs := [1, 2, 1, 3, 1, 4, 1, 5, 10, 1, 1, 6, 1, 1, 1, 1, 1, 1, 7, 11, 8, 12, 13, 14, 1, 9, 1, 1, 15, 1]) (bs := [8, 6]) (W := 8448) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1752_1 : P.sumLeaves 24 1794880 64 = 8448 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 28045) rows (by decide) (by decide)).symm.trans contract1752_1

theorem c1752_2 : P.sumLeaves 24 1794944 128 = 67832 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1752) (lo := 896) (len := 128) (W := 67832) check rows elimOK (by decide) (by decide) cover1752 (by decide)
  decide +kernel

theorem h1752 : P.leaf 34 1752 = 76280 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(832, 0), (64, 8448), (128, 67832)]) (.cons c1752_0 (.cons c1752_1 (.cons c1752_2 (.nil)))) (by decide) (by decide))

theorem cover1753 : P.CoversSplit 24 10 1753 0xff00ff00000000000000000000000000ff00ff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 474, 516, 536, 573, 860, 872, 915, 1258, 1259, 1264]) (ps := [(14, [923, 929], [487])]) (by decide +kernel)

theorem c1753_0 : P.sumLeaves 24 1795072 832 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1753) (lo := 0) (len := 832) (W := 0) check rows elimOK (by decide) (by decide) cover1753 (by decide)
  decide +kernel

theorem contract1753_1 : P.leaf 30 28061 = 58456 := by
  exact leaf_contract_factors (k := 30) (b := 19) (H := 28061) (ss := [(29, 1, 474), (18, 1, 475), (14, 1, 487), (31, 1, 536), (8, 1, 537), (17, 1, 537), (15, 1, 558), (12, 1, 867), (11, 1, 818), (16, 1, 874), (19, 1, 1273)]) (ids := [0, 1, 2, 3, 4, 5, 7, 8, 11, 18, 19, 20, 22, 24, 25, 26, 28, 21, 23]) (cs := [2, 3, 4, 5, 6, 7, 1, 8, 9, 1, 1, 10, 1, 1, 1, 1, 1, 1, 11, 12, 13, 19, 14, 20, 15, 16, 17, 1, 18, 1]) (bs := [17, 2]) (W := 58456) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1753_1 : P.sumLeaves 24 1795904 64 = 58456 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 28061) rows (by decide) (by decide)).symm.trans contract1753_1

theorem c1753_2 : P.sumLeaves 24 1795968 128 = 385648 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1753) (lo := 896) (len := 128) (W := 385648) check rows elimOK (by decide) (by decide) cover1753 (by decide)
  decide +kernel

theorem h1753 : P.leaf 34 1753 = 444104 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(832, 0), (64, 58456), (128, 385648)]) (.cons c1753_0 (.cons c1753_1 (.cons c1753_2 (.nil)))) (by decide) (by decide))

theorem cover1754 : P.CoversSplit 24 10 1754 0xff00ff00a00000000000000000000000a000a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 516, 536, 573, 860, 921, 1202, 1210, 1259]) (ps := [(8, [537], [516]), (14, [509], [860, 1266])]) (by decide +kernel)

theorem c1754_0 : P.sumLeaves 24 1796096 448 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1754) (lo := 0) (len := 448) (W := 0) check rows elimOK (by decide) (by decide) cover1754 (by decide)
  decide +kernel

theorem contract1754_1 : P.leaf 30 28071 = 13416 := by
  exact leaf_contract_factors (k := 30) (b := 16) (H := 28071) (ss := [(15, 1, 486), (14, 1, 509), (27, 1, 573), (8, 1, 580), (18, 1, 580), (12, 1, 867), (11, 1, 818), (29, 1, 916), (13, 1, 922), (19, 1, 930), (16, 1, 1265), (17, 1, 1273), (20, 1, 1657), (21, 1, 1658)]) (ids := [0, 1, 2, 3, 4, 5, 7, 8, 20, 22, 24, 26, 28, 29, 21, 23]) (cs := [2, 3, 4, 5, 6, 7, 1, 8, 9, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 10, 16, 11, 17, 12, 1, 13, 1, 14, 15]) (bs := [14, 2]) (W := 13416) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1754_1 : P.sumLeaves 24 1796544 64 = 13416 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 28071) rows (by decide) (by decide)).symm.trans contract1754_1

theorem c1754_2 : P.sumLeaves 24 1796608 512 = 348420 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1754) (lo := 512) (len := 512) (W := 348420) check rows elimOK (by decide) (by decide) cover1754 (by decide)
  decide +kernel

theorem h1754 : P.leaf 34 1754 = 361836 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(448, 0), (64, 13416), (512, 348420)]) (.cons c1754_0 (.cons c1754_1 (.cons c1754_2 (.nil)))) (by decide) (by decide))

theorem cover1755 : P.CoversSplit 24 10 1755 0xff00ff00a00000000000000000000000ff00ff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00800000000000000000000000cc00cc008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [516, 536, 573, 860, 921, 1202, 1210, 1217, 1259]) (by decide +kernel)

theorem c1755_0 : P.sumLeaves 24 1797120 320 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1755) (lo := 0) (len := 320) (W := 0) check rows elimOK (by decide) (by decide) cover1755 (by decide)
  decide +kernel

theorem contract1755_1 : P.leaf 30 28085 = 0 := by
  exact leaf_contract_zero (ss := [(27, 1, 573), (12, 1, 867), (11, 1, 901), (29, 1, 921), (8, 0, 1266), (14, 0, 537), (6, 1, 460), (20, 1, 482), (21, 0, 488), (5, 1, 608), (10, 1, 811)]) (q := 929) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c1755_1 : P.sumLeaves 24 1797440 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 28085) rows (by decide) (by decide)).symm.trans contract1755_1

theorem c1755_2 : P.sumLeaves 24 1797504 64 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1755) (lo := 384) (len := 64) (W := 0) check rows elimOK (by decide) (by decide) cover1755 (by decide)
  decide +kernel

theorem contract1755_3 : P.leaf 30 28087 = 17440 := by
  exact leaf_contract_factors (k := 30) (b := 16) (H := 28087) (ss := [(27, 1, 573), (8, 1, 580), (18, 1, 580), (12, 1, 867), (11, 1, 818), (29, 1, 921), (13, 1, 922), (14, 1, 923), (19, 1, 965), (15, 1, 930), (16, 1, 1265), (17, 1, 1273), (20, 1, 1657), (21, 1, 1658)]) (ids := [0, 1, 2, 3, 4, 5, 7, 8, 20, 22, 24, 26, 28, 29, 21, 23]) (cs := [2, 3, 4, 5, 6, 7, 1, 8, 9, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 10, 16, 11, 17, 12, 1, 13, 1, 14, 15]) (bs := [14, 2]) (W := 17440) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1755_3 : P.sumLeaves 24 1797568 64 = 17440 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 28087) rows (by decide) (by decide)).symm.trans contract1755_3

theorem c1755_4 : P.sumLeaves 24 1797632 512 = 969848 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1755) (lo := 512) (len := 512) (W := 969848) check rows elimOK (by decide) (by decide) cover1755 (by decide)
  decide +kernel

theorem h1755 : P.leaf 34 1755 = 987288 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(320, 0), (64, 0), (64, 0), (64, 17440), (512, 969848)]) (.cons c1755_0 (.cons c1755_1 (.cons c1755_2 (.cons c1755_3 (.cons c1755_4 (.nil)))))) (by decide) (by decide))

theorem cover1756 : P.CoversSplit 24 10 1756 0xfc00fc00000000000000000000000000a000a4000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 508, 516, 536, 573, 860, 872, 915, 1258, 1259, 1264]) (ps := [(14, [929], [860, 1266])]) (by decide +kernel)

theorem c1756_0 : P.sumLeaves 24 1798144 448 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1756) (lo := 0) (len := 448) (W := 0) check rows elimOK (by decide) (by decide) cover1756 (by decide)
  decide +kernel

theorem contract1756_1 : P.leaf 30 28103 = 7024 := by
  exact leaf_contract_factors (k := 30) (b := 15) (H := 28103) (ss := [(18, 1, 475), (27, 1, 573), (8, 1, 580), (31, 1, 872), (11, 1, 901), (6, 1, 459), (12, 1, 818), (29, 1, 915), (13, 1, 922), (14, 1, 923), (16, 1, 1265), (19, 1, 1308), (17, 1, 1273), (20, 1, 1657), (21, 1, 1658)]) (ids := [0, 1, 2, 3, 7, 8, 13, 20, 22, 24, 26, 28, 5, 21, 23]) (cs := [2, 3, 4, 5, 1, 14, 1, 6, 7, 1, 1, 1, 1, 8, 1, 1, 1, 1, 1, 1, 9, 15, 10, 16, 11, 1, 12, 1, 13, 1]) (bs := [12, 3]) (W := 7024) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1756_1 : P.sumLeaves 24 1798592 64 = 7024 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 28103) rows (by decide) (by decide)).symm.trans contract1756_1

theorem c1756_2 : P.sumLeaves 24 1798656 512 = 355920 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1756) (lo := 512) (len := 512) (W := 355920) check rows elimOK (by decide) (by decide) cover1756 (by decide)
  decide +kernel

theorem h1756 : P.leaf 34 1756 = 362944 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(448, 0), (64, 7024), (512, 355920)]) (.cons c1756_0 (.cons c1756_1 (.cons c1756_2 (.nil)))) (by decide) (by decide))

theorem cover1757 : P.CoversSplit 24 10 1757 0xff00ff00000000000000000000000000ff00ff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 516, 536, 573, 860, 867, 872, 915, 1258, 1259, 1264]) (ps := [(14, [929], [1266])]) (by decide +kernel)

theorem c1757_0 : P.sumLeaves 24 1799168 448 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1757) (lo := 0) (len := 448) (W := 0) check rows elimOK (by decide) (by decide) cover1757 (by decide)
  decide +kernel

theorem contract1757_1 : P.leaf 30 28119 = 20992 := by
  exact leaf_contract_factors (k := 30) (b := 16) (H := 28119) (ss := [(18, 1, 475), (27, 1, 573), (8, 1, 580), (31, 1, 872), (11, 1, 901), (12, 1, 818), (29, 1, 915), (13, 1, 922), (14, 1, 923), (16, 1, 1265), (19, 1, 1308), (17, 1, 1273), (20, 1, 1657), (21, 1, 1658)]) (ids := [0, 1, 2, 3, 4, 7, 8, 13, 20, 22, 26, 28, 5, 21, 23, 24]) (cs := [2, 3, 4, 5, 6, 14, 1, 7, 8, 1, 1, 1, 1, 9, 1, 1, 1, 1, 1, 1, 10, 15, 11, 16, 17, 1, 12, 1, 13, 1]) (bs := [12, 4]) (W := 20992) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1757_1 : P.sumLeaves 24 1799616 64 = 20992 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 28119) rows (by decide) (by decide)).symm.trans contract1757_1

theorem c1757_2 : P.sumLeaves 24 1799680 512 = 1629272 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1757) (lo := 512) (len := 512) (W := 1629272) check rows elimOK (by decide) (by decide) cover1757 (by decide)
  decide +kernel

theorem h1757 : P.leaf 34 1757 = 1650264 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(448, 0), (64, 20992), (512, 1629272)]) (.cons c1757_0 (.cons c1757_1 (.cons c1757_2 (.nil)))) (by decide) (by decide))

theorem cover1758 : P.CoversSplit 24 10 1758 0xff00ff00a00000000000000000000000a000a5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 516, 536, 573, 860, 916, 921, 1202, 1210, 1259]) (ps := [(14, [965], [860, 1266])]) (by decide +kernel)

theorem c1758_0 : P.sumLeaves 24 1800192 448 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1758) (lo := 0) (len := 448) (W := 0) check rows elimOK (by decide) (by decide) cover1758 (by decide)
  decide +kernel

theorem contract1758_1 : P.leaf 30 28135 = 38568 := by
  exact leaf_contract_factors (k := 30) (b := 19) (H := 28135) (ss := [(27, 1, 573), (8, 1, 580), (18, 1, 580), (29, 1, 916), (13, 1, 922), (14, 1, 923), (16, 1, 1265), (19, 1, 1308), (17, 1, 1273), (20, 1, 1657), (21, 1, 1658)]) (ids := [0, 1, 2, 3, 4, 5, 7, 8, 9, 10, 13, 20, 21, 22, 24, 26, 28, 29, 23]) (cs := [2, 3, 4, 5, 6, 7, 1, 8, 9, 10, 11, 1, 1, 12, 1, 1, 1, 1, 1, 1, 13, 14, 15, 20, 16, 1, 17, 1, 18, 19]) (bs := [18, 1]) (W := 38568) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1758_1 : P.sumLeaves 24 1800640 64 = 38568 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 28135) rows (by decide) (by decide)).symm.trans contract1758_1

theorem c1758_2 : P.sumLeaves 24 1800704 512 = 2185632 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1758) (lo := 512) (len := 512) (W := 2185632) check rows elimOK (by decide) (by decide) cover1758 (by decide)
  decide +kernel

theorem h1758 : P.leaf 34 1758 = 2224200 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(448, 0), (64, 38568), (512, 2185632)]) (.cons c1758_0 (.cons c1758_1 (.cons c1758_2 (.nil)))) (by decide) (by decide))

theorem cover1759 : P.CoversSplit 24 10 1759 0xff00ff00a00000000000000000000000ff00ff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [516, 536, 573, 860, 916, 921, 1202, 1210, 1217, 1259]) (ps := [(14, [965], [1217, 1266])]) (by decide +kernel)

theorem c1759_0 : P.sumLeaves 24 1801216 448 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1759) (lo := 0) (len := 448) (W := 0) check rows elimOK (by decide) (by decide) cover1759 (by decide)
  decide +kernel

theorem contract1759_1 : P.leaf 30 28151 = 66856 := by
  exact leaf_contract_factors (k := 30) (b := 19) (H := 28151) (ss := [(27, 1, 573), (8, 1, 580), (18, 1, 580), (29, 1, 916), (13, 1, 922), (14, 1, 923), (16, 1, 1265), (19, 1, 1308), (17, 1, 1273), (20, 1, 1657), (21, 1, 1658)]) (ids := [0, 1, 2, 3, 4, 5, 7, 8, 9, 10, 13, 20, 21, 22, 24, 26, 28, 29, 23]) (cs := [2, 3, 4, 5, 6, 7, 1, 8, 9, 10, 11, 1, 1, 12, 1, 1, 1, 1, 1, 1, 13, 14, 15, 20, 16, 1, 17, 1, 18, 19]) (bs := [18, 1]) (W := 66856) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1759_1 : P.sumLeaves 24 1801664 64 = 66856 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 28151) rows (by decide) (by decide)).symm.trans contract1759_1

theorem c1759_2 : P.sumLeaves 24 1801728 512 = 5701132 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1759) (lo := 512) (len := 512) (W := 5701132) check rows elimOK (by decide) (by decide) cover1759 (by decide)
  decide +kernel

theorem h1759 : P.leaf 34 1759 = 5767988 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(448, 0), (64, 66856), (512, 5701132)]) (.cons c1759_0 (.cons c1759_1 (.cons c1759_2 (.nil)))) (by decide) (by decide))

theorem cover1762 : P.CoversSplit 24 10 1762 0xaa000000000000000000000000000000a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000088000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 475, 515, 523, 524, 565, 566, 573, 860, 921, 1209, 1258, 1259, 1308]) (ps := [(14, [874], [860])]) (by decide +kernel)

theorem c1762_0 : P.sumLeaves 24 1804288 960 = 2384 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1762) (lo := 0) (len := 960) (W := 2384) check rows elimOK (by decide) (by decide) cover1762 (by decide)
  decide +kernel

theorem contract1762_1 : P.leaf 30 28207 = 13088 := by
  exact leaf_contract_factors (k := 30) (b := 20) (H := 28207) (ss := [(2, 1, 453), (5, 1, 453), (3, 1, 409), (30, 1, 524), (12, 1, 867), (11, 1, 818), (6, 1, 460), (29, 1, 921), (31, 1, 1209), (26, 1, 515)]) (ids := [2, 5, 6, 7, 8, 11, 12, 13, 14, 15, 16, 17, 18, 19, 21, 22, 25, 26, 20, 23]) (cs := [1, 1, 2, 1, 1, 3, 4, 5, 6, 1, 1, 7, 8, 9, 10, 11, 12, 13, 14, 15, 20, 16, 17, 21, 1, 18, 19, 1, 1, 1]) (bs := [18, 2]) (W := 13088) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1762_1 : P.sumLeaves 24 1805248 64 = 13088 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 28207) rows (by decide) (by decide)).symm.trans contract1762_1

theorem h1762 : P.leaf 34 1762 = 15472 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(960, 2384), (64, 13088)]) (.cons c1762_0 (.cons c1762_1 (.nil))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(1724, 48), (1725, 48), (1726, 48), (1727, 48), (1730, 24), (1731, 48), (1732, 48), (1733, 48), (1734, 48), (1735, 48), (1736, 48), (1737, 48), (1738, 48), (1739, 48), (1740, 48), (1741, 48), (1742, 48), (1743, 48), (1747, 24), (1748, 48), (1749, 48), (1750, 48), (1751, 48), (1752, 48), (1753, 48), (1754, 48), (1755, 48), (1756, 48), (1757, 48), (1758, 48), (1759, 48), (1762, 24)]

theorem segOK : checkSeg 16 perms 1724 1763 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 1724 1763 1464 1160290368 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 1160290368)
    (SegSum.cons (w := 48) h1724 (SegSum.cons (w := 48) h1725 (SegSum.cons (w := 48) h1726 (SegSum.cons (w := 48) h1727 (SegSum.cons (w := 24) h1730 (SegSum.cons (w := 48) h1731 (SegSum.cons (w := 48) h1732 (SegSum.cons (w := 48) h1733 (SegSum.cons (w := 48) h1734 (SegSum.cons (w := 48) h1735 (SegSum.cons (w := 48) h1736 (SegSum.cons (w := 48) h1737 (SegSum.cons (w := 48) h1738 (SegSum.cons (w := 48) h1739 (SegSum.cons (w := 48) h1740 (SegSum.cons (w := 48) h1741 (SegSum.cons (w := 48) h1742 (SegSum.cons (w := 48) h1743 (SegSum.cons (w := 24) h1747 (SegSum.cons (w := 48) h1748 (SegSum.cons (w := 48) h1749 (SegSum.cons (w := 48) h1750 (SegSum.cons (w := 48) h1751 (SegSum.cons (w := 48) h1752 (SegSum.cons (w := 48) h1753 (SegSum.cons (w := 48) h1754 (SegSum.cons (w := 48) h1755 (SegSum.cons (w := 48) h1756 (SegSum.cons (w := 48) h1757 (SegSum.cons (w := 48) h1758 (SegSum.cons (w := 48) h1759 (SegSum.cons (w := 24) h1762 (show SegSum (P.leaf 34) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S4N1.C0.S13
