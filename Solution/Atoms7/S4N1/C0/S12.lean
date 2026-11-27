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

namespace RACert.S4N1.C0.S12

open RACert RACert.Problem

theorem cover1663 : P.CoversSplit 24 10 1663 0xcc00cc00880000000000000000000000cc00cc008800000000330033002200000000000000000000003300330000000000000000000000000033003300000000cc00cc00880000000000000000000000cc00cc008000000000330033002000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [572, 860, 867, 915, 1202, 1209, 1258]) (ps := [(8, [1217], [572, 1266])]) (by decide +kernel)

theorem c1663_0 : P.sumLeaves 24 1702912 256 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1663) (lo := 0) (len := 256) (W := 0) check rows elimOK (by decide) (by decide) cover1663 (by decide)
  decide +kernel

theorem contract1663_1 : P.leaf 30 26612 = 1540 := by
  exact leaf_contract_factors (k := 30) (b := 14) (H := 26612) (ss := [(16, 0, 1258), (27, 0, 1258), (7, 0, 572), (8, 0, 572), (29, 0, 572), (9, 0, 573), (13, 0, 579), (14, 0, 580), (5, 1, 433), (15, 0, 587), (17, 0, 587), (12, 1, 825), (21, 1, 874), (20, 1, 880), (31, 1, 1217), (19, 18, 1658)]) (ids := [0, 1, 2, 4, 8, 9, 16, 20, 21, 22, 24, 26, 28, 23]) (cs := [2, 3, 4, 1, 5, 0, 0, 0, 6, 7, 1, 0, 0, 0, 0, 0, 8, 8, 1, 1, 9, 10, 11, 15, 12, 0, 13, 0, 14, 1]) (bs := [13, 1]) (W := 1540) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1663_1 : P.sumLeaves 24 1703168 64 = 1540 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 26612) rows (by decide) (by decide)).symm.trans contract1663_1

theorem contract1663_2 : P.leaf 30 26613 = 5902 := by
  exact leaf_contract_factors (k := 30) (b := 17) (H := 26613) (ss := [(27, 1, 572), (29, 1, 915), (8, 0, 1266), (14, 0, 580), (5, 1, 433), (12, 1, 825), (21, 1, 874), (9, 7, 629), (20, 1, 880), (15, 13, 972), (31, 1, 1217), (17, 16, 1315), (19, 18, 1658)]) (ids := [0, 1, 2, 4, 5, 8, 9, 11, 14, 16, 20, 21, 22, 24, 26, 28, 23]) (cs := [2, 3, 4, 1, 5, 6, 0, 6, 7, 8, 1, 9, 0, 9, 10, 10, 11, 11, 1, 1, 12, 13, 14, 18, 15, 1, 16, 1, 17, 1]) (bs := [16, 1]) (W := 5902) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1663_2 : P.sumLeaves 24 1703232 64 = 5902 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 26613) rows (by decide) (by decide)).symm.trans contract1663_2

theorem c1663_3 : P.sumLeaves 24 1703296 64 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1663) (lo := 384) (len := 64) (W := 0) check rows elimOK (by decide) (by decide) cover1663 (by decide)
  decide +kernel

theorem contract1663_4 : P.leaf 30 26615 = 21556 := by
  exact leaf_contract_factors (k := 30) (b := 17) (H := 26615) (ss := [(27, 1, 572), (8, 1, 580), (18, 1, 580), (7, 1, 579), (19, 1, 586), (9, 1, 587), (29, 1, 915), (13, 1, 922), (14, 1, 923), (15, 1, 930), (16, 1, 1265), (17, 1, 1273), (20, 1, 1657)]) (ids := [0, 1, 2, 3, 4, 8, 9, 10, 20, 21, 22, 24, 26, 28, 29, 19, 23]) (cs := [2, 3, 4, 5, 6, 1, 1, 1, 7, 8, 9, 1, 1, 1, 1, 1, 1, 1, 1, 17, 10, 11, 12, 18, 13, 1, 14, 1, 15, 16]) (bs := [15, 2]) (W := 21556) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1663_4 : P.sumLeaves 24 1703360 64 = 21556 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 26615) rows (by decide) (by decide)).symm.trans contract1663_4

theorem c1663_5 : P.sumLeaves 24 1703424 512 = 3785311 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1663) (lo := 512) (len := 512) (W := 3785311) check rows elimOK (by decide) (by decide) cover1663 (by decide)
  decide +kernel

theorem h1663 : P.leaf 34 1663 = 3814309 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(256, 0), (64, 1540), (64, 5902), (64, 0), (64, 21556), (512, 3785311)]) (.cons c1663_0 (.cons c1663_1 (.cons c1663_2 (.cons c1663_3 (.cons c1663_4 (.cons c1663_5 (.nil))))))) (by decide) (by decide))

theorem cover1683 : P.CoversSplit 24 10 1683 0xaa000000000000000000000000000000a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000088000000000000000000000000000000aa0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [516, 528, 536, 921, 1209, 1259]) (ps := [(8, [580], [573]), (14, [874], [860])]) (by decide +kernel)

noncomputable def f1683 (i : ℕ) := rowWeight keep4 twice4 i * P.leaf 24 (1723392 + i)

theorem c1683_0 : rowSum f1683 0 1024 = 8933 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 1683) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover1683 (by decide)
  decide +kernel

theorem sum1683 : rowSum f1683 0 1024 = 8933 :=
  c1683_0

theorem h1683 : P.leaf 34 1683 = 8933 :=
  leaf_weighted (k := 24) (d := 10) (H := 1683) (keep := keep4) (twice := twice4) rows (by decide) (by decide) bal4 (invRow4 (H := 1683) (by decide) (by decide +kernel)) sum1683

theorem cover1684 : P.CoversSplit 24 10 1684 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [559]) (by decide +kernel)

theorem c1684_0 : P.sumLeaves 24 1724416 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1684) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1684 (by decide)
  decide +kernel

theorem h1684 : P.leaf 34 1684 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1684_0 (.nil)) (by decide) (by decide))

theorem cover1685 : P.CoversSplit 24 10 1685 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [559]) (by decide +kernel)

theorem c1685_0 : P.sumLeaves 24 1725440 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1685) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1685 (by decide)
  decide +kernel

theorem h1685 : P.leaf 34 1685 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1685_0 (.nil)) (by decide) (by decide))

theorem cover1686 : P.CoversSplit 24 10 1686 0xaa00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000088000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 479, 516, 536, 860, 872, 916, 921, 1209, 1251, 1259]) (ps := [(8, [468, 531, 537], [468, 573])]) (by decide +kernel)

theorem c1686_0 : P.sumLeaves 24 1726464 1024 = 60416 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1686) (lo := 0) (len := 1024) (W := 60416) check rows elimOK (by decide) (by decide) cover1686 (by decide)
  decide +kernel

theorem h1686 : P.leaf 34 1686 = 60416 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 60416)]) (.cons c1686_0 (.nil)) (by decide) (by decide))

theorem cover1687 : P.CoversSplit 24 10 1687 0xaa000000000000000000000000000000a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000088000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [516, 528, 536, 860, 916, 921, 1209, 1259]) (ps := [(8, [580], [573]), (14, [965], [1266])]) (by decide +kernel)

theorem c1687_0 : P.sumLeaves 24 1727488 1024 = 128784 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1687) (lo := 0) (len := 1024) (W := 128784) check rows elimOK (by decide) (by decide) cover1687 (by decide)
  decide +kernel

theorem h1687 : P.leaf 34 1687 = 128784 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 128784)]) (.cons c1687_0 (.nil)) (by decide) (by decide))

theorem cover1692 : P.CoversSplit 24 10 1692 0xa8000000000000000000000000000000a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000088000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 508, 516, 524, 536, 573, 860, 872, 915, 1209, 1251, 1259, 1264]) (ps := [(8, [537], [1266])]) (by decide +kernel)

noncomputable def f1692 (i : ℕ) := rowWeight keep4 twice4 i * P.leaf 24 (1732608 + i)

theorem c1692_0 : rowSum f1692 0 1024 = 15056 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 1692) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover1692 (by decide)
  decide +kernel

theorem sum1692 : rowSum f1692 0 1024 = 15056 :=
  c1692_0

theorem h1692 : P.leaf 34 1692 = 15056 :=
  leaf_weighted (k := 24) (d := 10) (H := 1692) (keep := keep4) (twice := twice4) rows (by decide) (by decide) bal4 (invRow4 (H := 1692) (by decide) (by decide +kernel)) sum1692

theorem cover1693 : P.CoversSplit 24 10 1693 0xaa000000000000000000000000000000a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000088000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 516, 517, 524, 528, 573, 860, 915, 1209, 1259, 1264]) (ps := [(8, [615], [1266])]) (by decide +kernel)

theorem c1693_0 : P.sumLeaves 24 1733632 1024 = 230080 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1693) (lo := 0) (len := 1024) (W := 230080) check rows elimOK (by decide) (by decide) cover1693 (by decide)
  decide +kernel

theorem h1693 : P.leaf 34 1693 = 230080 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 230080)]) (.cons c1693_0 (.nil)) (by decide) (by decide))

theorem cover1695 : P.CoversSplit 24 10 1695 0xaa000000000000000000000000000000a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000088000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [516, 517, 524, 528, 573, 860, 916, 921, 1209, 1259]) (ps := [(8, [615], [1266])]) (by decide +kernel)

noncomputable def f1695 (i : ℕ) := rowWeight keep4 twice4 i * P.leaf 24 (1735680 + i)

theorem c1695_0 : rowSum f1695 0 1024 = 644896 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 1695) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover1695 (by decide)
  decide +kernel

theorem sum1695 : rowSum f1695 0 1024 = 644896 :=
  c1695_0

theorem h1695 : P.leaf 34 1695 = 644896 :=
  leaf_weighted (k := 24) (d := 10) (H := 1695) (keep := keep4) (twice := twice4) rows (by decide) (by decide) bal4 (invRow4 (H := 1695) (by decide) (by decide +kernel)) sum1695

theorem h1698 : P.leaf 34 1698 = 0 := by
  exact leaf_contract_zero (ss := [(2, 1, 453), (5, 1, 453), (3, 1, 409), (8, 0, 468), (34, 1, 475), (14, 0, 486), (35, 0, 482), (12, 1, 487), (15, 1, 509), (26, 9, 510), (16, 1, 529), (18, 1, 536), (4, 1, 426), (33, 0, 566), (21, 0, 531), (20, 1, 433)]) (q := 608) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem h1699 : P.leaf 34 1699 = 0 := by
  exact leaf_contract_zero (ss := [(2, 1, 453), (5, 1, 453), (31, 1, 468), (34, 1, 475), (6, 1, 478), (12, 1, 460), (35, 0, 524), (16, 3, 529), (18, 1, 536), (33, 0, 566), (11, 1, 818), (29, 1, 921), (13, 1, 922), (30, 1, 1251), (32, 1, 1259), (3, 1, 1265), (14, 0, 1266), (8, 1, 608), (15, 1, 488), (9, 1, 489), (26, 1, 517), (27, 1, 573), (10, 1, 811), (28, 1, 860)]) (q := 874) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem h1700 : P.leaf 34 1700 = 0 := by
  exact leaf_contract_zero (ss := [(6, 1, 466), (33, 8, 468), (26, 1, 472), (35, 0, 475), (13, 2, 480), (27, 1, 508), (9, 1, 510), (16, 3, 529), (14, 0, 559), (18, 4, 487), (8, 0, 566), (21, 0, 482), (20, 1, 537), (5, 1, 601), (12, 1, 461), (10, 1, 458), (11, 1, 459), (31, 1, 517), (30, 1, 515), (34, 1, 573), (29, 1, 473), (32, 1, 522), (28, 1, 860)]) (q := 965) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem h1701 : P.leaf 34 1701 = 0 := by
  exact leaf_contract_zero (ss := [(35, 0, 475), (13, 2, 480), (16, 3, 529), (14, 0, 559), (18, 4, 487), (33, 0, 566), (34, 12, 867), (31, 1, 872), (8, 0, 874), (5, 1, 468), (21, 0, 482), (20, 1, 433), (12, 1, 622), (27, 1, 473), (29, 1, 473), (32, 1, 522), (11, 1, 901)]) (q := 965) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem h1702 : P.leaf 34 1702 = 0 := by
  exact leaf_contract_zero (ss := [(33, 8, 468), (35, 0, 524), (34, 5, 475), (16, 3, 529), (18, 1, 536), (8, 0, 566), (21, 0, 531), (20, 1, 537), (14, 0, 580), (26, 9, 510), (12, 5, 559), (5, 1, 488), (4, 1, 426), (31, 1, 615), (9, 1, 515), (6, 1, 461), (30, 1, 515), (27, 1, 573), (7, 1, 628), (28, 1, 860), (29, 1, 916), (13, 1, 922), (2, 1, 412)]) (q := 965) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem h1703 : P.leaf 34 1703 = 0 := by
  exact leaf_contract_zero (ss := [(35, 0, 524), (34, 5, 475), (16, 3, 529), (18, 1, 536), (33, 0, 566), (12, 5, 867), (5, 1, 461), (31, 1, 468), (29, 1, 921), (13, 1, 922), (14, 1, 965), (3, 1, 531), (8, 1, 531), (26, 1, 517), (27, 1, 573), (28, 1, 860), (19, 1, 929), (30, 1, 1209), (32, 1, 1258)]) (q := 1266) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem h1704 : P.leaf 34 1704 = 4608 := by
  exact leaf_contract_factors (k := 34) (b := 18) (H := 1704) (ss := [(6, 1, 466), (26, 1, 472), (18, 11, 475), (33, 14, 486), (35, 14, 487), (27, 1, 508), (15, 1, 509), (14, 1, 524), (16, 1, 529), (11, 1, 536), (12, 1, 803), (31, 1, 872), (30, 1, 515), (29, 1, 915), (34, 1, 915), (32, 1, 522)]) (ids := [0, 1, 2, 3, 5, 6, 7, 8, 11, 15, 17, 18, 19, 20, 21, 26, 22, 23]) (cs := [2, 3, 4, 5, 1, 6, 7, 8, 9, 1, 1, 10, 1, 1, 1, 11, 1, 12, 13, 14, 15, 16, 18, 19, 1, 1, 17, 1, 1, 1, 1, 1, 1, 1]) (bs := [16, 2]) (W := 4608) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem cover1705 : P.CoversSplit 24 10 1705 0xcc00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 515, 517, 522, 524, 566, 573, 860, 872, 915, 1209]) (by decide +kernel)

theorem c1705_0 : P.sumLeaves 24 1745920 960 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1705) (lo := 0) (len := 960) (W := 0) check rows elimOK (by decide) (by decide) cover1705 (by decide)
  decide +kernel

theorem contract1705_1 : P.leaf 30 27295 = 37632 := by
  exact leaf_contract_factors (k := 30) (b := 20) (H := 27295) (ss := [(27, 1, 473), (29, 1, 473), (18, 11, 475), (14, 1, 487), (16, 1, 529), (11, 1, 536), (15, 1, 558), (12, 1, 818), (31, 1, 872), (30, 1, 1209)]) (ids := [0, 1, 2, 3, 4, 5, 6, 7, 8, 11, 15, 17, 18, 19, 20, 21, 24, 26, 22, 23]) (cs := [2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 1, 11, 1, 1, 1, 12, 1, 13, 14, 15, 16, 17, 20, 21, 18, 1, 19, 1, 1, 1]) (bs := [18, 2]) (W := 37632) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1705_1 : P.sumLeaves 24 1746880 64 = 37632 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 27295) rows (by decide) (by decide)).symm.trans contract1705_1

theorem h1705 : P.leaf 34 1705 = 37632 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(960, 0), (64, 37632)]) (.cons c1705_0 (.cons c1705_1 (.nil))) (by decide) (by decide))

theorem h1706 : P.leaf 34 1706 = 25984 := by
  exact leaf_contract_factors (k := 34) (b := 20) (H := 1706) (ss := [(33, 14, 486), (15, 1, 509), (35, 1, 524), (16, 1, 529), (18, 1, 536), (14, 1, 566), (12, 1, 867), (11, 1, 818), (31, 1, 872), (26, 1, 515), (30, 1, 515), (29, 1, 921), (34, 1, 916), (32, 1, 1258)]) (ids := [0, 1, 2, 3, 4, 5, 6, 7, 8, 11, 15, 17, 18, 19, 20, 21, 25, 26, 22, 23]) (cs := [2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 1, 11, 1, 1, 1, 12, 1, 13, 14, 15, 16, 17, 20, 21, 1, 18, 19, 1, 1, 1, 1, 1, 1, 1]) (bs := [18, 2]) (W := 25984) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem cover1707 : P.CoversSplit 24 10 1707 0xff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 517, 522, 524, 565, 566, 573, 860, 872, 921, 1209, 1258]) (by decide +kernel)

theorem c1707_0 : P.sumLeaves 24 1747968 1024 = 185280 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1707) (lo := 0) (len := 1024) (W := 185280) check rows elimOK (by decide) (by decide) cover1707 (by decide)
  decide +kernel

theorem h1707 : P.leaf 34 1707 = 185280 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 185280)]) (.cons c1707_0 (.nil)) (by decide) (by decide))

theorem h1708 : P.leaf 34 1708 = 24320 := by
  exact leaf_contract_factors (k := 34) (b := 20) (H := 1708) (ss := [(6, 1, 466), (26, 1, 472), (27, 1, 508), (35, 1, 524), (11, 1, 475), (16, 1, 529), (33, 1, 566), (18, 1, 536), (12, 1, 867), (31, 1, 872), (30, 1, 515), (29, 1, 915), (34, 1, 915), (32, 1, 522)]) (ids := [0, 1, 2, 3, 5, 6, 7, 8, 11, 12, 13, 15, 17, 18, 19, 20, 21, 26, 22, 23]) (cs := [2, 3, 4, 5, 1, 6, 7, 8, 9, 1, 1, 10, 11, 12, 1, 13, 1, 14, 15, 16, 17, 18, 20, 21, 1, 1, 19, 1, 1, 1, 1, 1, 1, 1]) (bs := [18, 2]) (W := 24320) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem cover1709 : P.CoversSplit 24 10 1709 0xcc00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 515, 517, 522, 524, 566, 573, 872, 915, 1209]) (by decide +kernel)

theorem c1709_0 : P.sumLeaves 24 1750016 1024 = 224768 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1709) (lo := 0) (len := 1024) (W := 224768) check rows elimOK (by decide) (by decide) cover1709 (by decide)
  decide +kernel

theorem h1709 : P.leaf 34 1709 = 224768 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 224768)]) (.cons c1709_0 (.nil)) (by decide) (by decide))

theorem cover1710 : P.CoversSplit 24 10 1710 0xaa00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 515, 517, 522, 524, 566, 573, 872, 916, 921, 1258]) (by decide +kernel)

theorem c1710_0 : P.sumLeaves 24 1751040 1024 = 242096 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1710) (lo := 0) (len := 1024) (W := 242096) check rows elimOK (by decide) (by decide) cover1710 (by decide)
  decide +kernel

theorem h1710 : P.leaf 34 1710 = 242096 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 242096)]) (.cons c1710_0 (.nil)) (by decide) (by decide))

theorem cover1711 : P.CoversSplit 24 10 1711 0xff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 517, 522, 524, 566, 573, 872, 916, 921, 1209, 1258]) (by decide +kernel)

theorem c1711_0 : P.sumLeaves 24 1752064 1024 = 994496 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1711) (lo := 0) (len := 1024) (W := 994496) check rows elimOK (by decide) (by decide) cover1711 (by decide)
  decide +kernel

theorem h1711 : P.leaf 34 1711 = 994496 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 994496)]) (.cons c1711_0 (.nil)) (by decide) (by decide))

theorem cover1715 : P.CoversSplit 24 10 1715 0xff000000000000000000000000000000a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [517, 573, 860, 872, 915, 921, 1209, 1251, 1259, 1308]) (ps := [(8, [531, 580], [517, 573]), (14, [874], [860])]) (by decide +kernel)

theorem c1715_0 : P.sumLeaves 24 1756160 448 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1715) (lo := 0) (len := 448) (W := 0) check rows elimOK (by decide) (by decide) cover1715 (by decide)
  decide +kernel

theorem contract1715_1 : P.leaf 30 27447 = 2560 := by
  exact leaf_contract_factors (k := 30) (b := 12) (H := 27447) (ss := [(2, 1, 453), (5, 1, 453), (31, 1, 468), (6, 1, 478), (12, 1, 460), (8, 1, 580), (27, 1, 573), (18, 1, 580), (11, 1, 818), (29, 1, 921), (13, 1, 922), (14, 1, 923), (19, 1, 929), (15, 1, 930), (30, 1, 1209), (16, 1, 1265), (20, 1, 1657), (21, 1, 1658)]) (ids := [1, 2, 7, 5, 8, 15, 20, 21, 22, 23, 24, 26]) (cs := [1, 2, 3, 1, 1, 5, 1, 4, 6, 1, 1, 1, 1, 1, 1, 7, 1, 1, 1, 1, 8, 9, 10, 11, 12, 1, 13, 1, 1, 1]) (bs := [3, 9]) (W := 2560) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1715_1 : P.sumLeaves 24 1756608 64 = 2560 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 27447) rows (by decide) (by decide)).symm.trans contract1715_1

theorem c1715_2 : P.sumLeaves 24 1756672 512 = 44672 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1715) (lo := 512) (len := 512) (W := 44672) check rows elimOK (by decide) (by decide) cover1715 (by decide)
  decide +kernel

theorem h1715 : P.leaf 34 1715 = 47232 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(448, 0), (64, 2560), (512, 44672)]) (.cons c1715_0 (.cons c1715_1 (.cons c1715_2 (.nil)))) (by decide) (by decide))

theorem cover1716 : P.CoversSplit 24 10 1716 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [559]) (by decide +kernel)

theorem c1716_0 : P.sumLeaves 24 1757184 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1716) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1716 (by decide)
  decide +kernel

theorem h1716 : P.leaf 34 1716 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1716_0 (.nil)) (by decide) (by decide))

theorem cover1717 : P.CoversSplit 24 10 1717 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [559]) (by decide +kernel)

theorem c1717_0 : P.sumLeaves 24 1758208 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1717) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1717 (by decide)
  decide +kernel

theorem h1717 : P.leaf 34 1717 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1717_0 (.nil)) (by decide) (by decide))

theorem cover1718 : P.CoversSplit 24 10 1718 0xff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 517, 573, 860, 867, 872, 915, 916, 921, 1209, 1251, 1259, 1308]) (ps := [(8, [468, 531], [468, 573])]) (by decide +kernel)

theorem c1718_0 : P.sumLeaves 24 1759232 448 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1718) (lo := 0) (len := 448) (W := 0) check rows elimOK (by decide) (by decide) cover1718 (by decide)
  decide +kernel

theorem contract1718_1 : P.leaf 30 27495 = 14920 := by
  exact leaf_contract_factors (k := 30) (b := 16) (H := 27495) (ss := [(8, 1, 468), (5, 1, 475), (27, 1, 573), (18, 1, 580), (31, 1, 872), (29, 1, 916), (13, 1, 922), (14, 1, 923), (16, 1, 486), (9, 1, 510), (19, 1, 929), (30, 1, 1209), (20, 1, 1657), (21, 1, 1658)]) (ids := [0, 1, 2, 4, 8, 9, 10, 13, 15, 20, 21, 24, 26, 5, 22, 23]) (cs := [2, 3, 4, 1, 5, 15, 1, 1, 6, 7, 8, 1, 1, 9, 1, 10, 1, 1, 1, 1, 11, 12, 16, 17, 13, 1, 14, 1, 1, 1]) (bs := [13, 3]) (W := 14920) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1718_1 : P.sumLeaves 24 1759680 64 = 14920 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 27495) rows (by decide) (by decide)).symm.trans contract1718_1

theorem c1718_2 : P.sumLeaves 24 1759744 512 = 180112 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1718) (lo := 512) (len := 512) (W := 180112) check rows elimOK (by decide) (by decide) cover1718 (by decide)
  decide +kernel

theorem h1718 : P.leaf 34 1718 = 195032 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(448, 0), (64, 14920), (512, 180112)]) (.cons c1718_0 (.cons c1718_1 (.cons c1718_2 (.nil)))) (by decide) (by decide))

theorem cover1719 : P.CoversSplit 24 10 1719 0xff000000000000000000000000000000a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [517, 573, 860, 867, 872, 915, 916, 921, 1209, 1251, 1259, 1308]) (ps := [(8, [531, 580], [517, 573])]) (by decide +kernel)

theorem c1719_0 : P.sumLeaves 24 1760256 448 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1719) (lo := 0) (len := 448) (W := 0) check rows elimOK (by decide) (by decide) cover1719 (by decide)
  decide +kernel

theorem contract1719_1 : P.leaf 30 27511 = 31296 := by
  exact leaf_contract_factors (k := 30) (b := 17) (H := 27511) (ss := [(5, 1, 475), (8, 1, 580), (27, 1, 573), (18, 1, 580), (31, 1, 872), (29, 1, 916), (13, 1, 922), (14, 1, 923), (19, 1, 929), (30, 1, 1209), (16, 1, 1265), (20, 1, 1657), (21, 1, 1658)]) (ids := [0, 1, 2, 4, 7, 8, 9, 10, 13, 20, 21, 24, 5, 15, 22, 23, 26]) (cs := [2, 3, 4, 1, 5, 14, 1, 6, 7, 8, 9, 1, 1, 10, 1, 15, 1, 1, 1, 1, 11, 12, 16, 17, 13, 1, 18, 1, 1, 1]) (bs := [12, 5]) (W := 31296) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1719_1 : P.sumLeaves 24 1760704 64 = 31296 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 27511) rows (by decide) (by decide)).symm.trans contract1719_1

theorem c1719_2 : P.sumLeaves 24 1760768 512 = 536776 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1719) (lo := 512) (len := 512) (W := 536776) check rows elimOK (by decide) (by decide) cover1719 (by decide)
  decide +kernel

theorem h1719 : P.leaf 34 1719 = 568072 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(448, 0), (64, 31296), (512, 536776)]) (.cons c1719_0 (.cons c1719_1 (.cons c1719_2 (.nil)))) (by decide) (by decide))

theorem h1720 : P.leaf 34 1720 = 15120 := by
  exact leaf_contract_factors (k := 34) (b := 21) (H := 1720) (ss := [(18, 11, 475), (33, 14, 486), (35, 14, 487), (15, 1, 509), (11, 1, 559), (12, 1, 901), (6, 1, 459), (31, 1, 909), (14, 1, 929), (30, 1, 1209), (32, 1, 1264), (29, 1, 915), (34, 1, 915)]) (ids := [0, 1, 2, 3, 5, 6, 7, 8, 11, 14, 15, 17, 18, 19, 20, 21, 24, 25, 26, 22, 23]) (cs := [2, 3, 4, 5, 1, 6, 7, 8, 9, 1, 1, 10, 1, 1, 11, 12, 1, 13, 14, 15, 16, 17, 21, 22, 18, 19, 20, 1, 1, 1, 1, 1, 1, 1]) (bs := [19, 2]) (W := 15120) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem cover1721 : P.CoversSplit 24 10 1721 0xff000000000000000000000000000000a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 517, 524, 566, 573, 860, 872, 915, 1209, 1251, 1258, 1259, 1264, 1308]) (ps := [(8, [531], [517]), (14, [487, 923], [487, 860])]) (by decide +kernel)

theorem c1721_0 : P.sumLeaves 24 1762304 1024 = 184320 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1721) (lo := 0) (len := 1024) (W := 184320) check rows elimOK (by decide) (by decide) cover1721 (by decide)
  decide +kernel

theorem h1721 : P.leaf 34 1721 = 184320 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 184320)]) (.cons c1721_0 (.nil)) (by decide) (by decide))

theorem cover1722 : P.CoversSplit 24 10 1722 0xff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 517, 524, 566, 573, 860, 872, 921, 1209, 1251, 1259, 1308]) (ps := [(8, [531], [517]), (14, [874], [486])]) (by decide +kernel)

theorem c1722_0 : P.sumLeaves 24 1763328 448 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1722) (lo := 0) (len := 448) (W := 0) check rows elimOK (by decide) (by decide) cover1722 (by decide)
  decide +kernel

theorem contract1722_1 : P.leaf 30 27559 = 7952 := by
  exact leaf_contract_factors (k := 30) (b := 15) (H := 27559) (ss := [(14, 1, 486), (15, 1, 509), (8, 1, 580), (16, 1, 468), (27, 1, 573), (18, 1, 580), (12, 1, 867), (11, 1, 818), (31, 1, 872), (29, 1, 916), (13, 1, 922), (19, 1, 930), (30, 1, 1209), (20, 1, 1657), (21, 1, 1658)]) (ids := [0, 1, 2, 3, 4, 5, 7, 8, 15, 20, 24, 26, 21, 22, 23]) (cs := [2, 3, 4, 5, 6, 7, 1, 8, 9, 1, 1, 1, 1, 1, 1, 10, 1, 1, 1, 1, 11, 14, 15, 16, 12, 1, 13, 1, 1, 1]) (bs := [12, 3]) (W := 7952) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1722_1 : P.sumLeaves 24 1763776 64 = 7952 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 27559) rows (by decide) (by decide)).symm.trans contract1722_1

theorem c1722_2 : P.sumLeaves 24 1763840 512 = 136224 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1722) (lo := 512) (len := 512) (W := 136224) check rows elimOK (by decide) (by decide) cover1722 (by decide)
  decide +kernel

theorem h1722 : P.leaf 34 1722 = 144176 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(448, 0), (64, 7952), (512, 136224)]) (.cons c1722_0 (.cons c1722_1 (.cons c1722_2 (.nil)))) (by decide) (by decide))

theorem cover1723 : P.CoversSplit 24 10 1723 0xff000000000000000000000000000000a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [517, 524, 566, 573, 860, 872, 921, 1209, 1251, 1259, 1308]) (ps := [(8, [531], [517]), (14, [874], [860])]) (by decide +kernel)

theorem c1723_0 : P.sumLeaves 24 1764352 448 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1723) (lo := 0) (len := 448) (W := 0) check rows elimOK (by decide) (by decide) cover1723 (by decide)
  decide +kernel

theorem contract1723_1 : P.leaf 30 27575 = 14592 := by
  exact leaf_contract_factors (k := 30) (b := 15) (H := 27575) (ss := [(8, 1, 580), (27, 1, 573), (18, 1, 580), (12, 1, 867), (11, 1, 818), (31, 1, 872), (29, 1, 921), (13, 1, 922), (14, 1, 923), (19, 1, 965), (15, 1, 930), (30, 1, 1209), (16, 1, 1265), (20, 1, 1657), (21, 1, 1658)]) (ids := [0, 1, 2, 3, 4, 5, 7, 8, 20, 26, 15, 21, 22, 23, 24]) (cs := [2, 3, 4, 5, 6, 7, 1, 8, 9, 1, 1, 1, 1, 1, 1, 12, 1, 1, 1, 1, 10, 13, 14, 15, 16, 1, 11, 1, 1, 1]) (bs := [10, 5]) (W := 14592) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c1723_1 : P.sumLeaves 24 1764800 64 = 14592 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 27575) rows (by decide) (by decide)).symm.trans contract1723_1

theorem c1723_2 : P.sumLeaves 24 1764864 512 = 371184 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1723) (lo := 512) (len := 512) (W := 371184) check rows elimOK (by decide) (by decide) cover1723 (by decide)
  decide +kernel

theorem h1723 : P.leaf 34 1723 = 385776 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(448, 0), (64, 14592), (512, 371184)]) (.cons c1723_0 (.cons c1723_1 (.cons c1723_2 (.nil)))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(1663, 24), (1683, 12), (1684, 48), (1685, 48), (1686, 48), (1687, 48), (1692, 24), (1693, 48), (1695, 24), (1698, 24), (1699, 48), (1700, 48), (1701, 48), (1702, 48), (1703, 48), (1704, 48), (1705, 48), (1706, 48), (1707, 48), (1708, 48), (1709, 48), (1710, 48), (1711, 48), (1715, 24), (1716, 48), (1717, 48), (1718, 48), (1719, 48), (1720, 48), (1721, 48), (1722, 48), (1723, 48)]

theorem segOK : checkSeg 16 perms 1663 1724 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 1663 1724 1380 283869108 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 283869108)
    (SegSum.cons (w := 24) h1663 (SegSum.cons (w := 12) h1683 (SegSum.cons (w := 48) h1684 (SegSum.cons (w := 48) h1685 (SegSum.cons (w := 48) h1686 (SegSum.cons (w := 48) h1687 (SegSum.cons (w := 24) h1692 (SegSum.cons (w := 48) h1693 (SegSum.cons (w := 24) h1695 (SegSum.cons (w := 24) h1698 (SegSum.cons (w := 48) h1699 (SegSum.cons (w := 48) h1700 (SegSum.cons (w := 48) h1701 (SegSum.cons (w := 48) h1702 (SegSum.cons (w := 48) h1703 (SegSum.cons (w := 48) h1704 (SegSum.cons (w := 48) h1705 (SegSum.cons (w := 48) h1706 (SegSum.cons (w := 48) h1707 (SegSum.cons (w := 48) h1708 (SegSum.cons (w := 48) h1709 (SegSum.cons (w := 48) h1710 (SegSum.cons (w := 48) h1711 (SegSum.cons (w := 24) h1715 (SegSum.cons (w := 48) h1716 (SegSum.cons (w := 48) h1717 (SegSum.cons (w := 48) h1718 (SegSum.cons (w := 48) h1719 (SegSum.cons (w := 48) h1720 (SegSum.cons (w := 48) h1721 (SegSum.cons (w := 48) h1722 (SegSum.cons (w := 48) h1723 (show SegSum (P.leaf 34) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S4N1.C0.S12
