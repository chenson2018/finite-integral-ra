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

theorem cover3707 : P.CoversSplit 24 10 3707 0xcc00cc00cc0000000000000000000000cc00cc00cc00000000330033003300000000000000000000003300330000000000000000000000000033003300000000cc00cc00cc0000000000000000000000cc00cc008000000000330033002000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [474, 572, 573, 915, 1209, 1217, 1258]) (ps := [(8, [1217], [572, 1266]), (14, [1217], [915, 1266])]) (by decide +kernel)

noncomputable def f3707 (i : ℕ) := rowWeight keep3 twice3 i * P.leaf 24 (3795968 + i)

theorem c3707_0 : rowSum f3707 0 1024 = 3814309 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 3707) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover3707 (by decide)
  decide +kernel

theorem sum3707 : rowSum f3707 0 1024 = 3814309 :=
  c3707_0

theorem h3707 : P.leaf 34 3707 = 3814309 :=
  leaf_weighted (k := 24) (d := 10) (H := 3707) (keep := keep3) (twice := twice3) rows (by decide) (by decide) (bal3) (invRow3 (H := 3707) (by decide) (by decide +kernel)) sum3707

theorem h1663 : P.leaf 34 1663 = 3814309 :=
  orient5 (v := 3707) (by decide) (by decide +kernel) h3707

theorem cover1683 : P.CoversSplit 24 10 1683 0xaa000000000000000000000000000000a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000088000000000000000000000000000000aa0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [516, 528, 536, 921, 1209, 1259]) (ps := [(8, [580], [573]), (14, [874], [860])]) (by decide +kernel)

theorem h1683 : P.leaf 34 1683 = 8933 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 1683) (keep := keep4) (twice := twice4) rows (by decide) (by decide) bal4 (invRow4 (H := 1683) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1683) (weight := rowWeight keep4 twice4) (xs := [377, 379, 381, 383, 507, 511, 893, 895, 1017, 1019, 1021, 1023]) check rows elimOK (by decide) (by decide) cover1683 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1684 : P.CoversSplit 24 10 1684 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [559]) (by decide +kernel)

theorem h1684 : P.leaf 34 1684 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1684) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1684) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1684 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1685 : P.CoversSplit 24 10 1685 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [559]) (by decide +kernel)

theorem h1685 : P.leaf 34 1685 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1685) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1685) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1685 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1686 : P.CoversSplit 24 10 1686 0xaa00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000088000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 479, 516, 536, 860, 872, 916, 921, 1209, 1251, 1259]) (ps := [(8, [468, 531, 537], [468, 573])]) (by decide +kernel)

theorem h1686 : P.leaf 34 1686 = 60416 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1686) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1686) (weight := fun _ => 1) (xs := [507, 511, 1017, 1019, 1021, 1023]) check rows elimOK (by decide) (by decide) cover1686 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1687 : P.CoversSplit 24 10 1687 0xaa000000000000000000000000000000a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000088000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [516, 528, 536, 860, 916, 921, 1209, 1259]) (ps := [(8, [580], [573]), (14, [965], [1266])]) (by decide +kernel)

theorem h1687 : P.leaf 34 1687 = 128784 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1687) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1687) (weight := fun _ => 1) (xs := [507, 511, 893, 895, 1017, 1019, 1021, 1023]) check rows elimOK (by decide) (by decide) cover1687 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1692 : P.CoversSplit 24 10 1692 0xa8000000000000000000000000000000a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000088000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 508, 516, 524, 536, 573, 860, 872, 915, 1209, 1251, 1259, 1264]) (ps := [(8, [537], [1266])]) (by decide +kernel)

theorem h1692 : P.leaf 34 1692 = 15056 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 1692) (keep := keep4) (twice := twice4) rows (by decide) (by decide) bal4 (invRow4 (H := 1692) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1692) (weight := rowWeight keep4 twice4) (xs := [507, 511, 893, 895, 1019, 1021, 1023]) check rows elimOK (by decide) (by decide) cover1692 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1693 : P.CoversSplit 24 10 1693 0xaa000000000000000000000000000000a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000088000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 516, 517, 524, 528, 573, 860, 915, 1209, 1259, 1264]) (ps := [(8, [615], [1266])]) (by decide +kernel)

theorem h1693 : P.leaf 34 1693 = 230080 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1693) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1693) (weight := fun _ => 1) (xs := [507, 511, 893, 895, 1017, 1019, 1021, 1023]) check rows elimOK (by decide) (by decide) cover1693 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1695 : P.CoversSplit 24 10 1695 0xaa000000000000000000000000000000a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000088000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [516, 517, 524, 528, 573, 860, 916, 921, 1209, 1259]) (ps := [(8, [615], [1266])]) (by decide +kernel)

theorem h1695 : P.leaf 34 1695 = 644896 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 1695) (keep := keep4) (twice := twice4) rows (by decide) (by decide) bal4 (invRow4 (H := 1695) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1695) (weight := rowWeight keep4 twice4) (xs := [507, 511, 893, 895, 1017, 1019, 1021, 1023]) check rows elimOK (by decide) (by decide) cover1695 (by decide) (by decide) (by decide +kernel)
  decide +kernel

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

theorem cover1704 : P.CoversSplit 24 10 1704 0x8800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 508, 515, 517, 522, 524, 566, 573, 860, 872, 915]) (by decide +kernel)

theorem h1704 : P.leaf 34 1704 = 4608 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1704) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1704) (weight := fun _ => 1) (xs := [1019, 1023]) check rows elimOK (by decide) (by decide) cover1704 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1705 : P.CoversSplit 24 10 1705 0xcc00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 515, 517, 522, 524, 566, 573, 860, 872, 915, 1209]) (by decide +kernel)

theorem h1705 : P.leaf 34 1705 = 37632 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1705) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1705) (weight := fun _ => 1) (xs := [1018, 1019, 1022, 1023]) check rows elimOK (by decide) (by decide) cover1705 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1706 : P.CoversSplit 24 10 1706 0xaa00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 515, 517, 522, 524, 565, 566, 573, 860, 872, 921, 1258]) (by decide +kernel)

theorem h1706 : P.leaf 34 1706 = 25984 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1706) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1706) (weight := fun _ => 1) (xs := [1017, 1019, 1021, 1023]) check rows elimOK (by decide) (by decide) cover1706 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1707 : P.CoversSplit 24 10 1707 0xff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 517, 522, 524, 565, 566, 573, 860, 872, 921, 1209, 1258]) (by decide +kernel)

theorem h1707 : P.leaf 34 1707 = 185280 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1707) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1707) (weight := fun _ => 1) (xs := [1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover1707 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1708 : P.CoversSplit 24 10 1708 0x8800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 508, 515, 517, 522, 524, 566, 573, 872, 915]) (by decide +kernel)

theorem h1708 : P.leaf 34 1708 = 24320 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1708) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1708) (weight := fun _ => 1) (xs := [1019, 1023]) check rows elimOK (by decide) (by decide) cover1708 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1709 : P.CoversSplit 24 10 1709 0xcc00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 515, 517, 522, 524, 566, 573, 872, 915, 1209]) (by decide +kernel)

theorem h1709 : P.leaf 34 1709 = 224768 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1709) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1709) (weight := fun _ => 1) (xs := [1018, 1019, 1022, 1023]) check rows elimOK (by decide) (by decide) cover1709 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1710 : P.CoversSplit 24 10 1710 0xaa00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 515, 517, 522, 524, 566, 573, 872, 916, 921, 1258]) (by decide +kernel)

theorem h1710 : P.leaf 34 1710 = 242096 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1710) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1710) (weight := fun _ => 1) (xs := [1017, 1019, 1021, 1023]) check rows elimOK (by decide) (by decide) cover1710 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1711 : P.CoversSplit 24 10 1711 0xff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 517, 522, 524, 566, 573, 872, 916, 921, 1209, 1258]) (by decide +kernel)

theorem h1711 : P.leaf 34 1711 = 994496 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1711) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1711) (weight := fun _ => 1) (xs := [1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover1711 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover2711 : P.CoversSplit 24 10 2711 0xaa000000000000000000000000000000a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000088000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [516, 517, 528, 536, 916, 921, 1210, 1251, 1259, 1264]) (ps := [(8, [580, 615], [573, 1266]), (14, [880], [859])]) (by decide +kernel)

theorem h2711 : P.leaf 34 2711 = 47232 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 2711) (keep := keep5) (twice := twice5) rows (by decide) (by decide) bal5 (invRow5 (H := 2711) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 2711) (weight := rowWeight keep5 twice5) (xs := [507, 511, 893, 895, 1017, 1019, 1021, 1023]) check rows elimOK (by decide) (by decide) cover2711 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h1715 : P.leaf 34 1715 = 47232 :=
  orient4 (v := 2711) (by decide) (by decide +kernel) h2711

theorem cover1716 : P.CoversSplit 24 10 1716 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [559]) (by decide +kernel)

theorem h1716 : P.leaf 34 1716 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1716) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1716) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1716 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1717 : P.CoversSplit 24 10 1717 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [559]) (by decide +kernel)

theorem h1717 : P.leaf 34 1717 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1717) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1717) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover1717 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1718 : P.CoversSplit 24 10 1718 0xff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 517, 573, 860, 867, 872, 915, 916, 921, 1209, 1251, 1259, 1308]) (ps := [(8, [468, 531], [468, 573])]) (by decide +kernel)

theorem h1718 : P.leaf 34 1718 = 195032 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1718) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1718) (weight := fun _ => 1) (xs := [506, 507, 510, 511, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover1718 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1719 : P.CoversSplit 24 10 1719 0xff000000000000000000000000000000a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [517, 573, 860, 867, 872, 915, 916, 921, 1209, 1251, 1259, 1308]) (ps := [(8, [531, 580], [517, 573])]) (by decide +kernel)

theorem h1719 : P.leaf 34 1719 = 568072 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1719) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1719) (weight := fun _ => 1) (xs := [506, 507, 510, 511, 893, 895, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover1719 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover2758 : P.CoversSplit 24 10 2758 0xaa00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 475, 515, 516, 522, 536, 566, 573, 859, 879, 915, 916, 921, 1258]) (ps := [(14, [965], [479])]) (by decide +kernel)

theorem h2758 : P.leaf 34 2758 = 15120 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 2758) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 2758) (weight := fun _ => 1) (xs := [1017, 1019, 1021, 1023]) check rows elimOK (by decide) (by decide) cover2758 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h1720 : P.leaf 34 1720 = 15120 :=
  orient4 (v := 2758) (by decide) (by decide +kernel) h2758

theorem cover2759 : P.CoversSplit 24 10 2759 0xff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [475, 515, 516, 522, 536, 566, 573, 859, 879, 915, 916, 921, 1258]) (ps := [(14, [965], [859, 1266])]) (by decide +kernel)

theorem h2759 : P.leaf 34 2759 = 184320 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 2759) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 2759) (weight := fun _ => 1) (xs := [1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover2759 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h1721 : P.leaf 34 1721 = 184320 :=
  orient4 (v := 2759) (by decide) (by decide +kernel) h2759

theorem cover1722 : P.CoversSplit 24 10 1722 0xff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 517, 524, 566, 573, 860, 872, 921, 1209, 1251, 1259, 1308]) (ps := [(8, [531], [517]), (14, [874], [486])]) (by decide +kernel)

theorem h1722 : P.leaf 34 1722 = 144176 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1722) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1722) (weight := fun _ => 1) (xs := [506, 507, 510, 511, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover1722 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1723 : P.CoversSplit 24 10 1723 0xff000000000000000000000000000000a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [517, 524, 566, 573, 860, 872, 921, 1209, 1251, 1259, 1308]) (ps := [(8, [531], [517]), (14, [874], [860])]) (by decide +kernel)

theorem h1723 : P.leaf 34 1723 = 385776 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1723) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1723) (weight := fun _ => 1) (xs := [506, 507, 510, 511, 893, 895, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover1723 (by decide) (by decide) (by decide +kernel)
  decide +kernel

def seg : List (ℕ × ℕ) := [(1663, 24), (1683, 12), (1684, 48), (1685, 48), (1686, 48), (1687, 48), (1692, 24), (1693, 48), (1695, 24), (1698, 24), (1699, 48), (1700, 48), (1701, 48), (1702, 48), (1703, 48), (1704, 48), (1705, 48), (1706, 48), (1707, 48), (1708, 48), (1709, 48), (1710, 48), (1711, 48), (1715, 24), (1716, 48), (1717, 48), (1718, 48), (1719, 48), (1720, 48), (1721, 48), (1722, 48), (1723, 48)]

theorem segOK : checkSeg 16 perms 1663 1724 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 1663 1724 1380 283869108 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 283869108)
    (SegSum.cons (w := 24) h1663 (SegSum.cons (w := 12) h1683 (SegSum.cons (w := 48) h1684 (SegSum.cons (w := 48) h1685 (SegSum.cons (w := 48) h1686 (SegSum.cons (w := 48) h1687 (SegSum.cons (w := 24) h1692 (SegSum.cons (w := 48) h1693 (SegSum.cons (w := 24) h1695 (SegSum.cons (w := 24) h1698 (SegSum.cons (w := 48) h1699 (SegSum.cons (w := 48) h1700 (SegSum.cons (w := 48) h1701 (SegSum.cons (w := 48) h1702 (SegSum.cons (w := 48) h1703 (SegSum.cons (w := 48) h1704 (SegSum.cons (w := 48) h1705 (SegSum.cons (w := 48) h1706 (SegSum.cons (w := 48) h1707 (SegSum.cons (w := 48) h1708 (SegSum.cons (w := 48) h1709 (SegSum.cons (w := 48) h1710 (SegSum.cons (w := 48) h1711 (SegSum.cons (w := 24) h1715 (SegSum.cons (w := 48) h1716 (SegSum.cons (w := 48) h1717 (SegSum.cons (w := 48) h1718 (SegSum.cons (w := 48) h1719 (SegSum.cons (w := 48) h1720 (SegSum.cons (w := 48) h1721 (SegSum.cons (w := 48) h1722 (SegSum.cons (w := 48) h1723 (show SegSum (P.leaf 34) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S4N1.C0.S12
