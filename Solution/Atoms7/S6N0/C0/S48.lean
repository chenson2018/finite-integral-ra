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

namespace RACert.S6N0.C0.S48

open RACert RACert.Problem

theorem cover79647 : P.CoversSplit 26 10 79647 0xaaaa000000000000000000000000000000000000000000000000000000000000000000000000000005050000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 538, 579, 972, 979, 1273, 1315, 1322, 1658]) (by decide +kernel)

theorem c79647_0 : P.sumLeaves 26 81558528 640 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79647) (lo := 0) (len := 640) (W := 0) check rows elimOK (by decide) (by decide) cover79647 (by decide)
  decide +kernel

theorem contract79647_1 : P.leaf 32 1274362 = 25488 := by
  apply (leaf_contract (k := 32) (b := 17) (H := 1274362) (ss := [(3, 1, 531), (17, 1, 874), (12, 1, 880), (21, 1, 1272), (33, 1, 1273), (30, 0, 1315), (20, 1, 1609), (28, 0, 1658), (32, 1, 579), (8, 0, 530), (26, 1, 629), (14, 1, 873), (18, 0, 1315), (11, 1, 879), (16, 1, 1210)]) (ids := [0, 2, 3, 4, 5, 7, 8, 11, 13, 17, 20, 21, 22, 23, 25, 27, 29]) (cs := [2, 1, 3, 4, 5, 6, 0, 7, 8, 1, 1, 9, 1, 10, 1, 1, 0, 11, 1, 1, 12, 13, 14, 15, 1, 16, 0, 17, 0, 18, 1, 1]) check rows (by decide) (by decide +kernel) (by decide +kernel)).trans
  decide +kernel

theorem c79647_1 : P.sumLeaves 26 81559168 64 = 25488 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1274362) rows (by decide) (by decide)).symm.trans contract79647_1

theorem c79647_2 : P.sumLeaves 26 81559232 320 = 2966824 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79647) (lo := 704) (len := 320) (W := 2966824) check rows elimOK (by decide) (by decide) cover79647 (by decide)
  decide +kernel

theorem h79647 : P.leaf 36 79647 = 2992312 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(640, 0), (64, 25488), (320, 2966824)]) (.cons c79647_0 (.cons c79647_1 (.cons c79647_2 (.nil)))) (by decide) (by decide))

theorem h79653 : P.leaf 36 79653 = 102416 := by
  exact leaf_contract_factors (k := 36) (b := 22) (H := 79653) (ss := [(2, 1, 475), (3, 1, 417), (4, 1, 410), (31, 1, 487), (33, 1, 536), (29, 1, 489), (17, 1, 874), (12, 1, 880), (36, 1, 923), (13, 1, 825), (35, 1, 930), (37, 1, 979), (18, 1, 1217), (34, 1, 1658)]) (ids := [3, 4, 5, 6, 7, 8, 9, 12, 13, 14, 17, 18, 19, 20, 23, 24, 26, 28, 30, 21, 22, 25]) (cs := [1, 1, 1, 2, 3, 4, 5, 6, 7, 8, 1, 1, 9, 10, 11, 1, 1, 12, 13, 14, 15, 21, 22, 16, 17, 23, 18, 1, 19, 1, 20, 1, 1, 1, 1, 1]) (bs := [19, 3]) (W := 102416) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem h79654 : P.leaf 36 79654 = 96768 := by
  exact leaf_contract_factors (k := 36) (b := 21) (H := 79654) (ss := [(7, 1, 468), (8, 1, 486), (3, 1, 524), (12, 1, 825), (13, 1, 461), (37, 17, 874), (17, 1, 880), (14, 1, 465), (29, 1, 489), (31, 1, 489), (18, 1, 517), (33, 1, 538), (35, 1, 930), (36, 1, 1266), (34, 1, 1658)]) (ids := [0, 2, 3, 4, 7, 8, 9, 13, 14, 17, 18, 19, 20, 23, 24, 26, 28, 30, 21, 22, 25]) (cs := [2, 1, 3, 4, 5, 1, 1, 6, 7, 8, 1, 1, 1, 9, 10, 1, 1, 11, 12, 13, 14, 20, 21, 15, 16, 22, 17, 1, 18, 1, 19, 1, 1, 1, 1, 1]) (bs := [18, 3]) (W := 96768) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem cover79655 : P.CoversSplit 26 10 79655 0xcc00cc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 538, 579, 930, 972, 979, 1266, 1658, 1665]) (by decide +kernel)

theorem c79655_0 : P.sumLeaves 26 81566720 1024 = 810040 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79655) (lo := 0) (len := 1024) (W := 810040) check rows elimOK (by decide) (by decide) cover79655 (by decide)
  decide +kernel

theorem h79655 : P.leaf 36 79655 = 810040 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 810040)]) (.cons c79655_0 (.nil)) (by decide) (by decide))

theorem h79656 : P.leaf 36 79656 = 6272 := by
  exact leaf_contract_factors (k := 36) (b := 17) (H := 79656) (ss := [(7, 1, 466), (2, 1, 467), (3, 1, 417), (4, 1, 417), (11, 1, 459), (30, 1, 479), (9, 1, 480), (15, 1, 473), (28, 1, 481), (19, 1, 522), (33, 1, 536), (20, 1, 572), (12, 1, 825), (13, 1, 825), (37, 1, 874), (21, 1, 916), (36, 1, 923), (35, 1, 1273), (34, 1, 1658)]) (ids := [3, 4, 6, 8, 12, 14, 15, 16, 20, 22, 25, 27, 29, 30, 21, 23, 24]) (cs := [1, 1, 1, 2, 3, 1, 4, 1, 5, 1, 1, 1, 6, 1, 7, 8, 9, 1, 1, 1, 10, 16, 11, 17, 18, 12, 1, 13, 1, 14, 15, 1, 1, 1, 1, 1]) (bs := [14, 3]) (W := 6272) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem h79657 : P.leaf 36 79657 = 110336 := by
  exact leaf_contract_factors (k := 36) (b := 22) (H := 79657) (ss := [(9, 1, 480), (3, 1, 524), (19, 1, 522), (15, 1, 473), (33, 1, 536), (20, 1, 572), (12, 1, 880), (21, 1, 916), (36, 1, 923), (28, 1, 481), (7, 1, 460), (30, 1, 481), (13, 1, 825), (34, 1, 1658)]) (ids := [0, 2, 3, 4, 6, 8, 9, 12, 14, 15, 16, 20, 22, 25, 27, 29, 30, 33, 35, 21, 23, 24]) (cs := [2, 1, 3, 4, 5, 1, 6, 1, 7, 8, 1, 1, 9, 1, 10, 11, 12, 1, 1, 1, 13, 21, 14, 22, 23, 15, 1, 16, 1, 17, 18, 1, 1, 19, 1, 20]) (bs := [19, 3]) (W := 110336) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem cover79658 : P.CoversSplit 26 10 79658 0xa0a0a0a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [479, 481, 538, 874, 972, 1266, 1273, 1658]) (by decide +kernel)

theorem c79658_0 : P.sumLeaves 26 81569792 1024 = 100800 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79658) (lo := 0) (len := 1024) (W := 100800) check rows elimOK (by decide) (by decide) cover79658 (by decide)
  decide +kernel

theorem h79658 : P.leaf 36 79658 = 100800 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 100800)]) (.cons c79658_0 (.nil)) (by decide) (by decide))

theorem cover79659 : P.CoversSplit 26 10 79659 0xa0a0a0a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 579, 972, 979, 1266, 1273, 1322, 1658]) (by decide +kernel)

theorem c79659_0 : P.sumLeaves 26 81570816 1024 = 888384 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79659) (lo := 0) (len := 1024) (W := 888384) check rows elimOK (by decide) (by decide) cover79659 (by decide)
  decide +kernel

theorem h79659 : P.leaf 36 79659 = 888384 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 888384)]) (.cons c79659_0 (.nil)) (by decide) (by decide))

theorem cover79660 : P.CoversSplit 26 10 79660 0xfffffffa00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [538, 566, 579, 873, 874, 923, 972, 979, 1273, 1658]) (by decide +kernel)

theorem c79660_0 : P.sumLeaves 26 81571840 1024 = 176032 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79660) (lo := 0) (len := 1024) (W := 176032) check rows elimOK (by decide) (by decide) cover79660 (by decide)
  decide +kernel

theorem h79660 : P.leaf 36 79660 = 176032 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 176032)]) (.cons c79660_0 (.nil)) (by decide) (by decide))

theorem cover79661 : P.CoversSplit 26 10 79661 0xfffffffa00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [538, 566, 579, 923, 972, 979, 1273, 1322, 1658]) (by decide +kernel)

theorem c79661_0 : P.sumLeaves 26 81572864 1024 = 869712 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79661) (lo := 0) (len := 1024) (W := 869712) check rows elimOK (by decide) (by decide) cover79661 (by decide)
  decide +kernel

theorem h79661 : P.leaf 36 79661 = 869712 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 869712)]) (.cons c79661_0 (.nil)) (by decide) (by decide))

theorem cover79662 : P.CoversSplit 26 10 79662 0xfffffffa00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [538, 579, 873, 874, 972, 979, 1266, 1273, 1658]) (by decide +kernel)

theorem c79662_0 : P.sumLeaves 26 81573888 1024 = 697264 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79662) (lo := 0) (len := 1024) (W := 697264) check rows elimOK (by decide) (by decide) cover79662 (by decide)
  decide +kernel

theorem h79662 : P.leaf 36 79662 = 697264 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 697264)]) (.cons c79662_0 (.nil)) (by decide) (by decide))

theorem cover79663 : P.CoversSplit 26 10 79663 0xfffffffa00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [538, 579, 972, 979, 1266, 1273, 1315, 1322, 1658]) (by decide +kernel)

theorem c79663_0 : P.sumLeaves 26 81574912 1024 = 3892712 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79663) (lo := 0) (len := 1024) (W := 3892712) check rows elimOK (by decide) (by decide) cover79663 (by decide)
  decide +kernel

theorem h79663 : P.leaf 36 79663 = 3892712 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 3892712)]) (.cons c79663_0 (.nil)) (by decide) (by decide))

theorem cover79670 : P.CoversSplit 26 10 79670 0xcc00cc0000000000000000000000000000000000000000000000000000000000440040000000000044004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 538, 579, 873, 930, 972, 979, 1273, 1658, 1665]) (by decide +kernel)

noncomputable def f79670 (i : ℕ) := rowWeight keep3 twice3 i * P.leaf 26 (81582080 + i)

theorem c79670_0 : rowSum f79670 0 1024 = 889584 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 79670) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover79670 (by decide)
  decide +kernel

theorem sum79670 : rowSum f79670 0 1024 = 889584 :=
  c79670_0

theorem h79670 : P.leaf 36 79670 = 889584 :=
  leaf_weighted (k := 26) (d := 10) (H := 79670) (keep := keep3) (twice := twice3) rows (by decide) (by decide) bal3 (invRow3 (H := 79670) (by decide) (by decide +kernel)) sum79670

theorem cover79671 : P.CoversSplit 26 10 79671 0xcc00cc0000000000000000000000000000000000000000000000000000000000440040000000000044004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 538, 579, 930, 972, 979, 1658, 1665]) (by decide +kernel)

noncomputable def f79671 (i : ℕ) := rowWeight keep3 twice3 i * P.leaf 26 (81583104 + i)

theorem c79671_0 : rowSum f79671 0 1024 = 4524360 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 79671) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover79671 (by decide)
  decide +kernel

theorem sum79671 : rowSum f79671 0 1024 = 4524360 :=
  c79671_0

theorem h79671 : P.leaf 36 79671 = 4524360 :=
  leaf_weighted (k := 26) (d := 10) (H := 79671) (keep := keep3) (twice := twice3) rows (by decide) (by decide) bal3 (invRow3 (H := 79671) (by decide) (by decide +kernel)) sum79671

theorem h79672 : P.leaf 36 79672 = 34016 := by
  exact leaf_contract_factors (k := 36) (b := 20) (H := 79672) (ss := [(2, 1, 467), (7, 1, 474), (9, 1, 480), (12, 1, 825), (13, 1, 825), (11, 1, 459), (37, 1, 874), (15, 1, 916), (21, 1, 916), (36, 1, 923), (28, 1, 481), (30, 1, 481), (33, 1, 1273), (35, 1, 1273), (20, 1, 1609), (34, 1, 1658)]) (ids := [1, 2, 3, 4, 6, 8, 12, 14, 15, 16, 17, 20, 22, 25, 27, 29, 30, 21, 23, 24]) (cs := [1, 2, 3, 4, 5, 1, 6, 1, 7, 1, 1, 1, 8, 1, 9, 10, 11, 12, 1, 1, 13, 19, 14, 20, 21, 15, 1, 16, 1, 17, 18, 1, 1, 1, 1, 1]) (bs := [17, 3]) (W := 34016) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem cover79673 : P.CoversSplit 26 10 79673 0xa0a0a0a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 579, 923, 930, 979, 1273, 1322, 1658]) (by decide +kernel)

theorem c79673_0 : P.sumLeaves 26 81585152 960 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79673) (lo := 0) (len := 960) (W := 0) check rows elimOK (by decide) (by decide) cover79673 (by decide)
  decide +kernel

theorem contract79673_1 : P.leaf 32 1274783 = 538752 := by
  exact leaf_contract_factors (k := 32) (b := 22) (H := 1274783) (ss := [(9, 1, 480), (28, 1, 481), (30, 1, 481), (12, 1, 880), (7, 1, 460), (13, 1, 825), (15, 1, 916), (21, 1, 916), (33, 1, 1273), (20, 1, 1609)]) (ids := [0, 1, 2, 3, 4, 6, 8, 9, 12, 14, 15, 16, 17, 20, 22, 27, 29, 30, 21, 23, 24, 25]) (cs := [2, 3, 4, 5, 6, 1, 7, 1, 8, 9, 1, 1, 10, 1, 11, 12, 13, 14, 1, 1, 15, 20, 16, 21, 22, 23, 1, 17, 1, 18, 19, 1]) (bs := [18, 4]) (W := 538752) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c79673_1 : P.sumLeaves 26 81586112 64 = 538752 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1274783) rows (by decide) (by decide)).symm.trans contract79673_1

theorem h79673 : P.leaf 36 79673 = 538752 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(960, 0), (64, 538752)]) (.cons c79673_0 (.cons c79673_1 (.nil))) (by decide) (by decide))

theorem cover79674 : P.CoversSplit 26 10 79674 0xa0a0a0a000000000000000000000000000000000000000000000000000000000000000000000000000005050000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 579, 873, 874, 972, 1273, 1658]) (by decide +kernel)

theorem c79674_0 : P.sumLeaves 26 81586176 1024 = 1174048 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79674) (lo := 0) (len := 1024) (W := 1174048) check rows elimOK (by decide) (by decide) cover79674 (by decide)
  decide +kernel

theorem h79674 : P.leaf 36 79674 = 1174048 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1174048)]) (.cons c79674_0 (.nil)) (by decide) (by decide))

theorem cover79675 : P.CoversSplit 26 10 79675 0xa0a0a0a000000000000000000000000000000000000000000000000000000000000000000000000000005050000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 579, 972, 979, 1273, 1322, 1658]) (by decide +kernel)

theorem c79675_0 : P.sumLeaves 26 81587200 640 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79675) (lo := 0) (len := 640) (W := 0) check rows elimOK (by decide) (by decide) cover79675 (by decide)
  decide +kernel

theorem contract79675_1 : P.leaf 32 1274810 = 53632 := by
  exact leaf_contract_factors (k := 32) (b := 20) (H := 1274810) (ss := [(3, 1, 531), (12, 1, 880), (21, 1, 929), (28, 0, 972), (32, 0, 481), (30, 1, 579), (7, 0, 481), (10, 1, 873), (13, 0, 972), (11, 1, 818), (33, 1, 1273), (20, 1, 1609)]) (ids := [0, 2, 3, 4, 6, 7, 12, 13, 14, 15, 16, 17, 20, 21, 22, 23, 27, 29, 24, 25]) (cs := [2, 1, 3, 4, 5, 0, 6, 7, 1, 1, 1, 0, 8, 9, 10, 11, 12, 13, 1, 1, 14, 15, 16, 17, 20, 21, 0, 18, 1, 19, 0, 1]) (bs := [18, 2]) (W := 53632) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c79675_1 : P.sumLeaves 26 81587840 64 = 53632 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1274810) rows (by decide) (by decide)).symm.trans contract79675_1

theorem c79675_2 : P.sumLeaves 26 81587904 320 = 3954640 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79675) (lo := 704) (len := 320) (W := 3954640) check rows elimOK (by decide) (by decide) cover79675 (by decide)
  decide +kernel

theorem h79675 : P.leaf 36 79675 = 4008272 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(640, 0), (64, 53632), (320, 3954640)]) (.cons c79675_0 (.cons c79675_1 (.cons c79675_2 (.nil)))) (by decide) (by decide))

theorem cover79676 : P.CoversSplit 26 10 79676 0xfffffffa00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [538, 579, 873, 874, 923, 972, 979, 1273, 1658]) (by decide +kernel)

theorem c79676_0 : P.sumLeaves 26 81588224 1024 = 2403192 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79676) (lo := 0) (len := 1024) (W := 2403192) check rows elimOK (by decide) (by decide) cover79676 (by decide)
  decide +kernel

theorem h79676 : P.leaf 36 79676 = 2403192 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 2403192)]) (.cons c79676_0 (.nil)) (by decide) (by decide))

theorem cover79677 : P.CoversSplit 26 10 79677 0xfffffffa00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [538, 579, 923, 930, 972, 979, 1273, 1315, 1322, 1658]) (by decide +kernel)

theorem c79677_0 : P.sumLeaves 26 81589248 1024 = 6476448 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79677) (lo := 0) (len := 1024) (W := 6476448) check rows elimOK (by decide) (by decide) cover79677 (by decide)
  decide +kernel

theorem h79677 : P.leaf 36 79677 = 6476448 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 6476448)]) (.cons c79677_0 (.nil)) (by decide) (by decide))

theorem cover79678 : P.CoversSplit 26 10 79678 0xfffffffa00000000000000000000000000000000000000000000000000000000555550500000000055555050000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [538, 579, 873, 874, 972, 979, 1273, 1315, 1658]) (by decide +kernel)

theorem c79678_0 : P.sumLeaves 26 81590272 1024 = 8615360 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79678) (lo := 0) (len := 1024) (W := 8615360) check rows elimOK (by decide) (by decide) cover79678 (by decide)
  decide +kernel

theorem h79678 : P.leaf 36 79678 = 8615360 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 8615360)]) (.cons c79678_0 (.nil)) (by decide) (by decide))

theorem cover79679 : P.CoversSplit 26 10 79679 0xfffffffa00000000000000000000000000000000000000000000000000000000555550500000000055555050000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [538, 579, 972, 979, 1273, 1315, 1322, 1658]) (by decide +kernel)

theorem c79679_0 : P.sumLeaves 26 81591296 1024 = 24553540 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79679) (lo := 0) (len := 1024) (W := 24553540) check rows elimOK (by decide) (by decide) cover79679 (by decide)
  decide +kernel

theorem h79679 : P.leaf 36 79679 = 24553540 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 24553540)]) (.cons c79679_0 (.nil)) (by decide) (by decide))

theorem h79689 : P.leaf 36 79689 = 109568 := by
  exact leaf_contract_factors (k := 36) (b := 20) (H := 79689) (ss := [(17, 1, 467), (28, 1, 474), (12, 1, 479), (7, 1, 460), (9, 1, 480), (8, 1, 516), (13, 1, 825), (15, 1, 916), (19, 1, 522), (21, 1, 916), (20, 1, 572), (36, 1, 923), (30, 1, 481), (32, 1, 530), (34, 1, 579), (18, 1, 1217)]) (ids := [0, 1, 2, 3, 4, 8, 9, 12, 14, 20, 25, 27, 29, 31, 33, 35, 21, 22, 23, 24]) (cs := [2, 3, 4, 5, 6, 1, 1, 1, 7, 8, 1, 1, 9, 1, 10, 1, 1, 1, 1, 1, 11, 18, 19, 20, 21, 12, 1, 13, 1, 14, 1, 15, 1, 16, 1, 17]) (bs := [16, 4]) (W := 109568) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem h79691 : P.leaf 36 79691 = 532608 := by
  exact leaf_contract_factors (k := 36) (b := 22) (H := 79691) (ss := [(12, 1, 479), (28, 1, 523), (9, 1, 529), (17, 1, 874), (8, 1, 516), (21, 1, 929), (30, 1, 972), (32, 1, 530), (34, 1, 579), (36, 1, 972), (13, 1, 825), (18, 1, 1217), (19, 1, 1259), (20, 1, 1609)]) (ids := [0, 1, 2, 3, 4, 5, 8, 9, 12, 13, 14, 20, 21, 25, 27, 29, 31, 33, 35, 22, 23, 24]) (cs := [2, 3, 4, 5, 6, 7, 1, 1, 8, 9, 1, 1, 10, 11, 12, 1, 1, 1, 1, 1, 13, 14, 21, 22, 23, 15, 1, 16, 1, 17, 1, 18, 1, 19, 1, 20]) (bs := [19, 3]) (W := 532608) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem h79692 : P.leaf 36 79692 = 214416 := by
  exact leaf_contract_factors (k := 36) (b := 21) (H := 79692) (ss := [(32, 1, 467), (8, 1, 472), (3, 1, 479), (9, 1, 529), (19, 1, 522), (28, 1, 530), (37, 17, 874), (17, 1, 880), (15, 1, 916), (20, 1, 572), (21, 1, 916), (36, 1, 923), (18, 1, 1217), (16, 1, 515), (34, 1, 1658)]) (ids := [0, 2, 3, 4, 5, 8, 9, 10, 11, 12, 20, 21, 25, 27, 28, 29, 31, 33, 22, 23, 24]) (cs := [2, 1, 3, 4, 5, 6, 1, 1, 7, 8, 9, 10, 11, 1, 1, 1, 1, 1, 1, 1, 12, 13, 20, 21, 22, 14, 1, 15, 16, 17, 1, 18, 1, 19, 1, 1]) (bs := [18, 3]) (W := 214416) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem cover79693 : P.CoversSplit 26 10 79693 0xaaaa0000aaaa00000000000000000000aaa80000aaa8000000000000000000000000000000000000000000000000000000000000000000000000000000000000aaaa0000aaaa00000000000000000000aa8800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 579, 923, 930, 979, 1322, 1658]) (by decide +kernel)

theorem c79693_0 : P.sumLeaves 26 81605632 320 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79693) (lo := 0) (len := 320) (W := 0) check rows elimOK (by decide) (by decide) cover79693 (by decide)
  decide +kernel

theorem contract79693_1 : P.leaf 32 1275093 = 26752 := by
  exact leaf_contract_factors (k := 32) (b := 17) (H := 1275093) (ss := [(2, 1, 475), (3, 1, 524), (9, 1, 529), (15, 1, 473), (19, 1, 522), (28, 1, 530), (32, 1, 530), (20, 1, 572), (4, 1, 580), (5, 1, 586), (17, 1, 874), (8, 1, 516), (21, 1, 916), (18, 1, 1217), (33, 1, 1322)]) (ids := [4, 5, 8, 9, 10, 11, 12, 14, 21, 25, 27, 29, 20, 22, 23, 24, 28]) (cs := [1, 1, 1, 1, 2, 3, 1, 1, 4, 5, 6, 7, 8, 1, 9, 1, 1, 1, 1, 1, 14, 10, 15, 16, 17, 11, 1, 12, 18, 13, 1, 1]) (bs := [12, 5]) (W := 26752) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c79693_1 : P.sumLeaves 26 81605952 64 = 26752 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1275093) rows (by decide) (by decide)).symm.trans contract79693_1

theorem c79693_2 : P.sumLeaves 26 81606016 64 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79693) (lo := 384) (len := 64) (W := 0) check rows elimOK (by decide) (by decide) cover79693 (by decide)
  decide +kernel

theorem contract79693_3 : P.leaf 32 1275095 = 227712 := by
  exact leaf_contract_factors (k := 32) (b := 20) (H := 1275095) (ss := [(9, 1, 529), (28, 1, 530), (32, 1, 530), (3, 1, 531), (19, 1, 522), (15, 1, 473), (20, 1, 572), (4, 1, 580), (17, 1, 874), (8, 1, 516), (21, 1, 916), (18, 1, 1217)]) (ids := [0, 3, 4, 5, 8, 9, 10, 11, 14, 20, 21, 25, 27, 28, 29, 31, 12, 22, 23, 24]) (cs := [2, 1, 1, 3, 4, 5, 1, 1, 6, 7, 8, 9, 18, 1, 10, 1, 1, 1, 1, 1, 11, 12, 19, 20, 21, 13, 1, 14, 15, 16, 1, 17]) (bs := [16, 4]) (W := 227712) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c79693_3 : P.sumLeaves 26 81606080 64 = 227712 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1275095) rows (by decide) (by decide)).symm.trans contract79693_3

theorem c79693_4 : P.sumLeaves 26 81606144 320 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79693) (lo := 512) (len := 320) (W := 0) check rows elimOK (by decide) (by decide) cover79693 (by decide)
  decide +kernel

theorem contract79693_5 : P.leaf 32 1275101 = 84768 := by
  exact leaf_contract_factors (k := 32) (b := 19) (H := 1275101) (ss := [(2, 1, 475), (3, 1, 524), (9, 1, 529), (15, 1, 473), (19, 1, 522), (28, 1, 530), (32, 1, 530), (20, 1, 572), (5, 1, 586), (17, 1, 874), (8, 1, 516), (21, 1, 916), (18, 1, 1217)]) (ids := [2, 4, 5, 8, 9, 10, 11, 12, 14, 20, 21, 25, 27, 28, 29, 31, 22, 23, 24]) (cs := [1, 1, 2, 1, 3, 4, 1, 1, 5, 6, 7, 8, 9, 1, 10, 1, 1, 1, 1, 1, 11, 12, 18, 19, 20, 13, 1, 14, 15, 16, 1, 17]) (bs := [16, 3]) (W := 84768) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c79693_5 : P.sumLeaves 26 81606464 64 = 84768 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1275101) rows (by decide) (by decide)).symm.trans contract79693_5

theorem c79693_6 : P.sumLeaves 26 81606528 128 = 603776 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79693) (lo := 896) (len := 128) (W := 603776) check rows elimOK (by decide) (by decide) cover79693 (by decide)
  decide +kernel

theorem h79693 : P.leaf 36 79693 = 943008 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(320, 0), (64, 26752), (64, 0), (64, 227712), (320, 0), (64, 84768), (128, 603776)]) (.cons c79693_0 (.cons c79693_1 (.cons c79693_2 (.cons c79693_3 (.cons c79693_4 (.cons c79693_5 (.cons c79693_6 (.nil)))))))) (by decide) (by decide))

theorem h79694 : P.leaf 36 79694 = 575624 := by
  exact leaf_contract_factors (k := 36) (b := 22) (H := 79694) (ss := [(3, 1, 479), (8, 1, 523), (9, 1, 529), (37, 17, 874), (17, 1, 880), (18, 1, 1217), (16, 1, 515), (19, 1, 1259), (21, 1, 1259), (36, 1, 1266), (28, 1, 530), (32, 1, 530), (20, 1, 1609), (34, 1, 1658)]) (ids := [0, 2, 3, 4, 5, 8, 9, 10, 11, 12, 13, 20, 21, 25, 27, 28, 29, 31, 33, 22, 23, 24]) (cs := [2, 1, 3, 4, 5, 6, 1, 1, 7, 8, 9, 10, 11, 12, 1, 1, 1, 1, 1, 1, 13, 14, 21, 22, 23, 15, 1, 16, 17, 18, 1, 19, 1, 20, 1, 1]) (bs := [19, 3]) (W := 575624) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem cover79695 : P.CoversSplit 26 10 79695 0xaaaa0000aaaa00000000000000000000aaa80000aaa8000000000000000000000000000000000000000000000000000000000000000000000000000000000000aaaa0000aaaa00000000000000000000aa8800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 579, 930, 972, 979, 1266, 1273, 1322, 1658]) (by decide +kernel)

theorem c79695_0 : P.sumLeaves 26 81607680 320 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79695) (lo := 0) (len := 320) (W := 0) check rows elimOK (by decide) (by decide) cover79695 (by decide)
  decide +kernel

theorem contract79695_1 : P.leaf 32 1275125 = 120576 := by
  exact leaf_contract_factors (k := 32) (b := 19) (H := 1275125) (ss := [(3, 1, 524), (9, 1, 529), (28, 1, 530), (32, 1, 530), (4, 1, 580), (5, 1, 586), (17, 1, 874), (8, 1, 516), (18, 1, 1217), (19, 1, 1259), (21, 1, 1259), (33, 1, 1322), (20, 1, 1609)]) (ids := [4, 5, 8, 9, 10, 11, 12, 14, 21, 25, 27, 29, 0, 13, 20, 22, 23, 24, 28]) (cs := [14, 1, 1, 1, 2, 3, 1, 1, 4, 5, 6, 7, 8, 15, 9, 1, 1, 1, 1, 1, 16, 10, 17, 18, 19, 11, 1, 12, 20, 13, 1, 1]) (bs := [12, 7]) (W := 120576) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c79695_1 : P.sumLeaves 26 81608000 64 = 120576 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1275125) rows (by decide) (by decide)).symm.trans contract79695_1

theorem c79695_2 : P.sumLeaves 26 81608064 64 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79695) (lo := 384) (len := 64) (W := 0) check rows elimOK (by decide) (by decide) cover79695 (by decide)
  decide +kernel

theorem contract79695_3 : P.leaf 32 1275127 = 514880 := by
  exact leaf_contract_factors (k := 32) (b := 21) (H := 1275127) (ss := [(9, 1, 529), (28, 1, 530), (32, 1, 530), (3, 1, 531), (4, 1, 580), (17, 1, 874), (8, 1, 516), (18, 1, 1217), (19, 1, 1259), (21, 1, 1259), (20, 1, 1609)]) (ids := [3, 4, 5, 8, 9, 10, 11, 13, 14, 20, 21, 25, 27, 28, 29, 31, 0, 12, 22, 23, 24]) (cs := [18, 1, 1, 2, 3, 4, 1, 1, 5, 6, 7, 8, 19, 9, 10, 1, 1, 1, 1, 1, 11, 12, 20, 21, 22, 13, 1, 14, 15, 16, 1, 17]) (bs := [16, 5]) (W := 514880) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c79695_3 : P.sumLeaves 26 81608128 64 = 514880 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1275127) rows (by decide) (by decide)).symm.trans contract79695_3

theorem c79695_4 : P.sumLeaves 26 81608192 320 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79695) (lo := 512) (len := 320) (W := 0) check rows elimOK (by decide) (by decide) cover79695 (by decide)
  decide +kernel

theorem contract79695_5 : P.leaf 32 1275133 = 454592 := by
  exact leaf_contract_factors (k := 32) (b := 21) (H := 1275133) (ss := [(3, 1, 524), (9, 1, 529), (28, 1, 530), (32, 1, 530), (5, 1, 586), (17, 1, 874), (8, 1, 516), (18, 1, 1217), (19, 1, 1259), (21, 1, 1259), (20, 1, 1609)]) (ids := [0, 2, 4, 5, 8, 9, 10, 11, 12, 13, 14, 20, 21, 25, 27, 28, 29, 31, 22, 23, 24]) (cs := [2, 1, 3, 1, 4, 5, 1, 1, 6, 7, 8, 9, 10, 11, 12, 1, 1, 1, 1, 1, 13, 14, 20, 21, 22, 15, 1, 16, 17, 18, 1, 19]) (bs := [18, 3]) (W := 454592) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c79695_5 : P.sumLeaves 26 81608512 64 = 454592 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1275133) rows (by decide) (by decide)).symm.trans contract79695_5

theorem c79695_6 : P.sumLeaves 26 81608576 128 = 1663072 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79695) (lo := 896) (len := 128) (W := 1663072) check rows elimOK (by decide) (by decide) cover79695 (by decide)
  decide +kernel

theorem h79695 : P.leaf 36 79695 = 2753120 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(320, 0), (64, 120576), (64, 0), (64, 514880), (320, 0), (64, 454592), (128, 1663072)]) (.cons c79695_0 (.cons c79695_1 (.cons c79695_2 (.cons c79695_3 (.cons c79695_4 (.cons c79695_5 (.cons c79695_6 (.nil)))))))) (by decide) (by decide))

theorem cover79707 : P.CoversSplit 26 10 79707 0xa0a00000a0a000000000000000000000a0a00000a0a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000a0a00000a0a000000000000000000000a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 579, 873, 930, 972, 979, 1322]) (by decide +kernel)

noncomputable def f79707 (i : ℕ) := rowWeight keep3 twice3 i * P.leaf 26 (81619968 + i)

theorem c79707_0 : rowSum f79707 0 1024 = 4098208 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 79707) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover79707 (by decide)
  decide +kernel

theorem sum79707 : rowSum f79707 0 1024 = 4098208 :=
  c79707_0

theorem h79707 : P.leaf 36 79707 = 4098208 :=
  leaf_weighted (k := 26) (d := 10) (H := 79707) (keep := keep3) (twice := twice3) rows (by decide) (by decide) bal3 (invRow3 (H := 79707) (by decide) (by decide +kernel)) sum79707

theorem cover79708 : P.CoversSplit 26 10 79708 0xaaaa0000aaaa00000000000000000000aaa80000aaa800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [467, 530, 880, 923, 979, 1658]) (by decide +kernel)

theorem c79708_0 : P.sumLeaves 26 81620992 1024 = 4259076 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79708) (lo := 0) (len := 1024) (W := 4259076) check rows elimOK (by decide) (by decide) cover79708 (by decide)
  decide +kernel

theorem h79708 : P.leaf 36 79708 = 4259076 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 4259076)]) (.cons c79708_0 (.nil)) (by decide) (by decide))

theorem cover79709 : P.CoversSplit 26 10 79709 0xaaaa0000aaaa00000000000000000000aaa80000aaa8000000000000000000000000000000000000000000000000000000000000000000000000000000000000aaaa0000aaaa00000000000000000000aa8800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 579, 923, 930, 979, 1322, 1658]) (by decide +kernel)

theorem c79709_0 : P.sumLeaves 26 81622016 1024 = 10082304 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79709) (lo := 0) (len := 1024) (W := 10082304) check rows elimOK (by decide) (by decide) cover79709 (by decide)
  decide +kernel

theorem h79709 : P.leaf 36 79709 = 10082304 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 10082304)]) (.cons c79709_0 (.nil)) (by decide) (by decide))

theorem cover79710 : P.CoversSplit 26 10 79710 0xaaaa0000aaaa00000000000000000000aaa80000aaa800000000000000000000000000000000000005050000050500000000000000000000050400000500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 579, 873, 880, 979, 1315, 1658, 1665]) (by decide +kernel)

theorem c79710_0 : P.sumLeaves 26 81623040 1024 = 9591805 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79710) (lo := 0) (len := 1024) (W := 9591805) check rows elimOK (by decide) (by decide) cover79710 (by decide)
  decide +kernel

theorem h79710 : P.leaf 36 79710 = 9591805 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 9591805)]) (.cons c79710_0 (.nil)) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(79647, 720), (79653, 360), (79654, 720), (79655, 720), (79656, 360), (79657, 720), (79658, 720), (79659, 720), (79660, 720), (79661, 720), (79662, 720), (79663, 720), (79670, 360), (79671, 360), (79672, 720), (79673, 720), (79674, 720), (79675, 720), (79676, 720), (79677, 720), (79678, 720), (79679, 720), (79689, 180), (79691, 720), (79692, 360), (79693, 720), (79694, 720), (79695, 720), (79707, 360), (79708, 720), (79709, 720), (79710, 720)]

theorem segOK : checkSeg 20 perms 79647 79711 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 79647 79711 20340 66326798160 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 66326798160)
    (SegSum.cons (w := 720) h79647 (SegSum.cons (w := 360) h79653 (SegSum.cons (w := 720) h79654 (SegSum.cons (w := 720) h79655 (SegSum.cons (w := 360) h79656 (SegSum.cons (w := 720) h79657 (SegSum.cons (w := 720) h79658 (SegSum.cons (w := 720) h79659 (SegSum.cons (w := 720) h79660 (SegSum.cons (w := 720) h79661 (SegSum.cons (w := 720) h79662 (SegSum.cons (w := 720) h79663 (SegSum.cons (w := 360) h79670 (SegSum.cons (w := 360) h79671 (SegSum.cons (w := 720) h79672 (SegSum.cons (w := 720) h79673 (SegSum.cons (w := 720) h79674 (SegSum.cons (w := 720) h79675 (SegSum.cons (w := 720) h79676 (SegSum.cons (w := 720) h79677 (SegSum.cons (w := 720) h79678 (SegSum.cons (w := 720) h79679 (SegSum.cons (w := 180) h79689 (SegSum.cons (w := 720) h79691 (SegSum.cons (w := 360) h79692 (SegSum.cons (w := 720) h79693 (SegSum.cons (w := 720) h79694 (SegSum.cons (w := 720) h79695 (SegSum.cons (w := 360) h79707 (SegSum.cons (w := 720) h79708 (SegSum.cons (w := 720) h79709 (SegSum.cons (w := 720) h79710 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S48
