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

namespace RACert.S6N0.C0.S49

open RACert RACert.Problem

theorem cover79711 : P.CoversSplit 26 10 79711 0xaaaa0000aaaa00000000000000000000aaa80000aaa8000000000000000000000000000000000000050500000505000000000000000000000504000005000000aaaa0000aaaa00000000000000000000aa8800000000000000000000000000000000000000000000050500000505000000000000000000000504000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 579, 930, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c79711_0 : P.sumLeaves 26 81624064 128 = 4152 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79711) (lo := 0) (len := 128) (W := 4152) check rows elimOK (by decide) (by decide) cover79711 (by decide)
  decide +kernel

theorem contract79711_1 : P.leaf 32 1275378 = 10488 := by
  exact leaf_contract_factors (k := 32) (b := 16) (H := 1275378) (ss := [(22, 1, 433), (2, 1, 482), (3, 1, 531), (4, 1, 580), (7, 1, 825), (17, 1, 874), (18, 8, 1217), (21, 1, 1272), (28, 0, 1315), (30, 0, 530), (32, 1, 579), (8, 0, 530), (14, 1, 516), (5, 1, 629), (16, 1, 1210), (20, 9, 1609)]) (ids := [4, 7, 8, 9, 10, 11, 13, 17, 21, 22, 23, 25, 27, 29, 31, 24]) (cs := [1, 1, 1, 1, 2, 1, 0, 3, 4, 5, 6, 7, 1, 8, 1, 1, 0, 9, 3, 1, 1, 10, 11, 12, 17, 13, 0, 14, 0, 15, 1, 16]) (bs := [15, 1]) (W := 10488) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c79711_1 : P.sumLeaves 26 81624192 64 = 10488 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1275378) rows (by decide) (by decide)).symm.trans contract79711_1

theorem c79711_2 : P.sumLeaves 26 81624256 832 = 25962502 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79711) (lo := 192) (len := 832) (W := 25962502) check rows elimOK (by decide) (by decide) cover79711 (by decide)
  decide +kernel

theorem h79711 : P.leaf 36 79711 = 25977142 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(128, 4152), (64, 10488), (832, 25962502)]) (.cons c79711_0 (.cons c79711_1 (.cons c79711_2 (.nil)))) (by decide) (by decide))

theorem cover79724 : P.CoversSplit 26 10 79724 0xfffffffafffffafa0000000000000000fffcfff8fffcc8c85554555055004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [579, 873, 874, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f79724 (i : ℕ) := rowWeight keep3 twice3 i * P.leaf 26 (81637376 + i)

theorem c79724_0 : rowSum f79724 0 1024 = 6345677 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 79724) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover79724 (by decide)
  decide +kernel

theorem sum79724 : rowSum f79724 0 1024 = 6345677 :=
  c79724_0

theorem h79724 : P.leaf 36 79724 = 6345677 :=
  leaf_weighted (k := 26) (d := 10) (H := 79724) (keep := keep3) (twice := twice3) rows (by decide) (by decide) bal3 (invRow3 (H := 79724) (by decide) (by decide +kernel)) sum79724

theorem cover79725 : P.CoversSplit 26 10 79725 0xfffffffafffffafa0000000000000000fffcfff8fffcc8c855545550550040000000000000000000000000000000000000000000000000000000000000000000fffffffafffffafa0000000000000000ffccffc8cc00c80055445540440040000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [579, 923, 930, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f79725 (i : ℕ) := rowWeight keep3 twice3 i * P.leaf 26 (81638400 + i)

theorem c79725_0 : rowSum f79725 0 875 = 6674766 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 79725) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover79725 (by decide)
  decide +kernel

theorem c79725_1 : rowSum f79725 875 149 = 9762942 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 79725) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover79725 (by decide)
  decide +kernel

theorem sum79725 : rowSum f79725 0 1024 = 16437708 :=
  rowSum_append (F := f79725) (lo := 0) (n := 875) (m := 149) (A := 6674766) (B := 9762942) c79725_0 (c79725_1)

theorem h79725 : P.leaf 36 79725 = 16437708 :=
  leaf_weighted (k := 26) (d := 10) (H := 79725) (keep := keep3) (twice := twice3) rows (by decide) (by decide) bal3 (invRow3 (H := 79725) (by decide) (by decide +kernel)) sum79725

theorem cover79726 : P.CoversSplit 26 10 79726 0xfffffffafffffafa0000000000000000fffcfff8fffcc8c85554555055004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [579, 873, 874, 972, 979, 1266, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c79726_0 : P.sumLeaves 26 81639424 997 = 17143584 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79726) (lo := 0) (len := 997) (W := 17143584) check rows elimOK (by decide) (by decide) cover79726 (by decide)
  decide +kernel

theorem c79726_1 : P.sumLeaves 26 81640421 27 = 14852286 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79726) (lo := 997) (len := 27) (W := 14852286) check rows elimOK (by decide) (by decide) cover79726 (by decide)
  decide +kernel

theorem h79726 : P.leaf 36 79726 = 31995870 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(997, 17143584), (27, 14852286)]) (.cons c79726_0 (.cons c79726_1 (.nil))) (by decide) (by decide))

theorem cover79727 : P.CoversSplit 26 10 79727 0xfffffffafffffafa0000000000000000fffcfff8fffcc8c855545550550040000000000000000000000000000000000000000000000000000000000000000000fffffffafffffafa0000000000000000ffccffc8cc00c80055445540440040000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [579, 930, 972, 979, 1266, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c79727_0 : P.sumLeaves 26 81640448 506 = 27905826 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79727) (lo := 0) (len := 506) (W := 27905826) check rows elimOK (by decide) (by decide) cover79727 (by decide)
  decide +kernel

theorem c79727_1 : P.sumLeaves 26 81640954 483 = 33873408 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79727) (lo := 506) (len := 483) (W := 33873408) check rows elimOK (by decide) (by decide) cover79727 (by decide)
  decide +kernel

theorem c79727_2 : P.sumLeaves 26 81641437 35 = 28846080 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79727) (lo := 989) (len := 35) (W := 28846080) check rows elimOK (by decide) (by decide) cover79727 (by decide)
  decide +kernel

theorem h79727 : P.leaf 36 79727 = 90625314 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(506, 27905826), (483, 33873408), (35, 28846080)]) (.cons c79727_0 (.cons c79727_1 (.cons c79727_2 (.nil)))) (by decide) (by decide))

theorem cover79742 : P.CoversSplit 26 10 79742 0xfffffffafffffafa0000000000000000fffcfff8fffcc8c85554555055004000555550505555505055555050555550500000000000000000555450505500400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [579, 873, 874, 972, 979, 1315, 1322, 1658, 1665]) (ps := [(21, [867], [1658])]) (by decide +kernel)

noncomputable def f79742 (i : ℕ) := rowWeight keep3 twice3 i * P.leaf 26 (81655808 + i)

theorem c79742_0 : rowSum f79742 0 986 = 73324345 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 79742) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover79742 (by decide)
  decide +kernel

theorem c79742_1 : rowSum f79742 986 38 = 49247692 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 79742) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover79742 (by decide)
  decide +kernel

theorem sum79742 : rowSum f79742 0 1024 = 122572037 :=
  rowSum_append (F := f79742) (lo := 0) (n := 986) (m := 38) (A := 73324345) (B := 49247692) c79742_0 (c79742_1)

theorem h79742 : P.leaf 36 79742 = 122572037 :=
  leaf_weighted (k := 26) (d := 10) (H := 79742) (keep := keep3) (twice := twice3) rows (by decide) (by decide) bal3 (invRow3 (H := 79742) (by decide) (by decide +kernel)) sum79742

theorem cover79743 : P.CoversSplit 26 10 79743 0xfffffffafffffafa0000000000000000fffcfff8fffcc8c855545550550040005555505055555050555550505555505055545050555440405554505055004000fffffffafffffafa0000000000000000ffccffc8cc00c80055445540440040005555505055555050555550505555505055445040440040005544504044004000 :=
  coversSplit check rows (by decide) (by decide) (xs := [579, 930, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f79743 (i : ℕ) := rowWeight keep3 twice3 i * P.leaf 26 (81656832 + i)

theorem c79743_0 : rowSum f79743 0 490 = 72859324 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 79743) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover79743 (by decide)
  decide +kernel

theorem c79743_1 : rowSum f79743 490 402 = 113444686 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 79743) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover79743 (by decide)
  decide +kernel

theorem c79743_2 : rowSum f79743 892 132 = 143445494 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 79743) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover79743 (by decide)
  decide +kernel

theorem sum79743 : rowSum f79743 0 1024 = 329749504 :=
  rowSum_append (F := f79743) (lo := 0) (n := 490) (m := 534) (A := 72859324) (B := 256890180) c79743_0 (rowSum_append (F := f79743) (lo := 490) (n := 402) (m := 132) (A := 113444686) (B := 143445494) c79743_1 (c79743_2))

theorem h79743 : P.leaf 36 79743 = 329749504 :=
  leaf_weighted (k := 26) (d := 10) (H := 79743) (keep := keep3) (twice := twice3) rows (by decide) (by decide) bal3 (invRow3 (H := 79743) (by decide) (by decide +kernel)) sum79743

theorem h79753 : P.leaf 36 79753 = 262144 := by
  exact leaf_contract_factors (k := 36) (b := 18) (H := 79753) (ss := [(17, 1, 467), (12, 1, 479), (3, 1, 524), (5, 1, 418), (4, 1, 417), (33, 1, 536), (36, 1, 923), (13, 1, 825), (7, 1, 460), (21, 1, 929), (18, 1, 1217), (8, 1, 516), (19, 1, 1259), (15, 1, 916), (32, 1, 1315), (30, 1, 972), (37, 1, 1322), (35, 1, 1273)]) (ids := [0, 4, 7, 8, 9, 12, 14, 18, 20, 21, 22, 23, 24, 25, 26, 27, 29, 32]) (cs := [2, 1, 1, 1, 3, 1, 1, 4, 5, 6, 1, 1, 7, 1, 8, 1, 1, 1, 9, 1, 10, 11, 12, 13, 14, 15, 16, 17, 1, 18, 1, 1, 19, 1, 1, 1]) (bs := [0, 18]) (W := 262144) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem h79755 : P.leaf 36 79755 = 1404928 := by
  exact leaf_contract_factors (k := 36) (b := 21) (H := 79755) (ss := [(12, 1, 479), (3, 1, 524), (33, 1, 537), (17, 1, 874), (5, 1, 418), (21, 1, 929), (19, 1, 1259), (36, 1, 1266), (13, 1, 825), (18, 1, 1217), (8, 1, 516), (32, 1, 1315), (30, 1, 972), (37, 1, 1322), (35, 1, 1273)]) (ids := [0, 2, 4, 5, 7, 8, 9, 12, 13, 18, 20, 21, 23, 27, 32, 14, 22, 24, 25, 26, 29]) (cs := [2, 1, 3, 1, 4, 5, 1, 6, 7, 8, 1, 1, 9, 10, 17, 1, 1, 1, 11, 1, 12, 13, 18, 14, 19, 20, 21, 15, 1, 22, 1, 1, 16, 1, 1, 1]) (bs := [15, 6]) (W := 1404928) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem h79757 : P.leaf 36 79757 = 1592448 := by
  exact leaf_contract_factors (k := 36) (b := 23) (H := 79757) (ss := [(3, 1, 524), (33, 1, 536), (17, 1, 874), (12, 1, 880), (36, 1, 923), (18, 1, 1217), (8, 1, 516), (21, 1, 1272), (19, 1, 1259), (15, 1, 916), (32, 1, 1315), (37, 1, 1322), (35, 1, 1273)]) (ids := [0, 2, 3, 4, 5, 7, 8, 9, 11, 12, 14, 18, 20, 21, 24, 26, 27, 28, 29, 32, 22, 23, 25]) (cs := [2, 1, 3, 4, 5, 6, 1, 7, 8, 9, 1, 10, 11, 1, 12, 1, 1, 1, 13, 1, 14, 15, 22, 23, 16, 24, 17, 18, 19, 20, 1, 1, 21, 1, 1, 1]) (bs := [20, 3]) (W := 1592448) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem cover79759 : P.CoversSplit 26 10 79759 0xffff000000000000ffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000800000000008800080000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [530, 538, 979, 1266, 1273, 1315, 1322, 1658]) (ps := [(17, [874], [1322])]) (by decide +kernel)

theorem c79759_0 : P.sumLeaves 26 81673216 1024 = 5241760 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79759) (lo := 0) (len := 1024) (W := 5241760) check rows elimOK (by decide) (by decide) cover79759 (by decide)
  decide +kernel

theorem h79759 : P.leaf 36 79759 = 5241760 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 5241760)]) (.cons c79759_0 (.nil)) (by decide) (by decide))

theorem cover79765 : P.CoversSplit 26 10 79765 0xcc00000000000000cc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 538, 923, 930, 972, 979, 1315, 1658, 1665]) (by decide +kernel)

theorem c79765_0 : P.sumLeaves 26 81679360 960 = 323008 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79765) (lo := 0) (len := 960) (W := 323008) check rows elimOK (by decide) (by decide) cover79765 (by decide)
  decide +kernel

theorem contract79765_1 : P.leaf 32 1276255 = 455824 := by
  exact leaf_contract_factors (k := 32) (b := 20) (H := 1276255) (ss := [(2, 1, 475), (29, 1, 489), (31, 1, 489), (3, 1, 531), (33, 1, 538), (17, 1, 874), (12, 1, 880), (13, 1, 825), (18, 1, 1217), (21, 1, 1272), (15, 1, 916), (32, 1, 1315)]) (ids := [2, 3, 4, 5, 6, 7, 8, 9, 12, 14, 17, 18, 20, 21, 23, 24, 26, 28, 22, 25]) (cs := [1, 1, 2, 3, 4, 5, 6, 7, 8, 9, 1, 1, 10, 1, 11, 1, 1, 12, 13, 1, 14, 15, 20, 16, 17, 21, 18, 1, 19, 1, 1, 1]) (bs := [18, 2]) (W := 455824) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c79765_1 : P.sumLeaves 26 81680320 64 = 455824 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1276255) rows (by decide) (by decide)).symm.trans contract79765_1

theorem h79765 : P.leaf 36 79765 = 778832 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(960, 323008), (64, 455824)]) (.cons c79765_0 (.cons c79765_1 (.nil))) (by decide) (by decide))

theorem cover79767 : P.CoversSplit 26 10 79767 0xcc00000000000000cc00000000000000000000000000000000000000000000000c0000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 538, 930, 972, 979, 1315, 1658, 1665]) (by decide +kernel)

theorem c79767_0 : P.sumLeaves 26 81681408 1024 = 3419288 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79767) (lo := 0) (len := 1024) (W := 3419288) check rows elimOK (by decide) (by decide) cover79767 (by decide)
  decide +kernel

theorem h79767 : P.leaf 36 79767 = 3419288 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 3419288)]) (.cons c79767_0 (.nil)) (by decide) (by decide))

theorem cover79772 : P.CoversSplit 26 10 79772 0xffff000000000000ffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [467, 538, 923, 930, 979, 1273, 1322]) (by decide +kernel)

theorem c79772_0 : P.sumLeaves 26 81686528 1024 = 2222272 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79772) (lo := 0) (len := 1024) (W := 2222272) check rows elimOK (by decide) (by decide) cover79772 (by decide)
  decide +kernel

theorem h79772 : P.leaf 36 79772 = 2222272 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 2222272)]) (.cons c79772_0 (.nil)) (by decide) (by decide))

theorem cover79773 : P.CoversSplit 26 10 79773 0xffff000000000000ffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 538, 923, 930, 972, 979, 1273, 1315, 1322]) (by decide +kernel)

theorem c79773_0 : P.sumLeaves 26 81687552 1024 = 8117756 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79773) (lo := 0) (len := 1024) (W := 8117756) check rows elimOK (by decide) (by decide) cover79773 (by decide)
  decide +kernel

theorem h79773 : P.leaf 36 79773 = 8117756 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 8117756)]) (.cons c79773_0 (.nil)) (by decide) (by decide))

theorem cover79774 : P.CoversSplit 26 10 79774 0xffff000000000000ffff000000000000000000000000000000000000000000000f0f0a0a000000000a0a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 538, 873, 972, 979, 1273, 1315, 1322, 1658]) (by decide +kernel)

theorem c79774_0 : P.sumLeaves 26 81688576 640 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79774) (lo := 0) (len := 640) (W := 0) check rows elimOK (by decide) (by decide) cover79774 (by decide)
  decide +kernel

theorem contract79774_1 : P.leaf 32 1276394 = 0 := by
  exact leaf_contract_zero (ss := [(3, 1, 531), (17, 1, 874), (8, 1, 517), (18, 1, 517), (12, 1, 880), (21, 1, 1272), (33, 1, 1273), (30, 0, 1315), (14, 1, 873), (32, 1, 873)]) (q := 1315) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c79774_1 : P.sumLeaves 26 81689216 64 = 0 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1276394) rows (by decide) (by decide)).symm.trans contract79774_1

theorem c79774_2 : P.sumLeaves 26 81689280 320 = 6425864 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79774) (lo := 704) (len := 320) (W := 6425864) check rows elimOK (by decide) (by decide) cover79774 (by decide)
  decide +kernel

theorem h79774 : P.leaf 36 79774 = 6425864 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(640, 0), (64, 0), (320, 6425864)]) (.cons c79774_0 (.cons c79774_1 (.cons c79774_2 (.nil)))) (by decide) (by decide))

theorem cover79775 : P.CoversSplit 26 10 79775 0xffff000000000000ffff000000000000000000000000000000000000000000000f0f0a0a000000000a0a0a0a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 538, 972, 979, 1273, 1315, 1322, 1658]) (by decide +kernel)

theorem c79775_0 : P.sumLeaves 26 81689600 1024 = 19969964 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79775) (lo := 0) (len := 1024) (W := 19969964) check rows elimOK (by decide) (by decide) cover79775 (by decide)
  decide +kernel

theorem h79775 : P.leaf 36 79775 = 19969964 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 19969964)]) (.cons c79775_0 (.nil)) (by decide) (by decide))

theorem cover79781 : P.CoversSplit 26 10 79781 0xcc00cc0000000000cc00cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 538, 559, 873, 923, 930, 979]) (by decide +kernel)

noncomputable def f79781 (i : ℕ) := rowWeight keep3 twice3 i * P.leaf 26 (81695744 + i)

theorem c79781_0 : rowSum f79781 0 1024 = 998592 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 79781) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover79781 (by decide)
  decide +kernel

theorem sum79781 : rowSum f79781 0 1024 = 998592 :=
  c79781_0

theorem h79781 : P.leaf 36 79781 = 998592 :=
  leaf_weighted (k := 26) (d := 10) (H := 79781) (keep := keep3) (twice := twice3) rows (by decide) (by decide) bal3 (invRow3 (H := 79781) (by decide) (by decide +kernel)) sum79781

theorem h79782 : P.leaf 36 79782 = 452608 := by
  exact leaf_contract_factors (k := 36) (b := 22) (H := 79782) (ss := [(7, 1, 468), (8, 1, 486), (3, 1, 524), (12, 1, 825), (13, 1, 461), (37, 17, 874), (17, 1, 880), (14, 1, 465), (29, 1, 489), (31, 1, 489), (18, 1, 517), (33, 1, 538), (35, 1, 930), (36, 1, 1266)]) (ids := [0, 2, 3, 4, 7, 8, 9, 13, 14, 17, 18, 19, 20, 23, 24, 26, 28, 30, 32, 21, 22, 25]) (cs := [2, 1, 3, 4, 5, 1, 1, 6, 7, 8, 1, 1, 1, 9, 10, 1, 1, 11, 12, 13, 14, 21, 22, 15, 16, 23, 17, 1, 18, 1, 19, 1, 20, 1, 1, 1]) (bs := [19, 3]) (W := 452608) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem cover79783 : P.CoversSplit 26 10 79783 0xcc00cc0000000000cc00cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 538, 873, 930, 972, 979, 1266, 1658, 1665]) (by decide +kernel)

theorem c79783_0 : P.sumLeaves 26 81697792 1024 = 3238208 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79783) (lo := 0) (len := 1024) (W := 3238208) check rows elimOK (by decide) (by decide) cover79783 (by decide)
  decide +kernel

theorem h79783 : P.leaf 36 79783 = 3238208 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 3238208)]) (.cons c79783_0 (.nil)) (by decide) (by decide))

theorem cover79784 : P.CoversSplit 26 10 79784 0xf0f0f0f000000000f0f0f0f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 509, 538, 566, 874, 923, 1273]) (by decide +kernel)

theorem c79784_0 : P.sumLeaves 26 81698816 1024 = 110080 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79784) (lo := 0) (len := 1024) (W := 110080) check rows elimOK (by decide) (by decide) cover79784 (by decide)
  decide +kernel

theorem h79784 : P.leaf 36 79784 = 110080 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 110080)]) (.cons c79784_0 (.nil)) (by decide) (by decide))

theorem cover79785 : P.CoversSplit 26 10 79785 0xf0f0f0f500000000f0f0f0f50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 566, 923, 972, 979, 1273, 1322]) (by decide +kernel)

theorem c79785_0 : P.sumLeaves 26 81699840 1024 = 1756768 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79785) (lo := 0) (len := 1024) (W := 1756768) check rows elimOK (by decide) (by decide) cover79785 (by decide)
  decide +kernel

theorem h79785 : P.leaf 36 79785 = 1756768 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1756768)]) (.cons c79785_0 (.nil)) (by decide) (by decide))

theorem cover79786 : P.CoversSplit 26 10 79786 0xf0f0f0f000000000f0f0f0f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [479, 538, 874, 972, 1266, 1273]) (by decide +kernel)

theorem c79786_0 : P.sumLeaves 26 81700864 1024 = 1082752 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79786) (lo := 0) (len := 1024) (W := 1082752) check rows elimOK (by decide) (by decide) cover79786 (by decide)
  decide +kernel

theorem h79786 : P.leaf 36 79786 = 1082752 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1082752)]) (.cons c79786_0 (.nil)) (by decide) (by decide))

theorem cover79787 : P.CoversSplit 26 10 79787 0xf0f0f0f500000000f0f0f0f50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 972, 979, 1266, 1273, 1315, 1322]) (by decide +kernel)

theorem c79787_0 : P.sumLeaves 26 81701888 1024 = 6799904 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79787) (lo := 0) (len := 1024) (W := 6799904) check rows elimOK (by decide) (by decide) cover79787 (by decide)
  decide +kernel

theorem h79787 : P.leaf 36 79787 = 6799904 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 6799904)]) (.cons c79787_0 (.nil)) (by decide) (by decide))

theorem cover79788 : P.CoversSplit 26 10 79788 0xfffffffa00000000fffffffa0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [538, 566, 873, 874, 923, 972, 979, 1273]) (by decide +kernel)

theorem c79788_0 : P.sumLeaves 26 81702912 1024 = 1338368 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79788) (lo := 0) (len := 1024) (W := 1338368) check rows elimOK (by decide) (by decide) cover79788 (by decide)
  decide +kernel

theorem h79788 : P.leaf 36 79788 = 1338368 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1338368)]) (.cons c79788_0 (.nil)) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(79711, 720), (79724, 360), (79725, 360), (79726, 720), (79727, 720), (79742, 360), (79743, 360), (79753, 240), (79755, 240), (79757, 720), (79759, 720), (79765, 720), (79767, 720), (79772, 360), (79773, 720), (79774, 360), (79775, 720), (79781, 360), (79782, 720), (79783, 720), (79784, 720), (79785, 720), (79786, 720), (79787, 720), (79788, 720)]

theorem segOK : checkSeg 20 perms 79711 79789 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 79711 79789 14520 320708577360 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 320708577360)
    (SegSum.cons (w := 720) h79711 (SegSum.cons (w := 360) h79724 (SegSum.cons (w := 360) h79725 (SegSum.cons (w := 720) h79726 (SegSum.cons (w := 720) h79727 (SegSum.cons (w := 360) h79742 (SegSum.cons (w := 360) h79743 (SegSum.cons (w := 240) h79753 (SegSum.cons (w := 240) h79755 (SegSum.cons (w := 720) h79757 (SegSum.cons (w := 720) h79759 (SegSum.cons (w := 720) h79765 (SegSum.cons (w := 720) h79767 (SegSum.cons (w := 360) h79772 (SegSum.cons (w := 720) h79773 (SegSum.cons (w := 360) h79774 (SegSum.cons (w := 720) h79775 (SegSum.cons (w := 360) h79781 (SegSum.cons (w := 720) h79782 (SegSum.cons (w := 720) h79783 (SegSum.cons (w := 720) h79784 (SegSum.cons (w := 720) h79785 (SegSum.cons (w := 720) h79786 (SegSum.cons (w := 720) h79787 (SegSum.cons (w := 720) h79788 (show SegSum (P.leaf 36) [] 0 from rfl)))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S49
