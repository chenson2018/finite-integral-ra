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

namespace RACert.S6N0.C0.S68

open RACert RACert.Problem

theorem cover97021 : P.CoversSplit 26 10 97021 0xfffffffffffffafafffffffafffffafa00000000000000000000000000300000fffffafafffffafaf0f0f0f0f0f0f0f00000000000000000000000000030000000000000003300320000000000330032000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [587, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c97021_0 : P.sumLeaves 26 99349504 760 = 30391156 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97021) (lo := 0) (len := 760) (W := 30391156) check rows elimOK (by decide) (by decide) cover97021 (by decide)
  decide +kernel

theorem c97021_1 : P.sumLeaves 26 99350264 232 = 73899976 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97021) (lo := 760) (len := 232) (W := 73899976) check rows elimOK (by decide) (by decide) cover97021 (by decide)
  decide +kernel

theorem c97021_2 : P.sumLeaves 26 99350496 32 = 45484592 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97021) (lo := 992) (len := 32) (W := 45484592) check rows elimOK (by decide) (by decide) cover97021 (by decide)
  decide +kernel

theorem h97021 : P.leaf 36 97021 = 149775724 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(760, 30391156), (232, 73899976), (32, 45484592)]) (.cons c97021_0 (.cons c97021_1 (.cons c97021_2 (.nil)))) (by decide) (by decide))

theorem cover97022 : P.CoversSplit 26 10 97022 0xfffffffffffffafafffffffafffffafa00000000000000000000000000300000fffffafafffffafaf0f0f0f0f0f0f0f00000000000000000000000000030000000000000003300320000000000330032000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [587, 874, 972, 979, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c97022_0 : P.sumLeaves 26 99350528 760 = 52592300 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97022) (lo := 0) (len := 760) (W := 52592300) check rows elimOK (by decide) (by decide) cover97022 (by decide)
  decide +kernel

theorem c97022_1 : P.sumLeaves 26 99351288 232 = 164065490 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97022) (lo := 760) (len := 232) (W := 164065490) check rows elimOK (by decide) (by decide) cover97022 (by decide)
  decide +kernel

theorem c97022_2 : P.sumLeaves 26 99351520 32 = 107758508 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97022) (lo := 992) (len := 32) (W := 107758508) check rows elimOK (by decide) (by decide) cover97022 (by decide)
  decide +kernel

theorem h97022 : P.leaf 36 97022 = 324416298 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(760, 52592300), (232, 164065490), (32, 107758508)]) (.cons c97022_0 (.cons c97022_1 (.cons c97022_2 (.nil)))) (by decide) (by decide))

theorem cover97023 : P.CoversSplit 26 10 97023 0xfffffffffffffafafffffffafffffafa00000000000000000000000000300000fffffafafffffafaf0f0f0f0f0f0f0f00000000000000000000000000030000000000000003300320000000000330032000000000000000000000000000000000000000000330032000000000030003000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [587, 972, 979, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c97023_0 : P.sumLeaves 26 99351552 128 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97023) (lo := 0) (len := 128) (W := 0) check rows elimOK (by decide) (by decide) cover97023 (by decide)
  decide +kernel

theorem contract97023_1 : P.leaf 32 1552370 = 18240 := by
  exact leaf_contract_factors (k := 32) (b := 15) (H := 1552370) (ss := [(22, 1, 433), (2, 1, 482), (3, 1, 531), (4, 1, 580), (6, 1, 636), (7, 1, 825), (8, 1, 1217), (9, 1, 1609), (19, 1, 1259), (21, 1, 1259), (30, 1, 1658), (5, 1, 629), (20, 0, 1665), (29, 0, 1665), (31, 0, 1665), (33, 0, 1665), (27, 1, 881)]) (ids := [8, 9, 11, 12, 14, 16, 21, 24, 26, 30, 10, 13, 15, 22, 23]) (cs := [1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 12, 4, 5, 13, 6, 14, 7, 1, 0, 1, 1, 8, 15, 16, 9, 1, 10, 0, 1, 0, 11, 0]) (bs := [10, 5]) (W := 18240) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c97023_1 : P.sumLeaves 26 99351680 64 = 18240 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1552370) rows (by decide) (by decide)).symm.trans contract97023_1

theorem contract97023_2 : P.leaf 32 1552371 = 36768 := by
  exact leaf_contract_factors (k := 32) (b := 17) (H := 1552371) (ss := [(22, 1, 433), (2, 1, 482), (3, 1, 531), (4, 1, 580), (6, 1, 636), (7, 1, 825), (8, 1, 1217), (9, 1, 1609), (19, 1, 1259), (21, 1, 1259), (20, 0, 1665), (29, 0, 1665), (31, 0, 1665), (33, 0, 1665), (27, 1, 881)]) (ids := [3, 8, 9, 10, 11, 12, 13, 14, 15, 16, 21, 22, 24, 26, 28, 30, 23]) (cs := [1, 1, 1, 2, 1, 1, 1, 1, 3, 4, 5, 6, 7, 8, 9, 10, 11, 1, 0, 1, 1, 12, 13, 18, 14, 1, 15, 0, 16, 0, 17, 0]) (bs := [16, 1]) (W := 36768) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c97023_2 : P.sumLeaves 26 99351744 64 = 36768 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1552371) rows (by decide) (by decide)).symm.trans contract97023_2

theorem c97023_3 : P.sumLeaves 26 99351808 504 = 111687425 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97023) (lo := 256) (len := 504) (W := 111687425) check rows elimOK (by decide) (by decide) cover97023 (by decide)
  decide +kernel

theorem c97023_4 : P.sumLeaves 26 99352312 232 = 337424778 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97023) (lo := 760) (len := 232) (W := 337424778) check rows elimOK (by decide) (by decide) cover97023 (by decide)
  decide +kernel

theorem c97023_5 : P.sumLeaves 26 99352544 32 = 156762428 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97023) (lo := 992) (len := 32) (W := 156762428) check rows elimOK (by decide) (by decide) cover97023 (by decide)
  decide +kernel

theorem h97023 : P.leaf 36 97023 = 605929639 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(128, 0), (64, 18240), (64, 36768), (504, 111687425), (232, 337424778), (32, 156762428)]) (.cons c97023_0 (.cons c97023_1 (.cons c97023_2 (.cons c97023_3 (.cons c97023_4 (.cons c97023_5 (.nil))))))) (by decide) (by decide))

theorem cover97091 : P.CoversSplit 26 10 97091 0xa0000000a00000000000000000000000a0000000a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 523, 530, 579, 608, 972, 979, 1266, 1273]) (by decide +kernel)

noncomputable def f97091 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 26 (99421184 + i)

theorem c97091_0 : rowSum f97091 0 1024 = 1145320 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 97091) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover97091 (by decide)
  decide +kernel

theorem sum97091 : rowSum f97091 0 1024 = 1145320 :=
  c97091_0

theorem h97091 : P.leaf 36 97091 = 1145320 :=
  leaf_weighted (k := 26) (d := 10) (H := 97091) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 97091) (by decide) (by decide +kernel)) sum97091

theorem cover97095 : P.CoversSplit 26 10 97095 0xaa000000aa0000000000000000000000aa000000aa0200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 523, 972, 979, 1266, 1273, 1315, 1658]) (by decide +kernel)

noncomputable def f97095 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 26 (99425280 + i)

theorem c97095_0 : rowSum f97095 0 1024 = 5899608 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 97095) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover97095 (by decide)
  decide +kernel

theorem sum97095 : rowSum f97095 0 1024 = 5899608 :=
  c97095_0

theorem h97095 : P.leaf 36 97095 = 5899608 :=
  leaf_weighted (k := 26) (d := 10) (H := 97095) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 97095) (by decide) (by decide +kernel)) sum97095

theorem cover97099 : P.CoversSplit 26 10 97099 0xa0a00000a0a000000000000000000000a0a00000a0a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000a0a00000a0a000000000000000000000a0a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 523, 530, 579, 972, 979, 1273]) (by decide +kernel)

noncomputable def f97099 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 26 (99429376 + i)

theorem c97099_0 : rowSum f97099 0 1024 = 4562654 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 97099) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover97099 (by decide)
  decide +kernel

theorem sum97099 : rowSum f97099 0 1024 = 4562654 :=
  c97099_0

theorem h97099 : P.leaf 36 97099 = 4562654 :=
  leaf_weighted (k := 26) (d := 10) (H := 97099) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 97099) (by decide) (by decide +kernel)) sum97099

theorem cover97103 : P.CoversSplit 26 10 97103 0xaaaa0000aaaa00000000000000000000aaaa0000aaa8000000000000000000000000000000000000000000000000000000000000000000000000000000000000aaaa0000aaaa00000000000000000000aaaa00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [523, 979, 1266, 1273, 1315, 1658]) (by decide +kernel)

noncomputable def f97103 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 26 (99433472 + i)

theorem c97103_0 : rowSum f97103 0 1024 = 12893924 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 97103) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover97103 (by decide)
  decide +kernel

theorem sum97103 : rowSum f97103 0 1024 = 12893924 :=
  c97103_0

theorem h97103 : P.leaf 36 97103 = 12893924 :=
  leaf_weighted (k := 26) (d := 10) (H := 97103) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 97103) (by decide) (by decide +kernel)) sum97103

theorem cover97107 : P.CoversSplit 26 10 97107 0xa0000000a00000000000000000000000a0000000a00000000000000000000000000000000000000000000500000005000000000000000000000005000000050000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000400 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 530, 579, 608, 972, 979, 1273, 1315]) (by decide +kernel)

noncomputable def f97107 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 26 (99437568 + i)

theorem c97107_0 : rowSum f97107 0 1024 = 15243180 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 97107) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover97107 (by decide)
  decide +kernel

theorem sum97107 : rowSum f97107 0 1024 = 15243180 :=
  c97107_0

theorem h97107 : P.leaf 36 97107 = 15243180 :=
  leaf_weighted (k := 26) (d := 10) (H := 97107) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 97107) (by decide) (by decide +kernel)) sum97107

theorem cover97108 : P.CoversSplit 26 10 97108 0xff000000ff0005000000000000000000ff000000ff0305000500000005000500050005000500050005000000050000000500050005010500050000000500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 874, 972, 979, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f97108 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 26 (99438592 + i)

theorem c97108_0 : rowSum f97108 0 1024 = 2939080 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 97108) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover97108 (by decide)
  decide +kernel

theorem sum97108 : rowSum f97108 0 1024 = 2939080 :=
  c97108_0

theorem h97108 : P.leaf 36 97108 = 2939080 :=
  leaf_weighted (k := 26) (d := 10) (H := 97108) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 97108) (by decide) (by decide +kernel)) sum97108

theorem cover97109 : P.CoversSplit 26 10 97109 0xff000000ff0005000000000000000000ff000000ff0305000500000005000500050005000500050005000000050000000500050005010500050000000500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 579, 923, 972, 979, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c97109_0 : P.sumLeaves 26 99439616 1024 = 58315676 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97109) (lo := 0) (len := 1024) (W := 58315676) check rows elimOK (by decide) (by decide) cover97109 (by decide)
  decide +kernel

theorem h97109 : P.leaf 36 97109 = 58315676 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 58315676)]) (.cons c97109_0 (.nil)) (by decide) (by decide))

theorem cover97111 : P.CoversSplit 26 10 97111 0xff000000ff0005000000000000000000ff000000ff0305000500000005000500050005000500050005000000050000000500050005010500050000000500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 972, 979, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f97111 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 26 (99441664 + i)

theorem c97111_0 : rowSum f97111 0 1024 = 137459282 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 97111) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover97111 (by decide)
  decide +kernel

theorem sum97111 : rowSum f97111 0 1024 = 137459282 :=
  c97111_0

theorem h97111 : P.leaf 36 97111 = 137459282 :=
  leaf_weighted (k := 26) (d := 10) (H := 97111) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 97111) (by decide) (by decide +kernel)) sum97111

theorem cover97113 : P.CoversSplit 26 10 97113 0xa0a00000a0a000000000000000000000a0a00000a0a0000000000000000000000000000000000000000005050000050500000000000000000000050500000500a0a00000a0a000000000000000000000a0a000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 579, 923, 972, 979, 1273]) (by decide +kernel)

theorem c97113_0 : P.sumLeaves 26 99443712 1024 = 29026773 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97113) (lo := 0) (len := 1024) (W := 29026773) check rows elimOK (by decide) (by decide) cover97113 (by decide)
  decide +kernel

theorem h97113 : P.leaf 36 97113 = 29026773 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 29026773)]) (.cons c97113_0 (.nil)) (by decide) (by decide))

theorem cover97115 : P.CoversSplit 26 10 97115 0xa0a00000a0a000000000000000000000a0a00000a0a0000000000000000000000000000000000000000005050000050500000000000000000000050500000500a0a00000a0a000000000000000000000a0a000008000000000000000000000000000000000000000000005050000050500000000000000000000050500000400 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 579, 972, 979, 1273]) (by decide +kernel)

noncomputable def f97115 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 26 (99445760 + i)

theorem c97115_0 : rowSum f97115 0 1024 = 80116446 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 97115) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover97115 (by decide)
  decide +kernel

theorem sum97115 : rowSum f97115 0 1024 = 80116446 :=
  c97115_0

theorem h97115 : P.leaf 36 97115 = 80116446 :=
  leaf_weighted (k := 26) (d := 10) (H := 97115) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 97115) (by decide) (by decide +kernel)) sum97115

theorem cover97116 : P.CoversSplit 26 10 97116 0xffff0000ffff05050000000000000000ffff0000fffc050005050000050005000505050505050505050500000505000005050505050405000505000005000000ffff0000ffff05050000000000000000ffff0000cc00040005050000040004000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 874, 972, 979, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f97116 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 26 (99446784 + i)

theorem c97116_0 : rowSum f97116 0 887 = 29223735 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 97116) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover97116 (by decide)
  decide +kernel

theorem c97116_1 : rowSum f97116 887 137 = 60598777 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 97116) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover97116 (by decide)
  decide +kernel

theorem sum97116 : rowSum f97116 0 1024 = 89822512 :=
  rowSum_append (F := f97116) (lo := 0) (n := 887) (m := 137) (A := 29223735) (B := 60598777) c97116_0 (c97116_1)

theorem h97116 : P.leaf 36 97116 = 89822512 :=
  leaf_weighted (k := 26) (d := 10) (H := 97116) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 97116) (by decide) (by decide +kernel)) sum97116

theorem cover97117 : P.CoversSplit 26 10 97117 0xffff0000ffff05050000000000000000ffff0000fffc050005050000050005000505050505050505050500000505000005050505050405000505000005000000ffff0000ffff05050000000000000000ffff0000cc00040005050000040004000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 579, 923, 972, 979, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c97117_0 : P.sumLeaves 26 99447808 728 = 33657406 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97117) (lo := 0) (len := 728) (W := 33657406) check rows elimOK (by decide) (by decide) cover97117 (by decide)
  decide +kernel

theorem c97117_1 : P.sumLeaves 26 99448536 296 = 166955096 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97117) (lo := 728) (len := 296) (W := 166955096) check rows elimOK (by decide) (by decide) cover97117 (by decide)
  decide +kernel

theorem h97117 : P.leaf 36 97117 = 200612502 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(728, 33657406), (296, 166955096)]) (.cons c97117_0 (.cons c97117_1 (.nil))) (by decide) (by decide))

theorem cover97119 : P.CoversSplit 26 10 97119 0xffff0000ffff05050000000000000000ffff0000fffc050005050000050005000505050505050505050500000505000005050505050405000505000005000000ffff0000ffff05050000000000000000ffff0000cc00040005050000040004000505050505050505050500000505000005050505040004000505000004000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 972, 979, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f97119 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 26 (99449856 + i)

theorem c97119_0 : rowSum f97119 0 826 = 87279330 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 97119) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover97119 (by decide)
  decide +kernel

theorem c97119_1 : rowSum f97119 826 198 = 376741145 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 97119) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover97119 (by decide)
  decide +kernel

theorem sum97119 : rowSum f97119 0 1024 = 464020475 :=
  rowSum_append (F := f97119) (lo := 0) (n := 826) (m := 198) (A := 87279330) (B := 376741145) c97119_0 (c97119_1)

theorem h97119 : P.leaf 36 97119 = 464020475 :=
  leaf_weighted (k := 26) (d := 10) (H := 97119) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 97119) (by decide) (by decide +kernel)) sum97119

def seg : List (ℕ × ℕ) := [(97021, 720), (97022, 720), (97023, 720), (97091, 180), (97095, 360), (97099, 180), (97103, 360), (97107, 360), (97108, 180), (97109, 720), (97111, 360), (97113, 360), (97115, 360), (97116, 360), (97117, 720), (97119, 360)]

theorem segOK : checkSeg 20 perms 97021 97122 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 97021 97122 7020 1266085945800 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 1266085945800)
    (SegSum.cons (w := 720) h97021 (SegSum.cons (w := 720) h97022 (SegSum.cons (w := 720) h97023 (SegSum.cons (w := 180) h97091 (SegSum.cons (w := 360) h97095 (SegSum.cons (w := 180) h97099 (SegSum.cons (w := 360) h97103 (SegSum.cons (w := 360) h97107 (SegSum.cons (w := 180) h97108 (SegSum.cons (w := 720) h97109 (SegSum.cons (w := 360) h97111 (SegSum.cons (w := 360) h97113 (SegSum.cons (w := 360) h97115 (SegSum.cons (w := 360) h97116 (SegSum.cons (w := 720) h97117 (SegSum.cons (w := 360) h97119 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))) (by decide)

end RACert.S6N0.C0.S68
