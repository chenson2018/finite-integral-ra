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

namespace RACert.S6N0.C0.S73

open RACert RACert.Problem

theorem cover97279 : P.CoversSplit 26 10 97279 0xfffffffffffffafafffffffafffffafafffffffffffcfac8fafafafafac8fac8fffffafafffffafafafafafafafafafafffffafafffcfac8fafafafafac8fac8fffffffffffffafafffffffafffffafaffffffffccccc8c8fafafafac8c8c8c8fffffafafffffafafafafafafafafafafffffafaccccc8c8fafafafac8c8c8c8 :=
  coversSplit check rows (by decide) (by decide) (xs := [972, 979, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f97279 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 26 (99613696 + i)

theorem c97279_0 : rowSum f97279 0 240 = 12421983 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 97279) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover97279 (by decide)
  decide +kernel

theorem c97279_1 : rowSum f97279 240 182 = 716998452 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 97279) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover97279 (by decide)
  decide +kernel

theorem c97279_2 : rowSum f97279 422 184 = 912343173 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 97279) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover97279 (by decide)
  decide +kernel

theorem c97279_3 : rowSum f97279 606 206 = 1220195532 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 97279) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover97279 (by decide)
  decide +kernel

theorem c97279_4 : rowSum f97279 812 200 = 2101695339 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 97279) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover97279 (by decide)
  decide +kernel

theorem c97279_5 : rowSum f97279 1012 12 = 225566966 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 97279) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover97279 (by decide)
  decide +kernel

theorem sum97279 : rowSum f97279 0 1024 = 5189221445 :=
  rowSum_append (F := f97279) (lo := 0) (n := 240) (m := 784) (A := 12421983) (B := 5176799462) c97279_0 (rowSum_append (F := f97279) (lo := 240) (n := 182) (m := 602) (A := 716998452) (B := 4459801010) c97279_1 (rowSum_append (F := f97279) (lo := 422) (n := 184) (m := 418) (A := 912343173) (B := 3547457837) c97279_2 (rowSum_append (F := f97279) (lo := 606) (n := 206) (m := 212) (A := 1220195532) (B := 2327262305) c97279_3 (rowSum_append (F := f97279) (lo := 812) (n := 200) (m := 12) (A := 2101695339) (B := 225566966) c97279_4 (c97279_5)))))

theorem h97279 : P.leaf 36 97279 = 5189221445 :=
  leaf_weighted (k := 26) (d := 10) (H := 97279) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 97279) (by decide) (by decide +kernel)) sum97279

theorem cover97783 : P.CoversSplit 26 10 97783 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 482, 489, 629, 636, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c97783_0 : P.sumLeaves 26 100129792 1024 = 10320176 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97783) (lo := 0) (len := 1024) (W := 10320176) check rows elimOK (by decide) (by decide) cover97783 (by decide)
  decide +kernel

theorem h97783 : P.leaf 36 97783 = 10320176 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 10320176)]) (.cons c97783_0 (.nil)) (by decide) (by decide))

theorem cover97787 : P.CoversSplit 26 10 97787 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 481, 482, 629, 636, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c97787_0 : P.sumLeaves 26 100133888 1024 = 8219805 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97787) (lo := 0) (len := 1024) (W := 8219805) check rows elimOK (by decide) (by decide) cover97787 (by decide)
  decide +kernel

theorem h97787 : P.leaf 36 97787 = 8219805 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 8219805)]) (.cons c97787_0 (.nil)) (by decide) (by decide))

theorem cover97788 : P.CoversSplit 26 10 97788 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 972, 979, 1266, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c97788_0 : P.sumLeaves 26 100134912 1024 = 13088244 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97788) (lo := 0) (len := 1024) (W := 13088244) check rows elimOK (by decide) (by decide) cover97788 (by decide)
  decide +kernel

theorem h97788 : P.leaf 36 97788 = 13088244 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 13088244)]) (.cons c97788_0 (.nil)) (by decide) (by decide))

theorem cover97789 : P.CoversSplit 26 10 97789 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 972, 979, 1266, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c97789_0 : P.sumLeaves 26 100135936 1024 = 13921772 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97789) (lo := 0) (len := 1024) (W := 13921772) check rows elimOK (by decide) (by decide) cover97789 (by decide)
  decide +kernel

theorem h97789 : P.leaf 36 97789 = 13921772 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 13921772)]) (.cons c97789_0 (.nil)) (by decide) (by decide))

theorem cover97791 : P.CoversSplit 26 10 97791 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 972, 979, 1266, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c97791_0 : P.sumLeaves 26 100137984 1024 = 15556414 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97791) (lo := 0) (len := 1024) (W := 15556414) check rows elimOK (by decide) (by decide) cover97791 (by decide)
  decide +kernel

theorem h97791 : P.leaf 36 97791 = 15556414 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 15556414)]) (.cons c97791_0 (.nil)) (by decide) (by decide))

theorem cover98035 : P.CoversSplit 26 10 98035 0xc000c000c000c000c000c000c000c0000000000000000000000000000000000000000000000000000000c0000000c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 587, 972, 979, 1658, 1665]) (by decide +kernel)

theorem c98035_0 : P.sumLeaves 26 100387840 1024 = 57646968 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98035) (lo := 0) (len := 1024) (W := 57646968) check rows elimOK (by decide) (by decide) cover98035 (by decide)
  decide +kernel

theorem h98035 : P.leaf 36 98035 = 57646968 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 57646968)]) (.cons c98035_0 (.nil)) (by decide) (by decide))

theorem cover98038 : P.CoversSplit 26 10 98038 0xcc00cc00cc00c800cc00cc00cc00c80000000000000000000000000000000000cc00c800cc00c800c000c000c000c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 587, 874, 972, 979, 1315, 1658]) (by decide +kernel)

theorem c98038_0 : P.sumLeaves 26 100390912 1024 = 157509264 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98038) (lo := 0) (len := 1024) (W := 157509264) check rows elimOK (by decide) (by decide) cover98038 (by decide)
  decide +kernel

theorem h98038 : P.leaf 36 98038 = 157509264 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 157509264)]) (.cons c98038_0 (.nil)) (by decide) (by decide))

theorem cover98039 : P.CoversSplit 26 10 98039 0xcc00cc00cc00c800cc00cc00cc00c80000000000000000000000000000000000cc00c800cc00c800c000c000c000c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 587, 972, 979, 1315, 1658]) (by decide +kernel)

theorem c98039_0 : P.sumLeaves 26 100391936 1024 = 241084462 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98039) (lo := 0) (len := 1024) (W := 241084462) check rows elimOK (by decide) (by decide) cover98039 (by decide)
  decide +kernel

theorem h98039 : P.leaf 36 98039 = 241084462 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 241084462)]) (.cons c98039_0 (.nil)) (by decide) (by decide))

theorem cover98040 : P.CoversSplit 26 10 98040 0xf0f0f0f0f0f0f0f0f0f0f0f5f0f0f0f000000000000000000000000000300000000000000000000000005050000050500000000000000000000000000000000000000000003000300000000000300030000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 587, 874, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c98040_0 : P.sumLeaves 26 100392960 1024 = 17088193 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98040) (lo := 0) (len := 1024) (W := 17088193) check rows elimOK (by decide) (by decide) cover98040 (by decide)
  decide +kernel

theorem h98040 : P.leaf 36 98040 = 17088193 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 17088193)]) (.cons c98040_0 (.nil)) (by decide) (by decide))

theorem cover98041 : P.CoversSplit 26 10 98041 0xf0f0f0f0f0f0f0f0f0f0f0f5f0f0f0f000000000000000000000000000300000000000000000000000005050000050500000000000000000000000000000000000000000003000300000000000300030000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 587, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c98041_0 : P.sumLeaves 26 100393984 1024 = 133308928 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98041) (lo := 0) (len := 1024) (W := 133308928) check rows elimOK (by decide) (by decide) cover98041 (by decide)
  decide +kernel

theorem h98041 : P.leaf 36 98041 = 133308928 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 133308928)]) (.cons c98041_0 (.nil)) (by decide) (by decide))

theorem cover98042 : P.CoversSplit 26 10 98042 0xf0f0f0f0f0f0f0f0f0f0f0f5f0f0f0f000000000000000000000000000300000000000000000000000005050000050500000000000000000000000000000000000000000003000300000000000300030000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 587, 874, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c98042_0 : P.sumLeaves 26 100395008 1024 = 289384086 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98042) (lo := 0) (len := 1024) (W := 289384086) check rows elimOK (by decide) (by decide) cover98042 (by decide)
  decide +kernel

theorem h98042 : P.leaf 36 98042 = 289384086 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 289384086)]) (.cons c98042_0 (.nil)) (by decide) (by decide))

theorem cover98043 : P.CoversSplit 26 10 98043 0xf0f0f0f0f0f0f0f0f0f0f0f5f0f0f0f000000000000000000000000000300000000000000000000000005050000050500000000000000000000000000000000000000000003000300000000000300030000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 587, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c98043_0 : P.sumLeaves 26 100396032 1024 = 479892306 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98043) (lo := 0) (len := 1024) (W := 479892306) check rows elimOK (by decide) (by decide) cover98043 (by decide)
  decide +kernel

theorem h98043 : P.leaf 36 98043 = 479892306 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 479892306)]) (.cons c98043_0 (.nil)) (by decide) (by decide))

theorem cover98046 : P.CoversSplit 26 10 98046 0xfffffffffffffafafffffffafffffafa00000000000000000000000000300000fffffafafffffafaf0f0f0f0f0f0f0f00000000000000000000000000030000000000000003300320000000000330032000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [587, 874, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c98046_0 : P.sumLeaves 26 100399104 760 = 159319234 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98046) (lo := 0) (len := 760) (W := 159319234) check rows elimOK (by decide) (by decide) cover98046 (by decide)
  decide +kernel

theorem c98046_1 : P.sumLeaves 26 100399864 232 = 485325768 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98046) (lo := 760) (len := 232) (W := 485325768) check rows elimOK (by decide) (by decide) cover98046 (by decide)
  decide +kernel

theorem c98046_2 : P.sumLeaves 26 100400096 32 = 337975688 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98046) (lo := 992) (len := 32) (W := 337975688) check rows elimOK (by decide) (by decide) cover98046 (by decide)
  decide +kernel

theorem h98046 : P.leaf 36 98046 = 982620690 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(760, 159319234), (232, 485325768), (32, 337975688)]) (.cons c98046_0 (.cons c98046_1 (.cons c98046_2 (.nil)))) (by decide) (by decide))

theorem cover98047 : P.CoversSplit 26 10 98047 0xfffffffffffffafafffffffafffffafa00000000000000000000000000300000fffffafafffffafaf0f0f0f0f0f0f0f00000000000000000000000000030000000000000003300320000000000330032000000000000000000000000000000000000000000330032000000000030003000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [587, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c98047_0 : P.sumLeaves 26 100400128 128 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98047) (lo := 0) (len := 128) (W := 0) check rows elimOK (by decide) (by decide) cover98047 (by decide)
  decide +kernel

theorem contract98047_1 : P.leaf 32 1568754 = 39856 := by
  exact leaf_contract_factors (k := 32) (b := 17) (H := 1568754) (ss := [(22, 1, 433), (2, 1, 482), (3, 1, 531), (4, 1, 580), (6, 1, 636), (7, 1, 825), (8, 1, 1217), (9, 1, 1609), (30, 1, 1658), (5, 1, 629), (20, 0, 1665), (29, 0, 1665), (31, 0, 1665), (33, 0, 1665), (19, 1, 1273)]) (ids := [8, 9, 10, 11, 12, 13, 14, 16, 19, 21, 24, 25, 26, 30, 15, 22, 23]) (cs := [1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 5, 6, 7, 8, 16, 9, 1, 0, 10, 1, 11, 17, 18, 12, 13, 14, 0, 1, 0, 15, 0]) (bs := [14, 3]) (W := 39856) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c98047_1 : P.sumLeaves 26 100400256 64 = 39856 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1568754) rows (by decide) (by decide)).symm.trans contract98047_1

theorem contract98047_2 : P.leaf 32 1568755 = 71616 := by
  exact leaf_contract_factors (k := 32) (b := 19) (H := 1568755) (ss := [(22, 1, 433), (2, 1, 482), (3, 1, 531), (4, 1, 580), (6, 1, 636), (7, 1, 825), (8, 1, 1217), (9, 1, 1609), (20, 0, 1665), (29, 0, 1665), (31, 0, 1665), (33, 0, 1665), (19, 1, 1273)]) (ids := [3, 8, 9, 10, 11, 12, 13, 14, 15, 16, 19, 21, 22, 24, 25, 26, 28, 30, 23]) (cs := [1, 1, 1, 2, 1, 1, 1, 1, 3, 4, 5, 6, 7, 8, 9, 10, 11, 1, 0, 12, 1, 13, 14, 20, 15, 16, 17, 0, 18, 0, 19, 0]) (bs := [18, 1]) (W := 71616) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c98047_2 : P.sumLeaves 26 100400320 64 = 71616 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1568755) rows (by decide) (by decide)).symm.trans contract98047_2

theorem c98047_3 : P.sumLeaves 26 100400384 504 = 245683150 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98047) (lo := 256) (len := 504) (W := 245683150) check rows elimOK (by decide) (by decide) cover98047 (by decide)
  decide +kernel

theorem c98047_4 : P.sumLeaves 26 100400888 232 = 783177324 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98047) (lo := 760) (len := 232) (W := 783177324) check rows elimOK (by decide) (by decide) cover98047 (by decide)
  decide +kernel

theorem c98047_5 : P.sumLeaves 26 100401120 32 = 352764712 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 98047) (lo := 992) (len := 32) (W := 352764712) check rows elimOK (by decide) (by decide) cover98047 (by decide)
  decide +kernel

theorem h98047 : P.leaf 36 98047 = 1381736658 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(128, 0), (64, 39856), (64, 71616), (504, 245683150), (232, 783177324), (32, 352764712)]) (.cons c98047_0 (.cons c98047_1 (.cons c98047_2 (.cons c98047_3 (.cons c98047_4 (.cons c98047_5 (.nil))))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(97279, 360), (97783, 90), (97787, 90), (97788, 180), (97789, 360), (97791, 180), (98035, 720), (98038, 360), (98039, 360), (98040, 360), (98041, 360), (98042, 720), (98043, 720), (98046, 360), (98047, 360)]

theorem segOK : checkSeg 20 perms 97279 98115 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 97279 98115 5580 3524146364250 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 3524146364250)
    (SegSum.cons (w := 360) h97279 (SegSum.cons (w := 90) h97783 (SegSum.cons (w := 90) h97787 (SegSum.cons (w := 180) h97788 (SegSum.cons (w := 360) h97789 (SegSum.cons (w := 180) h97791 (SegSum.cons (w := 720) h98035 (SegSum.cons (w := 360) h98038 (SegSum.cons (w := 360) h98039 (SegSum.cons (w := 360) h98040 (SegSum.cons (w := 360) h98041 (SegSum.cons (w := 720) h98042 (SegSum.cons (w := 720) h98043 (SegSum.cons (w := 360) h98046 (SegSum.cons (w := 360) h98047 (show SegSum (P.leaf 36) [] 0 from rfl)))))))))))))))) (by decide)

end RACert.S6N0.C0.S73
