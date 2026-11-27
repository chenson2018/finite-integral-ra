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

namespace RACert.S6N0.C0.S37

open RACert RACert.Problem

theorem cover32511 : P.CoversSplit 26 10 32511 0xfffffffffffffac8fffffafafffffac800000000000000000030003000000000fffffafafffffac8f0f0f0f0f0f0f0c00000000000000000003000300000000000330033000000000033003200000000003300330000000000300030000000000033003200000000003000300000000000330032000000000030003000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [587, 972, 979, 1265, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem contract32511_0 : P.leaf 32 520176 = 26112 := by
  exact leaf_contract_factors (k := 32) (b := 17) (H := 520176) (ss := [(22, 1, 433), (2, 1, 482), (3, 1, 531), (4, 1, 580), (7, 1, 825), (8, 1, 1217), (9, 1, 1609), (30, 1, 1658), (5, 1, 629), (29, 0, 1665), (31, 0, 1665), (33, 1, 587), (6, 1, 636), (16, 1, 1273), (17, 1, 1322)]) (ids := [8, 9, 10, 11, 12, 13, 19, 21, 24, 25, 26, 30, 16, 17, 18, 22, 23]) (cs := [1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 5, 6, 7, 1, 1, 14, 15, 16, 8, 1, 9, 17, 18, 10, 11, 12, 0, 1, 0, 13, 1]) (bs := [12, 5]) (W := 26112) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c32511_0 : P.sumLeaves 26 33291264 64 = 26112 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 520176) rows (by decide) (by decide)).symm.trans contract32511_0

theorem contract32511_1 : P.leaf 32 520177 = 50944 := by
  exact leaf_contract_factors (k := 32) (b := 19) (H := 520177) (ss := [(22, 1, 433), (2, 1, 482), (3, 1, 531), (4, 1, 580), (7, 1, 825), (8, 1, 1217), (9, 1, 1609), (29, 0, 1665), (31, 0, 1665), (33, 1, 587), (6, 1, 636), (16, 1, 1273), (17, 1, 1322)]) (ids := [3, 8, 9, 10, 11, 12, 13, 16, 17, 18, 19, 21, 23, 24, 25, 26, 28, 30, 22]) (cs := [1, 1, 1, 2, 1, 1, 1, 1, 3, 4, 5, 6, 7, 8, 1, 1, 9, 10, 11, 12, 1, 13, 20, 14, 15, 16, 17, 0, 18, 0, 19, 1]) (bs := [18, 1]) (W := 50944) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c32511_1 : P.sumLeaves 26 33291328 64 = 50944 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 520177) rows (by decide) (by decide)).symm.trans contract32511_1

theorem contract32511_2 : P.leaf 32 520178 = 40128 := by
  exact leaf_contract_factors (k := 32) (b := 17) (H := 520178) (ss := [(22, 1, 433), (2, 1, 482), (3, 1, 531), (4, 1, 580), (6, 1, 636), (7, 1, 825), (8, 1, 1217), (9, 1, 1609), (30, 1, 1658), (5, 1, 629), (20, 0, 1665), (29, 0, 1665), (31, 0, 1665), (17, 1, 1322), (33, 1, 1322)]) (ids := [8, 9, 10, 11, 12, 14, 16, 17, 19, 21, 24, 26, 30, 13, 22, 23, 25]) (cs := [1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 5, 6, 15, 7, 1, 8, 9, 0, 10, 1, 11, 16, 17, 12, 18, 13, 0, 1, 0, 14, 1]) (bs := [13, 4]) (W := 40128) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c32511_2 : P.sumLeaves 26 33291392 64 = 40128 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 520178) rows (by decide) (by decide)).symm.trans contract32511_2

theorem contract32511_3 : P.leaf 32 520179 = 72384 := by
  exact leaf_contract_factors (k := 32) (b := 19) (H := 520179) (ss := [(22, 1, 433), (2, 1, 482), (3, 1, 531), (4, 1, 580), (6, 1, 636), (7, 1, 825), (8, 1, 1217), (9, 1, 1609), (20, 0, 1665), (29, 0, 1665), (31, 0, 1665), (17, 1, 1322), (33, 1, 1322)]) (ids := [3, 8, 9, 10, 11, 12, 13, 14, 16, 17, 19, 21, 22, 23, 24, 26, 28, 30, 25]) (cs := [1, 1, 1, 2, 1, 1, 1, 1, 3, 4, 5, 6, 7, 8, 9, 1, 10, 11, 0, 12, 1, 13, 14, 15, 16, 20, 17, 0, 18, 0, 19, 1]) (bs := [18, 1]) (W := 72384) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c32511_3 : P.sumLeaves 26 33291456 64 = 72384 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 520179) rows (by decide) (by decide)).symm.trans contract32511_3

theorem c32511_4 : P.sumLeaves 26 33291520 494 = 155843918 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 32511) (lo := 256) (len := 494) (W := 155843918) check rows elimOK (by decide) (by decide) cover32511 (by decide)
  decide +kernel

theorem c32511_5 : P.sumLeaves 26 33292014 238 = 522052842 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 32511) (lo := 750) (len := 238) (W := 522052842) check rows elimOK (by decide) (by decide) cover32511 (by decide)
  decide +kernel

theorem c32511_6 : P.sumLeaves 26 33292252 36 = 289210154 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 32511) (lo := 988) (len := 36) (W := 289210154) check rows elimOK (by decide) (by decide) cover32511 (by decide)
  decide +kernel

theorem h32511 : P.leaf 36 32511 = 967296482 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(64, 26112), (64, 50944), (64, 40128), (64, 72384), (494, 155843918), (238, 522052842), (36, 289210154)]) (.cons c32511_0 (.cons c32511_1 (.cons c32511_2 (.cons c32511_3 (.cons c32511_4 (.cons c32511_5 (.cons c32511_6 (.nil)))))))) (by decide) (by decide))

theorem cover32736 : P.CoversSplit 26 10 32736 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c32736_0 : P.sumLeaves 26 33521664 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 32736) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover32736 (by decide)
  decide +kernel

theorem h32736 : P.leaf 36 32736 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c32736_0 (.nil)) (by decide) (by decide))

theorem cover32737 : P.CoversSplit 26 10 32737 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c32737_0 : P.sumLeaves 26 33522688 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 32737) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover32737 (by decide)
  decide +kernel

theorem h32737 : P.leaf 36 32737 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c32737_0 (.nil)) (by decide) (by decide))

theorem cover32739 : P.CoversSplit 26 10 32739 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c32739_0 : P.sumLeaves 26 33524736 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 32739) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover32739 (by decide)
  decide +kernel

theorem h32739 : P.leaf 36 32739 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c32739_0 (.nil)) (by decide) (by decide))

theorem cover32741 : P.CoversSplit 26 10 32741 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c32741_0 : P.sumLeaves 26 33526784 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 32741) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover32741 (by decide)
  decide +kernel

theorem h32741 : P.leaf 36 32741 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c32741_0 (.nil)) (by decide) (by decide))

theorem cover32743 : P.CoversSplit 26 10 32743 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c32743_0 : P.sumLeaves 26 33528832 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 32743) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover32743 (by decide)
  decide +kernel

theorem h32743 : P.leaf 36 32743 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c32743_0 (.nil)) (by decide) (by decide))

theorem cover32751 : P.CoversSplit 26 10 32751 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c32751_0 : P.sumLeaves 26 33537024 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 32751) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover32751 (by decide)
  decide +kernel

theorem h32751 : P.leaf 36 32751 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c32751_0 (.nil)) (by decide) (by decide))

theorem cover32752 : P.CoversSplit 26 10 32752 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00800000000000000000000fa000000fa0000000000000000000000fa000000fa080000000000000000000000000000000000000000f0c0f0c000000000f0c0f0c8000000000000000000000000000000000000000000000000000000000000fac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 972, 979]) (by decide +kernel)

noncomputable def f32752 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 26 (33538048 + i)

theorem c32752_0 : rowSum f32752 0 1024 = 1738848 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 32752) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover32752 (by decide)
  decide +kernel

theorem sum32752 : rowSum f32752 0 1024 = 1738848 :=
  c32752_0

theorem h32752 : P.leaf 36 32752 = 1738848 :=
  leaf_weighted (k := 26) (d := 10) (H := 32752) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 32752) (by decide) (by decide +kernel)) sum32752

theorem cover32753 : P.CoversSplit 26 10 32753 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00800000000000000000000fa000000fa0000000000000000000000fa000000fa080000000000000000000000000000000000000000f0c0f0c000000000f0c0f0c8000000000000000000000000000000000000000000000000000000000000fac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 972, 979]) (by decide +kernel)

noncomputable def f32753 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 26 (33539072 + i)

theorem c32753_0 : rowSum f32753 0 1024 = 61046772 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 32753) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover32753 (by decide)
  decide +kernel

theorem sum32753 : rowSum f32753 0 1024 = 61046772 :=
  c32753_0

theorem h32753 : P.leaf 36 32753 = 61046772 :=
  leaf_weighted (k := 26) (d := 10) (H := 32753) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 32753) (by decide) (by decide +kernel)) sum32753

theorem cover32755 : P.CoversSplit 26 10 32755 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00800000000000000000000fa000000fa0000000000000000000000fa000000fa080000000000000000000000000000000000000000f0c0f0c000000000f0c0f0c8000000000000000000000000000000000000000000000000000000000000fac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 972, 979]) (by decide +kernel)

noncomputable def f32755 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 26 (33541120 + i)

theorem c32755_0 : rowSum f32755 0 1024 = 129458992 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 32755) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover32755 (by decide)
  decide +kernel

theorem sum32755 : rowSum f32755 0 1024 = 129458992 :=
  c32755_0

theorem h32755 : P.leaf 36 32755 = 129458992 :=
  leaf_weighted (k := 26) (d := 10) (H := 32755) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 32755) (by decide) (by decide +kernel)) sum32755

theorem cover32756 : P.CoversSplit 26 10 32756 0xff00ff00ff00fa00ff00fa00ff00fa00ff00ff00ff00fa00fa00fa00fa00fa00ff00fa00ff00fa00fa00f000fa00f000ff00fa00ff00fa00fa00f000fa00f00000000000000000000000000000000000000000003300320000000000320032000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 880, 972, 979, 1265, 1273, 1315, 1658]) (by decide +kernel)

noncomputable def f32756 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 26 (33542144 + i)

theorem c32756_0 : rowSum f32756 0 858 = 53351854 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 32756) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover32756 (by decide)
  decide +kernel

theorem c32756_1 : rowSum f32756 858 166 = 61735292 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 32756) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover32756 (by decide)
  decide +kernel

theorem sum32756 : rowSum f32756 0 1024 = 115087146 :=
  rowSum_append (F := f32756) (lo := 0) (n := 858) (m := 166) (A := 53351854) (B := 61735292) c32756_0 (c32756_1)

theorem h32756 : P.leaf 36 32756 = 115087146 :=
  leaf_weighted (k := 26) (d := 10) (H := 32756) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 32756) (by decide) (by decide +kernel)) sum32756

theorem cover32757 : P.CoversSplit 26 10 32757 0xff00ff00ff00fa00ff00fa00ff00fa00ff00ff00ff00fa00fa00fa00fa00fa00ff00fa00ff00fa00fa00f000fa00f000ff00fa00ff00fa00fa00f000fa00f00000000000000000000000000000000000000000003300320000000000320032000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 929, 972, 979, 1265, 1273, 1315, 1658]) (by decide +kernel)

theorem c32757_0 : P.sumLeaves 26 33543168 747 = 87216562 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 32757) (lo := 0) (len := 747) (W := 87216562) check rows elimOK (by decide) (by decide) cover32757 (by decide)
  decide +kernel

theorem c32757_1 : P.sumLeaves 26 33543915 224 = 191832624 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 32757) (lo := 747) (len := 224) (W := 191832624) check rows elimOK (by decide) (by decide) cover32757 (by decide)
  decide +kernel

theorem c32757_2 : P.sumLeaves 26 33544139 53 = 120909276 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 32757) (lo := 971) (len := 53) (W := 120909276) check rows elimOK (by decide) (by decide) cover32757 (by decide)
  decide +kernel

theorem h32757 : P.leaf 36 32757 = 399958462 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(747, 87216562), (224, 191832624), (53, 120909276)]) (.cons c32757_0 (.cons c32757_1 (.cons c32757_2 (.nil)))) (by decide) (by decide))

theorem cover32759 : P.CoversSplit 26 10 32759 0xff00ff00ff00fa00ff00fa00ff00fa00ff00ff00ff00fa00fa00fa00fa00fa00ff00fa00ff00fa00fa00f000fa00f000ff00fa00ff00fa00fa00f000fa00f00000000000000000000000000000000000000000003300320000000000320032000000000000000000000000000000000000000000330032000000000032003000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 972, 979, 1265, 1273, 1315, 1658]) (by decide +kernel)

noncomputable def f32759 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 26 (33545216 + i)

theorem c32759_0 : rowSum f32759 0 815 = 357269462 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 32759) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover32759 (by decide)
  decide +kernel

theorem c32759_1 : rowSum f32759 815 209 = 483304882 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 32759) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover32759 (by decide)
  decide +kernel

theorem sum32759 : rowSum f32759 0 1024 = 840574344 :=
  rowSum_append (F := f32759) (lo := 0) (n := 815) (m := 209) (A := 357269462) (B := 483304882) c32759_0 (c32759_1)

theorem h32759 : P.leaf 36 32759 = 840574344 :=
  leaf_weighted (k := 26) (d := 10) (H := 32759) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 32759) (by decide) (by decide +kernel)) sum32759

theorem cover32764 : P.CoversSplit 26 10 32764 0xfffffffffffffac8fffffafafffffac8ffffffffffccfac8fac8fac8fac8fac8fffffafafffffac8fafafafafafafac8fffffafaffccfac8fac8fac8fac8fac8ffffffffffccfac8fffffafaffccfac8ffccffccffccfac8fac8fac8fac8fac80000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [874, 972, 979, 1265, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f32764 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 26 (33550336 + i)

theorem c32764_0 : rowSum f32764 0 410 = 146177522 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 32764) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover32764 (by decide)
  decide +kernel

theorem c32764_1 : rowSum f32764 410 383 = 314433038 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 32764) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover32764 (by decide)
  decide +kernel

theorem c32764_2 : rowSum f32764 793 230 = 490911620 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 32764) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover32764 (by decide)
  decide +kernel

theorem c32764_3 : rowSum f32764 1023 1 = 9297188 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 32764) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover32764 (by decide)
  decide +kernel

theorem sum32764 : rowSum f32764 0 1024 = 960819368 :=
  rowSum_append (F := f32764) (lo := 0) (n := 410) (m := 614) (A := 146177522) (B := 814641846) c32764_0 (rowSum_append (F := f32764) (lo := 410) (n := 383) (m := 231) (A := 314433038) (B := 500208808) c32764_1 (rowSum_append (F := f32764) (lo := 793) (n := 230) (m := 1) (A := 490911620) (B := 9297188) c32764_2 (c32764_3)))

theorem h32764 : P.leaf 36 32764 = 960819368 :=
  leaf_weighted (k := 26) (d := 10) (H := 32764) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 32764) (by decide) (by decide +kernel)) sum32764

theorem cover32765 : P.CoversSplit 26 10 32765 0xfffffffffffffac8fffffafafffffac8ffffffffffccfac8fac8fac8fac8fac8fffffafafffffac8fafafafafafafac8fffffafaffccfac8fac8fac8fac8fac8ffffffffffccfac8fffffafaffccfac8ffccffccffccfac8fac8fac8fac8fac80000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [923, 972, 979, 1265, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f32765 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 26 (33551360 + i)

theorem c32765_0 : rowSum f32765 0 410 = 377784388 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 32765) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover32765 (by decide)
  decide +kernel

theorem c32765_1 : rowSum f32765 410 383 = 672665168 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 32765) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover32765 (by decide)
  decide +kernel

theorem c32765_2 : rowSum f32765 793 230 = 995192308 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 32765) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover32765 (by decide)
  decide +kernel

theorem c32765_3 : rowSum f32765 1023 1 = 13171336 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 32765) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover32765 (by decide)
  decide +kernel

theorem sum32765 : rowSum f32765 0 1024 = 2058813200 :=
  rowSum_append (F := f32765) (lo := 0) (n := 410) (m := 614) (A := 377784388) (B := 1681028812) c32765_0 (rowSum_append (F := f32765) (lo := 410) (n := 383) (m := 231) (A := 672665168) (B := 1008363644) c32765_1 (rowSum_append (F := f32765) (lo := 793) (n := 230) (m := 1) (A := 995192308) (B := 13171336) c32765_2 (c32765_3)))

theorem h32765 : P.leaf 36 32765 = 2058813200 :=
  leaf_weighted (k := 26) (d := 10) (H := 32765) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 32765) (by decide) (by decide +kernel)) sum32765

def seg : List (ℕ × ℕ) := [(32511, 360), (32736, 90), (32737, 360), (32739, 180), (32741, 360), (32743, 360), (32751, 90), (32752, 180), (32753, 360), (32755, 180), (32756, 360), (32757, 720), (32759, 360), (32764, 180), (32765, 360)]

theorem segOK : checkSeg 20 perms 32511 32767 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 32511 32767 4500 1939947649920 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 1939947649920)
    (SegSum.cons (w := 360) h32511 (SegSum.cons (w := 90) h32736 (SegSum.cons (w := 360) h32737 (SegSum.cons (w := 180) h32739 (SegSum.cons (w := 360) h32741 (SegSum.cons (w := 360) h32743 (SegSum.cons (w := 90) h32751 (SegSum.cons (w := 180) h32752 (SegSum.cons (w := 360) h32753 (SegSum.cons (w := 180) h32755 (SegSum.cons (w := 360) h32756 (SegSum.cons (w := 720) h32757 (SegSum.cons (w := 360) h32759 (SegSum.cons (w := 180) h32764 (SegSum.cons (w := 360) h32765 (show SegSum (P.leaf 36) [] 0 from rfl)))))))))))))))) (by decide)

end RACert.S6N0.C0.S37
