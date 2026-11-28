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

namespace RACert.S4N1.C0.S17

open RACert RACert.Problem

theorem cover17388 : P.CoversSplit 24 10 17388 0x8000800000000000800080000000000080000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000080008000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 466, 472, 473, 859, 879, 1210, 1259]) (by decide +kernel)

theorem h17388 : P.leaf 34 17388 = 736882 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 17388) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 17388) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 17388) (weight := rowWeight keep1 twice1) (xs := [383, 495, 511, 831, 895, 943, 959, 1007, 1023]) check rows elimOK (by decide) (by decide) cover17388 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h2028 : P.leaf 34 2028 = 736882 :=
  orient24 (v := 17388) (by decide) (by decide +kernel) h17388

theorem cover2029 : P.CoversSplit 24 10 2029 0xcc000000000000000000000000000000cc0000000000000000000000000000000000000000000000003300000000000000000000000000000033000000000000cc000000000000000000000000000000cc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 515, 522, 860, 872, 915, 1209, 1251, 1609]) (by decide +kernel)

theorem h2029 : P.leaf 34 2029 = 6686356 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 2029) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 2029) (weight := fun _ => 1) (xs := [378, 379, 382, 383, 506, 507, 510, 511, 560, 561, 564, 565, 688, 689, 692, 693, 890, 891, 894, 895, 1018, 1019, 1022, 1023]) check rows elimOK (by decide) (by decide) cover2029 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover2030 : P.CoversSplit 24 10 2030 0xaaaa0000000000000000000000000000a0a000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000aaaa0000000000000000000000000000a0a000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 515, 522, 860, 872, 916, 1209, 1258, 1259]) (by decide +kernel)

theorem h2030 : P.leaf 34 2030 = 7664050 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 2030) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 2030) (weight := fun _ => 1) (xs := [309, 373, 375, 381, 383, 497, 499, 501, 503, 505, 507, 509, 511, 821, 885, 887, 893, 895, 1009, 1011, 1013, 1015, 1017, 1019, 1021, 1023]) check rows elimOK (by decide) (by decide) cover2030 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover2031 : P.CoversSplit 24 10 2031 0xffff0000000000000000000000000000ffff00000000000000330000000000000000000000000000000000000000000000000000000000000000000000000000ffff0000000000000000000000000000ffff00000000000000330000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 522, 860, 916, 1202, 1209, 1251, 1258, 1259]) (by decide +kernel)

theorem c2031_0 : P.sumLeaves 24 2079744 1024 = 34198476 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 2031) (lo := 0) (len := 1024) (W := 34198476) check rows elimOK (by decide) (by decide) cover2031 (by decide)
  decide +kernel

theorem h2031 : P.leaf 34 2031 = 34198476 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 34198476)]) (.cons c2031_0 (.nil)) (by decide) (by decide))

theorem cover17391 : P.CoversSplit 24 10 17391 0xffffffffaaaaaaaaffffffffaaaaaaaaffff000000005050ffff000000004040cccccccc88888888cccccccc88888888cccc000000004040cccc000000004040ffffffffaaaaaaaa0000000000000000ffff55550000505033331111000010100000000000000000330022002200220000000000000000003300110000001000 :=
  coversProjected check rows (by decide) (by decide) (xs := [515, 522, 859, 915, 1202, 1210, 1259, 1601]) (ps := [(17, [1259], [1251]), (18, [1210], [1264])]) (by decide +kernel)

noncomputable def f17391 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (17808384 + i)

theorem c17391_0 : rowSum f17391 0 679 = 28616698 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 17391) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover17391 (by decide)
  decide +kernel

theorem c17391_1 : rowSum f17391 679 345 = 47680286 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 17391) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover17391 (by decide)
  decide +kernel

theorem sum17391 : rowSum f17391 0 1024 = 76296984 :=
  rowSum_append (F := f17391) (lo := 0) (n := 679) (m := 345) (A := 28616698) (B := 47680286) c17391_0 (c17391_1)

theorem h17391 : P.leaf 34 17391 = 76296984 :=
  leaf_weighted (k := 24) (d := 10) (H := 17391) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 17391) (by decide) (by decide +kernel)) sum17391

theorem h2046 : P.leaf 34 2046 = 76296984 :=
  orient24 (v := 17391) (by decide) (by decide +kernel) h17391

theorem cover17407 : P.CoversSplit 24 10 17407 0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaacccccccc88888888cccccccc88888888cccccccc88888888cccccccc88888888ffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaacccccccc88888888cccccccc88888888cccccccc88888888cccccccc88888888 :=
  coversSplit check rows (by decide) (by decide) (xs := [859, 915, 1202, 1210, 1259, 1601]) (by decide +kernel)

noncomputable def f17407 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (17824768 + i)

theorem c17407_0 : rowSum f17407 0 295 = 63055020 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 17407) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover17407 (by decide)
  decide +kernel

theorem c17407_1 : rowSum f17407 295 187 = 110472968 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 17407) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover17407 (by decide)
  decide +kernel

theorem c17407_2 : rowSum f17407 482 476 = 202848146 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 17407) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover17407 (by decide)
  decide +kernel

theorem c17407_3 : rowSum f17407 958 66 = 39879908 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 17407) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover17407 (by decide)
  decide +kernel

theorem sum17407 : rowSum f17407 0 1024 = 416256042 :=
  rowSum_append (F := f17407) (lo := 0) (n := 295) (m := 729) (A := 63055020) (B := 353201022) c17407_0 (rowSum_append (F := f17407) (lo := 295) (n := 187) (m := 542) (A := 110472968) (B := 242728054) c17407_1 (rowSum_append (F := f17407) (lo := 482) (n := 476) (m := 66) (A := 202848146) (B := 39879908) c17407_2 (c17407_3)))

theorem h17407 : P.leaf 34 17407 = 416256042 :=
  leaf_weighted (k := 24) (d := 10) (H := 17407) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 17407) (by decide) (by decide +kernel)) sum17407

theorem h2047 : P.leaf 34 2047 = 416256042 :=
  orient24 (v := 17407) (by decide) (by decide +kernel) h17407

theorem cover3180 : P.CoversSplit 24 10 3180 0x800000000000000000000000000000008000000000000000000000000000000000000000000000000033000000320000000000000000000000330000003200008000cc000000c80000000000000000008000cc000000c80000000000000000000000000000000000003300000032000000000000000000000033000000320000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 515, 522, 523, 572, 858, 915, 1208, 1209]) (by decide +kernel)

noncomputable def f3180 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 24 (3256320 + i)

theorem c3180_0 : rowSum f3180 0 1024 = 2570417 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 3180) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover3180 (by decide)
  decide +kernel

theorem sum3180 : rowSum f3180 0 1024 = 2570417 :=
  c3180_0

theorem h3180 : P.leaf 34 3180 = 2570417 :=
  leaf_weighted (k := 24) (d := 10) (H := 3180) (keep := keep2) (twice := twice2) rows (by decide) (by decide) (bal2) (invRow2 (H := 3180) (by decide) (by decide +kernel)) sum3180

theorem cover3181 : P.CoversSplit 24 10 3181 0x800000000000000000000000000000008000000000000000000000000000000000000000000000000033000000330000000000000000000000330000003300008000cc000000cc0000000000000000008000cc000000c80000000000000000000000000000000000003300000033000000000000000000000033000000320000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 515, 522, 523, 572, 858, 865, 1208, 1209, 1217]) (by decide +kernel)

noncomputable def f3181 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 24 (3257344 + i)

theorem c3181_0 : rowSum f3181 0 1024 = 5488880 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 3181) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover3181 (by decide)
  decide +kernel

theorem sum3181 : rowSum f3181 0 1024 = 5488880 :=
  c3181_0

theorem h3181 : P.leaf 34 3181 = 5488880 :=
  leaf_weighted (k := 24) (d := 10) (H := 3181) (keep := keep2) (twice := twice2) rows (by decide) (by decide) (bal2) (invRow2 (H := 3181) (by decide) (by decide +kernel)) sum3181

theorem cover3182 : P.CoversSplit 24 10 3182 0x8000000000000000000000000000000080000000000000000000000000000000000000000000000000210000002100000000000000000000002100000021000080000000000000000000000000000000800000000000000000000000000000000000000000000000002100000021000000000000000000000021000000200000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 515, 522, 523, 565, 572, 858, 865, 915, 1209, 1217]) (by decide +kernel)

theorem h3182 : P.leaf 34 3182 = 113354 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 3182) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 3182) (weight := fun _ => 1) (xs := [21, 48, 53, 144, 149, 176, 181, 383, 511, 528, 533, 560, 565, 656, 661, 688, 693, 895, 1023]) check rows elimOK (by decide) (by decide) cover3182 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3183 : P.CoversSplit 24 10 3183 0x8000000000000000000000000000000080000000000000000000000000000000000000000000000000210000002100000000000000000000002100000021000080000000000000000000000000000000800000000000000000000000000000000000000000000000002100000021000000000000000000000021000000200000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 515, 522, 523, 565, 572, 858, 865, 1209, 1217]) (by decide +kernel)

theorem h3183 : P.leaf 34 3183 = 412830 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 3183) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 3183) (weight := fun _ => 1) (xs := [21, 48, 53, 144, 149, 176, 181, 383, 511, 528, 533, 560, 565, 656, 661, 688, 693, 895, 1023]) check rows elimOK (by decide) (by decide) cover3183 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3198 : P.CoversSplit 24 10 3198 0xc0004400c00000000000000000000000c0004400c000000000310011003100000000000000000000000000000000000000000000000000000000000000000000c0004400c00000000000000000000000c0004400c000000000310011002000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 572, 858, 865, 915, 1209, 1217, 1258]) (ps := [(14, [1217], [915])]) (by decide +kernel)

theorem c3198_0 : P.sumLeaves 24 3274752 1024 = 1006390 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3198) (lo := 0) (len := 1024) (W := 1006390) check rows elimOK (by decide) (by decide) cover3198 (by decide)
  decide +kernel

theorem h3198 : P.leaf 34 3198 = 1006390 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1006390)]) (.cons c3198_0 (.nil)) (by decide) (by decide))

theorem cover3709 : P.CoversSplit 24 10 3709 0xcc00cc00cc0000000000000000000000cc00cc00cc00000000330033003300000000000000000000000000000000000000000000000000000000000000000000cc00cc00cc0000000000000000000000cc00cc008000000000330033002000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 572, 915, 1209, 1217, 1258]) (ps := [(8, [1217], [572, 1266]), (14, [1217], [915, 1266])]) (by decide +kernel)

noncomputable def f3709 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 24 (3798016 + i)

theorem c3709_0 : rowSum f3709 0 1024 = 4563638 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 3709) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover3709 (by decide)
  decide +kernel

theorem sum3709 : rowSum f3709 0 1024 = 4563638 :=
  c3709_0

theorem h3709 : P.leaf 34 3709 = 4563638 :=
  leaf_weighted (k := 24) (d := 10) (H := 3709) (keep := keep2) (twice := twice2) rows (by decide) (by decide) (bal2) (invRow2 (H := 3709) (by decide) (by decide +kernel)) sum3709

theorem h3199 : P.leaf 34 3199 = 4563638 :=
  orient5 (v := 3709) (by decide) (by decide +kernel) h3709

theorem cover3236 : P.CoversSplit 24 10 3236 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem h3236 : P.leaf 34 3236 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 3236) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 3236) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3236 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h3237 : P.leaf 34 3237 = 0 := by
  exact leaf_contract_zero (ss := [(30, 1, 466), (11, 1, 472), (35, 0, 475), (13, 2, 480), (16, 3, 529), (14, 0, 559), (18, 4, 487), (33, 0, 566), (4, 1, 867), (5, 1, 404)]) (q := 965) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem cover3238 : P.CoversSplit 24 10 3238 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [566]) (by decide +kernel)

theorem h3238 : P.leaf 34 3238 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 3238) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 3238) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3238 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3239 : P.CoversSplit 24 10 3239 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [566]) (by decide +kernel)

theorem h3239 : P.leaf 34 3239 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 3239) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 3239) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3239 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3240 : P.CoversSplit 24 10 3240 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem h3240 : P.leaf 34 3240 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 3240) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 3240) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3240 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h3241 : P.leaf 34 3241 = 0 := by
  exact leaf_contract_zero (ss := [(30, 1, 466), (11, 1, 472), (18, 1, 475), (35, 14, 487), (14, 0, 524), (29, 2, 474), (16, 3, 529), (15, 2, 558), (4, 1, 559), (33, 0, 566)]) (q := 929) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem cover3242 : P.CoversSplit 24 10 3242 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [566]) (by decide +kernel)

theorem h3242 : P.leaf 34 3242 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 3242) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 3242) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3242 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3243 : P.CoversSplit 24 10 3243 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [566]) (by decide +kernel)

theorem h3243 : P.leaf 34 3243 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 3243) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 3243) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3243 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3244 : P.CoversSplit 24 10 3244 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem h3244 : P.leaf 34 3244 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 3244) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 3244) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3244 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h3245 : P.leaf 34 3245 = 0 := by
  exact leaf_contract_zero (ss := [(30, 1, 466), (11, 1, 472), (35, 0, 524), (18, 1, 475), (16, 3, 529), (33, 0, 566), (4, 1, 536), (14, 1, 929)]) (q := 1308) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem cover3246 : P.CoversSplit 24 10 3246 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [566]) (by decide +kernel)

theorem h3246 : P.leaf 34 3246 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 3246) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 3246) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3246 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3247 : P.CoversSplit 24 10 3247 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [566]) (by decide +kernel)

theorem h3247 : P.leaf 34 3247 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 3247) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 3247) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3247 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3254 : P.CoversSplit 24 10 3254 0xf0000000000000000000000000000000a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 517, 573, 858, 865, 866, 908, 916, 921, 1209, 1259, 1308]) (ps := [(8, [531, 580], [517, 573])]) (by decide +kernel)

theorem h3254 : P.leaf 34 3254 = 58912 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 3254) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 3254) (weight := fun _ => 1) (xs := [510, 511, 893, 895, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover3254 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3255 : P.CoversSplit 24 10 3255 0xff000000000000000000000000000000ff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [517, 573, 858, 865, 866, 915, 916, 921, 1202, 1209, 1259, 1308]) (ps := [(8, [580], [573])]) (by decide +kernel)

theorem h3255 : P.leaf 34 3255 = 605440 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 3255) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 3255) (weight := fun _ => 1) (xs := [506, 507, 510, 511, 888, 889, 890, 891, 892, 893, 894, 895, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover3255 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3270 : P.CoversSplit 24 10 3270 0x8000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 466, 515, 516, 522, 536, 566, 858, 865, 916, 1209]) (by decide +kernel)

theorem h3270 : P.leaf 34 3270 = 9856 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 3270) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 3270) (weight := fun _ => 1) (xs := [895, 1023]) check rows elimOK (by decide) (by decide) cover3270 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h3256 : P.leaf 34 3256 = 9856 :=
  orient4 (v := 3270) (by decide) (by decide +kernel) h3270

theorem cover3271 : P.CoversSplit 24 10 3271 0x8000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 515, 516, 522, 523, 536, 566, 858, 865, 916, 1209]) (by decide +kernel)

theorem h3271 : P.leaf 34 3271 = 135040 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 3271) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 3271) (weight := fun _ => 1) (xs := [895, 1023]) check rows elimOK (by decide) (by decide) cover3271 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h3257 : P.leaf 34 3257 = 135040 :=
  orient4 (v := 3271) (by decide) (by decide +kernel) h3271

theorem cover49351 : P.CoversSplit 24 10 49351 0xf000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [515, 516, 522, 536, 573, 858, 860, 865, 871, 879, 916, 921]) (ps := [(10, [852], [865]), (11, [901], [858])]) (by decide +kernel)

theorem h49351 : P.leaf 34 49351 = 106576 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 49351) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 49351) (weight := fun _ => 1) (xs := [383, 511, 895, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover49351 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h3258 : P.leaf 34 3258 = 106576 :=
  orient24 (v := 49351) (by decide) (by decide +kernel) h49351

theorem cover3259 : P.CoversSplit 24 10 3259 0xff000000000000000000000000000000ff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [487, 517, 573, 858, 867, 916, 921, 1202, 1209, 1210, 1251, 1259, 1308]) (by decide +kernel)

theorem h3259 : P.leaf 34 3259 = 1299648 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 3259) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 3259) (weight := fun _ => 1) (xs := [506, 507, 510, 511, 888, 889, 890, 891, 892, 893, 894, 895, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover3259 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3302 : P.CoversSplit 24 10 3302 0x8000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 465, 466, 515, 522, 524, 566, 573, 858, 865, 916, 1209, 1272]) (by decide +kernel)

theorem h3302 : P.leaf 34 3302 = 23488 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 3302) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 3302) (weight := fun _ => 1) (xs := [511, 895, 1023]) check rows elimOK (by decide) (by decide) cover3302 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h3260 : P.leaf 34 3260 = 23488 :=
  orient4 (v := 3302) (by decide) (by decide +kernel) h3302

theorem cover3303 : P.CoversSplit 24 10 3303 0x8000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 515, 522, 524, 566, 573, 858, 865, 915, 916, 1209, 1272]) (by decide +kernel)

theorem h3303 : P.leaf 34 3303 = 159552 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 3303) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 3303) (weight := fun _ => 1) (xs := [511, 895, 1023]) check rows elimOK (by decide) (by decide) cover3303 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h3261 : P.leaf 34 3261 = 159552 :=
  orient4 (v := 3303) (by decide) (by decide +kernel) h3303

def seg : List (ℕ × ℕ) := [(2028, 24), (2029, 24), (2030, 48), (2031, 48), (2046, 24), (2047, 24), (3180, 4), (3181, 4), (3182, 12), (3183, 12), (3198, 12), (3199, 12), (3236, 24), (3237, 24), (3238, 48), (3239, 48), (3240, 48), (3241, 48), (3242, 48), (3243, 48), (3244, 48), (3245, 48), (3246, 48), (3247, 48), (3254, 24), (3255, 24), (3256, 48), (3257, 48), (3258, 48), (3259, 48), (3260, 48), (3261, 48)]

theorem segOK : checkSeg 16 perms 2028 3262 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 2028 3262 1112 14213407444 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 14213407444)
    (SegSum.cons (w := 24) h2028 (SegSum.cons (w := 24) h2029 (SegSum.cons (w := 48) h2030 (SegSum.cons (w := 48) h2031 (SegSum.cons (w := 24) h2046 (SegSum.cons (w := 24) h2047 (SegSum.cons (w := 4) h3180 (SegSum.cons (w := 4) h3181 (SegSum.cons (w := 12) h3182 (SegSum.cons (w := 12) h3183 (SegSum.cons (w := 12) h3198 (SegSum.cons (w := 12) h3199 (SegSum.cons (w := 24) h3236 (SegSum.cons (w := 24) h3237 (SegSum.cons (w := 48) h3238 (SegSum.cons (w := 48) h3239 (SegSum.cons (w := 48) h3240 (SegSum.cons (w := 48) h3241 (SegSum.cons (w := 48) h3242 (SegSum.cons (w := 48) h3243 (SegSum.cons (w := 48) h3244 (SegSum.cons (w := 48) h3245 (SegSum.cons (w := 48) h3246 (SegSum.cons (w := 48) h3247 (SegSum.cons (w := 24) h3254 (SegSum.cons (w := 24) h3255 (SegSum.cons (w := 48) h3256 (SegSum.cons (w := 48) h3257 (SegSum.cons (w := 48) h3258 (SegSum.cons (w := 48) h3259 (SegSum.cons (w := 48) h3260 (SegSum.cons (w := 48) h3261 (show SegSum (P.leaf 34) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S4N1.C0.S17
