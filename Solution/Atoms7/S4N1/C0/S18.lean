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

namespace RACert.S4N1.C0.S18

open RACert RACert.Problem

theorem cover3262 : P.CoversSplit 24 10 3262 0xf0000000000000000000000000000000a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 517, 573, 858, 865, 916, 921, 1209, 1210, 1251, 1259, 1308]) (by decide +kernel)

theorem h3262 : P.leaf 34 3262 = 383080 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 3262) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 3262) (weight := fun _ => 1) (xs := [510, 511, 893, 895, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover3262 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3263 : P.CoversSplit 24 10 3263 0xff000000000000000000000000000000ff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [517, 573, 858, 865, 916, 921, 1202, 1209, 1210, 1251, 1259, 1308]) (by decide +kernel)

theorem h3263 : P.leaf 34 3263 = 2554400 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 3263) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 3263) (weight := fun _ => 1) (xs := [506, 507, 510, 511, 888, 889, 890, 891, 892, 893, 894, 895, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover3263 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3272 : P.CoversSplit 24 10 3272 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem h3272 : P.leaf 34 3272 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 3272) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 3272) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3272 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3273 : P.CoversSplit 24 10 3273 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [466, 473, 474, 515, 522, 536, 573, 858, 865, 915, 1202, 1209, 1217, 1272]) (by decide +kernel)

theorem h3273 : P.leaf 34 3273 = 2232 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 3273) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 3273) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover3273 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3274 : P.CoversSplit 24 10 3274 0x8000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 466, 515, 516, 522, 536, 566, 858, 865, 916, 1209]) (by decide +kernel)

theorem h3274 : P.leaf 34 3274 = 17312 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 3274) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 3274) (weight := fun _ => 1) (xs := [895, 1023]) check rows elimOK (by decide) (by decide) cover3274 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3275 : P.CoversSplit 24 10 3275 0x8000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 515, 516, 522, 523, 536, 566, 858, 865, 916, 1209]) (by decide +kernel)

theorem h3275 : P.leaf 34 3275 = 119264 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 3275) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 3275) (weight := fun _ => 1) (xs := [895, 1023]) check rows elimOK (by decide) (by decide) cover3275 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3276 : P.CoversSplit 24 10 3276 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem h3276 : P.leaf 34 3276 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 3276) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 3276) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3276 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3277 : P.CoversSplit 24 10 3277 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [466, 473, 515, 522, 523, 536, 573, 858, 865, 915, 1202, 1209, 1217, 1272]) (by decide +kernel)

theorem h3277 : P.leaf 34 3277 = 12544 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 3277) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 3277) (weight := fun _ => 1) (xs := [1023]) check rows elimOK (by decide) (by decide) cover3277 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3278 : P.CoversSplit 24 10 3278 0x8000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 466, 515, 516, 522, 536, 566, 858, 865, 916, 1209]) (by decide +kernel)

theorem h3278 : P.leaf 34 3278 = 90624 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 3278) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 3278) (weight := fun _ => 1) (xs := [895, 1023]) check rows elimOK (by decide) (by decide) cover3278 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3279 : P.CoversSplit 24 10 3279 0x8000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 515, 516, 522, 523, 536, 566, 858, 865, 916, 1209]) (by decide +kernel)

theorem h3279 : P.leaf 34 3279 = 402592 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 3279) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 3279) (weight := fun _ => 1) (xs := [895, 1023]) check rows elimOK (by decide) (by decide) cover3279 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover49479 : P.CoversSplit 24 10 49479 0xf0000000000000000000000000000000a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c0000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [515, 516, 522, 572, 858, 860, 865, 871, 879, 921]) (ps := [(10, [852], [865]), (11, [901], [858])]) (by decide +kernel)

theorem h49479 : P.leaf 34 49479 = 116064 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 49479) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 49479) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 49479) (weight := rowWeight keep0 twice0) (xs := [383, 510, 511, 893, 895, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover49479 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h3290 : P.leaf 34 3290 = 116064 :=
  orient24 (v := 49479) (by decide) (by decide +kernel) h49479

theorem cover3291 : P.CoversSplit 24 10 3291 0xff000000000000000000000000000000ff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [487, 516, 573, 858, 865, 867, 909, 916, 921, 1202, 1210, 1259]) (ps := [(8, [1272], [1266])]) (by decide +kernel)

theorem h3291 : P.leaf 34 3291 = 1114432 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 3291) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 3291) (weight := fun _ => 1) (xs := [506, 507, 510, 511, 888, 889, 890, 891, 892, 893, 894, 895, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover3291 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3306 : P.CoversSplit 24 10 3306 0x8000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 465, 466, 515, 522, 524, 566, 573, 858, 865, 916, 1209, 1272]) (by decide +kernel)

theorem h3306 : P.leaf 34 3306 = 57424 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 3306) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 3306) (weight := fun _ => 1) (xs := [511, 895, 1023]) check rows elimOK (by decide) (by decide) cover3306 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h3292 : P.leaf 34 3292 = 57424 :=
  orient4 (v := 3306) (by decide) (by decide +kernel) h3306

theorem cover3307 : P.CoversSplit 24 10 3307 0x8000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 515, 522, 524, 566, 573, 858, 865, 915, 916, 1209, 1272]) (by decide +kernel)

theorem h3307 : P.leaf 34 3307 = 289824 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 3307) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 3307) (weight := fun _ => 1) (xs := [511, 895, 1023]) check rows elimOK (by decide) (by decide) cover3307 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h3293 : P.leaf 34 3293 = 289824 :=
  orient4 (v := 3307) (by decide) (by decide +kernel) h3307

theorem cover3294 : P.CoversSplit 24 10 3294 0xf0000000000000000000000000000000a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 516, 536, 573, 858, 865, 916, 921, 1209, 1210, 1251, 1259]) (ps := [(8, [1272], [1266])]) (by decide +kernel)

theorem h3294 : P.leaf 34 3294 = 754352 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 3294) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 3294) (weight := fun _ => 1) (xs := [510, 511, 893, 895, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover3294 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3295 : P.CoversSplit 24 10 3295 0xff000000000000000000000000000000ff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [516, 536, 573, 858, 865, 916, 921, 1202, 1209, 1210, 1251, 1259]) (ps := [(8, [1272], [1266])]) (by decide +kernel)

theorem h3295 : P.leaf 34 3295 = 3534208 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 3295) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 3295) (weight := fun _ => 1) (xs := [506, 507, 510, 511, 888, 889, 890, 891, 892, 893, 894, 895, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover3295 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3308 : P.CoversSplit 24 10 3308 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem h3308 : P.leaf 34 3308 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 3308) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 3308) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3308 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3309 : P.CoversSplit 24 10 3309 0x8000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 466, 473, 515, 522, 573, 858, 865, 915, 1209, 1217, 1272, 1651]) (by decide +kernel)

theorem h3309 : P.leaf 34 3309 = 54048 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 3309) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 3309) (weight := fun _ => 1) (xs := [511, 895, 1023]) check rows elimOK (by decide) (by decide) cover3309 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3310 : P.CoversSplit 24 10 3310 0x8000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 465, 466, 515, 522, 524, 566, 573, 858, 865, 916, 1209, 1272]) (by decide +kernel)

theorem h3310 : P.leaf 34 3310 = 234008 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 3310) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 3310) (weight := fun _ => 1) (xs := [511, 895, 1023]) check rows elimOK (by decide) (by decide) cover3310 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3311 : P.CoversSplit 24 10 3311 0x8000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 515, 522, 524, 566, 573, 858, 865, 915, 916, 1209, 1272]) (by decide +kernel)

theorem h3311 : P.leaf 34 3311 = 620640 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 3311) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 3311) (weight := fun _ => 1) (xs := [511, 895, 1023]) check rows elimOK (by decide) (by decide) cover3311 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3326 : P.CoversSplit 24 10 3326 0xf0005500f00000000000000000000000f0005500f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c0004400c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 573, 858, 865, 916, 921, 1209, 1259, 1308]) (by decide +kernel)

theorem h3326 : P.leaf 34 3326 = 3585516 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 3326) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 3326) (weight := fun _ => 1) (xs := [478, 479, 490, 494, 510, 511, 860, 861, 862, 863, 872, 874, 876, 878, 892, 893, 894, 895, 988, 989, 990, 991, 1000, 1002, 1004, 1006, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover3326 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover36477 : P.CoversSplit 24 10 36477 0xcc00cc00c8000000cc00cc00c8000000cc00cc00c8000000cc00cc00c80000000000000000000000000000000000000000000000000000000000000000000000cc00cc00c80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 572, 578, 915, 1202, 1209, 1258, 1308]) (ps := [(8, [580], [1272])]) (by decide +kernel)

noncomputable def f36477 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 24 (37352448 + i)

theorem c36477_0 : rowSum f36477 0 1024 = 14087490 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 36477) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover36477 (by decide)
  decide +kernel

theorem sum36477 : rowSum f36477 0 1024 = 14087490 :=
  c36477_0

theorem h36477 : P.leaf 34 36477 = 14087490 :=
  leaf_weighted (k := 24) (d := 10) (H := 36477) (keep := keep2) (twice := twice2) rows (by decide) (by decide) (bal2) (invRow2 (H := 36477) (by decide) (by decide +kernel)) sum36477

theorem h3327 : P.leaf 34 3327 = 14087490 :=
  orient5 (v := 36477) (by decide) (by decide +kernel) h36477

theorem cover3456 : P.CoversSplit 24 10 3456 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem h3456 : P.leaf 34 3456 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 3456) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 3456) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3456 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3457 : P.CoversSplit 24 10 3457 0x8000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000002200000011000080000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [466, 473, 515, 522, 565, 858, 865, 915, 1209, 1217, 1609]) (by decide +kernel)

theorem h3457 : P.leaf 34 3457 = 6541 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 3457) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 3457) (weight := fun _ => 1) (xs := [383, 511, 528, 532, 561, 565, 895, 1023]) check rows elimOK (by decide) (by decide) cover3457 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3459 : P.CoversSplit 24 10 3459 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000800000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 515, 516, 522, 565, 858, 865, 1209, 1217, 1258]) (by decide +kernel)

theorem h3459 : P.leaf 34 3459 = 35544 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 3459) (keep := keep4) (twice := twice4) rows (by decide) (by decide) bal4 (invRow4 (H := 3459) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 3459) (weight := rowWeight keep4 twice4) (xs := [208, 383, 511, 592, 720, 895, 1023]) check rows elimOK (by decide) (by decide) cover3459 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3460 : P.CoversSplit 24 10 3460 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem h3460 : P.leaf 34 3460 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 3460) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 3460) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3460 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3489 : P.CoversSplit 24 10 3489 0x8000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 466, 473, 515, 522, 524, 566, 858, 865, 915, 1202, 1209, 1217, 1266]) (by decide +kernel)

theorem h3489 : P.leaf 34 3489 = 9408 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 3489) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 3489) (weight := fun _ => 1) (xs := [511, 895, 1023]) check rows elimOK (by decide) (by decide) cover3489 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h3461 : P.leaf 34 3461 = 9408 :=
  orient4 (v := 3489) (by decide) (by decide +kernel) h3489

theorem cover3463 : P.CoversSplit 24 10 3463 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000800000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 515, 516, 522, 565, 858, 865, 1209, 1217, 1258]) (by decide +kernel)

theorem h3463 : P.leaf 34 3463 = 88528 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 3463) (keep := keep5) (twice := twice5) rows (by decide) (by decide) bal5 (invRow5 (H := 3463) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 3463) (weight := rowWeight keep5 twice5) (xs := [208, 383, 511, 592, 720, 895, 1023]) check rows elimOK (by decide) (by decide) cover3463 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3468 : P.CoversSplit 24 10 3468 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem h3468 : P.leaf 34 3468 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 3468) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 3468) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3468 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3553 : P.CoversSplit 24 10 3553 0x8000000000000000000000000000000080000000000000000000000000000000000000000000000000220000001100000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 466, 473, 515, 522, 858, 865, 915, 1209, 1217, 1266, 1609]) (by decide +kernel)

theorem h3553 : P.leaf 34 3553 = 85048 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 3553) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 3553) (weight := fun _ => 1) (xs := [511, 656, 660, 689, 693, 895, 1023]) check rows elimOK (by decide) (by decide) cover3553 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h3469 : P.leaf 34 3469 = 85048 :=
  orient4 (v := 3553) (by decide) (by decide +kernel) h3553

theorem cover3471 : P.CoversSplit 24 10 3471 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000800000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 515, 516, 522, 565, 858, 865, 1209, 1217, 1258]) (by decide +kernel)

theorem h3471 : P.leaf 34 3471 = 750364 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 3471) (keep := keep4) (twice := twice4) rows (by decide) (by decide) bal4 (invRow4 (H := 3471) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 3471) (weight := rowWeight keep4 twice4) (xs := [208, 383, 511, 592, 720, 895, 1023]) check rows elimOK (by decide) (by decide) cover3471 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover49167 : P.CoversSplit 24 10 49167 0x8001000100010001000100010001000180010001000100000001000100010000000100010001000100010001000100010001000100010000000100010001000080010001000100010001000100010001800100010000000000010001000000000001000100010001000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 516, 522, 529, 572, 858, 865, 1217, 1609]) (by decide +kernel)

noncomputable def f49167 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (50347008 + i)

theorem c49167_0 : rowSum f49167 0 1024 = 217446 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 49167) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover49167 (by decide)
  decide +kernel

theorem sum49167 : rowSum f49167 0 1024 = 217446 :=
  c49167_0

theorem h49167 : P.leaf 34 49167 = 217446 :=
  leaf_weighted (k := 24) (d := 10) (H := 49167) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 49167) (by decide) (by decide +kernel)) sum49167

theorem h3474 : P.leaf 34 3474 = 217446 :=
  orient24 (v := 49167) (by decide) (by decide +kernel) h49167

def seg : List (ℕ × ℕ) := [(3262, 48), (3263, 48), (3272, 24), (3273, 24), (3274, 48), (3275, 48), (3276, 48), (3277, 48), (3278, 48), (3279, 48), (3290, 24), (3291, 24), (3292, 48), (3293, 48), (3294, 48), (3295, 48), (3308, 24), (3309, 24), (3310, 48), (3311, 48), (3326, 24), (3327, 24), (3456, 3), (3457, 12), (3459, 12), (3460, 24), (3461, 48), (3463, 24), (3468, 12), (3469, 24), (3471, 12), (3474, 6)]

theorem segOK : checkSeg 16 perms 3262 3475 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 3262 3475 1041 905839296 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 905839296)
    (SegSum.cons (w := 48) h3262 (SegSum.cons (w := 48) h3263 (SegSum.cons (w := 24) h3272 (SegSum.cons (w := 24) h3273 (SegSum.cons (w := 48) h3274 (SegSum.cons (w := 48) h3275 (SegSum.cons (w := 48) h3276 (SegSum.cons (w := 48) h3277 (SegSum.cons (w := 48) h3278 (SegSum.cons (w := 48) h3279 (SegSum.cons (w := 24) h3290 (SegSum.cons (w := 24) h3291 (SegSum.cons (w := 48) h3292 (SegSum.cons (w := 48) h3293 (SegSum.cons (w := 48) h3294 (SegSum.cons (w := 48) h3295 (SegSum.cons (w := 24) h3308 (SegSum.cons (w := 24) h3309 (SegSum.cons (w := 48) h3310 (SegSum.cons (w := 48) h3311 (SegSum.cons (w := 24) h3326 (SegSum.cons (w := 24) h3327 (SegSum.cons (w := 3) h3456 (SegSum.cons (w := 12) h3457 (SegSum.cons (w := 12) h3459 (SegSum.cons (w := 24) h3460 (SegSum.cons (w := 48) h3461 (SegSum.cons (w := 24) h3463 (SegSum.cons (w := 12) h3468 (SegSum.cons (w := 24) h3469 (SegSum.cons (w := 12) h3471 (SegSum.cons (w := 6) h3474 (show SegSum (P.leaf 34) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S4N1.C0.S18
