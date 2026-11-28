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

namespace RACert.S4N1.C0.S19

open RACert RACert.Problem

theorem cover49183 : P.CoversSplit 24 10 49183 0xf000f00040004000f000f00040004000f000f00040004000f000f000400040002000200010001000200020001000100020002000000000002000200000000000f000f00040004000f000f00040004000f000f00040004000f000f000400040002000200000000000200020000000000020002000100010002000200010001000 :=
  coversProjected check rows (by decide) (by decide) (xs := [516, 529, 572, 858, 859, 865, 866, 872, 915]) (ps := [(8, [531, 580], [523])]) (by decide +kernel)

noncomputable def f49183 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (50363392 + i)

theorem c49183_0 : rowSum f49183 0 1024 = 1467424 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 49183) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover49183 (by decide)
  decide +kernel

theorem sum49183 : rowSum f49183 0 1024 = 1467424 :=
  c49183_0

theorem h49183 : P.leaf 34 49183 = 1467424 :=
  leaf_weighted (k := 24) (d := 10) (H := 49183) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 49183) (by decide) (by decide +kernel)) sum49183

theorem h3475 : P.leaf 34 3475 = 1467424 :=
  orient24 (v := 49183) (by decide) (by decide +kernel) h49183

theorem cover3476 : P.CoversSplit 24 10 3476 0x8000000000000000000000000000000080000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 475, 479, 508, 516, 865, 866, 915, 916, 1209, 1217]) (ps := [(6, [479], [473]), (8, [537], [1266])]) (by decide +kernel)

theorem h3476 : P.leaf 34 3476 = 15936 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 3476) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 3476) (weight := fun _ => 1) (xs := [189, 511, 701, 895, 1023]) check rows elimOK (by decide) (by decide) cover3476 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3491 : P.CoversSplit 24 10 3491 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 515, 517, 522, 524, 566, 858, 865, 1209, 1217, 1258, 1266]) (by decide +kernel)

theorem h3491 : P.leaf 34 3491 = 144184 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 3491) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 3491) (weight := fun _ => 1) (xs := [208, 511, 592, 720, 895, 1023]) check rows elimOK (by decide) (by decide) cover3491 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h3477 : P.leaf 34 3477 = 144184 :=
  orient4 (v := 3491) (by decide) (by decide +kernel) h3491

theorem cover49199 : P.CoversSplit 24 10 49199 0xc000400000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 517, 522, 529, 572, 858, 859, 860, 865, 871, 872]) (by decide +kernel)

theorem h49199 : P.leaf 34 49199 = 349528 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 49199) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 49199) (weight := fun _ => 1) (xs := [383, 511, 895, 1006, 1022, 1023]) check rows elimOK (by decide) (by decide) cover49199 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h3478 : P.leaf 34 3478 = 349528 :=
  orient24 (v := 49199) (by decide) (by decide +kernel) h49199

theorem cover49215 : P.CoversSplit 24 10 49215 0xf000f00000000000f000f00000000000f000f00000000000f000f000000000003000300000000000300030000000000030003000000000003000300000000000f000f00000000000f000f00000000000f000f00000000000f000f000000000002000200000000000200020000000000020002000000000002000200000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [517, 529, 572, 573, 858, 860, 865, 866, 871, 872, 915]) (by decide +kernel)

theorem c49215_0 : P.sumLeaves 24 50396160 1024 = 3592198 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 49215) (lo := 0) (len := 1024) (W := 3592198) check rows elimOK (by decide) (by decide) cover49215 (by decide)
  decide +kernel

theorem h49215 : P.leaf 34 49215 = 3592198 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 3592198)]) (.cons c49215_0 (.nil)) (by decide) (by decide))

theorem h3479 : P.leaf 34 3479 = 3592198 :=
  orient24 (v := 49215) (by decide) (by decide +kernel) h49215

theorem cover3554 : P.CoversSplit 24 10 3554 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 465, 466, 515, 522, 858, 865, 1209, 1217, 1258, 1266]) (by decide +kernel)

theorem h3554 : P.leaf 34 3554 = 77868 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 3554) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 3554) (weight := fun _ => 1) (xs := [208, 511, 592, 720, 895, 1023]) check rows elimOK (by decide) (by decide) cover3554 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h3484 : P.leaf 34 3484 = 77868 :=
  orient4 (v := 3554) (by decide) (by decide +kernel) h3554

theorem cover3555 : P.CoversSplit 24 10 3555 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 515, 522, 858, 865, 866, 915, 1209, 1217, 1258, 1266]) (by decide +kernel)

theorem h3555 : P.leaf 34 3555 = 743582 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 3555) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 3555) (weight := fun _ => 1) (xs := [208, 511, 592, 720, 895, 1023]) check rows elimOK (by decide) (by decide) cover3555 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h3485 : P.leaf 34 3485 = 743582 :=
  orient4 (v := 3555) (by decide) (by decide +kernel) h3555

theorem cover49263 : P.CoversSplit 24 10 49263 0xc0004000c00040000000000000000000c0004000c000400000000000000000000000000000000000003000100030001000000000000000000030001000300010c0004000c00040000000000000000000c0004000c000400000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 522, 572, 858, 859, 865, 1609]) (by decide +kernel)

theorem c49263_0 : P.sumLeaves 24 50445312 1024 = 3034331 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 49263) (lo := 0) (len := 1024) (W := 3034331) check rows elimOK (by decide) (by decide) cover49263 (by decide)
  decide +kernel

theorem h49263 : P.leaf 34 49263 = 3034331 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 3034331)]) (.cons c49263_0 (.nil)) (by decide) (by decide))

theorem h3486 : P.leaf 34 3486 = 3034331 :=
  orient24 (v := 49263) (by decide) (by decide +kernel) h49263

theorem cover49279 : P.CoversSplit 24 10 49279 0xf030f030f030f030f000f000f000f000f030f030f030f020f000f000f000f0003030303020302030300030002000200030303030203020303000300020002000f030f030f030f030f000f000f000f000f030f030f020f020f000f000f000f0003030303020302030300030002000200030003000200020003000300020002000 :=
  coversProjected check rows (by decide) (by decide) (xs := [572, 858, 859, 865, 866, 915, 1609]) (ps := [(12, [859], [915]), (14, [1217], [915])]) (by decide +kernel)

theorem c49279_0 : P.sumLeaves 24 50461696 478 = 1705470 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 49279) (lo := 0) (len := 478) (W := 1705470) check rows elimOK (by decide) (by decide) cover49279 (by decide)
  decide +kernel

theorem c49279_1 : P.sumLeaves 24 50462174 433 = 8610864 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 49279) (lo := 478) (len := 433) (W := 8610864) check rows elimOK (by decide) (by decide) cover49279 (by decide)
  decide +kernel

theorem c49279_2 : P.sumLeaves 24 50462607 113 = 9944360 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 49279) (lo := 911) (len := 113) (W := 9944360) check rows elimOK (by decide) (by decide) cover49279 (by decide)
  decide +kernel

theorem h49279 : P.leaf 34 49279 = 20260694 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(478, 1705470), (433, 8610864), (113, 9944360)]) (.cons c49279_0 (.cons c49279_1 (.cons c49279_2 (.nil)))) (by decide) (by decide))

theorem h3487 : P.leaf 34 3487 = 20260694 :=
  orient24 (v := 49279) (by decide) (by decide +kernel) h49279

theorem cover3492 : P.CoversSplit 24 10 3492 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem h3492 : P.leaf 34 3492 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 3492) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 3492) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3492 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3493 : P.CoversSplit 24 10 3493 0x8000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 466, 473, 475, 515, 522, 566, 858, 865, 915, 1202, 1209, 1217, 1266]) (by decide +kernel)

theorem h3493 : P.leaf 34 3493 = 36512 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 3493) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 3493) (weight := fun _ => 1) (xs := [511, 895, 1023]) check rows elimOK (by decide) (by decide) cover3493 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3494 : P.CoversSplit 24 10 3494 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 465, 466, 515, 517, 522, 858, 865, 1209, 1258, 1266]) (by decide +kernel)

theorem h3494 : P.leaf 34 3494 = 55504 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 3494) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 3494) (weight := fun _ => 1) (xs := [208, 511, 720, 895, 1023]) check rows elimOK (by decide) (by decide) cover3494 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3495 : P.CoversSplit 24 10 3495 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 515, 517, 522, 524, 566, 858, 865, 1209, 1217, 1258, 1266]) (by decide +kernel)

theorem h3495 : P.leaf 34 3495 = 209920 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 3495) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 3495) (weight := fun _ => 1) (xs := [208, 511, 592, 720, 895, 1023]) check rows elimOK (by decide) (by decide) cover3495 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3496 : P.CoversSplit 24 10 3496 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem h3496 : P.leaf 34 3496 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 3496) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 3496) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3496 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3497 : P.CoversSplit 24 10 3497 0x8000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 466, 473, 474, 515, 522, 566, 858, 865, 915, 1202, 1209, 1217, 1266]) (by decide +kernel)

theorem h3497 : P.leaf 34 3497 = 123392 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 3497) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 3497) (weight := fun _ => 1) (xs := [511, 895, 1023]) check rows elimOK (by decide) (by decide) cover3497 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3498 : P.CoversSplit 24 10 3498 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 465, 466, 515, 517, 522, 858, 865, 1209, 1258, 1266]) (by decide +kernel)

theorem h3498 : P.leaf 34 3498 = 54800 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 3498) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 3498) (weight := fun _ => 1) (xs := [208, 511, 720, 895, 1023]) check rows elimOK (by decide) (by decide) cover3498 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3499 : P.CoversSplit 24 10 3499 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 515, 517, 522, 524, 566, 858, 865, 1209, 1217, 1258, 1266]) (by decide +kernel)

theorem h3499 : P.leaf 34 3499 = 545752 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 3499) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 3499) (weight := fun _ => 1) (xs := [208, 511, 592, 720, 895, 1023]) check rows elimOK (by decide) (by decide) cover3499 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3500 : P.CoversSplit 24 10 3500 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem h3500 : P.leaf 34 3500 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 3500) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 3500) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3500 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3501 : P.CoversSplit 24 10 3501 0x8000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 466, 473, 515, 522, 524, 566, 858, 865, 915, 1202, 1209, 1217, 1266]) (by decide +kernel)

theorem h3501 : P.leaf 34 3501 = 166496 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 3501) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 3501) (weight := fun _ => 1) (xs := [511, 895, 1023]) check rows elimOK (by decide) (by decide) cover3501 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3502 : P.CoversSplit 24 10 3502 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 465, 466, 515, 517, 522, 858, 865, 1209, 1258, 1266]) (by decide +kernel)

theorem h3502 : P.leaf 34 3502 = 381120 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 3502) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 3502) (weight := fun _ => 1) (xs := [208, 511, 720, 895, 1023]) check rows elimOK (by decide) (by decide) cover3502 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3503 : P.CoversSplit 24 10 3503 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 515, 517, 522, 524, 566, 858, 865, 1209, 1217, 1258, 1266]) (by decide +kernel)

theorem h3503 : P.leaf 34 3503 = 1187447 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 3503) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 3503) (weight := fun _ => 1) (xs := [208, 511, 592, 720, 895, 1023]) check rows elimOK (by decide) (by decide) cover3503 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover49327 : P.CoversSplit 24 10 49327 0xf0005000000000003000100000000000a00000000000000020000000000000000000000000000000000000000000000000000000000000000000000000000000c0004000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 517, 522, 573, 858, 859, 860, 865, 871, 872, 916, 921]) (by decide +kernel)

theorem h49327 : P.leaf 34 49327 = 996476 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 49327) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 49327) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 49327) (weight := rowWeight keep0 twice0) (xs := [383, 494, 510, 511, 829, 893, 895, 940, 956, 957, 1004, 1006, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover49327 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h3510 : P.leaf 34 3510 = 996476 :=
  orient24 (v := 49327) (by decide) (by decide +kernel) h49327

theorem cover49343 : P.CoversSplit 24 10 49343 0xf000f00000000000f000f00000000000f000f00000000000f000f000000000000000000000000000000000000000000000000000000000000000000000000000f000f00000000000f000f00000000000f000f00000000000f000f000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [517, 573, 858, 860, 865, 867, 871, 872, 916, 921]) (by decide +kernel)

noncomputable def f49343 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (50527232 + i)

theorem c49343_0 : rowSum f49343 0 1024 = 6493292 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 49343) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover49343 (by decide)
  decide +kernel

theorem sum49343 : rowSum f49343 0 1024 = 6493292 :=
  c49343_0

theorem h49343 : P.leaf 34 49343 = 6493292 :=
  leaf_weighted (k := 24) (d := 10) (H := 49343) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 49343) (by decide) (by decide +kernel)) sum49343

theorem h3511 : P.leaf 34 3511 = 6493292 :=
  orient24 (v := 49343) (by decide) (by decide +kernel) h49343

theorem cover49359 : P.CoversSplit 24 10 49359 0xf000500000000000300010000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 516, 522, 536, 573, 858, 859, 860, 865, 871, 879, 916, 921]) (by decide +kernel)

theorem h49359 : P.leaf 34 49359 = 1501048 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 49359) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 49359) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 49359) (weight := rowWeight keep1 twice1) (xs := [383, 511, 895, 940, 956, 957, 1004, 1006, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover49359 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h3514 : P.leaf 34 3514 = 1501048 :=
  orient24 (v := 49359) (by decide) (by decide +kernel) h49359

theorem cover49375 : P.CoversSplit 24 10 49375 0xf000f00000000000f000f00000000000f000f00000000000f000f000000000000000000000000000000000000000000000000000000000000000000000000000f000f00000000000f000f00000000000f000f00000000000f000f000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [516, 536, 573, 858, 859, 860, 865, 867, 871, 879, 916, 921]) (by decide +kernel)

noncomputable def f49375 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (50560000 + i)

theorem c49375_0 : rowSum f49375 0 1024 = 11112144 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 49375) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover49375 (by decide)
  decide +kernel

theorem sum49375 : rowSum f49375 0 1024 = 11112144 :=
  c49375_0

theorem h49375 : P.leaf 34 49375 = 11112144 :=
  leaf_weighted (k := 24) (d := 10) (H := 49375) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 49375) (by decide) (by decide +kernel)) sum49375

theorem h3515 : P.leaf 34 3515 = 11112144 :=
  orient24 (v := 49375) (by decide) (by decide +kernel) h49375

theorem cover3558 : P.CoversSplit 24 10 3558 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 465, 466, 515, 522, 858, 865, 1209, 1217, 1258, 1266]) (by decide +kernel)

theorem h3558 : P.leaf 34 3558 = 204732 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 3558) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 3558) (weight := fun _ => 1) (xs := [208, 511, 592, 720, 895, 1023]) check rows elimOK (by decide) (by decide) cover3558 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h3516 : P.leaf 34 3516 = 204732 :=
  orient4 (v := 3558) (by decide) (by decide +kernel) h3558

theorem cover3559 : P.CoversSplit 24 10 3559 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 515, 522, 858, 865, 866, 915, 1209, 1217, 1258, 1266]) (by decide +kernel)

theorem h3559 : P.leaf 34 3559 = 923626 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 3559) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 3559) (weight := fun _ => 1) (xs := [208, 511, 592, 720, 895, 1023]) check rows elimOK (by decide) (by decide) cover3559 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h3517 : P.leaf 34 3517 = 923626 :=
  orient4 (v := 3559) (by decide) (by decide +kernel) h3559

theorem cover49391 : P.CoversSplit 24 10 49391 0xf0005000f00050003000100030001000f0005000f000500030001000300010000000000000000000000000000000000000000000000000000000000000000000c0004000c00040000000000000000000c0004000c000400000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 522, 573, 858, 859, 865, 879, 916, 921]) (by decide +kernel)

theorem c49391_0 : P.sumLeaves 24 50576384 1024 = 6815788 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 49391) (lo := 0) (len := 1024) (W := 6815788) check rows elimOK (by decide) (by decide) cover49391 (by decide)
  decide +kernel

theorem h49391 : P.leaf 34 49391 = 6815788 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 6815788)]) (.cons c49391_0 (.nil)) (by decide) (by decide))

theorem h3518 : P.leaf 34 3518 = 6815788 :=
  orient24 (v := 49391) (by decide) (by decide +kernel) h49391

theorem cover49407 : P.CoversSplit 24 10 49407 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0000000000000000000000000000000000000000000000000000000000000000000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [573, 858, 859, 865, 867, 915, 916, 921]) (by decide +kernel)

theorem c49407_0 : P.sumLeaves 24 50592768 908 = 13811245 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 49407) (lo := 0) (len := 908) (W := 13811245) check rows elimOK (by decide) (by decide) cover49407 (by decide)
  decide +kernel

theorem c49407_1 : P.sumLeaves 24 50593676 116 = 15369838 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 49407) (lo := 908) (len := 116) (W := 15369838) check rows elimOK (by decide) (by decide) cover49407 (by decide)
  decide +kernel

theorem h49407 : P.leaf 34 49407 = 29181083 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(908, 13811245), (116, 15369838)]) (.cons c49407_0 (.cons c49407_1 (.nil))) (by decide) (by decide))

theorem h3519 : P.leaf 34 3519 = 29181083 :=
  orient24 (v := 49407) (by decide) (by decide +kernel) h49407

theorem cover3564 : P.CoversSplit 24 10 3564 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem h3564 : P.leaf 34 3564 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 3564) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 3564) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover3564 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3565 : P.CoversSplit 24 10 3565 0x8000000000000000000000000000000080000000000000000000000000000000000000000000000000220000001100000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 466, 473, 515, 522, 858, 865, 915, 1209, 1217, 1266, 1609]) (by decide +kernel)

theorem h3565 : P.leaf 34 3565 = 315336 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 3565) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 3565) (weight := fun _ => 1) (xs := [511, 656, 660, 689, 693, 895, 1023]) check rows elimOK (by decide) (by decide) cover3565 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover3566 : P.CoversSplit 24 10 3566 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 465, 466, 515, 522, 858, 865, 1209, 1217, 1258, 1266]) (by decide +kernel)

theorem h3566 : P.leaf 34 3566 = 1218256 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 3566) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 3566) (weight := fun _ => 1) (xs := [208, 511, 592, 720, 895, 1023]) check rows elimOK (by decide) (by decide) cover3566 (by decide) (by decide) (by decide +kernel)
  decide +kernel

def seg : List (ℕ × ℕ) := [(3475, 12), (3476, 48), (3477, 48), (3478, 48), (3479, 48), (3484, 24), (3485, 24), (3486, 24), (3487, 24), (3492, 24), (3493, 24), (3494, 48), (3495, 48), (3496, 24), (3497, 24), (3498, 48), (3499, 48), (3500, 48), (3501, 48), (3502, 48), (3503, 48), (3510, 24), (3511, 24), (3514, 24), (3515, 24), (3516, 48), (3517, 48), (3518, 48), (3519, 48), (3564, 12), (3565, 12), (3566, 24)]

theorem segOK : checkSeg 16 perms 3475 3567 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 3475 3567 1116 3219484872 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 3219484872)
    (SegSum.cons (w := 12) h3475 (SegSum.cons (w := 48) h3476 (SegSum.cons (w := 48) h3477 (SegSum.cons (w := 48) h3478 (SegSum.cons (w := 48) h3479 (SegSum.cons (w := 24) h3484 (SegSum.cons (w := 24) h3485 (SegSum.cons (w := 24) h3486 (SegSum.cons (w := 24) h3487 (SegSum.cons (w := 24) h3492 (SegSum.cons (w := 24) h3493 (SegSum.cons (w := 48) h3494 (SegSum.cons (w := 48) h3495 (SegSum.cons (w := 24) h3496 (SegSum.cons (w := 24) h3497 (SegSum.cons (w := 48) h3498 (SegSum.cons (w := 48) h3499 (SegSum.cons (w := 48) h3500 (SegSum.cons (w := 48) h3501 (SegSum.cons (w := 48) h3502 (SegSum.cons (w := 48) h3503 (SegSum.cons (w := 24) h3510 (SegSum.cons (w := 24) h3511 (SegSum.cons (w := 24) h3514 (SegSum.cons (w := 24) h3515 (SegSum.cons (w := 48) h3516 (SegSum.cons (w := 48) h3517 (SegSum.cons (w := 48) h3518 (SegSum.cons (w := 48) h3519 (SegSum.cons (w := 12) h3564 (SegSum.cons (w := 12) h3565 (SegSum.cons (w := 24) h3566 (show SegSum (P.leaf 34) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S4N1.C0.S19
