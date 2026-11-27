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

namespace RACert.S4N1.C0.S49

open RACert RACert.Problem

theorem cover7167 : P.CoversSplit 24 10 7167 0xffffffffafafaaaaffffffffafafaaaaffffffffafafaaaaffffffffafafaaaaccffccff88888888cccccccc88888888ccffccff88888888cccccccc88888888ffffffffafafaaaaffffffffafafaaaaffffffffaaaaaaaaffffffffaaaaaaaaccffccff88888888cccccccc88888888cccccccc88888888cccccccc88888888 :=
  coversSplit check rows (by decide) (by decide) (xs := [859, 916, 1202, 1209, 1217, 1258, 1259, 1601, 1609]) (by decide +kernel)

noncomputable def f7167 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (7339008 + i)

theorem c7167_0 : rowSum f7167 0 254 = 80324810 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 7167) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover7167 (by decide)
  decide +kernel

theorem c7167_1 : rowSum f7167 254 207 = 138348656 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 7167) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover7167 (by decide)
  decide +kernel

theorem c7167_2 : rowSum f7167 461 467 = 273706107 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 7167) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover7167 (by decide)
  decide +kernel

theorem c7167_3 : rowSum f7167 928 96 = 201589796 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 7167) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover7167 (by decide)
  decide +kernel

theorem sum7167 : rowSum f7167 0 1024 = 693969369 :=
  rowSum_append (F := f7167) (lo := 0) (n := 254) (m := 770) (A := 80324810) (B := 613644559) c7167_0 (rowSum_append (F := f7167) (lo := 254) (n := 207) (m := 563) (A := 138348656) (B := 475295903) c7167_1 (rowSum_append (F := f7167) (lo := 461) (n := 467) (m := 96) (A := 273706107) (B := 201589796) c7167_2 (c7167_3)))

theorem h7167 : P.leaf 34 7167 = 693969369 :=
  leaf_weighted (k := 24) (d := 10) (H := 7167) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 7167) (by decide) (by decide +kernel)) sum7167

theorem cover7396 : P.CoversSplit 24 10 7396 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem c7396_0 : P.sumLeaves 24 7573504 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7396) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover7396 (by decide)
  decide +kernel

theorem h7396 : P.leaf 34 7396 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c7396_0 (.nil)) (by decide) (by decide))

theorem cover7397 : P.CoversSplit 24 10 7397 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 466, 473, 515, 522, 573, 858, 865, 1209, 1258, 1272]) (by decide +kernel)

theorem c7397_0 : P.sumLeaves 24 7574528 1024 = 73600 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7397) (lo := 0) (len := 1024) (W := 73600) check rows elimOK (by decide) (by decide) cover7397 (by decide)
  decide +kernel

theorem h7397 : P.leaf 34 7397 = 73600 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 73600)]) (.cons c7397_0 (.nil)) (by decide) (by decide))

theorem cover7398 : P.CoversSplit 24 10 7398 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 465, 466, 515, 522, 524, 566, 573, 858, 865, 1209, 1258, 1272]) (by decide +kernel)

theorem c7398_0 : P.sumLeaves 24 7575552 1024 = 378448 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7398) (lo := 0) (len := 1024) (W := 378448) check rows elimOK (by decide) (by decide) cover7398 (by decide)
  decide +kernel

theorem h7398 : P.leaf 34 7398 = 378448 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 378448)]) (.cons c7398_0 (.nil)) (by decide) (by decide))

theorem cover7399 : P.CoversSplit 24 10 7399 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 515, 522, 524, 566, 573, 858, 865, 1209, 1217, 1258, 1272, 1651]) (by decide +kernel)

theorem c7399_0 : P.sumLeaves 24 7576576 1024 = 682184 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7399) (lo := 0) (len := 1024) (W := 682184) check rows elimOK (by decide) (by decide) cover7399 (by decide)
  decide +kernel

theorem h7399 : P.leaf 34 7399 = 682184 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 682184)]) (.cons c7399_0 (.nil)) (by decide) (by decide))

theorem cover7404 : P.CoversSplit 24 10 7404 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem c7404_0 : P.sumLeaves 24 7581696 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7404) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover7404 (by decide)
  decide +kernel

theorem h7404 : P.leaf 34 7404 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c7404_0 (.nil)) (by decide) (by decide))

theorem cover7405 : P.CoversSplit 24 10 7405 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 466, 473, 515, 522, 573, 858, 865, 1209, 1258, 1272]) (by decide +kernel)

theorem c7405_0 : P.sumLeaves 24 7582720 1024 = 424314 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7405) (lo := 0) (len := 1024) (W := 424314) check rows elimOK (by decide) (by decide) cover7405 (by decide)
  decide +kernel

theorem h7405 : P.leaf 34 7405 = 424314 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 424314)]) (.cons c7405_0 (.nil)) (by decide) (by decide))

theorem cover7406 : P.CoversSplit 24 10 7406 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 465, 466, 515, 522, 524, 566, 573, 858, 865, 1209, 1258, 1272]) (by decide +kernel)

theorem c7406_0 : P.sumLeaves 24 7583744 1024 = 922784 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7406) (lo := 0) (len := 1024) (W := 922784) check rows elimOK (by decide) (by decide) cover7406 (by decide)
  decide +kernel

theorem h7406 : P.leaf 34 7406 = 922784 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 922784)]) (.cons c7406_0 (.nil)) (by decide) (by decide))

theorem cover7407 : P.CoversSplit 24 10 7407 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 515, 522, 524, 566, 573, 858, 865, 1209, 1217, 1258, 1272, 1651]) (by decide +kernel)

theorem c7407_0 : P.sumLeaves 24 7584768 1024 = 1104842 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7407) (lo := 0) (len := 1024) (W := 1104842) check rows elimOK (by decide) (by decide) cover7407 (by decide)
  decide +kernel

theorem h7407 : P.leaf 34 7407 = 1104842 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1104842)]) (.cons c7407_0 (.nil)) (by decide) (by decide))

theorem cover7412 : P.CoversSplit 24 10 7412 0xf0000000f00000000000000000000000f0000000f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 573, 858, 865, 866, 916, 1210, 1259, 1308]) (ps := [(8, [580], [475])]) (by decide +kernel)

theorem c7412_0 : P.sumLeaves 24 7589888 1024 = 257264 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7412) (lo := 0) (len := 1024) (W := 257264) check rows elimOK (by decide) (by decide) cover7412 (by decide)
  decide +kernel

theorem h7412 : P.leaf 34 7412 = 257264 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 257264)]) (.cons c7412_0 (.nil)) (by decide) (by decide))

theorem cover7413 : P.CoversSplit 24 10 7413 0xff00ff00ff0000000000000000000000ff00ff00ff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 573, 858, 865, 866, 1209, 1210, 1217, 1259, 1308]) (ps := [(8, [580], [475])]) (by decide +kernel)

theorem c7413_0 : P.sumLeaves 24 7590912 1024 = 1327752 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7413) (lo := 0) (len := 1024) (W := 1327752) check rows elimOK (by decide) (by decide) cover7413 (by decide)
  decide +kernel

theorem h7413 : P.leaf 34 7413 = 1327752 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1327752)]) (.cons c7413_0 (.nil)) (by decide) (by decide))

theorem cover7414 : P.CoversSplit 24 10 7414 0xf0f00000f0f500000000000000000000f0f00000f0f5000000000000000000000000000000000000000000000000000000000000000000000000000000000000c0000000c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 573, 858, 865, 866, 908, 916, 1210, 1217, 1259, 1264, 1308]) (by decide +kernel)

theorem c7414_0 : P.sumLeaves 24 7591936 1024 = 6026177 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7414) (lo := 0) (len := 1024) (W := 6026177) check rows elimOK (by decide) (by decide) cover7414 (by decide)
  decide +kernel

theorem h7414 : P.leaf 34 7414 = 6026177 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 6026177)]) (.cons c7414_0 (.nil)) (by decide) (by decide))

theorem cover7415 : P.CoversSplit 24 10 7415 0xfffffffffffa00000000000000000000fffffffffffa000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00cc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [573, 858, 865, 866, 916, 1209, 1210, 1217, 1259, 1264, 1308]) (by decide +kernel)

theorem c7415_0 : P.sumLeaves 24 7592960 1016 = 15807308 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7415) (lo := 0) (len := 1016) (W := 15807308) check rows elimOK (by decide) (by decide) cover7415 (by decide)
  decide +kernel

theorem c7415_1 : P.sumLeaves 24 7593976 8 = 6167600 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7415) (lo := 1016) (len := 8) (W := 6167600) check rows elimOK (by decide) (by decide) cover7415 (by decide)
  decide +kernel

theorem h7415 : P.leaf 34 7415 = 21974908 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1016, 15807308), (8, 6167600)]) (.cons c7415_0 (.cons c7415_1 (.nil))) (by decide) (by decide))

theorem cover7416 : P.CoversSplit 24 10 7416 0xf0000000f00000000000000000000000f0000000f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 487, 858, 865, 867, 916, 1210, 1259]) (by decide +kernel)

theorem c7416_0 : P.sumLeaves 24 7593984 1024 = 637456 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7416) (lo := 0) (len := 1024) (W := 637456) check rows elimOK (by decide) (by decide) cover7416 (by decide)
  decide +kernel

theorem h7416 : P.leaf 34 7416 = 637456 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 637456)]) (.cons c7416_0 (.nil)) (by decide) (by decide))

theorem cover7417 : P.CoversSplit 24 10 7417 0xff000000ff0000000000000000000000ff000000ff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 487, 858, 865, 867, 1209, 1210, 1259]) (by decide +kernel)

theorem c7417_0 : P.sumLeaves 24 7595008 1024 = 4904080 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7417) (lo := 0) (len := 1024) (W := 4904080) check rows elimOK (by decide) (by decide) cover7417 (by decide)
  decide +kernel

theorem h7417 : P.leaf 34 7417 = 4904080 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 4904080)]) (.cons c7417_0 (.nil)) (by decide) (by decide))

theorem cover7418 : P.CoversSplit 24 10 7418 0xf0f00000f0f500000000000000000000f0f00000f0f5000000000000000000000000000000000000000000000000000000000000000000000000000000000000c0000000c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 487, 573, 858, 865, 867, 909, 916, 1210, 1217, 1259, 1264, 1308]) (by decide +kernel)

theorem c7418_0 : P.sumLeaves 24 7596032 448 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7418) (lo := 0) (len := 448) (W := 0) check rows elimOK (by decide) (by decide) cover7418 (by decide)
  decide +kernel

theorem contract7418_1 : P.leaf 30 118695 = 104016 := by
  exact leaf_contract_factors (k := 30) (b := 20) (H := 118695) (ss := [(27, 1, 573), (8, 1, 580), (18, 1, 580), (30, 1, 867), (29, 1, 916), (28, 1, 858), (14, 1, 923), (16, 1, 1265), (20, 1, 1657), (21, 1, 1658)]) (ids := [0, 1, 2, 3, 4, 5, 7, 8, 9, 10, 13, 15, 17, 20, 21, 22, 24, 29, 11, 23]) (cs := [2, 3, 4, 5, 6, 7, 1, 8, 9, 10, 11, 20, 1, 12, 1, 13, 1, 14, 1, 1, 15, 16, 17, 21, 18, 1, 1, 1, 1, 19]) (bs := [18, 2]) (W := 104016) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c7418_1 : P.sumLeaves 24 7596480 64 = 104016 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 118695) rows (by decide) (by decide)).symm.trans contract7418_1

theorem c7418_2 : P.sumLeaves 24 7596544 512 = 5549166 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7418) (lo := 512) (len := 512) (W := 5549166) check rows elimOK (by decide) (by decide) cover7418 (by decide)
  decide +kernel

theorem h7418 : P.leaf 34 7418 = 5653182 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(448, 0), (64, 104016), (512, 5549166)]) (.cons c7418_0 (.cons c7418_1 (.cons c7418_2 (.nil)))) (by decide) (by decide))

theorem cover7419 : P.CoversSplit 24 10 7419 0xffff0000fffa00000000000000000000ffff0000fffa000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000cc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [487, 573, 858, 865, 867, 909, 916, 1209, 1210, 1217, 1259, 1264, 1308]) (by decide +kernel)

theorem c7419_0 : P.sumLeaves 24 7597056 1024 = 14649606 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7419) (lo := 0) (len := 1024) (W := 14649606) check rows elimOK (by decide) (by decide) cover7419 (by decide)
  decide +kernel

theorem h7419 : P.leaf 34 7419 = 14649606 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 14649606)]) (.cons c7419_0 (.nil)) (by decide) (by decide))

theorem cover7420 : P.CoversSplit 24 10 7420 0xf0000000f00000000000000000000000f0000000f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c0000000c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 573, 858, 865, 916, 1210, 1259, 1308]) (by decide +kernel)

theorem c7420_0 : P.sumLeaves 24 7598080 448 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7420) (lo := 0) (len := 448) (W := 0) check rows elimOK (by decide) (by decide) cover7420 (by decide)
  decide +kernel

theorem contract7420_1 : P.leaf 30 118727 = 66992 := by
  exact leaf_contract_factors (k := 30) (b := 21) (H := 118727) (ss := [(2, 1, 466), (18, 1, 487), (27, 1, 573), (8, 1, 580), (29, 1, 865), (16, 1, 1265), (20, 1, 1657), (21, 1, 1658), (14, 1, 923)]) (ids := [1, 2, 3, 4, 7, 8, 9, 10, 13, 15, 17, 20, 21, 22, 24, 26, 28, 29, 5, 11, 23]) (cs := [1, 2, 3, 4, 5, 20, 1, 6, 7, 8, 9, 21, 1, 10, 1, 11, 1, 12, 1, 1, 13, 14, 15, 22, 16, 1, 17, 1, 18, 19]) (bs := [18, 3]) (W := 66992) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c7420_1 : P.sumLeaves 24 7598528 64 = 66992 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 118727) rows (by decide) (by decide)).symm.trans contract7420_1

theorem c7420_2 : P.sumLeaves 24 7598592 512 = 1767996 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7420) (lo := 512) (len := 512) (W := 1767996) check rows elimOK (by decide) (by decide) cover7420 (by decide)
  decide +kernel

theorem h7420 : P.leaf 34 7420 = 1834988 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(448, 0), (64, 66992), (512, 1767996)]) (.cons c7420_0 (.cons c7420_1 (.cons c7420_2 (.nil)))) (by decide) (by decide))

theorem cover7421 : P.CoversSplit 24 10 7421 0xff00ff00ff0000000000000000000000ff00ff00ff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00cc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 573, 858, 865, 1209, 1210, 1217, 1259, 1308]) (by decide +kernel)

theorem c7421_0 : P.sumLeaves 24 7599104 1024 = 8607402 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7421) (lo := 0) (len := 1024) (W := 8607402) check rows elimOK (by decide) (by decide) cover7421 (by decide)
  decide +kernel

theorem h7421 : P.leaf 34 7421 = 8607402 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 8607402)]) (.cons c7421_0 (.nil)) (by decide) (by decide))

theorem cover7422 : P.CoversSplit 24 10 7422 0xf0f00000f0f500000000000000000000f0f00000f0f5000000000000000000000000000000000000000000000000000000000000000000000000000000000000c0000000c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 573, 858, 865, 916, 1210, 1217, 1259, 1264, 1308]) (by decide +kernel)

theorem c7422_0 : P.sumLeaves 24 7600128 1024 = 15938906 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7422) (lo := 0) (len := 1024) (W := 15938906) check rows elimOK (by decide) (by decide) cover7422 (by decide)
  decide +kernel

theorem h7422 : P.leaf 34 7422 = 15938906 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 15938906)]) (.cons c7422_0 (.nil)) (by decide) (by decide))

theorem cover7423 : P.CoversSplit 24 10 7423 0xfffffffffffa00000000000000000000fffffffffffa000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00cc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [573, 858, 865, 916, 1209, 1210, 1217, 1259, 1264, 1308]) (by decide +kernel)

theorem c7423_0 : P.sumLeaves 24 7601152 1016 = 29841479 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7423) (lo := 0) (len := 1016) (W := 29841479) check rows elimOK (by decide) (by decide) cover7423 (by decide)
  decide +kernel

theorem c7423_1 : P.sumLeaves 24 7602168 8 = 7845664 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7423) (lo := 1016) (len := 8) (W := 7845664) check rows elimOK (by decide) (by decide) cover7423 (by decide)
  decide +kernel

theorem h7423 : P.leaf 34 7423 = 37687143 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1016, 29841479), (8, 7845664)]) (.cons c7423_0 (.cons c7423_1 (.nil))) (by decide) (by decide))

theorem cover7524 : P.CoversSplit 24 10 7524 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem c7524_0 : P.sumLeaves 24 7704576 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7524) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover7524 (by decide)
  decide +kernel

theorem h7524 : P.leaf 34 7524 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c7524_0 (.nil)) (by decide) (by decide))

theorem cover7525 : P.CoversSplit 24 10 7525 0x8000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000002000000001000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 466, 473, 515, 522, 572, 858, 865, 1209, 1210, 1217, 1258, 1266]) (by decide +kernel)

theorem c7525_0 : P.sumLeaves 24 7705600 1024 = 289650 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7525) (lo := 0) (len := 1024) (W := 289650) check rows elimOK (by decide) (by decide) cover7525 (by decide)
  decide +kernel

theorem h7525 : P.leaf 34 7525 = 289650 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 289650)]) (.cons c7525_0 (.nil)) (by decide) (by decide))

theorem cover7526 : P.CoversSplit 24 10 7526 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 465, 466, 515, 522, 523, 565, 858, 865, 1209, 1217, 1258, 1266, 1609]) (by decide +kernel)

theorem c7526_0 : P.sumLeaves 24 7706624 1024 = 1642208 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7526) (lo := 0) (len := 1024) (W := 1642208) check rows elimOK (by decide) (by decide) cover7526 (by decide)
  decide +kernel

theorem h7526 : P.leaf 34 7526 = 1642208 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1642208)]) (.cons c7526_0 (.nil)) (by decide) (by decide))

theorem cover7527 : P.CoversSplit 24 10 7527 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 515, 522, 523, 572, 858, 865, 1209, 1217, 1258, 1266, 1609]) (by decide +kernel)

theorem c7527_0 : P.sumLeaves 24 7707648 1024 = 2586416 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7527) (lo := 0) (len := 1024) (W := 2586416) check rows elimOK (by decide) (by decide) cover7527 (by decide)
  decide +kernel

theorem h7527 : P.leaf 34 7527 = 2586416 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 2586416)]) (.cons c7527_0 (.nil)) (by decide) (by decide))

theorem cover7528 : P.CoversSplit 24 10 7528 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem c7528_0 : P.sumLeaves 24 7708672 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7528) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover7528 (by decide)
  decide +kernel

theorem h7528 : P.leaf 34 7528 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c7528_0 (.nil)) (by decide) (by decide))

theorem cover7529 : P.CoversSplit 24 10 7529 0x8000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000002000000001000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 466, 473, 515, 522, 572, 858, 865, 1209, 1210, 1217, 1258, 1266]) (by decide +kernel)

theorem c7529_0 : P.sumLeaves 24 7709696 1024 = 125174 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7529) (lo := 0) (len := 1024) (W := 125174) check rows elimOK (by decide) (by decide) cover7529 (by decide)
  decide +kernel

theorem h7529 : P.leaf 34 7529 = 125174 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 125174)]) (.cons c7529_0 (.nil)) (by decide) (by decide))

theorem cover7530 : P.CoversSplit 24 10 7530 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 465, 466, 515, 522, 523, 565, 858, 865, 1209, 1217, 1258, 1266, 1609]) (by decide +kernel)

theorem c7530_0 : P.sumLeaves 24 7710720 1024 = 401071 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7530) (lo := 0) (len := 1024) (W := 401071) check rows elimOK (by decide) (by decide) cover7530 (by decide)
  decide +kernel

theorem h7530 : P.leaf 34 7530 = 401071 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 401071)]) (.cons c7530_0 (.nil)) (by decide) (by decide))

theorem cover7531 : P.CoversSplit 24 10 7531 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 515, 522, 523, 572, 858, 865, 1209, 1217, 1258, 1266, 1609]) (by decide +kernel)

theorem c7531_0 : P.sumLeaves 24 7711744 1024 = 749619 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7531) (lo := 0) (len := 1024) (W := 749619) check rows elimOK (by decide) (by decide) cover7531 (by decide)
  decide +kernel

theorem h7531 : P.leaf 34 7531 = 749619 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 749619)]) (.cons c7531_0 (.nil)) (by decide) (by decide))

theorem cover7532 : P.CoversSplit 24 10 7532 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem c7532_0 : P.sumLeaves 24 7712768 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7532) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover7532 (by decide)
  decide +kernel

theorem h7532 : P.leaf 34 7532 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c7532_0 (.nil)) (by decide) (by decide))

theorem cover7533 : P.CoversSplit 24 10 7533 0x8000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000002000000001000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 466, 473, 515, 522, 572, 858, 865, 1209, 1210, 1217, 1258, 1266]) (by decide +kernel)

theorem c7533_0 : P.sumLeaves 24 7713792 1024 = 947610 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7533) (lo := 0) (len := 1024) (W := 947610) check rows elimOK (by decide) (by decide) cover7533 (by decide)
  decide +kernel

theorem h7533 : P.leaf 34 7533 = 947610 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 947610)]) (.cons c7533_0 (.nil)) (by decide) (by decide))

theorem cover7534 : P.CoversSplit 24 10 7534 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 465, 466, 515, 522, 523, 565, 858, 865, 1209, 1217, 1258, 1266, 1609]) (by decide +kernel)

theorem c7534_0 : P.sumLeaves 24 7714816 1024 = 2076219 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7534) (lo := 0) (len := 1024) (W := 2076219) check rows elimOK (by decide) (by decide) cover7534 (by decide)
  decide +kernel

theorem h7534 : P.leaf 34 7534 = 2076219 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 2076219)]) (.cons c7534_0 (.nil)) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(7167, 24), (7396, 48), (7397, 48), (7398, 48), (7399, 48), (7404, 24), (7405, 24), (7406, 24), (7407, 24), (7412, 48), (7413, 48), (7414, 48), (7415, 48), (7416, 48), (7417, 48), (7418, 48), (7419, 48), (7420, 48), (7421, 48), (7422, 48), (7423, 48), (7524, 24), (7525, 24), (7526, 24), (7527, 24), (7528, 24), (7529, 24), (7530, 24), (7531, 24), (7532, 24), (7533, 24), (7534, 24)]

theorem segOK : checkSeg 16 perms 7167 7535 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 7167 7535 1152 22716131232 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 22716131232)
    (SegSum.cons (w := 24) h7167 (SegSum.cons (w := 48) h7396 (SegSum.cons (w := 48) h7397 (SegSum.cons (w := 48) h7398 (SegSum.cons (w := 48) h7399 (SegSum.cons (w := 24) h7404 (SegSum.cons (w := 24) h7405 (SegSum.cons (w := 24) h7406 (SegSum.cons (w := 24) h7407 (SegSum.cons (w := 48) h7412 (SegSum.cons (w := 48) h7413 (SegSum.cons (w := 48) h7414 (SegSum.cons (w := 48) h7415 (SegSum.cons (w := 48) h7416 (SegSum.cons (w := 48) h7417 (SegSum.cons (w := 48) h7418 (SegSum.cons (w := 48) h7419 (SegSum.cons (w := 48) h7420 (SegSum.cons (w := 48) h7421 (SegSum.cons (w := 48) h7422 (SegSum.cons (w := 48) h7423 (SegSum.cons (w := 24) h7524 (SegSum.cons (w := 24) h7525 (SegSum.cons (w := 24) h7526 (SegSum.cons (w := 24) h7527 (SegSum.cons (w := 24) h7528 (SegSum.cons (w := 24) h7529 (SegSum.cons (w := 24) h7530 (SegSum.cons (w := 24) h7531 (SegSum.cons (w := 24) h7532 (SegSum.cons (w := 24) h7533 (SegSum.cons (w := 24) h7534 (show SegSum (P.leaf 34) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S4N1.C0.S49
