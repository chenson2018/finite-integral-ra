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

namespace RACert.S6N0.C0.S28

open RACert RACert.Problem

theorem cover14177 : P.CoversSplit 26 10 14177 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c14177_0 : P.sumLeaves 26 14517248 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14177) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14177 (by decide)
  decide +kernel

theorem h14177 : P.leaf 36 14177 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14177_0 (.nil)) (by decide) (by decide))

theorem cover14178 : P.CoversSplit 26 10 14178 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c14178_0 : P.sumLeaves 26 14518272 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14178) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14178 (by decide)
  decide +kernel

theorem h14178 : P.leaf 36 14178 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14178_0 (.nil)) (by decide) (by decide))

theorem cover14179 : P.CoversSplit 26 10 14179 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c14179_0 : P.sumLeaves 26 14519296 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14179) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14179 (by decide)
  decide +kernel

theorem h14179 : P.leaf 36 14179 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14179_0 (.nil)) (by decide) (by decide))

theorem cover14180 : P.CoversSplit 26 10 14180 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c14180_0 : P.sumLeaves 26 14520320 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14180) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14180 (by decide)
  decide +kernel

theorem h14180 : P.leaf 36 14180 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14180_0 (.nil)) (by decide) (by decide))

theorem cover14181 : P.CoversSplit 26 10 14181 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c14181_0 : P.sumLeaves 26 14521344 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14181) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14181 (by decide)
  decide +kernel

theorem h14181 : P.leaf 36 14181 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14181_0 (.nil)) (by decide) (by decide))

theorem cover14182 : P.CoversSplit 26 10 14182 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c14182_0 : P.sumLeaves 26 14522368 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14182) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14182 (by decide)
  decide +kernel

theorem h14182 : P.leaf 36 14182 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14182_0 (.nil)) (by decide) (by decide))

theorem cover14183 : P.CoversSplit 26 10 14183 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c14183_0 : P.sumLeaves 26 14523392 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14183) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14183 (by decide)
  decide +kernel

theorem h14183 : P.leaf 36 14183 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14183_0 (.nil)) (by decide) (by decide))

theorem cover14184 : P.CoversSplit 26 10 14184 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c14184_0 : P.sumLeaves 26 14524416 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14184) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14184 (by decide)
  decide +kernel

theorem h14184 : P.leaf 36 14184 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14184_0 (.nil)) (by decide) (by decide))

theorem cover14185 : P.CoversSplit 26 10 14185 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c14185_0 : P.sumLeaves 26 14525440 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14185) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14185 (by decide)
  decide +kernel

theorem h14185 : P.leaf 36 14185 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14185_0 (.nil)) (by decide) (by decide))

theorem cover14186 : P.CoversSplit 26 10 14186 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c14186_0 : P.sumLeaves 26 14526464 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14186) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14186 (by decide)
  decide +kernel

theorem h14186 : P.leaf 36 14186 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14186_0 (.nil)) (by decide) (by decide))

theorem cover14187 : P.CoversSplit 26 10 14187 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c14187_0 : P.sumLeaves 26 14527488 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14187) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14187 (by decide)
  decide +kernel

theorem h14187 : P.leaf 36 14187 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14187_0 (.nil)) (by decide) (by decide))

theorem cover14188 : P.CoversSplit 26 10 14188 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c14188_0 : P.sumLeaves 26 14528512 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14188) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14188 (by decide)
  decide +kernel

theorem h14188 : P.leaf 36 14188 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14188_0 (.nil)) (by decide) (by decide))

theorem cover14189 : P.CoversSplit 26 10 14189 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c14189_0 : P.sumLeaves 26 14529536 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14189) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14189 (by decide)
  decide +kernel

theorem h14189 : P.leaf 36 14189 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14189_0 (.nil)) (by decide) (by decide))

theorem cover14190 : P.CoversSplit 26 10 14190 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c14190_0 : P.sumLeaves 26 14530560 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14190) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14190 (by decide)
  decide +kernel

theorem h14190 : P.leaf 36 14190 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14190_0 (.nil)) (by decide) (by decide))

theorem cover14191 : P.CoversSplit 26 10 14191 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c14191_0 : P.sumLeaves 26 14531584 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14191) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14191 (by decide)
  decide +kernel

theorem h14191 : P.leaf 36 14191 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14191_0 (.nil)) (by decide) (by decide))

theorem h14192 : P.leaf 36 14192 = 3584 := by
  exact leaf_contract_factors (k := 36) (b := 12) (H := 14192) (ss := [(2, 1, 467), (7, 1, 474), (9, 1, 480), (12, 1, 825), (5, 1, 411), (4, 1, 410), (3, 1, 409), (6, 1, 412), (10, 1, 458), (11, 1, 459), (13, 1, 461), (20, 1, 572), (37, 17, 874), (17, 1, 880), (36, 1, 923), (28, 1, 579), (30, 1, 481), (34, 1, 579), (14, 1, 859), (32, 1, 873), (21, 1, 929), (31, 1, 930), (15, 1, 916), (35, 1, 930)]) (ids := [6, 14, 16, 22, 17, 20, 21, 23, 24, 25, 27, 31]) (cs := [1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 6, 1, 1, 7, 8, 5, 9, 10, 11, 1, 12, 1, 1, 1, 13, 1, 1, 1, 1]) (bs := [4, 8]) (W := 3584) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem h14193 : P.leaf 36 14193 = 132864 := by
  exact leaf_contract_factors (k := 36) (b := 23) (H := 14193) (ss := [(7, 1, 474), (2, 1, 475), (9, 1, 480), (12, 1, 825), (13, 1, 825), (17, 1, 874), (36, 1, 923), (28, 1, 579), (30, 1, 481), (34, 1, 579), (32, 1, 873), (21, 1, 929), (20, 1, 572)]) (ids := [1, 2, 3, 4, 6, 8, 9, 12, 13, 14, 16, 17, 20, 22, 25, 27, 29, 31, 33, 35, 21, 23, 24]) (cs := [1, 2, 3, 4, 5, 1, 6, 1, 7, 8, 1, 1, 9, 10, 11, 1, 12, 13, 1, 1, 14, 22, 15, 23, 24, 16, 1, 17, 1, 18, 1, 19, 1, 20, 1, 21]) (bs := [20, 3]) (W := 132864) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem cover14194 : P.CoversSplit 26 10 14194 0xa0000000a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 579, 873, 930, 972, 979, 1265, 1315, 1322]) (by decide +kernel)

theorem c14194_0 : P.sumLeaves 26 14534656 960 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14194) (lo := 0) (len := 960) (W := 0) check rows elimOK (by decide) (by decide) cover14194 (by decide)
  decide +kernel

theorem contract14194_1 : P.leaf 32 227119 = 180352 := by
  exact leaf_contract_factors (k := 32) (b := 19) (H := 227119) (ss := [(2, 1, 467), (28, 1, 481), (30, 1, 481), (32, 1, 873), (17, 1, 874), (14, 1, 859), (12, 1, 880), (5, 1, 411), (7, 1, 461), (13, 1, 461), (21, 1, 929), (31, 1, 930), (20, 1, 1609)]) (ids := [1, 2, 4, 6, 7, 8, 13, 14, 16, 17, 20, 23, 27, 31, 9, 21, 22, 24, 25]) (cs := [1, 2, 3, 1, 4, 1, 5, 6, 7, 16, 1, 1, 1, 8, 9, 1, 10, 11, 1, 1, 12, 17, 18, 13, 19, 20, 1, 14, 1, 1, 1, 15]) (bs := [14, 5]) (W := 180352) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c14194_1 : P.sumLeaves 26 14535616 64 = 180352 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 227119) rows (by decide) (by decide)).symm.trans contract14194_1

theorem h14194 : P.leaf 36 14194 = 180352 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(960, 0), (64, 180352)]) (.cons c14194_0 (.cons c14194_1 (.nil))) (by decide) (by decide))

theorem cover14195 : P.CoversSplit 26 10 14195 0xa0000000a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 579, 873, 930, 972, 979, 1315, 1322]) (by decide +kernel)

theorem c14195_0 : P.sumLeaves 26 14535680 1024 = 1159360 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14195) (lo := 0) (len := 1024) (W := 1159360) check rows elimOK (by decide) (by decide) cover14195 (by decide)
  decide +kernel

theorem h14195 : P.leaf 36 14195 = 1159360 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1159360)]) (.cons c14195_0 (.nil)) (by decide) (by decide))

theorem cover14196 : P.CoversSplit 26 10 14196 0xff000500ff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 579, 873, 880, 929, 930, 1265, 1315, 1658]) (by decide +kernel)

theorem c14196_0 : P.sumLeaves 26 14536704 1024 = 88080 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14196) (lo := 0) (len := 1024) (W := 88080) check rows elimOK (by decide) (by decide) cover14196 (by decide)
  decide +kernel

theorem h14196 : P.leaf 36 14196 = 88080 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 88080)]) (.cons c14196_0 (.nil)) (by decide) (by decide))

theorem cover14197 : P.CoversSplit 26 10 14197 0xff000500ff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 579, 929, 930, 972, 979, 1265, 1315, 1322, 1658]) (by decide +kernel)

theorem c14197_0 : P.sumLeaves 26 14537728 1024 = 1175776 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14197) (lo := 0) (len := 1024) (W := 1175776) check rows elimOK (by decide) (by decide) cover14197 (by decide)
  decide +kernel

theorem h14197 : P.leaf 36 14197 = 1175776 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1175776)]) (.cons c14197_0 (.nil)) (by decide) (by decide))

theorem cover14198 : P.CoversSplit 26 10 14198 0xff000500ff000000000000000000000000000000000000000000000000000000550000005500000005000000050000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 579, 873, 880, 930, 972, 1265, 1315, 1658]) (by decide +kernel)

theorem c14198_0 : P.sumLeaves 26 14538752 640 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14198) (lo := 0) (len := 640) (W := 0) check rows elimOK (by decide) (by decide) cover14198 (by decide)
  decide +kernel

theorem contract14198_1 : P.leaf 32 227178 = 34016 := by
  exact leaf_contract_factors (k := 32) (b := 18) (H := 227178) (ss := [(2, 1, 482), (20, 1, 523), (17, 1, 874), (13, 1, 923), (12, 1, 825), (7, 1, 461), (31, 1, 930), (28, 0, 1265), (30, 0, 1265), (26, 1, 481), (32, 1, 579), (14, 1, 873), (16, 0, 1265), (18, 1, 1315)]) (ids := [1, 2, 3, 4, 6, 7, 8, 9, 13, 17, 19, 20, 21, 23, 27, 31, 22, 25]) (cs := [1, 2, 3, 4, 5, 1, 6, 7, 8, 9, 1, 1, 1, 10, 0, 1, 1, 11, 1, 12, 13, 14, 18, 15, 1, 19, 0, 16, 0, 1, 1, 17]) (bs := [16, 2]) (W := 34016) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c14198_1 : P.sumLeaves 26 14539392 64 = 34016 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 227178) rows (by decide) (by decide)).symm.trans contract14198_1

theorem c14198_2 : P.sumLeaves 26 14539456 320 = 2483296 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14198) (lo := 704) (len := 320) (W := 2483296) check rows elimOK (by decide) (by decide) cover14198 (by decide)
  decide +kernel

theorem h14198 : P.leaf 36 14198 = 2517312 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(640, 0), (64, 34016), (320, 2483296)]) (.cons c14198_0 (.cons c14198_1 (.cons c14198_2 (.nil)))) (by decide) (by decide))

theorem cover14199 : P.CoversSplit 26 10 14199 0xff000500ff000000000000000000000000000000000000000000000000000000550000005500000005000000050000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 579, 930, 972, 979, 1265, 1315, 1322, 1658]) (by decide +kernel)

theorem c14199_0 : P.sumLeaves 26 14539776 640 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14199) (lo := 0) (len := 640) (W := 0) check rows elimOK (by decide) (by decide) cover14199 (by decide)
  decide +kernel

theorem contract14199_1 : P.leaf 32 227194 = 140832 := by
  exact leaf_contract_factors (k := 32) (b := 20) (H := 227194) (ss := [(2, 1, 482), (20, 1, 580), (17, 1, 874), (13, 1, 923), (12, 1, 825), (31, 1, 930), (28, 0, 1265), (30, 0, 1265), (32, 1, 579), (14, 1, 873), (16, 0, 1265), (18, 1, 1315)]) (ids := [1, 2, 3, 4, 5, 7, 8, 9, 13, 17, 19, 20, 21, 23, 27, 31, 6, 24, 22, 25]) (cs := [1, 2, 3, 4, 5, 6, 18, 7, 8, 9, 1, 1, 1, 10, 0, 1, 1, 11, 1, 12, 13, 14, 20, 15, 19, 21, 0, 16, 0, 1, 1, 17]) (bs := [16, 2, 2]) (W := 140832) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c14199_1 : P.sumLeaves 26 14540416 64 = 140832 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 227194) rows (by decide) (by decide)).symm.trans contract14199_1

theorem c14199_2 : P.sumLeaves 26 14540480 320 = 9372096 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14199) (lo := 704) (len := 320) (W := 9372096) check rows elimOK (by decide) (by decide) cover14199 (by decide)
  decide +kernel

theorem h14199 : P.leaf 36 14199 = 9512928 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(640, 0), (64, 140832), (320, 9372096)]) (.cons c14199_0 (.cons c14199_1 (.cons c14199_2 (.nil)))) (by decide) (by decide))

theorem h14200 : P.leaf 36 14200 = 95336 := by
  exact leaf_contract_factors (k := 36) (b := 21) (H := 14200) (ss := [(2, 1, 467), (7, 1, 474), (9, 1, 480), (12, 1, 825), (13, 1, 825), (11, 1, 459), (37, 1, 874), (15, 1, 916), (21, 1, 916), (20, 1, 572), (36, 1, 923), (28, 1, 481), (30, 1, 481), (34, 1, 579), (32, 1, 873)]) (ids := [1, 2, 3, 4, 6, 8, 12, 14, 15, 16, 17, 20, 22, 25, 27, 29, 31, 33, 21, 23, 24]) (cs := [1, 2, 3, 4, 5, 1, 6, 1, 7, 1, 1, 1, 8, 1, 9, 10, 11, 12, 1, 1, 13, 20, 14, 21, 22, 15, 1, 16, 1, 17, 1, 18, 1, 19, 1, 1]) (bs := [18, 3]) (W := 95336) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem cover14201 : P.CoversSplit 26 10 14201 0xa0a00000a0a000000000000000000000a0a00000a080000000000000000000000000000000000000000000000000000000000000000000000000000000000000a0a00000808000000000000000000000a00000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 579, 873, 930, 972, 979, 1265, 1273, 1315, 1322]) (by decide +kernel)

theorem c14201_0 : P.sumLeaves 26 14541824 448 = 58112 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14201) (lo := 0) (len := 448) (W := 58112) check rows elimOK (by decide) (by decide) cover14201 (by decide)
  decide +kernel

theorem contract14201_1 : P.leaf 32 227223 = 178944 := by
  exact leaf_contract_factors (k := 32) (b := 20) (H := 227223) (ss := [(7, 1, 474), (9, 1, 480), (28, 1, 481), (30, 1, 481), (2, 1, 482), (4, 1, 580), (12, 1, 825), (13, 1, 825), (32, 1, 873), (15, 1, 916), (21, 1, 916), (20, 1, 572)]) (ids := [1, 3, 4, 6, 9, 12, 14, 15, 16, 17, 20, 22, 25, 27, 29, 31, 8, 21, 23, 24]) (cs := [1, 2, 1, 3, 4, 1, 5, 1, 18, 6, 1, 1, 7, 1, 8, 9, 10, 11, 1, 1, 12, 19, 13, 20, 21, 14, 1, 15, 1, 16, 1, 17]) (bs := [16, 4]) (W := 178944) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c14201_1 : P.sumLeaves 26 14542272 64 = 178944 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 227223) rows (by decide) (by decide)).symm.trans contract14201_1

theorem c14201_2 : P.sumLeaves 26 14542336 320 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14201) (lo := 512) (len := 320) (W := 0) check rows elimOK (by decide) (by decide) cover14201 (by decide)
  decide +kernel

theorem contract14201_3 : P.leaf 32 227229 = 201888 := by
  exact leaf_contract_factors (k := 32) (b := 20) (H := 227229) (ss := [(7, 1, 474), (2, 1, 475), (9, 1, 480), (28, 1, 481), (30, 1, 481), (5, 1, 586), (12, 1, 460), (20, 1, 572), (13, 1, 825), (32, 1, 873), (15, 1, 916), (21, 1, 916)]) (ids := [1, 2, 4, 6, 8, 9, 12, 14, 15, 16, 17, 20, 22, 25, 27, 29, 31, 21, 23, 24]) (cs := [1, 2, 3, 1, 4, 1, 5, 1, 6, 7, 1, 1, 8, 1, 9, 10, 11, 12, 1, 1, 13, 19, 14, 20, 21, 15, 1, 16, 1, 17, 1, 18]) (bs := [17, 3]) (W := 201888) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c14201_3 : P.sumLeaves 26 14542656 64 = 201888 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 227229) rows (by decide) (by decide)).symm.trans contract14201_3

theorem c14201_4 : P.sumLeaves 26 14542720 128 = 599584 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14201) (lo := 896) (len := 128) (W := 599584) check rows elimOK (by decide) (by decide) cover14201 (by decide)
  decide +kernel

theorem h14201 : P.leaf 36 14201 = 1038528 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(448, 58112), (64, 178944), (320, 0), (64, 201888), (128, 599584)]) (.cons c14201_0 (.cons c14201_1 (.cons c14201_2 (.cons c14201_3 (.cons c14201_4 (.nil)))))) (by decide) (by decide))

theorem cover14202 : P.CoversSplit 26 10 14202 0xa0a00000a0a000000000000000000000a0a00000a08000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 579, 873, 874, 972, 979, 1273, 1315]) (by decide +kernel)

theorem c14202_0 : P.sumLeaves 26 14542848 1024 = 1276752 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14202) (lo := 0) (len := 1024) (W := 1276752) check rows elimOK (by decide) (by decide) cover14202 (by decide)
  decide +kernel

theorem h14202 : P.leaf 36 14202 = 1276752 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1276752)]) (.cons c14202_0 (.nil)) (by decide) (by decide))

theorem cover14203 : P.CoversSplit 26 10 14203 0xa0a00000a0a000000000000000000000a0a00000a080000000000000000000000000000000000000000000000000000000000000000000000000000000000000a0a00000808000000000000000000000a00000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 579, 873, 930, 972, 979, 1273, 1315, 1322]) (by decide +kernel)

theorem c14203_0 : P.sumLeaves 26 14543872 1024 = 9157124 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14203) (lo := 0) (len := 1024) (W := 9157124) check rows elimOK (by decide) (by decide) cover14203 (by decide)
  decide +kernel

theorem h14203 : P.leaf 36 14203 = 9157124 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 9157124)]) (.cons c14203_0 (.nil)) (by decide) (by decide))

theorem cover14204 : P.CoversSplit 26 10 14204 0xffff0500ffff00000000000000000000fffc0500ffcc00000500050005000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [579, 873, 874, 929, 972, 979, 1265, 1273, 1315, 1658, 1665]) (by decide +kernel)

theorem c14204_0 : P.sumLeaves 26 14544896 1024 = 2438060 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14204) (lo := 0) (len := 1024) (W := 2438060) check rows elimOK (by decide) (by decide) cover14204 (by decide)
  decide +kernel

theorem h14204 : P.leaf 36 14204 = 2438060 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 2438060)]) (.cons c14204_0 (.nil)) (by decide) (by decide))

theorem cover14205 : P.CoversSplit 26 10 14205 0xffff0500ffff00000000000000000000fffc0500ffcc000005000500050000000000000000000000000000000000000000000000000000000000000000000000ffff0500cccc00000000000000000000ff000500cc00000005000500040000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [579, 929, 930, 972, 979, 1265, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c14205_0 : P.sumLeaves 26 14545920 1002 = 7616956 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14205) (lo := 0) (len := 1002) (W := 7616956) check rows elimOK (by decide) (by decide) cover14205 (by decide)
  decide +kernel

theorem c14205_1 : P.sumLeaves 26 14546922 22 = 3868080 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14205) (lo := 1002) (len := 22) (W := 3868080) check rows elimOK (by decide) (by decide) cover14205 (by decide)
  decide +kernel

theorem h14205 : P.leaf 36 14205 = 11485036 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1002, 7616956), (22, 3868080)]) (.cons c14205_0 (.cons c14205_1 (.nil))) (by decide) (by decide))

theorem cover14206 : P.CoversSplit 26 10 14206 0xffff0500ffff00000000000000000000fffc0500ffcc00000500050005000000555500005555000005050000050500000000000000000000050000000500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [579, 873, 874, 972, 979, 1265, 1273, 1315, 1658, 1665]) (ps := [(21, [867], [1658])]) (by decide +kernel)

theorem c14206_0 : P.sumLeaves 26 14546944 512 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14206) (lo := 0) (len := 512) (W := 0) check rows elimOK (by decide) (by decide) cover14206 (by decide)
  decide +kernel

theorem contract14206_1 : P.leaf 32 227304 = 16260 := by
  exact leaf_contract_factors (k := 32) (b := 18) (H := 227304) (ss := [(20, 1, 523), (5, 1, 586), (21, 1, 867), (13, 1, 923), (28, 0, 1265), (30, 0, 1265), (26, 1, 481), (32, 1, 579), (14, 1, 873), (16, 0, 1265), (8, 1, 1210), (17, 1, 859), (18, 1, 1315), (31, 1, 1665)]) (ids := [0, 1, 2, 4, 5, 7, 8, 9, 10, 13, 17, 20, 21, 23, 25, 27, 31, 22]) (cs := [2, 3, 4, 1, 5, 6, 1, 7, 8, 9, 10, 1, 1, 11, 0, 1, 1, 12, 1, 1, 13, 14, 19, 15, 1, 16, 0, 17, 0, 1, 1, 18]) (bs := [17, 1]) (W := 16260) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c14206_1 : P.sumLeaves 26 14547456 64 = 16260 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 227304) rows (by decide) (by decide)).symm.trans contract14206_1

theorem c14206_2 : P.sumLeaves 26 14547520 448 = 13599476 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14206) (lo := 576) (len := 448) (W := 13599476) check rows elimOK (by decide) (by decide) cover14206 (by decide)
  decide +kernel

theorem h14206 : P.leaf 36 14206 = 13615736 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(512, 0), (64, 16260), (448, 13599476)]) (.cons c14206_0 (.cons c14206_1 (.cons c14206_2 (.nil)))) (by decide) (by decide))

theorem cover14207 : P.CoversSplit 26 10 14207 0xffff0500ffff00000000000000000000fffc0500ffcc000005000500050000005555000055550000050500000505000055540000554400000500000005000000ffff0500cccc00000000000000000000ff000500cc00000005000500040000005555000044440000050500000404000055000000440000000500000004000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [579, 930, 972, 979, 1265, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c14207_0 : P.sumLeaves 26 14547968 64 = 4728 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14207) (lo := 0) (len := 64) (W := 4728) check rows elimOK (by decide) (by decide) cover14207 (by decide)
  decide +kernel

theorem contract14207_1 : P.leaf 32 227313 = 23920 := by
  exact leaf_contract_factors (k := 32) (b := 19) (H := 227313) (ss := [(22, 1, 433), (2, 1, 482), (3, 1, 537), (4, 1, 580), (5, 1, 586), (7, 1, 825), (13, 1, 923), (8, 1, 1217), (21, 0, 1658), (9, 0, 1609), (28, 0, 1658), (31, 1, 1665), (6, 1, 587)]) (ids := [8, 9, 10, 12, 13, 14, 15, 16, 17, 18, 21, 23, 24, 25, 27, 28, 30, 31, 22]) (cs := [1, 1, 1, 1, 1, 1, 1, 0, 2, 3, 4, 1, 5, 6, 7, 8, 9, 10, 11, 0, 1, 12, 20, 13, 14, 15, 0, 16, 17, 1, 18, 19]) (bs := [18, 1]) (W := 23920) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c14207_1 : P.sumLeaves 26 14548032 64 = 23920 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 227313) rows (by decide) (by decide)).symm.trans contract14207_1

theorem contract14207_2 : P.leaf 32 227314 = 9752 := by
  exact leaf_contract_factors (k := 32) (b := 18) (H := 227314) (ss := [(22, 1, 433), (2, 1, 482), (3, 1, 537), (4, 1, 580), (7, 1, 825), (13, 1, 923), (8, 1, 1217), (28, 0, 1265), (30, 0, 1265), (32, 1, 579), (5, 1, 629), (14, 1, 873), (16, 0, 1265), (18, 1, 1315)]) (ids := [4, 7, 8, 9, 10, 13, 15, 17, 18, 19, 21, 23, 25, 27, 29, 31, 22, 24]) (cs := [1, 1, 1, 1, 2, 1, 1, 3, 4, 5, 6, 1, 1, 7, 0, 8, 1, 9, 10, 11, 1, 12, 18, 13, 19, 14, 0, 15, 0, 16, 1, 17]) (bs := [16, 2]) (W := 9752) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c14207_2 : P.sumLeaves 26 14548096 64 = 9752 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 227314) rows (by decide) (by decide)).symm.trans contract14207_2

theorem c14207_3 : P.sumLeaves 26 14548160 572 = 21259091 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14207) (lo := 192) (len := 572) (W := 21259091) check rows elimOK (by decide) (by decide) cover14207 (by decide)
  decide +kernel

theorem c14207_4 : P.sumLeaves 26 14548732 260 = 47034297 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14207) (lo := 764) (len := 260) (W := 47034297) check rows elimOK (by decide) (by decide) cover14207 (by decide)
  decide +kernel

theorem h14207 : P.leaf 36 14207 = 68331788 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(64, 4728), (64, 23920), (64, 9752), (572, 21259091), (260, 47034297)]) (.cons c14207_0 (.cons c14207_1 (.cons c14207_2 (.cons c14207_3 (.cons c14207_4 (.nil)))))) (by decide) (by decide))

theorem cover14304 : P.CoversSplit 26 10 14304 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c14304_0 : P.sumLeaves 26 14647296 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14304) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14304 (by decide)
  decide +kernel

theorem h14304 : P.leaf 36 14304 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14304_0 (.nil)) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(14177, 720), (14178, 720), (14179, 720), (14180, 720), (14181, 720), (14182, 720), (14183, 720), (14184, 720), (14185, 720), (14186, 720), (14187, 720), (14188, 720), (14189, 720), (14190, 720), (14191, 720), (14192, 720), (14193, 720), (14194, 720), (14195, 720), (14196, 720), (14197, 720), (14198, 720), (14199, 720), (14200, 720), (14201, 720), (14202, 720), (14203, 720), (14204, 720), (14205, 720), (14206, 720), (14207, 720), (14304, 360)]

theorem segOK : checkSeg 20 perms 14177 14305 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 14177 14305 22680 87990203520 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 87990203520)
    (SegSum.cons (w := 720) h14177 (SegSum.cons (w := 720) h14178 (SegSum.cons (w := 720) h14179 (SegSum.cons (w := 720) h14180 (SegSum.cons (w := 720) h14181 (SegSum.cons (w := 720) h14182 (SegSum.cons (w := 720) h14183 (SegSum.cons (w := 720) h14184 (SegSum.cons (w := 720) h14185 (SegSum.cons (w := 720) h14186 (SegSum.cons (w := 720) h14187 (SegSum.cons (w := 720) h14188 (SegSum.cons (w := 720) h14189 (SegSum.cons (w := 720) h14190 (SegSum.cons (w := 720) h14191 (SegSum.cons (w := 720) h14192 (SegSum.cons (w := 720) h14193 (SegSum.cons (w := 720) h14194 (SegSum.cons (w := 720) h14195 (SegSum.cons (w := 720) h14196 (SegSum.cons (w := 720) h14197 (SegSum.cons (w := 720) h14198 (SegSum.cons (w := 720) h14199 (SegSum.cons (w := 720) h14200 (SegSum.cons (w := 720) h14201 (SegSum.cons (w := 720) h14202 (SegSum.cons (w := 720) h14203 (SegSum.cons (w := 720) h14204 (SegSum.cons (w := 720) h14205 (SegSum.cons (w := 720) h14206 (SegSum.cons (w := 720) h14207 (SegSum.cons (w := 360) h14304 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S28
