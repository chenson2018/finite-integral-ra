/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Atoms7.S6N0.C0.Defs

/-! Generated certificate for the identity on six symmetric diversity atoms. -/

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option Elab.async false

@[expose] public section

namespace RACert.S6N0.C0.S28

open RACert RACert.Problem

theorem cover14113 : P.CoversSplit 26 10 14113 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c14113_0 : P.sumLeaves 26 14451712 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14113) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14113 (by decide)
  decide +kernel

theorem h14113 : P.leaf 36 14113 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14113_0 (.nil)) (by decide) (by decide))

theorem cover14115 : P.CoversSplit 26 10 14115 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c14115_0 : P.sumLeaves 26 14453760 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14115) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14115 (by decide)
  decide +kernel

theorem h14115 : P.leaf 36 14115 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14115_0 (.nil)) (by decide) (by decide))

theorem cover14117 : P.CoversSplit 26 10 14117 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c14117_0 : P.sumLeaves 26 14455808 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14117) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14117 (by decide)
  decide +kernel

theorem h14117 : P.leaf 36 14117 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14117_0 (.nil)) (by decide) (by decide))

theorem cover14119 : P.CoversSplit 26 10 14119 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c14119_0 : P.sumLeaves 26 14457856 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14119) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14119 (by decide)
  decide +kernel

theorem h14119 : P.leaf 36 14119 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14119_0 (.nil)) (by decide) (by decide))

theorem cover14127 : P.CoversSplit 26 10 14127 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c14127_0 : P.sumLeaves 26 14466048 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14127) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14127 (by decide)
  decide +kernel

theorem h14127 : P.leaf 36 14127 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14127_0 (.nil)) (by decide) (by decide))

theorem cover14128 : P.CoversSplit 26 10 14128 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [538, 579, 873, 930, 972, 979, 1265, 1273, 1315, 1665]) (by decide +kernel)

theorem c14128_0 : P.sumLeaves 26 14467072 1024 = 256 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14128) (lo := 0) (len := 1024) (W := 256) check rows elimOK (by decide) (by decide) cover14128 (by decide)
  decide +kernel

theorem h14128 : P.leaf 36 14128 = 256 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 256)]) (.cons c14128_0 (.nil)) (by decide) (by decide))

theorem cover14129 : P.CoversSplit 26 10 14129 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 538, 579, 873, 930, 972, 979, 1265, 1273, 1315, 1665]) (by decide +kernel)

theorem c14129_0 : P.sumLeaves 26 14468096 1024 = 16576 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14129) (lo := 0) (len := 1024) (W := 16576) check rows elimOK (by decide) (by decide) cover14129 (by decide)
  decide +kernel

theorem h14129 : P.leaf 36 14129 = 16576 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 16576)]) (.cons c14129_0 (.nil)) (by decide) (by decide))

theorem cover14131 : P.CoversSplit 26 10 14131 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 538, 579, 873, 930, 972, 979, 1315, 1665]) (by decide +kernel)

theorem c14131_0 : P.sumLeaves 26 14470144 1024 = 191744 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14131) (lo := 0) (len := 1024) (W := 191744) check rows elimOK (by decide) (by decide) cover14131 (by decide)
  decide +kernel

theorem h14131 : P.leaf 36 14131 = 191744 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 191744)]) (.cons c14131_0 (.nil)) (by decide) (by decide))

theorem cover14132 : P.CoversSplit 26 10 14132 0xcc00040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 538, 579, 873, 929, 930, 972, 979, 1265, 1273, 1658, 1665]) (by decide +kernel)

theorem c14132_0 : P.sumLeaves 26 14471168 1024 = 8608 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14132) (lo := 0) (len := 1024) (W := 8608) check rows elimOK (by decide) (by decide) cover14132 (by decide)
  decide +kernel

theorem h14132 : P.leaf 36 14132 = 8608 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 8608)]) (.cons c14132_0 (.nil)) (by decide) (by decide))

theorem cover14133 : P.CoversSplit 26 10 14133 0xcc00040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 538, 579, 929, 930, 972, 979, 1265, 1658, 1665]) (by decide +kernel)

theorem c14133_0 : P.sumLeaves 26 14472192 1024 = 221312 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14133) (lo := 0) (len := 1024) (W := 221312) check rows elimOK (by decide) (by decide) cover14133 (by decide)
  decide +kernel

theorem h14133 : P.leaf 36 14133 = 221312 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 221312)]) (.cons c14133_0 (.nil)) (by decide) (by decide))

theorem cover14134 : P.CoversSplit 26 10 14134 0xcc00040000000000000000000000000000000000000000000000000000000000440000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 538, 579, 873, 930, 972, 979, 1265, 1273, 1658, 1665]) (by decide +kernel)

theorem c14134_0 : P.sumLeaves 26 14473216 1024 = 219200 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14134) (lo := 0) (len := 1024) (W := 219200) check rows elimOK (by decide) (by decide) cover14134 (by decide)
  decide +kernel

theorem h14134 : P.leaf 36 14134 = 219200 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 219200)]) (.cons c14134_0 (.nil)) (by decide) (by decide))

theorem cover14135 : P.CoversSplit 26 10 14135 0xcc00040000000000000000000000000000000000000000000000000000000000440000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 538, 579, 930, 972, 979, 1265, 1658, 1665]) (by decide +kernel)

theorem c14135_0 : P.sumLeaves 26 14474240 1024 = 1619328 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14135) (lo := 0) (len := 1024) (W := 1619328) check rows elimOK (by decide) (by decide) cover14135 (by decide)
  decide +kernel

theorem h14135 : P.leaf 36 14135 = 1619328 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1619328)]) (.cons c14135_0 (.nil)) (by decide) (by decide))

theorem cover14140 : P.CoversSplit 26 10 14140 0xffff050000000000000000000000000000300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [538, 579, 873, 874, 929, 972, 979, 1265, 1273, 1322, 1658]) (by decide +kernel)

theorem c14140_0 : P.sumLeaves 26 14479360 1024 = 337616 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14140) (lo := 0) (len := 1024) (W := 337616) check rows elimOK (by decide) (by decide) cover14140 (by decide)
  decide +kernel

theorem h14140 : P.leaf 36 14140 = 337616 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 337616)]) (.cons c14140_0 (.nil)) (by decide) (by decide))

theorem cover14141 : P.CoversSplit 26 10 14141 0xffff050000000000000000000000000000300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000033330100003300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [538, 579, 929, 930, 972, 979, 1265, 1273, 1322, 1658]) (by decide +kernel)

theorem c14141_0 : P.sumLeaves 26 14480384 1024 = 1625248 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14141) (lo := 0) (len := 1024) (W := 1625248) check rows elimOK (by decide) (by decide) cover14141 (by decide)
  decide +kernel

theorem h14141 : P.leaf 36 14141 = 1625248 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1625248)]) (.cons c14141_0 (.nil)) (by decide) (by decide))

theorem cover14143 : P.CoversSplit 26 10 14143 0xffff050000000000000000000000000000300000000000000000000000000000555500000000000005050000000000000010000000000000000000000000000033330100003300000000000000000000000000000000000000000000000000001111000000110000010100000001000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [538, 579, 972, 979, 1265, 1273, 1322, 1658]) (by decide +kernel)

theorem c14143_0 : P.sumLeaves 26 14482432 1024 = 8069388 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14143) (lo := 0) (len := 1024) (W := 8069388) check rows elimOK (by decide) (by decide) cover14143 (by decide)
  decide +kernel

theorem h14143 : P.leaf 36 14143 = 8069388 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 8069388)]) (.cons c14143_0 (.nil)) (by decide) (by decide))

theorem cover14176 : P.CoversSplit 26 10 14176 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c14176_0 : P.sumLeaves 26 14516224 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14176) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14176 (by decide)
  decide +kernel

theorem h14176 : P.leaf 36 14176 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14176_0 (.nil)) (by decide) (by decide))

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

theorem cover14192 : P.CoversSplit 26 10 14192 0xa0000000a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 579, 873, 930, 972, 979, 1265, 1315, 1322, 1665]) (by decide +kernel)

theorem c14192_0 : P.sumLeaves 26 14532608 1024 = 3584 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14192) (lo := 0) (len := 1024) (W := 3584) check rows elimOK (by decide) (by decide) cover14192 (by decide)
  decide +kernel

theorem h14192 : P.leaf 36 14192 = 3584 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 3584)]) (.cons c14192_0 (.nil)) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(14113, 720), (14115, 360), (14117, 720), (14119, 720), (14127, 180), (14128, 360), (14129, 720), (14131, 360), (14132, 720), (14133, 720), (14134, 720), (14135, 720), (14140, 360), (14141, 720), (14143, 360), (14176, 720), (14177, 720), (14178, 720), (14179, 720), (14180, 720), (14181, 720), (14182, 720), (14183, 720), (14184, 720), (14185, 720), (14186, 720), (14187, 720), (14188, 720), (14189, 720), (14190, 720), (14191, 720), (14192, 720)]

theorem segOK : checkSeg 20 perms 14113 14193 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 14113 14193 20700 5769617760 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 5769617760)
    (SegSum.cons (w := 720) h14113 (SegSum.cons (w := 360) h14115 (SegSum.cons (w := 720) h14117 (SegSum.cons (w := 720) h14119 (SegSum.cons (w := 180) h14127 (SegSum.cons (w := 360) h14128 (SegSum.cons (w := 720) h14129 (SegSum.cons (w := 360) h14131 (SegSum.cons (w := 720) h14132 (SegSum.cons (w := 720) h14133 (SegSum.cons (w := 720) h14134 (SegSum.cons (w := 720) h14135 (SegSum.cons (w := 360) h14140 (SegSum.cons (w := 720) h14141 (SegSum.cons (w := 360) h14143 (SegSum.cons (w := 720) h14176 (SegSum.cons (w := 720) h14177 (SegSum.cons (w := 720) h14178 (SegSum.cons (w := 720) h14179 (SegSum.cons (w := 720) h14180 (SegSum.cons (w := 720) h14181 (SegSum.cons (w := 720) h14182 (SegSum.cons (w := 720) h14183 (SegSum.cons (w := 720) h14184 (SegSum.cons (w := 720) h14185 (SegSum.cons (w := 720) h14186 (SegSum.cons (w := 720) h14187 (SegSum.cons (w := 720) h14188 (SegSum.cons (w := 720) h14189 (SegSum.cons (w := 720) h14190 (SegSum.cons (w := 720) h14191 (SegSum.cons (w := 720) h14192 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S28
