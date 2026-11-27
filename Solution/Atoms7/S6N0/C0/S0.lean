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

namespace RACert.S6N0.C0.S0

open RACert RACert.Problem

theorem cover0 : P.CoversSplit 26 10 0 0x9009000000009009000000000000000000000000000000009009000000009009dd0ddd0d0000dd0ddd0ddd0d0000dd0d0000000000000000dd0ddd0d0000dd0db0bb0000b0bbb0bb0000000000000000b0bb0000b0bbb0bbb0bb0000b0bbb0bb0000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [629, 636, 972, 979, 1315, 1322, 1658, 1665, 2008]) (by decide +kernel)

theorem c0_0 : P.sumLeaves 26 0 556 = 155008 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 0) (lo := 0) (len := 556) (W := 155008) check rows elimOK (by decide) (by decide) cover0 (by decide)
  decide +kernel

theorem c0_1 : P.sumLeaves 26 556 468 = 144704 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 0) (lo := 556) (len := 468) (W := 144704) check rows elimOK (by decide) (by decide) cover0 (by decide)
  decide +kernel

theorem h0 : P.leaf 36 0 = 299712 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(556, 155008), (468, 144704)]) (.cons c0_0 (.cons c0_1 (.nil))) (by decide) (by decide))

theorem cover1 : P.CoversSplit 26 10 1 0x8000000000000001000000000000000000000000000000008000000000000001800004000000000180000400000000010000000000000000800004000000000180000000002000010000000000000000800000000020000180000000002000010000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 530, 538, 629, 636, 873, 881, 1658, 1665, 2008]) (by decide +kernel)

theorem c1_0 : P.sumLeaves 26 1024 1024 = 68864 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1) (lo := 0) (len := 1024) (W := 68864) check rows elimOK (by decide) (by decide) cover1 (by decide)
  decide +kernel

theorem h1 : P.leaf 36 1 = 68864 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 68864)]) (.cons c1_0 (.nil)) (by decide) (by decide))

theorem cover3 : P.CoversSplit 26 10 3 0x8000000000000000000000000000000000000000000000000000000000000001800000000000000000000400000000000000000000000000000000000000000180000000000000000000000000000000000000000020000000000000000000010000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 530, 538, 579, 587, 629, 636, 873, 881, 2008]) (by decide +kernel)

theorem c3_0 : P.sumLeaves 26 3072 1024 = 18112 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3) (lo := 0) (len := 1024) (W := 18112) check rows elimOK (by decide) (by decide) cover3 (by decide)
  decide +kernel

theorem h3 : P.leaf 36 3 = 18112 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 18112)]) (.cons c3_0 (.nil)) (by decide) (by decide))

theorem cover7 : P.CoversSplit 26 10 7 0x8000000000000000000000000000000000000000000000000000000000000000840004000000000004000400000000000000000000000000000000000000000000000000000000000000000000000000000000000021000100000000000100010000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 538, 579, 587, 629, 636, 873, 881, 2008]) (by decide +kernel)

theorem c7_0 : P.sumLeaves 26 7168 1024 = 15168 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 7) (lo := 0) (len := 1024) (W := 15168) check rows elimOK (by decide) (by decide) cover7 (by decide)
  decide +kernel

theorem h7 : P.leaf 36 7 = 15168 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 15168)]) (.cons c7_0 (.nil)) (by decide) (by decide))

theorem cover15 : P.CoversSplit 26 10 15 0x8001000000000001000000000000000000000000000000000001000000000001040104010000000104010401000000010000000000000000000100010000000100210000002100010000000000000000002100000021000100010000000100010000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 538, 579, 587, 629, 636, 873, 881, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c15_0 : P.sumLeaves 26 15360 1024 = 38800 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 15) (lo := 0) (len := 1024) (W := 38800) check rows elimOK (by decide) (by decide) cover15 (by decide)
  decide +kernel

theorem h15 : P.leaf 36 15 = 38800 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 38800)]) (.cons c15_0 (.nil)) (by decide) (by decide))

theorem cover19 : P.CoversSplit 26 10 19 0x8000000000000000000000000000000000000000000000000000000000000001800000000000000000000400000000000000000000000000000000000000000180000000000000000000000000000000000000000020000000000000000000010000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 530, 538, 579, 587, 629, 636, 873, 881, 2008]) (by decide +kernel)

theorem c19_0 : P.sumLeaves 26 19456 1024 = 261344 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 19) (lo := 0) (len := 1024) (W := 261344) check rows elimOK (by decide) (by decide) cover19 (by decide)
  decide +kernel

theorem h19 : P.leaf 36 19 = 261344 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 261344)]) (.cons c19_0 (.nil)) (by decide) (by decide))

theorem cover20 : P.CoversSplit 26 10 20 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [866]) (by decide +kernel)

theorem c20_0 : P.sumLeaves 26 20480 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 20) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover20 (by decide)
  decide +kernel

theorem h20 : P.leaf 36 20 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c20_0 (.nil)) (by decide) (by decide))

theorem cover21 : P.CoversSplit 26 10 21 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [866]) (by decide +kernel)

theorem c21_0 : P.sumLeaves 26 21504 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 21) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover21 (by decide)
  decide +kernel

theorem h21 : P.leaf 36 21 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c21_0 (.nil)) (by decide) (by decide))

theorem cover23 : P.CoversSplit 26 10 23 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [866]) (by decide +kernel)

theorem c23_0 : P.sumLeaves 26 23552 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 23) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover23 (by decide)
  decide +kernel

theorem h23 : P.leaf 36 23 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c23_0 (.nil)) (by decide) (by decide))

theorem cover28 : P.CoversSplit 26 10 28 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [866]) (by decide +kernel)

theorem c28_0 : P.sumLeaves 26 28672 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 28) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover28 (by decide)
  decide +kernel

theorem h28 : P.leaf 36 28 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c28_0 (.nil)) (by decide) (by decide))

theorem cover29 : P.CoversSplit 26 10 29 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [866]) (by decide +kernel)

theorem c29_0 : P.sumLeaves 26 29696 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 29) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover29 (by decide)
  decide +kernel

theorem h29 : P.leaf 36 29 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c29_0 (.nil)) (by decide) (by decide))

theorem cover31 : P.CoversSplit 26 10 31 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [866]) (by decide +kernel)

theorem c31_0 : P.sumLeaves 26 31744 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 31) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover31 (by decide)
  decide +kernel

theorem h31 : P.leaf 36 31 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c31_0 (.nil)) (by decide) (by decide))

theorem cover54 : P.CoversSplit 26 10 54 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [866]) (by decide +kernel)

theorem c54_0 : P.sumLeaves 26 55296 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 54) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover54 (by decide)
  decide +kernel

theorem h54 : P.leaf 36 54 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c54_0 (.nil)) (by decide) (by decide))

theorem cover55 : P.CoversSplit 26 10 55 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [866]) (by decide +kernel)

theorem c55_0 : P.sumLeaves 26 56320 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 55) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover55 (by decide)
  decide +kernel

theorem h55 : P.leaf 36 55 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c55_0 (.nil)) (by decide) (by decide))

theorem cover58 : P.CoversSplit 26 10 58 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem c58_0 : P.sumLeaves 26 59392 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 58) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover58 (by decide)
  decide +kernel

theorem h58 : P.leaf 36 58 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c58_0 (.nil)) (by decide) (by decide))

theorem cover59 : P.CoversSplit 26 10 59 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem c59_0 : P.sumLeaves 26 60416 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 59) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover59 (by decide)
  decide +kernel

theorem h59 : P.leaf 36 59 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c59_0 (.nil)) (by decide) (by decide))

theorem cover62 : P.CoversSplit 26 10 62 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [866]) (by decide +kernel)

theorem c62_0 : P.sumLeaves 26 63488 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 62) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover62 (by decide)
  decide +kernel

theorem h62 : P.leaf 36 62 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c62_0 (.nil)) (by decide) (by decide))

theorem cover63 : P.CoversSplit 26 10 63 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [866]) (by decide +kernel)

theorem c63_0 : P.sumLeaves 26 64512 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 63) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover63 (by decide)
  decide +kernel

theorem h63 : P.leaf 36 63 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c63_0 (.nil)) (by decide) (by decide))

theorem cover126 : P.CoversSplit 26 10 126 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [866]) (by decide +kernel)

theorem c126_0 : P.sumLeaves 26 129024 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 126) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover126 (by decide)
  decide +kernel

theorem h126 : P.leaf 36 126 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c126_0 (.nil)) (by decide) (by decide))

theorem cover127 : P.CoversSplit 26 10 127 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [866]) (by decide +kernel)

theorem c127_0 : P.sumLeaves 26 130048 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 127) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover127 (by decide)
  decide +kernel

theorem h127 : P.leaf 36 127 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c127_0 (.nil)) (by decide) (by decide))

theorem cover183 : P.CoversSplit 26 10 183 0x8000000000000000000000000000000000000000000000000000000000000000cc00c80000000000c8008800000000000000000000000000000000000000000000000000000000000000000000000000000000000033003200000000003200220000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 538, 587, 629, 636, 873, 881, 922, 972, 1265, 1315, 1658, 2008]) (by decide +kernel)

theorem c183_0 : P.sumLeaves 26 187392 1024 = 2889796 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 183) (lo := 0) (len := 1024) (W := 2889796) check rows elimOK (by decide) (by decide) cover183 (by decide)
  decide +kernel

theorem h183 : P.leaf 36 183 = 2889796 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 2889796)]) (.cons c183_0 (.nil)) (by decide) (by decide))

theorem cover184 : P.CoversSplit 26 10 184 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem c184_0 : P.sumLeaves 26 188416 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 184) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover184 (by decide)
  decide +kernel

theorem h184 : P.leaf 36 184 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c184_0 (.nil)) (by decide) (by decide))

theorem cover185 : P.CoversSplit 26 10 185 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [866]) (by decide +kernel)

theorem c185_0 : P.sumLeaves 26 189440 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 185) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover185 (by decide)
  decide +kernel

theorem h185 : P.leaf 36 185 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c185_0 (.nil)) (by decide) (by decide))

theorem cover187 : P.CoversSplit 26 10 187 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [866]) (by decide +kernel)

theorem c187_0 : P.sumLeaves 26 191488 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 187) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover187 (by decide)
  decide +kernel

theorem h187 : P.leaf 36 187 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c187_0 (.nil)) (by decide) (by decide))

theorem cover191 : P.CoversSplit 26 10 191 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem c191_0 : P.sumLeaves 26 195584 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 191) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover191 (by decide)
  decide +kernel

theorem h191 : P.leaf 36 191 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c191_0 (.nil)) (by decide) (by decide))

theorem cover207 : P.CoversSplit 26 10 207 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [866]) (by decide +kernel)

theorem c207_0 : P.sumLeaves 26 211968 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 207) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover207 (by decide)
  decide +kernel

theorem h207 : P.leaf 36 207 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c207_0 (.nil)) (by decide) (by decide))

theorem cover220 : P.CoversSplit 26 10 220 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [866]) (by decide +kernel)

theorem c220_0 : P.sumLeaves 26 225280 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 220) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover220 (by decide)
  decide +kernel

theorem h220 : P.leaf 36 220 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c220_0 (.nil)) (by decide) (by decide))

theorem cover221 : P.CoversSplit 26 10 221 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem c221_0 : P.sumLeaves 26 226304 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 221) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover221 (by decide)
  decide +kernel

theorem h221 : P.leaf 36 221 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c221_0 (.nil)) (by decide) (by decide))

theorem cover223 : P.CoversSplit 26 10 223 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem c223_0 : P.sumLeaves 26 228352 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 223) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover223 (by decide)
  decide +kernel

theorem h223 : P.leaf 36 223 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c223_0 (.nil)) (by decide) (by decide))

theorem cover254 : P.CoversSplit 26 10 254 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [866]) (by decide +kernel)

theorem c254_0 : P.sumLeaves 26 260096 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 254) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover254 (by decide)
  decide +kernel

theorem h254 : P.leaf 36 254 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c254_0 (.nil)) (by decide) (by decide))

theorem cover255 : P.CoversSplit 26 10 255 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [867]) (by decide +kernel)

theorem c255_0 : P.sumLeaves 26 261120 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 255) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover255 (by decide)
  decide +kernel

theorem h255 : P.leaf 36 255 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c255_0 (.nil)) (by decide) (by decide))

theorem cover495 : P.CoversSplit 26 10 495 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [866]) (by decide +kernel)

theorem c495_0 : P.sumLeaves 26 506880 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 495) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover495 (by decide)
  decide +kernel

theorem h495 : P.leaf 36 495 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c495_0 (.nil)) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(0, 1), (1, 20), (3, 90), (7, 60), (15, 15), (19, 60), (20, 90), (21, 360), (23, 360), (28, 180), (29, 360), (31, 180), (54, 90), (55, 180), (58, 360), (59, 360), (62, 360), (63, 360), (126, 60), (127, 60), (183, 30), (184, 60), (185, 360), (187, 360), (191, 120), (207, 90), (220, 72), (221, 360), (223, 360), (254, 180), (255, 180), (495, 90)]

theorem segOK : checkSeg 20 perms 0 511 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 0 511 5868 107173672 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 107173672)
    (SegSum.cons (w := 1) h0 (SegSum.cons (w := 20) h1 (SegSum.cons (w := 90) h3 (SegSum.cons (w := 60) h7 (SegSum.cons (w := 15) h15 (SegSum.cons (w := 60) h19 (SegSum.cons (w := 90) h20 (SegSum.cons (w := 360) h21 (SegSum.cons (w := 360) h23 (SegSum.cons (w := 180) h28 (SegSum.cons (w := 360) h29 (SegSum.cons (w := 180) h31 (SegSum.cons (w := 90) h54 (SegSum.cons (w := 180) h55 (SegSum.cons (w := 360) h58 (SegSum.cons (w := 360) h59 (SegSum.cons (w := 360) h62 (SegSum.cons (w := 360) h63 (SegSum.cons (w := 60) h126 (SegSum.cons (w := 60) h127 (SegSum.cons (w := 30) h183 (SegSum.cons (w := 60) h184 (SegSum.cons (w := 360) h185 (SegSum.cons (w := 360) h187 (SegSum.cons (w := 120) h191 (SegSum.cons (w := 90) h207 (SegSum.cons (w := 72) h220 (SegSum.cons (w := 360) h221 (SegSum.cons (w := 360) h223 (SegSum.cons (w := 180) h254 (SegSum.cons (w := 180) h255 (SegSum.cons (w := 90) h495 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S0
