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

namespace RACert.S6N0.C0.S29

open RACert RACert.Problem

theorem cover14193 : P.CoversSplit 26 10 14193 0xa0000000a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 579, 873, 930, 972, 979, 1265, 1315, 1322, 1665]) (by decide +kernel)

theorem c14193_0 : P.sumLeaves 26 14533632 1024 = 132864 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14193) (lo := 0) (len := 1024) (W := 132864) check rows elimOK (by decide) (by decide) cover14193 (by decide)
  decide +kernel

theorem h14193 : P.leaf 36 14193 = 132864 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 132864)]) (.cons c14193_0 (.nil)) (by decide) (by decide))

theorem cover14194 : P.CoversSplit 26 10 14194 0xa0000000a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 579, 873, 930, 972, 979, 1265, 1315, 1322]) (by decide +kernel)

theorem c14194_0 : P.sumLeaves 26 14534656 1024 = 180352 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14194) (lo := 0) (len := 1024) (W := 180352) check rows elimOK (by decide) (by decide) cover14194 (by decide)
  decide +kernel

theorem h14194 : P.leaf 36 14194 = 180352 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 180352)]) (.cons c14194_0 (.nil)) (by decide) (by decide))

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

theorem c14198_0 : P.sumLeaves 26 14538752 1024 = 2517312 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14198) (lo := 0) (len := 1024) (W := 2517312) check rows elimOK (by decide) (by decide) cover14198 (by decide)
  decide +kernel

theorem h14198 : P.leaf 36 14198 = 2517312 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 2517312)]) (.cons c14198_0 (.nil)) (by decide) (by decide))

theorem cover14199 : P.CoversSplit 26 10 14199 0xff000500ff000000000000000000000000000000000000000000000000000000550000005500000005000000050000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 579, 930, 972, 979, 1265, 1315, 1322, 1658]) (by decide +kernel)

theorem c14199_0 : P.sumLeaves 26 14539776 1024 = 9512928 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14199) (lo := 0) (len := 1024) (W := 9512928) check rows elimOK (by decide) (by decide) cover14199 (by decide)
  decide +kernel

theorem h14199 : P.leaf 36 14199 = 9512928 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 9512928)]) (.cons c14199_0 (.nil)) (by decide) (by decide))

theorem cover14200 : P.CoversSplit 26 10 14200 0xa0a00000a0a000000000000000000000a0a00000a08000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 579, 873, 874, 972, 979, 1265, 1273, 1315]) (by decide +kernel)

theorem c14200_0 : P.sumLeaves 26 14540800 1024 = 95336 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14200) (lo := 0) (len := 1024) (W := 95336) check rows elimOK (by decide) (by decide) cover14200 (by decide)
  decide +kernel

theorem h14200 : P.leaf 36 14200 = 95336 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 95336)]) (.cons c14200_0 (.nil)) (by decide) (by decide))

theorem cover14201 : P.CoversSplit 26 10 14201 0xa0a00000a0a000000000000000000000a0a00000a080000000000000000000000000000000000000000000000000000000000000000000000000000000000000a0a00000808000000000000000000000a00000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 579, 873, 930, 972, 979, 1265, 1273, 1315, 1322]) (by decide +kernel)

theorem c14201_0 : P.sumLeaves 26 14541824 1024 = 1038528 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14201) (lo := 0) (len := 1024) (W := 1038528) check rows elimOK (by decide) (by decide) cover14201 (by decide)
  decide +kernel

theorem h14201 : P.leaf 36 14201 = 1038528 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1038528)]) (.cons c14201_0 (.nil)) (by decide) (by decide))

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

theorem cover14206 : P.CoversSplit 26 10 14206 0xffff0500ffff00000000000000000000fffc0500ffcc00000500050005000000555500005555000005050000050500005554000055440000050000000500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [579, 873, 874, 972, 979, 1265, 1273, 1315, 1658, 1665]) (by decide +kernel)

theorem c14206_0 : P.sumLeaves 26 14546944 1011 = 8006116 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14206) (lo := 0) (len := 1011) (W := 8006116) check rows elimOK (by decide) (by decide) cover14206 (by decide)
  decide +kernel

theorem c14206_1 : P.sumLeaves 26 14547955 13 = 5609620 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14206) (lo := 1011) (len := 13) (W := 5609620) check rows elimOK (by decide) (by decide) cover14206 (by decide)
  decide +kernel

theorem h14206 : P.leaf 36 14206 = 13615736 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1011, 8006116), (13, 5609620)]) (.cons c14206_0 (.cons c14206_1 (.nil))) (by decide) (by decide))

theorem cover14207 : P.CoversSplit 26 10 14207 0xffff0500ffff00000000000000000000fffc0500ffcc000005000500050000005555000055550000050500000505000055540000554400000500000005000000ffff0500cccc00000000000000000000ff000500cc00000005000500040000005555000044440000050500000404000055000000440000000500000004000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [579, 930, 972, 979, 1265, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c14207_0 : P.sumLeaves 26 14547968 698 = 18640175 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14207) (lo := 0) (len := 698) (W := 18640175) check rows elimOK (by decide) (by decide) cover14207 (by decide)
  decide +kernel

theorem c14207_1 : P.sumLeaves 26 14548666 326 = 49691613 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14207) (lo := 698) (len := 326) (W := 49691613) check rows elimOK (by decide) (by decide) cover14207 (by decide)
  decide +kernel

theorem h14207 : P.leaf 36 14207 = 68331788 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(698, 18640175), (326, 49691613)]) (.cons c14207_0 (.cons c14207_1 (.nil))) (by decide) (by decide))

theorem cover14304 : P.CoversSplit 26 10 14304 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c14304_0 : P.sumLeaves 26 14647296 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14304) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14304 (by decide)
  decide +kernel

theorem h14304 : P.leaf 36 14304 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14304_0 (.nil)) (by decide) (by decide))

theorem cover14305 : P.CoversSplit 26 10 14305 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c14305_0 : P.sumLeaves 26 14648320 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14305) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14305 (by decide)
  decide +kernel

theorem h14305 : P.leaf 36 14305 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14305_0 (.nil)) (by decide) (by decide))

theorem cover14307 : P.CoversSplit 26 10 14307 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c14307_0 : P.sumLeaves 26 14650368 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14307) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14307 (by decide)
  decide +kernel

theorem h14307 : P.leaf 36 14307 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14307_0 (.nil)) (by decide) (by decide))

theorem cover14308 : P.CoversSplit 26 10 14308 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c14308_0 : P.sumLeaves 26 14651392 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14308) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14308 (by decide)
  decide +kernel

theorem h14308 : P.leaf 36 14308 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14308_0 (.nil)) (by decide) (by decide))

theorem cover14309 : P.CoversSplit 26 10 14309 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c14309_0 : P.sumLeaves 26 14652416 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14309) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14309 (by decide)
  decide +kernel

theorem h14309 : P.leaf 36 14309 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14309_0 (.nil)) (by decide) (by decide))

theorem cover14310 : P.CoversSplit 26 10 14310 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c14310_0 : P.sumLeaves 26 14653440 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14310) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14310 (by decide)
  decide +kernel

theorem h14310 : P.leaf 36 14310 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14310_0 (.nil)) (by decide) (by decide))

theorem cover14311 : P.CoversSplit 26 10 14311 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c14311_0 : P.sumLeaves 26 14654464 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14311) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14311 (by decide)
  decide +kernel

theorem h14311 : P.leaf 36 14311 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14311_0 (.nil)) (by decide) (by decide))

theorem cover14316 : P.CoversSplit 26 10 14316 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c14316_0 : P.sumLeaves 26 14659584 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14316) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14316 (by decide)
  decide +kernel

theorem h14316 : P.leaf 36 14316 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14316_0 (.nil)) (by decide) (by decide))

theorem cover14317 : P.CoversSplit 26 10 14317 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c14317_0 : P.sumLeaves 26 14660608 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14317) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14317 (by decide)
  decide +kernel

theorem h14317 : P.leaf 36 14317 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14317_0 (.nil)) (by decide) (by decide))

theorem cover14319 : P.CoversSplit 26 10 14319 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c14319_0 : P.sumLeaves 26 14662656 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14319) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover14319 (by decide)
  decide +kernel

theorem h14319 : P.leaf 36 14319 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c14319_0 (.nil)) (by decide) (by decide))

theorem cover14320 : P.CoversSplit 26 10 14320 0xf0000000f0000000f0000000f00000000000000000000000000000000000000000000000000000000000aa0000008800000000000000000000000000000000000000000000000000000000000000000000000000c0c0000000000000808000000000000000000000000000000000000000000000000000000000000000008888 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 873, 930, 972, 979, 1322, 1658]) (by decide +kernel)

theorem c14320_0 : P.sumLeaves 26 14663680 1024 = 50176 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14320) (lo := 0) (len := 1024) (W := 50176) check rows elimOK (by decide) (by decide) cover14320 (by decide)
  decide +kernel

theorem h14320 : P.leaf 36 14320 = 50176 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 50176)]) (.cons c14320_0 (.nil)) (by decide) (by decide))

theorem cover14321 : P.CoversSplit 26 10 14321 0xf0000000f0000000f0000000f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c0c0000000000000808000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 873, 930, 972, 979, 1322, 1658]) (by decide +kernel)

theorem c14321_0 : P.sumLeaves 26 14664704 1024 = 1536784 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14321) (lo := 0) (len := 1024) (W := 1536784) check rows elimOK (by decide) (by decide) cover14321 (by decide)
  decide +kernel

theorem h14321 : P.leaf 36 14321 = 1536784 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1536784)]) (.cons c14321_0 (.nil)) (by decide) (by decide))

theorem cover14323 : P.CoversSplit 26 10 14323 0xf0000000f0000000f0000000f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 873, 930, 972, 979, 1322, 1658]) (by decide +kernel)

theorem c14323_0 : P.sumLeaves 26 14666752 1024 = 6860096 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14323) (lo := 0) (len := 1024) (W := 6860096) check rows elimOK (by decide) (by decide) cover14323 (by decide)
  decide +kernel

theorem h14323 : P.leaf 36 14323 = 6860096 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 6860096)]) (.cons c14323_0 (.nil)) (by decide) (by decide))

theorem cover14324 : P.CoversSplit 26 10 14324 0xff00ff00ff00c800ff00fa00ff00c80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 873, 880, 929, 930, 1265, 1315, 1322]) (by decide +kernel)

theorem c14324_0 : P.sumLeaves 26 14667776 1024 = 1087824 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14324) (lo := 0) (len := 1024) (W := 1087824) check rows elimOK (by decide) (by decide) cover14324 (by decide)
  decide +kernel

theorem h14324 : P.leaf 36 14324 = 1087824 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1087824)]) (.cons c14324_0 (.nil)) (by decide) (by decide))

theorem cover14325 : P.CoversSplit 26 10 14325 0xff00ff00ff00c800ff00fa00ff00c80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 873, 929, 930, 972, 979, 1265, 1315, 1322]) (by decide +kernel)

theorem c14325_0 : P.sumLeaves 26 14668800 1024 = 7812712 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14325) (lo := 0) (len := 1024) (W := 7812712) check rows elimOK (by decide) (by decide) cover14325 (by decide)
  decide +kernel

theorem h14325 : P.leaf 36 14325 = 7812712 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 7812712)]) (.cons c14325_0 (.nil)) (by decide) (by decide))

theorem cover14326 : P.CoversSplit 26 10 14326 0xff00ff00ff00c800ff00fa00ff00c80000000000000000000000000000000000ff00f000ff00c000aa00a000aa0080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 873, 880, 930, 972, 1265, 1315, 1322, 1658]) (by decide +kernel)

theorem c14326_0 : P.sumLeaves 26 14669824 1024 = 13142184 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14326) (lo := 0) (len := 1024) (W := 13142184) check rows elimOK (by decide) (by decide) cover14326 (by decide)
  decide +kernel

theorem h14326 : P.leaf 36 14326 = 13142184 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 13142184)]) (.cons c14326_0 (.nil)) (by decide) (by decide))

theorem cover14327 : P.CoversSplit 26 10 14327 0xff00ff00ff00c800ff00fa00ff00c80000000000000000000000000000000000ff00f000ff00c000aa00a000aa0080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 873, 930, 972, 979, 1265, 1315, 1322, 1658]) (by decide +kernel)

theorem c14327_0 : P.sumLeaves 26 14670848 1024 = 61616798 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 14327) (lo := 0) (len := 1024) (W := 61616798) check rows elimOK (by decide) (by decide) cover14327 (by decide)
  decide +kernel

theorem h14327 : P.leaf 36 14327 = 61616798 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 61616798)]) (.cons c14327_0 (.nil)) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(14193, 720), (14194, 720), (14195, 720), (14196, 720), (14197, 720), (14198, 720), (14199, 720), (14200, 720), (14201, 720), (14202, 720), (14203, 720), (14204, 720), (14205, 720), (14206, 720), (14207, 720), (14304, 360), (14305, 720), (14307, 360), (14308, 720), (14309, 720), (14310, 720), (14311, 720), (14316, 360), (14317, 720), (14319, 360), (14320, 360), (14321, 720), (14323, 360), (14324, 720), (14325, 720), (14326, 720), (14327, 720)]

theorem segOK : checkSeg 20 perms 14193 14332 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 14193 14332 20880 151816658400 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 151816658400)
    (SegSum.cons (w := 720) h14193 (SegSum.cons (w := 720) h14194 (SegSum.cons (w := 720) h14195 (SegSum.cons (w := 720) h14196 (SegSum.cons (w := 720) h14197 (SegSum.cons (w := 720) h14198 (SegSum.cons (w := 720) h14199 (SegSum.cons (w := 720) h14200 (SegSum.cons (w := 720) h14201 (SegSum.cons (w := 720) h14202 (SegSum.cons (w := 720) h14203 (SegSum.cons (w := 720) h14204 (SegSum.cons (w := 720) h14205 (SegSum.cons (w := 720) h14206 (SegSum.cons (w := 720) h14207 (SegSum.cons (w := 360) h14304 (SegSum.cons (w := 720) h14305 (SegSum.cons (w := 360) h14307 (SegSum.cons (w := 720) h14308 (SegSum.cons (w := 720) h14309 (SegSum.cons (w := 720) h14310 (SegSum.cons (w := 720) h14311 (SegSum.cons (w := 360) h14316 (SegSum.cons (w := 720) h14317 (SegSum.cons (w := 360) h14319 (SegSum.cons (w := 360) h14320 (SegSum.cons (w := 720) h14321 (SegSum.cons (w := 360) h14323 (SegSum.cons (w := 720) h14324 (SegSum.cons (w := 720) h14325 (SegSum.cons (w := 720) h14326 (SegSum.cons (w := 720) h14327 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S29
