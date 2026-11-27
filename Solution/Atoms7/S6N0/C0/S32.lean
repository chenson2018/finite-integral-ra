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

namespace RACert.S6N0.C0.S32

open RACert RACert.Problem

theorem cover16176 : P.CoversSplit 26 10 16176 0x8000800000000000000000000000000000000000000000000000000000000000000040000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 579, 930, 972, 979, 1273, 1315, 1658, 1665]) (by decide +kernel)

theorem c16176_0 : P.sumLeaves 26 16564224 1024 = 1792 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16176) (lo := 0) (len := 1024) (W := 1792) check rows elimOK (by decide) (by decide) cover16176 (by decide)
  decide +kernel

theorem h16176 : P.leaf 36 16176 = 1792 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1792)]) (.cons c16176_0 (.nil)) (by decide) (by decide))

theorem cover16177 : P.CoversSplit 26 10 16177 0x8000800000000000000000000000000000000000000000000000000000000000000040000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 538, 579, 930, 972, 979, 1273, 1315, 1658, 1665]) (by decide +kernel)

theorem c16177_0 : P.sumLeaves 26 16565248 1024 = 98624 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16177) (lo := 0) (len := 1024) (W := 98624) check rows elimOK (by decide) (by decide) cover16177 (by decide)
  decide +kernel

theorem h16177 : P.leaf 36 16177 = 98624 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 98624)]) (.cons c16177_0 (.nil)) (by decide) (by decide))

theorem cover16178 : P.CoversSplit 26 10 16178 0x8000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 538, 579, 930, 972, 979, 1273, 1315, 1658, 1665]) (by decide +kernel)

theorem c16178_0 : P.sumLeaves 26 16566272 1024 = 132428 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16178) (lo := 0) (len := 1024) (W := 132428) check rows elimOK (by decide) (by decide) cover16178 (by decide)
  decide +kernel

theorem h16178 : P.leaf 36 16178 = 132428 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 132428)]) (.cons c16178_0 (.nil)) (by decide) (by decide))

theorem cover16179 : P.CoversSplit 26 10 16179 0x8000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 538, 579, 930, 972, 979, 1315, 1658, 1665]) (by decide +kernel)

theorem c16179_0 : P.sumLeaves 26 16567296 1024 = 929536 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16179) (lo := 0) (len := 1024) (W := 929536) check rows elimOK (by decide) (by decide) cover16179 (by decide)
  decide +kernel

theorem h16179 : P.leaf 36 16179 = 929536 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 929536)]) (.cons c16179_0 (.nil)) (by decide) (by decide))

theorem cover16182 : P.CoversSplit 26 10 16182 0xcc00cc0000000000000000000000000000000000000000000000000000000000440040000000000044004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 538, 579, 930, 972, 979, 1265, 1273, 1658, 1665]) (by decide +kernel)

theorem c16182_0 : P.sumLeaves 26 16570368 1024 = 1886080 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16182) (lo := 0) (len := 1024) (W := 1886080) check rows elimOK (by decide) (by decide) cover16182 (by decide)
  decide +kernel

theorem h16182 : P.leaf 36 16182 = 1886080 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1886080)]) (.cons c16182_0 (.nil)) (by decide) (by decide))

theorem cover16183 : P.CoversSplit 26 10 16183 0xcc00cc0000000000000000000000000000000000000000000000000000000000440040000000000044004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 538, 579, 930, 972, 979, 1265, 1658, 1665]) (by decide +kernel)

theorem c16183_0 : P.sumLeaves 26 16571392 1024 = 8822848 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16183) (lo := 0) (len := 1024) (W := 8822848) check rows elimOK (by decide) (by decide) cover16183 (by decide)
  decide +kernel

theorem h16183 : P.leaf 36 16183 = 8822848 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 8822848)]) (.cons c16183_0 (.nil)) (by decide) (by decide))

theorem cover16184 : P.CoversSplit 26 10 16184 0xa0a0a0a000000020000000000000000000200020000000200000000000000000000050500000001000005050000000100000001000000010000000000000000000200020002000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 579, 874, 930, 972, 1273, 1322, 1665]) (by decide +kernel)

theorem c16184_0 : P.sumLeaves 26 16572416 1024 = 45330 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16184) (lo := 0) (len := 1024) (W := 45330) check rows elimOK (by decide) (by decide) cover16184 (by decide)
  decide +kernel

theorem h16184 : P.leaf 36 16184 = 45330 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 45330)]) (.cons c16184_0 (.nil)) (by decide) (by decide))

theorem cover16185 : P.CoversSplit 26 10 16185 0xa0a0a0a000000020000000000000000000200020000000200000000000000000000050500000001000005050000000100000001000000010000000000000000000200020002000200000000000000000000000000000000000000000000000000000001000000010000000100000001000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 579, 930, 972, 1273, 1322, 1665]) (by decide +kernel)

theorem c16185_0 : P.sumLeaves 26 16573440 1024 = 1166520 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16185) (lo := 0) (len := 1024) (W := 1166520) check rows elimOK (by decide) (by decide) cover16185 (by decide)
  decide +kernel

theorem h16185 : P.leaf 36 16185 = 1166520 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1166520)]) (.cons c16185_0 (.nil)) (by decide) (by decide))

theorem cover16186 : P.CoversSplit 26 10 16186 0xa0a0a0a000000020000000000000000000200020000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000200020002000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 579, 874, 972, 979, 1273, 1315, 1322, 1665]) (by decide +kernel)

theorem c16186_0 : P.sumLeaves 26 16574464 1024 = 2329284 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16186) (lo := 0) (len := 1024) (W := 2329284) check rows elimOK (by decide) (by decide) cover16186 (by decide)
  decide +kernel

theorem h16186 : P.leaf 36 16186 = 2329284 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 2329284)]) (.cons c16186_0 (.nil)) (by decide) (by decide))

theorem cover16187 : P.CoversSplit 26 10 16187 0xa0a0a0a000000020000000000000000000200020000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000200020002000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 579, 972, 979, 1273, 1315, 1322, 1665]) (by decide +kernel)

theorem c16187_0 : P.sumLeaves 26 16575488 1024 = 8269264 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16187) (lo := 0) (len := 1024) (W := 8269264) check rows elimOK (by decide) (by decide) cover16187 (by decide)
  decide +kernel

theorem h16187 : P.leaf 36 16187 = 8269264 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 8269264)]) (.cons c16187_0 (.nil)) (by decide) (by decide))

theorem cover16190 : P.CoversSplit 26 10 16190 0xfffffffa00000030000000000000000000330032000000300000000000000000555550500000001055555050000000100011001000000010000000000000000000330032003300300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [538, 579, 874, 972, 979, 1265, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c16190_0 : P.sumLeaves 26 16578560 1024 = 14821432 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16190) (lo := 0) (len := 1024) (W := 14821432) check rows elimOK (by decide) (by decide) cover16190 (by decide)
  decide +kernel

theorem h16190 : P.leaf 36 16190 = 14821432 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 14821432)]) (.cons c16190_0 (.nil)) (by decide) (by decide))

theorem cover16191 : P.CoversSplit 26 10 16191 0xfffffffa00000030000000000000000000330032000000300000000000000000555550500000001055555050000000100011001000000010000000000000000000330032003300300000000000000000000000000000000000000000000000000011001000110010001100100011001000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [538, 579, 972, 979, 1265, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c16191_0 : P.sumLeaves 26 16579584 1024 = 49348876 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16191) (lo := 0) (len := 1024) (W := 49348876) check rows elimOK (by decide) (by decide) cover16191 (by decide)
  decide +kernel

theorem h16191 : P.leaf 36 16191 = 49348876 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 49348876)]) (.cons c16191_0 (.nil)) (by decide) (by decide))

theorem cover16208 : P.CoversSplit 26 10 16208 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c16208_0 : P.sumLeaves 26 16596992 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16208) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover16208 (by decide)
  decide +kernel

theorem h16208 : P.leaf 36 16208 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c16208_0 (.nil)) (by decide) (by decide))

theorem cover16209 : P.CoversSplit 26 10 16209 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c16209_0 : P.sumLeaves 26 16598016 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16209) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover16209 (by decide)
  decide +kernel

theorem h16209 : P.leaf 36 16209 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c16209_0 (.nil)) (by decide) (by decide))

theorem cover16210 : P.CoversSplit 26 10 16210 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c16210_0 : P.sumLeaves 26 16599040 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16210) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover16210 (by decide)
  decide +kernel

theorem h16210 : P.leaf 36 16210 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c16210_0 (.nil)) (by decide) (by decide))

theorem cover16211 : P.CoversSplit 26 10 16211 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c16211_0 : P.sumLeaves 26 16600064 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16211) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover16211 (by decide)
  decide +kernel

theorem h16211 : P.leaf 36 16211 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c16211_0 (.nil)) (by decide) (by decide))

theorem cover16212 : P.CoversSplit 26 10 16212 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c16212_0 : P.sumLeaves 26 16601088 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16212) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover16212 (by decide)
  decide +kernel

theorem h16212 : P.leaf 36 16212 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c16212_0 (.nil)) (by decide) (by decide))

theorem cover16213 : P.CoversSplit 26 10 16213 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c16213_0 : P.sumLeaves 26 16602112 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16213) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover16213 (by decide)
  decide +kernel

theorem h16213 : P.leaf 36 16213 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c16213_0 (.nil)) (by decide) (by decide))

theorem cover16214 : P.CoversSplit 26 10 16214 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c16214_0 : P.sumLeaves 26 16603136 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16214) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover16214 (by decide)
  decide +kernel

theorem h16214 : P.leaf 36 16214 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c16214_0 (.nil)) (by decide) (by decide))

theorem cover16215 : P.CoversSplit 26 10 16215 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c16215_0 : P.sumLeaves 26 16604160 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16215) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover16215 (by decide)
  decide +kernel

theorem h16215 : P.leaf 36 16215 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c16215_0 (.nil)) (by decide) (by decide))

theorem cover16216 : P.CoversSplit 26 10 16216 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c16216_0 : P.sumLeaves 26 16605184 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16216) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover16216 (by decide)
  decide +kernel

theorem h16216 : P.leaf 36 16216 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c16216_0 (.nil)) (by decide) (by decide))

theorem cover16217 : P.CoversSplit 26 10 16217 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c16217_0 : P.sumLeaves 26 16606208 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16217) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover16217 (by decide)
  decide +kernel

theorem h16217 : P.leaf 36 16217 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c16217_0 (.nil)) (by decide) (by decide))

theorem cover16218 : P.CoversSplit 26 10 16218 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c16218_0 : P.sumLeaves 26 16607232 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16218) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover16218 (by decide)
  decide +kernel

theorem h16218 : P.leaf 36 16218 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c16218_0 (.nil)) (by decide) (by decide))

theorem cover16219 : P.CoversSplit 26 10 16219 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c16219_0 : P.sumLeaves 26 16608256 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16219) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover16219 (by decide)
  decide +kernel

theorem h16219 : P.leaf 36 16219 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c16219_0 (.nil)) (by decide) (by decide))

theorem cover16220 : P.CoversSplit 26 10 16220 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c16220_0 : P.sumLeaves 26 16609280 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16220) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover16220 (by decide)
  decide +kernel

theorem h16220 : P.leaf 36 16220 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c16220_0 (.nil)) (by decide) (by decide))

theorem cover16221 : P.CoversSplit 26 10 16221 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c16221_0 : P.sumLeaves 26 16610304 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16221) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover16221 (by decide)
  decide +kernel

theorem h16221 : P.leaf 36 16221 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c16221_0 (.nil)) (by decide) (by decide))

theorem cover16222 : P.CoversSplit 26 10 16222 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c16222_0 : P.sumLeaves 26 16611328 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16222) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover16222 (by decide)
  decide +kernel

theorem h16222 : P.leaf 36 16222 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c16222_0 (.nil)) (by decide) (by decide))

theorem cover16223 : P.CoversSplit 26 10 16223 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1272]) (by decide +kernel)

theorem c16223_0 : P.sumLeaves 26 16612352 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16223) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover16223 (by decide)
  decide +kernel

theorem h16223 : P.leaf 36 16223 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c16223_0 (.nil)) (by decide) (by decide))

theorem cover16240 : P.CoversSplit 26 10 16240 0xa000a000a000a00000000000000000000000000000000000000000000000000000005000000050000000500000005000000000000000000000000000000000000000000000000000000000000000000000000000a000a00000000000000000000000000000000000000000000000000000000000000050000000000000005000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 579, 930, 972, 979, 1658, 1665]) (by decide +kernel)

theorem c16240_0 : P.sumLeaves 26 16629760 1024 = 17730 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16240) (lo := 0) (len := 1024) (W := 17730) check rows elimOK (by decide) (by decide) cover16240 (by decide)
  decide +kernel

theorem h16240 : P.leaf 36 16240 = 17730 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 17730)]) (.cons c16240_0 (.nil)) (by decide) (by decide))

theorem cover16241 : P.CoversSplit 26 10 16241 0xa000a000a000a00000000000000000000000000000000000000000000000000000005000000050000000500000005000000000000000000000000000000000000000000000000000000000000000000000000000a000a00000000000000000000000000000000000000000000000000000000000000050000000000000005000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 579, 930, 972, 979, 1658, 1665]) (by decide +kernel)

theorem c16241_0 : P.sumLeaves 26 16630784 1024 = 617528 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16241) (lo := 0) (len := 1024) (W := 617528) check rows elimOK (by decide) (by decide) cover16241 (by decide)
  decide +kernel

theorem h16241 : P.leaf 36 16241 = 617528 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 617528)]) (.cons c16241_0 (.nil)) (by decide) (by decide))

theorem cover16242 : P.CoversSplit 26 10 16242 0xa000a000a000a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002000200000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 579, 930, 972, 979, 1315, 1658]) (by decide +kernel)

theorem c16242_0 : P.sumLeaves 26 16631808 1024 = 1188592 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16242) (lo := 0) (len := 1024) (W := 1188592) check rows elimOK (by decide) (by decide) cover16242 (by decide)
  decide +kernel

theorem h16242 : P.leaf 36 16242 = 1188592 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1188592)]) (.cons c16242_0 (.nil)) (by decide) (by decide))

theorem cover16243 : P.CoversSplit 26 10 16243 0xa000a000a000a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002000200000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 579, 930, 972, 979, 1315, 1658]) (by decide +kernel)

theorem c16243_0 : P.sumLeaves 26 16632832 1024 = 4949352 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 16243) (lo := 0) (len := 1024) (W := 4949352) check rows elimOK (by decide) (by decide) cover16243 (by decide)
  decide +kernel

theorem h16243 : P.leaf 36 16243 = 4949352 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 4949352)]) (.cons c16243_0 (.nil)) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(16176, 360), (16177, 360), (16178, 720), (16179, 720), (16182, 360), (16183, 360), (16184, 360), (16185, 360), (16186, 720), (16187, 720), (16190, 360), (16191, 360), (16208, 720), (16209, 720), (16210, 720), (16211, 720), (16212, 720), (16213, 720), (16214, 720), (16215, 720), (16216, 720), (16217, 720), (16218, 720), (16219, 720), (16220, 720), (16221, 720), (16222, 720), (16223, 720), (16240, 360), (16241, 360), (16242, 720), (16243, 720)]

theorem segOK : checkSeg 20 perms 16176 16246 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 16176 16246 19440 40472521920 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 40472521920)
    (SegSum.cons (w := 360) h16176 (SegSum.cons (w := 360) h16177 (SegSum.cons (w := 720) h16178 (SegSum.cons (w := 720) h16179 (SegSum.cons (w := 360) h16182 (SegSum.cons (w := 360) h16183 (SegSum.cons (w := 360) h16184 (SegSum.cons (w := 360) h16185 (SegSum.cons (w := 720) h16186 (SegSum.cons (w := 720) h16187 (SegSum.cons (w := 360) h16190 (SegSum.cons (w := 360) h16191 (SegSum.cons (w := 720) h16208 (SegSum.cons (w := 720) h16209 (SegSum.cons (w := 720) h16210 (SegSum.cons (w := 720) h16211 (SegSum.cons (w := 720) h16212 (SegSum.cons (w := 720) h16213 (SegSum.cons (w := 720) h16214 (SegSum.cons (w := 720) h16215 (SegSum.cons (w := 720) h16216 (SegSum.cons (w := 720) h16217 (SegSum.cons (w := 720) h16218 (SegSum.cons (w := 720) h16219 (SegSum.cons (w := 720) h16220 (SegSum.cons (w := 720) h16221 (SegSum.cons (w := 720) h16222 (SegSum.cons (w := 720) h16223 (SegSum.cons (w := 360) h16240 (SegSum.cons (w := 360) h16241 (SegSum.cons (w := 720) h16242 (SegSum.cons (w := 720) h16243 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S32
