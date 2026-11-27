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

namespace RACert.S6N0.C0.S45

open RACert RACert.Problem

theorem cover78190 : P.CoversSplit 26 10 78190 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 579, 580, 629, 636, 873, 879, 972, 979, 1315, 1322, 1658]) (by decide +kernel)

theorem c78190_0 : P.sumLeaves 26 80066560 1024 = 14008 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78190) (lo := 0) (len := 1024) (W := 14008) check rows elimOK (by decide) (by decide) cover78190 (by decide)
  decide +kernel

theorem h78190 : P.leaf 36 78190 = 14008 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 14008)]) (.cons c78190_0 (.nil)) (by decide) (by decide))

theorem cover78191 : P.CoversSplit 26 10 78191 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 579, 580, 629, 636, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c78191_0 : P.sumLeaves 26 80067584 1024 = 117242 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78191) (lo := 0) (len := 1024) (W := 117242) check rows elimOK (by decide) (by decide) cover78191 (by decide)
  decide +kernel

theorem h78191 : P.leaf 36 78191 = 117242 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 117242)]) (.cons c78191_0 (.nil)) (by decide) (by decide))

theorem cover78206 : P.CoversSplit 26 10 78206 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 579, 580, 629, 636, 867, 873, 972, 979, 1315, 1322, 1658]) (by decide +kernel)

theorem c78206_0 : P.sumLeaves 26 80082944 1024 = 134384 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78206) (lo := 0) (len := 1024) (W := 134384) check rows elimOK (by decide) (by decide) cover78206 (by decide)
  decide +kernel

theorem h78206 : P.leaf 36 78206 = 134384 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 134384)]) (.cons c78206_0 (.nil)) (by decide) (by decide))

theorem cover78207 : P.CoversSplit 26 10 78207 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 579, 580, 629, 636, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c78207_0 : P.sumLeaves 26 80083968 1024 = 1760787 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78207) (lo := 0) (len := 1024) (W := 1760787) check rows elimOK (by decide) (by decide) cover78207 (by decide)
  decide +kernel

theorem h78207 : P.leaf 36 78207 = 1760787 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1760787)]) (.cons c78207_0 (.nil)) (by decide) (by decide))

theorem cover78245 : P.CoversSplit 26 10 78245 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000200000000001000010000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 482, 489, 538, 629, 636, 930, 972, 979, 1315, 1658]) (by decide +kernel)

theorem c78245_0 : P.sumLeaves 26 80122880 1024 = 5020 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78245) (lo := 0) (len := 1024) (W := 5020) check rows elimOK (by decide) (by decide) cover78245 (by decide)
  decide +kernel

theorem h78245 : P.leaf 36 78245 = 5020 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 5020)]) (.cons c78245_0 (.nil)) (by decide) (by decide))

theorem cover78246 : P.CoversSplit 26 10 78246 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000200000000001000010000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 482, 489, 538, 629, 636, 930, 972, 1315, 1658]) (by decide +kernel)

theorem c78246_0 : P.sumLeaves 26 80123904 1024 = 5252 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78246) (lo := 0) (len := 1024) (W := 5252) check rows elimOK (by decide) (by decide) cover78246 (by decide)
  decide +kernel

theorem h78246 : P.leaf 36 78246 = 5252 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 5252)]) (.cons c78246_0 (.nil)) (by decide) (by decide))

theorem cover78247 : P.CoversSplit 26 10 78247 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000200000000001000010000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 482, 489, 538, 629, 636, 930, 972, 1315, 1658]) (by decide +kernel)

theorem c78247_0 : P.sumLeaves 26 80124928 1024 = 32924 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78247) (lo := 0) (len := 1024) (W := 32924) check rows elimOK (by decide) (by decide) cover78247 (by decide)
  decide +kernel

theorem h78247 : P.leaf 36 78247 = 32924 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 32924)]) (.cons c78247_0 (.nil)) (by decide) (by decide))

theorem cover78249 : P.CoversSplit 26 10 78249 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 481, 482, 531, 629, 636, 972, 979, 1273, 1315, 1658]) (by decide +kernel)

theorem c78249_0 : P.sumLeaves 26 80126976 1024 = 5120 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78249) (lo := 0) (len := 1024) (W := 5120) check rows elimOK (by decide) (by decide) cover78249 (by decide)
  decide +kernel

theorem h78249 : P.leaf 36 78249 = 5120 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 5120)]) (.cons c78249_0 (.nil)) (by decide) (by decide))

theorem cover78251 : P.CoversSplit 26 10 78251 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 481, 482, 531, 629, 636, 972, 979, 1273, 1315, 1658]) (by decide +kernel)

theorem c78251_0 : P.sumLeaves 26 80129024 1024 = 14368 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78251) (lo := 0) (len := 1024) (W := 14368) check rows elimOK (by decide) (by decide) cover78251 (by decide)
  decide +kernel

theorem h78251 : P.leaf 36 78251 = 14368 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 14368)]) (.cons c78251_0 (.nil)) (by decide) (by decide))

theorem cover78253 : P.CoversSplit 26 10 78253 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 531, 538, 629, 636, 874, 972, 979, 1273, 1315, 1658]) (by decide +kernel)

theorem c78253_0 : P.sumLeaves 26 80131072 1024 = 10240 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78253) (lo := 0) (len := 1024) (W := 10240) check rows elimOK (by decide) (by decide) cover78253 (by decide)
  decide +kernel

theorem h78253 : P.leaf 36 78253 = 10240 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 10240)]) (.cons c78253_0 (.nil)) (by decide) (by decide))

theorem cover78254 : P.CoversSplit 26 10 78254 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 531, 538, 629, 636, 874, 972, 979, 1273, 1315, 1658]) (by decide +kernel)

theorem c78254_0 : P.sumLeaves 26 80132096 1024 = 13952 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78254) (lo := 0) (len := 1024) (W := 13952) check rows elimOK (by decide) (by decide) cover78254 (by decide)
  decide +kernel

theorem h78254 : P.leaf 36 78254 = 13952 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 13952)]) (.cons c78254_0 (.nil)) (by decide) (by decide))

theorem cover78255 : P.CoversSplit 26 10 78255 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 531, 538, 629, 636, 874, 972, 979, 1273, 1315, 1658]) (by decide +kernel)

theorem c78255_0 : P.sumLeaves 26 80133120 1024 = 69488 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78255) (lo := 0) (len := 1024) (W := 69488) check rows elimOK (by decide) (by decide) cover78255 (by decide)
  decide +kernel

theorem h78255 : P.leaf 36 78255 = 69488 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 69488)]) (.cons c78255_0 (.nil)) (by decide) (by decide))

theorem cover78262 : P.CoversSplit 26 10 78262 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000200000000001000010000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 482, 489, 538, 629, 636, 930, 972, 1315, 1658]) (by decide +kernel)

theorem c78262_0 : P.sumLeaves 26 80140288 1024 = 19391 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78262) (lo := 0) (len := 1024) (W := 19391) check rows elimOK (by decide) (by decide) cover78262 (by decide)
  decide +kernel

theorem h78262 : P.leaf 36 78262 = 19391 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 19391)]) (.cons c78262_0 (.nil)) (by decide) (by decide))

theorem cover78263 : P.CoversSplit 26 10 78263 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000200000000001000010000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 482, 489, 538, 629, 636, 930, 972, 1315, 1658]) (by decide +kernel)

theorem c78263_0 : P.sumLeaves 26 80141312 1024 = 161699 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78263) (lo := 0) (len := 1024) (W := 161699) check rows elimOK (by decide) (by decide) cover78263 (by decide)
  decide +kernel

theorem h78263 : P.leaf 36 78263 = 161699 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 161699)]) (.cons c78263_0 (.nil)) (by decide) (by decide))

theorem cover78265 : P.CoversSplit 26 10 78265 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 481, 482, 531, 629, 636, 972, 979, 1273, 1315, 1658]) (by decide +kernel)

theorem c78265_0 : P.sumLeaves 26 80143360 1024 = 24128 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78265) (lo := 0) (len := 1024) (W := 24128) check rows elimOK (by decide) (by decide) cover78265 (by decide)
  decide +kernel

theorem h78265 : P.leaf 36 78265 = 24128 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 24128)]) (.cons c78265_0 (.nil)) (by decide) (by decide))

theorem cover78267 : P.CoversSplit 26 10 78267 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 481, 482, 531, 629, 636, 972, 979, 1273, 1315, 1658]) (by decide +kernel)

theorem c78267_0 : P.sumLeaves 26 80145408 1024 = 78016 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78267) (lo := 0) (len := 1024) (W := 78016) check rows elimOK (by decide) (by decide) cover78267 (by decide)
  decide +kernel

theorem h78267 : P.leaf 36 78267 = 78016 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 78016)]) (.cons c78267_0 (.nil)) (by decide) (by decide))

theorem cover78268 : P.CoversSplit 26 10 78268 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 531, 538, 629, 636, 867, 972, 979, 1273, 1315, 1658]) (by decide +kernel)

theorem c78268_0 : P.sumLeaves 26 80146432 1024 = 17680 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78268) (lo := 0) (len := 1024) (W := 17680) check rows elimOK (by decide) (by decide) cover78268 (by decide)
  decide +kernel

theorem h78268 : P.leaf 36 78268 = 17680 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 17680)]) (.cons c78268_0 (.nil)) (by decide) (by decide))

theorem cover78269 : P.CoversSplit 26 10 78269 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 531, 538, 629, 636, 874, 972, 979, 1273, 1315, 1658]) (by decide +kernel)

theorem c78269_0 : P.sumLeaves 26 80147456 1024 = 65456 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78269) (lo := 0) (len := 1024) (W := 65456) check rows elimOK (by decide) (by decide) cover78269 (by decide)
  decide +kernel

theorem h78269 : P.leaf 36 78269 = 65456 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 65456)]) (.cons c78269_0 (.nil)) (by decide) (by decide))

theorem cover78270 : P.CoversSplit 26 10 78270 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 531, 538, 629, 636, 867, 972, 979, 1273, 1315, 1658]) (by decide +kernel)

theorem c78270_0 : P.sumLeaves 26 80148480 1024 = 72648 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78270) (lo := 0) (len := 1024) (W := 72648) check rows elimOK (by decide) (by decide) cover78270 (by decide)
  decide +kernel

theorem h78270 : P.leaf 36 78270 = 72648 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 72648)]) (.cons c78270_0 (.nil)) (by decide) (by decide))

theorem cover78271 : P.CoversSplit 26 10 78271 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 531, 538, 629, 636, 874, 972, 979, 1273, 1315, 1658]) (by decide +kernel)

theorem c78271_0 : P.sumLeaves 26 80149504 1024 = 376088 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78271) (lo := 0) (len := 1024) (W := 376088) check rows elimOK (by decide) (by decide) cover78271 (by decide)
  decide +kernel

theorem h78271 : P.leaf 36 78271 = 376088 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 376088)]) (.cons c78271_0 (.nil)) (by decide) (by decide))

theorem cover78285 : P.CoversSplit 26 10 78285 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 629, 636, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c78285_0 : P.sumLeaves 26 80163840 1024 = 13920 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78285) (lo := 0) (len := 1024) (W := 13920) check rows elimOK (by decide) (by decide) cover78285 (by decide)
  decide +kernel

theorem h78285 : P.leaf 36 78285 = 13920 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 13920)]) (.cons c78285_0 (.nil)) (by decide) (by decide))

theorem cover78286 : P.CoversSplit 26 10 78286 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 629, 636, 873, 879, 972, 979, 1315, 1322, 1658]) (by decide +kernel)

theorem c78286_0 : P.sumLeaves 26 80164864 1024 = 13440 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78286) (lo := 0) (len := 1024) (W := 13440) check rows elimOK (by decide) (by decide) cover78286 (by decide)
  decide +kernel

theorem h78286 : P.leaf 36 78286 = 13440 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 13440)]) (.cons c78286_0 (.nil)) (by decide) (by decide))

theorem cover78287 : P.CoversSplit 26 10 78287 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 629, 636, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c78287_0 : P.sumLeaves 26 80165888 1024 = 90016 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78287) (lo := 0) (len := 1024) (W := 90016) check rows elimOK (by decide) (by decide) cover78287 (by decide)
  decide +kernel

theorem h78287 : P.leaf 36 78287 = 90016 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 90016)]) (.cons c78287_0 (.nil)) (by decide) (by decide))

theorem cover78300 : P.CoversSplit 26 10 78300 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 479, 531, 629, 636, 867, 972, 979, 1322, 1658]) (by decide +kernel)

theorem c78300_0 : P.sumLeaves 26 80179200 1024 = 26048 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78300) (lo := 0) (len := 1024) (W := 26048) check rows elimOK (by decide) (by decide) cover78300 (by decide)
  decide +kernel

theorem h78300 : P.leaf 36 78300 = 26048 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 26048)]) (.cons c78300_0 (.nil)) (by decide) (by decide))

theorem cover78301 : P.CoversSplit 26 10 78301 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 629, 636, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c78301_0 : P.sumLeaves 26 80180224 1024 = 104840 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78301) (lo := 0) (len := 1024) (W := 104840) check rows elimOK (by decide) (by decide) cover78301 (by decide)
  decide +kernel

theorem h78301 : P.leaf 36 78301 = 104840 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 104840)]) (.cons c78301_0 (.nil)) (by decide) (by decide))

theorem cover78302 : P.CoversSplit 26 10 78302 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 629, 636, 867, 873, 972, 979, 1315, 1322, 1658]) (by decide +kernel)

theorem c78302_0 : P.sumLeaves 26 80181248 1024 = 73152 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78302) (lo := 0) (len := 1024) (W := 73152) check rows elimOK (by decide) (by decide) cover78302 (by decide)
  decide +kernel

theorem h78302 : P.leaf 36 78302 = 73152 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 73152)]) (.cons c78302_0 (.nil)) (by decide) (by decide))

theorem cover78303 : P.CoversSplit 26 10 78303 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 629, 636, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c78303_0 : P.sumLeaves 26 80182272 1024 = 665272 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78303) (lo := 0) (len := 1024) (W := 665272) check rows elimOK (by decide) (by decide) cover78303 (by decide)
  decide +kernel

theorem h78303 : P.leaf 36 78303 = 665272 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 665272)]) (.cons c78303_0 (.nil)) (by decide) (by decide))

theorem cover78317 : P.CoversSplit 26 10 78317 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 873, 874, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c78317_0 : P.sumLeaves 26 80196608 1024 = 68352 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78317) (lo := 0) (len := 1024) (W := 68352) check rows elimOK (by decide) (by decide) cover78317 (by decide)
  decide +kernel

theorem h78317 : P.leaf 36 78317 = 68352 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 68352)]) (.cons c78317_0 (.nil)) (by decide) (by decide))

theorem cover78318 : P.CoversSplit 26 10 78318 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 873, 874, 879, 972, 979, 1315, 1322, 1658]) (by decide +kernel)

theorem c78318_0 : P.sumLeaves 26 80197632 1024 = 73872 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78318) (lo := 0) (len := 1024) (W := 73872) check rows elimOK (by decide) (by decide) cover78318 (by decide)
  decide +kernel

theorem h78318 : P.leaf 36 78318 = 73872 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 73872)]) (.cons c78318_0 (.nil)) (by decide) (by decide))

theorem cover78319 : P.CoversSplit 26 10 78319 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 873, 874, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c78319_0 : P.sumLeaves 26 80198656 1024 = 638200 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78319) (lo := 0) (len := 1024) (W := 638200) check rows elimOK (by decide) (by decide) cover78319 (by decide)
  decide +kernel

theorem h78319 : P.leaf 36 78319 = 638200 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 638200)]) (.cons c78319_0 (.nil)) (by decide) (by decide))

theorem cover78334 : P.CoversSplit 26 10 78334 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 867, 873, 972, 979, 1315, 1322, 1658]) (by decide +kernel)

theorem c78334_0 : P.sumLeaves 26 80214016 1024 = 350692 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78334) (lo := 0) (len := 1024) (W := 350692) check rows elimOK (by decide) (by decide) cover78334 (by decide)
  decide +kernel

theorem h78334 : P.leaf 36 78334 = 350692 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 350692)]) (.cons c78334_0 (.nil)) (by decide) (by decide))

theorem cover78335 : P.CoversSplit 26 10 78335 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 873, 874, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c78335_0 : P.sumLeaves 26 80215040 1024 = 6302754 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78335) (lo := 0) (len := 1024) (W := 6302754) check rows elimOK (by decide) (by decide) cover78335 (by decide)
  decide +kernel

theorem h78335 : P.leaf 36 78335 = 6302754 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 6302754)]) (.cons c78335_0 (.nil)) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(78190, 720), (78191, 720), (78206, 360), (78207, 360), (78245, 360), (78246, 360), (78247, 720), (78249, 720), (78251, 720), (78253, 720), (78254, 720), (78255, 720), (78262, 180), (78263, 360), (78265, 720), (78267, 720), (78268, 720), (78269, 720), (78270, 720), (78271, 720), (78285, 720), (78286, 720), (78287, 720), (78300, 720), (78301, 720), (78302, 720), (78303, 720), (78317, 360), (78318, 720), (78319, 720), (78334, 360), (78335, 360)]

theorem segOK : checkSeg 20 perms 78190 78593 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 78190 78593 19620 5046793740 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 5046793740)
    (SegSum.cons (w := 720) h78190 (SegSum.cons (w := 720) h78191 (SegSum.cons (w := 360) h78206 (SegSum.cons (w := 360) h78207 (SegSum.cons (w := 360) h78245 (SegSum.cons (w := 360) h78246 (SegSum.cons (w := 720) h78247 (SegSum.cons (w := 720) h78249 (SegSum.cons (w := 720) h78251 (SegSum.cons (w := 720) h78253 (SegSum.cons (w := 720) h78254 (SegSum.cons (w := 720) h78255 (SegSum.cons (w := 180) h78262 (SegSum.cons (w := 360) h78263 (SegSum.cons (w := 720) h78265 (SegSum.cons (w := 720) h78267 (SegSum.cons (w := 720) h78268 (SegSum.cons (w := 720) h78269 (SegSum.cons (w := 720) h78270 (SegSum.cons (w := 720) h78271 (SegSum.cons (w := 720) h78285 (SegSum.cons (w := 720) h78286 (SegSum.cons (w := 720) h78287 (SegSum.cons (w := 720) h78300 (SegSum.cons (w := 720) h78301 (SegSum.cons (w := 720) h78302 (SegSum.cons (w := 720) h78303 (SegSum.cons (w := 360) h78317 (SegSum.cons (w := 720) h78318 (SegSum.cons (w := 720) h78319 (SegSum.cons (w := 360) h78334 (SegSum.cons (w := 360) h78335 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S45
