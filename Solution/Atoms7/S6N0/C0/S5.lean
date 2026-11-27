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

namespace RACert.S6N0.C0.S5

open RACert RACert.Problem

theorem cover1790 : P.CoversSplit 26 10 1790 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [874]) (by decide +kernel)

theorem c1790_0 : P.sumLeaves 26 1832960 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1790) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1790 (by decide)
  decide +kernel

theorem h1790 : P.leaf 36 1790 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1790_0 (.nil)) (by decide) (by decide))

theorem cover1791 : P.CoversSplit 26 10 1791 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [929]) (by decide +kernel)

theorem c1791_0 : P.sumLeaves 26 1833984 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1791) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover1791 (by decide)
  decide +kernel

theorem h1791 : P.leaf 36 1791 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c1791_0 (.nil)) (by decide) (by decide))

theorem cover2028 : P.CoversSplit 26 10 2028 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [874]) (by decide +kernel)

theorem c2028_0 : P.sumLeaves 26 2076672 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 2028) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover2028 (by decide)
  decide +kernel

theorem h2028 : P.leaf 36 2028 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c2028_0 (.nil)) (by decide) (by decide))

theorem cover2029 : P.CoversSplit 26 10 2029 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c2029_0 : P.sumLeaves 26 2077696 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 2029) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover2029 (by decide)
  decide +kernel

theorem h2029 : P.leaf 36 2029 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c2029_0 (.nil)) (by decide) (by decide))

theorem cover2031 : P.CoversSplit 26 10 2031 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c2031_0 : P.sumLeaves 26 2079744 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 2031) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover2031 (by decide)
  decide +kernel

theorem h2031 : P.leaf 36 2031 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c2031_0 (.nil)) (by decide) (by decide))

theorem cover2047 : P.CoversSplit 26 10 2047 0xfff8fff8fff88888fff8faf8fff88888fff8fff8ffc888888888888888888888faf8aaa8faf88888aaa8aaa8aaa88888faf8aaa8fac888888888888888888888ffc8ffc8ccc88888ffc8fac8ccc88888ccc8ccc8ccc888888888888888888888fac8aa88c8c88888aa88aa8888888888c8c88888c8c888888888888888888888 :=
  coversSplit check rows (by decide) (by decide) (xs := [873, 881, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c2047_0 : P.sumLeaves 26 2096128 319 = 16601280 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 2047) (lo := 0) (len := 319) (W := 16601280) check rows elimOK (by decide) (by decide) cover2047 (by decide)
  decide +kernel

theorem c2047_1 : P.sumLeaves 26 2096447 220 = 102950864 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 2047) (lo := 319) (len := 220) (W := 102950864) check rows elimOK (by decide) (by decide) cover2047 (by decide)
  decide +kernel

theorem c2047_2 : P.sumLeaves 26 2096667 226 = 93981256 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 2047) (lo := 539) (len := 226) (W := 93981256) check rows elimOK (by decide) (by decide) cover2047 (by decide)
  decide +kernel

theorem c2047_3 : P.sumLeaves 26 2096893 190 = 80980112 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 2047) (lo := 765) (len := 190) (W := 80980112) check rows elimOK (by decide) (by decide) cover2047 (by decide)
  decide +kernel

theorem c2047_4 : P.sumLeaves 26 2097083 69 = 92566808 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 2047) (lo := 955) (len := 69) (W := 92566808) check rows elimOK (by decide) (by decide) cover2047 (by decide)
  decide +kernel

theorem h2047 : P.leaf 36 2047 = 387080320 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(319, 16601280), (220, 102950864), (226, 93981256), (190, 80980112), (69, 92566808)]) (.cons c2047_0 (.cons c2047_1 (.cons c2047_2 (.cons c2047_3 (.cons c2047_4 (.nil)))))) (by decide) (by decide))

theorem cover3126 : P.CoversSplit 26 10 3126 0x8000000000000000000000000000000000000000000000000000000000000000800004000000000000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000020000100000000000000010000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 538, 579, 587, 629, 636, 922, 930, 1265, 2008]) (by decide +kernel)

theorem c3126_0 : P.sumLeaves 26 3201024 1024 = 173712 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3126) (lo := 0) (len := 1024) (W := 173712) check rows elimOK (by decide) (by decide) cover3126 (by decide)
  decide +kernel

theorem h3126 : P.leaf 36 3126 = 173712 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 173712)]) (.cons c3126_0 (.nil)) (by decide) (by decide))

theorem cover3127 : P.CoversSplit 26 10 3127 0x8000000000000000000000000000000000000000000000000000000000000000800004000000000000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000020000100000000000000010000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 538, 579, 587, 629, 636, 881, 922, 1265, 2008]) (by decide +kernel)

theorem c3127_0 : P.sumLeaves 26 3202048 1024 = 255600 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3127) (lo := 0) (len := 1024) (W := 255600) check rows elimOK (by decide) (by decide) cover3127 (by decide)
  decide +kernel

theorem h3127 : P.leaf 36 3127 = 255600 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 255600)]) (.cons c3127_0 (.nil)) (by decide) (by decide))

theorem cover3130 : P.CoversSplit 26 10 3130 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000100000000000000010000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 531, 538, 579, 587, 629, 636, 881, 922, 930, 1265]) (by decide +kernel)

theorem c3130_0 : P.sumLeaves 26 3205120 1024 = 916 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3130) (lo := 0) (len := 1024) (W := 916) check rows elimOK (by decide) (by decide) cover3130 (by decide)
  decide +kernel

theorem h3130 : P.leaf 36 3130 = 916 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 916)]) (.cons c3130_0 (.nil)) (by decide) (by decide))

theorem cover3131 : P.CoversSplit 26 10 3131 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000100000000000000010000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 531, 538, 579, 587, 629, 636, 881, 922, 1265]) (by decide +kernel)

theorem c3131_0 : P.sumLeaves 26 3206144 1024 = 4116 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3131) (lo := 0) (len := 1024) (W := 4116) check rows elimOK (by decide) (by decide) cover3131 (by decide)
  decide +kernel

theorem h3131 : P.leaf 36 3131 = 4116 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 4116)]) (.cons c3131_0 (.nil)) (by decide) (by decide))

theorem cover3134 : P.CoversSplit 26 10 3134 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000100000000000000010000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 531, 538, 579, 587, 629, 636, 881, 922, 930, 1265]) (by decide +kernel)

theorem c3134_0 : P.sumLeaves 26 3209216 1024 = 3664 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3134) (lo := 0) (len := 1024) (W := 3664) check rows elimOK (by decide) (by decide) cover3134 (by decide)
  decide +kernel

theorem h3134 : P.leaf 36 3134 = 3664 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 3664)]) (.cons c3134_0 (.nil)) (by decide) (by decide))

theorem cover3135 : P.CoversSplit 26 10 3135 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000100000000000000010000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 531, 538, 579, 587, 629, 636, 881, 922, 1265]) (by decide +kernel)

theorem c3135_0 : P.sumLeaves 26 3210240 1024 = 10188 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3135) (lo := 0) (len := 1024) (W := 10188) check rows elimOK (by decide) (by decide) cover3135 (by decide)
  decide +kernel

theorem h3135 : P.leaf 36 3135 = 10188 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 10188)]) (.cons c3135_0 (.nil)) (by decide) (by decide))

theorem cover3164 : P.CoversSplit 26 10 3164 0x8000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 475, 480, 531, 579, 587, 629, 636, 880, 922, 930, 972, 979, 1265, 1273]) (by decide +kernel)

theorem c3164_0 : P.sumLeaves 26 3239936 1024 = 1088 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3164) (lo := 0) (len := 1024) (W := 1088) check rows elimOK (by decide) (by decide) cover3164 (by decide)
  decide +kernel

theorem h3164 : P.leaf 36 3164 = 1088 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1088)]) (.cons c3164_0 (.nil)) (by decide) (by decide))

theorem cover3165 : P.CoversSplit 26 10 3165 0x8000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 475, 480, 531, 579, 587, 629, 636, 880, 922, 930, 972, 979, 1265, 1273]) (by decide +kernel)

theorem c3165_0 : P.sumLeaves 26 3240960 1024 = 16864 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3165) (lo := 0) (len := 1024) (W := 16864) check rows elimOK (by decide) (by decide) cover3165 (by decide)
  decide +kernel

theorem h3165 : P.leaf 36 3165 = 16864 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 16864)]) (.cons c3165_0 (.nil)) (by decide) (by decide))

theorem cover3166 : P.CoversSplit 26 10 3166 0x8000000000000001000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 579, 587, 629, 636, 880, 922, 930, 1265, 1273, 1658, 1665]) (by decide +kernel)

theorem c3166_0 : P.sumLeaves 26 3241984 1024 = 5392 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3166) (lo := 0) (len := 1024) (W := 5392) check rows elimOK (by decide) (by decide) cover3166 (by decide)
  decide +kernel

theorem h3166 : P.leaf 36 3166 = 5392 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 5392)]) (.cons c3166_0 (.nil)) (by decide) (by decide))

theorem cover3167 : P.CoversSplit 26 10 3167 0x8000000000000001000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 579, 587, 629, 636, 880, 922, 930, 1265, 1273, 1658, 1665]) (by decide +kernel)

theorem c3167_0 : P.sumLeaves 26 3243008 1024 = 53232 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3167) (lo := 0) (len := 1024) (W := 53232) check rows elimOK (by decide) (by decide) cover3167 (by decide)
  decide +kernel

theorem h3167 : P.leaf 36 3167 = 53232 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 53232)]) (.cons c3167_0 (.nil)) (by decide) (by decide))

theorem cover3198 : P.CoversSplit 26 10 3198 0x8000000000000001000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000002000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 579, 587, 629, 636, 874, 881, 922, 930, 1265, 1273, 1658, 1665]) (by decide +kernel)

theorem c3198_0 : P.sumLeaves 26 3274752 1024 = 37560 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3198) (lo := 0) (len := 1024) (W := 37560) check rows elimOK (by decide) (by decide) cover3198 (by decide)
  decide +kernel

theorem h3198 : P.leaf 36 3198 = 37560 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 37560)]) (.cons c3198_0 (.nil)) (by decide) (by decide))

theorem cover3199 : P.CoversSplit 26 10 3199 0x8000000000000001000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000002000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 579, 587, 629, 636, 874, 881, 922, 930, 1265, 1273, 1658, 1665]) (by decide +kernel)

theorem c3199_0 : P.sumLeaves 26 3275776 1024 = 153824 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3199) (lo := 0) (len := 1024) (W := 153824) check rows elimOK (by decide) (by decide) cover3199 (by decide)
  decide +kernel

theorem h3199 : P.leaf 36 3199 = 153824 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 153824)]) (.cons c3199_0 (.nil)) (by decide) (by decide))

theorem cover3219 : P.CoversSplit 26 10 3219 0x8000000000000000000000000000000000000000000000000000000000000000800000000000000000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000020000000000000000000010000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 530, 538, 587, 629, 636, 881, 922, 2008]) (by decide +kernel)

theorem c3219_0 : P.sumLeaves 26 3296256 1024 = 518776 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3219) (lo := 0) (len := 1024) (W := 518776) check rows elimOK (by decide) (by decide) cover3219 (by decide)
  decide +kernel

theorem h3219 : P.leaf 36 3219 = 518776 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 518776)]) (.cons c3219_0 (.nil)) (by decide) (by decide))

theorem cover3220 : P.CoversSplit 26 10 3220 0x8000000000000000000000000000000000000000000000000000000000000000cc0004000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000033000100000000000100000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 538, 587, 629, 636, 922, 972, 979, 1265, 2008]) (by decide +kernel)

theorem c3220_0 : P.sumLeaves 26 3297280 1024 = 53416 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3220) (lo := 0) (len := 1024) (W := 53416) check rows elimOK (by decide) (by decide) cover3220 (by decide)
  decide +kernel

theorem h3220 : P.leaf 36 3220 = 53416 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 53416)]) (.cons c3220_0 (.nil)) (by decide) (by decide))

theorem cover3221 : P.CoversSplit 26 10 3221 0x8000000000000000000000000000000000000000000000000000000000000000cc0004000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000033000100000000000100000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 538, 587, 629, 636, 881, 922, 972, 1265, 2008]) (by decide +kernel)

theorem c3221_0 : P.sumLeaves 26 3298304 1024 = 905548 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3221) (lo := 0) (len := 1024) (W := 905548) check rows elimOK (by decide) (by decide) cover3221 (by decide)
  decide +kernel

theorem h3221 : P.leaf 36 3221 = 905548 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 905548)]) (.cons c3221_0 (.nil)) (by decide) (by decide))

theorem cover3223 : P.CoversSplit 26 10 3223 0x8000000000000000000000000000000000000000000000000000000000000000cc0004000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000033000100000000000100000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 538, 587, 629, 636, 881, 972, 1265, 2008]) (by decide +kernel)

theorem c3223_0 : P.sumLeaves 26 3300352 1024 = 3523760 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3223) (lo := 0) (len := 1024) (W := 3523760) check rows elimOK (by decide) (by decide) cover3223 (by decide)
  decide +kernel

theorem h3223 : P.leaf 36 3223 = 3523760 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 3523760)]) (.cons c3223_0 (.nil)) (by decide) (by decide))

theorem cover3224 : P.CoversSplit 26 10 3224 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [531]) (by decide +kernel)

theorem c3224_0 : P.sumLeaves 26 3301376 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3224) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3224 (by decide)
  decide +kernel

theorem h3224 : P.leaf 36 3224 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3224_0 (.nil)) (by decide) (by decide))

theorem cover3225 : P.CoversSplit 26 10 3225 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [531]) (by decide +kernel)

theorem c3225_0 : P.sumLeaves 26 3302400 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3225) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3225 (by decide)
  decide +kernel

theorem h3225 : P.leaf 36 3225 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3225_0 (.nil)) (by decide) (by decide))

theorem cover3227 : P.CoversSplit 26 10 3227 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [531]) (by decide +kernel)

theorem c3227_0 : P.sumLeaves 26 3304448 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3227) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3227 (by decide)
  decide +kernel

theorem h3227 : P.leaf 36 3227 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3227_0 (.nil)) (by decide) (by decide))

theorem cover3228 : P.CoversSplit 26 10 3228 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [531]) (by decide +kernel)

theorem c3228_0 : P.sumLeaves 26 3305472 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3228) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3228 (by decide)
  decide +kernel

theorem h3228 : P.leaf 36 3228 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3228_0 (.nil)) (by decide) (by decide))

theorem cover3229 : P.CoversSplit 26 10 3229 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [531]) (by decide +kernel)

theorem c3229_0 : P.sumLeaves 26 3306496 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3229) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3229 (by decide)
  decide +kernel

theorem h3229 : P.leaf 36 3229 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3229_0 (.nil)) (by decide) (by decide))

theorem cover3231 : P.CoversSplit 26 10 3231 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [531]) (by decide +kernel)

theorem c3231_0 : P.sumLeaves 26 3308544 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3231) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3231 (by decide)
  decide +kernel

theorem h3231 : P.leaf 36 3231 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3231_0 (.nil)) (by decide) (by decide))

theorem cover3254 : P.CoversSplit 26 10 3254 0x8000000000000000000000000000000000000000000000000000000000000000cc00cc0000000000cc00c800000000000000000000000000000000000000000000000000000000000000000000000000000000000033003300000000003300320000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 538, 587, 629, 636, 922, 930, 972, 1315, 1658, 2008]) (by decide +kernel)

theorem c3254_0 : P.sumLeaves 26 3332096 1024 = 6821088 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3254) (lo := 0) (len := 1024) (W := 6821088) check rows elimOK (by decide) (by decide) cover3254 (by decide)
  decide +kernel

theorem h3254 : P.leaf 36 3254 = 6821088 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 6821088)]) (.cons c3254_0 (.nil)) (by decide) (by decide))

theorem cover3255 : P.CoversSplit 26 10 3255 0x8000000000000000000000000000000000000000000000000000000000000000cc00cc0000000000cc00c800000000000000000000000000000000000000000000000000000000000000000000000000000000000033003300000000003300320000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 538, 587, 629, 636, 881, 922, 972, 1315, 1658, 2008]) (by decide +kernel)

theorem c3255_0 : P.sumLeaves 26 3333120 1024 = 16517420 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3255) (lo := 0) (len := 1024) (W := 16517420) check rows elimOK (by decide) (by decide) cover3255 (by decide)
  decide +kernel

theorem h3255 : P.leaf 36 3255 = 16517420 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 16517420)]) (.cons c3255_0 (.nil)) (by decide) (by decide))

theorem cover3256 : P.CoversSplit 26 10 3256 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c3256_0 : P.sumLeaves 26 3334144 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3256) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3256 (by decide)
  decide +kernel

theorem h3256 : P.leaf 36 3256 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3256_0 (.nil)) (by decide) (by decide))

theorem cover3257 : P.CoversSplit 26 10 3257 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c3257_0 : P.sumLeaves 26 3335168 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 3257) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover3257 (by decide)
  decide +kernel

theorem h3257 : P.leaf 36 3257 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c3257_0 (.nil)) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(1790, 360), (1791, 360), (2028, 60), (2029, 180), (2031, 180), (2047, 60), (3126, 60), (3127, 60), (3130, 360), (3131, 360), (3134, 180), (3135, 180), (3164, 120), (3165, 120), (3166, 360), (3167, 360), (3198, 180), (3199, 180), (3219, 90), (3220, 72), (3221, 360), (3223, 360), (3224, 360), (3225, 720), (3227, 360), (3228, 360), (3229, 720), (3231, 360), (3254, 180), (3255, 180), (3256, 360), (3257, 360)]

theorem segOK : checkSeg 20 perms 1790 3258 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 1790 3258 8562 29158608912 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 29158608912)
    (SegSum.cons (w := 360) h1790 (SegSum.cons (w := 360) h1791 (SegSum.cons (w := 60) h2028 (SegSum.cons (w := 180) h2029 (SegSum.cons (w := 180) h2031 (SegSum.cons (w := 60) h2047 (SegSum.cons (w := 60) h3126 (SegSum.cons (w := 60) h3127 (SegSum.cons (w := 360) h3130 (SegSum.cons (w := 360) h3131 (SegSum.cons (w := 180) h3134 (SegSum.cons (w := 180) h3135 (SegSum.cons (w := 120) h3164 (SegSum.cons (w := 120) h3165 (SegSum.cons (w := 360) h3166 (SegSum.cons (w := 360) h3167 (SegSum.cons (w := 180) h3198 (SegSum.cons (w := 180) h3199 (SegSum.cons (w := 90) h3219 (SegSum.cons (w := 72) h3220 (SegSum.cons (w := 360) h3221 (SegSum.cons (w := 360) h3223 (SegSum.cons (w := 360) h3224 (SegSum.cons (w := 720) h3225 (SegSum.cons (w := 360) h3227 (SegSum.cons (w := 360) h3228 (SegSum.cons (w := 720) h3229 (SegSum.cons (w := 360) h3231 (SegSum.cons (w := 180) h3254 (SegSum.cons (w := 180) h3255 (SegSum.cons (w := 360) h3256 (SegSum.cons (w := 360) h3257 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S5
