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

namespace RACert.S6N0.C0.S49

open RACert RACert.Problem

theorem cover78847 : P.CoversSplit 26 10 78847 0xfffffffafffffafafffffffafffffafafffcfff8fffcc8c8aaa8aaa8aa888888fffffafafffffafaaaaaaaaaaaaaaaaafffcfaf8fffcc8c8aaa8aaa8aa888888fffffffafffffafafffffffafffffafaffccffc8ccccc8c8aa88aa8888888888fffffafafffffafaaaaaaaaaaaaaaaaaffccfac8ccccc8c8aa88aa8888888888 :=
  coversSplit check rows (by decide) (by decide) (xs := [873, 930, 972, 979, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c78847_0 : P.sumLeaves 26 80739328 205 = 7663120 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78847) (lo := 0) (len := 205) (W := 7663120) check rows elimOK (by decide) (by decide) cover78847 (by decide)
  decide +kernel

theorem c78847_1 : P.sumLeaves 26 80739533 171 = 111596744 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78847) (lo := 205) (len := 171) (W := 111596744) check rows elimOK (by decide) (by decide) cover78847 (by decide)
  decide +kernel

theorem c78847_2 : P.sumLeaves 26 80739704 108 = 293728737 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78847) (lo := 376) (len := 108) (W := 293728737) check rows elimOK (by decide) (by decide) cover78847 (by decide)
  decide +kernel

theorem c78847_3 : P.sumLeaves 26 80739812 155 = 272611819 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78847) (lo := 484) (len := 155) (W := 272611819) check rows elimOK (by decide) (by decide) cover78847 (by decide)
  decide +kernel

theorem c78847_4 : P.sumLeaves 26 80739967 156 = 428700164 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78847) (lo := 639) (len := 156) (W := 428700164) check rows elimOK (by decide) (by decide) cover78847 (by decide)
  decide +kernel

theorem c78847_5 : P.sumLeaves 26 80740123 139 = 370339351 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78847) (lo := 795) (len := 139) (W := 370339351) check rows elimOK (by decide) (by decide) cover78847 (by decide)
  decide +kernel

theorem c78847_6 : P.sumLeaves 26 80740262 90 = 570508301 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 78847) (lo := 934) (len := 90) (W := 570508301) check rows elimOK (by decide) (by decide) cover78847 (by decide)
  decide +kernel

theorem h78847 : P.leaf 36 78847 = 2055148236 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(205, 7663120), (171, 111596744), (108, 293728737), (155, 272611819), (156, 428700164), (139, 370339351), (90, 570508301)]) (.cons c78847_0 (.cons c78847_1 (.cons c78847_2 (.cons c78847_3 (.cons c78847_4 (.cons c78847_5 (.cons c78847_6 (.nil)))))))) (by decide) (by decide))

theorem cover79068 : P.CoversSplit 26 10 79068 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 467, 475, 537, 580, 587, 629, 930, 972, 1273, 1658]) (by decide +kernel)

theorem c79068_0 : P.sumLeaves 26 80965632 1024 = 123904 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79068) (lo := 0) (len := 1024) (W := 123904) check rows elimOK (by decide) (by decide) cover79068 (by decide)
  decide +kernel

theorem h79068 : P.leaf 36 79068 = 123904 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 123904)]) (.cons c79068_0 (.nil)) (by decide) (by decide))

theorem cover79069 : P.CoversSplit 26 10 79069 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 475, 530, 537, 580, 587, 629, 930, 972, 1273, 1315, 1658]) (by decide +kernel)

theorem c79069_0 : P.sumLeaves 26 80966656 1024 = 123904 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79069) (lo := 0) (len := 1024) (W := 123904) check rows elimOK (by decide) (by decide) cover79069 (by decide)
  decide +kernel

theorem h79069 : P.leaf 36 79069 = 123904 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 123904)]) (.cons c79069_0 (.nil)) (by decide) (by decide))

theorem cover79070 : P.CoversSplit 26 10 79070 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 537, 580, 587, 629, 930, 972, 1273, 1315, 1658]) (by decide +kernel)

theorem c79070_0 : P.sumLeaves 26 80967680 1024 = 123904 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79070) (lo := 0) (len := 1024) (W := 123904) check rows elimOK (by decide) (by decide) cover79070 (by decide)
  decide +kernel

theorem h79070 : P.leaf 36 79070 = 123904 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 123904)]) (.cons c79070_0 (.nil)) (by decide) (by decide))

theorem cover79071 : P.CoversSplit 26 10 79071 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 537, 580, 587, 629, 930, 972, 1273, 1315, 1658]) (by decide +kernel)

theorem c79071_0 : P.sumLeaves 26 80968704 1024 = 123904 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79071) (lo := 0) (len := 1024) (W := 123904) check rows elimOK (by decide) (by decide) cover79071 (by decide)
  decide +kernel

theorem h79071 : P.leaf 36 79071 = 123904 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 123904)]) (.cons c79071_0 (.nil)) (by decide) (by decide))

theorem cover79086 : P.CoversSplit 26 10 79086 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 524, 580, 587, 629, 636, 930, 972, 1273, 1315, 1658]) (by decide +kernel)

theorem c79086_0 : P.sumLeaves 26 80984064 1024 = 245216 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79086) (lo := 0) (len := 1024) (W := 245216) check rows elimOK (by decide) (by decide) cover79086 (by decide)
  decide +kernel

theorem h79086 : P.leaf 36 79086 = 245216 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 245216)]) (.cons c79086_0 (.nil)) (by decide) (by decide))

theorem cover79087 : P.CoversSplit 26 10 79087 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 524, 580, 587, 629, 636, 930, 972, 1273, 1315, 1658]) (by decide +kernel)

theorem c79087_0 : P.sumLeaves 26 80985088 1024 = 245216 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79087) (lo := 0) (len := 1024) (W := 245216) check rows elimOK (by decide) (by decide) cover79087 (by decide)
  decide +kernel

theorem h79087 : P.leaf 36 79087 = 245216 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 245216)]) (.cons c79087_0 (.nil)) (by decide) (by decide))

theorem cover79102 : P.CoversSplit 26 10 79102 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 580, 587, 629, 636, 874, 930, 972, 1273, 1315, 1658]) (by decide +kernel)

theorem c79102_0 : P.sumLeaves 26 81000448 1024 = 306152 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79102) (lo := 0) (len := 1024) (W := 306152) check rows elimOK (by decide) (by decide) cover79102 (by decide)
  decide +kernel

theorem h79102 : P.leaf 36 79102 = 306152 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 306152)]) (.cons c79102_0 (.nil)) (by decide) (by decide))

theorem cover79103 : P.CoversSplit 26 10 79103 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 580, 587, 629, 636, 874, 930, 972, 1273, 1315, 1658]) (by decide +kernel)

theorem c79103_0 : P.sumLeaves 26 81001472 1024 = 306152 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79103) (lo := 0) (len := 1024) (W := 306152) check rows elimOK (by decide) (by decide) cover79103 (by decide)
  decide +kernel

theorem h79103 : P.leaf 36 79103 = 306152 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 306152)]) (.cons c79103_0 (.nil)) (by decide) (by decide))

theorem cover79159 : P.CoversSplit 26 10 79159 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000200000000001000010000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [482, 489, 538, 629, 636, 930, 972, 1315, 1658]) (by decide +kernel)

theorem c79159_0 : P.sumLeaves 26 81058816 1024 = 280129 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79159) (lo := 0) (len := 1024) (W := 280129) check rows elimOK (by decide) (by decide) cover79159 (by decide)
  decide +kernel

theorem h79159 : P.leaf 36 79159 = 280129 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 280129)]) (.cons c79159_0 (.nil)) (by decide) (by decide))

theorem cover79163 : P.CoversSplit 26 10 79163 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 482, 531, 636, 979, 1273, 1315, 1658]) (by decide +kernel)

theorem c79163_0 : P.sumLeaves 26 81062912 1024 = 245760 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79163) (lo := 0) (len := 1024) (W := 245760) check rows elimOK (by decide) (by decide) cover79163 (by decide)
  decide +kernel

theorem h79163 : P.leaf 36 79163 = 245760 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 245760)]) (.cons c79163_0 (.nil)) (by decide) (by decide))

theorem cover79164 : P.CoversSplit 26 10 79164 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 531, 538, 580, 629, 636, 972, 979, 1273, 1315, 1658]) (by decide +kernel)

theorem c79164_0 : P.sumLeaves 26 81063936 1024 = 81508 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79164) (lo := 0) (len := 1024) (W := 81508) check rows elimOK (by decide) (by decide) cover79164 (by decide)
  decide +kernel

theorem h79164 : P.leaf 36 79164 = 81508 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 81508)]) (.cons c79164_0 (.nil)) (by decide) (by decide))

theorem cover79165 : P.CoversSplit 26 10 79165 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 531, 538, 580, 629, 636, 972, 979, 1273, 1315, 1658]) (by decide +kernel)

theorem c79165_0 : P.sumLeaves 26 81064960 1024 = 238852 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79165) (lo := 0) (len := 1024) (W := 238852) check rows elimOK (by decide) (by decide) cover79165 (by decide)
  decide +kernel

theorem h79165 : P.leaf 36 79165 = 238852 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 238852)]) (.cons c79165_0 (.nil)) (by decide) (by decide))

theorem cover79167 : P.CoversSplit 26 10 79167 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 531, 538, 580, 629, 636, 972, 979, 1273, 1315, 1658]) (by decide +kernel)

theorem c79167_0 : P.sumLeaves 26 81067008 1024 = 770884 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79167) (lo := 0) (len := 1024) (W := 770884) check rows elimOK (by decide) (by decide) cover79167 (by decide)
  decide +kernel

theorem h79167 : P.leaf 36 79167 = 770884 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 770884)]) (.cons c79167_0 (.nil)) (by decide) (by decide))

theorem cover79196 : P.CoversSplit 26 10 79196 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 479, 530, 531, 629, 636, 972, 979, 1322, 1658, 1665]) (by decide +kernel)

theorem c79196_0 : P.sumLeaves 26 81096704 1024 = 81920 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79196) (lo := 0) (len := 1024) (W := 81920) check rows elimOK (by decide) (by decide) cover79196 (by decide)
  decide +kernel

theorem h79196 : P.leaf 36 79196 = 81920 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 81920)]) (.cons c79196_0 (.nil)) (by decide) (by decide))

theorem cover79197 : P.CoversSplit 26 10 79197 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 579, 629, 636, 923, 972, 979, 1322, 1658, 1665]) (by decide +kernel)

theorem c79197_0 : P.sumLeaves 26 81097728 1024 = 260608 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79197) (lo := 0) (len := 1024) (W := 260608) check rows elimOK (by decide) (by decide) cover79197 (by decide)
  decide +kernel

theorem h79197 : P.leaf 36 79197 = 260608 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 260608)]) (.cons c79197_0 (.nil)) (by decide) (by decide))

theorem cover79198 : P.CoversSplit 26 10 79198 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 579, 629, 636, 873, 972, 979, 1322, 1658, 1665]) (by decide +kernel)

theorem c79198_0 : P.sumLeaves 26 81098752 1024 = 231552 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79198) (lo := 0) (len := 1024) (W := 231552) check rows elimOK (by decide) (by decide) cover79198 (by decide)
  decide +kernel

theorem h79198 : P.leaf 36 79198 = 231552 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 231552)]) (.cons c79198_0 (.nil)) (by decide) (by decide))

theorem cover79199 : P.CoversSplit 26 10 79199 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 579, 629, 636, 923, 972, 979, 1322, 1658, 1665]) (by decide +kernel)

theorem c79199_0 : P.sumLeaves 26 81099776 1024 = 853504 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79199) (lo := 0) (len := 1024) (W := 853504) check rows elimOK (by decide) (by decide) cover79199 (by decide)
  decide +kernel

theorem h79199 : P.leaf 36 79199 = 853504 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 853504)]) (.cons c79199_0 (.nil)) (by decide) (by decide))

theorem cover79212 : P.CoversSplit 26 10 79212 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 579, 580, 629, 636, 873, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c79212_0 : P.sumLeaves 26 81113088 1024 = 124056 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79212) (lo := 0) (len := 1024) (W := 124056) check rows elimOK (by decide) (by decide) cover79212 (by decide)
  decide +kernel

theorem h79212 : P.leaf 36 79212 = 124056 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 124056)]) (.cons c79212_0 (.nil)) (by decide) (by decide))

theorem cover79213 : P.CoversSplit 26 10 79213 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 579, 580, 629, 636, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c79213_0 : P.sumLeaves 26 81114112 1024 = 153132 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79213) (lo := 0) (len := 1024) (W := 153132) check rows elimOK (by decide) (by decide) cover79213 (by decide)
  decide +kernel

theorem h79213 : P.leaf 36 79213 = 153132 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 153132)]) (.cons c79213_0 (.nil)) (by decide) (by decide))

theorem cover79214 : P.CoversSplit 26 10 79214 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 579, 580, 629, 636, 873, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c79214_0 : P.sumLeaves 26 81115136 1024 = 559542 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79214) (lo := 0) (len := 1024) (W := 559542) check rows elimOK (by decide) (by decide) cover79214 (by decide)
  decide +kernel

theorem h79214 : P.leaf 36 79214 = 559542 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 559542)]) (.cons c79214_0 (.nil)) (by decide) (by decide))

theorem cover79215 : P.CoversSplit 26 10 79215 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 579, 580, 629, 636, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c79215_0 : P.sumLeaves 26 81116160 1024 = 775504 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79215) (lo := 0) (len := 1024) (W := 775504) check rows elimOK (by decide) (by decide) cover79215 (by decide)
  decide +kernel

theorem h79215 : P.leaf 36 79215 = 775504 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 775504)]) (.cons c79215_0 (.nil)) (by decide) (by decide))

theorem cover79230 : P.CoversSplit 26 10 79230 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 579, 580, 629, 636, 873, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c79230_0 : P.sumLeaves 26 81131520 1024 = 1942709 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79230) (lo := 0) (len := 1024) (W := 1942709) check rows elimOK (by decide) (by decide) cover79230 (by decide)
  decide +kernel

theorem h79230 : P.leaf 36 79230 = 1942709 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1942709)]) (.cons c79230_0 (.nil)) (by decide) (by decide))

theorem cover79231 : P.CoversSplit 26 10 79231 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 579, 580, 629, 636, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c79231_0 : P.sumLeaves 26 81132544 1024 = 2958212 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79231) (lo := 0) (len := 1024) (W := 2958212) check rows elimOK (by decide) (by decide) cover79231 (by decide)
  decide +kernel

theorem h79231 : P.leaf 36 79231 = 2958212 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 2958212)]) (.cons c79231_0 (.nil)) (by decide) (by decide))

theorem cover79269 : P.CoversSplit 26 10 79269 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000200000000001000010000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 482, 489, 538, 629, 636, 930, 972, 979, 1315, 1658]) (by decide +kernel)

theorem c79269_0 : P.sumLeaves 26 81171456 1024 = 68444 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79269) (lo := 0) (len := 1024) (W := 68444) check rows elimOK (by decide) (by decide) cover79269 (by decide)
  decide +kernel

theorem h79269 : P.leaf 36 79269 = 68444 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 68444)]) (.cons c79269_0 (.nil)) (by decide) (by decide))

theorem cover79271 : P.CoversSplit 26 10 79271 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000200000000001000010000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 482, 489, 538, 629, 636, 930, 972, 1315, 1658]) (by decide +kernel)

theorem c79271_0 : P.sumLeaves 26 81173504 1024 = 231996 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79271) (lo := 0) (len := 1024) (W := 231996) check rows elimOK (by decide) (by decide) cover79271 (by decide)
  decide +kernel

theorem h79271 : P.leaf 36 79271 = 231996 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 231996)]) (.cons c79271_0 (.nil)) (by decide) (by decide))

theorem cover79276 : P.CoversSplit 26 10 79276 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 531, 538, 566, 629, 636, 972, 979, 1273, 1315, 1658]) (by decide +kernel)

theorem c79276_0 : P.sumLeaves 26 81178624 1024 = 39664 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79276) (lo := 0) (len := 1024) (W := 39664) check rows elimOK (by decide) (by decide) cover79276 (by decide)
  decide +kernel

theorem h79276 : P.leaf 36 79276 = 39664 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 39664)]) (.cons c79276_0 (.nil)) (by decide) (by decide))

theorem cover79277 : P.CoversSplit 26 10 79277 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 531, 538, 566, 629, 636, 972, 979, 1273, 1315, 1658]) (by decide +kernel)

theorem c79277_0 : P.sumLeaves 26 81179648 1024 = 249636 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79277) (lo := 0) (len := 1024) (W := 249636) check rows elimOK (by decide) (by decide) cover79277 (by decide)
  decide +kernel

theorem h79277 : P.leaf 36 79277 = 249636 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 249636)]) (.cons c79277_0 (.nil)) (by decide) (by decide))

theorem cover79278 : P.CoversSplit 26 10 79278 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 531, 538, 629, 636, 874, 972, 979, 1273, 1315, 1658]) (by decide +kernel)

theorem c79278_0 : P.sumLeaves 26 81180672 1024 = 75048 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79278) (lo := 0) (len := 1024) (W := 75048) check rows elimOK (by decide) (by decide) cover79278 (by decide)
  decide +kernel

theorem h79278 : P.leaf 36 79278 = 75048 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 75048)]) (.cons c79278_0 (.nil)) (by decide) (by decide))

theorem cover79279 : P.CoversSplit 26 10 79279 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 531, 538, 629, 636, 874, 972, 979, 1273, 1315, 1658]) (by decide +kernel)

theorem c79279_0 : P.sumLeaves 26 81181696 1024 = 473696 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79279) (lo := 0) (len := 1024) (W := 473696) check rows elimOK (by decide) (by decide) cover79279 (by decide)
  decide +kernel

theorem h79279 : P.leaf 36 79279 = 473696 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 473696)]) (.cons c79279_0 (.nil)) (by decide) (by decide))

theorem cover79287 : P.CoversSplit 26 10 79287 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000200000000001000010000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 482, 489, 538, 629, 636, 930, 972, 1315, 1658]) (by decide +kernel)

theorem c79287_0 : P.sumLeaves 26 81189888 1024 = 914628 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79287) (lo := 0) (len := 1024) (W := 914628) check rows elimOK (by decide) (by decide) cover79287 (by decide)
  decide +kernel

theorem h79287 : P.leaf 36 79287 = 914628 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 914628)]) (.cons c79287_0 (.nil)) (by decide) (by decide))

theorem cover79292 : P.CoversSplit 26 10 79292 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 531, 538, 629, 636, 874, 972, 979, 1273, 1315, 1658]) (by decide +kernel)

theorem c79292_0 : P.sumLeaves 26 81195008 1024 = 320956 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79292) (lo := 0) (len := 1024) (W := 320956) check rows elimOK (by decide) (by decide) cover79292 (by decide)
  decide +kernel

theorem h79292 : P.leaf 36 79292 = 320956 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 320956)]) (.cons c79292_0 (.nil)) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(78847, 180), (79068, 360), (79069, 360), (79070, 360), (79071, 360), (79086, 360), (79087, 360), (79102, 360), (79103, 360), (79159, 90), (79163, 180), (79164, 360), (79165, 720), (79167, 360), (79196, 720), (79197, 720), (79198, 720), (79199, 720), (79212, 360), (79213, 360), (79214, 720), (79215, 720), (79230, 360), (79231, 360), (79269, 180), (79271, 360), (79276, 720), (79277, 720), (79278, 720), (79279, 720), (79287, 180), (79292, 720)]

theorem segOK : checkSeg 20 perms 78847 79293 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 78847 79293 14850 375998536530 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 375998536530)
    (SegSum.cons (w := 180) h78847 (SegSum.cons (w := 360) h79068 (SegSum.cons (w := 360) h79069 (SegSum.cons (w := 360) h79070 (SegSum.cons (w := 360) h79071 (SegSum.cons (w := 360) h79086 (SegSum.cons (w := 360) h79087 (SegSum.cons (w := 360) h79102 (SegSum.cons (w := 360) h79103 (SegSum.cons (w := 90) h79159 (SegSum.cons (w := 180) h79163 (SegSum.cons (w := 360) h79164 (SegSum.cons (w := 720) h79165 (SegSum.cons (w := 360) h79167 (SegSum.cons (w := 720) h79196 (SegSum.cons (w := 720) h79197 (SegSum.cons (w := 720) h79198 (SegSum.cons (w := 720) h79199 (SegSum.cons (w := 360) h79212 (SegSum.cons (w := 360) h79213 (SegSum.cons (w := 720) h79214 (SegSum.cons (w := 720) h79215 (SegSum.cons (w := 360) h79230 (SegSum.cons (w := 360) h79231 (SegSum.cons (w := 180) h79269 (SegSum.cons (w := 360) h79271 (SegSum.cons (w := 720) h79276 (SegSum.cons (w := 720) h79277 (SegSum.cons (w := 720) h79278 (SegSum.cons (w := 720) h79279 (SegSum.cons (w := 180) h79287 (SegSum.cons (w := 720) h79292 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S49
