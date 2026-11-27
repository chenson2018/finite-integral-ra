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

namespace RACert.S6N0.C0.S56

open RACert RACert.Problem

theorem cover79855 : P.CoversSplit 26 10 79855 0xfffffffafffffafafffffffafffffafafffcfff8fffcc8c8aaa8aaa8aa8888880000000000000000000000000000000000000000000000000000000000000000fffffffafffffafafffffffafffffafaffccffc8cc00c800aa88aa88880088000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [873, 930, 972, 979, 1266, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c79855_0 : P.sumLeaves 26 81771520 440 = 56543194 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79855) (lo := 0) (len := 440) (W := 56543194) check rows elimOK (by decide) (by decide) cover79855 (by decide)
  decide +kernel

theorem c79855_1 : P.sumLeaves 26 81771960 410 = 93620212 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79855) (lo := 440) (len := 410) (W := 93620212) check rows elimOK (by decide) (by decide) cover79855 (by decide)
  decide +kernel

theorem c79855_2 : P.sumLeaves 26 81772370 107 = 128931517 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79855) (lo := 850) (len := 107) (W := 128931517) check rows elimOK (by decide) (by decide) cover79855 (by decide)
  decide +kernel

theorem c79855_3 : P.sumLeaves 26 81772477 67 = 136507112 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79855) (lo := 957) (len := 67) (W := 136507112) check rows elimOK (by decide) (by decide) cover79855 (by decide)
  decide +kernel

theorem h79855 : P.leaf 36 79855 = 415602035 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(440, 56543194), (410, 93620212), (107, 128931517), (67, 136507112)]) (.cons c79855_0 (.cons c79855_1 (.cons c79855_2 (.cons c79855_3 (.nil))))) (by decide) (by decide))

theorem cover79870 : P.CoversSplit 26 10 79870 0xfffffffafffffafafffffffafffffafafffcfff8fffcc8c8aaa8aaa8aa888888fffffafafffffafaaaaaa0a0aaaaa0a0fffcfaf8fffcc8c8aaa8a0a0aa88808000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [873, 874, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c79870_0 : P.sumLeaves 26 81786880 716 = 141134918 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79870) (lo := 0) (len := 716) (W := 141134918) check rows elimOK (by decide) (by decide) cover79870 (by decide)
  decide +kernel

theorem c79870_1 : P.sumLeaves 26 81787596 155 = 200957372 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79870) (lo := 716) (len := 155) (W := 200957372) check rows elimOK (by decide) (by decide) cover79870 (by decide)
  decide +kernel

theorem c79870_2 : P.sumLeaves 26 81787751 108 = 319575784 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79870) (lo := 871) (len := 108) (W := 319575784) check rows elimOK (by decide) (by decide) cover79870 (by decide)
  decide +kernel

theorem c79870_3 : P.sumLeaves 26 81787859 45 = 214668856 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79870) (lo := 979) (len := 45) (W := 214668856) check rows elimOK (by decide) (by decide) cover79870 (by decide)
  decide +kernel

theorem h79870 : P.leaf 36 79870 = 876336930 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(716, 141134918), (155, 200957372), (108, 319575784), (45, 214668856)]) (.cons c79870_0 (.cons c79870_1 (.cons c79870_2 (.cons c79870_3 (.nil))))) (by decide) (by decide))

theorem cover79871 : P.CoversSplit 26 10 79871 0xfffffffafffffafafffffffafffffafafffcfff8fffcc8c8aaa8aaa8aa888888fffffafafffffafaaaaaaaaaaaaaaaaafffcfaf8fffcc8c8aaa8aaa8aa888888fffffffafffffafafffffffafffffafaffccffc8ccccc8c8aa88aa8888888888fffffafafffffafaaaaaaaaaaaaaaaaaffccfac8ccccc8c8aa88aa8888888888 :=
  coversSplit check rows (by decide) (by decide) (xs := [873, 930, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c79871_0 : P.sumLeaves 26 81787904 205 = 9012496 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79871) (lo := 0) (len := 205) (W := 9012496) check rows elimOK (by decide) (by decide) cover79871 (by decide)
  decide +kernel

theorem c79871_1 : P.sumLeaves 26 81788109 171 = 123667789 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79871) (lo := 205) (len := 171) (W := 123667789) check rows elimOK (by decide) (by decide) cover79871 (by decide)
  decide +kernel

theorem c79871_2 : P.sumLeaves 26 81788280 108 = 401010532 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79871) (lo := 376) (len := 108) (W := 401010532) check rows elimOK (by decide) (by decide) cover79871 (by decide)
  decide +kernel

theorem c79871_3 : P.sumLeaves 26 81788388 155 = 348241282 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79871) (lo := 484) (len := 155) (W := 348241282) check rows elimOK (by decide) (by decide) cover79871 (by decide)
  decide +kernel

theorem c79871_4 : P.sumLeaves 26 81788543 156 = 544677536 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79871) (lo := 639) (len := 156) (W := 544677536) check rows elimOK (by decide) (by decide) cover79871 (by decide)
  decide +kernel

theorem c79871_5 : P.sumLeaves 26 81788699 139 = 482637500 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79871) (lo := 795) (len := 139) (W := 482637500) check rows elimOK (by decide) (by decide) cover79871 (by decide)
  decide +kernel

theorem c79871_6 : P.sumLeaves 26 81788838 90 = 795453490 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 79871) (lo := 934) (len := 90) (W := 795453490) check rows elimOK (by decide) (by decide) cover79871 (by decide)
  decide +kernel

theorem h79871 : P.leaf 36 79871 = 2704700625 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(205, 9012496), (171, 123667789), (108, 401010532), (155, 348241282), (156, 544677536), (139, 482637500), (90, 795453490)]) (.cons c79871_0 (.cons c79871_1 (.cons c79871_2 (.cons c79871_3 (.cons c79871_4 (.cons c79871_5 (.cons c79871_6 (.nil)))))))) (by decide) (by decide))

theorem cover81150 : P.CoversSplit 26 10 81150 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000100000000002000010000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 580, 587, 629, 636, 930, 972, 1273, 1315, 1658]) (by decide +kernel)

theorem c81150_0 : P.sumLeaves 26 83097600 1024 = 408104 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81150) (lo := 0) (len := 1024) (W := 408104) check rows elimOK (by decide) (by decide) cover81150 (by decide)
  decide +kernel

theorem h81150 : P.leaf 36 81150 = 408104 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 408104)]) (.cons c81150_0 (.nil)) (by decide) (by decide))

theorem cover81151 : P.CoversSplit 26 10 81151 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000100000000002000010000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 580, 587, 629, 636, 930, 972, 1273, 1315, 1658]) (by decide +kernel)

theorem c81151_0 : P.sumLeaves 26 83098624 1024 = 454112 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81151) (lo := 0) (len := 1024) (W := 454112) check rows elimOK (by decide) (by decide) cover81151 (by decide)
  decide +kernel

theorem h81151 : P.leaf 36 81151 = 454112 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 454112)]) (.cons c81151_0 (.nil)) (by decide) (by decide))

theorem cover81260 : P.CoversSplit 26 10 81260 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 579, 580, 629, 636, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c81260_0 : P.sumLeaves 26 83210240 1024 = 176376 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81260) (lo := 0) (len := 1024) (W := 176376) check rows elimOK (by decide) (by decide) cover81260 (by decide)
  decide +kernel

theorem h81260 : P.leaf 36 81260 = 176376 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 176376)]) (.cons c81260_0 (.nil)) (by decide) (by decide))

theorem cover81261 : P.CoversSplit 26 10 81261 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 579, 580, 629, 636, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c81261_0 : P.sumLeaves 26 83211264 1024 = 180274 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81261) (lo := 0) (len := 1024) (W := 180274) check rows elimOK (by decide) (by decide) cover81261 (by decide)
  decide +kernel

theorem h81261 : P.leaf 36 81261 = 180274 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 180274)]) (.cons c81261_0 (.nil)) (by decide) (by decide))

theorem cover81262 : P.CoversSplit 26 10 81262 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 579, 580, 629, 636, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c81262_0 : P.sumLeaves 26 83212288 1024 = 877236 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81262) (lo := 0) (len := 1024) (W := 877236) check rows elimOK (by decide) (by decide) cover81262 (by decide)
  decide +kernel

theorem h81262 : P.leaf 36 81262 = 877236 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 877236)]) (.cons c81262_0 (.nil)) (by decide) (by decide))

theorem cover81263 : P.CoversSplit 26 10 81263 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 579, 580, 629, 636, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c81263_0 : P.sumLeaves 26 83213312 1024 = 910198 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81263) (lo := 0) (len := 1024) (W := 910198) check rows elimOK (by decide) (by decide) cover81263 (by decide)
  decide +kernel

theorem h81263 : P.leaf 36 81263 = 910198 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 910198)]) (.cons c81263_0 (.nil)) (by decide) (by decide))

theorem cover81278 : P.CoversSplit 26 10 81278 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 579, 580, 629, 636, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c81278_0 : P.sumLeaves 26 83228672 1024 = 3413757 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81278) (lo := 0) (len := 1024) (W := 3413757) check rows elimOK (by decide) (by decide) cover81278 (by decide)
  decide +kernel

theorem h81278 : P.leaf 36 81278 = 3413757 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 3413757)]) (.cons c81278_0 (.nil)) (by decide) (by decide))

theorem cover81279 : P.CoversSplit 26 10 81279 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 579, 580, 629, 636, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c81279_0 : P.sumLeaves 26 83229696 1024 = 3791700 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81279) (lo := 0) (len := 1024) (W := 3791700) check rows elimOK (by decide) (by decide) cover81279 (by decide)
  decide +kernel

theorem h81279 : P.leaf 36 81279 = 3791700 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 3791700)]) (.cons c81279_0 (.nil)) (by decide) (by decide))

theorem cover81335 : P.CoversSplit 26 10 81335 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000200000000001000010000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 482, 489, 538, 629, 636, 930, 972, 1315, 1658]) (by decide +kernel)

theorem c81335_0 : P.sumLeaves 26 83287040 1024 = 3173551 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81335) (lo := 0) (len := 1024) (W := 3173551) check rows elimOK (by decide) (by decide) cover81335 (by decide)
  decide +kernel

theorem h81335 : P.leaf 36 81335 = 3173551 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 3173551)]) (.cons c81335_0 (.nil)) (by decide) (by decide))

theorem cover81336 : P.CoversSplit 26 10 81336 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 481, 482, 531, 629, 636, 972, 979, 1273, 1315, 1658]) (by decide +kernel)

theorem c81336_0 : P.sumLeaves 26 83288064 1024 = 44100 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81336) (lo := 0) (len := 1024) (W := 44100) check rows elimOK (by decide) (by decide) cover81336 (by decide)
  decide +kernel

theorem h81336 : P.leaf 36 81336 = 44100 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 44100)]) (.cons c81336_0 (.nil)) (by decide) (by decide))

theorem cover81337 : P.CoversSplit 26 10 81337 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 481, 482, 531, 629, 636, 972, 979, 1273, 1315, 1658]) (by decide +kernel)

theorem c81337_0 : P.sumLeaves 26 83289088 1024 = 1577976 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81337) (lo := 0) (len := 1024) (W := 1577976) check rows elimOK (by decide) (by decide) cover81337 (by decide)
  decide +kernel

theorem h81337 : P.leaf 36 81337 = 1577976 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1577976)]) (.cons c81337_0 (.nil)) (by decide) (by decide))

theorem cover81339 : P.CoversSplit 26 10 81339 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 481, 482, 531, 629, 636, 972, 979, 1273, 1315, 1658]) (by decide +kernel)

theorem c81339_0 : P.sumLeaves 26 83291136 1024 = 3449824 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81339) (lo := 0) (len := 1024) (W := 3449824) check rows elimOK (by decide) (by decide) cover81339 (by decide)
  decide +kernel

theorem h81339 : P.leaf 36 81339 = 3449824 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 3449824)]) (.cons c81339_0 (.nil)) (by decide) (by decide))

theorem cover81340 : P.CoversSplit 26 10 81340 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 531, 538, 629, 636, 930, 972, 979, 1273, 1315, 1658]) (by decide +kernel)

theorem c81340_0 : P.sumLeaves 26 83292160 1024 = 1126320 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81340) (lo := 0) (len := 1024) (W := 1126320) check rows elimOK (by decide) (by decide) cover81340 (by decide)
  decide +kernel

theorem h81340 : P.leaf 36 81340 = 1126320 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1126320)]) (.cons c81340_0 (.nil)) (by decide) (by decide))

theorem cover81341 : P.CoversSplit 26 10 81341 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 531, 538, 629, 636, 930, 972, 979, 1273, 1315, 1658]) (by decide +kernel)

theorem c81341_0 : P.sumLeaves 26 83293184 1024 = 2555700 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81341) (lo := 0) (len := 1024) (W := 2555700) check rows elimOK (by decide) (by decide) cover81341 (by decide)
  decide +kernel

theorem h81341 : P.leaf 36 81341 = 2555700 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 2555700)]) (.cons c81341_0 (.nil)) (by decide) (by decide))

theorem cover81343 : P.CoversSplit 26 10 81343 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 531, 538, 629, 636, 972, 979, 1273, 1315, 1658]) (by decide +kernel)

theorem c81343_0 : P.sumLeaves 26 83295232 1024 = 5305160 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81343) (lo := 0) (len := 1024) (W := 5305160) check rows elimOK (by decide) (by decide) cover81343 (by decide)
  decide +kernel

theorem h81343 : P.leaf 36 81343 = 5305160 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 5305160)]) (.cons c81343_0 (.nil)) (by decide) (by decide))

theorem cover81353 : P.CoversSplit 26 10 81353 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 481, 482, 629, 636, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c81353_0 : P.sumLeaves 26 83305472 1024 = 100096 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81353) (lo := 0) (len := 1024) (W := 100096) check rows elimOK (by decide) (by decide) cover81353 (by decide)
  decide +kernel

theorem h81353 : P.leaf 36 81353 = 100096 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 100096)]) (.cons c81353_0 (.nil)) (by decide) (by decide))

theorem cover81355 : P.CoversSplit 26 10 81355 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 481, 482, 530, 629, 636, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c81355_0 : P.sumLeaves 26 83307520 1024 = 690848 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81355) (lo := 0) (len := 1024) (W := 690848) check rows elimOK (by decide) (by decide) cover81355 (by decide)
  decide +kernel

theorem h81355 : P.leaf 36 81355 = 690848 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 690848)]) (.cons c81355_0 (.nil)) (by decide) (by decide))

theorem cover81356 : P.CoversSplit 26 10 81356 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 629, 636, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c81356_0 : P.sumLeaves 26 83308544 1024 = 103584 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81356) (lo := 0) (len := 1024) (W := 103584) check rows elimOK (by decide) (by decide) cover81356 (by decide)
  decide +kernel

theorem h81356 : P.leaf 36 81356 = 103584 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 103584)]) (.cons c81356_0 (.nil)) (by decide) (by decide))

theorem cover81357 : P.CoversSplit 26 10 81357 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 629, 636, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c81357_0 : P.sumLeaves 26 83309568 1024 = 954792 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81357) (lo := 0) (len := 1024) (W := 954792) check rows elimOK (by decide) (by decide) cover81357 (by decide)
  decide +kernel

theorem h81357 : P.leaf 36 81357 = 954792 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 954792)]) (.cons c81357_0 (.nil)) (by decide) (by decide))

theorem cover81358 : P.CoversSplit 26 10 81358 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 629, 636, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c81358_0 : P.sumLeaves 26 83310592 1024 = 257136 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81358) (lo := 0) (len := 1024) (W := 257136) check rows elimOK (by decide) (by decide) cover81358 (by decide)
  decide +kernel

theorem h81358 : P.leaf 36 81358 = 257136 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 257136)]) (.cons c81358_0 (.nil)) (by decide) (by decide))

theorem cover81359 : P.CoversSplit 26 10 81359 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 629, 636, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c81359_0 : P.sumLeaves 26 83311616 1024 = 2337492 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81359) (lo := 0) (len := 1024) (W := 2337492) check rows elimOK (by decide) (by decide) cover81359 (by decide)
  decide +kernel

theorem h81359 : P.leaf 36 81359 = 2337492 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 2337492)]) (.cons c81359_0 (.nil)) (by decide) (by decide))

theorem cover81371 : P.CoversSplit 26 10 81371 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 481, 482, 629, 636, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c81371_0 : P.sumLeaves 26 83323904 1024 = 2984152 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81371) (lo := 0) (len := 1024) (W := 2984152) check rows elimOK (by decide) (by decide) cover81371 (by decide)
  decide +kernel

theorem h81371 : P.leaf 36 81371 = 2984152 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 2984152)]) (.cons c81371_0 (.nil)) (by decide) (by decide))

theorem cover81372 : P.CoversSplit 26 10 81372 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 629, 636, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c81372_0 : P.sumLeaves 26 83324928 1024 = 2038468 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81372) (lo := 0) (len := 1024) (W := 2038468) check rows elimOK (by decide) (by decide) cover81372 (by decide)
  decide +kernel

theorem h81372 : P.leaf 36 81372 = 2038468 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 2038468)]) (.cons c81372_0 (.nil)) (by decide) (by decide))

theorem cover81373 : P.CoversSplit 26 10 81373 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 629, 636, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c81373_0 : P.sumLeaves 26 83325952 1024 = 2587148 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81373) (lo := 0) (len := 1024) (W := 2587148) check rows elimOK (by decide) (by decide) cover81373 (by decide)
  decide +kernel

theorem h81373 : P.leaf 36 81373 = 2587148 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 2587148)]) (.cons c81373_0 (.nil)) (by decide) (by decide))

theorem cover81374 : P.CoversSplit 26 10 81374 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 629, 636, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c81374_0 : P.sumLeaves 26 83326976 1024 = 4274000 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81374) (lo := 0) (len := 1024) (W := 4274000) check rows elimOK (by decide) (by decide) cover81374 (by decide)
  decide +kernel

theorem h81374 : P.leaf 36 81374 = 4274000 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 4274000)]) (.cons c81374_0 (.nil)) (by decide) (by decide))

theorem cover81375 : P.CoversSplit 26 10 81375 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 530, 531, 629, 636, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c81375_0 : P.sumLeaves 26 83328000 1024 = 5435960 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81375) (lo := 0) (len := 1024) (W := 5435960) check rows elimOK (by decide) (by decide) cover81375 (by decide)
  decide +kernel

theorem h81375 : P.leaf 36 81375 = 5435960 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 5435960)]) (.cons c81375_0 (.nil)) (by decide) (by decide))

theorem cover81388 : P.CoversSplit 26 10 81388 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 923, 930, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c81388_0 : P.sumLeaves 26 83341312 1024 = 1545664 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81388) (lo := 0) (len := 1024) (W := 1545664) check rows elimOK (by decide) (by decide) cover81388 (by decide)
  decide +kernel

theorem h81388 : P.leaf 36 81388 = 1545664 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1545664)]) (.cons c81388_0 (.nil)) (by decide) (by decide))

theorem cover81389 : P.CoversSplit 26 10 81389 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 923, 930, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c81389_0 : P.sumLeaves 26 83342336 1024 = 1569322 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81389) (lo := 0) (len := 1024) (W := 1569322) check rows elimOK (by decide) (by decide) cover81389 (by decide)
  decide +kernel

theorem h81389 : P.leaf 36 81389 = 1569322 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1569322)]) (.cons c81389_0 (.nil)) (by decide) (by decide))

theorem cover81390 : P.CoversSplit 26 10 81390 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 923, 930, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c81390_0 : P.sumLeaves 26 83343360 1024 = 3412344 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81390) (lo := 0) (len := 1024) (W := 3412344) check rows elimOK (by decide) (by decide) cover81390 (by decide)
  decide +kernel

theorem h81390 : P.leaf 36 81390 = 3412344 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 3412344)]) (.cons c81390_0 (.nil)) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(79855, 720), (79870, 360), (79871, 360), (81150, 60), (81151, 60), (81260, 360), (81261, 360), (81262, 720), (81263, 720), (81278, 360), (81279, 360), (81335, 90), (81336, 360), (81337, 720), (81339, 360), (81340, 360), (81341, 720), (81343, 360), (81353, 180), (81355, 360), (81356, 720), (81357, 720), (81358, 720), (81359, 720), (81371, 180), (81372, 720), (81373, 720), (81374, 720), (81375, 720), (81388, 360), (81389, 360), (81390, 720)]

theorem segOK : checkSeg 20 perms 79855 81391 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 79855 81391 15330 1616636970870 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 1616636970870)
    (SegSum.cons (w := 720) h79855 (SegSum.cons (w := 360) h79870 (SegSum.cons (w := 360) h79871 (SegSum.cons (w := 60) h81150 (SegSum.cons (w := 60) h81151 (SegSum.cons (w := 360) h81260 (SegSum.cons (w := 360) h81261 (SegSum.cons (w := 720) h81262 (SegSum.cons (w := 720) h81263 (SegSum.cons (w := 360) h81278 (SegSum.cons (w := 360) h81279 (SegSum.cons (w := 90) h81335 (SegSum.cons (w := 360) h81336 (SegSum.cons (w := 720) h81337 (SegSum.cons (w := 360) h81339 (SegSum.cons (w := 360) h81340 (SegSum.cons (w := 720) h81341 (SegSum.cons (w := 360) h81343 (SegSum.cons (w := 180) h81353 (SegSum.cons (w := 360) h81355 (SegSum.cons (w := 720) h81356 (SegSum.cons (w := 720) h81357 (SegSum.cons (w := 720) h81358 (SegSum.cons (w := 720) h81359 (SegSum.cons (w := 180) h81371 (SegSum.cons (w := 720) h81372 (SegSum.cons (w := 720) h81373 (SegSum.cons (w := 720) h81374 (SegSum.cons (w := 720) h81375 (SegSum.cons (w := 360) h81388 (SegSum.cons (w := 360) h81389 (SegSum.cons (w := 720) h81390 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S56
