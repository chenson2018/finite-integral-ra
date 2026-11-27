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

namespace RACert.S6N0.C0.S15

open RACert RACert.Problem

theorem cover8093 : P.CoversSplit 26 10 8093 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c8093_0 : P.sumLeaves 26 8287232 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 8093) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover8093 (by decide)
  decide +kernel

theorem h8093 : P.leaf 36 8093 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c8093_0 (.nil)) (by decide) (by decide))

theorem cover8094 : P.CoversSplit 26 10 8094 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c8094_0 : P.sumLeaves 26 8288256 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 8094) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover8094 (by decide)
  decide +kernel

theorem h8094 : P.leaf 36 8094 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c8094_0 (.nil)) (by decide) (by decide))

theorem cover8095 : P.CoversSplit 26 10 8095 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c8095_0 : P.sumLeaves 26 8289280 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 8095) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover8095 (by decide)
  decide +kernel

theorem h8095 : P.leaf 36 8095 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c8095_0 (.nil)) (by decide) (by decide))

theorem cover8118 : P.CoversSplit 26 10 8118 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c8118_0 : P.sumLeaves 26 8312832 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 8118) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover8118 (by decide)
  decide +kernel

theorem h8118 : P.leaf 36 8118 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c8118_0 (.nil)) (by decide) (by decide))

theorem cover8119 : P.CoversSplit 26 10 8119 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [923]) (by decide +kernel)

theorem c8119_0 : P.sumLeaves 26 8313856 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 8119) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover8119 (by decide)
  decide +kernel

theorem h8119 : P.leaf 36 8119 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c8119_0 (.nil)) (by decide) (by decide))

theorem cover8122 : P.CoversSplit 26 10 8122 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [929]) (by decide +kernel)

theorem c8122_0 : P.sumLeaves 26 8316928 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 8122) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover8122 (by decide)
  decide +kernel

theorem h8122 : P.leaf 36 8122 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c8122_0 (.nil)) (by decide) (by decide))

theorem cover8123 : P.CoversSplit 26 10 8123 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [929]) (by decide +kernel)

theorem c8123_0 : P.sumLeaves 26 8317952 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 8123) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover8123 (by decide)
  decide +kernel

theorem h8123 : P.leaf 36 8123 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c8123_0 (.nil)) (by decide) (by decide))

theorem cover8126 : P.CoversSplit 26 10 8126 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c8126_0 : P.sumLeaves 26 8321024 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 8126) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover8126 (by decide)
  decide +kernel

theorem h8126 : P.leaf 36 8126 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c8126_0 (.nil)) (by decide) (by decide))

theorem cover8127 : P.CoversSplit 26 10 8127 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c8127_0 : P.sumLeaves 26 8322048 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 8127) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover8127 (by decide)
  decide +kernel

theorem h8127 : P.leaf 36 8127 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c8127_0 (.nil)) (by decide) (by decide))

theorem cover8190 : P.CoversSplit 26 10 8190 0xfffffffafffcfac8fffffafafffcfac8fffffffaffccfac88888888888888888fffffafafffcfac8aaaaaaaaaaa8aa88fffffafaffccfac88888888888888888fffffffaffccfac8fffffafaffccfac8ccccccc8ccccc8c888888888888888880000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [874, 922, 930, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c8190_0 : P.sumLeaves 26 8386560 455 = 65742100 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 8190) (lo := 0) (len := 455) (W := 65742100) check rows elimOK (by decide) (by decide) cover8190 (by decide)
  decide +kernel

theorem c8190_1 : P.sumLeaves 26 8387015 167 = 100862224 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 8190) (lo := 455) (len := 167) (W := 100862224) check rows elimOK (by decide) (by decide) cover8190 (by decide)
  decide +kernel

theorem c8190_2 : P.sumLeaves 26 8387182 144 = 105665500 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 8190) (lo := 622) (len := 144) (W := 105665500) check rows elimOK (by decide) (by decide) cover8190 (by decide)
  decide +kernel

theorem c8190_3 : P.sumLeaves 26 8387326 168 = 99184028 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 8190) (lo := 766) (len := 168) (W := 99184028) check rows elimOK (by decide) (by decide) cover8190 (by decide)
  decide +kernel

theorem c8190_4 : P.sumLeaves 26 8387494 90 = 168322672 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 8190) (lo := 934) (len := 90) (W := 168322672) check rows elimOK (by decide) (by decide) cover8190 (by decide)
  decide +kernel

theorem h8190 : P.leaf 36 8190 = 539776524 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(455, 65742100), (167, 100862224), (144, 105665500), (168, 99184028), (90, 168322672)]) (.cons c8190_0 (.cons c8190_1 (.cons c8190_2 (.cons c8190_3 (.cons c8190_4 (.nil)))))) (by decide) (by decide))

theorem cover8191 : P.CoversSplit 26 10 8191 0xfffffffafffcfac8fffffafafffcfac8fffffffaffccfac88888888888888888fffffafafffcfac8aaaaaaaaaaa8aa88fffffafaffccfac88888888888888888fffffffaffccfac8fffffafaffccfac8ccccccc8ccccc8c88888888888888888fffffafaffccfac8aaaaaaaaaa88aa88ccccc8c8ccccc8c88888888888888888 :=
  coversSplit check rows (by decide) (by decide) (xs := [922, 930, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c8191_0 : P.sumLeaves 26 8387584 229 = 8777161 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 8191) (lo := 0) (len := 229) (W := 8777161) check rows elimOK (by decide) (by decide) cover8191 (by decide)
  decide +kernel

theorem c8191_1 : P.sumLeaves 26 8387813 194 = 141592456 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 8191) (lo := 229) (len := 194) (W := 141592456) check rows elimOK (by decide) (by decide) cover8191 (by decide)
  decide +kernel

theorem c8191_2 : P.sumLeaves 26 8388007 166 = 302202952 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 8191) (lo := 423) (len := 166) (W := 302202952) check rows elimOK (by decide) (by decide) cover8191 (by decide)
  decide +kernel

theorem c8191_3 : P.sumLeaves 26 8388173 150 = 244231568 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 8191) (lo := 589) (len := 150) (W := 244231568) check rows elimOK (by decide) (by decide) cover8191 (by decide)
  decide +kernel

theorem c8191_4 : P.sumLeaves 26 8388323 164 = 309458308 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 8191) (lo := 739) (len := 164) (W := 309458308) check rows elimOK (by decide) (by decide) cover8191 (by decide)
  decide +kernel

theorem c8191_5 : P.sumLeaves 26 8388487 115 = 441949128 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 8191) (lo := 903) (len := 115) (W := 441949128) check rows elimOK (by decide) (by decide) cover8191 (by decide)
  decide +kernel

theorem c8191_6 : P.sumLeaves 26 8388602 6 = 55793620 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 8191) (lo := 1018) (len := 6) (W := 55793620) check rows elimOK (by decide) (by decide) cover8191 (by decide)
  decide +kernel

theorem h8191 : P.leaf 36 8191 = 1504005193 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(229, 8777161), (194, 141592456), (166, 302202952), (150, 244231568), (164, 309458308), (115, 441949128), (6, 55793620)]) (.cons c8191_0 (.cons c8191_1 (.cons c8191_2 (.cons c8191_3 (.cons c8191_4 (.cons c8191_5 (.cons c8191_6 (.nil)))))))) (by decide) (by decide))

theorem cover11443 : P.CoversSplit 26 10 11443 0x8000000000000000000000000000000000000000000000000000000000000000cc00cc0000000000cc00c800000000000000000000000000000000000000000000000000000000000000000000000000000000000033003300000000003300320000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 538, 587, 629, 636, 881, 972, 1315, 1658, 2008]) (by decide +kernel)

theorem c11443_0 : P.sumLeaves 26 11717632 1024 = 15481888 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 11443) (lo := 0) (len := 1024) (W := 15481888) check rows elimOK (by decide) (by decide) cover11443 (by decide)
  decide +kernel

theorem h11443 : P.leaf 36 11443 = 15481888 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 15481888)]) (.cons c11443_0 (.nil)) (by decide) (by decide))

theorem cover11447 : P.CoversSplit 26 10 11447 0x8000000000000000000000000000000000000000000000000000000000000000cc00cc0000000000cc00c800000000000000000000000000000000000000000000000000000000000000000000000000000000000033003300000000003300320000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 538, 587, 629, 636, 881, 972, 1265, 1315, 1658, 2008]) (by decide +kernel)

theorem c11447_0 : P.sumLeaves 26 11721728 1024 = 33668760 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 11447) (lo := 0) (len := 1024) (W := 33668760) check rows elimOK (by decide) (by decide) cover11447 (by decide)
  decide +kernel

theorem h11447 : P.leaf 36 11447 = 33668760 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 33668760)]) (.cons c11447_0 (.nil)) (by decide) (by decide))

theorem cover11448 : P.CoversSplit 26 10 11448 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000021002100000000002100200000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 531, 538, 587, 629, 636, 881, 972, 1265, 1273, 1315, 1658]) (by decide +kernel)

theorem c11448_0 : P.sumLeaves 26 11722752 1024 = 6575 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 11448) (lo := 0) (len := 1024) (W := 6575) check rows elimOK (by decide) (by decide) cover11448 (by decide)
  decide +kernel

theorem h11448 : P.leaf 36 11448 = 6575 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 6575)]) (.cons c11448_0 (.nil)) (by decide) (by decide))

theorem cover11449 : P.CoversSplit 26 10 11449 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000021002100000000002100200000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 531, 538, 587, 629, 636, 881, 972, 1265, 1315, 1658]) (by decide +kernel)

theorem c11449_0 : P.sumLeaves 26 11723776 1024 = 9812 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 11449) (lo := 0) (len := 1024) (W := 9812) check rows elimOK (by decide) (by decide) cover11449 (by decide)
  decide +kernel

theorem h11449 : P.leaf 36 11449 = 9812 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 9812)]) (.cons c11449_0 (.nil)) (by decide) (by decide))

theorem cover11451 : P.CoversSplit 26 10 11451 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000021002100000000002100200000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 531, 538, 587, 629, 636, 881, 972, 1265, 1315, 1658]) (by decide +kernel)

theorem c11451_0 : P.sumLeaves 26 11725824 1024 = 18106 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 11451) (lo := 0) (len := 1024) (W := 18106) check rows elimOK (by decide) (by decide) cover11451 (by decide)
  decide +kernel

theorem h11451 : P.leaf 36 11451 = 18106 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 18106)]) (.cons c11451_0 (.nil)) (by decide) (by decide))

theorem cover11455 : P.CoversSplit 26 10 11455 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000021002100000000002100200000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 531, 538, 587, 629, 636, 881, 972, 1265, 1315, 1658]) (by decide +kernel)

theorem c11455_0 : P.sumLeaves 26 11729920 1024 = 42574 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 11455) (lo := 0) (len := 1024) (W := 42574) check rows elimOK (by decide) (by decide) cover11455 (by decide)
  decide +kernel

theorem h11455 : P.leaf 36 11455 = 42574 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 42574)]) (.cons c11455_0 (.nil)) (by decide) (by decide))

theorem cover11458 : P.CoversSplit 26 10 11458 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [482]) (by decide +kernel)

theorem c11458_0 : P.sumLeaves 26 11732992 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 11458) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover11458 (by decide)
  decide +kernel

theorem h11458 : P.leaf 36 11458 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c11458_0 (.nil)) (by decide) (by decide))

theorem cover11459 : P.CoversSplit 26 10 11459 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [482]) (by decide +kernel)

theorem c11459_0 : P.sumLeaves 26 11734016 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 11459) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover11459 (by decide)
  decide +kernel

theorem h11459 : P.leaf 36 11459 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c11459_0 (.nil)) (by decide) (by decide))

theorem cover11462 : P.CoversSplit 26 10 11462 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c11462_0 : P.sumLeaves 26 11737088 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 11462) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover11462 (by decide)
  decide +kernel

theorem h11462 : P.leaf 36 11462 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c11462_0 (.nil)) (by decide) (by decide))

theorem cover11463 : P.CoversSplit 26 10 11463 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c11463_0 : P.sumLeaves 26 11738112 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 11463) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover11463 (by decide)
  decide +kernel

theorem h11463 : P.leaf 36 11463 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c11463_0 (.nil)) (by decide) (by decide))

theorem cover11464 : P.CoversSplit 26 10 11464 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c11464_0 : P.sumLeaves 26 11739136 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 11464) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover11464 (by decide)
  decide +kernel

theorem h11464 : P.leaf 36 11464 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c11464_0 (.nil)) (by decide) (by decide))

theorem cover11465 : P.CoversSplit 26 10 11465 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c11465_0 : P.sumLeaves 26 11740160 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 11465) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover11465 (by decide)
  decide +kernel

theorem h11465 : P.leaf 36 11465 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c11465_0 (.nil)) (by decide) (by decide))

theorem cover11466 : P.CoversSplit 26 10 11466 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c11466_0 : P.sumLeaves 26 11741184 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 11466) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover11466 (by decide)
  decide +kernel

theorem h11466 : P.leaf 36 11466 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c11466_0 (.nil)) (by decide) (by decide))

theorem cover11467 : P.CoversSplit 26 10 11467 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c11467_0 : P.sumLeaves 26 11742208 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 11467) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover11467 (by decide)
  decide +kernel

theorem h11467 : P.leaf 36 11467 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c11467_0 (.nil)) (by decide) (by decide))

theorem cover11470 : P.CoversSplit 26 10 11470 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c11470_0 : P.sumLeaves 26 11745280 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 11470) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover11470 (by decide)
  decide +kernel

theorem h11470 : P.leaf 36 11470 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c11470_0 (.nil)) (by decide) (by decide))

theorem cover11471 : P.CoversSplit 26 10 11471 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c11471_0 : P.sumLeaves 26 11746304 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 11471) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover11471 (by decide)
  decide +kernel

theorem h11471 : P.leaf 36 11471 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c11471_0 (.nil)) (by decide) (by decide))

theorem cover11475 : P.CoversSplit 26 10 11475 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [482]) (by decide +kernel)

theorem c11475_0 : P.sumLeaves 26 11750400 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 11475) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover11475 (by decide)
  decide +kernel

theorem h11475 : P.leaf 36 11475 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c11475_0 (.nil)) (by decide) (by decide))

theorem cover11476 : P.CoversSplit 26 10 11476 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [475]) (by decide +kernel)

theorem c11476_0 : P.sumLeaves 26 11751424 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 11476) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover11476 (by decide)
  decide +kernel

theorem h11476 : P.leaf 36 11476 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c11476_0 (.nil)) (by decide) (by decide))

theorem cover11477 : P.CoversSplit 26 10 11477 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [475]) (by decide +kernel)

theorem c11477_0 : P.sumLeaves 26 11752448 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 11477) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover11477 (by decide)
  decide +kernel

theorem h11477 : P.leaf 36 11477 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c11477_0 (.nil)) (by decide) (by decide))

theorem cover11478 : P.CoversSplit 26 10 11478 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c11478_0 : P.sumLeaves 26 11753472 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 11478) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover11478 (by decide)
  decide +kernel

theorem h11478 : P.leaf 36 11478 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c11478_0 (.nil)) (by decide) (by decide))

theorem cover11479 : P.CoversSplit 26 10 11479 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c11479_0 : P.sumLeaves 26 11754496 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 11479) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover11479 (by decide)
  decide +kernel

theorem h11479 : P.leaf 36 11479 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c11479_0 (.nil)) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(8093, 360), (8094, 360), (8095, 360), (8118, 180), (8119, 180), (8122, 360), (8123, 360), (8126, 360), (8127, 360), (8190, 60), (8191, 60), (11443, 90), (11447, 60), (11448, 60), (11449, 180), (11451, 180), (11455, 60), (11458, 360), (11459, 720), (11462, 360), (11463, 360), (11464, 360), (11465, 360), (11466, 720), (11467, 720), (11470, 360), (11471, 360), (11475, 360), (11476, 360), (11477, 720), (11478, 720), (11479, 720)]

theorem segOK : checkSeg 20 perms 8093 11480 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 8093 11480 11190 126048372720 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 126048372720)
    (SegSum.cons (w := 360) h8093 (SegSum.cons (w := 360) h8094 (SegSum.cons (w := 360) h8095 (SegSum.cons (w := 180) h8118 (SegSum.cons (w := 180) h8119 (SegSum.cons (w := 360) h8122 (SegSum.cons (w := 360) h8123 (SegSum.cons (w := 360) h8126 (SegSum.cons (w := 360) h8127 (SegSum.cons (w := 60) h8190 (SegSum.cons (w := 60) h8191 (SegSum.cons (w := 90) h11443 (SegSum.cons (w := 60) h11447 (SegSum.cons (w := 60) h11448 (SegSum.cons (w := 180) h11449 (SegSum.cons (w := 180) h11451 (SegSum.cons (w := 60) h11455 (SegSum.cons (w := 360) h11458 (SegSum.cons (w := 720) h11459 (SegSum.cons (w := 360) h11462 (SegSum.cons (w := 360) h11463 (SegSum.cons (w := 360) h11464 (SegSum.cons (w := 360) h11465 (SegSum.cons (w := 720) h11466 (SegSum.cons (w := 720) h11467 (SegSum.cons (w := 360) h11470 (SegSum.cons (w := 360) h11471 (SegSum.cons (w := 360) h11475 (SegSum.cons (w := 360) h11476 (SegSum.cons (w := 720) h11477 (SegSum.cons (w := 720) h11478 (SegSum.cons (w := 720) h11479 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S15
