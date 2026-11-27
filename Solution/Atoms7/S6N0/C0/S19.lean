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

namespace RACert.S6N0.C0.S19

open RACert RACert.Problem

theorem cover12146 : P.CoversSplit 26 10 12146 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c12146_0 : P.sumLeaves 26 12437504 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12146) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12146 (by decide)
  decide +kernel

theorem h12146 : P.leaf 36 12146 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12146_0 (.nil)) (by decide) (by decide))

theorem cover12147 : P.CoversSplit 26 10 12147 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c12147_0 : P.sumLeaves 26 12438528 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12147) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12147 (by decide)
  decide +kernel

theorem h12147 : P.leaf 36 12147 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12147_0 (.nil)) (by decide) (by decide))

theorem cover12150 : P.CoversSplit 26 10 12150 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c12150_0 : P.sumLeaves 26 12441600 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12150) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12150 (by decide)
  decide +kernel

theorem h12150 : P.leaf 36 12150 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12150_0 (.nil)) (by decide) (by decide))

theorem cover12151 : P.CoversSplit 26 10 12151 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c12151_0 : P.sumLeaves 26 12442624 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12151) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12151 (by decide)
  decide +kernel

theorem h12151 : P.leaf 36 12151 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12151_0 (.nil)) (by decide) (by decide))

theorem cover12152 : P.CoversSplit 26 10 12152 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c12152_0 : P.sumLeaves 26 12443648 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12152) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12152 (by decide)
  decide +kernel

theorem h12152 : P.leaf 36 12152 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12152_0 (.nil)) (by decide) (by decide))

theorem cover12153 : P.CoversSplit 26 10 12153 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c12153_0 : P.sumLeaves 26 12444672 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12153) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12153 (by decide)
  decide +kernel

theorem h12153 : P.leaf 36 12153 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12153_0 (.nil)) (by decide) (by decide))

theorem cover12154 : P.CoversSplit 26 10 12154 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c12154_0 : P.sumLeaves 26 12445696 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12154) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12154 (by decide)
  decide +kernel

theorem h12154 : P.leaf 36 12154 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12154_0 (.nil)) (by decide) (by decide))

theorem cover12155 : P.CoversSplit 26 10 12155 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c12155_0 : P.sumLeaves 26 12446720 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12155) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12155 (by decide)
  decide +kernel

theorem h12155 : P.leaf 36 12155 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12155_0 (.nil)) (by decide) (by decide))

theorem cover12158 : P.CoversSplit 26 10 12158 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c12158_0 : P.sumLeaves 26 12449792 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12158) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12158 (by decide)
  decide +kernel

theorem h12158 : P.leaf 36 12158 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12158_0 (.nil)) (by decide) (by decide))

theorem cover12159 : P.CoversSplit 26 10 12159 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c12159_0 : P.sumLeaves 26 12450816 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12159) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12159 (by decide)
  decide +kernel

theorem h12159 : P.leaf 36 12159 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12159_0 (.nil)) (by decide) (by decide))

theorem cover12272 : P.CoversSplit 26 10 12272 0xf000f00000000000f000f0000000000000000000000000000000000000000000fa00aa0000000000aa00aa0000000000000000000000000000000000000000000000000000000000000000000000000000000000f000a00000000000a000a0000000000000000000000000000000000000000000fa00aa0000000000aa00aa00 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 510, 881, 930, 972, 979, 1315, 1658]) (by decide +kernel)

theorem c12272_0 : P.sumLeaves 26 12566528 1024 = 43688 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12272) (lo := 0) (len := 1024) (W := 43688) check rows elimOK (by decide) (by decide) cover12272 (by decide)
  decide +kernel

theorem h12272 : P.leaf 36 12272 = 43688 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 43688)]) (.cons c12272_0 (.nil)) (by decide) (by decide))

theorem cover12273 : P.CoversSplit 26 10 12273 0xc000c00000000000c000c0000000000000000000000000000000000000000000cc0088000000000088008800000000000000000000000000000000000000000000000000000000000000000000000000000000003000200000000000200020000000000000000000000000000000000000000000330022000000000022002200 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 559, 881, 930, 972, 979, 1315, 1658]) (by decide +kernel)

theorem c12273_0 : P.sumLeaves 26 12567552 1024 = 282062 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12273) (lo := 0) (len := 1024) (W := 282062) check rows elimOK (by decide) (by decide) cover12273 (by decide)
  decide +kernel

theorem h12273 : P.leaf 36 12273 = 282062 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 282062)]) (.cons c12273_0 (.nil)) (by decide) (by decide))

theorem cover12275 : P.CoversSplit 26 10 12275 0xc000c00000000000c000c0000000000000000000000000000000000000000000cc0088000000000088008800000000000000000000000000000000000000000000000000000000000000000000000000000000003000200000000000200020000000000000000000000000000000000000000000330022000000000022002200 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 608, 881, 930, 972, 979, 1315, 1658]) (by decide +kernel)

theorem c12275_0 : P.sumLeaves 26 12569600 1024 = 1030864 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12275) (lo := 0) (len := 1024) (W := 1030864) check rows elimOK (by decide) (by decide) cover12275 (by decide)
  decide +kernel

theorem h12275 : P.leaf 36 12275 = 1030864 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1030864)]) (.cons c12275_0 (.nil)) (by decide) (by decide))

theorem cover12279 : P.CoversSplit 26 10 12279 0xcc00cc0000000000cc00c8000000000000000000000000000000000000000000c00080000000000080008000000000000000000000000000000000000000000000000000000000000000000000000000000000003300220000000000220022000000000000000000000000000000000000000000300020000000000020002000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 881, 930, 972, 979, 1265, 1273, 1315, 1658]) (by decide +kernel)

theorem c12279_0 : P.sumLeaves 26 12573696 1024 = 4892912 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12279) (lo := 0) (len := 1024) (W := 4892912) check rows elimOK (by decide) (by decide) cover12279 (by decide)
  decide +kernel

theorem h12279 : P.leaf 36 12279 = 4892912 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 4892912)]) (.cons c12279_0 (.nil)) (by decide) (by decide))

theorem cover12280 : P.CoversSplit 26 10 12280 0xf0f5f0f5f0f5a080f0f5f0f0f0f5a080f0f5f0f5f0c0a080a080a080a080a0800000000000000000000000000000000000000000000000000000000000000000f0f5f0f5f0c4a080f0f5f0f0f0c4a080f0c4f0c4f000a000a080a080a000a0000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 874, 881, 972, 979, 1265, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c12280_0 : P.sumLeaves 26 12574720 815 = 685793 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12280) (lo := 0) (len := 815) (W := 685793) check rows elimOK (by decide) (by decide) cover12280 (by decide)
  decide +kernel

theorem c12280_1 : P.sumLeaves 26 12575535 208 = 1321314 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12280) (lo := 815) (len := 208) (W := 1321314) check rows elimOK (by decide) (by decide) cover12280 (by decide)
  decide +kernel

theorem c12280_2 : P.sumLeaves 26 12575743 1 = 69440 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12280) (lo := 1023) (len := 1) (W := 69440) check rows elimOK (by decide) (by decide) cover12280 (by decide)
  decide +kernel

theorem h12280 : P.leaf 36 12280 = 2076547 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(815, 685793), (208, 1321314), (1, 69440)]) (.cons c12280_0 (.cons c12280_1 (.cons c12280_2 (.nil)))) (by decide) (by decide))

theorem cover12281 : P.CoversSplit 26 10 12281 0xf0f5f0f5f0f5a080f0f5f0f0f0f5a080f0f5f0f5f0c0a080a080a080a080a0800000000000000000000000000000000000000000000000000000000000000000f0f5f0f5f0c4a080f0f5f0f0f0c4a080f0c4f0c4f000a000a080a080a000a0000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 881, 923, 930, 972, 979, 1265, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c12281_0 : P.sumLeaves 26 12575744 815 = 5846596 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12281) (lo := 0) (len := 815) (W := 5846596) check rows elimOK (by decide) (by decide) cover12281 (by decide)
  decide +kernel

theorem c12281_1 : P.sumLeaves 26 12576559 208 = 8919110 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12281) (lo := 815) (len := 208) (W := 8919110) check rows elimOK (by decide) (by decide) cover12281 (by decide)
  decide +kernel

theorem c12281_2 : P.sumLeaves 26 12576767 1 = 341236 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12281) (lo := 1023) (len := 1) (W := 341236) check rows elimOK (by decide) (by decide) cover12281 (by decide)
  decide +kernel

theorem h12281 : P.leaf 36 12281 = 15106942 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(815, 5846596), (208, 8919110), (1, 341236)]) (.cons c12281_0 (.cons c12281_1 (.cons c12281_2 (.nil)))) (by decide) (by decide))

theorem cover12283 : P.CoversSplit 26 10 12283 0xf0f5f0f5f0f5a080f0f5f0f0f0f5a080f0f5f0f5f0c0a080a080a080a080a0805555000055550000000000000000000055550000554000000000000000000000f0f5f0f5f0c4a080f0f5f0f0f0c4a080f0c4f0c4f000a000a080a080a000a0005555000055440000000000000000000055440000550000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 881, 972, 979, 1265, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c12283_0 : P.sumLeaves 26 12577792 486 = 13695194 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12283) (lo := 0) (len := 486) (W := 13695194) check rows elimOK (by decide) (by decide) cover12283 (by decide)
  decide +kernel

theorem c12283_1 : P.sumLeaves 26 12578278 439 = 26441690 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12283) (lo := 486) (len := 439) (W := 26441690) check rows elimOK (by decide) (by decide) cover12283 (by decide)
  decide +kernel

theorem c12283_2 : P.sumLeaves 26 12578717 99 = 27955512 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12283) (lo := 925) (len := 99) (W := 27955512) check rows elimOK (by decide) (by decide) cover12283 (by decide)
  decide +kernel

theorem h12283 : P.leaf 36 12283 = 68092396 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(486, 13695194), (439, 26441690), (99, 27955512)]) (.cons c12283_0 (.cons c12283_1 (.cons c12283_2 (.nil)))) (by decide) (by decide))

theorem cover12287 : P.CoversSplit 26 10 12287 0xfffafffafffaaa88fffafafafffaaa88fffafffaffc8aa88aa88aa88aa88aa88fafaaaaafafaaa88aaaaaaaaaaaaaa88fafaaaaafac8aa88aa88aa88aa88aa88fffafffaffc8aa88fffafafaffc8aa88ffc8ffc8ffc8aa88aa88aa88aa88aa88fafaaaaafac8aa88aaaaaaaaaa88aa88fac8aa88fac8aa88aa88aa88aa88aa88 :=
  coversSplit check rows (by decide) (by decide) (xs := [881, 972, 979, 1265, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c12287_0 : P.sumLeaves 26 12581888 223 = 9664512 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12287) (lo := 0) (len := 223) (W := 9664512) check rows elimOK (by decide) (by decide) cover12287 (by decide)
  decide +kernel

theorem c12287_1 : P.sumLeaves 26 12582111 188 = 105487241 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12287) (lo := 223) (len := 188) (W := 105487241) check rows elimOK (by decide) (by decide) cover12287 (by decide)
  decide +kernel

theorem c12287_2 : P.sumLeaves 26 12582299 158 = 255166936 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12287) (lo := 411) (len := 158) (W := 255166936) check rows elimOK (by decide) (by decide) cover12287 (by decide)
  decide +kernel

theorem c12287_3 : P.sumLeaves 26 12582457 186 = 263555096 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12287) (lo := 569) (len := 186) (W := 263555096) check rows elimOK (by decide) (by decide) cover12287 (by decide)
  decide +kernel

theorem c12287_4 : P.sumLeaves 26 12582643 169 = 243511274 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12287) (lo := 755) (len := 169) (W := 243511274) check rows elimOK (by decide) (by decide) cover12287 (by decide)
  decide +kernel

theorem c12287_5 : P.sumLeaves 26 12582812 100 = 398905448 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12287) (lo := 924) (len := 100) (W := 398905448) check rows elimOK (by decide) (by decide) cover12287 (by decide)
  decide +kernel

theorem h12287 : P.leaf 36 12287 = 1276290507 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(223, 9664512), (188, 105487241), (158, 255166936), (186, 263555096), (169, 243511274), (100, 398905448)]) (.cons c12287_0 (.cons c12287_1 (.cons c12287_2 (.cons c12287_3 (.cons c12287_4 (.cons c12287_5 (.nil))))))) (by decide) (by decide))

theorem cover12486 : P.CoversSplit 26 10 12486 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c12486_0 : P.sumLeaves 26 12785664 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12486) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12486 (by decide)
  decide +kernel

theorem h12486 : P.leaf 36 12486 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12486_0 (.nil)) (by decide) (by decide))

theorem cover12487 : P.CoversSplit 26 10 12487 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c12487_0 : P.sumLeaves 26 12786688 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12487) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12487 (by decide)
  decide +kernel

theorem h12487 : P.leaf 36 12487 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12487_0 (.nil)) (by decide) (by decide))

theorem cover12495 : P.CoversSplit 26 10 12495 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c12495_0 : P.sumLeaves 26 12794880 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12495) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12495 (by decide)
  decide +kernel

theorem h12495 : P.leaf 36 12495 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12495_0 (.nil)) (by decide) (by decide))

theorem cover12502 : P.CoversSplit 26 10 12502 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c12502_0 : P.sumLeaves 26 12802048 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12502) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12502 (by decide)
  decide +kernel

theorem h12502 : P.leaf 36 12502 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12502_0 (.nil)) (by decide) (by decide))

theorem cover12503 : P.CoversSplit 26 10 12503 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c12503_0 : P.sumLeaves 26 12803072 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12503) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12503 (by decide)
  decide +kernel

theorem h12503 : P.leaf 36 12503 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12503_0 (.nil)) (by decide) (by decide))

theorem cover12508 : P.CoversSplit 26 10 12508 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c12508_0 : P.sumLeaves 26 12808192 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12508) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12508 (by decide)
  decide +kernel

theorem h12508 : P.leaf 36 12508 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12508_0 (.nil)) (by decide) (by decide))

theorem cover12509 : P.CoversSplit 26 10 12509 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c12509_0 : P.sumLeaves 26 12809216 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12509) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12509 (by decide)
  decide +kernel

theorem h12509 : P.leaf 36 12509 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12509_0 (.nil)) (by decide) (by decide))

theorem cover12511 : P.CoversSplit 26 10 12511 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c12511_0 : P.sumLeaves 26 12811264 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12511) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12511 (by decide)
  decide +kernel

theorem h12511 : P.leaf 36 12511 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12511_0 (.nil)) (by decide) (by decide))

theorem cover12534 : P.CoversSplit 26 10 12534 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c12534_0 : P.sumLeaves 26 12834816 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12534) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12534 (by decide)
  decide +kernel

theorem h12534 : P.leaf 36 12534 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12534_0 (.nil)) (by decide) (by decide))

theorem cover12535 : P.CoversSplit 26 10 12535 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c12535_0 : P.sumLeaves 26 12835840 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12535) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12535 (by decide)
  decide +kernel

theorem h12535 : P.leaf 36 12535 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12535_0 (.nil)) (by decide) (by decide))

theorem cover12536 : P.CoversSplit 26 10 12536 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c12536_0 : P.sumLeaves 26 12836864 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12536) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12536 (by decide)
  decide +kernel

theorem h12536 : P.leaf 36 12536 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12536_0 (.nil)) (by decide) (by decide))

theorem cover12537 : P.CoversSplit 26 10 12537 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c12537_0 : P.sumLeaves 26 12837888 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12537) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12537 (by decide)
  decide +kernel

theorem h12537 : P.leaf 36 12537 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12537_0 (.nil)) (by decide) (by decide))

theorem cover12538 : P.CoversSplit 26 10 12538 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c12538_0 : P.sumLeaves 26 12838912 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12538) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12538 (by decide)
  decide +kernel

theorem h12538 : P.leaf 36 12538 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12538_0 (.nil)) (by decide) (by decide))

theorem cover12539 : P.CoversSplit 26 10 12539 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [1266]) (by decide +kernel)

theorem c12539_0 : P.sumLeaves 26 12839936 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 12539) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover12539 (by decide)
  decide +kernel

theorem h12539 : P.leaf 36 12539 = 0 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c12539_0 (.nil)) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(12146, 720), (12147, 720), (12150, 360), (12151, 360), (12152, 360), (12153, 360), (12154, 720), (12155, 720), (12158, 360), (12159, 360), (12272, 120), (12273, 360), (12275, 360), (12279, 120), (12280, 120), (12281, 360), (12283, 360), (12287, 120), (12486, 90), (12487, 180), (12495, 45), (12502, 720), (12503, 720), (12508, 360), (12509, 720), (12511, 360), (12534, 360), (12535, 360), (12536, 360), (12537, 360), (12538, 720), (12539, 720)]

theorem segOK : checkSeg 20 perms 12146 12542 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 12146 12542 13035 184420853520 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 184420853520)
    (SegSum.cons (w := 720) h12146 (SegSum.cons (w := 720) h12147 (SegSum.cons (w := 360) h12150 (SegSum.cons (w := 360) h12151 (SegSum.cons (w := 360) h12152 (SegSum.cons (w := 360) h12153 (SegSum.cons (w := 720) h12154 (SegSum.cons (w := 720) h12155 (SegSum.cons (w := 360) h12158 (SegSum.cons (w := 360) h12159 (SegSum.cons (w := 120) h12272 (SegSum.cons (w := 360) h12273 (SegSum.cons (w := 360) h12275 (SegSum.cons (w := 120) h12279 (SegSum.cons (w := 120) h12280 (SegSum.cons (w := 360) h12281 (SegSum.cons (w := 360) h12283 (SegSum.cons (w := 120) h12287 (SegSum.cons (w := 90) h12486 (SegSum.cons (w := 180) h12487 (SegSum.cons (w := 45) h12495 (SegSum.cons (w := 720) h12502 (SegSum.cons (w := 720) h12503 (SegSum.cons (w := 360) h12508 (SegSum.cons (w := 720) h12509 (SegSum.cons (w := 360) h12511 (SegSum.cons (w := 360) h12534 (SegSum.cons (w := 360) h12535 (SegSum.cons (w := 360) h12536 (SegSum.cons (w := 360) h12537 (SegSum.cons (w := 720) h12538 (SegSum.cons (w := 720) h12539 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S19
