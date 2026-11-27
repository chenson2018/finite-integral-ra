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

namespace RACert.S6N0.C0.S59

open RACert RACert.Problem

theorem cover81819 : P.CoversSplit 26 10 81819 0xf0f0000000000000f0f000000000000000000000000000000000000000000000000005050000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003000000000000000200000000000000000000000000000000000000000000000000001000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 538, 615, 972, 1273, 1315, 1322, 1658]) (by decide +kernel)

theorem c81819_0 : P.sumLeaves 26 83782656 1024 = 26211328 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81819) (lo := 0) (len := 1024) (W := 26211328) check rows elimOK (by decide) (by decide) cover81819 (by decide)
  decide +kernel

theorem h81819 : P.leaf 36 81819 = 26211328 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 26211328)]) (.cons c81819_0 (.nil)) (by decide) (by decide))

theorem cover81820 : P.CoversSplit 26 10 81820 0xffff000000000000ffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003300000000000000220000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 538, 923, 930, 972, 1273, 1315, 1322, 1658]) (by decide +kernel)

theorem c81820_0 : P.sumLeaves 26 83783680 1024 = 8403120 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81820) (lo := 0) (len := 1024) (W := 8403120) check rows elimOK (by decide) (by decide) cover81820 (by decide)
  decide +kernel

theorem h81820 : P.leaf 36 81820 = 8403120 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 8403120)]) (.cons c81820_0 (.nil)) (by decide) (by decide))

theorem cover81821 : P.CoversSplit 26 10 81821 0xffff000000000000ffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003300000000000000220000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 538, 923, 930, 972, 1273, 1315, 1322, 1658]) (by decide +kernel)

theorem c81821_0 : P.sumLeaves 26 83784704 1024 = 34607802 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81821) (lo := 0) (len := 1024) (W := 34607802) check rows elimOK (by decide) (by decide) cover81821 (by decide)
  decide +kernel

theorem h81821 : P.leaf 36 81821 = 34607802 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 34607802)]) (.cons c81821_0 (.nil)) (by decide) (by decide))

theorem cover81822 : P.CoversSplit 26 10 81822 0xffff000000000000ffff000000000000000000000000000000000000000000000f0f0a0a000000000a0a0a0a000000000000000000000000000000000000000000000000000000000000000000000000003300000000000000220000000000000000000000000000000000000000000000030002000000000002000200000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 538, 972, 1273, 1315, 1322, 1658]) (by decide +kernel)

theorem c81822_0 : P.sumLeaves 26 83785728 1024 = 27650916 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81822) (lo := 0) (len := 1024) (W := 27650916) check rows elimOK (by decide) (by decide) cover81822 (by decide)
  decide +kernel

theorem h81822 : P.leaf 36 81822 = 27650916 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 27650916)]) (.cons c81822_0 (.nil)) (by decide) (by decide))

theorem cover81823 : P.CoversSplit 26 10 81823 0xffff000000000000ffff000000000000000000000000000000000000000000000f0f0a0a000000000a0a0a0a000000000000000000000000000000000000000000000000000000000000000000000000003300000000000000220000000000000000000000000000000000000000000000030002000000000002000200000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 538, 972, 1273, 1315, 1322, 1658]) (by decide +kernel)

theorem c81823_0 : P.sumLeaves 26 83786752 1024 = 77338324 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81823) (lo := 0) (len := 1024) (W := 77338324) check rows elimOK (by decide) (by decide) cover81823 (by decide)
  decide +kernel

theorem h81823 : P.leaf 36 81823 = 77338324 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 77338324)]) (.cons c81823_0 (.nil)) (by decide) (by decide))

theorem cover81846 : P.CoversSplit 26 10 81846 0xcc00cc0000000000cc00cc000000000000000000000000000000000000000000cc00c0000000000088008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 538, 930, 972, 979, 1273, 1658, 1665]) (by decide +kernel)

theorem c81846_0 : P.sumLeaves 26 83810304 1024 = 17990104 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81846) (lo := 0) (len := 1024) (W := 17990104) check rows elimOK (by decide) (by decide) cover81846 (by decide)
  decide +kernel

theorem h81846 : P.leaf 36 81846 = 17990104 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 17990104)]) (.cons c81846_0 (.nil)) (by decide) (by decide))

theorem cover81847 : P.CoversSplit 26 10 81847 0xcc00cc0000000000cc00cc000000000000000000000000000000000000000000cc00c0000000000088008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 538, 930, 972, 979, 1658, 1665]) (by decide +kernel)

theorem c81847_0 : P.sumLeaves 26 83811328 1024 = 73773806 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81847) (lo := 0) (len := 1024) (W := 73773806) check rows elimOK (by decide) (by decide) cover81847 (by decide)
  decide +kernel

theorem h81847 : P.leaf 36 81847 = 73773806 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 73773806)]) (.cons c81847_0 (.nil)) (by decide) (by decide))

theorem cover81848 : P.CoversSplit 26 10 81848 0xf0f0f0f500000000f0f0f0f50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003000310000000000200020000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 874, 923, 930, 972, 979, 1273, 1315, 1322, 1658]) (by decide +kernel)

theorem c81848_0 : P.sumLeaves 26 83812352 1024 = 1768443 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81848) (lo := 0) (len := 1024) (W := 1768443) check rows elimOK (by decide) (by decide) cover81848 (by decide)
  decide +kernel

theorem h81848 : P.leaf 36 81848 = 1768443 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1768443)]) (.cons c81848_0 (.nil)) (by decide) (by decide))

theorem cover81849 : P.CoversSplit 26 10 81849 0xf0f0f0f500000000f0f0f0f50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003000310000000000200020000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 923, 930, 972, 979, 1273, 1315, 1322, 1658]) (by decide +kernel)

theorem c81849_0 : P.sumLeaves 26 83813376 1024 = 60253869 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81849) (lo := 0) (len := 1024) (W := 60253869) check rows elimOK (by decide) (by decide) cover81849 (by decide)
  decide +kernel

theorem h81849 : P.leaf 36 81849 = 60253869 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 60253869)]) (.cons c81849_0 (.nil)) (by decide) (by decide))

theorem cover81850 : P.CoversSplit 26 10 81850 0xf0f0f0f500000000f0f0f0f50000000000000000000000000000000000000000000050500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003000310000000000200020000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 874, 972, 979, 1273, 1315, 1322, 1658]) (by decide +kernel)

theorem c81850_0 : P.sumLeaves 26 83814400 1024 = 42922789 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81850) (lo := 0) (len := 1024) (W := 42922789) check rows elimOK (by decide) (by decide) cover81850 (by decide)
  decide +kernel

theorem h81850 : P.leaf 36 81850 = 42922789 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 42922789)]) (.cons c81850_0 (.nil)) (by decide) (by decide))

theorem cover81851 : P.CoversSplit 26 10 81851 0xf0f0f0f500000000f0f0f0f50000000000000000000000000000000000000000000050500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003000310000000000200020000000000000000000000000000000000000000000000010000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 972, 979, 1273, 1315, 1322, 1658]) (by decide +kernel)

theorem c81851_0 : P.sumLeaves 26 83815424 1024 = 134977234 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81851) (lo := 0) (len := 1024) (W := 134977234) check rows elimOK (by decide) (by decide) cover81851 (by decide)
  decide +kernel

theorem h81851 : P.leaf 36 81851 = 134977234 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 134977234)]) (.cons c81851_0 (.nil)) (by decide) (by decide))

theorem cover81854 : P.CoversSplit 26 10 81854 0xfffffffa00000000fffffffa0000000000000000000000000000000000000000fffff0f000000000aaaaa0a0000000000000000000000000000000000000000000000000000000000000000000000000003300320000000000220022000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [538, 874, 972, 979, 1273, 1315, 1322, 1658]) (by decide +kernel)

theorem c81854_0 : P.sumLeaves 26 83818496 1013 = 135697686 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81854) (lo := 0) (len := 1013) (W := 135697686) check rows elimOK (by decide) (by decide) cover81854 (by decide)
  decide +kernel

theorem c81854_1 : P.sumLeaves 26 83819509 11 = 33768084 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81854) (lo := 1013) (len := 11) (W := 33768084) check rows elimOK (by decide) (by decide) cover81854 (by decide)
  decide +kernel

theorem h81854 : P.leaf 36 81854 = 169465770 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1013, 135697686), (11, 33768084)]) (.cons c81854_0 (.cons c81854_1 (.nil))) (by decide) (by decide))

theorem cover81855 : P.CoversSplit 26 10 81855 0xfffffffa00000000fffffffa0000000000000000000000000000000000000000fffff0f000000000aaaaa0a0000000000000000000000000000000000000000000000000000000000000000000000000003300320000000000220022000000000000000000000000000000000000000000330030000000000022002000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [538, 972, 979, 1273, 1315, 1322, 1658]) (by decide +kernel)

theorem c81855_0 : P.sumLeaves 26 83819520 1004 = 312779919 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81855) (lo := 0) (len := 1004) (W := 312779919) check rows elimOK (by decide) (by decide) cover81855 (by decide)
  decide +kernel

theorem c81855_1 : P.sumLeaves 26 83820524 20 = 132792444 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81855) (lo := 1004) (len := 20) (W := 132792444) check rows elimOK (by decide) (by decide) cover81855 (by decide)
  decide +kernel

theorem h81855 : P.leaf 36 81855 = 445572363 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1004, 312779919), (20, 132792444)]) (.cons c81855_0 (.cons c81855_1 (.nil))) (by decide) (by decide))

theorem cover81864 : P.CoversSplit 26 10 81864 0xf0f00000f0f00005f0f00000f0f00005f0f00000f0f00000a0a00000a08000000000000000000000000000000000000000000000000000000000000000000000f0f00000f0f00005f0f00000f0f00005f0f00000f0000000a0a00000a00000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 923, 930, 972, 979, 1315, 1658, 1665]) (by decide +kernel)

theorem c81864_0 : P.sumLeaves 26 83828736 962 = 613408 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81864) (lo := 0) (len := 962) (W := 613408) check rows elimOK (by decide) (by decide) cover81864 (by decide)
  decide +kernel

theorem c81864_1 : P.sumLeaves 26 83829698 62 = 370592 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81864) (lo := 962) (len := 62) (W := 370592) check rows elimOK (by decide) (by decide) cover81864 (by decide)
  decide +kernel

theorem h81864 : P.leaf 36 81864 = 984000 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(962, 613408), (62, 370592)]) (.cons c81864_0 (.cons c81864_1 (.nil))) (by decide) (by decide))

theorem cover81865 : P.CoversSplit 26 10 81865 0xf0f00000f0f00005f0f00000f0f00005f0f00000f0f00000a0a00000a08000000000000000000000000000000000000000000000000000000000000000000000f0f00000f0f00005f0f00000f0f00005f0f00000f0000000a0a00000a00000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 923, 930, 972, 979, 1315, 1658, 1665]) (by decide +kernel)

theorem c81865_0 : P.sumLeaves 26 83829760 962 = 7455824 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81865) (lo := 0) (len := 962) (W := 7455824) check rows elimOK (by decide) (by decide) cover81865 (by decide)
  decide +kernel

theorem c81865_1 : P.sumLeaves 26 83830722 62 = 4912680 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81865) (lo := 962) (len := 62) (W := 4912680) check rows elimOK (by decide) (by decide) cover81865 (by decide)
  decide +kernel

theorem h81865 : P.leaf 36 81865 = 12368504 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(962, 7455824), (62, 4912680)]) (.cons c81865_0 (.cons c81865_1 (.nil))) (by decide) (by decide))

theorem cover81866 : P.CoversSplit 26 10 81866 0xf0f00000f0f00005f0f00000f0f00005f0f00000f0f00000a0a00000a08000000000000000000000000000000000000000000000000000000000000000000000f0f00000f0f00005f0f00000f0f00005f0f00000f0000000a0a00000a00000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 930, 972, 979, 1315, 1658, 1665]) (by decide +kernel)

theorem c81866_0 : P.sumLeaves 26 83830784 962 = 7038456 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81866) (lo := 0) (len := 962) (W := 7038456) check rows elimOK (by decide) (by decide) cover81866 (by decide)
  decide +kernel

theorem c81866_1 : P.sumLeaves 26 83831746 62 = 3635256 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81866) (lo := 962) (len := 62) (W := 3635256) check rows elimOK (by decide) (by decide) cover81866 (by decide)
  decide +kernel

theorem h81866 : P.leaf 36 81866 = 10673712 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(962, 7038456), (62, 3635256)]) (.cons c81866_0 (.cons c81866_1 (.nil))) (by decide) (by decide))

theorem cover81867 : P.CoversSplit 26 10 81867 0xf0f00000f0f00005f0f00000f0f00005f0f00000f0f00000a0a00000a08000000000000000000000000000000000000000000000000000000000000000000000f0f00000f0f00005f0f00000f0f00005f0f00000f0000000a0a00000a00000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 930, 972, 979, 1266, 1315, 1658, 1665]) (by decide +kernel)

theorem c81867_0 : P.sumLeaves 26 83831808 962 = 37499950 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81867) (lo := 0) (len := 962) (W := 37499950) check rows elimOK (by decide) (by decide) cover81867 (by decide)
  decide +kernel

theorem c81867_1 : P.sumLeaves 26 83832770 62 = 21634168 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81867) (lo := 962) (len := 62) (W := 21634168) check rows elimOK (by decide) (by decide) cover81867 (by decide)
  decide +kernel

theorem h81867 : P.leaf 36 81867 = 59134118 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(962, 37499950), (62, 21634168)]) (.cons c81867_0 (.cons c81867_1 (.nil))) (by decide) (by decide))

theorem cover81870 : P.CoversSplit 26 10 81870 0xffff0000ffff0500ffff0000ffff0500ffff0000fffc0500aaaa0000aa8800000000000000000000000000000000000000000000000000000000000000000000ffff0000ffff0500ffff0000ffff0500ffff0000ff000500aaaa0000aa0000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 880, 930, 972, 979, 1266, 1273, 1315, 1658, 1665]) (by decide +kernel)

theorem c81870_0 : P.sumLeaves 26 83834880 502 = 8652378 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81870) (lo := 0) (len := 502) (W := 8652378) check rows elimOK (by decide) (by decide) cover81870 (by decide)
  decide +kernel

theorem c81870_1 : P.sumLeaves 26 83835382 478 = 22372175 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81870) (lo := 502) (len := 478) (W := 22372175) check rows elimOK (by decide) (by decide) cover81870 (by decide)
  decide +kernel

theorem c81870_2 : P.sumLeaves 26 83835860 44 = 12678516 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81870) (lo := 980) (len := 44) (W := 12678516) check rows elimOK (by decide) (by decide) cover81870 (by decide)
  decide +kernel

theorem h81870 : P.leaf 36 81870 = 43703069 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(502, 8652378), (478, 22372175), (44, 12678516)]) (.cons c81870_0 (.cons c81870_1 (.cons c81870_2 (.nil)))) (by decide) (by decide))

theorem cover81871 : P.CoversSplit 26 10 81871 0xffff0000ffff0500ffff0000ffff0500ffff0000fffc0500aaaa0000aa8800000000000000000000000000000000000000000000000000000000000000000000ffff0000ffff0500ffff0000ffff0500ffff0000ff000500aaaa0000aa0000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 930, 972, 979, 1266, 1273, 1315, 1658, 1665]) (by decide +kernel)

theorem c81871_0 : P.sumLeaves 26 83835904 502 = 42761503 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81871) (lo := 0) (len := 502) (W := 42761503) check rows elimOK (by decide) (by decide) cover81871 (by decide)
  decide +kernel

theorem c81871_1 : P.sumLeaves 26 83836406 478 = 120923986 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81871) (lo := 502) (len := 478) (W := 120923986) check rows elimOK (by decide) (by decide) cover81871 (by decide)
  decide +kernel

theorem c81871_2 : P.sumLeaves 26 83836884 44 = 71689660 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 81871) (lo := 980) (len := 44) (W := 71689660) check rows elimOK (by decide) (by decide) cover81871 (by decide)
  decide +kernel

theorem h81871 : P.leaf 36 81871 = 235375149 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(502, 42761503), (478, 120923986), (44, 71689660)]) (.cons c81871_0 (.cons c81871_1 (.cons c81871_2 (.nil)))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(81819, 720), (81820, 720), (81821, 720), (81822, 720), (81823, 720), (81846, 180), (81847, 180), (81848, 360), (81849, 360), (81850, 720), (81851, 720), (81854, 360), (81855, 360), (81864, 90), (81865, 180), (81866, 720), (81867, 720), (81870, 360), (81871, 360)]

theorem segOK : checkSeg 20 perms 81819 81882 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 81819 81882 9270 666824240160 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 666824240160)
    (SegSum.cons (w := 720) h81819 (SegSum.cons (w := 720) h81820 (SegSum.cons (w := 720) h81821 (SegSum.cons (w := 720) h81822 (SegSum.cons (w := 720) h81823 (SegSum.cons (w := 180) h81846 (SegSum.cons (w := 180) h81847 (SegSum.cons (w := 360) h81848 (SegSum.cons (w := 360) h81849 (SegSum.cons (w := 720) h81850 (SegSum.cons (w := 720) h81851 (SegSum.cons (w := 360) h81854 (SegSum.cons (w := 360) h81855 (SegSum.cons (w := 90) h81864 (SegSum.cons (w := 180) h81865 (SegSum.cons (w := 720) h81866 (SegSum.cons (w := 720) h81867 (SegSum.cons (w := 360) h81870 (SegSum.cons (w := 360) h81871 (show SegSum (P.leaf 36) [] 0 from rfl)))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S59
