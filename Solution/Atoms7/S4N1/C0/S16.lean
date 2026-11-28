/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Atoms7.S4N1.C0.Actions

/-! Generated identity-class certificate for the product-row count. -/

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option Elab.async false

@[expose] public section

namespace RACert.S4N1.C0.S16

open RACert RACert.Problem

theorem cover1967 : P.CoversSplit 24 10 1967 0xffff0000000000000000000000000000a0a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [515, 517, 522, 860, 872, 916, 1209, 1251, 1258, 1259, 1308]) (ps := [(16, [529], [1258])]) (by decide +kernel)

theorem c1967_0 : P.sumLeaves 24 2014208 1024 = 6460706 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1967) (lo := 0) (len := 1024) (W := 6460706) check rows elimOK (by decide) (by decide) cover1967 (by decide)
  decide +kernel

theorem h1967 : P.leaf 34 1967 = 6460706 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 6460706)]) (.cons c1967_0 (.nil)) (by decide) (by decide))

theorem cover17070 : P.CoversSplit 24 10 17070 0xa000000000000000a00000000000000080000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 515, 517, 522, 524, 566, 573, 859, 860, 879, 916, 921]) (by decide +kernel)

theorem h17070 : P.leaf 34 17070 = 242304 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 17070) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 17070) (weight := fun _ => 1) (xs := [831, 895, 957, 959, 1021, 1023]) check rows elimOK (by decide) (by decide) cover17070 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h1972 : P.leaf 34 1972 = 242304 :=
  orient24 (v := 17070) (by decide) (by decide +kernel) h17070

theorem cover17086 : P.CoversSplit 24 10 17086 0xf000f00000000000f000f00000000000f000f00000000000f0000000000000000000000000000000000000000000000000000000000000000000000000000000c000c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 517, 524, 566, 573, 859, 866, 867, 871, 916, 921, 1251, 1259]) (ps := [(14, [880], [1266])]) (by decide +kernel)

theorem h17086 : P.leaf 34 17086 = 1488664 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 17086) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 17086) (weight := fun _ => 1) (xs := [494, 495, 510, 511, 828, 829, 830, 831, 876, 877, 878, 879, 892, 893, 894, 895, 940, 941, 942, 943, 956, 957, 958, 959, 1004, 1005, 1006, 1007, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover17086 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h1973 : P.leaf 34 1973 = 1488664 :=
  orient24 (v := 17086) (by decide) (by decide +kernel) h17086

theorem cover17071 : P.CoversSplit 24 10 17071 0xff00ff00aa000000ff00ff00aa0000008c000000000000008c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 517, 522, 524, 566, 573, 859, 872, 879, 916, 921, 1202, 1210]) (by decide +kernel)

theorem c17071_0 : P.sumLeaves 24 17480704 1024 = 3451514 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 17071) (lo := 0) (len := 1024) (W := 3451514) check rows elimOK (by decide) (by decide) cover17071 (by decide)
  decide +kernel

theorem h17071 : P.leaf 34 17071 = 3451514 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 3451514)]) (.cons c17071_0 (.nil)) (by decide) (by decide))

theorem h1974 : P.leaf 34 1974 = 3451514 :=
  orient24 (v := 17071) (by decide) (by decide +kernel) h17071

theorem cover17087 : P.CoversSplit 24 10 17087 0xff00ff00aa000000ff00ff00aa000000ff00ff0000000000ff000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00880000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [517, 524, 566, 573, 867, 872, 916, 921, 1202, 1210, 1217, 1251, 1259]) (ps := [(14, [958], [1217, 1266])]) (by decide +kernel)

theorem c17087_0 : P.sumLeaves 24 17497088 1024 = 9597562 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 17087) (lo := 0) (len := 1024) (W := 9597562) check rows elimOK (by decide) (by decide) cover17087 (by decide)
  decide +kernel

theorem h17087 : P.leaf 34 17087 = 9597562 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 9597562)]) (.cons c17087_0 (.nil)) (by decide) (by decide))

theorem h1975 : P.leaf 34 1975 = 9597562 :=
  orient24 (v := 17087) (by decide) (by decide +kernel) h17087

theorem cover17103 : P.CoversSplit 24 10 17103 0xf000f00000000000f000f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [515, 516, 522, 536, 573, 859, 860, 871, 879, 916, 921]) (ps := [(14, [958], [1266])]) (by decide +kernel)

theorem h17103 : P.leaf 34 17103 = 2141172 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 17103) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 17103) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 17103) (weight := rowWeight keep1 twice1) (xs := [940, 941, 942, 943, 956, 957, 958, 959, 1004, 1005, 1006, 1007, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover17103 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h1978 : P.leaf 34 1978 = 2141172 :=
  orient24 (v := 17103) (by decide) (by decide +kernel) h17103

theorem cover17119 : P.CoversSplit 24 10 17119 0xf000f00000000000f000f00000000000a000000000000000a0000000000000000000000000000000000000000000000000000000000000000000000000000000c000c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [516, 536, 573, 859, 860, 867, 871, 916, 921, 1210, 1259]) (ps := [(14, [958], [1266])]) (by decide +kernel)

theorem h17119 : P.leaf 34 17119 = 4468121 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 17119) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 17119) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 17119) (weight := rowWeight keep1 twice1) (xs := [494, 495, 510, 511, 829, 831, 893, 895, 940, 941, 942, 943, 956, 957, 958, 959, 1004, 1005, 1006, 1007, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover17119 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h1979 : P.leaf 34 1979 = 4468121 :=
  orient24 (v := 17119) (by decide) (by decide +kernel) h17119

theorem cover17134 : P.CoversSplit 24 10 17134 0xa000a00000000000a000a00000000000a000000000000000a000000000000000000000000000000000000000000000000000000000000000000000000000000080008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 515, 522, 573, 859, 871, 879, 916, 921, 1210, 1259]) (ps := [(14, [874], [1266])]) (by decide +kernel)

theorem h17134 : P.leaf 34 17134 = 1561650 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 17134) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 17134) (weight := fun _ => 1) (xs := [495, 511, 829, 831, 893, 895, 941, 943, 957, 959, 1005, 1007, 1021, 1023]) check rows elimOK (by decide) (by decide) cover17134 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h1980 : P.leaf 34 1980 = 1561650 :=
  orient24 (v := 17134) (by decide) (by decide +kernel) h17134

theorem cover17150 : P.CoversSplit 24 10 17150 0xf000f00000000000f000f00000000000f000f00000000000f000f000000000000000000000000000000000000000000000000000000000000000000000000000c000c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 573, 859, 860, 866, 867, 871, 916, 921, 1259]) (ps := [(14, [874], [1266])]) (by decide +kernel)

theorem c17150_0 : P.sumLeaves 24 17561600 1024 = 6228136 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 17150) (lo := 0) (len := 1024) (W := 6228136) check rows elimOK (by decide) (by decide) cover17150 (by decide)
  decide +kernel

theorem h17150 : P.leaf 34 17150 = 6228136 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 6228136)]) (.cons c17150_0 (.nil)) (by decide) (by decide))

theorem h1981 : P.leaf 34 1981 = 6228136 :=
  orient24 (v := 17150) (by decide) (by decide +kernel) h17150

theorem cover17135 : P.CoversSplit 24 10 17135 0xff00ff00aa000000ff00ff00aa000000ff0000000000fa00ff0000000000c8000000000000000000000000000000000000000000000000000000000000000000cc00cc00880000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [515, 522, 573, 859, 879, 916, 921, 1202, 1210, 1259]) (ps := [(14, [965], [1266]), (17, [1259], [1251])]) (by decide +kernel)

theorem c17135_0 : P.sumLeaves 24 17546240 1024 = 10218392 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 17135) (lo := 0) (len := 1024) (W := 10218392) check rows elimOK (by decide) (by decide) cover17135 (by decide)
  decide +kernel

theorem h17135 : P.leaf 34 17135 = 10218392 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 10218392)]) (.cons c17135_0 (.nil)) (by decide) (by decide))

theorem h1982 : P.leaf 34 1982 = 10218392 :=
  orient24 (v := 17135) (by decide) (by decide +kernel) h17135

theorem cover17151 : P.CoversSplit 24 10 17151 0xff00ff00aa000000ff00ff00aa000000ff00ff00aa000000ff00ff00aa0000000000000000000000000000000000000000000000000000000000000000000000cc00cc00880000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [573, 859, 867, 916, 921, 1202, 1210, 1259]) (ps := [(8, [1217], [1266]), (14, [965], [1266])]) (by decide +kernel)

theorem c17151_0 : P.sumLeaves 24 17562624 1024 = 28766172 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 17151) (lo := 0) (len := 1024) (W := 28766172) check rows elimOK (by decide) (by decide) cover17151 (by decide)
  decide +kernel

theorem h17151 : P.leaf 34 17151 = 28766172 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 28766172)]) (.cons c17151_0 (.nil)) (by decide) (by decide))

theorem h1983 : P.leaf 34 1983 = 28766172 :=
  orient24 (v := 17151) (by decide) (by decide +kernel) h17151

theorem cover17196 : P.CoversSplit 24 10 17196 0x8000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 466, 472, 473, 515, 517, 522, 572, 859, 879]) (by decide +kernel)

theorem h17196 : P.leaf 34 17196 = 34536 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 17196) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 17196) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 17196) (weight := rowWeight keep1 twice1) (xs := [383, 511, 895, 1023]) check rows elimOK (by decide) (by decide) cover17196 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h1988 : P.leaf 34 1988 = 34536 :=
  orient24 (v := 17196) (by decide) (by decide +kernel) h17196

theorem cover1989 : P.CoversSplit 24 10 1989 0xcc000000000000000000000000000000cc0000000000000000000000000000000000000000000000003300000000000000000000000000000033000000000000cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 515, 522, 566, 860, 872, 915, 916, 1209, 1251, 1308, 1609]) (by decide +kernel)

theorem h1989 : P.leaf 34 1989 = 753834 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1989) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1989) (weight := fun _ => 1) (xs := [506, 507, 510, 511, 560, 561, 564, 565, 688, 689, 692, 693, 890, 891, 894, 895, 1018, 1019, 1022, 1023]) check rows elimOK (by decide) (by decide) cover1989 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1990 : P.CoversSplit 24 10 1990 0xa0a00000000000000000000000000000a0a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000a0a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 515, 516, 522, 566, 860, 872, 915, 916, 1202, 1209, 1210, 1258, 1259, 1308]) (ps := [(17, [1308], [1259])]) (by decide +kernel)

theorem h1990 : P.leaf 34 1990 = 392644 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1990) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1990) (weight := fun _ => 1) (xs := [501, 503, 509, 511, 885, 887, 893, 895, 1013, 1015, 1021, 1023]) check rows elimOK (by decide) (by decide) cover1990 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1991 : P.CoversSplit 24 10 1991 0xffff0000000000000000000000000000ffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [515, 522, 566, 860, 915, 916, 1202, 1209, 1251, 1258, 1259, 1308]) (ps := [(17, [1308], [1259])]) (by decide +kernel)

theorem c1991_0 : P.sumLeaves 24 2038784 1024 = 4259570 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1991) (lo := 0) (len := 1024) (W := 4259570) check rows elimOK (by decide) (by decide) cover1991 (by decide)
  decide +kernel

theorem h1991 : P.leaf 34 1991 = 4259570 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 4259570)]) (.cons c1991_0 (.nil)) (by decide) (by decide))

theorem cover1996 : P.CoversSplit 24 10 1996 0x8000000000000000000000000000000080000000000000000000000000000000000000000000000000200000000000000000000000000000002000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 508, 515, 516, 522, 860, 872, 915, 1202, 1209, 1259, 1308]) (by decide +kernel)

theorem h1996 : P.leaf 34 1996 = 138568 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1996) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1996) (weight := fun _ => 1) (xs := [511, 565, 693, 895, 1023]) check rows elimOK (by decide) (by decide) cover1996 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1997 : P.CoversSplit 24 10 1997 0xcc000000000000000000000000000000cc0000000000000000000000000000000000000000000000003300000000000000000000000000000033000000000000cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 515, 522, 860, 872, 915, 1209, 1251, 1308, 1609]) (by decide +kernel)

theorem h1997 : P.leaf 34 1997 = 1807756 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1997) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1997) (weight := fun _ => 1) (xs := [506, 507, 510, 511, 560, 561, 564, 565, 688, 689, 692, 693, 890, 891, 894, 895, 1018, 1019, 1022, 1023]) check rows elimOK (by decide) (by decide) cover1997 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1998 : P.CoversSplit 24 10 1998 0xa0a00000000000000000000000000000a0a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000a0a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 515, 516, 522, 860, 872, 916, 1202, 1209, 1210, 1258, 1259, 1308]) (ps := [(17, [1308], [1259])]) (by decide +kernel)

theorem h1998 : P.leaf 34 1998 = 1340356 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 1998) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 1998) (weight := fun _ => 1) (xs := [501, 503, 509, 511, 885, 887, 893, 895, 1013, 1015, 1021, 1023]) check rows elimOK (by decide) (by decide) cover1998 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover1999 : P.CoversSplit 24 10 1999 0xffff0000000000000000000000000000ffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [515, 522, 860, 916, 1202, 1209, 1251, 1258, 1259, 1308]) (ps := [(17, [1308], [1259])]) (by decide +kernel)

theorem c1999_0 : P.sumLeaves 24 2046976 1024 = 8962256 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 1999) (lo := 0) (len := 1024) (W := 8962256) check rows elimOK (by decide) (by decide) cover1999 (by decide)
  decide +kernel

theorem h1999 : P.leaf 34 1999 = 8962256 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 8962256)]) (.cons c1999_0 (.nil)) (by decide) (by decide))

theorem cover17199 : P.CoversSplit 24 10 17199 0xffffffffaa000000ffffffffaa00000088880000000000008888000000000000c0c0c0c08008000000000000000000008080000000000000000000000000000088888888880000000000000000000000888800000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 517, 522, 529, 572, 859, 872, 915, 1202, 1210, 1259, 1601]) (by decide +kernel)

noncomputable def f17199 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (17611776 + i)

theorem c17199_0 : rowSum f17199 0 1024 = 8249276 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 17199) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover17199 (by decide)
  decide +kernel

theorem sum17199 : rowSum f17199 0 1024 = 8249276 :=
  c17199_0

theorem h17199 : P.leaf 34 17199 = 8249276 :=
  leaf_weighted (k := 24) (d := 10) (H := 17199) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 17199) (by decide) (by decide +kernel)) sum17199

theorem h2006 : P.leaf 34 2006 = 8249276 :=
  orient24 (v := 17199) (by decide) (by decide +kernel) h17199

theorem cover17215 : P.CoversSplit 24 10 17215 0xffffffffaa000000ffffffffaa000000ffffffff00000000ffff000000000000c0c0c0c0800000000000000000000000c0c0c0c0000000000000000000000000ffffffffaa000000ffff0000aa000000ffffffff00000000ffff0000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [517, 529, 572, 859, 866, 872, 915, 1202, 1210, 1217, 1251, 1259, 1264, 1308, 1601, 1609]) (ps := [(14, [958], [1217])]) (by decide +kernel)

noncomputable def f17215 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (17628160 + i)

theorem c17215_0 : rowSum f17215 0 934 = 11380367 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 17215) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover17215 (by decide)
  decide +kernel

theorem c17215_1 : rowSum f17215 934 90 = 21587585 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 17215) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover17215 (by decide)
  decide +kernel

theorem sum17215 : rowSum f17215 0 1024 = 32967952 :=
  rowSum_append (F := f17215) (lo := 0) (n := 934) (m := 90) (A := 11380367) (B := 21587585) c17215_0 (c17215_1)

theorem h17215 : P.leaf 34 17215 = 32967952 :=
  leaf_weighted (k := 24) (d := 10) (H := 17215) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 17215) (by decide) (by decide +kernel)) sum17215

theorem h2007 : P.leaf 34 2007 = 32967952 :=
  orient24 (v := 17215) (by decide) (by decide +kernel) h17215

theorem cover3050 : P.CoversSplit 24 10 3050 0xaaaa0000000000000000000000000000a0a000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000aaaa0000000000000000000000000000a0a000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 515, 522, 523, 565, 859, 879, 915, 916, 1210, 1258]) (by decide +kernel)

theorem h3050 : P.leaf 34 3050 = 2345194 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 3050) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 3050) (weight := fun _ => 1) (xs := [309, 373, 375, 381, 383, 497, 499, 501, 503, 505, 507, 509, 511, 821, 885, 887, 893, 895, 1009, 1011, 1013, 1015, 1017, 1019, 1021, 1023]) check rows elimOK (by decide) (by decide) cover3050 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h2012 : P.leaf 34 2012 = 2345194 :=
  orient4 (v := 3050) (by decide) (by decide +kernel) h3050

theorem cover3051 : P.CoversSplit 24 10 3051 0xffff0000000000000000000000000000ffff00000000000000330000000000000000000000000000000000000000000000000000000000000000000000000000ffff0000000000000000000000000000ffff00000000000000330000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 522, 523, 565, 859, 915, 916, 1202, 1210, 1251, 1258]) (by decide +kernel)

theorem c3051_0 : P.sumLeaves 24 3124224 1024 = 11357204 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 3051) (lo := 0) (len := 1024) (W := 11357204) check rows elimOK (by decide) (by decide) cover3051 (by decide)
  decide +kernel

theorem h3051 : P.leaf 34 3051 = 11357204 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 11357204)]) (.cons c3051_0 (.nil)) (by decide) (by decide))

theorem h2013 : P.leaf 34 2013 = 11357204 :=
  orient4 (v := 3051) (by decide) (by decide +kernel) h3051

theorem cover17263 : P.CoversSplit 24 10 17263 0xffffffffaaaaaaaaffffffffaaaaaaaaffff000000005050ffff000000000000c0c0c0c0808080800000000000000000c0c00000000040400000000000000000cccccccc888888880000000000000000cccc44440000000000330011000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [515, 522, 572, 859, 872, 915, 1202, 1210, 1259, 1308, 1601]) (ps := [(17, [1259, 1308], [1251])]) (by decide +kernel)

theorem c17263_0 : P.sumLeaves 24 17677312 897 = 6194078 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 17263) (lo := 0) (len := 897) (W := 6194078) check rows elimOK (by decide) (by decide) cover17263 (by decide)
  decide +kernel

theorem c17263_1 : P.sumLeaves 24 17678209 127 = 15117455 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 17263) (lo := 897) (len := 127) (W := 15117455) check rows elimOK (by decide) (by decide) cover17263 (by decide)
  decide +kernel

theorem h17263 : P.leaf 34 17263 = 21311533 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(897, 6194078), (127, 15117455)]) (.cons c17263_0 (.cons c17263_1 (.nil))) (by decide) (by decide))

theorem h2014 : P.leaf 34 2014 = 21311533 :=
  orient24 (v := 17263) (by decide) (by decide +kernel) h17263

theorem cover2015 : P.CoversSplit 24 10 2015 0xffffffffa0a0a0a0ffffffffa0a0a0a0ffffffff0000a0a0ffffffff0000a0a0ffccffcc80008000cc00cc0080008000ffccffcc00008000cc00cc0000008000ffffffffa0a0a0a0ffffffffa0a0a0a000000000000000000000000000000000ffccffcc80008000cc00cc008000800000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [516, 860, 915, 916, 1202, 1217, 1258, 1259, 1308]) (by decide +kernel)

theorem c2015_0 : P.sumLeaves 24 2063360 492 = 9143964 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 2015) (lo := 0) (len := 492) (W := 9143964) check rows elimOK (by decide) (by decide) cover2015 (by decide)
  decide +kernel

theorem c2015_1 : P.sumLeaves 24 2063852 310 = 20725818 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 2015) (lo := 492) (len := 310) (W := 20725818) check rows elimOK (by decide) (by decide) cover2015 (by decide)
  decide +kernel

theorem c2015_2 : P.sumLeaves 24 2064162 148 = 15821283 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 2015) (lo := 802) (len := 148) (W := 15821283) check rows elimOK (by decide) (by decide) cover2015 (by decide)
  decide +kernel

theorem c2015_3 : P.sumLeaves 24 2064310 74 = 35833462 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 2015) (lo := 950) (len := 74) (W := 35833462) check rows elimOK (by decide) (by decide) cover2015 (by decide)
  decide +kernel

theorem h2015 : P.leaf 34 2015 = 81524527 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(492, 9143964), (310, 20725818), (148, 15821283), (74, 35833462)]) (.cons c2015_0 (.cons c2015_1 (.cons c2015_2 (.cons c2015_3 (.nil))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(1967, 48), (1972, 48), (1973, 48), (1974, 48), (1975, 48), (1978, 24), (1979, 24), (1980, 48), (1981, 48), (1982, 48), (1983, 48), (1988, 24), (1989, 24), (1990, 48), (1991, 48), (1996, 48), (1997, 48), (1998, 48), (1999, 48), (2006, 24), (2007, 24), (2012, 48), (2013, 48), (2014, 48), (2015, 48)]

theorem segOK : checkSeg 16 perms 1967 2028 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 1967 2028 1056 10836583368 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 10836583368)
    (SegSum.cons (w := 48) h1967 (SegSum.cons (w := 48) h1972 (SegSum.cons (w := 48) h1973 (SegSum.cons (w := 48) h1974 (SegSum.cons (w := 48) h1975 (SegSum.cons (w := 24) h1978 (SegSum.cons (w := 24) h1979 (SegSum.cons (w := 48) h1980 (SegSum.cons (w := 48) h1981 (SegSum.cons (w := 48) h1982 (SegSum.cons (w := 48) h1983 (SegSum.cons (w := 24) h1988 (SegSum.cons (w := 24) h1989 (SegSum.cons (w := 48) h1990 (SegSum.cons (w := 48) h1991 (SegSum.cons (w := 48) h1996 (SegSum.cons (w := 48) h1997 (SegSum.cons (w := 48) h1998 (SegSum.cons (w := 48) h1999 (SegSum.cons (w := 24) h2006 (SegSum.cons (w := 24) h2007 (SegSum.cons (w := 48) h2012 (SegSum.cons (w := 48) h2013 (SegSum.cons (w := 48) h2014 (SegSum.cons (w := 48) h2015 (show SegSum (P.leaf 34) [] 0 from rfl)))))))))))))))))))))))))) (by decide)

end RACert.S4N1.C0.S16
