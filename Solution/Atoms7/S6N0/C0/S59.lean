/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Atoms7.S6N0.C0.Actions

/-! Generated identity-class certificate for the product-row count. -/

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option Elab.async false

@[expose] public section

namespace RACert.S6N0.C0.S59

open RACert RACert.Problem

theorem cover88990 : P.CoversSplit 26 10 88990 0xffff000000000000ffff000000000000ffff00000000000cfafa00000000000800000f0f0000000000000a0a0000000000000f0f0000000c00000a0a000000080000000000000000000000000000000000ff000000cc000c00fa000000c800080000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [530, 538, 874, 922, 979, 1315, 1322, 1658]) (ps := [(18, [1266], [1315])]) (by decide +kernel)

theorem c88990_0 : P.sumLeaves 26 91125760 958 = 7316804 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88990) (lo := 0) (len := 958) (W := 7316804) check rows elimOK (by decide) (by decide) cover88990 (by decide)
  decide +kernel

theorem c88990_1 : P.sumLeaves 26 91126718 66 = 5598776 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88990) (lo := 958) (len := 66) (W := 5598776) check rows elimOK (by decide) (by decide) cover88990 (by decide)
  decide +kernel

theorem h88990 : P.leaf 36 88990 = 12915580 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(958, 7316804), (66, 5598776)]) (.cons c88990_0 (.cons c88990_1 (.nil))) (by decide) (by decide))

theorem cover88991 : P.CoversSplit 26 10 88991 0xffff000000000000ffff000000000000ffff00000000000cfafa00000000000800000f0f0000000000000a0a0000000000000f0f0000000c00000a0a000000080000000000000000000000000000000000ff000000cc000c00fa000000c80008000000000000000000000000000000000000000f0000000c0000000a00000008 :=
  coversProjected check rows (by decide) (by decide) (xs := [530, 538, 922, 979, 1273, 1315, 1322, 1658]) (ps := [(18, [1266], [1315])]) (by decide +kernel)

theorem c88991_0 : P.sumLeaves 26 91126784 64 = 5456 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88991) (lo := 0) (len := 64) (W := 5456) check rows elimOK (by decide) (by decide) cover88991 (by decide)
  decide +kernel

theorem contract88991_1 : P.leaf 32 1423857 = 6048 := by
  exact leaf_contract_factors (k := 32) (b := 19) (H := 1423857) (ss := [(22, 1, 433), (2, 1, 488), (3, 1, 531), (4, 1, 580), (5, 1, 629), (7, 1, 825), (8, 1, 1217), (16, 1, 1210), (18, 1, 1210), (30, 0, 1315), (32, 0, 1315), (31, 0, 1322), (9, 1, 1609)]) (ids := [4, 8, 9, 10, 11, 12, 13, 15, 17, 18, 19, 21, 23, 24, 25, 26, 27, 31, 22]) (cs := [1, 1, 1, 1, 2, 1, 1, 1, 3, 4, 5, 6, 7, 8, 1, 9, 1, 10, 11, 12, 1, 13, 20, 14, 15, 16, 17, 18, 0, 0, 0, 19]) (bs := [18, 1]) (W := 6048) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c88991_1 : P.sumLeaves 26 91126848 64 = 6048 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1423857) rows (by decide) (by decide)).symm.trans contract88991_1

theorem c88991_2 : P.sumLeaves 26 91126912 830 = 41369425 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88991) (lo := 128) (len := 830) (W := 41369425) check rows elimOK (by decide) (by decide) cover88991 (by decide)
  decide +kernel

theorem c88991_3 : P.sumLeaves 26 91127742 66 = 23747460 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88991) (lo := 958) (len := 66) (W := 23747460) check rows elimOK (by decide) (by decide) cover88991 (by decide)
  decide +kernel

theorem h88991 : P.leaf 36 88991 = 65128389 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(64, 5456), (64, 6048), (830, 41369425), (66, 23747460)]) (.cons c88991_0 (.cons c88991_1 (.cons c88991_2 (.cons c88991_3 (.nil))))) (by decide) (by decide))

theorem cover88999 : P.CoversSplit 26 10 88999 0xcc00cc0000000000cc00cc0000000000cc00cc0000000000c800c80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 538, 922, 972, 979, 1272, 1315, 1322, 1658]) (by decide +kernel)

theorem c88999_0 : P.sumLeaves 26 91134976 1024 = 7550600 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 88999) (lo := 0) (len := 1024) (W := 7550600) check rows elimOK (by decide) (by decide) cover88999 (by decide)
  decide +kernel

theorem h88999 : P.leaf 36 88999 = 7550600 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 7550600)]) (.cons c88999_0 (.nil)) (by decide) (by decide))

theorem cover89001 : P.CoversSplit 26 10 89001 0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [480, 536, 923, 972, 1272]) (by decide +kernel)

noncomputable def f89001 (i : ℕ) := rowWeight keep4 twice4 i * P.leaf 26 (91137024 + i)

theorem c89001_0 : rowSum f89001 0 1024 = 2684026 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 89001) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover89001 (by decide)
  decide +kernel

theorem sum89001 : rowSum f89001 0 1024 = 2684026 :=
  c89001_0

theorem h89001 : P.leaf 36 89001 = 2684026 :=
  leaf_weighted (k := 26) (d := 10) (H := 89001) (keep := keep4) (twice := twice4) rows (by decide) (by decide) bal4 (invRow4 (H := 89001) (by decide) (by decide +kernel)) sum89001

theorem cover89003 : P.CoversSplit 26 10 89003 0xf0f0f0f000000000f0f0f0f500000000f0f0f0f000000030f0f0f0f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003000300000000000300030000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 922, 972, 979, 1272, 1273, 1322, 1658, 1665]) (by decide +kernel)

theorem c89003_0 : P.sumLeaves 26 91139072 1024 = 7321098 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89003) (lo := 0) (len := 1024) (W := 7321098) check rows elimOK (by decide) (by decide) cover89003 (by decide)
  decide +kernel

theorem h89003 : P.leaf 36 89003 = 7321098 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 7321098)]) (.cons c89003_0 (.nil)) (by decide) (by decide))

theorem cover89005 : P.CoversSplit 26 10 89005 0xffffffff00000000fffffffa00000000ffffffff00000000fafafafa00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [536, 922, 923, 972, 1272, 1658]) (by decide +kernel)

theorem c89005_0 : P.sumLeaves 26 91141120 1002 = 4344446 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89005) (lo := 0) (len := 1002) (W := 4344446) check rows elimOK (by decide) (by decide) cover89005 (by decide)
  decide +kernel

theorem c89005_1 : P.sumLeaves 26 91142122 22 = 1793240 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89005) (lo := 1002) (len := 22) (W := 1793240) check rows elimOK (by decide) (by decide) cover89005 (by decide)
  decide +kernel

theorem h89005 : P.leaf 36 89005 = 6137686 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1002, 4344446), (22, 1793240)]) (.cons c89005_0 (.cons c89005_1 (.nil))) (by decide) (by decide))

theorem cover89007 : P.CoversSplit 26 10 89007 0xffffffff00000000fffffffa00000000ffffffff00000030fafafafa00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003300330000000000320032000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [538, 922, 972, 979, 1272, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c89007_0 : P.sumLeaves 26 91143168 954 = 19220620 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89007) (lo := 0) (len := 954) (W := 19220620) check rows elimOK (by decide) (by decide) cover89007 (by decide)
  decide +kernel

theorem c89007_1 : P.sumLeaves 26 91144122 70 = 15558120 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89007) (lo := 954) (len := 70) (W := 15558120) check rows elimOK (by decide) (by decide) cover89007 (by decide)
  decide +kernel

theorem h89007 : P.leaf 36 89007 = 34778740 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(954, 19220620), (70, 15558120)]) (.cons c89007_0 (.cons c89007_1 (.nil))) (by decide) (by decide))

theorem h89012 : P.leaf 36 89012 = 291776 := by
  exact leaf_contract_factors (k := 36) (b := 22) (H := 89012) (ss := [(7, 1, 468), (15, 1, 472), (11, 1, 817), (13, 1, 461), (12, 1, 817), (20, 1, 915), (19, 1, 865), (37, 1, 923), (29, 1, 538), (33, 1, 538), (31, 1, 979), (18, 1, 1266), (8, 1, 517), (16, 1, 1210)]) (ids := [0, 1, 2, 3, 4, 7, 8, 12, 15, 19, 20, 24, 26, 28, 30, 32, 33, 34, 21, 22, 23, 25]) (cs := [2, 3, 4, 5, 6, 1, 1, 7, 8, 1, 1, 1, 9, 1, 1, 10, 1, 1, 1, 11, 12, 20, 21, 22, 13, 23, 14, 1, 15, 1, 16, 1, 17, 18, 19, 1]) (bs := [18, 4]) (W := 291776) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem cover89013 : P.CoversSplit 26 10 89013 0xcc00cc0000000000cc00cc0000000000cc00cc0000000000c800c80000000000cc00c00000000000c000c00000000000cc00c00000000000c000c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 538, 922, 923, 972, 979, 1315, 1658]) (by decide +kernel)

theorem c89013_0 : P.sumLeaves 26 91149312 1024 = 2462500 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89013) (lo := 0) (len := 1024) (W := 2462500) check rows elimOK (by decide) (by decide) cover89013 (by decide)
  decide +kernel

theorem h89013 : P.leaf 36 89013 = 2462500 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 2462500)]) (.cons c89013_0 (.nil)) (by decide) (by decide))

theorem cover89014 : P.CoversSplit 26 10 89014 0xcc00cc0000000000cc00cc0000000000cc00cc0000000000c800c80000000000cc00c00000000000c800c00000000000cc00c00000000000c800c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 538, 874, 922, 972, 979, 1273, 1315, 1658]) (by decide +kernel)

theorem c89014_0 : P.sumLeaves 26 91150336 512 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89014) (lo := 0) (len := 512) (W := 0) check rows elimOK (by decide) (by decide) cover89014 (by decide)
  decide +kernel

theorem contract89014_1 : P.leaf 32 1424232 = 213696 := by
  exact leaf_contract_factors (k := 32) (b := 21) (H := 1424232) (ss := [(7, 1, 468), (2, 1, 488), (3, 1, 531), (29, 1, 538), (33, 1, 538), (14, 1, 866), (10, 1, 879), (31, 1, 979), (16, 1, 1210), (8, 1, 517), (18, 1, 517)]) (ids := [2, 3, 4, 7, 9, 10, 11, 13, 15, 17, 18, 19, 20, 23, 24, 26, 28, 30, 21, 22, 25]) (cs := [1, 1, 2, 3, 4, 1, 1, 5, 1, 6, 7, 8, 1, 9, 1, 10, 1, 11, 12, 13, 14, 20, 21, 15, 16, 22, 17, 1, 18, 1, 19, 1]) (bs := [18, 3]) (W := 213696) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c89014_1 : P.sumLeaves 26 91150848 64 = 213696 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1424232) rows (by decide) (by decide)).symm.trans contract89014_1

theorem c89014_2 : P.sumLeaves 26 91150912 448 = 11049528 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89014) (lo := 576) (len := 448) (W := 11049528) check rows elimOK (by decide) (by decide) cover89014 (by decide)
  decide +kernel

theorem h89014 : P.leaf 36 89014 = 11263224 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(512, 0), (64, 213696), (448, 11049528)]) (.cons c89014_0 (.cons c89014_1 (.cons c89014_2 (.nil)))) (by decide) (by decide))

theorem cover89015 : P.CoversSplit 26 10 89015 0xcc00cc0000000000cc00cc0000000000cc00cc0000000000c800c80000000000cc00c00000000000c800c00000000000cc00c00000000000c800c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 538, 922, 972, 979, 1315, 1658]) (by decide +kernel)

theorem c89015_0 : P.sumLeaves 26 91151360 1024 = 68153292 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89015) (lo := 0) (len := 1024) (W := 68153292) check rows elimOK (by decide) (by decide) cover89015 (by decide)
  decide +kernel

theorem h89015 : P.leaf 36 89015 = 68153292 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 68153292)]) (.cons c89015_0 (.nil)) (by decide) (by decide))

theorem cover89018 : P.CoversSplit 26 10 89018 0xf0f0f0f000000000f0f0f0f500000000f0f0f0f000000030f0f0f0f000000000000000000000000000005050000000000000000000000000000050500000000000000000000000000000000000000000003000300000000000300030000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 874, 972, 979, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f89018 (i : ℕ) := rowWeight keep4 twice4 i * P.leaf 26 (91154432 + i)

theorem c89018_0 : rowSum f89018 0 1024 = 4638636 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 89018) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover89018 (by decide)
  decide +kernel

theorem sum89018 : rowSum f89018 0 1024 = 4638636 :=
  c89018_0

theorem h89018 : P.leaf 36 89018 = 4638636 :=
  leaf_weighted (k := 26) (d := 10) (H := 89018) (keep := keep4) (twice := twice4) rows (by decide) (by decide) bal4 (invRow4 (H := 89018) (by decide) (by decide +kernel)) sum89018

theorem cover89019 : P.CoversSplit 26 10 89019 0xf0f0f0f000000000f0f0f0f500000000f0f0f0f000000030f0f0f0f000000000000000000000000000005050000000000000000000000000000050500000000000000000000000000000000000000000003000300000000000300030000000000000000000000000000000000000000000000000000000000000001000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 922, 972, 979, 1273, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f89019 (i : ℕ) := rowWeight keep4 twice4 i * P.leaf 26 (91155456 + i)

theorem c89019_0 : rowSum f89019 0 1024 = 55588634 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 89019) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover89019 (by decide)
  decide +kernel

theorem sum89019 : rowSum f89019 0 1024 = 55588634 :=
  c89019_0

theorem h89019 : P.leaf 36 89019 = 55588634 :=
  leaf_weighted (k := 26) (d := 10) (H := 89019) (keep := keep4) (twice := twice4) rows (by decide) (by decide) bal4 (invRow4 (H := 89019) (by decide) (by decide +kernel)) sum89019

theorem cover89020 : P.CoversSplit 26 10 89020 0xffffffff00000000fffffffa00000000ffffffff00000030fafafafa00000000fffff0f000000000f0f0f0f000000000fffff0f000000030f0f0f0f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [538, 874, 922, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c89020_0 : P.sumLeaves 26 91156480 512 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89020) (lo := 0) (len := 512) (W := 0) check rows elimOK (by decide) (by decide) cover89020 (by decide)
  decide +kernel

theorem contract89020_1 : P.leaf 32 1424328 = 32720 := by
  exact leaf_contract_factors (k := 32) (b := 19) (H := 1424328) (ss := [(15, 1, 472), (2, 1, 474), (3, 1, 531), (14, 1, 866), (8, 1, 517), (18, 1, 517), (10, 1, 867), (11, 1, 817), (12, 1, 817), (19, 1, 865), (20, 1, 915), (30, 1, 922), (16, 1, 1210)]) (ids := [2, 3, 4, 5, 7, 11, 15, 19, 20, 21, 24, 25, 26, 27, 29, 30, 31, 22, 23]) (cs := [1, 1, 2, 3, 4, 5, 1, 6, 1, 1, 1, 7, 1, 1, 1, 8, 1, 1, 1, 9, 10, 11, 19, 20, 12, 13, 14, 15, 1, 16, 17, 18]) (bs := [17, 2]) (W := 32720) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c89020_1 : P.sumLeaves 26 91156992 64 = 32720 :=
  (leaf_eq_inner (k := 26) (d := 6) (H := 1424328) rows (by decide) (by decide)).symm.trans contract89020_1

theorem c89020_2 : P.sumLeaves 26 91157056 292 = 882004 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89020) (lo := 576) (len := 292) (W := 882004) check rows elimOK (by decide) (by decide) cover89020 (by decide)
  decide +kernel

theorem c89020_3 : P.sumLeaves 26 91157348 156 = 3411608 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89020) (lo := 868) (len := 156) (W := 3411608) check rows elimOK (by decide) (by decide) cover89020 (by decide)
  decide +kernel

theorem h89020 : P.leaf 36 89020 = 4326332 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(512, 0), (64, 32720), (292, 882004), (156, 3411608)]) (.cons c89020_0 (.cons c89020_1 (.cons c89020_2 (.cons c89020_3 (.nil))))) (by decide) (by decide))

theorem cover89021 : P.CoversSplit 26 10 89021 0xffffffff00000000fffffffa00000000ffffffff00000030fafafafa00000000fffff0f000000000f0f0f0f000000000fffff0f000000030f0f0f0f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [538, 922, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c89021_0 : P.sumLeaves 26 91157504 820 = 4148714 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89021) (lo := 0) (len := 820) (W := 4148714) check rows elimOK (by decide) (by decide) cover89021 (by decide)
  decide +kernel

theorem c89021_1 : P.sumLeaves 26 91158324 194 = 15392240 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89021) (lo := 820) (len := 194) (W := 15392240) check rows elimOK (by decide) (by decide) cover89021 (by decide)
  decide +kernel

theorem c89021_2 : P.sumLeaves 26 91158518 10 = 2622240 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89021) (lo := 1014) (len := 10) (W := 2622240) check rows elimOK (by decide) (by decide) cover89021 (by decide)
  decide +kernel

theorem h89021 : P.leaf 36 89021 = 22163194 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(820, 4148714), (194, 15392240), (10, 2622240)]) (.cons c89021_0 (.cons c89021_1 (.cons c89021_2 (.nil)))) (by decide) (by decide))

theorem cover89022 : P.CoversSplit 26 10 89022 0xffffffff00000000fffffffa00000000ffffffff00000030fafafafa00000000fffff0f000000000fafaf0f000000000fffff0f000000030fafaf0f00000000000000000000000000000000000000000003300330000000000320032000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [538, 874, 922, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c89022_0 : P.sumLeaves 26 91158528 760 = 17700151 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89022) (lo := 0) (len := 760) (W := 17700151) check rows elimOK (by decide) (by decide) cover89022 (by decide)
  decide +kernel

theorem c89022_1 : P.sumLeaves 26 91159288 232 = 33380865 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89022) (lo := 760) (len := 232) (W := 33380865) check rows elimOK (by decide) (by decide) cover89022 (by decide)
  decide +kernel

theorem c89022_2 : P.sumLeaves 26 91159520 32 = 27183908 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89022) (lo := 992) (len := 32) (W := 27183908) check rows elimOK (by decide) (by decide) cover89022 (by decide)
  decide +kernel

theorem h89022 : P.leaf 36 89022 = 78264924 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(760, 17700151), (232, 33380865), (32, 27183908)]) (.cons c89022_0 (.cons c89022_1 (.cons c89022_2 (.nil)))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(88990, 720), (88991, 720), (88999, 720), (89001, 360), (89003, 720), (89005, 720), (89007, 720), (89012, 360), (89013, 720), (89014, 720), (89015, 720), (89018, 360), (89019, 360), (89020, 720), (89021, 720), (89022, 720)]

theorem segOK : checkSeg 20 perms 88990 89023 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 88990 89023 10080 253488308400 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 253488308400)
    (SegSum.cons (w := 720) h88990 (SegSum.cons (w := 720) h88991 (SegSum.cons (w := 720) h88999 (SegSum.cons (w := 360) h89001 (SegSum.cons (w := 720) h89003 (SegSum.cons (w := 720) h89005 (SegSum.cons (w := 720) h89007 (SegSum.cons (w := 360) h89012 (SegSum.cons (w := 720) h89013 (SegSum.cons (w := 720) h89014 (SegSum.cons (w := 720) h89015 (SegSum.cons (w := 360) h89018 (SegSum.cons (w := 360) h89019 (SegSum.cons (w := 720) h89020 (SegSum.cons (w := 720) h89021 (SegSum.cons (w := 720) h89022 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))) (by decide)

end RACert.S6N0.C0.S59
