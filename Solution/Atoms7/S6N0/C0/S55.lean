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

namespace RACert.S6N0.C0.S55

open RACert RACert.Problem

theorem cover110971 : P.CoversSplit 26 10 110971 0xa0a00000a0a00000a0a00000a0a0000000000000000000000000000000a00000000000000000000000000000000000000000000000000000000000000000000000000000008000000000000000800000000000000080000000000000008000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 579, 629, 636, 930, 1266, 1315, 1665]) (by decide +kernel)

theorem h110971 : P.leaf 36 110971 = 12915580 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 110971) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 110971) (weight := fun _ => 1) (xs := [279, 343, 407, 471, 789, 791, 917, 919, 925, 927, 949, 951, 957, 959, 981, 983, 989, 991, 1013, 1015, 1021, 1023]) check rows elimOK (by decide) (by decide) cover110971 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h88990 : P.leaf 36 88990 = 12915580 :=
  orient72 (v := 110971) (by decide) (by decide +kernel) h110971

theorem cover110975 : P.CoversSplit 26 10 110975 0xffff0000ffee0504ffff0000ffee040400000000000000000000000000aa000000000000000000000000000000000000000000000000000000000000000000000000000000cc00040000000000cc00040000000000cc000400000000008800000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [579, 629, 636, 873, 930, 1266, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c110975_0 : P.sumLeaves 26 113638400 1024 = 65128389 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 110975) (lo := 0) (len := 1024) (W := 65128389) check rows elimOK (by decide) (by decide) cover110975 (by decide)
  decide +kernel

theorem h110975 : P.leaf 36 110975 = 65128389 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 65128389)]) (.cons c110975_0 (.nil)) (by decide) (by decide))

theorem h88991 : P.leaf 36 88991 = 65128389 :=
  orient72 (v := 110975) (by decide) (by decide +kernel) h110975

theorem cover104343 : P.CoversSplit 26 10 104343 0xc000000000000000c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c000000000000000c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 538, 873, 930, 1273, 1315, 1658]) (by decide +kernel)

theorem h104343 : P.leaf 36 104343 = 7550600 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 104343) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 104343) (weight := fun _ => 1) (xs := [446, 447, 510, 511, 958, 959, 1022, 1023]) check rows elimOK (by decide) (by decide) cover104343 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h88999 : P.leaf 36 88999 = 7550600 :=
  orient4 (v := 104343) (by decide) (by decide +kernel) h104343

theorem cover104345 : P.CoversSplit 26 10 104345 0xf0f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000f0f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 537, 873, 922, 965, 1315]) (by decide +kernel)

theorem h104345 : P.leaf 36 104345 = 2684026 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 104345) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 104345) (weight := fun _ => 1) (xs := [500, 501, 502, 503, 508, 509, 510, 511, 1012, 1013, 1014, 1015, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover104345 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h89001 : P.leaf 36 89001 = 2684026 :=
  orient4 (v := 104345) (by decide) (by decide +kernel) h104345

theorem cover276423 : P.CoversSplit 26 10 276423 0xf0000000f0000000000000000000000000000000000000000000000000000000f0000000f0000000000000000000000000000000000000000000000000000000f0000000f0300000000000000000000000000000000000000000000000000000f0000000f0300000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 873, 930, 1265, 1308, 1658]) (by decide +kernel)

theorem c276423_0 : P.sumLeaves 26 283057152 1024 = 7321098 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 276423) (lo := 0) (len := 1024) (W := 7321098) check rows elimOK (by decide) (by decide) cover276423 (by decide)
  decide +kernel

theorem h276423 : P.leaf 36 276423 = 7321098 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 7321098)]) (.cons c276423_0 (.nil)) (by decide) (by decide))

theorem h89003 : P.leaf 36 89003 = 7321098 :=
  orient6 (v := 276423) (by decide) (by decide +kernel) h276423

theorem cover104347 : P.CoversSplit 26 10 104347 0xf0f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000f0f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 537, 873, 922, 929, 1315]) (by decide +kernel)

theorem h104347 : P.leaf 36 104347 = 6137686 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 104347) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 104347) (weight := fun _ => 1) (xs := [500, 501, 502, 503, 508, 509, 510, 511, 1012, 1013, 1014, 1015, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover104347 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h89005 : P.leaf 36 89005 = 6137686 :=
  orient4 (v := 104347) (by decide) (by decide +kernel) h104347

theorem cover104351 : P.CoversSplit 26 10 104351 0xf0f0000000000000f0f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000f0f0000000300000f0f0000000300000003000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 538, 873, 1273, 1315, 1658]) (by decide +kernel)

theorem c104351_0 : P.sumLeaves 26 106855424 1024 = 34778740 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 104351) (lo := 0) (len := 1024) (W := 34778740) check rows elimOK (by decide) (by decide) cover104351 (by decide)
  decide +kernel

theorem h104351 : P.leaf 36 104351 = 34778740 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 34778740)]) (.cons c104351_0 (.nil)) (by decide) (by decide))

theorem h89007 : P.leaf 36 89007 = 34778740 :=
  orient4 (v := 104351) (by decide) (by decide +kernel) h104351

theorem cover304595 : P.CoversSplit 26 10 304595 0x8800000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 488, 489, 530, 629, 636, 881, 930, 958, 1265, 1665]) (by decide +kernel)

theorem h304595 : P.leaf 36 304595 = 291776 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 304595) (keep := keep18) (twice := twice18) rows (by decide) (by decide) bal18 (invRow18 (H := 304595) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 304595) (weight := rowWeight keep18 twice18) (xs := [991, 1019, 1023]) check rows elimOK (by decide) (by decide) cover304595 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h89012 : P.leaf 36 89012 = 291776 :=
  orient84 (v := 304595) (by decide) (by decide +kernel) h304595

theorem cover104371 : P.CoversSplit 26 10 104371 0xc000000000000000000000000000000000000000000000000000000000000000c000000000000000000000000000000000000000000000000000000000000000c000000000000000000000000000000000000000000000000000000000000000c000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 538, 608, 873, 922, 929, 930, 1658]) (by decide +kernel)

theorem h104371 : P.leaf 36 104371 = 2462500 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 104371) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 104371) (weight := fun _ => 1) (xs := [254, 255, 510, 511, 766, 767, 1022, 1023]) check rows elimOK (by decide) (by decide) cover104371 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h89013 : P.leaf 36 89013 = 2462500 :=
  orient4 (v := 104371) (by decide) (by decide +kernel) h104371

theorem cover111091 : P.CoversSplit 26 10 111091 0x8800000088000000880000008800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 629, 636, 930, 1266, 1273, 1315]) (by decide +kernel)

theorem h111091 : P.leaf 36 111091 = 11263224 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 111091) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 111091) (weight := fun _ => 1) (xs := [923, 927, 955, 959, 987, 991, 1019, 1023]) check rows elimOK (by decide) (by decide) cover111091 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h89014 : P.leaf 36 89014 = 11263224 :=
  orient72 (v := 111091) (by decide) (by decide +kernel) h111091

theorem cover111095 : P.CoversSplit 26 10 111095 0xcc000000cc000400cc000000cc00040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 629, 636, 873, 930, 1266, 1315]) (by decide +kernel)

theorem h111095 : P.leaf 36 111095 = 68153292 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 111095) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 111095) (weight := fun _ => 1) (xs := [906, 922, 923, 926, 927, 954, 955, 958, 959, 970, 986, 987, 990, 991, 1018, 1019, 1022, 1023]) check rows elimOK (by decide) (by decide) cover111095 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h89015 : P.leaf 36 89015 = 68153292 :=
  orient72 (v := 111095) (by decide) (by decide +kernel) h111095

theorem cover798943 : P.CoversSplit 26 10 798943 0x8000000080000000800000008000000000000000000000000000000000000000800000008000000084000000840000000000000000000000000000000000000080000000802000008000000080200000000000000000000000000000000000008000000080000000800000008000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [530, 587, 629, 636, 867, 872, 873, 930]) (ps := [(14, [874, 880], [873]), (15, [923], [930])]) (by decide +kernel)

theorem h798943 : P.leaf 36 798943 = 4638636 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 798943) (keep := keep2) (twice := twice2) rows (by decide) (by decide) bal2 (invRow2 (H := 798943) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 798943) (weight := rowWeight keep2 twice2) (xs := [159, 191, 223, 255, 405, 415, 447, 469, 479, 511, 666, 671, 698, 703, 735, 767, 927, 959, 991, 1023]) check rows elimOK (by decide) (by decide) cover798943 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h89018 : P.leaf 36 89018 = 4638636 :=
  orient324 (v := 798943) (by decide) (by decide +kernel) h798943

theorem cover89019 : P.CoversSplit 26 10 89019 0xf0f0f0f000000000f0f0f0f500000000f0f0f0f000000030f0f0f0f000000000000000000000000000005050000000000000000000000000000050500000000000000000000000000000000000000000003000300000000000300030000000000000000000000000000000000000000000000000000000000000001000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 922, 972, 979, 1273, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f89019 (i : ℕ) := rowWeight keep4 twice4 i * P.leaf 26 (91155456 + i)

theorem c89019_0 : rowSum f89019 0 1024 = 55588634 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 89019) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover89019 (by decide)
  decide +kernel

theorem sum89019 : rowSum f89019 0 1024 = 55588634 :=
  c89019_0

theorem h89019 : P.leaf 36 89019 = 55588634 :=
  leaf_weighted (k := 26) (d := 10) (H := 89019) (keep := keep4) (twice := twice4) rows (by decide) (by decide) (bal4) (invRow4 (H := 89019) (by decide) (by decide +kernel)) sum89019

theorem cover289651 : P.CoversSplit 26 10 289651 0xaa00aa00000000000000000000000000aa00aa00000000000000000000000000000005000000000000000000000000000000050000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 488, 579, 881, 972, 979, 1273, 1658]) (by decide +kernel)

theorem h289651 : P.leaf 36 289651 = 4326332 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 289651) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 289651) (weight := fun _ => 1) (xs := [616, 618, 744, 746, 873, 875, 877, 879, 889, 891, 893, 895, 1001, 1003, 1005, 1007, 1017, 1019, 1021, 1023]) check rows elimOK (by decide) (by decide) cover289651 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h89020 : P.leaf 36 89020 = 4326332 :=
  orient80 (v := 289651) (by decide) (by decide +kernel) h289651

theorem cover104379 : P.CoversSplit 26 10 104379 0xf0f0000000000000000000000000000000000000000000000000000000000000f0f0000000000000000000000000000000000000000000000000000000000000f0f0000000300000000000000000000000000000000000000000000000000000f0f0000000300000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 873, 922, 929, 1273, 1658]) (by decide +kernel)

theorem c104379_0 : P.sumLeaves 26 106884096 1024 = 22163194 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 104379) (lo := 0) (len := 1024) (W := 22163194) check rows elimOK (by decide) (by decide) cover104379 (by decide)
  decide +kernel

theorem h104379 : P.leaf 36 104379 = 22163194 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 22163194)]) (.cons c104379_0 (.nil)) (by decide) (by decide))

theorem h89021 : P.leaf 36 89021 = 22163194 :=
  orient4 (v := 104379) (by decide) (by decide +kernel) h104379

theorem cover111099 : P.CoversSplit 26 10 111099 0xaaaa0000aaaa0000aaaa0000aaaa010100000000000000000000000000220000000000000000000000000000000000000000000000000000000000000000000000000000002200000000000000220001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 629, 636, 930, 1266, 1315, 1665]) (by decide +kernel)

theorem c111099_0 : P.sumLeaves 26 113765376 1024 = 78264924 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 111099) (lo := 0) (len := 1024) (W := 78264924) check rows elimOK (by decide) (by decide) cover111099 (by decide)
  decide +kernel

theorem h111099 : P.leaf 36 111099 = 78264924 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 78264924)]) (.cons c111099_0 (.nil)) (by decide) (by decide))

theorem h89022 : P.leaf 36 89022 = 78264924 :=
  orient72 (v := 111099) (by decide) (by decide +kernel) h111099

theorem cover111103 : P.CoversSplit 26 10 111103 0xffff0000ffff0505ffff0000ffff040400000000000000000000000000220000000000000000000000000000000000000000000000000000000000000000000000000000003300010000000000330000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [629, 636, 873, 930, 1266, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c111103_0 : P.sumLeaves 26 113769472 1024 = 355439630 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 111103) (lo := 0) (len := 1024) (W := 355439630) check rows elimOK (by decide) (by decide) cover111103 (by decide)
  decide +kernel

theorem h111103 : P.leaf 36 111103 = 355439630 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 355439630)]) (.cons c111103_0 (.nil)) (by decide) (by decide))

theorem h89023 : P.leaf 36 89023 = 355439630 :=
  orient72 (v := 111103) (by decide) (by decide +kernel) h111103

theorem cover289237 : P.CoversSplit 26 10 289237 0xaa00aa0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 629, 636, 881, 929, 972, 979, 1265, 1273, 1658, 1665]) (by decide +kernel)

theorem h289237 : P.leaf 36 289237 = 1488936 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 289237) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 289237) (weight := fun _ => 1) (xs := [1001, 1003, 1005, 1007, 1017, 1019, 1021, 1023]) check rows elimOK (by decide) (by decide) cover289237 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h89029 : P.leaf 36 89029 = 1488936 :=
  orient80 (v := 289237) (by decide) (by decide +kernel) h289237

theorem cover289241 : P.CoversSplit 26 10 289241 0xaa000000aa000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 629, 636, 881, 923, 979, 1273, 1658, 1665]) (by decide +kernel)

theorem h289241 : P.leaf 36 289241 = 1487300 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 289241) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 289241) (weight := fun _ => 1) (xs := [985, 987, 989, 991, 1017, 1019, 1021, 1023]) check rows elimOK (by decide) (by decide) cover289241 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h89030 : P.leaf 36 89030 = 1487300 :=
  orient80 (v := 289241) (by decide) (by decide +kernel) h289241

theorem cover289245 : P.CoversSplit 26 10 289245 0xaa00aa00aa00aa00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 629, 636, 881, 923, 972, 979, 1265, 1273, 1658, 1665]) (by decide +kernel)

theorem h289245 : P.leaf 36 289245 = 14280416 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 289245) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 289245) (weight := fun _ => 1) (xs := [969, 971, 973, 975, 985, 987, 989, 991, 1001, 1003, 1005, 1007, 1017, 1019, 1021, 1023]) check rows elimOK (by decide) (by decide) cover289245 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h89031 : P.leaf 36 89031 = 14280416 :=
  orient80 (v := 289245) (by decide) (by decide +kernel) h289245

theorem cover289239 : P.CoversSplit 26 10 289239 0xaa00aa0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 629, 636, 881, 929, 972, 979, 1265, 1273, 1658, 1665]) (by decide +kernel)

theorem h289239 : P.leaf 36 289239 = 4550568 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 289239) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 289239) (weight := fun _ => 1) (xs := [1001, 1003, 1005, 1007, 1017, 1019, 1021, 1023]) check rows elimOK (by decide) (by decide) cover289239 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h89037 : P.leaf 36 89037 = 4550568 :=
  orient80 (v := 289239) (by decide) (by decide +kernel) h289239

theorem cover289243 : P.CoversSplit 26 10 289243 0xaa000000aa000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 629, 636, 881, 923, 979, 1273, 1658, 1665]) (by decide +kernel)

theorem h289243 : P.leaf 36 289243 = 6575688 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 289243) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 289243) (weight := fun _ => 1) (xs := [985, 987, 989, 991, 1017, 1019, 1021, 1023]) check rows elimOK (by decide) (by decide) cover289243 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h89038 : P.leaf 36 89038 = 6575688 :=
  orient80 (v := 289243) (by decide) (by decide +kernel) h289243

theorem cover289247 : P.CoversSplit 26 10 289247 0xaa00aa00aa00aa00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 629, 636, 881, 923, 972, 979, 1265, 1273, 1658, 1665]) (by decide +kernel)

theorem h289247 : P.leaf 36 289247 = 30069648 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 289247) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 289247) (weight := fun _ => 1) (xs := [969, 971, 973, 975, 985, 987, 989, 991, 1001, 1003, 1005, 1007, 1017, 1019, 1021, 1023]) check rows elimOK (by decide) (by decide) cover289247 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h89039 : P.leaf 36 89039 = 30069648 :=
  orient80 (v := 289247) (by decide) (by decide +kernel) h289247

theorem cover89046 : P.CoversSplit 26 10 89046 0xff000000ff030501ff000000ff030500ff000000ff030500fa000000c8000000050005000501050100000000000000000500050005010500000000000000000000000000333301010000000033330100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 874, 922, 972, 979, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f89046 (i : ℕ) := rowWeight keep4 twice4 i * P.leaf 26 (91183104 + i)

theorem c89046_0 : rowSum f89046 0 1024 = 75966616 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 89046) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover89046 (by decide)
  decide +kernel

theorem sum89046 : rowSum f89046 0 1024 = 75966616 :=
  c89046_0

theorem h89046 : P.leaf 36 89046 = 75966616 :=
  leaf_weighted (k := 26) (d := 10) (H := 89046) (keep := keep4) (twice := twice4) rows (by decide) (by decide) (bal4) (invRow4 (H := 89046) (by decide) (by decide +kernel)) sum89046

theorem cover89047 : P.CoversSplit 26 10 89047 0xff000000ff030501ff000000ff030500ff000000ff030500fa000000c8000000050005000501050100000000000000000500050005010500000000000000000000000000333301010000000033330100000000000000000000000000000000000000000001010101000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 922, 972, 979, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f89047 (i : ℕ) := rowWeight keep4 twice4 i * P.leaf 26 (91184128 + i)

theorem c89047_0 : rowSum f89047 0 1024 = 169810808 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 89047) (keep := keep4) (twice := twice4) check rows elimOK (by decide) (by decide) cover89047 (by decide)
  decide +kernel

theorem sum89047 : rowSum f89047 0 1024 = 169810808 :=
  c89047_0

theorem h89047 : P.leaf 36 89047 = 169810808 :=
  leaf_weighted (k := 26) (d := 10) (H := 89047) (keep := keep4) (twice := twice4) rows (by decide) (by decide) (bal4) (invRow4 (H := 89047) (by decide) (by decide +kernel)) sum89047

theorem cover539130 : P.CoversSplit 26 10 539130 0xff00000000000000ff00000000000000ff00000000000000ff00000000000000050000000000000000000000000000000500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 629, 636, 874, 930, 972, 979, 1265, 1273, 1315, 1322]) (by decide +kernel)

theorem c539130_0 : P.sumLeaves 26 552069120 1024 = 18748760 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 539130) (lo := 0) (len := 1024) (W := 18748760) check rows elimOK (by decide) (by decide) cover539130 (by decide)
  decide +kernel

theorem h539130 : P.leaf 36 539130 = 18748760 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 18748760)]) (.cons c539130_0 (.nil)) (by decide) (by decide))

theorem h89052 : P.leaf 36 89052 = 18748760 :=
  orient92 (v := 539130) (by decide) (by decide +kernel) h539130

theorem cover539134 : P.CoversSplit 26 10 539134 0xff00000000000000ff00000000000000ff00000000000000ff00000000000000050000000000000005000000000000000500000000000000050000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [629, 636, 874, 930, 972, 979, 1265, 1273, 1315, 1322]) (by decide +kernel)

theorem c539134_0 : P.sumLeaves 26 552073216 1024 = 54869694 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 539134) (lo := 0) (len := 1024) (W := 54869694) check rows elimOK (by decide) (by decide) cover539134 (by decide)
  decide +kernel

theorem h539134 : P.leaf 36 539134 = 54869694 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 54869694)]) (.cons c539134_0 (.nil)) (by decide) (by decide))

theorem h89053 : P.leaf 36 89053 = 54869694 :=
  orient92 (v := 539134) (by decide) (by decide +kernel) h539134

theorem cover304635 : P.CoversSplit 26 10 304635 0xfffffffff0f0f0f0fffffafaf0f0f0f000000000000000000022002200000000fffffffff0f0f0f0aaaaaaaaa0a0a0a00000000000000000002200220000000000330033003000300033003200300030003300330000000000220022000000000033003300300030002200220020002000330033000000000022002200000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 629, 636, 873, 881, 958, 1658, 1665]) (by decide +kernel)

theorem c304635_0 : P.sumLeaves 26 311946240 711 = 42728438 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 304635) (lo := 0) (len := 711) (W := 42728438) check rows elimOK (by decide) (by decide) cover304635 (by decide)
  decide +kernel

theorem c304635_1 : P.sumLeaves 26 311946951 256 = 139650354 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 304635) (lo := 711) (len := 256) (W := 139650354) check rows elimOK (by decide) (by decide) cover304635 (by decide)
  decide +kernel

theorem c304635_2 : P.sumLeaves 26 311947207 57 = 101760593 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 304635) (lo := 967) (len := 57) (W := 101760593) check rows elimOK (by decide) (by decide) cover304635 (by decide)
  decide +kernel

theorem h304635 : P.leaf 36 304635 = 284139385 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(711, 42728438), (256, 139650354), (57, 101760593)]) (.cons c304635_0 (.cons c304635_1 (.cons c304635_2 (.nil)))) (by decide) (by decide))

theorem h89054 : P.leaf 36 89054 = 284139385 :=
  orient74 (v := 304635) (by decide) (by decide +kernel) h304635

theorem cover89055 : P.CoversSplit 26 10 89055 0xffff0000fffc0504ffff0000fffc0500ffff0000fffc0500fafa0000c8c800000505050505040504000000000000000005050505050405000000000000000000ffff0000ffcc0504ffff0000ffcc0500ffff0000cc000400fafa0000c80000000505050505040504000000000000000005050505040004000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 922, 972, 979, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c89055_0 : P.sumLeaves 26 91192320 471 = 106796582 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89055) (lo := 0) (len := 471) (W := 106796582) check rows elimOK (by decide) (by decide) cover89055 (by decide)
  decide +kernel

theorem c89055_1 : P.sumLeaves 26 91192791 419 = 223059646 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89055) (lo := 471) (len := 419) (W := 223059646) check rows elimOK (by decide) (by decide) cover89055 (by decide)
  decide +kernel

theorem c89055_2 : P.sumLeaves 26 91193210 134 = 355650618 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 89055) (lo := 890) (len := 134) (W := 355650618) check rows elimOK (by decide) (by decide) cover89055 (by decide)
  decide +kernel

theorem h89055 : P.leaf 36 89055 = 685506846 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(471, 106796582), (419, 223059646), (134, 355650618)]) (.cons c89055_0 (.cons c89055_1 (.cons c89055_2 (.nil)))) (by decide) (by decide))

theorem cover289271 : P.CoversSplit 26 10 289271 0xff00ff0000000000000000000000000000000000000000000000000000000000050005000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 629, 636, 881, 929, 972, 979, 1265, 1273, 1658, 1665]) (by decide +kernel)

theorem h289271 : P.leaf 36 289271 = 12914842 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 289271) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 289271) (weight := fun _ => 1) (xs := [744, 746, 760, 762, 1000, 1001, 1002, 1003, 1004, 1005, 1006, 1007, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover289271 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h89069 : P.leaf 36 89069 = 12914842 :=
  orient80 (v := 289271) (by decide) (by decide +kernel) h289271

theorem cover289275 : P.CoversSplit 26 10 289275 0xff00ff00ff00ff00000000000000000000000000000000000000000000000000050005000500050000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 629, 636, 881, 923, 972, 979, 1265, 1273, 1658, 1665]) (by decide +kernel)

theorem c289275_0 : P.sumLeaves 26 296217600 1024 = 44040110 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 289275) (lo := 0) (len := 1024) (W := 44040110) check rows elimOK (by decide) (by decide) cover289275 (by decide)
  decide +kernel

theorem h289275 : P.leaf 36 289275 = 44040110 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 44040110)]) (.cons c289275_0 (.nil)) (by decide) (by decide))

theorem h89070 : P.leaf 36 89070 = 44040110 :=
  orient80 (v := 289275) (by decide) (by decide +kernel) h289275

theorem cover289279 : P.CoversSplit 26 10 289279 0xff00ff00ff00ff00000000000000000000000000000000000000000000000000050005000500050000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [629, 636, 881, 923, 972, 979, 1265, 1273, 1658, 1665]) (by decide +kernel)

theorem c289279_0 : P.sumLeaves 26 296221696 1024 = 121550328 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 289279) (lo := 0) (len := 1024) (W := 121550328) check rows elimOK (by decide) (by decide) cover289279 (by decide)
  decide +kernel

theorem h289279 : P.leaf 36 289279 = 121550328 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 121550328)]) (.cons c289279_0 (.nil)) (by decide) (by decide))

theorem h89071 : P.leaf 36 89071 = 121550328 :=
  orient80 (v := 289279) (by decide) (by decide +kernel) h289279

def seg : List (ℕ × ℕ) := [(88990, 720), (88991, 720), (88999, 720), (89001, 360), (89003, 720), (89005, 720), (89007, 720), (89012, 360), (89013, 720), (89014, 720), (89015, 720), (89018, 360), (89019, 360), (89020, 720), (89021, 720), (89022, 720), (89023, 720), (89029, 360), (89030, 720), (89031, 720), (89037, 720), (89038, 720), (89039, 720), (89046, 360), (89047, 360), (89052, 720), (89053, 720), (89054, 720), (89055, 720), (89069, 360), (89070, 720), (89071, 720)]

theorem segOK : checkSeg 20 perms 88990 89086 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 88990 89086 20160 1514459569680 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 1514459569680)
    (SegSum.cons (w := 720) h88990 (SegSum.cons (w := 720) h88991 (SegSum.cons (w := 720) h88999 (SegSum.cons (w := 360) h89001 (SegSum.cons (w := 720) h89003 (SegSum.cons (w := 720) h89005 (SegSum.cons (w := 720) h89007 (SegSum.cons (w := 360) h89012 (SegSum.cons (w := 720) h89013 (SegSum.cons (w := 720) h89014 (SegSum.cons (w := 720) h89015 (SegSum.cons (w := 360) h89018 (SegSum.cons (w := 360) h89019 (SegSum.cons (w := 720) h89020 (SegSum.cons (w := 720) h89021 (SegSum.cons (w := 720) h89022 (SegSum.cons (w := 720) h89023 (SegSum.cons (w := 360) h89029 (SegSum.cons (w := 720) h89030 (SegSum.cons (w := 720) h89031 (SegSum.cons (w := 720) h89037 (SegSum.cons (w := 720) h89038 (SegSum.cons (w := 720) h89039 (SegSum.cons (w := 360) h89046 (SegSum.cons (w := 360) h89047 (SegSum.cons (w := 720) h89052 (SegSum.cons (w := 720) h89053 (SegSum.cons (w := 720) h89054 (SegSum.cons (w := 720) h89055 (SegSum.cons (w := 360) h89069 (SegSum.cons (w := 720) h89070 (SegSum.cons (w := 720) h89071 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S55
