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

namespace RACert.S6N0.C0.S61

open RACert RACert.Problem

theorem cover112122 : P.CoversSplit 26 10 112122 0xaaaa0000aaaa0000aaaa0000aaaa010100000000000000000000000000220000000000000000000000000000000000000000000000000000000000000000000000000000002200000000000000220001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 531, 629, 636, 873, 1315, 1665]) (by decide +kernel)

theorem c112122_0 : P.sumLeaves 26 114812928 1024 = 75141458 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 112122) (lo := 0) (len := 1024) (W := 75141458) check rows elimOK (by decide) (by decide) cover112122 (by decide)
  decide +kernel

theorem h112122 : P.leaf 36 112122 = 75141458 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 75141458)]) (.cons c112122_0 (.nil)) (by decide) (by decide))

theorem h97020 : P.leaf 36 97020 = 75141458 :=
  orient4 (v := 112122) (by decide) (by decide +kernel) h112122

theorem cover112123 : P.CoversSplit 26 10 112123 0xaaaa0000aaaa0000aaaa0000aaaa010100000000000000000000000000220000000000000000000000000000000000000000000000000000000000000000000000000000002200000000000000220001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 629, 636, 1315, 1665]) (by decide +kernel)

theorem c112123_0 : P.sumLeaves 26 114813952 1024 = 149775724 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 112123) (lo := 0) (len := 1024) (W := 149775724) check rows elimOK (by decide) (by decide) cover112123 (by decide)
  decide +kernel

theorem h112123 : P.leaf 36 112123 = 149775724 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 149775724)]) (.cons c112123_0 (.nil)) (by decide) (by decide))

theorem h97021 : P.leaf 36 97021 = 149775724 :=
  orient4 (v := 112123) (by decide) (by decide +kernel) h112123

theorem cover112126 : P.CoversSplit 26 10 112126 0xffff0000ffff0505ffff0000ffff040400000000000000000000000000220000050505050505050500000000000000000000000000000000000000000000000000000000003300010000000000330000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [531, 629, 636, 873, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c112126_0 : P.sumLeaves 26 114817024 1023 = 315511514 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 112126) (lo := 0) (len := 1023) (W := 315511514) check rows elimOK (by decide) (by decide) cover112126 (by decide)
  decide +kernel

theorem c112126_1 : P.sumLeaves 26 114818047 1 = 8904784 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 112126) (lo := 1023) (len := 1) (W := 8904784) check rows elimOK (by decide) (by decide) cover112126 (by decide)
  decide +kernel

theorem h112126 : P.leaf 36 112126 = 324416298 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1023, 315511514), (1, 8904784)]) (.cons c112126_0 (.cons c112126_1 (.nil))) (by decide) (by decide))

theorem h97022 : P.leaf 36 97022 = 324416298 :=
  orient4 (v := 112126) (by decide) (by decide +kernel) h112126

theorem cover112127 : P.CoversSplit 26 10 112127 0xffff0000ffff0505ffff0000ffff040400000000000000000000000000220000050505050505050500000000000000000000000000000000000000000000000000000000003300010000000000330000000000000000000000000000000000000000000000010001000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [629, 636, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c112127_0 : P.sumLeaves 26 114818048 1021 = 570072247 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 112127) (lo := 0) (len := 1021) (W := 570072247) check rows elimOK (by decide) (by decide) cover112127 (by decide)
  decide +kernel

theorem c112127_1 : P.sumLeaves 26 114819069 3 = 35857392 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 112127) (lo := 1021) (len := 3) (W := 35857392) check rows elimOK (by decide) (by decide) cover112127 (by decide)
  decide +kernel

theorem h112127 : P.leaf 36 112127 = 605929639 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1021, 570072247), (3, 35857392)]) (.cons c112127_0 (.cons c112127_1 (.nil))) (by decide) (by decide))

theorem h97023 : P.leaf 36 97023 = 605929639 :=
  orient4 (v := 112127) (by decide) (by decide +kernel) h112127

theorem cover97091 : P.CoversSplit 26 10 97091 0xa0000000a00000000000000000000000a0000000a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 523, 530, 579, 608, 972, 979, 1266, 1273]) (by decide +kernel)

theorem h97091 : P.leaf 36 97091 = 1145320 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 97091) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 97091) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 97091) (weight := rowWeight keep1 twice1) (xs := [861, 863, 893, 895, 989, 991, 1021, 1023]) check rows elimOK (by decide) (by decide) cover97091 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover308637 : P.CoversSplit 26 10 308637 0x8888000000000000040404040000000000000000000000000000000000000000888800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 531, 629, 930, 1265, 1272, 1273, 1665]) (by decide +kernel)

theorem h308637 : P.leaf 36 308637 = 5899608 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 308637) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 308637) (weight := fun _ => 1) (xs := [755, 759, 763, 767, 930, 938, 946, 954, 1011, 1015, 1019, 1023]) check rows elimOK (by decide) (by decide) cover308637 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h97095 : P.leaf 36 97095 = 5899608 :=
  orient6 (v := 308637) (by decide) (by decide +kernel) h308637

theorem cover308631 : P.CoversSplit 26 10 308631 0x8800000000000000040004000000000000000000000000000000000000000000880000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 531, 538, 629, 636, 930, 1265]) (by decide +kernel)

theorem h308631 : P.leaf 36 308631 = 4562654 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 308631) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 308631) (weight := fun _ => 1) (xs := [763, 767, 938, 954, 1019, 1023]) check rows elimOK (by decide) (by decide) cover308631 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h97099 : P.leaf 36 97099 = 4562654 :=
  orient6 (v := 308631) (by decide) (by decide +kernel) h308631

theorem cover308639 : P.CoversSplit 26 10 308639 0x8888000000000000040404040000000000000000000000000000000000000000888800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 531, 629, 1265, 1272, 1273, 1665]) (by decide +kernel)

theorem h308639 : P.leaf 36 308639 = 12893924 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 308639) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 308639) (weight := fun _ => 1) (xs := [755, 759, 763, 767, 930, 938, 946, 954, 1011, 1015, 1019, 1023]) check rows elimOK (by decide) (by decide) cover308639 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h97103 : P.leaf 36 97103 = 12893924 :=
  orient6 (v := 308639) (by decide) (by decide +kernel) h308639

theorem cover97107 : P.CoversSplit 26 10 97107 0xa0000000a00000000000000000000000a0000000a00000000000000000000000000000000000000000000500000005000000000000000000000005000000050000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000400 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 530, 579, 608, 972, 979, 1273, 1315]) (by decide +kernel)

theorem h97107 : P.leaf 36 97107 = 15243180 := by
  apply leaf_weighted (k := 26) (d := 10) (H := 97107) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 97107) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 97107) (weight := rowWeight keep1 twice1) (xs := [10, 351, 520, 522, 552, 554, 648, 650, 680, 682, 861, 863, 893, 895, 989, 991, 1021, 1023]) check rows elimOK (by decide) (by decide) cover97107 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover370121 : P.CoversSplit 26 10 370121 0xaaaaaa00a0a0a00aaaaaaa00a0a0a00a00000000000000000000000000000000000000000000000000000a000000000a0000000000000000000000000000000000000000002000020000000000200002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 580, 629, 636, 873, 881, 930, 958, 1665]) (by decide +kernel)

noncomputable def f370121 (i : ℕ) := rowWeight keep18 twice18 i * P.leaf 26 (379003904 + i)

theorem c370121_0 : rowSum f370121 0 1024 = 2939080 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 370121) (keep := keep18) (twice := twice18) check rows elimOK (by decide) (by decide) cover370121 (by decide)
  decide +kernel

theorem sum370121 : rowSum f370121 0 1024 = 2939080 :=
  c370121_0

theorem h370121 : P.leaf 36 370121 = 2939080 :=
  leaf_weighted (k := 26) (d := 10) (H := 370121) (keep := keep18) (twice := twice18) rows (by decide) (by decide) (bal18) (invRow18 (H := 370121) (by decide) (by decide +kernel)) sum370121

theorem h97108 : P.leaf 36 97108 = 2939080 :=
  orient84 (v := 370121) (by decide) (by decide +kernel) h370121

theorem cover97109 : P.CoversSplit 26 10 97109 0xff000000ff0005000000000000000000ff000000ff0305000500000005000500050005000500050005000000050000000500050005010500050000000500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 579, 923, 972, 979, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c97109_0 : P.sumLeaves 26 99439616 1024 = 58315676 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97109) (lo := 0) (len := 1024) (W := 58315676) check rows elimOK (by decide) (by decide) cover97109 (by decide)
  decide +kernel

theorem h97109 : P.leaf 36 97109 = 58315676 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 58315676)]) (.cons c97109_0 (.nil)) (by decide) (by decide))

theorem cover97111 : P.CoversSplit 26 10 97111 0xff000000ff0005000000000000000000ff000000ff0305000500000005000500050005000500050005000000050000000500050005010500050000000500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 972, 979, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f97111 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 26 (99441664 + i)

theorem c97111_0 : rowSum f97111 0 1024 = 137459282 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 97111) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover97111 (by decide)
  decide +kernel

theorem sum97111 : rowSum f97111 0 1024 = 137459282 :=
  c97111_0

theorem h97111 : P.leaf 36 97111 = 137459282 :=
  leaf_weighted (k := 26) (d := 10) (H := 97111) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 97111) (by decide) (by decide +kernel)) sum97111

theorem cover308659 : P.CoversSplit 26 10 308659 0xcc00cc0000000000cc00c8000000000000000000000000000000000000000000cc00cc000000000088008800000000000000000000000000000000000000000000000000000000000000000000000000000000000033003300000000002200220000000000000000000000000000000000000000003300330000000000220022 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 538, 629, 636, 930]) (by decide +kernel)

noncomputable def f308659 (i : ℕ) := rowWeight keep17 twice17 i * P.leaf 26 (316066816 + i)

theorem c308659_0 : rowSum f308659 0 1024 = 29026773 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 308659) (keep := keep17) (twice := twice17) check rows elimOK (by decide) (by decide) cover308659 (by decide)
  decide +kernel

theorem sum308659 : rowSum f308659 0 1024 = 29026773 :=
  c308659_0

theorem h308659 : P.leaf 36 308659 = 29026773 :=
  leaf_weighted (k := 26) (d := 10) (H := 308659) (keep := keep17) (twice := twice17) rows (by decide) (by decide) (bal17) (invRow17 (H := 308659) (by decide) (by decide +kernel)) sum308659

theorem h97113 : P.leaf 36 97113 = 29026773 :=
  orient6 (v := 308659) (by decide) (by decide +kernel) h308659

theorem cover604414 : P.CoversSplit 26 10 604414 0xcc00cc0000000000cc00cc000000000000000000000000000000000000000000cc00c80000000000cc00c800000000000000000000000000000000000000000000000000000000000000000000000000000000000033003200000000003300320000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [587, 629, 636, 874, 930, 1273]) (by decide +kernel)

noncomputable def f604414 (i : ℕ) := rowWeight keep3 twice3 i * P.leaf 26 (618919936 + i)

theorem c604414_0 : rowSum f604414 0 1024 = 80116446 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 604414) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover604414 (by decide)
  decide +kernel

theorem sum604414 : rowSum f604414 0 1024 = 80116446 :=
  c604414_0

theorem h604414 : P.leaf 36 604414 = 80116446 :=
  leaf_weighted (k := 26) (d := 10) (H := 604414) (keep := keep3) (twice := twice3) rows (by decide) (by decide) (bal3) (invRow3 (H := 604414) (by decide) (by decide +kernel)) sum604414

theorem h97115 : P.leaf 36 97115 = 80116446 :=
  orient87 (v := 604414) (by decide) (by decide +kernel) h604414

theorem cover97116 : P.CoversSplit 26 10 97116 0xffff0000ffff05050000000000000000ffff0000fffc050005050000050005000505050505050505050500000505000005050505050405000505000005000000ffff0000ffff05050000000000000000ffff0000cc00040005050000040004000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 874, 972, 979, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f97116 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 26 (99446784 + i)

theorem c97116_0 : rowSum f97116 0 887 = 29223735 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 97116) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover97116 (by decide)
  decide +kernel

theorem c97116_1 : rowSum f97116 887 137 = 60598777 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 97116) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover97116 (by decide)
  decide +kernel

theorem sum97116 : rowSum f97116 0 1024 = 89822512 :=
  rowSum_append (F := f97116) (lo := 0) (n := 887) (m := 137) (A := 29223735) (B := 60598777) c97116_0 (c97116_1)

theorem h97116 : P.leaf 36 97116 = 89822512 :=
  leaf_weighted (k := 26) (d := 10) (H := 97116) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 97116) (by decide) (by decide +kernel)) sum97116

theorem cover604894 : P.CoversSplit 26 10 604894 0xff00ff0000000000ff00ff000000000000000000000000000000000000000000ff00fa0000000000ff00aa000000000000000000000000000000000000000000ff33ff3233333232ff33ff3233333232333333323300320033333332330032000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 587, 880, 930, 972, 1273, 1315]) (by decide +kernel)

theorem c604894_0 : P.sumLeaves 26 619411456 484 = 41408056 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 604894) (lo := 0) (len := 484) (W := 41408056) check rows elimOK (by decide) (by decide) cover604894 (by decide)
  decide +kernel

theorem c604894_1 : P.sumLeaves 26 619411940 540 = 159204446 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 604894) (lo := 484) (len := 540) (W := 159204446) check rows elimOK (by decide) (by decide) cover604894 (by decide)
  decide +kernel

theorem h604894 : P.leaf 36 604894 = 200612502 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(484, 41408056), (540, 159204446)]) (.cons c604894_0 (.cons c604894_1 (.nil))) (by decide) (by decide))

theorem h97117 : P.leaf 36 97117 = 200612502 :=
  orient87 (v := 604894) (by decide) (by decide +kernel) h604894

theorem cover604926 : P.CoversSplit 26 10 604926 0xff00ff0000000000ff00ff000000000000000000000000000000000000000000ff00fa0000000000ff00fa000000000000000000000000000000000000000000ff33ff3233333232ff33ff3233333232333333323300320033333332330032000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [587, 874, 930, 972, 1273, 1315]) (by decide +kernel)

noncomputable def f604926 (i : ℕ) := rowWeight keep3 twice3 i * P.leaf 26 (619444224 + i)

theorem c604926_0 : rowSum f604926 0 938 = 265580849 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 604926) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover604926 (by decide)
  decide +kernel

theorem c604926_1 : rowSum f604926 938 86 = 198439626 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 604926) (keep := keep3) (twice := twice3) check rows elimOK (by decide) (by decide) cover604926 (by decide)
  decide +kernel

theorem sum604926 : rowSum f604926 0 1024 = 464020475 :=
  rowSum_append (F := f604926) (lo := 0) (n := 938) (m := 86) (A := 265580849) (B := 198439626) c604926_0 (c604926_1)

theorem h604926 : P.leaf 36 604926 = 464020475 :=
  leaf_weighted (k := 26) (d := 10) (H := 604926) (keep := keep3) (twice := twice3) rows (by decide) (by decide) (bal3) (invRow3 (H := 604926) (by decide) (by decide +kernel)) sum604926

theorem h97119 : P.leaf 36 97119 = 464020475 :=
  orient87 (v := 604926) (by decide) (by decide +kernel) h604926

theorem cover308692 : P.CoversSplit 26 10 308692 0xaa000000aa000000000000000000000000000000000000000000000000000000aa000000aa00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [467, 489, 530, 636, 930, 1265, 1272, 1658, 1665]) (by decide +kernel)

theorem h308692 : P.leaf 36 308692 = 1728000 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 308692) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 308692) (weight := fun _ => 1) (xs := [729, 731, 733, 735, 761, 763, 765, 767, 985, 987, 989, 991, 1017, 1019, 1021, 1023]) check rows elimOK (by decide) (by decide) cover308692 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h97122 : P.leaf 36 97122 = 1728000 :=
  orient6 (v := 308692) (by decide) (by decide +kernel) h308692

theorem cover308693 : P.CoversSplit 26 10 308693 0xaa000000aa000000000000000000000000000000000000000000000000000000aa000000aa00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 629, 636, 930, 1265, 1272, 1658, 1665]) (by decide +kernel)

theorem h308693 : P.leaf 36 308693 = 9401376 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 308693) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 308693) (weight := fun _ => 1) (xs := [729, 731, 733, 735, 761, 763, 765, 767, 985, 987, 989, 991, 1017, 1019, 1021, 1023]) check rows elimOK (by decide) (by decide) cover308693 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h97123 : P.leaf 36 97123 = 9401376 :=
  orient6 (v := 308693) (by decide) (by decide +kernel) h308693

theorem cover112470 : P.CoversSplit 26 10 112470 0xaa000000aa000000aa000000aa000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000aa000000aa220000aa000000aa220000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 579, 873, 930, 1315, 1322, 1658]) (by decide +kernel)

theorem c112470_0 : P.sumLeaves 26 115169280 1024 = 17000864 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 112470) (lo := 0) (len := 1024) (W := 17000864) check rows elimOK (by decide) (by decide) cover112470 (by decide)
  decide +kernel

theorem h112470 : P.leaf 36 112470 = 17000864 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 17000864)]) (.cons c112470_0 (.nil)) (by decide) (by decide))

theorem h97126 : P.leaf 36 97126 = 17000864 :=
  orient4 (v := 112470) (by decide) (by decide +kernel) h112470

theorem cover112471 : P.CoversSplit 26 10 112471 0xaa000000aa000000aa000000aa000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000aa000000aa220000aa000000aa220000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 579, 930, 1315, 1322, 1658]) (by decide +kernel)

theorem c112471_0 : P.sumLeaves 26 115170304 1024 = 49088144 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 112471) (lo := 0) (len := 1024) (W := 49088144) check rows elimOK (by decide) (by decide) cover112471 (by decide)
  decide +kernel

theorem h112471 : P.leaf 36 112471 = 49088144 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 49088144)]) (.cons c112471_0 (.nil)) (by decide) (by decide))

theorem h97127 : P.leaf 36 97127 = 49088144 :=
  orient4 (v := 112471) (by decide) (by decide +kernel) h112471

theorem cover308694 : P.CoversSplit 26 10 308694 0xaa000000aa000000000000000000000000000000000000000000000000000000aa000000aa00000000000000000000000000000000000000000000000000000000000000002200000000000000000000000000000000000000000000000000000000000000220000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [467, 489, 530, 636, 930, 1265, 1272, 1658, 1665]) (by decide +kernel)

theorem h308694 : P.leaf 36 308694 = 14364864 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 308694) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 308694) (weight := fun _ => 1) (xs := [209, 213, 465, 469, 729, 731, 733, 735, 761, 763, 765, 767, 985, 987, 989, 991, 1017, 1019, 1021, 1023]) check rows elimOK (by decide) (by decide) cover308694 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h97130 : P.leaf 36 97130 = 14364864 :=
  orient6 (v := 308694) (by decide) (by decide +kernel) h308694

theorem cover308695 : P.CoversSplit 26 10 308695 0xaa000000aa000000000000000000000000000000000000000000000000000000aa000000aa00000000000000000000000000000000000000000000000000000000000000002200000000000000000000000000000000000000000000000000000000000000220000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 530, 629, 636, 930, 1265, 1272, 1658, 1665]) (by decide +kernel)

theorem h308695 : P.leaf 36 308695 = 36515740 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 308695) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 308695) (weight := fun _ => 1) (xs := [209, 213, 465, 469, 729, 731, 733, 735, 761, 763, 765, 767, 985, 987, 989, 991, 1017, 1019, 1021, 1023]) check rows elimOK (by decide) (by decide) cover308695 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h97131 : P.leaf 36 97131 = 36515740 :=
  orient6 (v := 308695) (by decide) (by decide +kernel) h308695

theorem cover308699 : P.CoversSplit 26 10 308699 0xaaaa0000aaaa0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000220000002200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 629, 636, 1265, 1272, 1665]) (by decide +kernel)

theorem h308699 : P.leaf 36 308699 = 24899880 := by
  apply leaf_of_rowSum (k := 26) (d := 10) (H := 308699) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 6) (d := 10) (H := 308699) (weight := fun _ => 1) (xs := [465, 469, 497, 501, 977, 979, 981, 983, 985, 987, 989, 991, 1009, 1011, 1013, 1015, 1017, 1019, 1021, 1023]) check rows elimOK (by decide) (by decide) cover308699 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h97133 : P.leaf 36 97133 = 24899880 :=
  orient6 (v := 308699) (by decide) (by decide +kernel) h308699

theorem cover308702 : P.CoversSplit 26 10 308702 0xaaaa0000aaaa0000000000000000000000000000000000000000000000000000aaaa0000aaaa000000000000000000000000000000000000000000000000000000220000002200000000000000000000000000000000000000000000000000000022000000220000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 629, 636, 873, 1265, 1272, 1658, 1665]) (by decide +kernel)

theorem c308702_0 : P.sumLeaves 26 316110848 1024 = 41505976 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 308702) (lo := 0) (len := 1024) (W := 41505976) check rows elimOK (by decide) (by decide) cover308702 (by decide)
  decide +kernel

theorem h308702 : P.leaf 36 308702 = 41505976 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 41505976)]) (.cons c308702_0 (.nil)) (by decide) (by decide))

theorem h97134 : P.leaf 36 97134 = 41505976 :=
  orient6 (v := 308702) (by decide) (by decide +kernel) h308702

theorem cover308703 : P.CoversSplit 26 10 308703 0xaaaa0000aaaa0000000000000000000000000000000000000000000000000000aaaa0000aaaa000000000000000000000000000000000000000000000000000000220000002200000000000000000000000000000000000000000000000000000022000000220000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 629, 636, 1265, 1272, 1658, 1665]) (by decide +kernel)

theorem c308703_0 : P.sumLeaves 26 316111872 1024 = 101083816 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 308703) (lo := 0) (len := 1024) (W := 101083816) check rows elimOK (by decide) (by decide) cover308703 (by decide)
  decide +kernel

theorem h308703 : P.leaf 36 308703 = 101083816 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 101083816)]) (.cons c308703_0 (.nil)) (by decide) (by decide))

theorem h97135 : P.leaf 36 97135 = 101083816 :=
  orient6 (v := 308703) (by decide) (by decide +kernel) h308703

theorem cover97139 : P.CoversSplit 26 10 97139 0xf000f000f000f0000000000000000000f000f000f000f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c000c00000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 972, 979, 1273, 1658, 1665]) (by decide +kernel)

theorem c97139_0 : P.sumLeaves 26 99470336 1024 = 67601920 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97139) (lo := 0) (len := 1024) (W := 67601920) check rows elimOK (by decide) (by decide) cover97139 (by decide)
  decide +kernel

theorem h97139 : P.leaf 36 97139 = 67601920 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 67601920)]) (.cons c97139_0 (.nil)) (by decide) (by decide))

theorem cover370123 : P.CoversSplit 26 10 370123 0xaaaaaa00a0a0a00aaaaaaa00a0a0a00a00000000000000000000000000000000000000000000000000000a000000000a0000000000000000000000000000000000000000002000020000000000200002000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 530, 629, 636, 873, 881, 958, 1273, 1665]) (by decide +kernel)

noncomputable def f370123 (i : ℕ) := rowWeight keep16 twice16 i * P.leaf 26 (379005952 + i)

theorem c370123_0 : rowSum f370123 0 1024 = 15588698 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 370123) (keep := keep16) (twice := twice16) check rows elimOK (by decide) (by decide) cover370123 (by decide)
  decide +kernel

theorem sum370123 : rowSum f370123 0 1024 = 15588698 :=
  c370123_0

theorem h370123 : P.leaf 36 370123 = 15588698 :=
  leaf_weighted (k := 26) (d := 10) (H := 370123) (keep := keep16) (twice := twice16) rows (by decide) (by decide) (bal16) (invRow16 (H := 370123) (by decide) (by decide +kernel)) sum370123

theorem h97140 : P.leaf 36 97140 = 15588698 :=
  orient84 (v := 370123) (by decide) (by decide +kernel) h370123

theorem cover97141 : P.CoversSplit 26 10 97141 0xff00ff00ff00fa000000000000000000ff00ff00ff03fa000500050005000000050000000500000005000000050000000500000005010000050000000500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 579, 923, 972, 979, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c97141_0 : P.sumLeaves 26 99472384 1024 = 165011375 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97141) (lo := 0) (len := 1024) (W := 165011375) check rows elimOK (by decide) (by decide) cover97141 (by decide)
  decide +kernel

theorem h97141 : P.leaf 36 97141 = 165011375 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 165011375)]) (.cons c97141_0 (.nil)) (by decide) (by decide))

theorem cover97142 : P.CoversSplit 26 10 97142 0xff00ff00ff00fa000000000000000000ff00ff00ff03fa000500050005000000050000000500000005000000050000000500000005010000050000000500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 579, 874, 972, 979, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c97142_0 : P.sumLeaves 26 99473408 1024 = 172035492 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97142) (lo := 0) (len := 1024) (W := 172035492) check rows elimOK (by decide) (by decide) cover97142 (by decide)
  decide +kernel

theorem h97142 : P.leaf 36 97142 = 172035492 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 172035492)]) (.cons c97142_0 (.nil)) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(97020, 720), (97021, 720), (97022, 720), (97023, 720), (97091, 180), (97095, 360), (97099, 180), (97103, 360), (97107, 360), (97108, 180), (97109, 720), (97111, 360), (97113, 360), (97115, 360), (97116, 360), (97117, 720), (97119, 360), (97122, 240), (97123, 720), (97126, 720), (97127, 720), (97130, 720), (97131, 720), (97133, 720), (97134, 720), (97135, 720), (97139, 720), (97140, 360), (97141, 720), (97142, 720)]

theorem segOK : checkSeg 20 perms 97020 97143 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 97020 97143 16260 1829141248680 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 1829141248680)
    (SegSum.cons (w := 720) h97020 (SegSum.cons (w := 720) h97021 (SegSum.cons (w := 720) h97022 (SegSum.cons (w := 720) h97023 (SegSum.cons (w := 180) h97091 (SegSum.cons (w := 360) h97095 (SegSum.cons (w := 180) h97099 (SegSum.cons (w := 360) h97103 (SegSum.cons (w := 360) h97107 (SegSum.cons (w := 180) h97108 (SegSum.cons (w := 720) h97109 (SegSum.cons (w := 360) h97111 (SegSum.cons (w := 360) h97113 (SegSum.cons (w := 360) h97115 (SegSum.cons (w := 360) h97116 (SegSum.cons (w := 720) h97117 (SegSum.cons (w := 360) h97119 (SegSum.cons (w := 240) h97122 (SegSum.cons (w := 720) h97123 (SegSum.cons (w := 720) h97126 (SegSum.cons (w := 720) h97127 (SegSum.cons (w := 720) h97130 (SegSum.cons (w := 720) h97131 (SegSum.cons (w := 720) h97133 (SegSum.cons (w := 720) h97134 (SegSum.cons (w := 720) h97135 (SegSum.cons (w := 720) h97139 (SegSum.cons (w := 360) h97140 (SegSum.cons (w := 720) h97141 (SegSum.cons (w := 720) h97142 (show SegSum (P.leaf 36) [] 0 from rfl))))))))))))))))))))))))))))))) (by decide)

end RACert.S6N0.C0.S61
