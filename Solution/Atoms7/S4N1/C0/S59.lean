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

namespace RACert.S4N1.C0.S59

open RACert RACert.Problem

theorem cover21668 : P.CoversSplit 24 10 21668 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem h21668 : P.leaf 34 21668 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 21668) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 21668) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover21668 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover26964 : P.CoversSplit 24 10 26964 0xf000f00000000000000000000000000000000000000000000000000000000000f000f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000a000000000000000000000000000000000000000000000000000000000000000a0080000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 508, 516, 858, 865, 915, 1202, 1210, 1259, 1264, 1609]) (ps := [(5, [572], [523]), (14, [479, 480], [479, 480])]) (by decide +kernel)

theorem h26964 : P.leaf 34 26964 = 102064 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 26964) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 26964) (weight := fun _ => 1) (xs := [115, 125, 127, 381, 383, 748, 749, 750, 751, 764, 765, 766, 767, 1004, 1005, 1006, 1007, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover26964 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h21669 : P.leaf 34 21669 = 102064 :=
  orient32 (v := 26964) (by decide) (by decide +kernel) h26964

theorem cover21670 : P.CoversSplit 24 10 21670 0xa0a00000a0a00000000000000000000080800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 466, 515, 517, 522, 573, 858, 860, 916, 1202, 1210, 1259, 1601]) (ps := [(8, [468], [524]), (9, [510], [566])]) (by decide +kernel)

theorem h21670 : P.leaf 34 21670 = 56128 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 21670) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 21670) (weight := fun _ => 1) (xs := [887, 895, 981, 983, 989, 991, 1013, 1015, 1021, 1023]) check rows elimOK (by decide) (by decide) cover21670 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover38201 : P.CoversSplit 24 10 38201 0xcc00cc0000000000000000000000000080000000000000000000000000000000cc00cc0000000000000000000000000080000000000000000000000000000000cc00cc00000000000000000000000000800000000000000000000000000000000000000000000000003300330000000000000000000000000020000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 517, 529, 572, 858, 860, 865, 1202, 1209, 1601]) (ps := [(15, [487], [860])]) (by decide +kernel)

theorem c38201_0 : P.sumLeaves 24 39117824 1024 = 373350 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 38201) (lo := 0) (len := 1024) (W := 373350) check rows elimOK (by decide) (by decide) cover38201 (by decide)
  decide +kernel

theorem h38201 : P.leaf 34 38201 = 373350 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 373350)]) (.cons c38201_0 (.nil)) (by decide) (by decide))

theorem h21671 : P.leaf 34 21671 = 373350 :=
  orient25 (v := 38201) (by decide) (by decide +kernel) h38201

theorem cover21676 : P.CoversSplit 24 10 21676 0xa0a00000b0ba0000a0a00000b0ba0000a0a0000000000000a0a0000000000000000000000000000000000000000000000000000000000000000000000000000080000000800000000000000000000000802000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 515, 517, 522, 573, 858, 860, 865, 916, 1202, 1210, 1259, 1601]) (ps := [(9, [566], [573])]) (by decide +kernel)

noncomputable def f21676 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 24 (22196224 + i)

theorem c21676_0 : rowSum f21676 0 1024 = 362276 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 21676) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover21676 (by decide)
  decide +kernel

theorem sum21676 : rowSum f21676 0 1024 = 362276 :=
  c21676_0

theorem h21676 : P.leaf 34 21676 = 362276 :=
  leaf_weighted (k := 24) (d := 10) (H := 21676) (keep := keep2) (twice := twice2) rows (by decide) (by decide) (bal2) (invRow2 (H := 21676) (by decide) (by decide +kernel)) sum21676

theorem cover21677 : P.CoversSplit 24 10 21677 0xa0a00000b0ba0000a0a00000b0ba0000a0a0000000000505a0a0000000000504000000000000000000000000000000000000000000000000000000000000000080000000800000000000000000000000802000000000040100200000000000010000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 515, 517, 522, 573, 858, 860, 865, 916, 1202, 1210, 1259, 1601]) (ps := [(9, [566], [573]), (17, [1259], [1251])]) (by decide +kernel)

noncomputable def f21677 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 24 (22197248 + i)

theorem c21677_0 : rowSum f21677 0 1024 = 334744 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 21677) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover21677 (by decide)
  decide +kernel

theorem sum21677 : rowSum f21677 0 1024 = 334744 :=
  c21677_0

theorem h21677 : P.leaf 34 21677 = 334744 :=
  leaf_weighted (k := 24) (d := 10) (H := 21677) (keep := keep2) (twice := twice2) rows (by decide) (by decide) (bal2) (invRow2 (H := 21677) (by decide) (by decide +kernel)) sum21677

theorem cover21678 : P.CoversSplit 24 10 21678 0xa0a00000a0a00000a0a00000a0a00000a0a0000000000000a0a0000000000000000000000000000000000000000000000000000000000000000000000000000080000000800000000000000000000000802000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 515, 517, 522, 573, 858, 865, 916, 1202, 1210, 1259, 1601]) (ps := [(9, [566], [573])]) (by decide +kernel)

theorem h21678 : P.leaf 34 21678 = 377740 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 21678) (keep := keep2) (twice := twice2) rows (by decide) (by decide) bal2 (invRow2 (H := 21678) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 21678) (weight := rowWeight keep2 twice2) (xs := [309, 373, 383, 479, 511, 821, 823, 829, 831, 885, 887, 893, 895, 917, 919, 925, 927, 949, 951, 957, 959, 981, 983, 989, 991, 1013, 1015, 1021, 1023]) check rows elimOK (by decide) (by decide) cover21678 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover21679 : P.CoversSplit 24 10 21679 0xa0a00000a0a00000a0a00000a0a00000a0a0000000000505a0a0000000000504000000000000000000000000000000000000000000000000000000000000000080000000800000000000000000000000802000000000040100200000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [515, 517, 522, 573, 858, 916, 1202, 1210, 1259, 1601]) (ps := [(8, [565], [524]), (9, [566], [573]), (17, [1259], [1251])]) (by decide +kernel)

noncomputable def f21679 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 24 (22199296 + i)

theorem c21679_0 : rowSum f21679 0 1024 = 640420 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 21679) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover21679 (by decide)
  decide +kernel

theorem sum21679 : rowSum f21679 0 1024 = 640420 :=
  c21679_0

theorem h21679 : P.leaf 34 21679 = 640420 :=
  leaf_weighted (k := 24) (d := 10) (H := 21679) (keep := keep2) (twice := twice2) rows (by decide) (by decide) (bal2) (invRow2 (H := 21679) (by decide) (by decide +kernel)) sum21679

theorem cover26965 : P.CoversSplit 24 10 26965 0xff00ff0000000000000000000000000000000000000000000000000000000000ff00ff0000000000000000000000000000000000000000000000000000000000f000f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 516, 572, 858, 859, 865, 1202, 1210, 1259, 1264, 1609]) (ps := [(8, [537], [516]), (13, [559], [859, 866]), (14, [480], [908])]) (by decide +kernel)

theorem c26965_0 : P.sumLeaves 24 27612160 1024 = 1053746 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 26965) (lo := 0) (len := 1024) (W := 1053746) check rows elimOK (by decide) (by decide) cover26965 (by decide)
  decide +kernel

theorem h26965 : P.leaf 34 26965 = 1053746 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1053746)]) (.cons c26965_0 (.nil)) (by decide) (by decide))

theorem h21685 : P.leaf 34 21685 = 1053746 :=
  orient32 (v := 26965) (by decide) (by decide +kernel) h26965

theorem cover26791 : P.CoversSplit 24 10 26791 0xaa000000a00000000000000000000000aa0000000000000000000000000000008800000080000000000000000000000088000000000000000000000000000000aa000000a00000000000000000000000aa0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 517, 522, 573, 859, 865, 1210, 1259]) (by decide +kernel)

theorem h26791 : P.leaf 34 26791 = 390176 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 26791) (keep := keep5) (twice := twice5) rows (by decide) (by decide) bal5 (invRow5 (H := 26791) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 26791) (weight := rowWeight keep5 twice5) (xs := [377, 379, 381, 383, 477, 479, 505, 507, 509, 511, 635, 639, 735, 763, 767, 889, 891, 893, 895, 989, 991, 1017, 1019, 1021, 1023]) check rows elimOK (by decide) (by decide) cover26791 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h21686 : P.leaf 34 21686 = 390176 :=
  orient24 (v := 26791) (by decide) (by decide +kernel) h26791

theorem cover42809 : P.CoversSplit 24 10 42809 0xffffffff00000000ffffffff00000000a0a0000000000000a0a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 474, 486, 517, 572, 860, 1202, 1209, 1258, 1601]) (by decide +kernel)

theorem c42809_0 : P.sumLeaves 24 43836416 1024 = 5355622 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 42809) (lo := 0) (len := 1024) (W := 5355622) check rows elimOK (by decide) (by decide) cover42809 (by decide)
  decide +kernel

theorem h42809 : P.leaf 34 42809 = 5355622 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 5355622)]) (.cons c42809_0 (.nil)) (by decide) (by decide))

theorem h21687 : P.leaf 34 21687 = 5355622 :=
  orient5 (v := 42809) (by decide) (by decide +kernel) h42809

theorem cover22727 : P.CoversSplit 24 10 22727 0xffffffff00000000ffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080008c0000000000a0208000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [515, 516, 522, 536, 573, 858, 859, 865, 916, 1202, 1259, 1308, 1601]) (ps := [(7, [523], [516]), (9, [566], [573]), (13, [866], [859])]) (by decide +kernel)

noncomputable def f22727 (i : ℕ) := rowWeight keep5 twice5 i * P.leaf 24 (23272448 + i)

theorem c22727_0 : rowSum f22727 0 1024 = 1645784 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 22727) (keep := keep5) (twice := twice5) check rows elimOK (by decide) (by decide) cover22727 (by decide)
  decide +kernel

theorem sum22727 : rowSum f22727 0 1024 = 1645784 :=
  c22727_0

theorem h22727 : P.leaf 34 22727 = 1645784 :=
  leaf_weighted (k := 24) (d := 10) (H := 22727) (keep := keep5) (twice := twice5) rows (by decide) (by decide) (bal5) (invRow5 (H := 22727) (by decide) (by decide +kernel)) sum22727

theorem h21689 : P.leaf 34 21689 = 1645784 :=
  orient4 (v := 22727) (by decide) (by decide +kernel) h22727

theorem cover22743 : P.CoversSplit 24 10 22743 0xffffffff00000000ffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008000000000000000a0200000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [479, 516, 536, 573, 858, 859, 865, 879, 916, 1202, 1259, 1601]) (ps := [(13, [866], [859]), (17, [1251], [1259]), (18, [867], [1210])]) (by decide +kernel)

theorem c22743_0 : P.sumLeaves 24 23288832 1024 = 5336378 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22743) (lo := 0) (len := 1024) (W := 5336378) check rows elimOK (by decide) (by decide) cover22743 (by decide)
  decide +kernel

theorem h22743 : P.leaf 34 22743 = 5336378 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 5336378)]) (.cons c22743_0 (.nil)) (by decide) (by decide))

theorem h21691 : P.leaf 34 21691 = 5336378 :=
  orient4 (v := 22743) (by decide) (by decide +kernel) h22743

theorem cover21692 : P.CoversSplit 24 10 21692 0xf0000000f00a0000f0000000f00a0000f000000000000000f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 508, 573, 858, 860, 865, 867, 1202, 1210, 1217, 1601]) (by decide +kernel)

theorem h21692 : P.leaf 34 21692 = 1158980 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 21692) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 21692) (weight := fun _ => 1) (xs := [828, 829, 830, 831, 892, 893, 894, 895, 913, 915, 924, 925, 926, 927, 956, 957, 958, 959, 977, 979, 988, 989, 990, 991, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover21692 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover21693 : P.CoversSplit 24 10 21693 0xfffffffffaf00000fffffffffaf00000f500f50000000000f500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 517, 573, 858, 860, 865, 867, 909, 1202, 1210, 1217, 1251, 1601]) (by decide +kernel)

theorem c21693_0 : P.sumLeaves 24 22213632 1018 = 6712530 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21693) (lo := 0) (len := 1018) (W := 6712530) check rows elimOK (by decide) (by decide) cover21693 (by decide)
  decide +kernel

theorem c21693_1 : P.sumLeaves 24 22214650 6 = 1071976 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21693) (lo := 1018) (len := 6) (W := 1071976) check rows elimOK (by decide) (by decide) cover21693 (by decide)
  decide +kernel

theorem h21693 : P.leaf 34 21693 = 7784506 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1018, 6712530), (6, 1071976)]) (.cons c21693_0 (.cons c21693_1 (.nil))) (by decide) (by decide))

theorem cover21694 : P.CoversSplit 24 10 21694 0xf0f00000f0f00000f0f00000f0f00000f000000000000000f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 517, 573, 858, 860, 865, 867, 909, 1202, 1210, 1217, 1601]) (by decide +kernel)

theorem c21694_0 : P.sumLeaves 24 22214656 1024 = 4159348 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21694) (lo := 0) (len := 1024) (W := 4159348) check rows elimOK (by decide) (by decide) cover21694 (by decide)
  decide +kernel

theorem h21694 : P.leaf 34 21694 = 4159348 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 4159348)]) (.cons c21694_0 (.nil)) (by decide) (by decide))

theorem cover21695 : P.CoversSplit 24 10 21695 0xfffffffffafa0000fffffffffafa0000f500f50000000000f500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [517, 573, 860, 865, 867, 909, 1202, 1210, 1217, 1251, 1601]) (by decide +kernel)

theorem c21695_0 : P.sumLeaves 24 22215680 1014 = 20150934 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21695) (lo := 0) (len := 1014) (W := 20150934) check rows elimOK (by decide) (by decide) cover21695 (by decide)
  decide +kernel

theorem c21695_1 : P.sumLeaves 24 22216694 10 = 4031936 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21695) (lo := 1014) (len := 10) (W := 4031936) check rows elimOK (by decide) (by decide) cover21695 (by decide)
  decide +kernel

theorem h21695 : P.leaf 34 21695 = 24182870 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1014, 20150934), (10, 4031936)]) (.cons c21695_0 (.cons c21695_1 (.nil))) (by decide) (by decide))

theorem cover21700 : P.CoversSplit 24 10 21700 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem h21700 : P.leaf 34 21700 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 21700) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 21700) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover21700 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover26932 : P.CoversSplit 24 10 26932 0xa000a000a000a000000000000000000000000000000000000000000000000000a000a0008000800000000000000000000000000000000000000000000000000000000000000000000000000000000000a000a0000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 472, 508, 517, 529, 865, 1202, 1217, 1251, 1259, 1264, 1308, 1601, 1609]) (ps := [(8, [622], [1609]), (12, [915], [859]), (14, [480, 908], [480, 908])]) (by decide +kernel)

theorem h26932 : P.leaf 34 26932 = 51671 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 26932) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 26932) (weight := fun _ => 1) (xs := [125, 365, 367, 381, 383, 719, 735, 749, 751, 765, 767, 973, 975, 989, 991, 1005, 1007, 1021, 1023]) check rows elimOK (by decide) (by decide) cover26932 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h21701 : P.leaf 34 21701 = 51671 :=
  orient24 (v := 26932) (by decide) (by decide +kernel) h26932

theorem cover26917 : P.CoversSplit 24 10 26917 0x8800000080000000000000000000000000000000000000000000000000000000880000008000000000000000000000000000000000000000000000000000000080000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [466, 473, 515, 522, 529, 572, 858, 859, 865, 1210]) (ps := [(13, [559], [866]), (14, [480], [908])]) (by decide +kernel)

theorem h26917 : P.leaf 34 26917 = 50976 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 26917) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 26917) (weight := fun _ => 1) (xs := [479, 511, 735, 763, 767, 991, 1019, 1023]) check rows elimOK (by decide) (by decide) cover26917 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h21702 : P.leaf 34 21702 = 50976 :=
  orient24 (v := 26917) (by decide) (by decide +kernel) h26917

theorem cover21703 : P.CoversSplit 24 10 21703 0xf0f00000f0f00000f0f00000f0f00000f0f0000000000000f0f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [466, 515, 522, 536, 573, 858, 860, 916, 1202, 1210, 1217, 1259, 1601]) (by decide +kernel)

theorem c21703_0 : P.sumLeaves 24 22223872 1024 = 1202548 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21703) (lo := 0) (len := 1024) (W := 1202548) check rows elimOK (by decide) (by decide) cover21703 (by decide)
  decide +kernel

theorem h21703 : P.leaf 34 21703 = 1202548 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1202548)]) (.cons c21703_0 (.nil)) (by decide) (by decide))

theorem cover21708 : P.CoversSplit 24 10 21708 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [472]) (by decide +kernel)

theorem h21708 : P.leaf 34 21708 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 21708) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 21708) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover21708 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover21709 : P.CoversSplit 24 10 21709 0xf0f00000e0e00000f0f00000e0e0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c00000000000000000300000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 515, 522, 536, 573, 858, 860, 865, 916, 1202, 1210, 1259, 1601]) (ps := [(11, [472], [858])]) (by decide +kernel)

theorem h21709 : P.leaf 34 21709 = 271294 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 21709) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 21709) (weight := fun _ => 1) (xs := [308, 309, 382, 383, 917, 918, 919, 925, 926, 927, 948, 949, 950, 951, 956, 957, 958, 959, 981, 982, 983, 989, 990, 991, 1012, 1013, 1014, 1015, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover21709 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover26981 : P.CoversSplit 24 10 26981 0xcc00000080000000000000000000000000000000000000000000000000000000cc00000080000000000000000000000000000000000000000000000000000000c0000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [466, 473, 515, 522, 572, 858, 859, 865, 915, 1202, 1210]) (ps := [(13, [559], [866]), (14, [480], [908])]) (by decide +kernel)

theorem h26981 : P.leaf 34 26981 = 297894 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 26981) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 26981) (weight := fun _ => 1) (xs := [479, 510, 511, 735, 762, 763, 766, 767, 991, 1018, 1019, 1022, 1023]) check rows elimOK (by decide) (by decide) cover26981 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h21710 : P.leaf 34 21710 = 297894 :=
  orient24 (v := 26981) (by decide) (by decide +kernel) h26981

theorem cover21711 : P.CoversSplit 24 10 21711 0xf0f00000f0f00000f0f00000f0f00000f0f0000000000000f0f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 522, 536, 858, 860, 916, 1202, 1210, 1217, 1259, 1601]) (by decide +kernel)

theorem c21711_0 : P.sumLeaves 24 22232064 1024 = 2390268 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21711) (lo := 0) (len := 1024) (W := 2390268) check rows elimOK (by decide) (by decide) cover21711 (by decide)
  decide +kernel

theorem h21711 : P.leaf 34 21711 = 2390268 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 2390268)]) (.cons c21711_0 (.nil)) (by decide) (by decide))

theorem cover26919 : P.CoversSplit 24 10 26919 0x8800000080000000000000000000000088000000000000000000000000000000880000008000000000000000000000008800000000000000000000000000000088000000800000000000000000000000880000000000000000000000000000000000000000000000002200000020000000000000000000000022000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [466, 515, 517, 522, 529, 572, 858, 859, 865, 1210]) (by decide +kernel)

theorem h26919 : P.leaf 34 26919 = 655933 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 26919) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 26919) (weight := fun _ => 1) (xs := [49, 53, 149, 177, 181, 379, 383, 479, 507, 511, 635, 639, 735, 763, 767, 891, 895, 991, 1019, 1023]) check rows elimOK (by decide) (by decide) cover26919 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h21718 : P.leaf 34 21718 = 655933 :=
  orient24 (v := 26919) (by decide) (by decide +kernel) h26919

theorem cover21719 : P.CoversSplit 24 10 21719 0xfffffffff0f00000fffffffff0f00000ffff000000000000ffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [516, 536, 573, 858, 860, 865, 867, 916, 1202, 1210, 1217, 1259, 1601]) (ps := [(8, [615], [1217])]) (by decide +kernel)

theorem c21719_0 : P.sumLeaves 24 22240256 1008 = 9832558 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21719) (lo := 0) (len := 1008) (W := 9832558) check rows elimOK (by decide) (by decide) cover21719 (by decide)
  decide +kernel

theorem c21719_1 : P.sumLeaves 24 22241264 16 = 3603628 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21719) (lo := 1008) (len := 16) (W := 3603628) check rows elimOK (by decide) (by decide) cover21719 (by decide)
  decide +kernel

theorem h21719 : P.leaf 34 21719 = 13436186 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1008, 9832558), (16, 3603628)]) (.cons c21719_0 (.cons c21719_1 (.nil))) (by decide) (by decide))

theorem cover21724 : P.CoversSplit 24 10 21724 0xa0000000f0000000a0000000f0000000a000000000000000a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 472, 508, 516, 536, 573, 858, 867, 1202, 1210, 1601]) (by decide +kernel)

theorem h21724 : P.leaf 34 21724 = 901268 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 21724) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 21724) (weight := fun _ => 1) (xs := [829, 831, 893, 895, 924, 925, 926, 927, 957, 959, 988, 989, 990, 991, 1021, 1023]) check rows elimOK (by decide) (by decide) cover21724 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover21725 : P.CoversSplit 24 10 21725 0xfffffffff0f00000fffffffff0f00000ff00000000000000ff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 516, 536, 573, 858, 860, 865, 867, 909, 916, 1202, 1210, 1259, 1601]) (by decide +kernel)

theorem c21725_0 : P.sumLeaves 24 22246400 1024 = 7837230 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21725) (lo := 0) (len := 1024) (W := 7837230) check rows elimOK (by decide) (by decide) cover21725 (by decide)
  decide +kernel

theorem h21725 : P.leaf 34 21725 = 7837230 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 7837230)]) (.cons c21725_0 (.nil)) (by decide) (by decide))

theorem cover21726 : P.CoversSplit 24 10 21726 0xa0a00000a0a00000a0a00000a0a00000a0a0000000000505a0a0000000000505000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 516, 536, 573, 858, 865, 867, 916, 1202, 1210, 1601]) (by decide +kernel)

theorem h21726 : P.leaf 34 21726 = 2739236 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 21726) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 21726) (weight := fun _ => 1) (xs := [768, 770, 776, 778, 821, 823, 829, 831, 832, 834, 840, 842, 885, 887, 893, 895, 917, 919, 925, 927, 949, 951, 957, 959, 981, 983, 989, 991, 1013, 1015, 1021, 1023]) check rows elimOK (by decide) (by decide) cover21726 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover21727 : P.CoversSplit 24 10 21727 0xfffffffff0f00000fffffffff0f00000ffff00000000a0a0ffff00000000a0a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [516, 536, 573, 858, 860, 865, 867, 916, 1202, 1210, 1217, 1259, 1601]) (by decide +kernel)

theorem c21727_0 : P.sumLeaves 24 22248448 1000 = 17342216 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21727) (lo := 0) (len := 1000) (W := 17342216) check rows elimOK (by decide) (by decide) cover21727 (by decide)
  decide +kernel

theorem c21727_1 : P.sumLeaves 24 22249448 24 = 9042576 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21727) (lo := 1000) (len := 24) (W := 9042576) check rows elimOK (by decide) (by decide) cover21727 (by decide)
  decide +kernel

theorem h21727 : P.leaf 34 21727 = 26384792 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1000, 17342216), (24, 9042576)]) (.cons c21727_0 (.cons c21727_1 (.nil))) (by decide) (by decide))

theorem cover22716 : P.CoversSplit 24 10 22716 0xa000a000a0000000a000a000a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000800080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 466, 473, 508, 573, 859, 879, 1202, 1210, 1251, 1259, 1601]) (by decide +kernel)

theorem h22716 : P.leaf 34 22716 = 373256 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 22716) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 22716) (weight := fun _ => 1) (xs := [367, 383, 925, 927, 941, 943, 957, 959, 989, 991, 1005, 1007, 1021, 1023]) check rows elimOK (by decide) (by decide) cover22716 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h21734 : P.leaf 34 21734 = 373256 :=
  orient4 (v := 22716) (by decide) (by decide +kernel) h22716

def seg : List (ℕ × ℕ) := [(21668, 24), (21669, 48), (21670, 48), (21671, 48), (21676, 24), (21677, 24), (21678, 24), (21679, 24), (21685, 48), (21686, 24), (21687, 48), (21689, 24), (21691, 48), (21692, 48), (21693, 48), (21694, 48), (21695, 48), (21700, 16), (21701, 16), (21702, 48), (21703, 48), (21708, 48), (21709, 48), (21710, 48), (21711, 48), (21718, 48), (21719, 48), (21724, 48), (21725, 48), (21726, 48), (21727, 48), (21734, 48)]

theorem segOK : checkSeg 16 perms 21668 21735 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 21668 21735 1304 5183840000 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 5183840000)
    (SegSum.cons (w := 24) h21668 (SegSum.cons (w := 48) h21669 (SegSum.cons (w := 48) h21670 (SegSum.cons (w := 48) h21671 (SegSum.cons (w := 24) h21676 (SegSum.cons (w := 24) h21677 (SegSum.cons (w := 24) h21678 (SegSum.cons (w := 24) h21679 (SegSum.cons (w := 48) h21685 (SegSum.cons (w := 24) h21686 (SegSum.cons (w := 48) h21687 (SegSum.cons (w := 24) h21689 (SegSum.cons (w := 48) h21691 (SegSum.cons (w := 48) h21692 (SegSum.cons (w := 48) h21693 (SegSum.cons (w := 48) h21694 (SegSum.cons (w := 48) h21695 (SegSum.cons (w := 16) h21700 (SegSum.cons (w := 16) h21701 (SegSum.cons (w := 48) h21702 (SegSum.cons (w := 48) h21703 (SegSum.cons (w := 48) h21708 (SegSum.cons (w := 48) h21709 (SegSum.cons (w := 48) h21710 (SegSum.cons (w := 48) h21711 (SegSum.cons (w := 48) h21718 (SegSum.cons (w := 48) h21719 (SegSum.cons (w := 48) h21724 (SegSum.cons (w := 48) h21725 (SegSum.cons (w := 48) h21726 (SegSum.cons (w := 48) h21727 (SegSum.cons (w := 48) h21734 (show SegSum (P.leaf 34) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S4N1.C0.S59
