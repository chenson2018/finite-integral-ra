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

namespace RACert.S4N1.C0.S30

open RACert RACert.Problem

theorem cover19163 : P.CoversSplit 24 10 19163 0xff00ff0000000000ff00ff0000000000a000000000000000a0000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [467, 487, 516, 573, 859, 879, 915, 916, 921, 1210, 1259]) (ps := [(14, [965], [859, 1266])]) (by decide +kernel)

theorem c19163_0 : P.sumLeaves 24 19622912 1024 = 4663832 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 19163) (lo := 0) (len := 1024) (W := 4663832) check rows elimOK (by decide) (by decide) cover19163 (by decide)
  decide +kernel

theorem h19163 : P.leaf 34 19163 = 4663832 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 4663832)]) (.cons c19163_0 (.nil)) (by decide) (by decide))

theorem h5851 : P.leaf 34 5851 = 4663832 :=
  orient4 (v := 19163) (by decide) (by decide +kernel) h19163

theorem cover5852 : P.CoversSplit 24 10 5852 0xfcfcfcfca0a000000000000000000000a0a0a4a40000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 508, 516, 536, 573, 860, 916, 1202, 1210, 1258, 1259, 1264, 1308]) (by decide +kernel)

theorem c5852_0 : P.sumLeaves 24 5992448 1024 = 2737202 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5852) (lo := 0) (len := 1024) (W := 2737202) check rows elimOK (by decide) (by decide) cover5852 (by decide)
  decide +kernel

theorem h5852 : P.leaf 34 5852 = 2737202 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 2737202)]) (.cons c5852_0 (.nil)) (by decide) (by decide))

theorem cover19179 : P.CoversSplit 24 10 19179 0xff00ff00aa000000ff00ff00aa000000ff0000000000aa00ff0000000000aa000000000000000000000000000000000000000000000000000000000000000000cc00cc00880000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [515, 522, 573, 859, 879, 915, 916, 921, 1202, 1210, 1259]) (ps := [(14, [958, 965], [1266])]) (by decide +kernel)

theorem c19179_0 : P.sumLeaves 24 19639296 1024 = 7928344 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 19179) (lo := 0) (len := 1024) (W := 7928344) check rows elimOK (by decide) (by decide) cover19179 (by decide)
  decide +kernel

theorem h19179 : P.leaf 34 19179 = 7928344 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 7928344)]) (.cons c19179_0 (.nil)) (by decide) (by decide))

theorem h5853 : P.leaf 34 5853 = 7928344 :=
  orient4 (v := 19179) (by decide) (by decide +kernel) h19179

theorem cover5854 : P.CoversSplit 24 10 5854 0xffffffffa0a000000000000000000000a0a0a5a50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 516, 536, 573, 860, 916, 1202, 1210, 1258, 1259, 1264, 1308]) (by decide +kernel)

theorem c5854_0 : P.sumLeaves 24 5994496 1024 = 6552175 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5854) (lo := 0) (len := 1024) (W := 6552175) check rows elimOK (by decide) (by decide) cover5854 (by decide)
  decide +kernel

theorem h5854 : P.leaf 34 5854 = 6552175 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 6552175)]) (.cons c5854_0 (.nil)) (by decide) (by decide))

theorem cover5855 : P.CoversSplit 24 10 5855 0xffffffffa0a000000000000000000000ffffffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [516, 536, 573, 860, 916, 1202, 1210, 1217, 1258, 1259, 1264, 1308]) (by decide +kernel)

theorem c5855_0 : P.sumLeaves 24 5995520 1024 = 18599145 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5855) (lo := 0) (len := 1024) (W := 18599145) check rows elimOK (by decide) (by decide) cover5855 (by decide)
  decide +kernel

theorem h5855 : P.leaf 34 5855 = 18599145 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 18599145)]) (.cons c5855_0 (.nil)) (by decide) (by decide))

theorem cover50443 : P.CoversSplit 24 10 50443 0xaa000000000000000000000000000000880000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000a0000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 516, 517, 522, 528, 529, 572, 865, 872, 915, 921]) (by decide +kernel)

theorem h50443 : P.leaf 34 50443 = 67392 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 50443) (keep := keep5) (twice := twice5) rows (by decide) (by decide) bal5 (invRow5 (H := 50443) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 50443) (weight := rowWeight keep5 twice5) (xs := [383, 509, 511, 891, 895, 1017, 1019, 1021, 1023]) check rows elimOK (by decide) (by decide) cover50443 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h5858 : P.leaf 34 5858 = 67392 :=
  orient25 (v := 50443) (by decide) (by decide +kernel) h50443

theorem cover19101 : P.CoversSplit 24 10 19101 0xaa00aa0000000000aa00aa0000000000a000000000000000a000000000000000000000000000000000000000000000000000000000000000000000000000000088008800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 516, 517, 524, 528, 573, 859, 916, 921, 1210, 1259]) (ps := [(8, [615], [1266])]) (by decide +kernel)

theorem h19101 : P.leaf 34 19101 = 1119552 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 19101) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 19101) (weight := fun _ => 1) (xs := [491, 495, 507, 511, 829, 831, 893, 895, 937, 939, 941, 943, 953, 955, 957, 959, 1001, 1003, 1005, 1007, 1017, 1019, 1021, 1023]) check rows elimOK (by decide) (by decide) cover19101 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h5859 : P.leaf 34 5859 = 1119552 :=
  orient4 (v := 19101) (by decide) (by decide +kernel) h19101

theorem cover19116 : P.CoversSplit 24 10 19116 0x8000000000000000800000000000000080000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 466, 472, 473, 515, 517, 524, 859, 879, 916]) (by decide +kernel)

theorem h19116 : P.leaf 34 19116 = 81008 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 19116) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 19116) (weight := fun _ => 1) (xs := [831, 895, 959, 1023]) check rows elimOK (by decide) (by decide) cover19116 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h5860 : P.leaf 34 5860 = 81008 :=
  orient4 (v := 19116) (by decide) (by decide +kernel) h19116

theorem cover5861 : P.CoversSplit 24 10 5861 0xcccc0000000000000000000000000000cccc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 475, 515, 522, 524, 860, 916, 1202, 1209, 1259]) (by decide +kernel)

theorem h5861 : P.leaf 34 5861 = 1515672 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5861) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5861) (weight := fun _ => 1) (xs := [882, 883, 886, 887, 890, 891, 894, 895, 1010, 1011, 1014, 1015, 1018, 1019, 1022, 1023]) check rows elimOK (by decide) (by decide) cover5861 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover5862 : P.CoversSplit 24 10 5862 0xaaaa0000000000000000000000000000a0a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000088000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 475, 515, 522, 524, 566, 573, 860, 916, 1209, 1259, 1264, 1308]) (by decide +kernel)

theorem h5862 : P.leaf 34 5862 = 869700 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5862) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5862) (weight := fun _ => 1) (xs := [507, 511, 885, 887, 893, 895, 1009, 1011, 1013, 1015, 1017, 1019, 1021, 1023]) check rows elimOK (by decide) (by decide) cover5862 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover5863 : P.CoversSplit 24 10 5863 0xffff0000000000000000000000000000ffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [475, 515, 522, 524, 566, 573, 860, 916, 1202, 1209, 1251, 1259, 1264, 1308]) (by decide +kernel)

theorem c5863_0 : P.sumLeaves 24 6003712 1024 = 5710944 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5863) (lo := 0) (len := 1024) (W := 5710944) check rows elimOK (by decide) (by decide) cover5863 (by decide)
  decide +kernel

theorem h5863 : P.leaf 34 5863 = 5710944 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 5710944)]) (.cons c5863_0 (.nil)) (by decide) (by decide))

theorem cover5864 : P.CoversSplit 24 10 5864 0x8888000000000000000000000000000080800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 508, 515, 522, 523, 573, 860, 916, 1202, 1209, 1259, 1308]) (ps := [(14, [487, 923], [487, 860])]) (by decide +kernel)

theorem h5864 : P.leaf 34 5864 = 64812 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5864) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5864) (weight := fun _ => 1) (xs := [887, 895, 1011, 1015, 1019, 1023]) check rows elimOK (by decide) (by decide) cover5864 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover5865 : P.CoversSplit 24 10 5865 0xcccc0000000000000000000000000000cccc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 515, 522, 523, 573, 860, 916, 1202, 1209, 1251, 1259, 1308]) (ps := [(14, [923], [487])]) (by decide +kernel)

theorem h5865 : P.leaf 34 5865 = 470944 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5865) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5865) (weight := fun _ => 1) (xs := [882, 883, 886, 887, 890, 891, 894, 895, 1010, 1011, 1014, 1015, 1018, 1019, 1022, 1023]) check rows elimOK (by decide) (by decide) cover5865 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover5866 : P.CoversSplit 24 10 5866 0xaaaa0000000000000000000000000000a0a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000088000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 515, 522, 523, 565, 573, 860, 916, 1209, 1259, 1264, 1308]) (ps := [(14, [874, 923], [860, 916])]) (by decide +kernel)

theorem h5866 : P.leaf 34 5866 = 619396 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5866) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5866) (weight := fun _ => 1) (xs := [507, 511, 885, 887, 893, 895, 1009, 1011, 1013, 1015, 1017, 1019, 1021, 1023]) check rows elimOK (by decide) (by decide) cover5866 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover5867 : P.CoversSplit 24 10 5867 0xffff0000000000000000000000000000ffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [515, 522, 523, 573, 860, 916, 1202, 1209, 1251, 1258, 1259, 1264, 1308]) (ps := [(14, [923], [916])]) (by decide +kernel)

theorem c5867_0 : P.sumLeaves 24 6007808 1024 = 2523928 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5867) (lo := 0) (len := 1024) (W := 2523928) check rows elimOK (by decide) (by decide) cover5867 (by decide)
  decide +kernel

theorem h5867 : P.leaf 34 5867 = 2523928 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 2523928)]) (.cons c5867_0 (.nil)) (by decide) (by decide))

theorem cover5868 : P.CoversSplit 24 10 5868 0x8888000000000000000000000000000080800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000088000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 508, 515, 522, 573, 860, 916, 1202, 1209, 1259, 1308]) (by decide +kernel)

theorem h5868 : P.leaf 34 5868 = 312332 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5868) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5868) (weight := fun _ => 1) (xs := [507, 511, 887, 895, 1011, 1015, 1019, 1023]) check rows elimOK (by decide) (by decide) cover5868 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover5869 : P.CoversSplit 24 10 5869 0xcccc0000000000000000000000000000cccc00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 515, 522, 573, 860, 916, 1202, 1209, 1251, 1259, 1308]) (by decide +kernel)

theorem h5869 : P.leaf 34 5869 = 2361496 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5869) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5869) (weight := fun _ => 1) (xs := [506, 507, 510, 511, 882, 883, 886, 887, 890, 891, 894, 895, 1010, 1011, 1014, 1015, 1018, 1019, 1022, 1023]) check rows elimOK (by decide) (by decide) cover5869 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover5870 : P.CoversSplit 24 10 5870 0xaaaa0000000000000000000000000000a0a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000088000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 515, 522, 573, 860, 916, 1209, 1259, 1264, 1308]) (by decide +kernel)

theorem h5870 : P.leaf 34 5870 = 2334430 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5870) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5870) (weight := fun _ => 1) (xs := [507, 511, 885, 887, 893, 895, 1009, 1011, 1013, 1015, 1017, 1019, 1021, 1023]) check rows elimOK (by decide) (by decide) cover5870 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover5871 : P.CoversSplit 24 10 5871 0xffff0000000000000000000000000000ffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 522, 573, 860, 916, 1202, 1209, 1251, 1258, 1259, 1264, 1308]) (by decide +kernel)

theorem c5871_0 : P.sumLeaves 24 6011904 1024 = 8997848 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5871) (lo := 0) (len := 1024) (W := 8997848) check rows elimOK (by decide) (by decide) cover5871 (by decide)
  decide +kernel

theorem h5871 : P.leaf 34 5871 = 8997848 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 8997848)]) (.cons c5871_0 (.nil)) (by decide) (by decide))

theorem cover19103 : P.CoversSplit 24 10 19103 0xaa00aa0000000000aa00aa0000000000a000000000000000a000000000000000000000000000000000000000000000000000000000000000000000000000000088008800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [516, 517, 524, 528, 573, 859, 916, 921, 1210, 1259]) (ps := [(8, [615], [1266])]) (by decide +kernel)

theorem h19103 : P.leaf 34 19103 = 3603072 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 19103) (keep := keep5) (twice := twice5) rows (by decide) (by decide) bal5 (invRow5 (H := 19103) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 19103) (weight := rowWeight keep5 twice5) (xs := [491, 495, 507, 511, 829, 831, 893, 895, 937, 939, 941, 943, 953, 955, 957, 959, 1001, 1003, 1005, 1007, 1017, 1019, 1021, 1023]) check rows elimOK (by decide) (by decide) cover19103 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h5875 : P.leaf 34 5875 = 3603072 :=
  orient4 (v := 19103) (by decide) (by decide +kernel) h19103

theorem cover19118 : P.CoversSplit 24 10 19118 0xa0000000a0000000a0000000a0000000a000000000000500a000000000000500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 515, 517, 522, 524, 573, 859, 916, 921, 1202]) (by decide +kernel)

theorem h19118 : P.leaf 34 19118 = 890124 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 19118) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 19118) (weight := fun _ => 1) (xs := [776, 778, 829, 831, 840, 842, 893, 895, 925, 927, 957, 959, 989, 991, 1021, 1023]) check rows elimOK (by decide) (by decide) cover19118 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h5876 : P.leaf 34 5876 = 890124 :=
  orient4 (v := 19118) (by decide) (by decide +kernel) h19118

theorem cover19119 : P.CoversSplit 24 10 19119 0xff00ff00aa000000ff00ff00aa000000ff0000000000a000ff0000000000a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 517, 522, 524, 573, 916, 921, 1202, 1210]) (by decide +kernel)

theorem c19119_0 : P.sumLeaves 24 19577856 1024 = 8782736 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 19119) (lo := 0) (len := 1024) (W := 8782736) check rows elimOK (by decide) (by decide) cover19119 (by decide)
  decide +kernel

theorem h19119 : P.leaf 34 19119 = 8782736 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 8782736)]) (.cons c19119_0 (.nil)) (by decide) (by decide))

theorem h5877 : P.leaf 34 5877 = 8782736 :=
  orient4 (v := 19119) (by decide) (by decide +kernel) h19119

theorem cover36666 : P.CoversSplit 24 10 36666 0xff00ff00f0000000ff00ff00f0000000aa00af0000000000aa00af00000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 474, 517, 572, 915, 921, 1202, 1209, 1258]) (ps := [(14, [965], [1272])]) (by decide +kernel)

theorem c36666_0 : P.sumLeaves 24 37545984 1024 = 6945688 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 36666) (lo := 0) (len := 1024) (W := 6945688) check rows elimOK (by decide) (by decide) cover36666 (by decide)
  decide +kernel

theorem h36666 : P.leaf 34 36666 = 6945688 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 6945688)]) (.cons c36666_0 (.nil)) (by decide) (by decide))

theorem h5878 : P.leaf 34 5878 = 6945688 :=
  orient5 (v := 36666) (by decide) (by decide +kernel) h36666

theorem cover19135 : P.CoversSplit 24 10 19135 0xff00ff00aa000000ff00ff00aa000000ff00ff0000000000ff00ff00000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00880000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [517, 524, 573, 916, 921, 1202, 1210, 1217, 1259]) (ps := [(14, [965], [1217, 1266])]) (by decide +kernel)

theorem c19135_0 : P.sumLeaves 24 19594240 1024 = 21953292 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 19135) (lo := 0) (len := 1024) (W := 21953292) check rows elimOK (by decide) (by decide) cover19135 (by decide)
  decide +kernel

theorem h19135 : P.leaf 34 19135 = 21953292 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 21953292)]) (.cons c19135_0 (.nil)) (by decide) (by decide))

theorem h5879 : P.leaf 34 5879 = 21953292 :=
  orient4 (v := 19135) (by decide) (by decide +kernel) h19135

theorem cover36682 : P.CoversSplit 24 10 36682 0xaa000000aa000000aa000000aa000000aa00000000000000aa00000000000000000000000000000000000000000000000000000000000000000000000000000088000000880000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 515, 516, 522, 572, 915, 921, 1202, 1258]) (ps := [(5, [474], [516]), (7, [565], [572]), (14, [965], [1272])]) (by decide +kernel)

theorem h36682 : P.leaf 34 36682 = 995094 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 36682) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 36682) (weight := fun _ => 1) (xs := [475, 479, 507, 511, 825, 827, 829, 831, 889, 891, 893, 895, 921, 923, 925, 927, 953, 955, 957, 959, 985, 987, 989, 991, 1017, 1019, 1021, 1023]) check rows elimOK (by decide) (by decide) cover36682 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h5880 : P.leaf 34 5880 = 995094 :=
  orient5 (v := 36682) (by decide) (by decide +kernel) h36682

theorem cover19151 : P.CoversSplit 24 10 19151 0xff00ff0000000000ff00ff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [515, 516, 522, 536, 573, 859, 879, 915, 916, 921]) (ps := [(14, [965], [859, 1266])]) (by decide +kernel)

theorem h19151 : P.leaf 34 19151 = 4539328 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 19151) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 19151) (weight := fun _ => 1) (xs := [936, 937, 938, 939, 940, 941, 942, 943, 952, 953, 954, 955, 956, 957, 958, 959, 1000, 1001, 1002, 1003, 1004, 1005, 1006, 1007, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover19151 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h5881 : P.leaf 34 5881 = 4539328 :=
  orient4 (v := 19151) (by decide) (by decide +kernel) h19151

theorem cover19166 : P.CoversSplit 24 10 19166 0xff00ff0000000000ff00ff0000000000a000000000000000a0000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 516, 536, 573, 859, 879, 915, 916, 921, 1210, 1259]) (ps := [(14, [965], [859, 1266])]) (by decide +kernel)

theorem c19166_0 : P.sumLeaves 24 19625984 1024 = 4058016 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 19166) (lo := 0) (len := 1024) (W := 4058016) check rows elimOK (by decide) (by decide) cover19166 (by decide)
  decide +kernel

theorem h19166 : P.leaf 34 19166 = 4058016 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 4058016)]) (.cons c19166_0 (.nil)) (by decide) (by decide))

theorem h5882 : P.leaf 34 5882 = 4058016 :=
  orient4 (v := 19166) (by decide) (by decide +kernel) h19166

theorem cover19167 : P.CoversSplit 24 10 19167 0xff00ff0000000000ff00ff0000000000a000000000000000a0000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [516, 536, 573, 859, 879, 908, 915, 916, 921, 1210, 1259]) (ps := [(14, [965], [859, 1266])]) (by decide +kernel)

theorem c19167_0 : P.sumLeaves 24 19627008 1024 = 8422220 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 19167) (lo := 0) (len := 1024) (W := 8422220) check rows elimOK (by decide) (by decide) cover19167 (by decide)
  decide +kernel

theorem h19167 : P.leaf 34 19167 = 8422220 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 8422220)]) (.cons c19167_0 (.nil)) (by decide) (by decide))

theorem h5883 : P.leaf 34 5883 = 8422220 :=
  orient4 (v := 19167) (by decide) (by decide +kernel) h19167

theorem cover5884 : P.CoversSplit 24 10 5884 0xfcfcfcfca8a800000000000000000000f4f4f4f40000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00880000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 508, 573, 860, 867, 909, 916, 1202, 1210, 1258, 1259, 1264, 1308]) (by decide +kernel)

theorem c5884_0 : P.sumLeaves 24 6025216 1024 = 6298336 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5884) (lo := 0) (len := 1024) (W := 6298336) check rows elimOK (by decide) (by decide) cover5884 (by decide)
  decide +kernel

theorem h5884 : P.leaf 34 5884 = 6298336 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 6298336)]) (.cons c5884_0 (.nil)) (by decide) (by decide))

theorem cover19183 : P.CoversSplit 24 10 19183 0xff00ff00aa000000ff00ff00aa000000ff0000000000aa00ff0000000000aa000000000000000000000000000000000000000000000000000000000000000000cc00cc00880000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [515, 522, 573, 859, 879, 915, 916, 921, 1202, 1210, 1259]) (ps := [(14, [965], [1266])]) (by decide +kernel)

theorem c19183_0 : P.sumLeaves 24 19643392 1024 = 14358744 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 19183) (lo := 0) (len := 1024) (W := 14358744) check rows elimOK (by decide) (by decide) cover19183 (by decide)
  decide +kernel

theorem h19183 : P.leaf 34 19183 = 14358744 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 14358744)]) (.cons c19183_0 (.nil)) (by decide) (by decide))

theorem h5885 : P.leaf 34 5885 = 14358744 :=
  orient4 (v := 19183) (by decide) (by decide +kernel) h19183

theorem cover19198 : P.CoversSplit 24 10 19198 0xff00ff00aa000000ff00ff00aa000000f500f50000000000f500f500000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00880000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 573, 859, 866, 879, 915, 916, 921, 1202, 1210, 1259]) (ps := [(14, [965], [859, 1266])]) (by decide +kernel)

theorem c19198_0 : P.sumLeaves 24 19658752 1024 = 15690892 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 19198) (lo := 0) (len := 1024) (W := 15690892) check rows elimOK (by decide) (by decide) cover19198 (by decide)
  decide +kernel

theorem h19198 : P.leaf 34 19198 = 15690892 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 15690892)]) (.cons c19198_0 (.nil)) (by decide) (by decide))

theorem h5886 : P.leaf 34 5886 = 15690892 :=
  orient4 (v := 19198) (by decide) (by decide +kernel) h19198

theorem cover5887 : P.CoversSplit 24 10 5887 0xffffffffaaaa00000000000000000000ffffffffaaaa000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00880000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [573, 860, 867, 916, 1202, 1210, 1258, 1259, 1264, 1308]) (by decide +kernel)

theorem c5887_0 : P.sumLeaves 24 6028288 1024 = 33209680 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5887) (lo := 0) (len := 1024) (W := 33209680) check rows elimOK (by decide) (by decide) cover5887 (by decide)
  decide +kernel

theorem h5887 : P.leaf 34 5887 = 33209680 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 33209680)]) (.cons c5887_0 (.nil)) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(5851, 48), (5852, 48), (5853, 48), (5854, 48), (5855, 48), (5858, 24), (5859, 48), (5860, 48), (5861, 48), (5862, 48), (5863, 48), (5864, 48), (5865, 48), (5866, 48), (5867, 48), (5868, 48), (5869, 48), (5870, 48), (5871, 48), (5875, 24), (5876, 48), (5877, 48), (5878, 48), (5879, 48), (5880, 48), (5881, 48), (5882, 48), (5883, 48), (5884, 48), (5885, 48), (5886, 48), (5887, 48)]

theorem segOK : checkSeg 16 perms 5851 5968 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 5851 5968 1488 9381222816 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 9381222816)
    (SegSum.cons (w := 48) h5851 (SegSum.cons (w := 48) h5852 (SegSum.cons (w := 48) h5853 (SegSum.cons (w := 48) h5854 (SegSum.cons (w := 48) h5855 (SegSum.cons (w := 24) h5858 (SegSum.cons (w := 48) h5859 (SegSum.cons (w := 48) h5860 (SegSum.cons (w := 48) h5861 (SegSum.cons (w := 48) h5862 (SegSum.cons (w := 48) h5863 (SegSum.cons (w := 48) h5864 (SegSum.cons (w := 48) h5865 (SegSum.cons (w := 48) h5866 (SegSum.cons (w := 48) h5867 (SegSum.cons (w := 48) h5868 (SegSum.cons (w := 48) h5869 (SegSum.cons (w := 48) h5870 (SegSum.cons (w := 48) h5871 (SegSum.cons (w := 24) h5875 (SegSum.cons (w := 48) h5876 (SegSum.cons (w := 48) h5877 (SegSum.cons (w := 48) h5878 (SegSum.cons (w := 48) h5879 (SegSum.cons (w := 48) h5880 (SegSum.cons (w := 48) h5881 (SegSum.cons (w := 48) h5882 (SegSum.cons (w := 48) h5883 (SegSum.cons (w := 48) h5884 (SegSum.cons (w := 48) h5885 (SegSum.cons (w := 48) h5886 (SegSum.cons (w := 48) h5887 (show SegSum (P.leaf 34) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S4N1.C0.S30
