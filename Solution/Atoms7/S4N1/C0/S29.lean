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

namespace RACert.S4N1.C0.S29

open RACert RACert.Problem

theorem cover5628 : P.CoversSplit 24 10 5628 0xf0000000a000aa00000000000000000000000000000000000000000000000000c000000080088808c0c00000808888880000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 858, 860, 865, 867, 909, 1202, 1258, 1601]) (by decide +kernel)

theorem h5628 : P.leaf 34 5628 = 1145902 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 5628) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 5628) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5628) (weight := rowWeight keep0 twice0) (xs := [643, 647, 651, 655, 659, 663, 671, 694, 695, 702, 703, 707, 715, 719, 723, 735, 766, 767, 969, 971, 973, 975, 989, 991, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover5628 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover5629 : P.CoversSplit 24 10 5629 0xff00ff00aa00a000000000000000000000000000000000000000000000000000cc00cc0088008000000000000000000000000000000000000000000000000000ff00ff00aa00a0000000000000000000000000000000000000000000000000000003000300000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 858, 860, 865, 909, 916, 1202, 1258, 1601]) (by decide +kernel)

theorem c5629_0 : P.sumLeaves 24 5764096 1024 = 12565871 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5629) (lo := 0) (len := 1024) (W := 12565871) check rows elimOK (by decide) (by decide) cover5629 (by decide)
  decide +kernel

theorem h5629 : P.leaf 34 5629 = 12565871 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 12565871)]) (.cons c5629_0 (.nil)) (by decide) (by decide))

theorem cover5631 : P.CoversSplit 24 10 5631 0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaacccccccc88888888cccccccc88888888cccccccc88888888cccccccc88888888ffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaacccccccc88888888cccccccc88888888cccccccc88888888cccccccc88888888 :=
  coversSplit check rows (by decide) (by decide) (xs := [858, 860, 865, 916, 1202, 1258, 1601]) (by decide +kernel)

noncomputable def f5631 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (5766144 + i)

theorem c5631_0 : rowSum f5631 0 295 = 45829736 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 5631) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover5631 (by decide)
  decide +kernel

theorem c5631_1 : rowSum f5631 295 187 = 67492009 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 5631) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover5631 (by decide)
  decide +kernel

theorem c5631_2 : rowSum f5631 482 476 = 143413960 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 5631) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover5631 (by decide)
  decide +kernel

theorem c5631_3 : rowSum f5631 958 66 = 36921880 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 5631) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover5631 (by decide)
  decide +kernel

theorem sum5631 : rowSum f5631 0 1024 = 293657585 :=
  rowSum_append (F := f5631) (lo := 0) (n := 295) (m := 729) (A := 45829736) (B := 247827849) c5631_0 (rowSum_append (F := f5631) (lo := 295) (n := 187) (m := 542) (A := 67492009) (B := 180335840) c5631_1 (rowSum_append (F := f5631) (lo := 482) (n := 476) (m := 66) (A := 143413960) (B := 36921880) c5631_2 (c5631_3)))

theorem h5631 : P.leaf 34 5631 = 293657585 :=
  leaf_weighted (k := 24) (d := 10) (H := 5631) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 5631) (by decide) (by decide +kernel)) sum5631

theorem cover5811 : P.CoversSplit 24 10 5811 0xffff0000000000000000000000000000a0a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [517, 573, 860, 916, 1202, 1209, 1210, 1251, 1258, 1259, 1264, 1308]) (ps := [(8, [531, 580], [517, 573]), (14, [874, 923], [860, 916])]) (by decide +kernel)

theorem h5811 : P.leaf 34 5811 = 229440 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 5811) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 5811) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5811) (weight := rowWeight keep0 twice0) (xs := [506, 507, 510, 511, 885, 887, 893, 895, 1008, 1009, 1010, 1011, 1012, 1013, 1014, 1015, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover5811 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover5812 : P.CoversSplit 24 10 5812 0xfca9000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 508, 517, 573, 860, 867, 909, 916, 1202, 1209, 1251, 1258, 1259, 1264, 1308]) (ps := [(8, [468, 475], [468, 475])]) (by decide +kernel)

theorem h5812 : P.leaf 34 5812 = 73376 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 5812) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 5812) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5812) (weight := rowWeight keep0 twice0) (xs := [1008, 1011, 1013, 1015, 1018, 1019, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover5812 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover5813 : P.CoversSplit 24 10 5813 0xffff0000000000000000000000000000a0a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 517, 573, 860, 867, 909, 916, 1202, 1209, 1251, 1258, 1259, 1264, 1308]) (ps := [(8, [475, 580], [475, 517])]) (by decide +kernel)

theorem h5813 : P.leaf 34 5813 = 605792 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5813) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5813) (weight := fun _ => 1) (xs := [885, 887, 893, 895, 1008, 1009, 1010, 1011, 1012, 1013, 1014, 1015, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover5813 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover5815 : P.CoversSplit 24 10 5815 0xffff0000000000000000000000000000a0a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [517, 573, 860, 867, 909, 916, 1202, 1209, 1251, 1258, 1259, 1264, 1308]) (ps := [(8, [531, 580], [517, 573])]) (by decide +kernel)

theorem h5815 : P.leaf 34 5815 = 1542848 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 5815) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 5815) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5815) (weight := rowWeight keep0 twice0) (xs := [506, 507, 510, 511, 885, 887, 893, 895, 1008, 1009, 1010, 1011, 1012, 1013, 1014, 1015, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover5815 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover5820 : P.CoversSplit 24 10 5820 0xfca90000000000000000000000000000a0a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 508, 517, 524, 566, 573, 860, 916, 1202, 1209, 1251, 1258, 1259, 1264, 1308]) (ps := [(8, [531, 580], [517, 573])]) (by decide +kernel)

theorem h5820 : P.leaf 34 5820 = 649760 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 5820) (keep := keep4) (twice := twice4) rows (by decide) (by decide) bal4 (invRow4 (H := 5820) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5820) (weight := rowWeight keep4 twice4) (xs := [506, 507, 510, 511, 885, 887, 893, 895, 1008, 1011, 1013, 1015, 1018, 1019, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover5820 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover5821 : P.CoversSplit 24 10 5821 0xffff0000000000000000000000000000a0a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 517, 524, 566, 573, 860, 916, 1202, 1209, 1251, 1258, 1259, 1264, 1308]) (ps := [(8, [531, 580], [517, 573])]) (by decide +kernel)

theorem h5821 : P.leaf 34 5821 = 2139040 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 5821) (keep := keep2) (twice := twice2) rows (by decide) (by decide) bal2 (invRow2 (H := 5821) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5821) (weight := rowWeight keep2 twice2) (xs := [506, 507, 510, 511, 885, 887, 893, 895, 1008, 1009, 1010, 1011, 1012, 1013, 1014, 1015, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover5821 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover5823 : P.CoversSplit 24 10 5823 0xffff0000000000000000000000000000a0a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [517, 524, 566, 573, 860, 916, 1202, 1209, 1251, 1258, 1259, 1264, 1308]) (ps := [(8, [531, 580], [517, 573])]) (by decide +kernel)

theorem h5823 : P.leaf 34 5823 = 5236464 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 5823) (keep := keep0) (twice := twice0) rows (by decide) (by decide) bal0 (invRow0 (H := 5823) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5823) (weight := rowWeight keep0 twice0) (xs := [506, 507, 510, 511, 885, 887, 893, 895, 1008, 1009, 1010, 1011, 1012, 1013, 1014, 1015, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover5823 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover17675 : P.CoversSplit 24 10 17675 0x8000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 516, 517, 522, 528, 529, 572, 858, 865, 872, 915]) (by decide +kernel)

theorem h17675 : P.leaf 34 17675 = 30720 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 17675) (keep := keep5) (twice := twice5) rows (by decide) (by decide) bal5 (invRow5 (H := 17675) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 17675) (weight := rowWeight keep5 twice5) (xs := [383, 511, 895, 1023]) check rows elimOK (by decide) (by decide) cover17675 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h5826 : P.leaf 34 5826 = 30720 :=
  orient25 (v := 17675) (by decide) (by decide +kernel) h17675

theorem cover19097 : P.CoversSplit 24 10 19097 0xaa00aa0000000000aa00aa0000000000a000000000000000a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [467, 473, 474, 487, 516, 517, 524, 528, 859, 1210]) (by decide +kernel)

theorem h19097 : P.leaf 34 19097 = 519056 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 19097) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 19097) (weight := fun _ => 1) (xs := [829, 831, 893, 895, 937, 939, 941, 943, 953, 955, 957, 959, 1001, 1003, 1005, 1007, 1017, 1019, 1021, 1023]) check rows elimOK (by decide) (by decide) cover19097 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h5827 : P.leaf 34 5827 = 519056 :=
  orient4 (v := 19097) (by decide) (by decide +kernel) h19097

theorem cover5828 : P.CoversSplit 24 10 5828 0x8080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 475, 508, 515, 516, 522, 536, 566, 1202, 1209, 1259, 1264]) (by decide +kernel)

theorem h5828 : P.leaf 34 5828 = 12416 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5828) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5828) (weight := fun _ => 1) (xs := [1015, 1023]) check rows elimOK (by decide) (by decide) cover5828 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover5829 : P.CoversSplit 24 10 5829 0xcccc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 475, 515, 522, 536, 566, 860, 916, 1202, 1209, 1259, 1264]) (by decide +kernel)

theorem h5829 : P.leaf 34 5829 = 310332 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5829) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5829) (weight := fun _ => 1) (xs := [1010, 1011, 1014, 1015, 1018, 1019, 1022, 1023]) check rows elimOK (by decide) (by decide) cover5829 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover17707 : P.CoversSplit 24 10 17707 0x8000000080000000000000000000000080000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000080000000800000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 517, 522, 529, 572, 858, 860, 865, 872, 915, 916]) (by decide +kernel)

theorem h17707 : P.leaf 34 17707 = 175008 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 17707) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 17707) (weight := fun _ => 1) (xs := [383, 479, 511, 842, 895, 991, 1023]) check rows elimOK (by decide) (by decide) cover17707 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h5830 : P.leaf 34 5830 = 175008 :=
  orient25 (v := 17707) (by decide) (by decide +kernel) h17707

theorem cover5831 : P.CoversSplit 24 10 5831 0xffff0000000000000000000000000000ffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [475, 515, 522, 536, 566, 573, 860, 916, 1202, 1209, 1259, 1264]) (by decide +kernel)

theorem h5831 : P.leaf 34 5831 = 3193868 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5831) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5831) (weight := fun _ => 1) (xs := [880, 881, 882, 883, 884, 885, 886, 887, 888, 889, 890, 891, 892, 893, 894, 895, 1008, 1009, 1010, 1011, 1012, 1013, 1014, 1015, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover5831 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover5832 : P.CoversSplit 24 10 5832 0x8080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 508, 515, 516, 522, 523, 536, 573, 860, 916, 1202, 1209, 1210, 1259, 1264, 1308]) (by decide +kernel)

theorem h5832 : P.leaf 34 5832 = 9136 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5832) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5832) (weight := fun _ => 1) (xs := [1015, 1023]) check rows elimOK (by decide) (by decide) cover5832 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover5833 : P.CoversSplit 24 10 5833 0xcccc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 515, 522, 523, 536, 573, 860, 916, 1202, 1209, 1251, 1259, 1308]) (by decide +kernel)

theorem h5833 : P.leaf 34 5833 = 60800 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5833) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5833) (weight := fun _ => 1) (xs := [1010, 1011, 1014, 1015, 1018, 1019, 1022, 1023]) check rows elimOK (by decide) (by decide) cover5833 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover5834 : P.CoversSplit 24 10 5834 0xa0a00000000000000000000000000000a0a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 515, 516, 522, 523, 536, 860, 916, 1202, 1209, 1210, 1259]) (by decide +kernel)

theorem h5834 : P.leaf 34 5834 = 91960 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5834) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5834) (weight := fun _ => 1) (xs := [885, 887, 893, 895, 1013, 1015, 1021, 1023]) check rows elimOK (by decide) (by decide) cover5834 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover5835 : P.CoversSplit 24 10 5835 0xffff0000000000000000000000000000ffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 516, 522, 523, 536, 860, 916, 1202, 1209, 1259]) (by decide +kernel)

theorem h5835 : P.leaf 34 5835 = 1166808 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5835) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5835) (weight := fun _ => 1) (xs := [880, 881, 882, 883, 884, 885, 886, 887, 888, 889, 890, 891, 892, 893, 894, 895, 1008, 1009, 1010, 1011, 1012, 1013, 1014, 1015, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover5835 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover5836 : P.CoversSplit 24 10 5836 0x8080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 508, 515, 516, 522, 536, 573, 860, 916, 1202, 1209, 1210, 1259, 1264, 1308]) (by decide +kernel)

theorem h5836 : P.leaf 34 5836 = 40272 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5836) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5836) (weight := fun _ => 1) (xs := [1015, 1023]) check rows elimOK (by decide) (by decide) cover5836 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover5837 : P.CoversSplit 24 10 5837 0xcccc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 515, 522, 536, 573, 860, 916, 1202, 1209, 1251, 1259, 1264, 1308]) (by decide +kernel)

theorem h5837 : P.leaf 34 5837 = 435048 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5837) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5837) (weight := fun _ => 1) (xs := [1010, 1011, 1014, 1015, 1018, 1019, 1022, 1023]) check rows elimOK (by decide) (by decide) cover5837 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover5838 : P.CoversSplit 24 10 5838 0xa0a00000000000000000000000000000a0a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 515, 516, 522, 536, 860, 916, 1202, 1209, 1210, 1259, 1264]) (by decide +kernel)

theorem h5838 : P.leaf 34 5838 = 531420 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5838) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5838) (weight := fun _ => 1) (xs := [885, 887, 893, 895, 1013, 1015, 1021, 1023]) check rows elimOK (by decide) (by decide) cover5838 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover5839 : P.CoversSplit 24 10 5839 0xffff0000000000000000000000000000ffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 522, 536, 860, 916, 1202, 1209, 1258, 1259, 1264]) (by decide +kernel)

theorem h5839 : P.leaf 34 5839 = 5180176 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5839) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5839) (weight := fun _ => 1) (xs := [880, 881, 882, 883, 884, 885, 886, 887, 888, 889, 890, 891, 892, 893, 894, 895, 1008, 1009, 1010, 1011, 1012, 1013, 1014, 1015, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover5839 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover19099 : P.CoversSplit 24 10 19099 0xaa00aa0000000000aa00aa0000000000a000000000000000a000000000000000000000000000000000000000000000000000000000000000000000000000000088008800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [467, 487, 516, 517, 524, 528, 573, 859, 916, 921, 1210, 1259]) (ps := [(8, [615], [1266])]) (by decide +kernel)

theorem h19099 : P.leaf 34 19099 = 2002296 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 19099) (keep := keep5) (twice := twice5) rows (by decide) (by decide) bal5 (invRow5 (H := 19099) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 19099) (weight := rowWeight keep5 twice5) (xs := [491, 495, 507, 511, 829, 831, 893, 895, 937, 939, 941, 943, 953, 955, 957, 959, 1001, 1003, 1005, 1007, 1017, 1019, 1021, 1023]) check rows elimOK (by decide) (by decide) cover19099 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h5843 : P.leaf 34 5843 = 2002296 :=
  orient4 (v := 19099) (by decide) (by decide +kernel) h19099

theorem cover19114 : P.CoversSplit 24 10 19114 0xa0000000a0000000a0000000a0000000a000000000000500a000000000000500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 515, 517, 522, 524, 573, 859, 916, 921, 1202]) (by decide +kernel)

theorem h19114 : P.leaf 34 19114 = 218140 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 19114) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 19114) (weight := fun _ => 1) (xs := [776, 778, 829, 831, 840, 842, 893, 895, 925, 927, 957, 959, 989, 991, 1021, 1023]) check rows elimOK (by decide) (by decide) cover19114 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h5844 : P.leaf 34 5844 = 218140 :=
  orient4 (v := 19114) (by decide) (by decide +kernel) h19114

theorem cover19115 : P.CoversSplit 24 10 19115 0xff00ff00aa000000ff00ff00aa000000ff0000000000a000ff0000000000a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 517, 522, 524, 573, 916, 921, 1202, 1210]) (by decide +kernel)

theorem c19115_0 : P.sumLeaves 24 19573760 1024 = 5075216 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 19115) (lo := 0) (len := 1024) (W := 5075216) check rows elimOK (by decide) (by decide) cover19115 (by decide)
  decide +kernel

theorem h19115 : P.leaf 34 19115 = 5075216 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 5075216)]) (.cons c19115_0 (.nil)) (by decide) (by decide))

theorem h5845 : P.leaf 34 5845 = 5075216 :=
  orient4 (v := 19115) (by decide) (by decide +kernel) h19115

theorem cover5846 : P.CoversSplit 24 10 5846 0xffffffffa0a000000000000000000000a0a0a5a50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 475, 516, 573, 860, 916, 1202, 1210, 1259, 1264, 1308]) (by decide +kernel)

theorem c5846_0 : P.sumLeaves 24 5986304 1024 = 2807514 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5846) (lo := 0) (len := 1024) (W := 2807514) check rows elimOK (by decide) (by decide) cover5846 (by decide)
  decide +kernel

theorem h5846 : P.leaf 34 5846 = 2807514 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 2807514)]) (.cons c5846_0 (.nil)) (by decide) (by decide))

theorem cover5847 : P.CoversSplit 24 10 5847 0xffffffffa0a000000000000000000000ffffffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [475, 516, 573, 860, 916, 1202, 1210, 1217, 1259, 1264, 1308]) (by decide +kernel)

theorem c5847_0 : P.sumLeaves 24 5987328 1024 = 13135988 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5847) (lo := 0) (len := 1024) (W := 13135988) check rows elimOK (by decide) (by decide) cover5847 (by decide)
  decide +kernel

theorem h5847 : P.leaf 34 5847 = 13135988 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 13135988)]) (.cons c5847_0 (.nil)) (by decide) (by decide))

theorem cover35658 : P.CoversSplit 24 10 35658 0xaa000000aa000000aa000000aa00000088000000000000008800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 515, 516, 522, 572, 859, 879, 915, 921, 1202, 1217, 1251, 1258]) (ps := [(5, [474], [516]), (7, [509], [565, 572]), (8, [467], [523])]) (by decide +kernel)

theorem h35658 : P.leaf 34 35658 = 374980 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 35658) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 35658) (weight := fun _ => 1) (xs := [827, 831, 891, 895, 921, 923, 925, 927, 953, 955, 957, 959, 985, 987, 989, 991, 1017, 1019, 1021, 1023]) check rows elimOK (by decide) (by decide) cover35658 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h5848 : P.leaf 34 5848 = 374980 :=
  orient5 (v := 35658) (by decide) (by decide +kernel) h35658

theorem cover19147 : P.CoversSplit 24 10 19147 0xff00ff0000000000ff00ff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [467, 515, 516, 522, 536, 573, 859, 879, 915, 916, 921]) (ps := [(14, [965], [859, 1266])]) (by decide +kernel)

theorem h19147 : P.leaf 34 19147 = 1750924 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 19147) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 19147) (weight := fun _ => 1) (xs := [936, 937, 938, 939, 940, 941, 942, 943, 952, 953, 954, 955, 956, 957, 958, 959, 1000, 1001, 1002, 1003, 1004, 1005, 1006, 1007, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover19147 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h5849 : P.leaf 34 5849 = 1750924 :=
  orient4 (v := 19147) (by decide) (by decide +kernel) h19147

theorem cover19162 : P.CoversSplit 24 10 19162 0xff00ff0000000000ff00ff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 467, 487, 516, 573, 859, 879, 915, 916, 921, 1259]) (by decide +kernel)

theorem c19162_0 : P.sumLeaves 24 19621888 1024 = 1620040 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 19162) (lo := 0) (len := 1024) (W := 1620040) check rows elimOK (by decide) (by decide) cover19162 (by decide)
  decide +kernel

theorem h19162 : P.leaf 34 19162 = 1620040 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1620040)]) (.cons c19162_0 (.nil)) (by decide) (by decide))

theorem h5850 : P.leaf 34 5850 = 1620040 :=
  orient4 (v := 19162) (by decide) (by decide +kernel) h19162

def seg : List (ℕ × ℕ) := [(5628, 24), (5629, 48), (5631, 24), (5811, 6), (5812, 24), (5813, 48), (5815, 24), (5820, 12), (5821, 24), (5823, 12), (5826, 24), (5827, 48), (5828, 48), (5829, 48), (5830, 48), (5831, 48), (5832, 48), (5833, 48), (5834, 48), (5835, 48), (5836, 48), (5837, 48), (5838, 48), (5839, 48), (5843, 24), (5844, 48), (5845, 48), (5846, 48), (5847, 48), (5848, 48), (5849, 48), (5850, 48)]

theorem segOK : checkSeg 16 perms 5628 5851 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 5628 5851 1254 9680490456 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 9680490456)
    (SegSum.cons (w := 24) h5628 (SegSum.cons (w := 48) h5629 (SegSum.cons (w := 24) h5631 (SegSum.cons (w := 6) h5811 (SegSum.cons (w := 24) h5812 (SegSum.cons (w := 48) h5813 (SegSum.cons (w := 24) h5815 (SegSum.cons (w := 12) h5820 (SegSum.cons (w := 24) h5821 (SegSum.cons (w := 12) h5823 (SegSum.cons (w := 24) h5826 (SegSum.cons (w := 48) h5827 (SegSum.cons (w := 48) h5828 (SegSum.cons (w := 48) h5829 (SegSum.cons (w := 48) h5830 (SegSum.cons (w := 48) h5831 (SegSum.cons (w := 48) h5832 (SegSum.cons (w := 48) h5833 (SegSum.cons (w := 48) h5834 (SegSum.cons (w := 48) h5835 (SegSum.cons (w := 48) h5836 (SegSum.cons (w := 48) h5837 (SegSum.cons (w := 48) h5838 (SegSum.cons (w := 48) h5839 (SegSum.cons (w := 24) h5843 (SegSum.cons (w := 48) h5844 (SegSum.cons (w := 48) h5845 (SegSum.cons (w := 48) h5846 (SegSum.cons (w := 48) h5847 (SegSum.cons (w := 48) h5848 (SegSum.cons (w := 48) h5849 (SegSum.cons (w := 48) h5850 (show SegSum (P.leaf 34) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S4N1.C0.S29
