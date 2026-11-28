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

namespace RACert.S4N1.C0.S31

open RACert RACert.Problem

theorem cover9507 : P.CoversSplit 24 10 9507 0x8000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 515, 517, 522, 524, 529, 565, 572, 858, 865, 1202, 1258, 1266]) (by decide +kernel)

theorem h9507 : P.leaf 34 9507 = 48640 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 9507) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 9507) (weight := fun _ => 1) (xs := [720, 1023]) check rows elimOK (by decide) (by decide) cover9507 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h5968 : P.leaf 34 5968 = 48640 :=
  orient32 (v := 9507) (by decide) (by decide +kernel) h9507

theorem cover9523 : P.CoversSplit 24 10 9523 0xffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [480, 486, 517, 572, 860, 867, 872, 908, 915]) (ps := [(8, [1266], [1272])]) (by decide +kernel)

theorem h9523 : P.leaf 34 9523 = 811308 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 9523) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 9523) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 9523) (weight := rowWeight keep1 twice1) (xs := [1008, 1009, 1010, 1011, 1012, 1013, 1014, 1015, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover9523 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h5969 : P.leaf 34 5969 = 811308 :=
  orient32 (v := 9523) (by decide) (by decide +kernel) h9523

theorem cover10035 : P.CoversSplit 24 10 10035 0xffff0000000000000000000000000000a0a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [468, 474, 517, 572, 860, 915, 1209, 1251, 1258, 1264]) (by decide +kernel)

theorem h10035 : P.leaf 34 10035 = 2144792 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 10035) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 10035) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 10035) (weight := rowWeight keep1 twice1) (xs := [383, 506, 507, 510, 511, 885, 887, 893, 895, 1008, 1009, 1010, 1011, 1012, 1013, 1014, 1015, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover10035 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h5971 : P.leaf 34 5971 = 2144792 :=
  orient32 (v := 10035) (by decide) (by decide +kernel) h10035

theorem cover25891 : P.CoversSplit 24 10 25891 0x8000000080000000000000000000000080000000000004000000000000000000800000008000000000000000000000008000000000000400000000000000000080000000800000000000000000000000800000000000000000000000000000000000000000000000002000000020000000000000000000000000000000000001 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 517, 522, 529, 572, 858, 865, 1202]) (by decide +kernel)

theorem h25891 : P.leaf 34 25891 = 520316 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 25891) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 25891) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 25891) (weight := rowWeight keep1 twice1) (xs := [0, 149, 181, 383, 479, 511, 586, 639, 735, 767, 842, 895, 991, 1023]) check rows elimOK (by decide) (by decide) cover25891 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h5972 : P.leaf 34 5972 = 520316 :=
  orient32 (v := 25891) (by decide) (by decide +kernel) h25891

theorem cover25907 : P.CoversSplit 24 10 25907 0xfffffffffafa0000fffffffffafa0000f000f00000000000f000000000000000ffccffccfac800000000000000000000f000f000000000000000000000000000f000f000f0000000f0000000f0000000f000f00000000000f0000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [517, 529, 572, 858, 860, 865, 872, 915, 1202, 1251, 1259, 1264, 1308, 1601]) (ps := [(14, [867, 908], [860, 915])]) (by decide +kernel)

noncomputable def f25907 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (26528768 + i)

theorem c25907_0 : rowSum f25907 0 1024 = 8597201 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 25907) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover25907 (by decide)
  decide +kernel

theorem sum25907 : rowSum f25907 0 1024 = 8597201 :=
  c25907_0

theorem h25907 : P.leaf 34 25907 = 8597201 :=
  leaf_weighted (k := 24) (d := 10) (H := 25907) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 25907) (by decide) (by decide +kernel)) sum25907

theorem h5973 : P.leaf 34 5973 = 8597201 :=
  orient32 (v := 25907) (by decide) (by decide +kernel) h25907

theorem cover26419 : P.CoversSplit 24 10 26419 0xfffffffffafa0000fffffffffafa0000ffffffff00000000ffff000000000000ffccffccfac800000000000000000000ffccffcc000000000000000000000000fffffffffafa0000ffff0000fafa0000ffffffff00000000ffff0000000000000000000000000000000000000000000000000000900800000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [517, 529, 572, 860, 872, 915, 1202, 1217, 1251, 1259, 1264, 1308, 1601, 1609]) (by decide +kernel)

noncomputable def f26419 (i : ℕ) := rowWeight keep5 twice5 i * P.leaf 24 (27053056 + i)

theorem c26419_0 : rowSum f26419 0 508 = 14029564 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 26419) (keep := keep5) (twice := twice5) check rows elimOK (by decide) (by decide) cover26419 (by decide)
  decide +kernel

theorem c26419_1 : rowSum f26419 508 516 = 23363520 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 26419) (keep := keep5) (twice := twice5) check rows elimOK (by decide) (by decide) cover26419 (by decide)
  decide +kernel

theorem sum26419 : rowSum f26419 0 1024 = 37393084 :=
  rowSum_append (F := f26419) (lo := 0) (n := 508) (m := 516) (A := 14029564) (B := 23363520) c26419_0 (c26419_1)

theorem h26419 : P.leaf 34 26419 = 37393084 :=
  leaf_weighted (k := 24) (d := 10) (H := 26419) (keep := keep5) (twice := twice5) rows (by decide) (by decide) (bal5) (invRow5 (H := 26419) (by decide) (by decide +kernel)) sum26419

theorem h5975 : P.leaf 34 5975 = 37393084 :=
  orient32 (v := 26419) (by decide) (by decide +kernel) h26419

theorem cover42275 : P.CoversSplit 24 10 42275 0xffffffff00000000ffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008000cc0000000000a0a08000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [515, 517, 522, 529, 572, 858, 860, 865, 915, 1202, 1258, 1308, 1601]) (ps := [(7, [565], [572]), (9, [524], [517]), (13, [908], [915]), (15, [867], [860])]) (by decide +kernel)

noncomputable def f42275 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (43289600 + i)

theorem c42275_0 : rowSum f42275 0 1024 = 820446 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 42275) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover42275 (by decide)
  decide +kernel

theorem sum42275 : rowSum f42275 0 1024 = 820446 :=
  c42275_0

theorem h42275 : P.leaf 34 42275 = 820446 :=
  leaf_weighted (k := 24) (d := 10) (H := 42275) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 42275) (by decide) (by decide +kernel)) sum42275

theorem h5976 : P.leaf 34 5976 = 820446 :=
  orient32 (v := 42275) (by decide) (by decide +kernel) h42275

theorem cover42291 : P.CoversSplit 24 10 42291 0xffffffff00000000ffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008000cc0000000000a0a00000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [480, 486, 517, 572, 860, 872, 915]) (ps := [(13, [908], [915]), (15, [867], [860]), (16, [528, 1251], [1258])]) (by decide +kernel)

noncomputable def f42291 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (43305984 + i)

theorem c42291_0 : rowSum f42291 0 1024 = 2076078 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 42291) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover42291 (by decide)
  decide +kernel

theorem sum42291 : rowSum f42291 0 1024 = 2076078 :=
  c42291_0

theorem h42291 : P.leaf 34 42291 = 2076078 :=
  leaf_weighted (k := 24) (d := 10) (H := 42291) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 42291) (by decide) (by decide +kernel)) sum42291

theorem h5977 : P.leaf 34 5977 = 2076078 :=
  orient32 (v := 42291) (by decide) (by decide +kernel) h42291

theorem cover42803 : P.CoversSplit 24 10 42803 0xffffffff00000000ffffffff00000000a0a0000000000000a0a00000000000000000000000000000000000000000000000000000000000000000000000000000cc00cc000000000000000000000000008000cc0000000000a0a00000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [468, 474, 517, 572, 860, 915, 1209, 1258]) (ps := [(16, [528, 871, 1251], [1258])]) (by decide +kernel)

noncomputable def f42803 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (43830272 + i)

theorem c42803_0 : rowSum f42803 0 1024 = 7164357 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 42803) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover42803 (by decide)
  decide +kernel

theorem sum42803 : rowSum f42803 0 1024 = 7164357 :=
  c42803_0

theorem h42803 : P.leaf 34 42803 = 7164357 :=
  leaf_weighted (k := 24) (d := 10) (H := 42803) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 42803) (by decide) (by decide +kernel)) sum42803

theorem h5979 : P.leaf 34 5979 = 7164357 :=
  orient32 (v := 42803) (by decide) (by decide +kernel) h42803

theorem cover58659 : P.CoversSplit 24 10 58659 0xfffffffffefa0000fffffffffefa00008000cc00000000008000cc0000000000ffecffecfee8000000000000000000008000cc000000000000000000000000008000800080000000a0a0a0a0a0a00000800080000000000080009009000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 517, 522, 529, 572, 858, 860, 865, 872, 915, 1202, 1601]) (by decide +kernel)

noncomputable def f58659 (i : ℕ) := rowWeight keep5 twice5 i * P.leaf 24 (60066816 + i)

theorem c58659_0 : rowSum f58659 0 1024 = 3793930 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 58659) (keep := keep5) (twice := twice5) check rows elimOK (by decide) (by decide) cover58659 (by decide)
  decide +kernel

theorem sum58659 : rowSum f58659 0 1024 = 3793930 :=
  c58659_0

theorem h58659 : P.leaf 34 58659 = 3793930 :=
  leaf_weighted (k := 24) (d := 10) (H := 58659) (keep := keep5) (twice := twice5) rows (by decide) (by decide) (bal5) (invRow5 (H := 58659) (by decide) (by decide +kernel)) sum58659

theorem h5980 : P.leaf 34 5980 = 3793930 :=
  orient32 (v := 58659) (by decide) (by decide +kernel) h58659

theorem cover58675 : P.CoversSplit 24 10 58675 0xfffffffffffa0000fffffffffffa0000f000ff0000000000f000ff0000000000fffcfffcfff800000000000000000000f000ff00000000000000000000000000f000f000f0000000f0f0f0f0f0f00000f000f00000000000f000f00f000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [517, 529, 572, 858, 860, 865, 872, 915, 1202, 1601]) (by decide +kernel)

noncomputable def f58675 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (60083200 + i)

theorem c58675_0 : rowSum f58675 0 945 = 8950895 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 58675) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover58675 (by decide)
  decide +kernel

theorem c58675_1 : rowSum f58675 945 79 = 4909648 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 58675) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover58675 (by decide)
  decide +kernel

theorem sum58675 : rowSum f58675 0 1024 = 13860543 :=
  rowSum_append (F := f58675) (lo := 0) (n := 945) (m := 79) (A := 8950895) (B := 4909648) c58675_0 (c58675_1)

theorem h58675 : P.leaf 34 58675 = 13860543 :=
  leaf_weighted (k := 24) (d := 10) (H := 58675) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 58675) (by decide) (by decide +kernel)) sum58675

theorem h5981 : P.leaf 34 5981 = 13860543 :=
  orient32 (v := 58675) (by decide) (by decide +kernel) h58675

theorem cover5983 : P.CoversSplit 24 10 5983 0xffffffffa0a0a0a0ffffffffa0a0a0a0ffffffff0000a0a0ffffffff0000a0a0cc00cc0080008000cc00cc0080008000cc00cc0000008000cc00cc0000008000ffffffffa0a0a0a0ffffffffa0a0a0a0ffffffffa0a0a0a0ffffffffa0a0a0a00000000000000000cc00cc0080008000cc00cc0080008000cc00cc0080008000 :=
  coversSplit check rows (by decide) (by decide) (xs := [516, 572, 1202, 1217, 1258, 1259, 1601, 1609]) (by decide +kernel)

noncomputable def f5983 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (6126592 + i)

theorem c5983_0 : rowSum f5983 0 439 = 3264258 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 5983) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover5983 (by decide)
  decide +kernel

theorem c5983_1 : rowSum f5983 439 572 = 43361005 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 5983) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover5983 (by decide)
  decide +kernel

theorem c5983_2 : rowSum f5983 1011 13 = 8864848 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 5983) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover5983 (by decide)
  decide +kernel

theorem sum5983 : rowSum f5983 0 1024 = 55490111 :=
  rowSum_append (F := f5983) (lo := 0) (n := 439) (m := 585) (A := 3264258) (B := 52225853) c5983_0 (rowSum_append (F := f5983) (lo := 439) (n := 572) (m := 13) (A := 43361005) (B := 8864848) c5983_1 (c5983_2))

theorem h5983 : P.leaf 34 5983 = 55490111 :=
  leaf_weighted (k := 24) (d := 10) (H := 5983) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 5983) (by decide) (by decide +kernel)) sum5983

theorem cover19212 : P.CoversSplit 24 10 19212 0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 472, 473, 508, 515, 516, 517, 565, 572, 879, 916, 1259]) (ps := [(3, [479], [522])]) (by decide +kernel)

theorem h19212 : P.leaf 34 19212 = 8320 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 19212) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 19212) (weight := fun _ => 1) (xs := [511, 1023]) check rows elimOK (by decide) (by decide) cover19212 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h5984 : P.leaf 34 5984 = 8320 :=
  orient4 (v := 19212) (by decide) (by decide +kernel) h19212

theorem cover19213 : P.CoversSplit 24 10 19213 0x8800880000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000088008800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 515, 516, 522, 523, 528, 529, 565, 572, 915, 916]) (by decide +kernel)

theorem h19213 : P.leaf 34 19213 = 216328 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 19213) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 19213) (weight := fun _ => 1) (xs := [491, 495, 507, 511, 1003, 1007, 1019, 1023]) check rows elimOK (by decide) (by decide) cover19213 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h5985 : P.leaf 34 5985 = 216328 :=
  orient4 (v := 19213) (by decide) (by decide +kernel) h19213

theorem cover51467 : P.CoversSplit 24 10 51467 0xaa000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000aa000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [515, 517, 522, 528, 572, 859, 865, 879, 915, 921]) (ps := [(8, [615], [565])]) (by decide +kernel)

theorem h51467 : P.leaf 34 51467 = 103792 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 51467) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 51467) (weight := fun _ => 1) (xs := [383, 505, 507, 509, 511, 895, 1017, 1019, 1021, 1023]) check rows elimOK (by decide) (by decide) cover51467 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h5986 : P.leaf 34 5986 = 103792 :=
  orient25 (v := 51467) (by decide) (by decide +kernel) h51467

theorem cover19229 : P.CoversSplit 24 10 19229 0xaa00aa0000000000aa00aa0000000000a000000000000000a0000000000000000000000000000000000000000000000000000000000000000000000000000000aa00aa0000000000aa00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 516, 517, 523, 528, 572, 859, 866, 916, 921, 1210, 1264]) (ps := [(8, [615], [1266])]) (by decide +kernel)

theorem h19229 : P.leaf 34 19229 = 1864711 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 19229) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 19229) (weight := fun _ => 1) (xs := [441, 443, 445, 447, 489, 491, 493, 495, 505, 507, 509, 511, 829, 831, 893, 895, 937, 939, 941, 943, 953, 955, 957, 959, 1001, 1003, 1005, 1007, 1017, 1019, 1021, 1023]) check rows elimOK (by decide) (by decide) cover19229 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h5987 : P.leaf 34 5987 = 1864711 :=
  orient4 (v := 19229) (by decide) (by decide +kernel) h19229

theorem cover19244 : P.CoversSplit 24 10 19244 0x8000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 472, 473, 508, 515, 517, 522, 572, 859, 879, 916]) (by decide +kernel)

theorem h19244 : P.leaf 34 19244 = 102696 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 19244) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 19244) (weight := fun _ => 1) (xs := [383, 511, 895, 1023]) check rows elimOK (by decide) (by decide) cover19244 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h5988 : P.leaf 34 5988 = 102696 :=
  orient4 (v := 19244) (by decide) (by decide +kernel) h19244

theorem cover5989 : P.CoversSplit 24 10 5989 0xcc000000000000000000000000000000cc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 515, 522, 524, 572, 860, 916, 1202, 1209, 1251, 1258, 1259]) (ps := [(14, [1266], [1272])]) (by decide +kernel)

theorem h5989 : P.leaf 34 5989 = 1098124 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5989) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5989) (weight := fun _ => 1) (xs := [506, 507, 510, 511, 890, 891, 894, 895, 1018, 1019, 1022, 1023]) check rows elimOK (by decide) (by decide) cover5989 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover5990 : P.CoversSplit 24 10 5990 0xaaaa0000000000000000000000000000a0a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000aaaa0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 515, 522, 524, 860, 916, 1209, 1251, 1259, 1264]) (ps := [(14, [1266], [1272])]) (by decide +kernel)

theorem h5990 : P.leaf 34 5990 = 2628004 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5990) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5990) (weight := fun _ => 1) (xs := [497, 499, 501, 503, 505, 507, 509, 511, 885, 887, 893, 895, 1009, 1011, 1013, 1015, 1017, 1019, 1021, 1023]) check rows elimOK (by decide) (by decide) cover5990 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover5991 : P.CoversSplit 24 10 5991 0xffff0000000000000000000000000000ffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [515, 522, 524, 860, 916, 1202, 1209, 1251, 1258, 1259, 1264]) (ps := [(14, [1266], [1272])]) (by decide +kernel)

theorem c5991_0 : P.sumLeaves 24 6134784 1024 = 12279259 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5991) (lo := 0) (len := 1024) (W := 12279259) check rows elimOK (by decide) (by decide) cover5991 (by decide)
  decide +kernel

theorem h5991 : P.leaf 34 5991 = 12279259 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 12279259)]) (.cons c5991_0 (.nil)) (by decide) (by decide))

theorem cover5992 : P.CoversSplit 24 10 5992 0x8800000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000088000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 515, 522, 523, 565, 572, 860, 916, 1202, 1209, 1251, 1258, 1259]) (ps := [(14, [558], [860, 1272])]) (by decide +kernel)

theorem h5992 : P.leaf 34 5992 = 101824 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5992) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5992) (weight := fun _ => 1) (xs := [507, 511, 895, 1019, 1023]) check rows elimOK (by decide) (by decide) cover5992 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover5993 : P.CoversSplit 24 10 5993 0xcc000000000000000000000000000000cc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 515, 522, 523, 572, 860, 916, 1202, 1209, 1258, 1259]) (ps := [(14, [558], [1272])]) (by decide +kernel)

theorem h5993 : P.leaf 34 5993 = 637104 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5993) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5993) (weight := fun _ => 1) (xs := [506, 507, 510, 511, 890, 891, 894, 895, 1018, 1019, 1022, 1023]) check rows elimOK (by decide) (by decide) cover5993 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover5994 : P.CoversSplit 24 10 5994 0xaaaa0000000000000000000000000000a0a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000aaaa0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 515, 522, 523, 565, 860, 916, 1209, 1251, 1259, 1264]) (ps := [(14, [874, 1266], [860, 1272])]) (by decide +kernel)

theorem h5994 : P.leaf 34 5994 = 739236 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5994) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5994) (weight := fun _ => 1) (xs := [497, 499, 501, 503, 505, 507, 509, 511, 885, 887, 893, 895, 1009, 1011, 1013, 1015, 1017, 1019, 1021, 1023]) check rows elimOK (by decide) (by decide) cover5994 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover5995 : P.CoversSplit 24 10 5995 0xffff0000000000000000000000000000ffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [515, 522, 523, 572, 860, 916, 1202, 1209, 1259, 1264]) (ps := [(14, [1266], [1272])]) (by decide +kernel)

theorem c5995_0 : P.sumLeaves 24 6138880 1024 = 4168548 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5995) (lo := 0) (len := 1024) (W := 4168548) check rows elimOK (by decide) (by decide) cover5995 (by decide)
  decide +kernel

theorem h5995 : P.leaf 34 5995 = 4168548 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 4168548)]) (.cons c5995_0 (.nil)) (by decide) (by decide))

theorem cover5996 : P.CoversSplit 24 10 5996 0x8800000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000088000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 515, 522, 572, 860, 916, 1202, 1209, 1251, 1258, 1259]) (ps := [(14, [1266], [1272])]) (by decide +kernel)

theorem h5996 : P.leaf 34 5996 = 383572 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5996) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5996) (weight := fun _ => 1) (xs := [507, 511, 895, 1019, 1023]) check rows elimOK (by decide) (by decide) cover5996 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover5997 : P.CoversSplit 24 10 5997 0xcc000000000000000000000000000000cc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 515, 522, 572, 860, 916, 1202, 1209, 1251, 1258, 1259]) (ps := [(14, [1266], [1272])]) (by decide +kernel)

theorem h5997 : P.leaf 34 5997 = 2813462 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5997) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5997) (weight := fun _ => 1) (xs := [506, 507, 510, 511, 890, 891, 894, 895, 1018, 1019, 1022, 1023]) check rows elimOK (by decide) (by decide) cover5997 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover5998 : P.CoversSplit 24 10 5998 0xaaaa0000000000000000000000000000a0a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000aaaa0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 515, 522, 860, 916, 1209, 1251, 1259, 1264]) (ps := [(14, [1266], [1272])]) (by decide +kernel)

theorem h5998 : P.leaf 34 5998 = 4213278 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 5998) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 5998) (weight := fun _ => 1) (xs := [497, 499, 501, 503, 505, 507, 509, 511, 885, 887, 893, 895, 1009, 1011, 1013, 1015, 1017, 1019, 1021, 1023]) check rows elimOK (by decide) (by decide) cover5998 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover5999 : P.CoversSplit 24 10 5999 0xffff0000000000000000000000000000ffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [515, 522, 860, 916, 1202, 1209, 1251, 1258, 1259, 1264]) (ps := [(14, [1266], [1272])]) (by decide +kernel)

theorem c5999_0 : P.sumLeaves 24 6142976 1024 = 17251744 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 5999) (lo := 0) (len := 1024) (W := 17251744) check rows elimOK (by decide) (by decide) cover5999 (by decide)
  decide +kernel

theorem h5999 : P.leaf 34 5999 = 17251744 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 17251744)]) (.cons c5999_0 (.nil)) (by decide) (by decide))

theorem cover9571 : P.CoversSplit 24 10 9571 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 515, 522, 523, 565, 572, 858, 865, 867, 872, 1209, 1210, 1258]) (by decide +kernel)

theorem h9571 : P.leaf 34 9571 = 156608 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 9571) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 9571) (weight := fun _ => 1) (xs := [592, 720, 895, 1023]) check rows elimOK (by decide) (by decide) cover9571 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h6000 : P.leaf 34 6000 = 156608 :=
  orient32 (v := 9571) (by decide) (by decide +kernel) h9571

theorem cover19215 : P.CoversSplit 24 10 19215 0xaaaaaaaa00000000aa88aa880000000000000000000000000000000000000000888888880000000000000000000000000000000000000000000000000000000088aa88aa000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 516, 522, 523, 528, 565, 572, 915, 1259, 1601]) (by decide +kernel)

theorem c19215_0 : P.sumLeaves 24 19676160 1024 = 3229564 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 19215) (lo := 0) (len := 1024) (W := 3229564) check rows elimOK (by decide) (by decide) cover19215 (by decide)
  decide +kernel

theorem h19215 : P.leaf 34 19215 = 3229564 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 3229564)]) (.cons c19215_0 (.nil)) (by decide) (by decide))

theorem h6001 : P.leaf 34 6001 = 3229564 :=
  orient4 (v := 19215) (by decide) (by decide +kernel) h19215

theorem cover10083 : P.CoversSplit 24 10 10083 0xffff0000000000000000000000000000ffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [474, 515, 523, 524, 565, 572, 915, 1202, 1209, 1258, 1264, 1308]) (by decide +kernel)

theorem c10083_0 : P.sumLeaves 24 10324992 1024 = 2772228 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 10083) (lo := 0) (len := 1024) (W := 2772228) check rows elimOK (by decide) (by decide) cover10083 (by decide)
  decide +kernel

theorem h10083 : P.leaf 34 10083 = 2772228 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 2772228)]) (.cons c10083_0 (.nil)) (by decide) (by decide))

theorem h6002 : P.leaf 34 6002 = 2772228 :=
  orient32 (v := 10083) (by decide) (by decide +kernel) h10083

theorem cover19231 : P.CoversSplit 24 10 19231 0xaaaaaaaa00000000aaaaaaaa00000000a0a0000000000000a0a00000000000008888888800000000000000000000000080800000000000000000000000000000aaaaaaaa00000000aaaa000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [516, 517, 523, 528, 572, 859, 866, 1210, 1259, 1264, 1308, 1601, 1609]) (ps := [(8, [615], [1266])]) (by decide +kernel)

theorem c19231_0 : P.sumLeaves 24 19692544 1024 = 10935070 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 19231) (lo := 0) (len := 1024) (W := 10935070) check rows elimOK (by decide) (by decide) cover19231 (by decide)
  decide +kernel

theorem h19231 : P.leaf 34 19231 = 10935070 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 10935070)]) (.cons c19231_0 (.nil)) (by decide) (by decide))

theorem h6003 : P.leaf 34 6003 = 10935070 :=
  orient4 (v := 19231) (by decide) (by decide +kernel) h19231

def seg : List (ℕ × ℕ) := [(5968, 12), (5969, 24), (5971, 12), (5972, 12), (5973, 24), (5975, 12), (5976, 12), (5977, 24), (5979, 12), (5980, 12), (5981, 24), (5983, 12), (5984, 48), (5985, 48), (5986, 48), (5987, 48), (5988, 48), (5989, 48), (5990, 48), (5991, 48), (5992, 48), (5993, 48), (5994, 48), (5995, 48), (5996, 48), (5997, 48), (5998, 48), (5999, 48), (6000, 48), (6001, 48), (6002, 48), (6003, 48)]

theorem segOK : checkSeg 16 perms 5968 6004 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 5968 6004 1152 5050557888 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 5050557888)
    (SegSum.cons (w := 12) h5968 (SegSum.cons (w := 24) h5969 (SegSum.cons (w := 12) h5971 (SegSum.cons (w := 12) h5972 (SegSum.cons (w := 24) h5973 (SegSum.cons (w := 12) h5975 (SegSum.cons (w := 12) h5976 (SegSum.cons (w := 24) h5977 (SegSum.cons (w := 12) h5979 (SegSum.cons (w := 12) h5980 (SegSum.cons (w := 24) h5981 (SegSum.cons (w := 12) h5983 (SegSum.cons (w := 48) h5984 (SegSum.cons (w := 48) h5985 (SegSum.cons (w := 48) h5986 (SegSum.cons (w := 48) h5987 (SegSum.cons (w := 48) h5988 (SegSum.cons (w := 48) h5989 (SegSum.cons (w := 48) h5990 (SegSum.cons (w := 48) h5991 (SegSum.cons (w := 48) h5992 (SegSum.cons (w := 48) h5993 (SegSum.cons (w := 48) h5994 (SegSum.cons (w := 48) h5995 (SegSum.cons (w := 48) h5996 (SegSum.cons (w := 48) h5997 (SegSum.cons (w := 48) h5998 (SegSum.cons (w := 48) h5999 (SegSum.cons (w := 48) h6000 (SegSum.cons (w := 48) h6001 (SegSum.cons (w := 48) h6002 (SegSum.cons (w := 48) h6003 (show SegSum (P.leaf 34) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S4N1.C0.S31
