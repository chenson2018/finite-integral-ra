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

namespace RACert.S4N1.C0.S37

open RACert RACert.Problem

theorem cover6628 : P.CoversSplit 24 10 6628 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem h6628 : P.leaf 34 6628 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 6628) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 6628) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover6628 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover6629 : P.CoversSplit 24 10 6629 0x8000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 466, 473, 515, 522, 858, 865, 879, 916, 1209, 1258]) (by decide +kernel)

theorem h6629 : P.leaf 34 6629 = 143184 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 6629) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 6629) (weight := fun _ => 1) (xs := [511, 720, 1023]) check rows elimOK (by decide) (by decide) cover6629 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover6630 : P.CoversSplit 24 10 6630 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 465, 466, 515, 522, 858, 859, 865, 879, 1209, 1258]) (by decide +kernel)

theorem h6630 : P.leaf 34 6630 = 269344 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 6630) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 6630) (weight := fun _ => 1) (xs := [720, 895, 1023]) check rows elimOK (by decide) (by decide) cover6630 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover6631 : P.CoversSplit 24 10 6631 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 515, 522, 858, 859, 865, 866, 1209, 1217, 1258, 1266]) (by decide +kernel)

theorem h6631 : P.leaf 34 6631 = 1556670 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 6631) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 6631) (weight := fun _ => 1) (xs := [208, 511, 592, 720, 895, 1023]) check rows elimOK (by decide) (by decide) cover6631 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover6636 : P.CoversSplit 24 10 6636 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem h6636 : P.leaf 34 6636 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 6636) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 6636) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover6636 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover6637 : P.CoversSplit 24 10 6637 0x8000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 466, 473, 515, 522, 858, 865, 879, 916, 1209, 1258]) (by decide +kernel)

theorem h6637 : P.leaf 34 6637 = 517668 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 6637) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 6637) (weight := fun _ => 1) (xs := [511, 720, 1023]) check rows elimOK (by decide) (by decide) cover6637 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover6639 : P.CoversSplit 24 10 6639 0x8000000000000000000000000000000080000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 515, 522, 858, 859, 865, 866, 1209, 1217, 1258, 1266]) (by decide +kernel)

theorem h6639 : P.leaf 34 6639 = 4277968 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 6639) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 6639) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 6639) (weight := rowWeight keep1 twice1) (xs := [208, 511, 592, 720, 895, 1023]) check rows elimOK (by decide) (by decide) cover6639 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover11489 : P.CoversSplit 24 10 11489 0x8000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000002000000001000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [417, 466, 473, 515, 522, 573, 858, 865, 1209, 1210, 1217, 1258, 1266]) (by decide +kernel)

theorem h11489 : P.leaf 34 11489 = 41428 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 11489) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 11489) (weight := fun _ => 1) (xs := [144, 181, 511, 895, 1023]) check rows elimOK (by decide) (by decide) cover11489 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h6640 : P.leaf 34 6640 = 41428 :=
  orient32 (v := 11489) (by decide) (by decide +kernel) h11489

theorem cover17807 : P.CoversSplit 24 10 17807 0xa0000000000000000000000000000000a00000000000000000000000000000008000000000000000200000000000000080000000000000002000000000000000a0000000000000000000000000000000a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 516, 517, 522, 528, 858, 865, 1259, 1601]) (by decide +kernel)

theorem h17807 : P.leaf 34 17807 = 687700 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 17807) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 17807) (weight := fun _ => 1) (xs := [381, 383, 509, 511, 573, 639, 701, 767, 893, 895, 1021, 1023]) check rows elimOK (by decide) (by decide) cover17807 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h6641 : P.leaf 34 6641 = 687700 :=
  orient4 (v := 17807) (by decide) (by decide +kernel) h17807

theorem cover6643 : P.CoversSplit 24 10 6643 0xffff0000afaa00000000000000000000ffff0000afaa00000000000000000000ccfc0000888800000000000000000000ccfc0000888800000000000000000000ffff0000afaa00000000000000000000ffff0000aaaa00000000000000000000ccfc0000888800000000000000000000cccc0000888800000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [858, 859, 865, 866, 867, 1202, 1209, 1217, 1258, 1259, 1601, 1609]) (by decide +kernel)

noncomputable def f6643 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (6802432 + i)

theorem c6643_0 : rowSum f6643 0 1024 = 15939899 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 6643) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover6643 (by decide)
  decide +kernel

theorem sum6643 : rowSum f6643 0 1024 = 15939899 :=
  c6643_0

theorem h6643 : P.leaf 34 6643 = 15939899 :=
  leaf_weighted (k := 24) (d := 10) (H := 6643) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 6643) (by decide) (by decide +kernel)) sum6643

theorem cover17838 : P.CoversSplit 24 10 17838 0xa0000000a00000000000000000000000a00000000000000000000000000000008000000080000000800000008000000080000000000000008000000000000000a0000000a00000000000000000000000a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 515, 517, 522, 858, 860, 865, 872, 1259, 1601]) (by decide +kernel)

theorem h17838 : P.leaf 34 17838 = 303976 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 17838) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 17838) (weight := fun _ => 1) (xs := [381, 383, 477, 479, 509, 511, 575, 639, 671, 703, 735, 767, 893, 895, 989, 991, 1021, 1023]) check rows elimOK (by decide) (by decide) cover17838 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h6644 : P.leaf 34 6644 = 303976 :=
  orient4 (v := 17838) (by decide) (by decide +kernel) h17838

theorem cover17839 : P.CoversSplit 24 10 17839 0xa0000000a00000000000000000000000a00000000000050000000000000000008000000080000000200000002000000080000000000004002000000000000100a0000000a00000000000000000000000a00000000000050000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 517, 522, 858, 860, 865, 1259, 1601]) (by decide +kernel)

theorem h17839 : P.leaf 34 17839 = 2522020 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 17839) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 17839) (weight := fun _ => 1) (xs := [328, 330, 381, 383, 477, 479, 509, 511, 520, 573, 586, 639, 669, 701, 735, 767, 840, 842, 893, 895, 989, 991, 1021, 1023]) check rows elimOK (by decide) (by decide) cover17839 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h6645 : P.leaf 34 6645 = 2522020 :=
  orient4 (v := 17839) (by decide) (by decide +kernel) h17839

theorem cover6646 : P.CoversSplit 24 10 6646 0xf0f00000a0a500000000000000000000f0f00000000000000000000000000000c0f00000808000000000000000000000c0f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 858, 859, 865, 866, 879, 1202, 1258, 1259, 1601]) (by decide +kernel)

theorem c6646_0 : P.sumLeaves 24 6805504 1024 = 3032736 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6646) (lo := 0) (len := 1024) (W := 3032736) check rows elimOK (by decide) (by decide) cover6646 (by decide)
  decide +kernel

theorem h6646 : P.leaf 34 6646 = 3032736 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 3032736)]) (.cons c6646_0 (.nil)) (by decide) (by decide))

theorem cover17855 : P.CoversSplit 24 10 17855 0xff00fa00fa000000ff00fa00fa000000f500f00000000000f500000000000000cc00c80088000000ff00fa00aa000000c400c00000000000f500000000000000ff00fa00fa000000ff00fa00fa000000f500f00000000000f500000000000000cc00c80088000000ff00fa00aa00000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [517, 858, 860, 865, 872, 1202, 1210, 1217, 1251, 1308, 1601]) (ps := [(14, [958], [1217])]) (by decide +kernel)

theorem c17855_0 : P.sumLeaves 24 18283520 669 = 14838393 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 17855) (lo := 0) (len := 669) (W := 14838393) check rows elimOK (by decide) (by decide) cover17855 (by decide)
  decide +kernel

theorem c17855_1 : P.sumLeaves 24 18284189 355 = 36592832 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 17855) (lo := 669) (len := 355) (W := 36592832) check rows elimOK (by decide) (by decide) cover17855 (by decide)
  decide +kernel

theorem h17855 : P.leaf 34 17855 = 51431225 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(669, 14838393), (355, 36592832)]) (.cons c17855_0 (.cons c17855_1 (.nil))) (by decide) (by decide))

theorem h6647 : P.leaf 34 6647 = 51431225 :=
  orient4 (v := 17855) (by decide) (by decide +kernel) h17855

theorem cover6652 : P.CoversSplit 24 10 6652 0xf0000000a000aa00000000000000000000000000000000000000000000000000c000000080088808c0c00000808888880000000000000000000000000000000000000000000000000000000000000000f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 858, 859, 865, 879, 916, 1202, 1259, 1601]) (by decide +kernel)

theorem h6652 : P.leaf 34 6652 = 1237453 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 6652) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 6652) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 6652) (weight := rowWeight keep1 twice1) (xs := [380, 381, 382, 383, 643, 647, 651, 655, 659, 663, 671, 694, 695, 702, 703, 707, 715, 719, 723, 735, 766, 767, 969, 971, 973, 975, 989, 991, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover6652 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover17903 : P.CoversSplit 24 10 17903 0xf0005500f00000000000000000000000f0000000000000000000000000000000c0004400800000003000110020000000c0000000400000003000000010000000f0005500f00000000000000000000000f00055000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 522, 858, 860, 865, 1202, 1210, 1259, 1601]) (by decide +kernel)

theorem c17903_0 : P.sumLeaves 24 18332672 1024 = 8912021 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 17903) (lo := 0) (len := 1024) (W := 8912021) check rows elimOK (by decide) (by decide) cover17903 (by decide)
  decide +kernel

theorem h17903 : P.leaf 34 17903 = 8912021 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 8912021)]) (.cons c17903_0 (.nil)) (by decide) (by decide))

theorem h6653 : P.leaf 34 6653 = 8912021 :=
  orient4 (v := 17903) (by decide) (by decide +kernel) h17903

theorem cover6655 : P.CoversSplit 24 10 6655 0xffffffffafaaaaaaffffffffafaaaaaaffffffffafaaaaaaffffffffafaaaaaaccfcccfc88888888cccccccc88888888ccfcccfc88888888cccccccc88888888ffffffffafaaaaaaffffffffafaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaccfcccfc88888888cccccccc88888888cccccccc88888888cccccccc88888888 :=
  coversSplit check rows (by decide) (by decide) (xs := [858, 865, 1202, 1209, 1217, 1258, 1259, 1601, 1609]) (by decide +kernel)

noncomputable def f6655 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (6814720 + i)

theorem c6655_0 : rowSum f6655 0 291 = 51933378 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 6655) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover6655 (by decide)
  decide +kernel

theorem c6655_1 : rowSum f6655 291 181 = 71069718 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 6655) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover6655 (by decide)
  decide +kernel

theorem c6655_2 : rowSum f6655 472 474 = 157954578 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 6655) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover6655 (by decide)
  decide +kernel

theorem c6655_3 : rowSum f6655 946 78 = 85330614 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 6655) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover6655 (by decide)
  decide +kernel

theorem sum6655 : rowSum f6655 0 1024 = 366288288 :=
  rowSum_append (F := f6655) (lo := 0) (n := 291) (m := 733) (A := 51933378) (B := 314354910) c6655_0 (rowSum_append (F := f6655) (lo := 291) (n := 181) (m := 552) (A := 71069718) (B := 243285192) c6655_1 (rowSum_append (F := f6655) (lo := 472) (n := 474) (m := 78) (A := 157954578) (B := 85330614) c6655_2 (c6655_3)))

theorem h6655 : P.leaf 34 6655 = 366288288 :=
  leaf_weighted (k := 24) (d := 10) (H := 6655) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 6655) (by decide) (by decide +kernel)) sum6655

theorem cover6868 : P.CoversSplit 24 10 6868 0xffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 475, 479, 573, 859, 1202, 1210, 1259, 1264]) (by decide +kernel)

theorem h6868 : P.leaf 34 6868 = 95136 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 6868) (keep := keep5) (twice := twice5) rows (by decide) (by decide) bal5 (invRow5 (H := 6868) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 6868) (weight := rowWeight keep5 twice5) (xs := [1008, 1009, 1010, 1011, 1012, 1013, 1014, 1015, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover6868 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover6869 : P.CoversSplit 24 10 6869 0xffff0000000000000000000000000000a0a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 475, 479, 516, 573, 859, 1202, 1209, 1210, 1259, 1264]) (by decide +kernel)

theorem h6869 : P.leaf 34 6869 = 1253744 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 6869) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 6869) (weight := fun _ => 1) (xs := [885, 887, 893, 895, 1008, 1009, 1010, 1011, 1012, 1013, 1014, 1015, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover6869 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover6871 : P.CoversSplit 24 10 6871 0xffff0000000000000000000000000000a0a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [475, 479, 516, 573, 859, 916, 1202, 1209, 1210, 1251, 1259, 1264]) (by decide +kernel)

theorem h6871 : P.leaf 34 6871 = 3198704 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 6871) (keep := keep5) (twice := twice5) rows (by decide) (by decide) bal5 (invRow5 (H := 6871) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 6871) (weight := rowWeight keep5 twice5) (xs := [383, 506, 507, 510, 511, 885, 887, 893, 895, 1008, 1009, 1010, 1011, 1012, 1013, 1014, 1015, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover6871 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover6876 : P.CoversSplit 24 10 6876 0xffff0000000000000000000000000000a0a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 516, 536, 573, 859, 916, 1202, 1210, 1251, 1259, 1264]) (by decide +kernel)

theorem h6876 : P.leaf 34 6876 = 1391496 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 6876) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 6876) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 6876) (weight := rowWeight keep1 twice1) (xs := [383, 506, 507, 510, 511, 885, 887, 893, 895, 1008, 1009, 1010, 1011, 1012, 1013, 1014, 1015, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover6876 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover6877 : P.CoversSplit 24 10 6877 0xffff0000000000000000000000000000a0a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 516, 536, 573, 859, 916, 1202, 1209, 1210, 1251, 1259, 1264]) (by decide +kernel)

theorem h6877 : P.leaf 34 6877 = 3259280 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 6877) (keep := keep2) (twice := twice2) rows (by decide) (by decide) bal2 (invRow2 (H := 6877) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 6877) (weight := rowWeight keep2 twice2) (xs := [383, 506, 507, 510, 511, 885, 887, 893, 895, 1008, 1009, 1010, 1011, 1012, 1013, 1014, 1015, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover6877 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover6879 : P.CoversSplit 24 10 6879 0xffff0000000000000000000000000000a0a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [516, 536, 573, 859, 916, 1202, 1209, 1210, 1251, 1259, 1264]) (by decide +kernel)

theorem h6879 : P.leaf 34 6879 = 5371140 := by
  apply leaf_weighted (k := 24) (d := 10) (H := 6879) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 6879) (by decide) (by decide +kernel))
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 6879) (weight := rowWeight keep1 twice1) (xs := [383, 506, 507, 510, 511, 885, 887, 893, 895, 1008, 1009, 1010, 1011, 1012, 1013, 1014, 1015, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023]) check rows elimOK (by decide) (by decide) cover6879 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover6884 : P.CoversSplit 24 10 6884 0x8888000000000000000000000000000080800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 475, 515, 522, 524, 573, 859, 1202, 1210, 1251, 1259]) (by decide +kernel)

theorem h6884 : P.leaf 34 6884 = 148416 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 6884) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 6884) (weight := fun _ => 1) (xs := [887, 895, 1011, 1015, 1019, 1023]) check rows elimOK (by decide) (by decide) cover6884 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover6885 : P.CoversSplit 24 10 6885 0xcccc0000000000000000000000000000cccc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 475, 515, 522, 524, 879, 1202, 1209, 1210, 1251, 1259]) (by decide +kernel)

theorem h6885 : P.leaf 34 6885 = 1418528 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 6885) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 6885) (weight := fun _ => 1) (xs := [882, 883, 886, 887, 890, 891, 894, 895, 1010, 1011, 1014, 1015, 1018, 1019, 1022, 1023]) check rows elimOK (by decide) (by decide) cover6885 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover6886 : P.CoversSplit 24 10 6886 0xaaaa0000000000000000000000000000a0a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000088000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 475, 515, 522, 524, 566, 573, 859, 916, 1210, 1251, 1259, 1264, 1308]) (by decide +kernel)

theorem h6886 : P.leaf 34 6886 = 817000 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 6886) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 6886) (weight := fun _ => 1) (xs := [507, 511, 885, 887, 893, 895, 1009, 1011, 1013, 1015, 1017, 1019, 1021, 1023]) check rows elimOK (by decide) (by decide) cover6886 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover6887 : P.CoversSplit 24 10 6887 0xffff0000000000000000000000000000ffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [475, 515, 522, 524, 566, 573, 916, 1202, 1209, 1210, 1251, 1259, 1264, 1308]) (by decide +kernel)

theorem c6887_0 : P.sumLeaves 24 7052288 1024 = 4879224 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6887) (lo := 0) (len := 1024) (W := 4879224) check rows elimOK (by decide) (by decide) cover6887 (by decide)
  decide +kernel

theorem h6887 : P.leaf 34 6887 = 4879224 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 4879224)]) (.cons c6887_0 (.nil)) (by decide) (by decide))

theorem cover6888 : P.CoversSplit 24 10 6888 0x8888000000000000000000000000000080800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 515, 522, 523, 573, 859, 879, 916, 1202, 1210, 1251, 1259, 1264, 1308]) (ps := [(14, [923], [487])]) (by decide +kernel)

theorem h6888 : P.leaf 34 6888 = 64336 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 6888) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 6888) (weight := fun _ => 1) (xs := [887, 895, 1011, 1015, 1019, 1023]) check rows elimOK (by decide) (by decide) cover6888 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover6889 : P.CoversSplit 24 10 6889 0xcccc0000000000000000000000000000cccc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 515, 522, 523, 573, 879, 916, 1202, 1209, 1210, 1251, 1259, 1308]) (ps := [(14, [923], [487])]) (by decide +kernel)

theorem h6889 : P.leaf 34 6889 = 565576 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 6889) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 6889) (weight := fun _ => 1) (xs := [882, 883, 886, 887, 890, 891, 894, 895, 1010, 1011, 1014, 1015, 1018, 1019, 1022, 1023]) check rows elimOK (by decide) (by decide) cover6889 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover6890 : P.CoversSplit 24 10 6890 0xaaaa0000000000000000000000000000a0a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000088000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 515, 522, 523, 573, 859, 879, 916, 1210, 1251, 1259, 1264, 1308]) (by decide +kernel)

theorem h6890 : P.leaf 34 6890 = 1433408 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 6890) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 6890) (weight := fun _ => 1) (xs := [507, 511, 885, 887, 893, 895, 1009, 1011, 1013, 1015, 1017, 1019, 1021, 1023]) check rows elimOK (by decide) (by decide) cover6890 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover6891 : P.CoversSplit 24 10 6891 0xffff0000000000000000000000000000ffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 522, 523, 573, 879, 916, 1202, 1209, 1210, 1251, 1259, 1264, 1308]) (by decide +kernel)

theorem c6891_0 : P.sumLeaves 24 7056384 1024 = 7111682 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 6891) (lo := 0) (len := 1024) (W := 7111682) check rows elimOK (by decide) (by decide) cover6891 (by decide)
  decide +kernel

theorem h6891 : P.leaf 34 6891 = 7111682 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 7111682)]) (.cons c6891_0 (.nil)) (by decide) (by decide))

theorem cover6892 : P.CoversSplit 24 10 6892 0x8888000000000000000000000000000080800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000088000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 515, 522, 573, 859, 879, 916, 1202, 1210, 1251, 1259, 1264, 1308]) (by decide +kernel)

theorem h6892 : P.leaf 34 6892 = 591656 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 6892) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 6892) (weight := fun _ => 1) (xs := [507, 511, 887, 895, 1011, 1015, 1019, 1023]) check rows elimOK (by decide) (by decide) cover6892 (by decide) (by decide) (by decide +kernel)
  decide +kernel

def seg : List (ℕ × ℕ) := [(6628, 48), (6629, 48), (6630, 48), (6631, 48), (6636, 24), (6637, 48), (6639, 24), (6640, 24), (6641, 48), (6643, 24), (6644, 48), (6645, 48), (6646, 48), (6647, 48), (6652, 24), (6653, 48), (6655, 24), (6868, 24), (6869, 48), (6871, 24), (6876, 12), (6877, 24), (6879, 12), (6884, 48), (6885, 48), (6886, 48), (6887, 48), (6888, 48), (6889, 48), (6890, 48), (6891, 48), (6892, 48)]

theorem segOK : checkSeg 16 perms 6628 6893 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 6628 6893 1248 13752952848 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 13752952848)
    (SegSum.cons (w := 48) h6628 (SegSum.cons (w := 48) h6629 (SegSum.cons (w := 48) h6630 (SegSum.cons (w := 48) h6631 (SegSum.cons (w := 24) h6636 (SegSum.cons (w := 48) h6637 (SegSum.cons (w := 24) h6639 (SegSum.cons (w := 24) h6640 (SegSum.cons (w := 48) h6641 (SegSum.cons (w := 24) h6643 (SegSum.cons (w := 48) h6644 (SegSum.cons (w := 48) h6645 (SegSum.cons (w := 48) h6646 (SegSum.cons (w := 48) h6647 (SegSum.cons (w := 24) h6652 (SegSum.cons (w := 48) h6653 (SegSum.cons (w := 24) h6655 (SegSum.cons (w := 24) h6868 (SegSum.cons (w := 48) h6869 (SegSum.cons (w := 24) h6871 (SegSum.cons (w := 12) h6876 (SegSum.cons (w := 24) h6877 (SegSum.cons (w := 12) h6879 (SegSum.cons (w := 48) h6884 (SegSum.cons (w := 48) h6885 (SegSum.cons (w := 48) h6886 (SegSum.cons (w := 48) h6887 (SegSum.cons (w := 48) h6888 (SegSum.cons (w := 48) h6889 (SegSum.cons (w := 48) h6890 (SegSum.cons (w := 48) h6891 (SegSum.cons (w := 48) h6892 (show SegSum (P.leaf 34) [] 0 from rfl))))))))))))))))))))))))))))))))) (by decide)

end RACert.S4N1.C0.S37
