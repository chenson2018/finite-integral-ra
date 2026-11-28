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

namespace RACert.S4N1.C0.S70

open RACert RACert.Problem

theorem cover23790 : P.CoversSplit 24 10 23790 0xfffffffffafa0000fffffffffafa0000ffff00000000fafaffff00000000fac80000000000000000000000000000000000000000000000000000000000000000cc00cc00c80000000000000000000000cc0000000000c80000330000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 515, 522, 573, 858, 865, 916, 1202, 1210, 1259, 1601]) (ps := [(8, [565], [573]), (17, [1259], [1251]), (18, [536], [1210])]) (by decide +kernel)

noncomputable def f23790 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 24 (24360960 + i)

theorem c23790_0 : rowSum f23790 0 1013 = 28052286 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 23790) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover23790 (by decide)
  decide +kernel

theorem c23790_1 : rowSum f23790 1013 11 = 7068312 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 23790) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover23790 (by decide)
  decide +kernel

theorem sum23790 : rowSum f23790 0 1024 = 35120598 :=
  rowSum_append (F := f23790) (lo := 0) (n := 1013) (m := 11) (A := 28052286) (B := 7068312) c23790_0 (c23790_1)

theorem h23790 : P.leaf 34 23790 = 35120598 :=
  leaf_weighted (k := 24) (d := 10) (H := 23790) (keep := keep2) (twice := twice2) rows (by decide) (by decide) (bal2) (invRow2 (H := 23790) (by decide) (by decide +kernel)) sum23790

theorem cover23791 : P.CoversSplit 24 10 23791 0xfffffffffafa0000fffffffffafa0000ffff00000000fafaffff00000000fac80000000000000000000000000000000000000000000000000000000000000000cc00cc00c80000000000000000000000cc0000000000c80000330000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [515, 522, 573, 858, 865, 916, 1202, 1210, 1259, 1601]) (ps := [(8, [565], [573]), (17, [1259], [1251]), (18, [536], [1210])]) (by decide +kernel)

noncomputable def f23791 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 24 (24361984 + i)

theorem c23791_0 : rowSum f23791 0 1013 = 36858799 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 23791) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover23791 (by decide)
  decide +kernel

theorem c23791_1 : rowSum f23791 1013 11 = 9022940 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 23791) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover23791 (by decide)
  decide +kernel

theorem sum23791 : rowSum f23791 0 1024 = 45881739 :=
  rowSum_append (F := f23791) (lo := 0) (n := 1013) (m := 11) (A := 36858799) (B := 9022940) c23791_0 (c23791_1)

theorem h23791 : P.leaf 34 23791 = 45881739 :=
  leaf_weighted (k := 24) (d := 10) (H := 23791) (keep := keep2) (twice := twice2) rows (by decide) (by decide) (bal2) (invRow2 (H := 23791) (by decide) (by decide +kernel)) sum23791

theorem cover44924 : P.CoversSplit 24 10 44924 0xfffffffffafa0000fffffffffafa0000fffffffffafa0000fffffffffafa00000000000000000000000000000000000000000000000000000000000000000000cc00cc00c80000000000000000000000cc00cc008000000000330033002000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 572, 915, 1209, 1258, 1601]) (ps := [(8, [1217], [572, 1272]), (14, [1217], [915, 1272])]) (by decide +kernel)

noncomputable def f44924 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 24 (46002176 + i)

theorem c44924_0 : rowSum f44924 0 947 = 47396995 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 44924) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover44924 (by decide)
  decide +kernel

theorem c44924_1 : rowSum f44924 947 77 = 49158404 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 44924) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover44924 (by decide)
  decide +kernel

theorem sum44924 : rowSum f44924 0 1024 = 96555399 :=
  rowSum_append (F := f44924) (lo := 0) (n := 947) (m := 77) (A := 47396995) (B := 49158404) c44924_0 (c44924_1)

theorem h44924 : P.leaf 34 44924 = 96555399 :=
  leaf_weighted (k := 24) (d := 10) (H := 44924) (keep := keep2) (twice := twice2) rows (by decide) (by decide) (bal2) (invRow2 (H := 44924) (by decide) (by decide +kernel)) sum44924

theorem h23806 : P.leaf 34 23806 = 96555399 :=
  orient5 (v := 44924) (by decide) (by decide +kernel) h44924

theorem cover44925 : P.CoversSplit 24 10 44925 0xfffffffffafa0000fffffffffafa0000fffffffffafa0000fffffffffafa00000000000000000000000000000000000000000000000000000000000000000000cc00cc00c80000000000000000000000cc00cc008000000000330033002000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 572, 915, 1202, 1209, 1258, 1601]) (ps := [(8, [1217], [572, 1272]), (14, [1217], [915, 1272])]) (by decide +kernel)

noncomputable def f44925 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 24 (46003200 + i)

theorem c44925_0 : rowSum f44925 0 947 = 56723111 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 44925) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover44925 (by decide)
  decide +kernel

theorem c44925_1 : rowSum f44925 947 77 = 58450956 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 44925) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover44925 (by decide)
  decide +kernel

theorem sum44925 : rowSum f44925 0 1024 = 115174067 :=
  rowSum_append (F := f44925) (lo := 0) (n := 947) (m := 77) (A := 56723111) (B := 58450956) c44925_0 (c44925_1)

theorem h44925 : P.leaf 34 44925 = 115174067 :=
  leaf_weighted (k := 24) (d := 10) (H := 44925) (keep := keep2) (twice := twice2) rows (by decide) (by decide) (bal2) (invRow2 (H := 44925) (by decide) (by decide +kernel)) sum44925

theorem h23807 : P.leaf 34 23807 = 115174067 :=
  orient5 (v := 44925) (by decide) (by decide +kernel) h44925

theorem cover23844 : P.CoversSplit 24 10 23844 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem h23844 : P.leaf 34 23844 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 23844) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 23844) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover23844 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover25901 : P.CoversSplit 24 10 25901 0x8000000080000000000000000000000080000000000004000000000000000000800000008000000000000000000000008000000000000400000000000000000080000000800000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 515, 517, 522, 529, 572, 858, 860, 865, 872, 1202]) (by decide +kernel)

theorem h25901 : P.leaf 34 25901 = 497537 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 25901) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 25901) (weight := fun _ => 1) (xs := [383, 479, 511, 586, 639, 735, 767, 842, 895, 991, 1023]) check rows elimOK (by decide) (by decide) cover25901 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h23845 : P.leaf 34 23845 = 497537 :=
  orient5 (v := 25901) (by decide) (by decide +kernel) h25901

theorem cover25916 : P.CoversSplit 24 10 25916 0xf0000000f00000000000000000000000f0000000000000000000000000000000f0000000f00000000000000000000000f0000000000000000000000000000000f0000000f00000000000000000000000f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 466, 472, 529, 858, 860, 865, 915, 1202, 1308, 1601]) (by decide +kernel)

noncomputable def f25916 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (26537984 + i)

theorem c25916_0 : rowSum f25916 0 1024 = 2923776 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 25916) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover25916 (by decide)
  decide +kernel

theorem sum25916 : rowSum f25916 0 1024 = 2923776 :=
  c25916_0

theorem h25916 : P.leaf 34 25916 = 2923776 :=
  leaf_weighted (k := 24) (d := 10) (H := 25916) (keep := keep1) (twice := twice1) rows (by decide) (by decide) (bal1) (invRow1 (H := 25916) (by decide) (by decide +kernel)) sum25916

theorem h23846 : P.leaf 34 23846 = 2923776 :=
  orient5 (v := 25916) (by decide) (by decide +kernel) h25916

theorem cover23847 : P.CoversSplit 24 10 23847 0x8888000088880000000000000000000088880000000000000000000000000000888800008888000000000000000000008888000000000000000000000000000088880000888800000000000000000000888800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [466, 515, 517, 522, 572, 858, 1202, 1210, 1259, 1601]) (by decide +kernel)

theorem c23847_0 : P.sumLeaves 24 24419328 1024 = 10790448 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23847) (lo := 0) (len := 1024) (W := 10790448) check rows elimOK (by decide) (by decide) cover23847 (by decide)
  decide +kernel

theorem h23847 : P.leaf 34 23847 = 10790448 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 10790448)]) (.cons c23847_0 (.nil)) (by decide) (by decide))

theorem cover23852 : P.CoversSplit 24 10 23852 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [508]) (by decide +kernel)

theorem h23852 : P.leaf 34 23852 = 0 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 23852) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 23852) (weight := fun _ => 1) (xs := []) check rows elimOK (by decide) (by decide) cover23852 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem cover25965 : P.CoversSplit 24 10 25965 0xc0000000c00088000000000000000000c0000000000000000000000000000000c0000000c00088000000000000000000c0000000000000000000000000000000c0000000c00080000000000000000000c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 515, 522, 572, 858, 865, 872, 1210]) (by decide +kernel)

theorem h25965 : P.leaf 34 25965 = 2127788 := by
  apply leaf_of_rowSum (k := 24) (d := 10) (H := 25965) rows (by decide) (by decide)
  apply rowSum_sparse (b := 20) (m := 4) (d := 10) (H := 25965) (weight := fun _ => 1) (xs := [382, 383, 463, 478, 479, 510, 511, 638, 639, 715, 719, 734, 735, 766, 767, 894, 895, 971, 975, 990, 991, 1022, 1023]) check rows elimOK (by decide) (by decide) cover25965 (by decide) (by decide) (by decide +kernel)
  decide +kernel

theorem h23853 : P.leaf 34 23853 = 2127788 :=
  orient5 (v := 25965) (by decide) (by decide +kernel) h25965

theorem cover23854 : P.CoversSplit 24 10 23854 0x8888000088880000000000000000000088880000000000000000000000000000888000008880000000000000000000008880000000000000000000000000000088880000888800000000000000000000888800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 515, 517, 522, 529, 572, 858, 865, 1202, 1259, 1601]) (ps := [(3, [508], [522])]) (by decide +kernel)

theorem c23854_0 : P.sumLeaves 24 24426496 1024 = 5038540 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23854) (lo := 0) (len := 1024) (W := 5038540) check rows elimOK (by decide) (by decide) cover23854 (by decide)
  decide +kernel

theorem h23854 : P.leaf 34 23854 = 5038540 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 5038540)]) (.cons c23854_0 (.nil)) (by decide) (by decide))

theorem cover23855 : P.CoversSplit 24 10 23855 0x8888000088880000000000000000000088880000000000000000000000000000888800008888000000000000000000008888000000000000000000000000000088880000888800000000000000000000888800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 517, 522, 572, 858, 1202, 1210, 1259, 1601]) (by decide +kernel)

theorem c23855_0 : P.sumLeaves 24 24427520 1024 = 19810718 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23855) (lo := 0) (len := 1024) (W := 19810718) check rows elimOK (by decide) (by decide) cover23855 (by decide)
  decide +kernel

theorem h23855 : P.leaf 34 23855 = 19810718 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 19810718)]) (.cons c23855_0 (.nil)) (by decide) (by decide))

theorem cover26428 : P.CoversSplit 24 10 26428 0xfca8fca8f8a80000fca8fca8f8a80000fca8fca800000000fca8000000000000fc88fc88f88800000000000000000000fc88fc88000000000000000000000000fca8fca8f8a80000fca80000f8a80000fca8fca800000000fca80000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 466, 472, 473, 529, 872, 1202, 1217, 1251, 1264, 1308, 1601, 1609]) (ps := [(8, [615], [1217, 1272])]) (by decide +kernel)

noncomputable def f26428 (i : ℕ) := rowWeight keep5 twice5 i * P.leaf 24 (27062272 + i)

theorem c26428_0 : rowSum f26428 0 1024 = 65087654 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 26428) (keep := keep5) (twice := twice5) check rows elimOK (by decide) (by decide) cover26428 (by decide)
  decide +kernel

theorem sum26428 : rowSum f26428 0 1024 = 65087654 :=
  c26428_0

theorem h26428 : P.leaf 34 26428 = 65087654 :=
  leaf_weighted (k := 24) (d := 10) (H := 26428) (keep := keep5) (twice := twice5) rows (by decide) (by decide) (bal5) (invRow5 (H := 26428) (by decide) (by decide +kernel)) sum26428

theorem h23862 : P.leaf 34 23862 = 65087654 :=
  orient5 (v := 26428) (by decide) (by decide +kernel) h26428

theorem cover26429 : P.CoversSplit 24 10 26429 0xfffffffffafa0000fffffffffafa0000ffffffff00000000ffff000000000000ffccffccfac800000000000000000000ffccffcc000000000000000000000000fffffffffafa0000ffff0000fafa0000ffffffff00000000ffff0000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 517, 529, 872, 1202, 1217, 1251, 1259, 1264, 1308, 1601, 1609]) (ps := [(8, [615], [1217, 1272])]) (by decide +kernel)

noncomputable def f26429 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 24 (27063296 + i)

theorem c26429_0 : rowSum f26429 0 743 = 37679303 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 26429) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover26429 (by decide)
  decide +kernel

theorem c26429_1 : rowSum f26429 743 281 = 111448563 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 26429) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover26429 (by decide)
  decide +kernel

theorem sum26429 : rowSum f26429 0 1024 = 149127866 :=
  rowSum_append (F := f26429) (lo := 0) (n := 743) (m := 281) (A := 37679303) (B := 111448563) c26429_0 (c26429_1)

theorem h26429 : P.leaf 34 26429 = 149127866 :=
  leaf_weighted (k := 24) (d := 10) (H := 26429) (keep := keep2) (twice := twice2) rows (by decide) (by decide) (bal2) (invRow2 (H := 26429) (by decide) (by decide +kernel)) sum26429

theorem h23863 : P.leaf 34 23863 = 149127866 :=
  orient5 (v := 26429) (by decide) (by decide +kernel) h26429

theorem cover23910 : P.CoversSplit 24 10 23910 0xccccccccc8c888880000000000000000cccc0000000040400000000000000000ccc0ccc0888088800000000000000000ccc00000404040400000000000000000ccccccccc8c888880000000000000000cccc00000000404000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 466, 515, 522, 858, 865, 1202, 1210, 1259, 1601]) (ps := [(18, [879], [1210])]) (by decide +kernel)

theorem c23910_0 : P.sumLeaves 24 24483840 1018 = 17087018 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23910) (lo := 0) (len := 1018) (W := 17087018) check rows elimOK (by decide) (by decide) cover23910 (by decide)
  decide +kernel

theorem c23910_1 : P.sumLeaves 24 24484858 6 = 5110096 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23910) (lo := 1018) (len := 6) (W := 5110096) check rows elimOK (by decide) (by decide) cover23910 (by decide)
  decide +kernel

theorem h23910 : P.leaf 34 23910 = 22197114 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1018, 17087018), (6, 5110096)]) (.cons c23910_0 (.cons c23910_1 (.nil))) (by decide) (by decide))

theorem h23868 : P.leaf 34 23868 = 22197114 :=
  orient4 (v := 23910) (by decide) (by decide +kernel) h23910

theorem cover23869 : P.CoversSplit 24 10 23869 0xcc00cc00c8008000cc00cc00c8008000cc00cc00c8008000cc00000000000000cc00cc0088008000cc00cc0088008000cc00cc0088008000cc00000000000000cc00cc00c8008000cc000000c8000000cc00cc00c8008000cc000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 517, 529, 572, 858, 916, 1202, 1210, 1251, 1264, 1308, 1601]) (by decide +kernel)

theorem c23869_0 : P.sumLeaves 24 24441856 954 = 24762316 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23869) (lo := 0) (len := 954) (W := 24762316) check rows elimOK (by decide) (by decide) cover23869 (by decide)
  decide +kernel

theorem c23869_1 : P.sumLeaves 24 24442810 70 = 17132192 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23869) (lo := 954) (len := 70) (W := 17132192) check rows elimOK (by decide) (by decide) cover23869 (by decide)
  decide +kernel

theorem h23869 : P.leaf 34 23869 = 41894508 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(954, 24762316), (70, 17132192)]) (.cons c23869_0 (.cons c23869_1 (.nil))) (by decide) (by decide))

theorem cover26492 : P.CoversSplit 24 10 26492 0xfcfcfcfcf8f8a8a8fcfcfcfcf8f8a8a8fcfcfcfcf800a800fcfcfcfcf800a800fcccfcccf8c8a8880000000000000000fcccfcccf800a8000000000000000000fcfcfcfcf8f8a8a8fcfc0000f8f80000fcfcfcfc00000000fcfc0000000000000000000000000000000000000000000000c00000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 466, 473, 872, 1202, 1264, 1308, 1601, 1609]) (ps := [(14, [965], [1609])]) (by decide +kernel)

theorem c26492_0 : P.sumLeaves 24 27127808 508 = 22080136 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 26492) (lo := 0) (len := 508) (W := 22080136) check rows elimOK (by decide) (by decide) cover26492 (by decide)
  decide +kernel

theorem c26492_1 : P.sumLeaves 24 27128316 323 = 19515493 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 26492) (lo := 508) (len := 323) (W := 19515493) check rows elimOK (by decide) (by decide) cover26492 (by decide)
  decide +kernel

theorem c26492_2 : P.sumLeaves 24 27128639 172 = 55094027 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 26492) (lo := 831) (len := 172) (W := 55094027) check rows elimOK (by decide) (by decide) cover26492 (by decide)
  decide +kernel

theorem c26492_3 : P.sumLeaves 24 27128811 21 = 29536992 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 26492) (lo := 1003) (len := 21) (W := 29536992) check rows elimOK (by decide) (by decide) cover26492 (by decide)
  decide +kernel

theorem h26492 : P.leaf 34 26492 = 126226648 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(508, 22080136), (323, 19515493), (172, 55094027), (21, 29536992)]) (.cons c26492_0 (.cons c26492_1 (.cons c26492_2 (.cons c26492_3 (.nil))))) (by decide) (by decide))

theorem h23870 : P.leaf 34 23870 = 126226648 :=
  orient5 (v := 26492) (by decide) (by decide +kernel) h26492

def seg : List (ℕ × ℕ) := [(23790, 24), (23791, 24), (23806, 24), (23807, 24), (23844, 12), (23845, 24), (23846, 24), (23847, 48), (23852, 48), (23853, 48), (23854, 48), (23855, 48), (23862, 12), (23863, 24), (23868, 48), (23869, 48), (23870, 48)]

theorem segOK : checkSeg 16 perms 23790 23871 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 23790 23871 576 22415912088 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 22415912088)
    (SegSum.cons (w := 24) h23790 (SegSum.cons (w := 24) h23791 (SegSum.cons (w := 24) h23806 (SegSum.cons (w := 24) h23807 (SegSum.cons (w := 12) h23844 (SegSum.cons (w := 24) h23845 (SegSum.cons (w := 24) h23846 (SegSum.cons (w := 48) h23847 (SegSum.cons (w := 48) h23852 (SegSum.cons (w := 48) h23853 (SegSum.cons (w := 48) h23854 (SegSum.cons (w := 48) h23855 (SegSum.cons (w := 12) h23862 (SegSum.cons (w := 24) h23863 (SegSum.cons (w := 48) h23868 (SegSum.cons (w := 48) h23869 (SegSum.cons (w := 48) h23870 (show SegSum (P.leaf 34) [] 0 from rfl)))))))))))))))))) (by decide)

end RACert.S4N1.C0.S70
