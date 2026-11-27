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

namespace RACert.S4N1.C0.S83

open RACert RACert.Problem

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

theorem c23852_0 : P.sumLeaves 24 24424448 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23852) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover23852 (by decide)
  decide +kernel

theorem h23852 : P.leaf 34 23852 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c23852_0 (.nil)) (by decide) (by decide))

theorem cover23853 : P.CoversSplit 24 10 23853 0x8800000088008000000000000000000088000000000040000000000000000000880000008800800000000000000000008800000000004000000000000000000088000000880080000000000000000000880000000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 515, 517, 522, 529, 572, 858, 865, 916, 1210, 1601]) (by decide +kernel)

theorem c23853_0 : P.sumLeaves 24 24425472 1024 = 2127788 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23853) (lo := 0) (len := 1024) (W := 2127788) check rows elimOK (by decide) (by decide) cover23853 (by decide)
  decide +kernel

theorem h23853 : P.leaf 34 23853 = 2127788 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 2127788)]) (.cons c23853_0 (.nil)) (by decide) (by decide))

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

theorem cover23862 : P.CoversSplit 24 10 23862 0xfffffffffafaa0a0fffffffffafaa0a0fffffffffafaa0a0ffff000000000000ccc0ccc088808080cc00cc0088008000ccc0ccc088808080cc00000000000000fffffffffafaa0a0ffff0000fafa0000fffffffffafaa0a0ffff0000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 517, 529, 572, 858, 865, 1202, 1210, 1251, 1259, 1264, 1308, 1601, 1609]) (ps := [(14, [965], [1609])]) (by decide +kernel)

theorem c23862_0 : P.sumLeaves 24 24434688 465 = 6837358 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23862) (lo := 0) (len := 465) (W := 6837358) check rows elimOK (by decide) (by decide) cover23862 (by decide)
  decide +kernel

theorem c23862_1 : P.sumLeaves 24 24435153 354 = 11132262 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23862) (lo := 465) (len := 354) (W := 11132262) check rows elimOK (by decide) (by decide) cover23862 (by decide)
  decide +kernel

theorem c23862_2 : P.sumLeaves 24 24435507 128 = 17358616 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23862) (lo := 819) (len := 128) (W := 17358616) check rows elimOK (by decide) (by decide) cover23862 (by decide)
  decide +kernel

theorem c23862_3 : P.sumLeaves 24 24435635 77 = 29759418 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23862) (lo := 947) (len := 77) (W := 29759418) check rows elimOK (by decide) (by decide) cover23862 (by decide)
  decide +kernel

theorem h23862 : P.leaf 34 23862 = 65087654 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(465, 6837358), (354, 11132262), (128, 17358616), (77, 29759418)]) (.cons c23862_0 (.cons c23862_1 (.cons c23862_2 (.cons c23862_3 (.nil))))) (by decide) (by decide))

theorem cover23863 : P.CoversSplit 24 10 23863 0xfffffffffafaa0a0fffffffffafaa0a0fffffffffafaa0a0ffff000000000000cccccccc88888080cc00cc0088008000cccccccc88888080cc00000000000000fffffffffafaa0a0ffff0000fafa0000fffffffffafaa0a0ffff0000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [517, 572, 858, 865, 1202, 1210, 1251, 1259, 1264, 1308, 1601, 1609]) (ps := [(14, [965], [1609])]) (by decide +kernel)

theorem c23863_0 : P.sumLeaves 24 24435712 465 = 17180534 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23863) (lo := 0) (len := 465) (W := 17180534) check rows elimOK (by decide) (by decide) cover23863 (by decide)
  decide +kernel

theorem c23863_1 : P.sumLeaves 24 24436177 290 = 24436441 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23863) (lo := 465) (len := 290) (W := 24436441) check rows elimOK (by decide) (by decide) cover23863 (by decide)
  decide +kernel

theorem c23863_2 : P.sumLeaves 24 24436467 182 = 41174611 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23863) (lo := 755) (len := 182) (W := 41174611) check rows elimOK (by decide) (by decide) cover23863 (by decide)
  decide +kernel

theorem c23863_3 : P.sumLeaves 24 24436649 87 = 66336280 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23863) (lo := 937) (len := 87) (W := 66336280) check rows elimOK (by decide) (by decide) cover23863 (by decide)
  decide +kernel

theorem h23863 : P.leaf 34 23863 = 149127866 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(465, 17180534), (290, 24436441), (182, 41174611), (87, 66336280)]) (.cons c23863_0 (.cons c23863_1 (.cons c23863_2 (.cons c23863_3 (.nil))))) (by decide) (by decide))

theorem cover23868 : P.CoversSplit 24 10 23868 0xcc00cc00c8008000cc00cc00c8008000cc00cc00c8008000cc00000000000000cc00cc0088008000cc00cc0088008000cc00cc0088008000cc00000000000000cc00cc00c8008000cc000000c8000000cc00cc00c8008000cc000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 508, 529, 858, 916, 1210, 1251, 1264, 1308, 1601]) (by decide +kernel)

theorem c23868_0 : P.sumLeaves 24 24440832 954 = 11694226 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23868) (lo := 0) (len := 954) (W := 11694226) check rows elimOK (by decide) (by decide) cover23868 (by decide)
  decide +kernel

theorem c23868_1 : P.sumLeaves 24 24441786 70 = 10502888 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23868) (lo := 954) (len := 70) (W := 10502888) check rows elimOK (by decide) (by decide) cover23868 (by decide)
  decide +kernel

theorem h23868 : P.leaf 34 23868 = 22197114 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(954, 11694226), (70, 10502888)]) (.cons c23868_0 (.cons c23868_1 (.nil))) (by decide) (by decide))

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

theorem cover23870 : P.CoversSplit 24 10 23870 0xfffffffffafaa0a0fffffffffafaa0a0fffffffffafaa0a0ffff000000000000ccc0ccc088808080cc00cc0088008000ccc0ccc088808080cc00000000000000fffffffffafaa0a0ffff0000fafa0000fffffffffafaa0a0ffff0000000000000000000000000000880000008800000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 529, 572, 858, 865, 1202, 1210, 1251, 1259, 1264, 1308, 1601, 1609]) (by decide +kernel)

theorem c23870_0 : P.sumLeaves 24 24442880 128 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23870) (lo := 0) (len := 128) (W := 0) check rows elimOK (by decide) (by decide) cover23870 (by decide)
  decide +kernel

theorem contract23870_1 : P.leaf 30 381922 = 4640 := by
  exact leaf_contract_factors (k := 30) (b := 14) (H := 381922) (ss := [(26, 1, 529), (4, 1, 578), (10, 1, 865), (29, 1, 865), (18, 1, 867), (11, 1, 921), (30, 1, 1264), (27, 1, 1601), (8, 0, 1609), (5, 3, 524), (3, 1, 580), (14, 0, 1609), (9, 1, 629), (21, 1, 629), (20, 1, 678), (16, 1, 1265)]) (ids := [0, 4, 5, 10, 11, 13, 15, 17, 21, 22, 23, 26, 29, 20]) (cs := [2, 1, 1, 1, 3, 4, 0, 1, 1, 1, 5, 6, 0, 7, 1, 8, 1, 9, 1, 1, 15, 10, 11, 12, 1, 1, 13, 1, 1, 14]) (bs := [13, 1]) (W := 4640) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c23870_1 : P.sumLeaves 24 24443008 64 = 4640 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 381922) rows (by decide) (by decide)).symm.trans contract23870_1

theorem c23870_2 : P.sumLeaves 24 24443072 273 = 13308372 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23870) (lo := 192) (len := 273) (W := 13308372) check rows elimOK (by decide) (by decide) cover23870 (by decide)
  decide +kernel

theorem c23870_3 : P.sumLeaves 24 24443345 354 = 21514396 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23870) (lo := 465) (len := 354) (W := 21514396) check rows elimOK (by decide) (by decide) cover23870 (by decide)
  decide +kernel

theorem c23870_4 : P.sumLeaves 24 24443699 128 = 34331686 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23870) (lo := 819) (len := 128) (W := 34331686) check rows elimOK (by decide) (by decide) cover23870 (by decide)
  decide +kernel

theorem c23870_5 : P.sumLeaves 24 24443827 77 = 57067554 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23870) (lo := 947) (len := 77) (W := 57067554) check rows elimOK (by decide) (by decide) cover23870 (by decide)
  decide +kernel

theorem h23870 : P.leaf 34 23870 = 126226648 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(128, 0), (64, 4640), (273, 13308372), (354, 21514396), (128, 34331686), (77, 57067554)]) (.cons c23870_0 (.cons c23870_1 (.cons c23870_2 (.cons c23870_3 (.cons c23870_4 (.cons c23870_5 (.nil))))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(23847, 48), (23852, 48), (23853, 48), (23854, 48), (23855, 48), (23862, 12), (23863, 24), (23868, 48), (23869, 48), (23870, 48)]

theorem segOK : checkSeg 16 perms 23847 23871 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 23847 23871 420 15308237304 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 15308237304)
    (SegSum.cons (w := 48) h23847 (SegSum.cons (w := 48) h23852 (SegSum.cons (w := 48) h23853 (SegSum.cons (w := 48) h23854 (SegSum.cons (w := 48) h23855 (SegSum.cons (w := 12) h23862 (SegSum.cons (w := 24) h23863 (SegSum.cons (w := 48) h23868 (SegSum.cons (w := 48) h23869 (SegSum.cons (w := 48) h23870 (show SegSum (P.leaf 34) [] 0 from rfl))))))))))) (by decide)

end RACert.S4N1.C0.S83
