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

namespace RACert.S4N1.C0.S85

open RACert RACert.Problem

theorem cover23972 : P.CoversSplit 24 10 23972 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [466]) (by decide +kernel)

theorem c23972_0 : P.sumLeaves 24 24547328 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23972) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover23972 (by decide)
  decide +kernel

theorem h23972 : P.leaf 34 23972 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c23972_0 (.nil)) (by decide) (by decide))

theorem cover23973 : P.CoversSplit 24 10 23973 0xaaaa0000bab00000aaaa0000bab00000aaaa000000000000aaaa0000000000008888000088800000888800008880000088880000000000008888000000000000aa000000ba0000000000000000000000aa0000000000000000220000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [466, 473, 515, 522, 858, 865, 916, 1202, 1210, 1259, 1601]) (by decide +kernel)

theorem c23973_0 : P.sumLeaves 24 24548352 1024 = 3875868 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23973) (lo := 0) (len := 1024) (W := 3875868) check rows elimOK (by decide) (by decide) cover23973 (by decide)
  decide +kernel

theorem h23973 : P.leaf 34 23973 = 3875868 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 3875868)]) (.cons c23973_0 (.nil)) (by decide) (by decide))

theorem cover23974 : P.CoversSplit 24 10 23974 0xaaaa0000aaaa00000000000000000000aaaa00000000000000000000000000008880000088800000000000000000000088800000000000000000000000000000aaaa0000aaaa00000000000000000000aaaa00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 466, 515, 517, 522, 858, 865, 1202, 1259, 1601]) (by decide +kernel)

theorem c23974_0 : P.sumLeaves 24 24549376 1024 = 11127630 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23974) (lo := 0) (len := 1024) (W := 11127630) check rows elimOK (by decide) (by decide) cover23974 (by decide)
  decide +kernel

theorem h23974 : P.leaf 34 23974 = 11127630 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 11127630)]) (.cons c23974_0 (.nil)) (by decide) (by decide))

theorem cover23975 : P.CoversSplit 24 10 23975 0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa000000000000aaaa0000000000008888000088880000888800008888000088880000000000008888000000000000aaaa0000aaaa00000000000000000000aaaa00000000000000220000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [466, 515, 517, 522, 858, 865, 1202, 1210, 1259, 1601]) (by decide +kernel)

theorem c23975_0 : P.sumLeaves 24 24550400 1021 = 22883818 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23975) (lo := 0) (len := 1021) (W := 22883818) check rows elimOK (by decide) (by decide) cover23975 (by decide)
  decide +kernel

theorem c23975_1 : P.sumLeaves 24 24551421 3 = 2886040 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23975) (lo := 1021) (len := 3) (W := 2886040) check rows elimOK (by decide) (by decide) cover23975 (by decide)
  decide +kernel

theorem h23975 : P.leaf 34 23975 = 25769858 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1021, 22883818), (3, 2886040)]) (.cons c23975_0 (.cons c23975_1 (.nil))) (by decide) (by decide))

theorem cover23976 : P.CoversSplit 24 10 23976 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [472]) (by decide +kernel)

theorem c23976_0 : P.sumLeaves 24 24551424 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23976) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover23976 (by decide)
  decide +kernel

theorem h23976 : P.leaf 34 23976 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c23976_0 (.nil)) (by decide) (by decide))

theorem cover23977 : P.CoversSplit 24 10 23977 0xaaaa0000bab00000aaaa0000bab00000aaaa000000000000aaaa0000000000008888000088800000880000008800000088880000000000008800000000000000aa000000ba0000000000000000000000aa0000000000000000220000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [472, 473, 515, 522, 858, 865, 916, 1202, 1210, 1259, 1601]) (by decide +kernel)

theorem c23977_0 : P.sumLeaves 24 24552448 320 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23977) (lo := 0) (len := 320) (W := 0) check rows elimOK (by decide) (by decide) cover23977 (by decide)
  decide +kernel

theorem contract23977_1 : P.leaf 30 383637 = 70528 := by
  exact leaf_contract_factors (k := 30) (b := 19) (H := 383637) (ss := [(30, 1, 472), (11, 1, 508), (3, 1, 524), (29, 1, 916), (31, 1, 1210), (26, 1, 515), (21, 1, 1266), (14, 1, 923), (2, 1, 487), (18, 1, 923), (20, 1, 1272)]) (ids := [2, 3, 4, 5, 6, 7, 8, 10, 11, 13, 14, 15, 17, 20, 21, 25, 26, 22, 23]) (cs := [1, 1, 2, 3, 4, 5, 6, 7, 8, 1, 9, 10, 1, 11, 12, 13, 1, 14, 1, 1, 15, 16, 19, 20, 1, 17, 18, 1, 1, 1]) (bs := [17, 2]) (W := 70528) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c23977_1 : P.sumLeaves 24 24552768 64 = 70528 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 383637) rows (by decide) (by decide)).symm.trans contract23977_1

theorem c23977_2 : P.sumLeaves 24 24552832 640 = 7331828 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23977) (lo := 384) (len := 640) (W := 7331828) check rows elimOK (by decide) (by decide) cover23977 (by decide)
  decide +kernel

theorem h23977 : P.leaf 34 23977 = 7402356 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(320, 0), (64, 70528), (640, 7331828)]) (.cons c23977_0 (.cons c23977_1 (.cons c23977_2 (.nil)))) (by decide) (by decide))

theorem cover23978 : P.CoversSplit 24 10 23978 0xaaaa0000aaaa00000000000000000000aaaa00000000000000000000000000008880000088800000000000000000000088800000000000000000000000000000aaaa0000aaaa00000000000000000000aaaa00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 472, 515, 517, 522, 858, 865, 1202, 1259, 1601]) (by decide +kernel)

theorem c23978_0 : P.sumLeaves 24 24553472 1024 = 3793384 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23978) (lo := 0) (len := 1024) (W := 3793384) check rows elimOK (by decide) (by decide) cover23978 (by decide)
  decide +kernel

theorem h23978 : P.leaf 34 23978 = 3793384 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 3793384)]) (.cons c23978_0 (.nil)) (by decide) (by decide))

theorem cover23979 : P.CoversSplit 24 10 23979 0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa000000000000aaaa0000000000008888000088880000880000008800000088880000000000008800000000000000aaaa0000aaaa00000000000000000000aaaa00000000000000220000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [472, 515, 517, 522, 858, 865, 916, 1202, 1210, 1259, 1601]) (by decide +kernel)

theorem c23979_0 : P.sumLeaves 24 24554496 1024 = 21176370 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23979) (lo := 0) (len := 1024) (W := 21176370) check rows elimOK (by decide) (by decide) cover23979 (by decide)
  decide +kernel

theorem h23979 : P.leaf 34 23979 = 21176370 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 21176370)]) (.cons c23979_0 (.nil)) (by decide) (by decide))

theorem cover23980 : P.CoversSplit 24 10 23980 0 :=
  coversSplit check rows (by decide) (by decide) (xs := [508]) (by decide +kernel)

theorem c23980_0 : P.sumLeaves 24 24555520 1024 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23980) (lo := 0) (len := 1024) (W := 0) check rows elimOK (by decide) (by decide) cover23980 (by decide)
  decide +kernel

theorem h23980 : P.leaf 34 23980 = 0 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 0)]) (.cons c23980_0 (.nil)) (by decide) (by decide))

theorem cover23981 : P.CoversSplit 24 10 23981 0xaaaa0000bab0a0a0aaaa0000bab0a0a0aaaa000000005050aaaa0000000050408888000088808080888800008880808088880000000040408888000000004040aa000000ba00a0000000000000000000aa0000000000500000220000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 515, 517, 522, 858, 865, 916, 1202, 1210, 1259, 1601]) (ps := [(14, [867], [916]), (17, [1259], [1251])]) (by decide +kernel)

theorem c23981_0 : P.sumLeaves 24 24556544 980 = 9613194 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23981) (lo := 0) (len := 980) (W := 9613194) check rows elimOK (by decide) (by decide) cover23981 (by decide)
  decide +kernel

theorem c23981_1 : P.sumLeaves 24 24557524 44 = 7478690 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23981) (lo := 980) (len := 44) (W := 7478690) check rows elimOK (by decide) (by decide) cover23981 (by decide)
  decide +kernel

theorem h23981 : P.leaf 34 23981 = 17091884 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(980, 9613194), (44, 7478690)]) (.cons c23981_0 (.cons c23981_1 (.nil))) (by decide) (by decide))

theorem cover23982 : P.CoversSplit 24 10 23982 0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa000000000000aaaa0000000000008880000088800000880000008800000088800000000000008800000000000000aaaa0000aaaa00000000000000000000aaaa00000000000000220000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 515, 517, 522, 858, 865, 1202, 1259, 1601]) (by decide +kernel)

theorem c23982_0 : P.sumLeaves 24 24557568 1024 = 21976726 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23982) (lo := 0) (len := 1024) (W := 21976726) check rows elimOK (by decide) (by decide) cover23982 (by decide)
  decide +kernel

theorem h23982 : P.leaf 34 23982 = 21976726 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 21976726)]) (.cons c23982_0 (.nil)) (by decide) (by decide))

theorem cover23983 : P.CoversSplit 24 10 23983 0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa000000000000aaaa0000000000008888000088880000888800008888000088880000000000008888000000000000aaaa0000aaaa00000000000000000000aaaa00000000000000220000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 517, 522, 858, 865, 1202, 1210, 1259, 1601]) (by decide +kernel)

theorem c23983_0 : P.sumLeaves 24 24558592 1021 = 45678058 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23983) (lo := 0) (len := 1021) (W := 45678058) check rows elimOK (by decide) (by decide) cover23983 (by decide)
  decide +kernel

theorem c23983_1 : P.sumLeaves 24 24559613 3 = 4954192 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23983) (lo := 1021) (len := 3) (W := 4954192) check rows elimOK (by decide) (by decide) cover23983 (by decide)
  decide +kernel

theorem h23983 : P.leaf 34 23983 = 50632250 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1021, 45678058), (3, 4954192)]) (.cons c23983_0 (.cons c23983_1 (.nil))) (by decide) (by decide))

theorem cover23990 : P.CoversSplit 24 10 23990 0xfffffffffafaa0a0fffffffffafaa0a0fffffffffafaa0a0ffff000000000000ccc0ccc088808080cc00cc0088008000ccc0ccc088808080cc00000000000000fffffffffafaa0a0fffffffffafaa0a0fffffffffafaa0a0ffff000000000000ccc0ccc088808080cc00cc008800800000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 517, 858, 865, 1202, 1210, 1251, 1259, 1308, 1601]) (by decide +kernel)

theorem c23990_0 : P.sumLeaves 24 24565760 401 = 6039682 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23990) (lo := 0) (len := 401) (W := 6039682) check rows elimOK (by decide) (by decide) cover23990 (by decide)
  decide +kernel

theorem c23990_1 : P.sumLeaves 24 24566161 182 = 17405436 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23990) (lo := 401) (len := 182) (W := 17405436) check rows elimOK (by decide) (by decide) cover23990 (by decide)
  decide +kernel

theorem c23990_2 : P.sumLeaves 24 24566343 300 = 20910366 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23990) (lo := 583) (len := 300) (W := 20910366) check rows elimOK (by decide) (by decide) cover23990 (by decide)
  decide +kernel

theorem c23990_3 : P.sumLeaves 24 24566643 128 = 41816612 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23990) (lo := 883) (len := 128) (W := 41816612) check rows elimOK (by decide) (by decide) cover23990 (by decide)
  decide +kernel

theorem c23990_4 : P.sumLeaves 24 24566771 13 = 12309080 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23990) (lo := 1011) (len := 13) (W := 12309080) check rows elimOK (by decide) (by decide) cover23990 (by decide)
  decide +kernel

theorem h23990 : P.leaf 34 23990 = 98481176 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(401, 6039682), (182, 17405436), (300, 20910366), (128, 41816612), (13, 12309080)]) (.cons c23990_0 (.cons c23990_1 (.cons c23990_2 (.cons c23990_3 (.cons c23990_4 (.nil)))))) (by decide) (by decide))

theorem cover23991 : P.CoversSplit 24 10 23991 0xfffffffffafaa0a0fffffffffafaa0a0fffffffffafaa0a0ffff000000000000cccccccc88888080cccccccc88888080cccccccc88888080cccc000000000000fffffffffafaa0a0fffffffffafaa0a0fffffffffafaa0a0ffff000000000000cccccccc88888080cccccccc8888808000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [517, 858, 865, 1202, 1210, 1251, 1259, 1308, 1601]) (by decide +kernel)

theorem c23991_0 : P.sumLeaves 24 24566784 372 = 10689788 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23991) (lo := 0) (len := 372) (W := 10689788) check rows elimOK (by decide) (by decide) cover23991 (by decide)
  decide +kernel

theorem c23991_1 : P.sumLeaves 24 24567156 128 = 34763262 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23991) (lo := 372) (len := 128) (W := 34763262) check rows elimOK (by decide) (by decide) cover23991 (by decide)
  decide +kernel

theorem c23991_2 : P.sumLeaves 24 24567284 326 = 35649732 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23991) (lo := 500) (len := 326) (W := 35649732) check rows elimOK (by decide) (by decide) cover23991 (by decide)
  decide +kernel

theorem c23991_3 : P.sumLeaves 24 24567610 128 = 55528989 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23991) (lo := 826) (len := 128) (W := 55528989) check rows elimOK (by decide) (by decide) cover23991 (by decide)
  decide +kernel

theorem c23991_4 : P.sumLeaves 24 24567738 70 = 81522960 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 23991) (lo := 954) (len := 70) (W := 81522960) check rows elimOK (by decide) (by decide) cover23991 (by decide)
  decide +kernel

theorem h23991 : P.leaf 34 23991 = 218154731 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(372, 10689788), (128, 34763262), (326, 35649732), (128, 55528989), (70, 81522960)]) (.cons c23991_0 (.cons c23991_1 (.cons c23991_2 (.cons c23991_3 (.cons c23991_4 (.nil)))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(23972, 12), (23973, 24), (23974, 24), (23975, 48), (23976, 24), (23977, 48), (23978, 48), (23979, 48), (23980, 48), (23981, 48), (23982, 48), (23983, 48), (23990, 12), (23991, 24)]

theorem segOK : checkSeg 16 perms 23972 23993 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 23972 23993 504 13874027352 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 13874027352)
    (SegSum.cons (w := 12) h23972 (SegSum.cons (w := 24) h23973 (SegSum.cons (w := 24) h23974 (SegSum.cons (w := 48) h23975 (SegSum.cons (w := 24) h23976 (SegSum.cons (w := 48) h23977 (SegSum.cons (w := 48) h23978 (SegSum.cons (w := 48) h23979 (SegSum.cons (w := 48) h23980 (SegSum.cons (w := 48) h23981 (SegSum.cons (w := 48) h23982 (SegSum.cons (w := 48) h23983 (SegSum.cons (w := 12) h23990 (SegSum.cons (w := 24) h23991 (show SegSum (P.leaf 34) [] 0 from rfl))))))))))))))) (by decide)

end RACert.S4N1.C0.S85
