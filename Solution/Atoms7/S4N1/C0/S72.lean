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

namespace RACert.S4N1.C0.S72

open RACert RACert.Problem

theorem cover21948 : P.CoversSplit 24 10 21948 0xf0000000f0000000f0000000f0000000f000000000000000f000000000000000c000000080000000c000000080000000c000000000000000c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 508, 858, 860, 867, 1202, 1210, 1217, 1601]) (by decide +kernel)

theorem c21948_0 : P.sumLeaves 24 22474752 1024 = 3592640 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21948) (lo := 0) (len := 1024) (W := 3592640) check rows elimOK (by decide) (by decide) cover21948 (by decide)
  decide +kernel

theorem h21948 : P.leaf 34 21948 = 3592640 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 3592640)]) (.cons c21948_0 (.nil)) (by decide) (by decide))

theorem cover21949 : P.CoversSplit 24 10 21949 0xfffffffffaf00000fffffffffaf00000f500f50000000000f500000000000000cccccccc88800000cccccccc88800000c400c40000000000c400000000000000ff33ff33fa300000ff33ff33fa300000f500f50050000000f5000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 517, 858, 860, 865, 909, 916, 1202, 1210, 1217, 1251, 1259, 1308, 1601]) (by decide +kernel)

theorem c21949_0 : P.sumLeaves 24 22475776 674 = 9677860 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21949) (lo := 0) (len := 674) (W := 9677860) check rows elimOK (by decide) (by decide) cover21949 (by decide)
  decide +kernel

theorem c21949_1 : P.sumLeaves 24 22476450 307 = 17803538 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21949) (lo := 674) (len := 307) (W := 17803538) check rows elimOK (by decide) (by decide) cover21949 (by decide)
  decide +kernel

theorem c21949_2 : P.sumLeaves 24 22476757 43 = 17862448 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21949) (lo := 981) (len := 43) (W := 17862448) check rows elimOK (by decide) (by decide) cover21949 (by decide)
  decide +kernel

theorem h21949 : P.leaf 34 21949 = 45343846 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(674, 9677860), (307, 17803538), (43, 17862448)]) (.cons c21949_0 (.cons c21949_1 (.cons c21949_2 (.nil)))) (by decide) (by decide))

theorem cover21950 : P.CoversSplit 24 10 21950 0xf0f00000f0f00000f0f00000f0f00000f000000000000000f000000000000000c0c0000080800000c000000080000000c000000000000000c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 858, 860, 865, 867, 909, 916, 1202, 1210, 1217, 1601]) (by decide +kernel)

theorem c21950_0 : P.sumLeaves 24 22476800 1024 = 9210732 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21950) (lo := 0) (len := 1024) (W := 9210732) check rows elimOK (by decide) (by decide) cover21950 (by decide)
  decide +kernel

theorem h21950 : P.leaf 34 21950 = 9210732 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 9210732)]) (.cons c21950_0 (.nil)) (by decide) (by decide))

theorem cover21951 : P.CoversSplit 24 10 21951 0xfffffffffafa0000fffffffffafa0000f500f50000000000f500000000000000cccccccc88880000cccccccc88880000c400c40000000000c400000000000000fffffffffafa0000fffffffffafa0000f500f50050000000f500000000000000cccccccc88880000cccccccc8888000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [517, 858, 860, 865, 909, 916, 1202, 1210, 1217, 1251, 1308, 1601]) (by decide +kernel)

theorem c21951_0 : P.sumLeaves 24 22477824 440 = 14387031 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21951) (lo := 0) (len := 440) (W := 14387031) check rows elimOK (by decide) (by decide) cover21951 (by decide)
  decide +kernel

theorem c21951_1 : P.sumLeaves 24 22478264 319 = 37954008 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21951) (lo := 440) (len := 319) (W := 37954008) check rows elimOK (by decide) (by decide) cover21951 (by decide)
  decide +kernel

theorem c21951_2 : P.sumLeaves 24 22478583 250 = 63517443 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21951) (lo := 759) (len := 250) (W := 63517443) check rows elimOK (by decide) (by decide) cover21951 (by decide)
  decide +kernel

theorem c21951_3 : P.sumLeaves 24 22478833 15 = 17520882 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21951) (lo := 1009) (len := 15) (W := 17520882) check rows elimOK (by decide) (by decide) cover21951 (by decide)
  decide +kernel

theorem h21951 : P.leaf 34 21951 = 133379364 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(440, 14387031), (319, 37954008), (250, 63517443), (15, 17520882)]) (.cons c21951_0 (.cons c21951_1 (.cons c21951_2 (.cons c21951_3 (.nil))))) (by decide) (by decide))

theorem cover21996 : P.CoversSplit 24 10 21996 0xf0f00000e0eaaaaaf0f00000e0eaaaaaf0f0000000000000f0f0000000000000c0c0000080808880c000000080008800c0c0000040400000c000000040000000f0000000e000aa000000000000000000f03000000000000000300000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 515, 522, 858, 860, 865, 916, 1210, 1259, 1601]) (ps := [(15, [909], [916])]) (by decide +kernel)

theorem c21996_0 : P.sumLeaves 24 22523904 990 = 3281112 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21996) (lo := 0) (len := 990) (W := 3281112) check rows elimOK (by decide) (by decide) cover21996 (by decide)
  decide +kernel

theorem c21996_1 : P.sumLeaves 24 22524894 34 = 1432200 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21996) (lo := 990) (len := 34) (W := 1432200) check rows elimOK (by decide) (by decide) cover21996 (by decide)
  decide +kernel

theorem h21996 : P.leaf 34 21996 = 4713312 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(990, 3281112), (34, 1432200)]) (.cons c21996_0 (.cons c21996_1 (.nil))) (by decide) (by decide))

theorem cover21997 : P.CoversSplit 24 10 21997 0xf0f00000e0eaaaaaf0f00000e0eaaaaaf0f0000000000000f0f0000000000000c0c0000080888888c0c0000080888888c0c0000040400000c0c0000040400000f0000000e000aa000000000000000000f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 515, 522, 858, 860, 865, 916, 1210, 1259, 1601]) (ps := [(14, [867], [916])]) (by decide +kernel)

theorem c21997_0 : P.sumLeaves 24 22524928 975 = 6912732 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21997) (lo := 0) (len := 975) (W := 6912732) check rows elimOK (by decide) (by decide) cover21997 (by decide)
  decide +kernel

theorem c21997_1 : P.sumLeaves 24 22525903 49 = 4147310 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21997) (lo := 975) (len := 49) (W := 4147310) check rows elimOK (by decide) (by decide) cover21997 (by decide)
  decide +kernel

theorem h21997 : P.leaf 34 21997 = 11060042 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(975, 6912732), (49, 4147310)]) (.cons c21997_0 (.cons c21997_1 (.nil))) (by decide) (by decide))

theorem cover21998 : P.CoversSplit 24 10 21998 0xf0f00000f0f00000f0f00000f0f00000f0f0000000000000f0f0000000000000c0c0000080800000c000000080000000c0c0000040400000c000000040000000f0f00000f0f000000000000000000000f0f000000000000000300000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 515, 522, 858, 860, 865, 916, 1202, 1210, 1259, 1601]) (by decide +kernel)

theorem c21998_0 : P.sumLeaves 24 22525952 1024 = 12641150 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21998) (lo := 0) (len := 1024) (W := 12641150) check rows elimOK (by decide) (by decide) cover21998 (by decide)
  decide +kernel

theorem h21998 : P.leaf 34 21998 = 12641150 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 12641150)]) (.cons c21998_0 (.nil)) (by decide) (by decide))

theorem cover21999 : P.CoversSplit 24 10 21999 0xf0f00000f0f00000f0f00000f0f00000f0f0000000000000f0f0000000000000c0c0000080800000c0c0000080800000c0c0000040400000c0c0000040400000f0f00000f0f000000000000000000000f0f000000000000000300000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 522, 858, 860, 916, 1202, 1210, 1259, 1601]) (by decide +kernel)

theorem c21999_0 : P.sumLeaves 24 22526976 1022 = 27869130 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21999) (lo := 0) (len := 1022) (W := 27869130) check rows elimOK (by decide) (by decide) cover21999 (by decide)
  decide +kernel

theorem c21999_1 : P.sumLeaves 24 22527998 2 = 2152056 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 21999) (lo := 1022) (len := 2) (W := 2152056) check rows elimOK (by decide) (by decide) cover21999 (by decide)
  decide +kernel

theorem h21999 : P.leaf 34 21999 = 30021186 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1022, 27869130), (2, 2152056)]) (.cons c21999_0 (.cons c21999_1 (.nil))) (by decide) (by decide))

theorem cover22013 : P.CoversSplit 24 10 22013 0xfffffffffaf0a0a0fffffffffaf0a0a0ff00ff00fa00a000ff00ff00fa00a000cccccccc88808080cccccccc88808080cc00cc0088008000cc00cc0088008000ff33ff33fa30a020ff33ff33fa30a020ff00ff00fa00a000ff00ff00fa00a0000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 858, 860, 865, 909, 916, 1202, 1210, 1259, 1601]) (by decide +kernel)

theorem c22013_0 : P.sumLeaves 24 22541312 484 = 22027434 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22013) (lo := 0) (len := 484) (W := 22027434) check rows elimOK (by decide) (by decide) cover22013 (by decide)
  decide +kernel

theorem c22013_1 : P.sumLeaves 24 22541796 326 = 29214704 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22013) (lo := 484) (len := 326) (W := 29214704) check rows elimOK (by decide) (by decide) cover22013 (by decide)
  decide +kernel

theorem c22013_2 : P.sumLeaves 24 22542122 180 = 55872428 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22013) (lo := 810) (len := 180) (W := 55872428) check rows elimOK (by decide) (by decide) cover22013 (by decide)
  decide +kernel

theorem c22013_3 : P.sumLeaves 24 22542302 34 = 27353346 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22013) (lo := 990) (len := 34) (W := 27353346) check rows elimOK (by decide) (by decide) cover22013 (by decide)
  decide +kernel

theorem h22013 : P.leaf 34 22013 = 134467912 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(484, 22027434), (326, 29214704), (180, 55872428), (34, 27353346)]) (.cons c22013_0 (.cons c22013_1 (.cons c22013_2 (.cons c22013_3 (.nil))))) (by decide) (by decide))

theorem cover22015 : P.CoversSplit 24 10 22015 0xfffffffffafaaaaafffffffffafaaaaafffffffffafaaaaafffffffffafaaaaacccccccc88888888cccccccc88888888cccccccc88888888cccccccc88888888fffffffffafaaaaafffffffffafaaaaafffffffffafaaaaafffffffffafaaaaacccccccc88888888cccccccc88888888cccccccc88888888cccccccc88888888 :=
  coversSplit check rows (by decide) (by decide) (xs := [858, 860, 865, 916, 1202, 1210, 1601]) (by decide +kernel)

theorem c22015_0 : P.sumLeaves 24 22543360 257 = 56850249 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22015) (lo := 0) (len := 257) (W := 56850249) check rows elimOK (by decide) (by decide) cover22015 (by decide)
  decide +kernel

theorem c22015_1 : P.sumLeaves 24 22543617 119 = 58554208 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22015) (lo := 257) (len := 119) (W := 58554208) check rows elimOK (by decide) (by decide) cover22015 (by decide)
  decide +kernel

theorem c22015_2 : P.sumLeaves 24 22543736 120 = 102129064 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22015) (lo := 376) (len := 120) (W := 102129064) check rows elimOK (by decide) (by decide) cover22015 (by decide)
  decide +kernel

theorem c22015_3 : P.sumLeaves 24 22543856 242 = 128146066 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22015) (lo := 496) (len := 242) (W := 128146066) check rows elimOK (by decide) (by decide) cover22015 (by decide)
  decide +kernel

theorem c22015_4 : P.sumLeaves 24 22544098 134 = 119037330 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22015) (lo := 738) (len := 134) (W := 119037330) check rows elimOK (by decide) (by decide) cover22015 (by decide)
  decide +kernel

theorem c22015_5 : P.sumLeaves 24 22544232 120 = 196742549 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22015) (lo := 872) (len := 120) (W := 196742549) check rows elimOK (by decide) (by decide) cover22015 (by decide)
  decide +kernel

theorem c22015_6 : P.sumLeaves 24 22544352 32 = 86138658 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22015) (lo := 992) (len := 32) (W := 86138658) check rows elimOK (by decide) (by decide) cover22015 (by decide)
  decide +kernel

theorem h22015 : P.leaf 34 22015 = 747598124 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(257, 56850249), (119, 58554208), (120, 102129064), (242, 128146066), (134, 119037330), (120, 196742549), (32, 86138658)]) (.cons c22015_0 (.cons c22015_1 (.cons c22015_2 (.cons c22015_3 (.cons c22015_4 (.cons c22015_5 (.cons c22015_6 (.nil)))))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(21948, 48), (21949, 48), (21950, 48), (21951, 48), (21996, 24), (21997, 48), (21998, 24), (21999, 48), (22013, 24), (22015, 24)]

theorem segOK : checkSeg 16 perms 21948 22199 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 21948 22199 384 32751266832 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 32751266832)
    (SegSum.cons (w := 48) h21948 (SegSum.cons (w := 48) h21949 (SegSum.cons (w := 48) h21950 (SegSum.cons (w := 48) h21951 (SegSum.cons (w := 24) h21996 (SegSum.cons (w := 48) h21997 (SegSum.cons (w := 24) h21998 (SegSum.cons (w := 48) h21999 (SegSum.cons (w := 24) h22013 (SegSum.cons (w := 24) h22015 (show SegSum (P.leaf 34) [] 0 from rfl))))))))))) (by decide)

end RACert.S4N1.C0.S72
