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

namespace RACert.S4N1.C0.S81

open RACert RACert.Problem

theorem cover22508 : P.CoversSplit 24 10 22508 0xffffffffeaeaaaaaffffffffeaeaaaaaffffffffeaaaaaaaffff000000000000cccccccc88888888cccccccc88888888cccccccc88888888cccc000000000000ff33ff33ea22aa220000000000000000ff33ff33ea22aa2200330000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 515, 522, 916, 1210, 1251, 1259, 1601]) (ps := [(12, [860], [909])]) (by decide +kernel)

theorem c22508_0 : P.sumLeaves 24 23048192 256 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22508) (lo := 0) (len := 256) (W := 0) check rows elimOK (by decide) (by decide) cover22508 (by decide)
  decide +kernel

theorem contract22508_1 : P.leaf 30 360132 = 948 := by
  apply (leaf_contract (k := 30) (b := 14) (H := 360132) (ss := [(30, 1, 1251), (31, 1, 1251), (17, 0, 1259), (4, 1, 565), (27, 0, 1259), (29, 0, 1259), (14, 0, 916), (12, 1, 867), (21, 1, 874), (20, 1, 880), (15, 0, 916), (3, 1, 509), (10, 1, 852), (11, 1, 901), (18, 1, 921), (9, 8, 1021)]) (ids := [0, 3, 4, 5, 6, 11, 14, 17, 20, 21, 22, 23, 24, 26]) (cs := [2, 1, 1, 3, 4, 5, 6, 6, 1, 1, 1, 7, 0, 0, 8, 0, 1, 9, 1, 1, 10, 11, 12, 13, 14, 0, 15, 0, 1, 1]) check rows (by decide) (by decide +kernel) (by decide +kernel)).trans
  decide +kernel

theorem c22508_1 : P.sumLeaves 24 23048448 64 = 948 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 360132) rows (by decide) (by decide)).symm.trans contract22508_1

theorem c22508_2 : P.sumLeaves 24 23048512 302 = 8926115 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22508) (lo := 320) (len := 302) (W := 8926115) check rows elimOK (by decide) (by decide) cover22508 (by decide)
  decide +kernel

theorem c22508_3 : P.sumLeaves 24 23048814 247 = 11139587 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22508) (lo := 622) (len := 247) (W := 11139587) check rows elimOK (by decide) (by decide) cover22508 (by decide)
  decide +kernel

theorem c22508_4 : P.sumLeaves 24 23049061 124 = 21162675 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22508) (lo := 869) (len := 124) (W := 21162675) check rows elimOK (by decide) (by decide) cover22508 (by decide)
  decide +kernel

theorem c22508_5 : P.sumLeaves 24 23049185 31 = 20048710 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22508) (lo := 993) (len := 31) (W := 20048710) check rows elimOK (by decide) (by decide) cover22508 (by decide)
  decide +kernel

theorem h22508 : P.leaf 34 22508 = 61278035 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(256, 0), (64, 948), (302, 8926115), (247, 11139587), (124, 21162675), (31, 20048710)]) (.cons c22508_0 (.cons c22508_1 (.cons c22508_2 (.cons c22508_3 (.cons c22508_4 (.cons c22508_5 (.nil))))))) (by decide) (by decide))

theorem cover22509 : P.CoversSplit 24 10 22509 0xffffffffeaeaaaaaffffffffeaeaaaaaffffffffeaaaaaaaffff000000000000cccccccc88888888cccccccc88888888cccccccc88888888cccc000000000000ff33ff33ea22aa220000000000000000ff33ff33ea22aa2200330000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 515, 522, 860, 916, 1210, 1251, 1259, 1601]) (ps := [(12, [860], [909])]) (by decide +kernel)

theorem c22509_0 : P.sumLeaves 24 23049216 256 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22509) (lo := 0) (len := 256) (W := 0) check rows elimOK (by decide) (by decide) cover22509 (by decide)
  decide +kernel

theorem contract22509_1 : P.leaf 30 360148 = 3096 := by
  apply (leaf_contract (k := 30) (b := 16) (H := 360148) (ss := [(30, 1, 1251), (31, 1, 1251), (17, 0, 1259), (4, 1, 565), (27, 0, 1259), (29, 0, 1259), (14, 0, 916), (12, 1, 867), (15, 0, 916), (11, 1, 901), (18, 1, 921), (21, 1, 923), (20, 1, 929), (9, 8, 1021)]) (ids := [0, 1, 3, 4, 5, 6, 8, 11, 14, 17, 20, 21, 22, 23, 24, 26]) (cs := [2, 3, 1, 4, 5, 6, 7, 7, 8, 1, 1, 9, 0, 0, 10, 0, 1, 11, 1, 1, 12, 13, 14, 15, 16, 0, 17, 0, 1, 1]) check rows (by decide) (by decide +kernel) (by decide +kernel)).trans
  decide +kernel

theorem c22509_1 : P.sumLeaves 24 23049472 64 = 3096 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 360148) rows (by decide) (by decide)).symm.trans contract22509_1

theorem c22509_2 : P.sumLeaves 24 23049536 302 = 19750970 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22509) (lo := 320) (len := 302) (W := 19750970) check rows elimOK (by decide) (by decide) cover22509 (by decide)
  decide +kernel

theorem c22509_3 : P.sumLeaves 24 23049838 247 = 27214876 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22509) (lo := 622) (len := 247) (W := 27214876) check rows elimOK (by decide) (by decide) cover22509 (by decide)
  decide +kernel

theorem c22509_4 : P.sumLeaves 24 23050085 124 = 39982290 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22509) (lo := 869) (len := 124) (W := 39982290) check rows elimOK (by decide) (by decide) cover22509 (by decide)
  decide +kernel

theorem c22509_5 : P.sumLeaves 24 23050209 31 = 34881244 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22509) (lo := 993) (len := 31) (W := 34881244) check rows elimOK (by decide) (by decide) cover22509 (by decide)
  decide +kernel

theorem h22509 : P.leaf 34 22509 = 121832476 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(256, 0), (64, 3096), (302, 19750970), (247, 27214876), (124, 39982290), (31, 34881244)]) (.cons c22509_0 (.cons c22509_1 (.cons c22509_2 (.cons c22509_3 (.cons c22509_4 (.cons c22509_5 (.nil))))))) (by decide) (by decide))

theorem cover22510 : P.CoversSplit 24 10 22510 0xfffffffffafaaaaafffffffffafaaaaafffffffffafaaaaaffff000000000000cccccccc88888888cccccccc88888888cccccccc88888888cccc000000000000fffffffffafaaaaa0000000000000000fffffffffafaaaaa00330000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 515, 522, 860, 916, 1202, 1210, 1251, 1259, 1601]) (by decide +kernel)

theorem c22510_0 : P.sumLeaves 24 23050240 500 = 25809330 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22510) (lo := 0) (len := 500) (W := 25809330) check rows elimOK (by decide) (by decide) cover22510 (by decide)
  decide +kernel

theorem c22510_1 : P.sumLeaves 24 23050740 320 = 27053894 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22510) (lo := 500) (len := 320) (W := 27053894) check rows elimOK (by decide) (by decide) cover22510 (by decide)
  decide +kernel

theorem c22510_2 : P.sumLeaves 24 23051060 120 = 38362189 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22510) (lo := 820) (len := 120) (W := 38362189) check rows elimOK (by decide) (by decide) cover22510 (by decide)
  decide +kernel

theorem c22510_3 : P.sumLeaves 24 23051180 84 = 73902706 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22510) (lo := 940) (len := 84) (W := 73902706) check rows elimOK (by decide) (by decide) cover22510 (by decide)
  decide +kernel

theorem h22510 : P.leaf 34 22510 = 165128119 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(500, 25809330), (320, 27053894), (120, 38362189), (84, 73902706)]) (.cons c22510_0 (.cons c22510_1 (.cons c22510_2 (.cons c22510_3 (.nil))))) (by decide) (by decide))

theorem cover22511 : P.CoversSplit 24 10 22511 0xfffffffffafaaaaafffffffffafaaaaafffffffffafaaaaaffff000000000000cccccccc88888888cccccccc88888888cccccccc88888888cccc000000000000fffffffffafaaaaa0000000000000000fffffffffafaaaaa00330000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 522, 860, 916, 1202, 1210, 1251, 1259, 1601]) (by decide +kernel)

theorem c22511_0 : P.sumLeaves 24 23051264 500 = 54228112 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22511) (lo := 0) (len := 500) (W := 54228112) check rows elimOK (by decide) (by decide) cover22511 (by decide)
  decide +kernel

theorem c22511_1 : P.sumLeaves 24 23051764 320 = 59549474 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22511) (lo := 500) (len := 320) (W := 59549474) check rows elimOK (by decide) (by decide) cover22511 (by decide)
  decide +kernel

theorem c22511_2 : P.sumLeaves 24 23052084 120 = 75816190 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22511) (lo := 820) (len := 120) (W := 75816190) check rows elimOK (by decide) (by decide) cover22511 (by decide)
  decide +kernel

theorem c22511_3 : P.sumLeaves 24 23052204 84 = 138499552 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22511) (lo := 940) (len := 84) (W := 138499552) check rows elimOK (by decide) (by decide) cover22511 (by decide)
  decide +kernel

theorem h22511 : P.leaf 34 22511 = 328093328 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(500, 54228112), (320, 59549474), (120, 75816190), (84, 138499552)]) (.cons c22511_0 (.cons c22511_1 (.cons c22511_2 (.cons c22511_3 (.nil))))) (by decide) (by decide))

theorem cover22525 : P.CoversSplit 24 10 22525 0xfffffffffafaaaaafffffffffafaaaaafffffffffa00aa00fffffffffa00aa00cccccccc88888888cccccccc88888888cccccccc88008800cccccccc88008800ff33ff33fa32aa22ff33ff33fa32aa22ff33ff33fa00aa00ff33ff33fa00aa000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 860, 909, 916, 1202, 1210, 1259, 1601]) (by decide +kernel)

theorem c22525_0 : P.sumLeaves 24 23065600 433 = 24782983 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22525) (lo := 0) (len := 433) (W := 24782983) check rows elimOK (by decide) (by decide) cover22525 (by decide)
  decide +kernel

theorem c22525_1 : P.sumLeaves 24 23066033 234 = 38282381 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22525) (lo := 433) (len := 234) (W := 38282381) check rows elimOK (by decide) (by decide) cover22525 (by decide)
  decide +kernel

theorem c22525_2 : P.sumLeaves 24 23066267 199 = 55483726 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22525) (lo := 667) (len := 199) (W := 55483726) check rows elimOK (by decide) (by decide) cover22525 (by decide)
  decide +kernel

theorem c22525_3 : P.sumLeaves 24 23066466 119 = 89154156 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22525) (lo := 866) (len := 119) (W := 89154156) check rows elimOK (by decide) (by decide) cover22525 (by decide)
  decide +kernel

theorem c22525_4 : P.sumLeaves 24 23066585 39 = 51504962 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22525) (lo := 985) (len := 39) (W := 51504962) check rows elimOK (by decide) (by decide) cover22525 (by decide)
  decide +kernel

theorem h22525 : P.leaf 34 22525 = 259208208 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(433, 24782983), (234, 38282381), (199, 55483726), (119, 89154156), (39, 51504962)]) (.cons c22525_0 (.cons c22525_1 (.cons c22525_2 (.cons c22525_3 (.cons c22525_4 (.nil)))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(22508, 24), (22509, 48), (22510, 24), (22511, 48), (22525, 24)]

theorem segOK : checkSeg 16 perms 22508 22527 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 22508 22527 168 33251183280 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 33251183280)
    (SegSum.cons (w := 24) h22508 (SegSum.cons (w := 48) h22509 (SegSum.cons (w := 24) h22510 (SegSum.cons (w := 48) h22511 (SegSum.cons (w := 24) h22525 (show SegSum (P.leaf 34) [] 0 from rfl)))))) (by decide)

end RACert.S4N1.C0.S81
