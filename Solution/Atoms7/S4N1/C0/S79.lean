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

namespace RACert.S4N1.C0.S79

open RACert RACert.Problem

theorem cover22398 : P.CoversSplit 24 10 22398 0xfffffffffafaaaaafffffffffafaaaaafffffffffafaaaaafffffffffafaaaaacccccccc88888888cc00cc0088008800cccccccc88888888cc00cc0088008800fffffffffafaaaaafffffffffafaaaaafffffffffafaaaaafffffffffafaaaaa0000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 572, 860, 867, 916, 1202, 1210, 1601]) (by decide +kernel)

theorem c22398_0 : P.sumLeaves 24 22935552 376 = 10344444 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22398) (lo := 0) (len := 376) (W := 10344444) check rows elimOK (by decide) (by decide) cover22398 (by decide)
  decide +kernel

theorem c22398_1 : P.sumLeaves 24 22935928 120 = 24017466 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22398) (lo := 376) (len := 120) (W := 24017466) check rows elimOK (by decide) (by decide) cover22398 (by decide)
  decide +kernel

theorem c22398_2 : P.sumLeaves 24 22936048 289 = 26651794 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22398) (lo := 496) (len := 289) (W := 26651794) check rows elimOK (by decide) (by decide) cover22398 (by decide)
  decide +kernel

theorem c22398_3 : P.sumLeaves 24 22936337 112 = 45832734 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22398) (lo := 785) (len := 112) (W := 45832734) check rows elimOK (by decide) (by decide) cover22398 (by decide)
  decide +kernel

theorem c22398_4 : P.sumLeaves 24 22936449 119 = 88437287 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22398) (lo := 897) (len := 119) (W := 88437287) check rows elimOK (by decide) (by decide) cover22398 (by decide)
  decide +kernel

theorem c22398_5 : P.sumLeaves 24 22936568 8 = 9524700 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22398) (lo := 1016) (len := 8) (W := 9524700) check rows elimOK (by decide) (by decide) cover22398 (by decide)
  decide +kernel

theorem h22398 : P.leaf 34 22398 = 204808425 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(376, 10344444), (120, 24017466), (289, 26651794), (112, 45832734), (119, 88437287), (8, 9524700)]) (.cons c22398_0 (.cons c22398_1 (.cons c22398_2 (.cons c22398_3 (.cons c22398_4 (.cons c22398_5 (.nil))))))) (by decide) (by decide))

theorem cover22399 : P.CoversSplit 24 10 22399 0xfffffffffafaaaaafffffffffafaaaaafffffffffafaaaaafffffffffafaaaaacccccccc88888888cc00cc0088008800cccccccc88888888cc00cc0088008800fffffffffafaaaaafffffffffafaaaaafffffffffafaaaaafffffffffafaaaaa0000000000000000cc00cc0088008800cccccccc80808080cc00cc0080008000 :=
  coversProjected check rows (by decide) (by decide) (xs := [572, 860, 916, 1202, 1210, 1601, 1609]) (ps := [(8, [1217], [1272])]) (by decide +kernel)

theorem contract22399_0 : P.leaf 30 358384 = 2752 := by
  apply (leaf_contract (k := 30) (b := 16) (H := 358384) (ss := [(4, 1, 578), (29, 27, 1601), (27, 1, 572), (8, 0, 1609), (5, 1, 622), (14, 0, 1609), (20, 1, 580), (21, 1, 586), (9, 7, 629), (12, 1, 825), (15, 13, 972), (31, 1, 1217), (17, 16, 1315), (19, 18, 1658)]) (ids := [0, 1, 4, 5, 8, 9, 11, 14, 16, 20, 21, 22, 23, 24, 26, 28]) (cs := [2, 3, 1, 1, 4, 5, 0, 5, 6, 7, 1, 8, 0, 8, 9, 9, 10, 10, 1, 1, 11, 12, 13, 14, 15, 1, 16, 1, 17, 1]) check rows (by decide) (by decide +kernel) (by decide +kernel)).trans
  decide +kernel

theorem c22399_0 : P.sumLeaves 24 22936576 64 = 2752 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 358384) rows (by decide) (by decide)).symm.trans contract22399_0

theorem c22399_1 : P.sumLeaves 24 22936640 64 = 110144 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22399) (lo := 64) (len := 64) (W := 110144) check rows elimOK (by decide) (by decide) cover22399 (by decide)
  decide +kernel

theorem contract22399_2 : P.leaf 30 358386 = 115728 := by
  exact leaf_contract_factors (k := 30) (b := 19) (H := 358386) (ss := [(4, 1, 578), (29, 27, 1601), (27, 1, 572), (8, 0, 1609), (5, 1, 580), (14, 0, 1609), (12, 1, 965), (15, 1, 972), (21, 1, 972), (20, 1, 1021), (18, 1, 1658)]) (ids := [0, 1, 4, 5, 7, 8, 9, 11, 14, 17, 20, 21, 22, 23, 24, 26, 28, 29, 15]) (cs := [2, 3, 1, 1, 4, 5, 0, 6, 7, 8, 1, 9, 0, 1, 10, 20, 1, 11, 1, 1, 12, 13, 14, 15, 16, 1, 17, 1, 18, 19]) (bs := [18, 1]) (W := 115728) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c22399_2 : P.sumLeaves 24 22936704 64 = 115728 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 358386) rows (by decide) (by decide)).symm.trans contract22399_2

theorem c22399_3 : P.sumLeaves 24 22936768 184 = 22377104 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22399) (lo := 192) (len := 184) (W := 22377104) check rows elimOK (by decide) (by decide) cover22399 (by decide)
  decide +kernel

theorem c22399_4 : P.sumLeaves 24 22936952 120 = 48343375 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22399) (lo := 376) (len := 120) (W := 48343375) check rows elimOK (by decide) (by decide) cover22399 (by decide)
  decide +kernel

theorem c22399_5 : P.sumLeaves 24 22937072 289 = 67849062 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22399) (lo := 496) (len := 289) (W := 67849062) check rows elimOK (by decide) (by decide) cover22399 (by decide)
  decide +kernel

theorem c22399_6 : P.sumLeaves 24 22937361 112 = 95135545 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22399) (lo := 785) (len := 112) (W := 95135545) check rows elimOK (by decide) (by decide) cover22399 (by decide)
  decide +kernel

theorem c22399_7 : P.sumLeaves 24 22937473 119 = 171524798 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22399) (lo := 897) (len := 119) (W := 171524798) check rows elimOK (by decide) (by decide) cover22399 (by decide)
  decide +kernel

theorem c22399_8 : P.sumLeaves 24 22937592 8 = 16936644 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22399) (lo := 1016) (len := 8) (W := 16936644) check rows elimOK (by decide) (by decide) cover22399 (by decide)
  decide +kernel

theorem h22399 : P.leaf 34 22399 = 422395152 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(64, 2752), (64, 110144), (64, 115728), (184, 22377104), (120, 48343375), (289, 67849062), (112, 95135545), (119, 171524798), (8, 16936644)]) (.cons c22399_0 (.cons c22399_1 (.cons c22399_2 (.cons c22399_3 (.cons c22399_4 (.cons c22399_5 (.cons c22399_6 (.cons c22399_7 (.cons c22399_8 (.nil)))))))))) (by decide) (by decide))

theorem cover22444 : P.CoversSplit 24 10 22444 0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa000000000000aaaa0000000000008888000088880000888800008888000088880000000000008888000000000000aa220000aa2200000000000000000000aa2200000000000000220000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 508, 515, 517, 522, 916, 1202, 1259, 1601]) (by decide +kernel)

theorem c22444_0 : P.sumLeaves 24 22982656 1024 = 7741442 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22444) (lo := 0) (len := 1024) (W := 7741442) check rows elimOK (by decide) (by decide) cover22444 (by decide)
  decide +kernel

theorem h22444 : P.leaf 34 22444 = 7741442 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 7741442)]) (.cons c22444_0 (.nil)) (by decide) (by decide))

theorem cover22445 : P.CoversSplit 24 10 22445 0xffffffffeaea0000ffffffffeaea0000aaaaafaf00000000aaaa000000000000cccccccc88880000cccccccc8888000088888c8c000000008888000000000000ff33ff33ea2200000000000000000000aa22af230000000000220000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 515, 517, 522, 860, 916, 1202, 1210, 1251, 1259, 1601]) (by decide +kernel)

theorem c22445_0 : P.sumLeaves 24 22983680 758 = 9663029 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22445) (lo := 0) (len := 758) (W := 9663029) check rows elimOK (by decide) (by decide) cover22445 (by decide)
  decide +kernel

theorem c22445_1 : P.sumLeaves 24 22984438 244 = 20851952 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22445) (lo := 758) (len := 244) (W := 20851952) check rows elimOK (by decide) (by decide) cover22445 (by decide)
  decide +kernel

theorem c22445_2 : P.sumLeaves 24 22984682 22 = 11960246 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22445) (lo := 1002) (len := 22) (W := 11960246) check rows elimOK (by decide) (by decide) cover22445 (by decide)
  decide +kernel

theorem h22445 : P.leaf 34 22445 = 42475227 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(758, 9663029), (244, 20851952), (22, 11960246)]) (.cons c22445_0 (.cons c22445_1 (.cons c22445_2 (.nil)))) (by decide) (by decide))

theorem cover22446 : P.CoversSplit 24 10 22446 0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa000000000000aaaa0000000000008888000088880000888800008888000088880000000000008888000000000000aaaa0000aaaa00000000000000000000aaaa00000000000000220000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 515, 517, 522, 860, 916, 1202, 1259, 1601]) (by decide +kernel)

theorem c22446_0 : P.sumLeaves 24 22984704 1021 = 16106796 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22446) (lo := 0) (len := 1021) (W := 16106796) check rows elimOK (by decide) (by decide) cover22446 (by decide)
  decide +kernel

theorem c22446_1 : P.sumLeaves 24 22985725 3 = 1319956 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22446) (lo := 1021) (len := 3) (W := 1319956) check rows elimOK (by decide) (by decide) cover22446 (by decide)
  decide +kernel

theorem h22446 : P.leaf 34 22446 = 17426752 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1021, 16106796), (3, 1319956)]) (.cons c22446_0 (.cons c22446_1 (.nil))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(22398, 48), (22399, 48), (22444, 48), (22445, 48), (22446, 48)]

theorem segOK : checkSeg 16 perms 22398 22447 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 22398 22447 240 33352655904 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 33352655904)
    (SegSum.cons (w := 48) h22398 (SegSum.cons (w := 48) h22399 (SegSum.cons (w := 48) h22444 (SegSum.cons (w := 48) h22445 (SegSum.cons (w := 48) h22446 (show SegSum (P.leaf 34) [] 0 from rfl)))))) (by decide)

end RACert.S4N1.C0.S79
