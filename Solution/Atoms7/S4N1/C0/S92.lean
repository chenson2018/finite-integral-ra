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

namespace RACert.S4N1.C0.S92

open RACert RACert.Problem

theorem cover24382 : P.CoversSplit 24 10 24382 0xfffffffffafaa0a0fffffffffafaa0a0fffffffffafaa0a0fffffffffafaa0a0cccccccc88888080cc00cc0088008000cccccccc88888080cc00cc0088008000fffffffffafaa0a0fffffffffafaa0a0fffffffffafaa0a0fffffffffafaa0a00000000000000000880088008800800000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 529, 572, 1202, 1210, 1259, 1308, 1601, 1609]) (by decide +kernel)

theorem c24382_0 : P.sumLeaves 24 24967168 128 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24382) (lo := 0) (len := 128) (W := 0) check rows elimOK (by decide) (by decide) cover24382 (by decide)
  decide +kernel

theorem contract24382_1 : P.leaf 30 390114 = 21060 := by
  exact leaf_contract_factors (k := 30) (b := 17) (H := 390114) (ss := [(3, 1, 524), (26, 1, 529), (4, 1, 578), (18, 1, 867), (29, 27, 1601), (27, 1, 572), (8, 0, 1609), (5, 1, 580), (14, 0, 1609), (9, 1, 629), (21, 1, 629), (20, 1, 678), (16, 1, 1265)]) (ids := [0, 4, 5, 8, 9, 10, 11, 13, 15, 17, 21, 22, 23, 26, 28, 29, 20]) (cs := [2, 1, 1, 1, 3, 4, 0, 1, 5, 6, 7, 8, 0, 9, 1, 10, 1, 11, 1, 1, 18, 12, 13, 14, 1, 1, 15, 1, 16, 17]) (bs := [16, 1]) (W := 21060) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c24382_1 : P.sumLeaves 24 24967296 64 = 21060 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 390114) rows (by decide) (by decide)).symm.trans contract24382_1

theorem c24382_2 : P.sumLeaves 24 24967360 197 = 15041161 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24382) (lo := 192) (len := 197) (W := 15041161) check rows elimOK (by decide) (by decide) cover24382 (by decide)
  decide +kernel

theorem c24382_3 : P.sumLeaves 24 24967557 138 = 45341378 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24382) (lo := 389) (len := 138) (W := 45341378) check rows elimOK (by decide) (by decide) cover24382 (by decide)
  decide +kernel

theorem c24382_4 : P.sumLeaves 24 24967695 287 = 32509756 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24382) (lo := 527) (len := 287) (W := 32509756) check rows elimOK (by decide) (by decide) cover24382 (by decide)
  decide +kernel

theorem c24382_5 : P.sumLeaves 24 24967982 128 = 81982429 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24382) (lo := 814) (len := 128) (W := 81982429) check rows elimOK (by decide) (by decide) cover24382 (by decide)
  decide +kernel

theorem c24382_6 : P.sumLeaves 24 24968110 82 = 112478109 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24382) (lo := 942) (len := 82) (W := 112478109) check rows elimOK (by decide) (by decide) cover24382 (by decide)
  decide +kernel

theorem h24382 : P.leaf 34 24382 = 287373893 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(128, 0), (64, 21060), (197, 15041161), (138, 45341378), (287, 32509756), (128, 81982429), (82, 112478109)]) (.cons c24382_0 (.cons c24382_1 (.cons c24382_2 (.cons c24382_3 (.cons c24382_4 (.cons c24382_5 (.cons c24382_6 (.nil)))))))) (by decide) (by decide))

theorem cover24383 : P.CoversSplit 24 10 24383 0xfffffffffafaa0a0fffffffffafaa0a0fffffffffafaa0a0fffffffffafaa0a0cccccccc88888080cc00cc0088008000cccccccc88888080cc00cc0088008000fffffffffafaa0a0fffffffffafaa0a0fffffffffafaa0a0fffffffffafaa0a00000000000000000cc00cc008800800000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [517, 572, 1202, 1210, 1259, 1308, 1601, 1609]) (by decide +kernel)

theorem c24383_0 : P.sumLeaves 24 24968192 128 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24383) (lo := 0) (len := 128) (W := 0) check rows elimOK (by decide) (by decide) cover24383 (by decide)
  decide +kernel

theorem contract24383_1 : P.leaf 30 390130 = 54212 := by
  exact leaf_contract_factors (k := 30) (b := 18) (H := 390130) (ss := [(3, 1, 524), (4, 1, 578), (18, 1, 1308), (29, 27, 1601), (27, 1, 572), (8, 0, 1609), (5, 1, 580), (14, 0, 1609), (9, 1, 629), (21, 1, 629), (20, 1, 678), (16, 1, 1265)]) (ids := [0, 4, 5, 8, 9, 10, 11, 13, 15, 17, 21, 22, 23, 24, 26, 28, 29, 20]) (cs := [2, 1, 1, 1, 3, 4, 0, 1, 5, 6, 7, 8, 0, 9, 1, 10, 1, 11, 1, 1, 19, 12, 13, 14, 15, 1, 16, 1, 17, 18]) (bs := [17, 1]) (W := 54212) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c24383_1 : P.sumLeaves 24 24968320 64 = 54212 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 390130) rows (by decide) (by decide)).symm.trans contract24383_1

theorem c24383_2 : P.sumLeaves 24 24968384 197 = 27892406 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24383) (lo := 192) (len := 197) (W := 27892406) check rows elimOK (by decide) (by decide) cover24383 (by decide)
  decide +kernel

theorem c24383_3 : P.sumLeaves 24 24968581 138 = 66076194 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24383) (lo := 389) (len := 138) (W := 66076194) check rows elimOK (by decide) (by decide) cover24383 (by decide)
  decide +kernel

theorem c24383_4 : P.sumLeaves 24 24968719 287 = 72270719 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24383) (lo := 527) (len := 287) (W := 72270719) check rows elimOK (by decide) (by decide) cover24383 (by decide)
  decide +kernel

theorem c24383_5 : P.sumLeaves 24 24969006 128 = 146530080 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24383) (lo := 814) (len := 128) (W := 146530080) check rows elimOK (by decide) (by decide) cover24383 (by decide)
  decide +kernel

theorem c24383_6 : P.sumLeaves 24 24969134 82 = 172794986 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24383) (lo := 942) (len := 82) (W := 172794986) check rows elimOK (by decide) (by decide) cover24383 (by decide)
  decide +kernel

theorem h24383 : P.leaf 34 24383 = 485618597 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(128, 0), (64, 54212), (197, 27892406), (138, 66076194), (287, 72270719), (128, 146530080), (82, 172794986)]) (.cons c24383_0 (.cons c24383_1 (.cons c24383_2 (.cons c24383_3 (.cons c24383_4 (.cons c24383_5 (.cons c24383_6 (.nil)))))))) (by decide) (by decide))

theorem cover24428 : P.CoversSplit 24 10 24428 0xcc00cc00c80088000000000000000000cc00cc00c80088000000000000000000cccccccc88808880cc00cc0088008800cccccccc88808880cc00cc0088008800cc00cc00c80088000000000000000000cc00cc00c800880000000000000000000000000000000000003300330022002200000000000000000033003300220022 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 515, 522, 572, 916, 1210, 1601]) (ps := [(2, [465], [473])]) (by decide +kernel)

theorem c24428_0 : P.sumLeaves 24 25014272 711 = 6960731 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24428) (lo := 0) (len := 711) (W := 6960731) check rows elimOK (by decide) (by decide) cover24428 (by decide)
  decide +kernel

theorem c24428_1 : P.sumLeaves 24 25014983 313 = 18694785 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24428) (lo := 711) (len := 313) (W := 18694785) check rows elimOK (by decide) (by decide) cover24428 (by decide)
  decide +kernel

theorem h24428 : P.leaf 34 24428 = 25655516 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(711, 6960731), (313, 18694785)]) (.cons c24428_0 (.cons c24428_1 (.nil))) (by decide) (by decide))

theorem cover24429 : P.CoversSplit 24 10 24429 0xcc00cc00c80088000000000000000000cc00cc00c80088000000000000000000cc00cc00880088000000000000000000cc00cc00880088000000000000000000cc00cc00c80088000000000000000000cc00cc00c800880000000000000000000000000000000000003300330022002200000000000000000033003300220022 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 515, 522, 572, 916, 1202, 1210, 1601]) (by decide +kernel)

theorem c24429_0 : P.sumLeaves 24 25015296 1018 = 33170312 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24429) (lo := 0) (len := 1018) (W := 33170312) check rows elimOK (by decide) (by decide) cover24429 (by decide)
  decide +kernel

theorem c24429_1 : P.sumLeaves 24 25016314 6 = 6942558 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24429) (lo := 1018) (len := 6) (W := 6942558) check rows elimOK (by decide) (by decide) cover24429 (by decide)
  decide +kernel

theorem h24429 : P.leaf 34 24429 = 40112870 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1018, 33170312), (6, 6942558)]) (.cons c24429_0 (.cons c24429_1 (.nil))) (by decide) (by decide))

theorem cover24430 : P.CoversSplit 24 10 24430 0xfffffffffafaaaaafffffffffafaaaaafffffffffafaaaaafffffffffafaaaaacccccccc88888888cc00cc0088008800cccccccc88888888cc00cc0088008800fffffffffafaaaaa0000000000000000fffffffffafaaaaa00330033003200220000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 515, 522, 1202, 1210, 1259, 1601]) (by decide +kernel)

theorem c24430_0 : P.sumLeaves 24 25016320 491 = 19712117 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24430) (lo := 0) (len := 491) (W := 19712117) check rows elimOK (by decide) (by decide) cover24430 (by decide)
  decide +kernel

theorem c24430_1 : P.sumLeaves 24 25016811 284 = 36218951 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24430) (lo := 491) (len := 284) (W := 36218951) check rows elimOK (by decide) (by decide) cover24430 (by decide)
  decide +kernel

theorem c24430_2 : P.sumLeaves 24 25017095 116 = 49847733 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24430) (lo := 775) (len := 116) (W := 49847733) check rows elimOK (by decide) (by decide) cover24430 (by decide)
  decide +kernel

theorem c24430_3 : P.sumLeaves 24 25017211 120 = 97184661 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24430) (lo := 891) (len := 120) (W := 97184661) check rows elimOK (by decide) (by decide) cover24430 (by decide)
  decide +kernel

theorem c24430_4 : P.sumLeaves 24 25017331 13 = 24345428 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24430) (lo := 1011) (len := 13) (W := 24345428) check rows elimOK (by decide) (by decide) cover24430 (by decide)
  decide +kernel

theorem h24430 : P.leaf 34 24430 = 227308890 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(491, 19712117), (284, 36218951), (116, 49847733), (120, 97184661), (13, 24345428)]) (.cons c24430_0 (.cons c24430_1 (.cons c24430_2 (.cons c24430_3 (.cons c24430_4 (.nil)))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(24382, 48), (24383, 48), (24428, 24), (24429, 24), (24430, 48)]

theorem segOK : checkSeg 16 perms 24382 24431 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 24382 24431 192 49592907504 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 49592907504)
    (SegSum.cons (w := 48) h24382 (SegSum.cons (w := 48) h24383 (SegSum.cons (w := 24) h24428 (SegSum.cons (w := 24) h24429 (SegSum.cons (w := 48) h24430 (show SegSum (P.leaf 34) [] 0 from rfl)))))) (by decide)

end RACert.S4N1.C0.S92
