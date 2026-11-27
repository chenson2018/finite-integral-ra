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

namespace RACert.S4N1.C0.S93

open RACert RACert.Problem

theorem cover24431 : P.CoversSplit 24 10 24431 0xfffffffffafaaaaafffffffffafaaaaafffffffffafaaaaafffffffffafaaaaacccccccc88888888cc00cc0088008800cccccccc88888888cc00cc0088008800fffffffffafaaaaa0000000000000000fffffffffafaaaaa00330033003200220000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 522, 1202, 1210, 1259, 1601]) (by decide +kernel)

theorem c24431_0 : P.sumLeaves 24 25017344 491 = 31559806 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24431) (lo := 0) (len := 491) (W := 31559806) check rows elimOK (by decide) (by decide) cover24431 (by decide)
  decide +kernel

theorem c24431_1 : P.sumLeaves 24 25017835 284 = 65883202 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24431) (lo := 491) (len := 284) (W := 65883202) check rows elimOK (by decide) (by decide) cover24431 (by decide)
  decide +kernel

theorem c24431_2 : P.sumLeaves 24 25018119 116 = 82412966 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24431) (lo := 775) (len := 116) (W := 82412966) check rows elimOK (by decide) (by decide) cover24431 (by decide)
  decide +kernel

theorem c24431_3 : P.sumLeaves 24 25018235 120 = 132156920 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24431) (lo := 891) (len := 120) (W := 132156920) check rows elimOK (by decide) (by decide) cover24431 (by decide)
  decide +kernel

theorem c24431_4 : P.sumLeaves 24 25018355 13 = 33997610 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24431) (lo := 1011) (len := 13) (W := 33997610) check rows elimOK (by decide) (by decide) cover24431 (by decide)
  decide +kernel

theorem h24431 : P.leaf 34 24431 = 346010504 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(491, 31559806), (284, 65883202), (116, 82412966), (120, 132156920), (13, 33997610)]) (.cons c24431_0 (.cons c24431_1 (.cons c24431_2 (.cons c24431_3 (.cons c24431_4 (.nil)))))) (by decide) (by decide))

theorem cover24446 : P.CoversSplit 24 10 24446 0xfffffffffafaaaaafffffffffafaaaaafffffffffafaaaaafffffffffafaaaaacccccccc88888888cc00cc0088008800cccccccc88888888cc00cc0088008800fffffffffafaaaaafffffffffafaaaaafffffffffafaaaaafffffffffafaaaaa0000000000000000cc00cc0088008800cccccccc80808080cc00cc0080008000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 572, 1202, 1210, 1259, 1601, 1609]) (ps := [(8, [1217], [1609])]) (by decide +kernel)

theorem contract24446_0 : P.leaf 30 391136 = 2432 := by
  exact leaf_contract_factors (k := 30) (b := 12) (H := 391136) (ss := [(4, 1, 578), (18, 1, 867), (29, 27, 1601), (27, 1, 572), (8, 0, 1609), (5, 1, 622), (14, 0, 1609), (20, 1, 580), (21, 1, 586), (9, 7, 629), (12, 1, 825), (13, 1, 971), (7, 1, 628), (15, 1, 972), (31, 1, 1217), (16, 1, 1314), (17, 1, 1315), (19, 1, 1658)]) (ids := [0, 1, 4, 8, 23, 9, 20, 21, 22, 24, 26, 28]) (cs := [2, 3, 1, 1, 4, 1, 0, 1, 5, 7, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 8, 9, 10, 6, 11, 1, 12, 1, 13, 1]) (bs := [5, 7]) (W := 2432) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c24446_0 : P.sumLeaves 24 25032704 64 = 2432 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 391136) rows (by decide) (by decide)).symm.trans contract24446_0

theorem c24446_1 : P.sumLeaves 24 25032768 278 = 16073526 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24446) (lo := 64) (len := 278) (W := 16073526) check rows elimOK (by decide) (by decide) cover24446 (by decide)
  decide +kernel

theorem c24446_2 : P.sumLeaves 24 25033046 115 = 48027868 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24446) (lo := 342) (len := 115) (W := 48027868) check rows elimOK (by decide) (by decide) cover24446 (by decide)
  decide +kernel

theorem c24446_3 : P.sumLeaves 24 25033161 250 = 62510444 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24446) (lo := 457) (len := 250) (W := 62510444) check rows elimOK (by decide) (by decide) cover24446 (by decide)
  decide +kernel

theorem c24446_4 : P.sumLeaves 24 25033411 157 = 95015756 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24446) (lo := 707) (len := 157) (W := 95015756) check rows elimOK (by decide) (by decide) cover24446 (by decide)
  decide +kernel

theorem c24446_5 : P.sumLeaves 24 25033568 118 = 179543442 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24446) (lo := 864) (len := 118) (W := 179543442) check rows elimOK (by decide) (by decide) cover24446 (by decide)
  decide +kernel

theorem c24446_6 : P.sumLeaves 24 25033686 42 = 108193560 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24446) (lo := 982) (len := 42) (W := 108193560) check rows elimOK (by decide) (by decide) cover24446 (by decide)
  decide +kernel

theorem h24446 : P.leaf 34 24446 = 509367028 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(64, 2432), (278, 16073526), (115, 48027868), (250, 62510444), (157, 95015756), (118, 179543442), (42, 108193560)]) (.cons c24446_0 (.cons c24446_1 (.cons c24446_2 (.cons c24446_3 (.cons c24446_4 (.cons c24446_5 (.cons c24446_6 (.nil)))))))) (by decide) (by decide))

theorem cover24447 : P.CoversSplit 24 10 24447 0xfffffffffafaaaaafffffffffafaaaaafffffffffafaaaaafffffffffafaaaaacccccccc88888888cc00cc0088008800cccccccc88888888cc00cc0088008800fffffffffafaaaaafffffffffafaaaaafffffffffafaaaaafffffffffafaaaaa0000000000000000cc00cc0088008800cccccccc80808080cc00cc0080008000 :=
  coversProjected check rows (by decide) (by decide) (xs := [572, 1202, 1210, 1259, 1601, 1609]) (ps := [(8, [1217], [1609])]) (by decide +kernel)

theorem contract24447_0 : P.leaf 30 391152 = 3648 := by
  apply (leaf_contract (k := 30) (b := 16) (H := 391152) (ss := [(4, 1, 578), (29, 27, 1601), (27, 1, 572), (8, 0, 1609), (5, 1, 622), (14, 0, 1609), (20, 1, 580), (21, 1, 586), (9, 7, 629), (12, 1, 825), (15, 13, 972), (31, 1, 1217), (17, 16, 1315), (19, 18, 1658)]) (ids := [0, 1, 4, 5, 8, 9, 11, 14, 16, 20, 21, 22, 23, 24, 26, 28]) (cs := [2, 3, 1, 1, 4, 5, 0, 5, 6, 7, 1, 8, 0, 8, 9, 9, 10, 10, 1, 1, 11, 12, 13, 14, 15, 1, 16, 1, 17, 1]) check rows (by decide) (by decide +kernel) (by decide +kernel)).trans
  decide +kernel

theorem c24447_0 : P.sumLeaves 24 25033728 64 = 3648 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 391152) rows (by decide) (by decide)).symm.trans contract24447_0

theorem c24447_1 : P.sumLeaves 24 25033792 278 = 23092829 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24447) (lo := 64) (len := 278) (W := 23092829) check rows elimOK (by decide) (by decide) cover24447 (by decide)
  decide +kernel

theorem c24447_2 : P.sumLeaves 24 25034070 115 = 61573984 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24447) (lo := 342) (len := 115) (W := 61573984) check rows elimOK (by decide) (by decide) cover24447 (by decide)
  decide +kernel

theorem c24447_3 : P.sumLeaves 24 25034185 250 = 92134444 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24447) (lo := 457) (len := 250) (W := 92134444) check rows elimOK (by decide) (by decide) cover24447 (by decide)
  decide +kernel

theorem c24447_4 : P.sumLeaves 24 25034435 157 = 141658604 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24447) (lo := 707) (len := 157) (W := 141658604) check rows elimOK (by decide) (by decide) cover24447 (by decide)
  decide +kernel

theorem c24447_5 : P.sumLeaves 24 25034592 118 = 234933805 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24447) (lo := 864) (len := 118) (W := 234933805) check rows elimOK (by decide) (by decide) cover24447 (by decide)
  decide +kernel

theorem c24447_6 : P.sumLeaves 24 25034710 42 = 137235914 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24447) (lo := 982) (len := 42) (W := 137235914) check rows elimOK (by decide) (by decide) cover24447 (by decide)
  decide +kernel

theorem h24447 : P.leaf 34 24447 = 690633228 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(64, 3648), (278, 23092829), (115, 61573984), (250, 92134444), (157, 141658604), (118, 234933805), (42, 137235914)]) (.cons c24447_0 (.cons c24447_1 (.cons c24447_2 (.cons c24447_3 (.cons c24447_4 (.cons c24447_5 (.cons c24447_6 (.nil)))))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(24431, 48), (24446, 24), (24447, 24)]

theorem segOK : checkSeg 16 perms 24431 24485 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 24431 24485 96 45408510336 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 45408510336)
    (SegSum.cons (w := 48) h24431 (SegSum.cons (w := 24) h24446 (SegSum.cons (w := 24) h24447 (show SegSum (P.leaf 34) [] 0 from rfl)))) (by decide)

end RACert.S4N1.C0.S93
