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

namespace RACert.S4N1.C0.S78

open RACert RACert.Problem

theorem cover22389 : P.CoversSplit 24 10 22389 0xfffffffffafaaaaafffffffffafaaaaafffffffffa00aa00fffffffffa00aa00cccccccc88888888cc00cc0088008800cccccccc88008800cc00cc0088008800ff33ff33fa32aa22ff33ff33fa32aa22ff33ff33fa00aa00ff33ff33fa00aa000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 860, 909, 916, 1202, 1210, 1259, 1601]) (by decide +kernel)

theorem c22389_0 : P.sumLeaves 24 22926336 433 = 5206631 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22389) (lo := 0) (len := 433) (W := 5206631) check rows elimOK (by decide) (by decide) cover22389 (by decide)
  decide +kernel

theorem c22389_1 : P.sumLeaves 24 22926769 282 = 12777413 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22389) (lo := 433) (len := 282) (W := 12777413) check rows elimOK (by decide) (by decide) cover22389 (by decide)
  decide +kernel

theorem c22389_2 : P.sumLeaves 24 22927051 171 = 20797910 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22389) (lo := 715) (len := 171) (W := 20797910) check rows elimOK (by decide) (by decide) cover22389 (by decide)
  decide +kernel

theorem c22389_3 : P.sumLeaves 24 22927222 120 = 32207465 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22389) (lo := 886) (len := 120) (W := 32207465) check rows elimOK (by decide) (by decide) cover22389 (by decide)
  decide +kernel

theorem c22389_4 : P.sumLeaves 24 22927342 18 = 10735178 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22389) (lo := 1006) (len := 18) (W := 10735178) check rows elimOK (by decide) (by decide) cover22389 (by decide)
  decide +kernel

theorem h22389 : P.leaf 34 22389 = 81724597 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(433, 5206631), (282, 12777413), (171, 20797910), (120, 32207465), (18, 10735178)]) (.cons c22389_0 (.cons c22389_1 (.cons c22389_2 (.cons c22389_3 (.cons c22389_4 (.nil)))))) (by decide) (by decide))

theorem cover22391 : P.CoversSplit 24 10 22391 0xfffffffffafaaaaafffffffffafaaaaafffffffffafaaaaafffffffffafaaaaacccccccc88888888cc00cc0088008800cccccccc88888888cc00cc0088008800fffffffffafaaaaafffffffffafaaaaafffffffffafaaaaafffffffffafaaaaa0000000000000000cc00cc0088008800cccccccc80808080cc00cc0080008000 :=
  coversProjected check rows (by decide) (by decide) (xs := [572, 860, 916, 1202, 1210, 1601, 1609]) (ps := [(8, [1217], [1272])]) (by decide +kernel)

theorem contract22391_0 : P.leaf 30 358256 = 136 := by
  exact leaf_contract_factors (k := 30) (b := 8) (H := 358256) (ss := [(2, 1, 475), (4, 1, 578), (29, 27, 1601), (27, 1, 572), (8, 0, 1609), (5, 1, 622), (14, 0, 1609), (21, 1, 482), (20, 1, 488), (9, 7, 629), (13, 1, 922), (7, 1, 628), (18, 1, 922), (12, 0, 965), (6, 1, 818), (31, 1, 880), (30, 1, 908), (25, 1, 915), (15, 1, 930), (19, 1, 930), (16, 1, 1314), (17, 1, 1315)]) (ids := [1, 8, 9, 21, 24, 26, 20, 22]) (cs := [1, 2, 1, 1, 1, 1, 0, 1, 3, 4, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 8, 5, 9, 1, 6, 1, 7, 1, 1, 1]) (bs := [6, 2]) (W := 136) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c22391_0 : P.sumLeaves 24 22928384 64 = 136 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 358256) rows (by decide) (by decide)).symm.trans contract22391_0

theorem c22391_1 : P.sumLeaves 24 22928448 64 = 16960 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22391) (lo := 64) (len := 64) (W := 16960) check rows elimOK (by decide) (by decide) cover22391 (by decide)
  decide +kernel

theorem contract22391_2 : P.leaf 30 358258 = 320 := by
  exact leaf_contract_factors (k := 30) (b := 10) (H := 358258) (ss := [(2, 1, 475), (4, 1, 578), (29, 27, 1601), (27, 1, 572), (8, 0, 1609), (5, 1, 580), (14, 0, 1609), (12, 0, 965), (6, 1, 818), (10, 0, 825), (11, 1, 803), (23, 1, 817), (28, 1, 872), (30, 1, 908), (25, 1, 915), (15, 1, 972), (19, 1, 930), (21, 1, 972), (18, 1, 1658), (13, 1, 922)]) (ids := [5, 7, 14, 15, 18, 22, 24, 29, 1, 20]) (cs := [1, 10, 1, 1, 1, 2, 0, 3, 0, 1, 0, 1, 0, 1, 4, 5, 1, 1, 6, 1, 11, 1, 7, 1, 8, 1, 1, 1, 1, 9]) (bs := [8, 2]) (W := 320) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c22391_2 : P.sumLeaves 24 22928512 64 = 320 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 358258) rows (by decide) (by decide)).symm.trans contract22391_2

theorem c22391_3 : P.sumLeaves 24 22928576 184 = 15311839 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22391) (lo := 192) (len := 184) (W := 15311839) check rows elimOK (by decide) (by decide) cover22391 (by decide)
  decide +kernel

theorem c22391_4 : P.sumLeaves 24 22928760 120 = 35740207 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22391) (lo := 376) (len := 120) (W := 35740207) check rows elimOK (by decide) (by decide) cover22391 (by decide)
  decide +kernel

theorem c22391_5 : P.sumLeaves 24 22928880 289 = 39151287 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22391) (lo := 496) (len := 289) (W := 39151287) check rows elimOK (by decide) (by decide) cover22391 (by decide)
  decide +kernel

theorem c22391_6 : P.sumLeaves 24 22929169 112 = 66257556 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22391) (lo := 785) (len := 112) (W := 66257556) check rows elimOK (by decide) (by decide) cover22391 (by decide)
  decide +kernel

theorem c22391_7 : P.sumLeaves 24 22929281 119 = 112436781 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22391) (lo := 897) (len := 119) (W := 112436781) check rows elimOK (by decide) (by decide) cover22391 (by decide)
  decide +kernel

theorem c22391_8 : P.sumLeaves 24 22929400 8 = 11946598 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22391) (lo := 1016) (len := 8) (W := 11946598) check rows elimOK (by decide) (by decide) cover22391 (by decide)
  decide +kernel

theorem h22391 : P.leaf 34 22391 = 280861684 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(64, 136), (64, 16960), (64, 320), (184, 15311839), (120, 35740207), (289, 39151287), (112, 66257556), (119, 112436781), (8, 11946598)]) (.cons c22391_0 (.cons c22391_1 (.cons c22391_2 (.cons c22391_3 (.cons c22391_4 (.cons c22391_5 (.cons c22391_6 (.cons c22391_7 (.cons c22391_8 (.nil)))))))))) (by decide) (by decide))

theorem cover22396 : P.CoversSplit 24 10 22396 0xfcfcfcfcf8f8a8a8fcfcfcfcf8f8a8a8fcfcfcfcf800a800fcfcfcfcf800a800cccccccc88888888cc00cc0088008800cccccccc88008800cc00cc0088008800fc30fc30f830a820fc30fc30f830a820fc30fc30f800a800fc30fc30f800a8000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 466, 473, 867, 909, 916, 1202, 1210, 1601]) (by decide +kernel)

theorem c22396_0 : P.sumLeaves 24 22933504 506 = 6241738 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22396) (lo := 0) (len := 506) (W := 6241738) check rows elimOK (by decide) (by decide) cover22396 (by decide)
  decide +kernel

theorem c22396_1 : P.sumLeaves 24 22934010 314 = 12499359 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22396) (lo := 506) (len := 314) (W := 12499359) check rows elimOK (by decide) (by decide) cover22396 (by decide)
  decide +kernel

theorem c22396_2 : P.sumLeaves 24 22934324 170 = 25741436 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22396) (lo := 820) (len := 170) (W := 25741436) check rows elimOK (by decide) (by decide) cover22396 (by decide)
  decide +kernel

theorem c22396_3 : P.sumLeaves 24 22934494 34 = 14805620 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22396) (lo := 990) (len := 34) (W := 14805620) check rows elimOK (by decide) (by decide) cover22396 (by decide)
  decide +kernel

theorem h22396 : P.leaf 34 22396 = 59288153 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(506, 6241738), (314, 12499359), (170, 25741436), (34, 14805620)]) (.cons c22396_0 (.cons c22396_1 (.cons c22396_2 (.cons c22396_3 (.nil))))) (by decide) (by decide))

theorem cover22397 : P.CoversSplit 24 10 22397 0xfffffffffafaaaaafffffffffafaaaaafffffffffa00aa00fffffffffa00aa00cccccccc88888888cc00cc0088008800cccccccc88008800cc00cc0088008800ff33ff33fa32aa22ff33ff33fa32aa22ff33ff33fa00aa00ff33ff33fa00aa000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 860, 909, 916, 1202, 1210, 1259, 1601]) (by decide +kernel)

theorem c22397_0 : P.sumLeaves 24 22934528 433 = 9928368 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22397) (lo := 0) (len := 433) (W := 9928368) check rows elimOK (by decide) (by decide) cover22397 (by decide)
  decide +kernel

theorem c22397_1 : P.sumLeaves 24 22934961 282 = 21170669 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22397) (lo := 433) (len := 282) (W := 21170669) check rows elimOK (by decide) (by decide) cover22397 (by decide)
  decide +kernel

theorem c22397_2 : P.sumLeaves 24 22935243 171 = 33079633 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22397) (lo := 715) (len := 171) (W := 33079633) check rows elimOK (by decide) (by decide) cover22397 (by decide)
  decide +kernel

theorem c22397_3 : P.sumLeaves 24 22935414 120 = 53613880 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22397) (lo := 886) (len := 120) (W := 53613880) check rows elimOK (by decide) (by decide) cover22397 (by decide)
  decide +kernel

theorem c22397_4 : P.sumLeaves 24 22935534 18 = 16313944 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 22397) (lo := 1006) (len := 18) (W := 16313944) check rows elimOK (by decide) (by decide) cover22397 (by decide)
  decide +kernel

theorem h22397 : P.leaf 34 22397 = 134106494 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(433, 9928368), (282, 21170669), (171, 33079633), (120, 53613880), (18, 16313944)]) (.cons c22397_0 (.cons c22397_1 (.cons c22397_2 (.cons c22397_3 (.cons c22397_4 (.nil)))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(22389, 24), (22391, 24), (22396, 48), (22397, 48)]

theorem segOK : checkSeg 16 perms 22389 22398 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 22389 22398 144 17985013800 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 17985013800)
    (SegSum.cons (w := 24) h22389 (SegSum.cons (w := 24) h22391 (SegSum.cons (w := 48) h22396 (SegSum.cons (w := 48) h22397 (show SegSum (P.leaf 34) [] 0 from rfl))))) (by decide)

end RACert.S4N1.C0.S78
