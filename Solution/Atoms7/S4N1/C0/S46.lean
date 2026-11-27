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

namespace RACert.S4N1.C0.S46

open RACert RACert.Problem

theorem cover7034 : P.CoversSplit 24 10 7034 0xffffffffafafa0a0ffffffffafafa0a0f0f0f5f500000000f0f0f5f500000000cc33cc3380008000cc00cc0080008000c030c43100000000c000c40000000000ffffffffafafa0a0ffffffffafafa0a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 572, 859, 879, 916, 1202, 1209, 1258, 1259, 1308, 1601]) (by decide +kernel)

theorem c7034_0 : P.sumLeaves 24 7202816 554 = 1506988 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7034) (lo := 0) (len := 554) (W := 1506988) check rows elimOK (by decide) (by decide) cover7034 (by decide)
  decide +kernel

theorem c7034_1 : P.sumLeaves 24 7203370 369 = 3436264 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7034) (lo := 554) (len := 369) (W := 3436264) check rows elimOK (by decide) (by decide) cover7034 (by decide)
  decide +kernel

theorem c7034_2 : P.sumLeaves 24 7203739 101 = 10546850 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7034) (lo := 923) (len := 101) (W := 10546850) check rows elimOK (by decide) (by decide) cover7034 (by decide)
  decide +kernel

theorem h7034 : P.leaf 34 7034 = 15490102 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(554, 1506988), (369, 3436264), (101, 10546850)]) (.cons c7034_0 (.cons c7034_1 (.cons c7034_2 (.nil)))) (by decide) (by decide))

theorem cover7035 : P.CoversSplit 24 10 7035 0xffffffffafafa0a0ffffffffafafa0a0ffffffffafafa0a0ffffffffafafa0a0cc33cc3380008000cc00cc0080008000cc33cc3380008000cc00cc0080008000ffffffffafafa0a0ffffffffafafa0a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [572, 859, 916, 1202, 1209, 1217, 1258, 1259, 1308, 1601, 1609]) (ps := [(8, [586], [1609])]) (by decide +kernel)

theorem c7035_0 : P.sumLeaves 24 7203840 527 = 3683028 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7035) (lo := 0) (len := 527) (W := 3683028) check rows elimOK (by decide) (by decide) cover7035 (by decide)
  decide +kernel

theorem c7035_1 : P.sumLeaves 24 7204367 297 = 8277927 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7035) (lo := 527) (len := 297) (W := 8277927) check rows elimOK (by decide) (by decide) cover7035 (by decide)
  decide +kernel

theorem c7035_2 : P.sumLeaves 24 7204664 128 = 15326503 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7035) (lo := 824) (len := 128) (W := 15326503) check rows elimOK (by decide) (by decide) cover7035 (by decide)
  decide +kernel

theorem c7035_3 : P.sumLeaves 24 7204792 72 = 25886037 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7035) (lo := 952) (len := 72) (W := 25886037) check rows elimOK (by decide) (by decide) cover7035 (by decide)
  decide +kernel

theorem h7035 : P.leaf 34 7035 = 53173495 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(527, 3683028), (297, 8277927), (128, 15326503), (72, 25886037)]) (.cons c7035_0 (.cons c7035_1 (.cons c7035_2 (.cons c7035_3 (.nil))))) (by decide) (by decide))

theorem cover7036 : P.CoversSplit 24 10 7036 0xfcfcfcfca8a8a0a0fcfcfcfca8a8a0a0f0f0f4f400000000f0f0f4f400000000cc00cc0080008000cc00cc0080008000c000c40000000000c000c40000000000cc00cc0088008000cc30cc3088208020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 508, 572, 859, 879, 916, 1202, 1209, 1259, 1308, 1601]) (by decide +kernel)

theorem c7036_0 : P.sumLeaves 24 7204864 909 = 9020312 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7036) (lo := 0) (len := 909) (W := 9020312) check rows elimOK (by decide) (by decide) cover7036 (by decide)
  decide +kernel

theorem c7036_1 : P.sumLeaves 24 7205773 115 = 21458770 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7036) (lo := 909) (len := 115) (W := 21458770) check rows elimOK (by decide) (by decide) cover7036 (by decide)
  decide +kernel

theorem h7036 : P.leaf 34 7036 = 30479082 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(909, 9020312), (115, 21458770)]) (.cons c7036_0 (.cons c7036_1 (.nil))) (by decide) (by decide))

theorem cover7037 : P.CoversSplit 24 10 7037 0xffffffffafafa0a0ffffffffafafa0a0ffffffff00000000ffffffff00000000cc33cc3380008000cc00cc0080008000cc33cc3300000000cc00cc0000000000cc00cc008c008000cc33cc338c238020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 572, 859, 879, 916, 1202, 1209, 1258, 1259, 1308, 1601]) (by decide +kernel)

theorem c7037_0 : P.sumLeaves 24 7205888 808 = 10992141 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7037) (lo := 0) (len := 808) (W := 10992141) check rows elimOK (by decide) (by decide) cover7037 (by decide)
  decide +kernel

theorem c7037_1 : P.sumLeaves 24 7206696 144 = 18099706 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7037) (lo := 808) (len := 144) (W := 18099706) check rows elimOK (by decide) (by decide) cover7037 (by decide)
  decide +kernel

theorem c7037_2 : P.sumLeaves 24 7206840 72 = 38372864 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7037) (lo := 952) (len := 72) (W := 38372864) check rows elimOK (by decide) (by decide) cover7037 (by decide)
  decide +kernel

theorem h7037 : P.leaf 34 7037 = 67464711 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(808, 10992141), (144, 18099706), (72, 38372864)]) (.cons c7037_0 (.cons c7037_1 (.cons c7037_2 (.nil)))) (by decide) (by decide))

theorem cover7038 : P.CoversSplit 24 10 7038 0xffffffffafafa0a0ffffffffafafa0a0f0f0f5f500000000f0f0f5f500000000cc33cc3380008000cc00cc0080008000c030c43100000000c000c40000000000ffffffffafafa0a0ffffffffafafa0a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 572, 859, 879, 1202, 1209, 1258, 1259, 1308, 1601]) (by decide +kernel)

theorem c7038_0 : P.sumLeaves 24 7206912 554 = 6039470 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7038) (lo := 0) (len := 554) (W := 6039470) check rows elimOK (by decide) (by decide) cover7038 (by decide)
  decide +kernel

theorem c7038_1 : P.sumLeaves 24 7207466 369 = 16753399 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7038) (lo := 554) (len := 369) (W := 16753399) check rows elimOK (by decide) (by decide) cover7038 (by decide)
  decide +kernel

theorem c7038_2 : P.sumLeaves 24 7207835 101 = 51347604 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7038) (lo := 923) (len := 101) (W := 51347604) check rows elimOK (by decide) (by decide) cover7038 (by decide)
  decide +kernel

theorem h7038 : P.leaf 34 7038 = 74140473 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(554, 6039470), (369, 16753399), (101, 51347604)]) (.cons c7038_0 (.cons c7038_1 (.cons c7038_2 (.nil)))) (by decide) (by decide))

theorem cover7039 : P.CoversSplit 24 10 7039 0xffffffffafafa0a0ffffffffafafa0a0ffffffffafafa0a0ffffffffafafa0a0cc33cc3380008000cc00cc0080008000cc33cc3380008000cc00cc0080008000ffffffffafafa0a0ffffffffafafa0a0000000000000000000000000000000000000000000000000cc00cc008000800000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [572, 859, 1202, 1209, 1217, 1258, 1259, 1308, 1601, 1609]) (by decide +kernel)

theorem c7039_0 : P.sumLeaves 24 7207936 128 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7039) (lo := 0) (len := 128) (W := 0) check rows elimOK (by decide) (by decide) cover7039 (by decide)
  decide +kernel

theorem contract7039_1 : P.leaf 30 112626 = 6600 := by
  exact leaf_contract_factors (k := 30) (b := 15) (H := 112626) (ss := [(4, 1, 578), (10, 1, 866), (11, 1, 921), (27, 1, 1259), (19, 1, 1308), (29, 1, 1601), (8, 0, 1609), (5, 1, 580), (14, 0, 1609), (12, 1, 929), (13, 1, 972), (20, 1, 971), (21, 1, 972), (30, 1, 1266), (18, 1, 1658)]) (ids := [0, 1, 4, 5, 7, 13, 15, 20, 22, 23, 24, 26, 29, 14, 21]) (cs := [2, 3, 1, 1, 4, 5, 0, 6, 1, 1, 1, 1, 0, 7, 15, 8, 1, 1, 1, 1, 9, 16, 10, 11, 12, 1, 13, 1, 1, 14]) (bs := [13, 2]) (W := 6600) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c7039_1 : P.sumLeaves 24 7208064 64 = 6600 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 112626) rows (by decide) (by decide)).symm.trans contract7039_1

theorem c7039_2 : P.sumLeaves 24 7208128 335 = 10437752 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7039) (lo := 192) (len := 335) (W := 10437752) check rows elimOK (by decide) (by decide) cover7039 (by decide)
  decide +kernel

theorem c7039_3 : P.sumLeaves 24 7208463 297 = 24792292 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7039) (lo := 527) (len := 297) (W := 24792292) check rows elimOK (by decide) (by decide) cover7039 (by decide)
  decide +kernel

theorem c7039_4 : P.sumLeaves 24 7208760 128 = 48688156 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7039) (lo := 824) (len := 128) (W := 48688156) check rows elimOK (by decide) (by decide) cover7039 (by decide)
  decide +kernel

theorem c7039_5 : P.sumLeaves 24 7208888 72 = 78365035 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7039) (lo := 952) (len := 72) (W := 78365035) check rows elimOK (by decide) (by decide) cover7039 (by decide)
  decide +kernel

theorem h7039 : P.leaf 34 7039 = 162289835 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(128, 0), (64, 6600), (335, 10437752), (297, 24792292), (128, 48688156), (72, 78365035)]) (.cons c7039_0 (.cons c7039_1 (.cons c7039_2 (.cons c7039_3 (.cons c7039_4 (.cons c7039_5 (.nil))))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(7034, 48), (7035, 48), (7036, 48), (7037, 48), (7038, 48), (7039, 48)]

theorem segOK : checkSeg 16 perms 7034 7136 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 7034 7136 288 19345809504 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 19345809504)
    (SegSum.cons (w := 48) h7034 (SegSum.cons (w := 48) h7035 (SegSum.cons (w := 48) h7036 (SegSum.cons (w := 48) h7037 (SegSum.cons (w := 48) h7038 (SegSum.cons (w := 48) h7039 (show SegSum (P.leaf 34) [] 0 from rfl))))))) (by decide)

end RACert.S4N1.C0.S46
