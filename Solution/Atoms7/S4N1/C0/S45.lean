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

namespace RACert.S4N1.C0.S45

open RACert RACert.Problem

theorem cover7028 : P.CoversSplit 24 10 7028 0xfcfcfcfca8a8a0a0fcfcfcfca8a8a0a0f0f0f0f000000000f0f0f0f000000000cc00cc0080008000cc00cc0080008000c000c00000000000c000c00000000000cc00cc0088008000cc30cc3088208020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 508, 572, 859, 879, 916, 1202, 1209, 1259, 1308, 1601]) (ps := [(14, [880], [859])]) (by decide +kernel)

theorem c7028_0 : P.sumLeaves 24 7196672 512 = 171036 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7028) (lo := 0) (len := 512) (W := 171036) check rows elimOK (by decide) (by decide) cover7028 (by decide)
  decide +kernel

theorem contract7028_1 : P.leaf 30 112456 = 7552 := by
  apply (leaf_contract (k := 30) (b := 17) (H := 112456) (ss := [(2, 1, 479), (19, 1, 578), (12, 1, 866), (6, 1, 459), (11, 1, 459), (4, 1, 410), (18, 1, 867), (31, 1, 879), (14, 1, 880), (28, 1, 859), (17, 1, 880), (27, 1, 1259), (29, 1, 1601)]) (ids := [1, 3, 5, 6, 7, 8, 11, 13, 14, 18, 19, 20, 21, 22, 23, 24, 28]) (cs := [1, 2, 1, 3, 1, 4, 5, 6, 7, 1, 1, 8, 1, 9, 10, 1, 1, 1, 11, 12, 13, 14, 15, 16, 17, 1, 1, 1, 18, 1]) check rows (by decide) (by decide +kernel) (by decide +kernel)).trans
  decide +kernel

theorem c7028_1 : P.sumLeaves 24 7197184 64 = 7552 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 112456) rows (by decide) (by decide)).symm.trans contract7028_1

theorem c7028_2 : P.sumLeaves 24 7197248 407 = 972718 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7028) (lo := 576) (len := 407) (W := 972718) check rows elimOK (by decide) (by decide) cover7028 (by decide)
  decide +kernel

theorem c7028_3 : P.sumLeaves 24 7197655 41 = 1120690 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7028) (lo := 983) (len := 41) (W := 1120690) check rows elimOK (by decide) (by decide) cover7028 (by decide)
  decide +kernel

theorem h7028 : P.leaf 34 7028 = 2271996 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(512, 171036), (64, 7552), (407, 972718), (41, 1120690)]) (.cons c7028_0 (.cons c7028_1 (.cons c7028_2 (.cons c7028_3 (.nil))))) (by decide) (by decide))

theorem cover7029 : P.CoversSplit 24 10 7029 0xffffffffafafa0a0ffffffffafafa0a0ffffffff00000000ffffffff00000000cc33cc3380008000cc00cc0080008000cc33cc3300000000cc00cc0000000000cc00cc008c008000cc33cc338c238020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 572, 859, 879, 916, 1202, 1209, 1258, 1259, 1308, 1601]) (by decide +kernel)

theorem c7029_0 : P.sumLeaves 24 7197696 808 = 3917433 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7029) (lo := 0) (len := 808) (W := 3917433) check rows elimOK (by decide) (by decide) cover7029 (by decide)
  decide +kernel

theorem c7029_1 : P.sumLeaves 24 7198504 144 = 5921666 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7029) (lo := 808) (len := 144) (W := 5921666) check rows elimOK (by decide) (by decide) cover7029 (by decide)
  decide +kernel

theorem c7029_2 : P.sumLeaves 24 7198648 72 = 13833436 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7029) (lo := 952) (len := 72) (W := 13833436) check rows elimOK (by decide) (by decide) cover7029 (by decide)
  decide +kernel

theorem h7029 : P.leaf 34 7029 = 23672535 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(808, 3917433), (144, 5921666), (72, 13833436)]) (.cons c7029_0 (.cons c7029_1 (.cons c7029_2 (.nil)))) (by decide) (by decide))

theorem cover7030 : P.CoversSplit 24 10 7030 0xffffffffafafa0a0ffffffffafafa0a0f0f0f0f00000a0a0f0f0f0f000000000cc33cc3380008000cc00cc0080008000c030c03000008000c000c00000000000ffffffffafafa0a0ffffffffafafa0a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 572, 859, 879, 1202, 1209, 1258, 1259, 1308, 1601]) (ps := [(12, [866], [859]), (14, [880], [859])]) (by decide +kernel)

theorem c7030_0 : P.sumLeaves 24 7198720 558 = 4027642 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7030) (lo := 0) (len := 558) (W := 4027642) check rows elimOK (by decide) (by decide) cover7030 (by decide)
  decide +kernel

theorem c7030_1 : P.sumLeaves 24 7199278 373 = 6272999 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7030) (lo := 558) (len := 373) (W := 6272999) check rows elimOK (by decide) (by decide) cover7030 (by decide)
  decide +kernel

theorem c7030_2 : P.sumLeaves 24 7199651 93 = 22012448 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7030) (lo := 931) (len := 93) (W := 22012448) check rows elimOK (by decide) (by decide) cover7030 (by decide)
  decide +kernel

theorem h7030 : P.leaf 34 7030 = 32313089 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(558, 4027642), (373, 6272999), (93, 22012448)]) (.cons c7030_0 (.cons c7030_1 (.cons c7030_2 (.nil)))) (by decide) (by decide))

theorem cover7031 : P.CoversSplit 24 10 7031 0xffffffffafafa0a0ffffffffafafa0a0ffffffffafafa0a0ffffffffafafa0a0cc33cc3380008000cc00cc0080008000cc33cc3380008000cc00cc0080008000ffffffffafafa0a0ffffffffafafa0a0000000000000000000000000000000000000000000000000cc00cc008000800000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [572, 859, 1202, 1209, 1217, 1258, 1259, 1308, 1601, 1609]) (by decide +kernel)

theorem c7031_0 : P.sumLeaves 24 7199744 128 = 0 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7031) (lo := 0) (len := 128) (W := 0) check rows elimOK (by decide) (by decide) cover7031 (by decide)
  decide +kernel

theorem contract7031_1 : P.leaf 30 112498 = 0 := by
  exact leaf_contract_zero (ss := [(2, 1, 475), (4, 1, 578), (12, 10, 866), (10, 1, 908), (6, 1, 480), (11, 1, 921), (14, 1, 965), (18, 1, 965), (27, 1, 1259), (19, 1, 1308), (9, 1, 587), (17, 1, 1273), (29, 1, 1601), (13, 1, 922)]) (q := 1609) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c7031_1 : P.sumLeaves 24 7199872 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 112498) rows (by decide) (by decide)).symm.trans contract7031_1

theorem c7031_2 : P.sumLeaves 24 7199936 335 = 7502445 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7031) (lo := 192) (len := 335) (W := 7502445) check rows elimOK (by decide) (by decide) cover7031 (by decide)
  decide +kernel

theorem c7031_3 : P.sumLeaves 24 7200271 297 = 8215254 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7031) (lo := 527) (len := 297) (W := 8215254) check rows elimOK (by decide) (by decide) cover7031 (by decide)
  decide +kernel

theorem c7031_4 : P.sumLeaves 24 7200568 128 = 20424096 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7031) (lo := 824) (len := 128) (W := 20424096) check rows elimOK (by decide) (by decide) cover7031 (by decide)
  decide +kernel

theorem c7031_5 : P.sumLeaves 24 7200696 72 = 42150488 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7031) (lo := 952) (len := 72) (W := 42150488) check rows elimOK (by decide) (by decide) cover7031 (by decide)
  decide +kernel

theorem h7031 : P.leaf 34 7031 = 78292283 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(128, 0), (64, 0), (335, 7502445), (297, 8215254), (128, 20424096), (72, 42150488)]) (.cons c7031_0 (.cons c7031_1 (.cons c7031_2 (.cons c7031_3 (.cons c7031_4 (.cons c7031_5 (.nil))))))) (by decide) (by decide))

theorem cover7032 : P.CoversSplit 24 10 7032 0xfcfcfcfca8a8a0a0fcfcfcfca8a8a0a0f0f0f4f400000000f0f0f4f400000000cc00cc0080008000cc00cc0080008000c000c40000000000c000c40000000000cc00cc0088008000cc00cc0088008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 508, 572, 859, 879, 916, 1202, 1209, 1259, 1308, 1601]) (ps := [(8, [586], [572]), (14, [923], [916])]) (by decide +kernel)

theorem c7032_0 : P.sumLeaves 24 7200768 925 = 952036 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7032) (lo := 0) (len := 925) (W := 952036) check rows elimOK (by decide) (by decide) cover7032 (by decide)
  decide +kernel

theorem c7032_1 : P.sumLeaves 24 7201693 99 = 2076780 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7032) (lo := 925) (len := 99) (W := 2076780) check rows elimOK (by decide) (by decide) cover7032 (by decide)
  decide +kernel

theorem h7032 : P.leaf 34 7032 = 3028816 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(925, 952036), (99, 2076780)]) (.cons c7032_0 (.cons c7032_1 (.nil))) (by decide) (by decide))

theorem cover7033 : P.CoversSplit 24 10 7033 0xffffffffafafa0a0ffffffffafafa0a0ffffffff00000000ffffffff00000000cc33cc3380008000cc00cc0080008000cc33cc3300000000cc00cc0000000000cc00cc008c008000cc00cc008c008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 572, 859, 879, 916, 1202, 1209, 1258, 1259, 1308, 1601]) (ps := [(5, [523], [572]), (8, [586], [572, 1609]), (14, [923], [916])]) (by decide +kernel)

theorem c7033_0 : P.sumLeaves 24 7201792 820 = 3927404 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7033) (lo := 0) (len := 820) (W := 3927404) check rows elimOK (by decide) (by decide) cover7033 (by decide)
  decide +kernel

theorem c7033_1 : P.sumLeaves 24 7202612 156 = 8147290 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7033) (lo := 820) (len := 156) (W := 8147290) check rows elimOK (by decide) (by decide) cover7033 (by decide)
  decide +kernel

theorem c7033_2 : P.sumLeaves 24 7202768 48 = 7824648 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7033) (lo := 976) (len := 48) (W := 7824648) check rows elimOK (by decide) (by decide) cover7033 (by decide)
  decide +kernel

theorem h7033 : P.leaf 34 7033 = 19899342 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(820, 3927404), (156, 8147290), (48, 7824648)]) (.cons c7033_0 (.cons c7033_1 (.cons c7033_2 (.nil)))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(7028, 48), (7029, 48), (7030, 48), (7031, 48), (7032, 48), (7033, 48)]

theorem segOK : checkSeg 16 perms 7028 7034 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 7028 7034 288 7654946928 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 7654946928)
    (SegSum.cons (w := 48) h7028 (SegSum.cons (w := 48) h7029 (SegSum.cons (w := 48) h7030 (SegSum.cons (w := 48) h7031 (SegSum.cons (w := 48) h7032 (SegSum.cons (w := 48) h7033 (show SegSum (P.leaf 34) [] 0 from rfl))))))) (by decide)

end RACert.S4N1.C0.S45
