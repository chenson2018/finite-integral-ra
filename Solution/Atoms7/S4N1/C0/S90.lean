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

namespace RACert.S4N1.C0.S90

open RACert RACert.Problem

theorem cover24063 : P.CoversSplit 24 10 24063 0xfffffffffafaaaaafffffffffafaaaaafffffffffafaaaaafffffffffafaaaaacccccccc88888888cccccccc88888888cccccccc88888888cccccccc88888888fffffffffafaaaaafffffffffafaaaaafffffffffafaaaaafffffffffafaaaaacccccccc88888888cccccccc88888888cccccccc88888888cccccccc88888888 :=
  coversSplit check rows (by decide) (by decide) (xs := [858, 865, 1202, 1210, 1259, 1601]) (by decide +kernel)

theorem c24063_0 : P.sumLeaves 24 24640512 257 = 68208006 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24063) (lo := 0) (len := 257) (W := 68208006) check rows elimOK (by decide) (by decide) cover24063 (by decide)
  decide +kernel

theorem c24063_1 : P.sumLeaves 24 24640769 119 = 81328151 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24063) (lo := 257) (len := 119) (W := 81328151) check rows elimOK (by decide) (by decide) cover24063 (by decide)
  decide +kernel

theorem c24063_2 : P.sumLeaves 24 24640888 120 = 129659684 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24063) (lo := 376) (len := 120) (W := 129659684) check rows elimOK (by decide) (by decide) cover24063 (by decide)
  decide +kernel

theorem c24063_3 : P.sumLeaves 24 24641008 242 = 161509605 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24063) (lo := 496) (len := 242) (W := 161509605) check rows elimOK (by decide) (by decide) cover24063 (by decide)
  decide +kernel

theorem c24063_4 : P.sumLeaves 24 24641250 134 = 170578301 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24063) (lo := 738) (len := 134) (W := 170578301) check rows elimOK (by decide) (by decide) cover24063 (by decide)
  decide +kernel

theorem c24063_5 : P.sumLeaves 24 24641384 120 = 269100469 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24063) (lo := 872) (len := 120) (W := 269100469) check rows elimOK (by decide) (by decide) cover24063 (by decide)
  decide +kernel

theorem c24063_6 : P.sumLeaves 24 24641504 32 = 128030804 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24063) (lo := 992) (len := 32) (W := 128030804) check rows elimOK (by decide) (by decide) cover24063 (by decide)
  decide +kernel

theorem h24063 : P.leaf 34 24063 = 1008415020 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(257, 68208006), (119, 81328151), (120, 129659684), (242, 161509605), (134, 170578301), (120, 269100469), (32, 128030804)]) (.cons c24063_0 (.cons c24063_1 (.cons c24063_2 (.cons c24063_3 (.cons c24063_4 (.cons c24063_5 (.cons c24063_6 (.nil)))))))) (by decide) (by decide))

theorem cover24318 : P.CoversSplit 24 10 24318 0xfffffffffafa0000fffffffffafa0000fffffffffafa0000fffffffffafa00000000000000000000000000000000000000000000000000000000000000000000cc00cc00c80000000000000000000000cc00cc008000000000330033002000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 573, 916, 1202, 1210, 1259, 1308, 1601, 1651]) (ps := [(8, [1217], [573, 1266]), (14, [1217], [916, 1266])]) (by decide +kernel)

noncomputable def f24318 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 24 (24901632 + i)

theorem c24318_0 : rowSum f24318 0 947 = 78120007 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 24318) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover24318 (by decide)
  decide +kernel

theorem c24318_1 : rowSum f24318 947 77 = 70249792 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 24318) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover24318 (by decide)
  decide +kernel

theorem sum24318 : rowSum f24318 0 1024 = 148369799 :=
  rowSum_append (F := f24318) (lo := 0) (n := 947) (m := 77) (A := 78120007) (B := 70249792) c24318_0 (c24318_1)

theorem h24318 : P.leaf 34 24318 = 148369799 :=
  leaf_weighted (k := 24) (d := 10) (H := 24318) (keep := keep2) (twice := twice2) rows (by decide) (by decide) bal2 (invRow2 (H := 24318) (by decide) (by decide +kernel)) sum24318

theorem cover24319 : P.CoversSplit 24 10 24319 0xfffffffffafa0000fffffffffafa0000fffffffffafa0000fffffffffafa00000000000000000000000000000000000000000000000000000000000000000000cc00cc00c80000000000000000000000cc00cc008000000000330033002000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [573, 916, 1202, 1210, 1259, 1308, 1601, 1651]) (ps := [(8, [1217], [573, 1266]), (14, [1217], [916, 1266])]) (by decide +kernel)

noncomputable def f24319 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 24 (24902656 + i)

theorem c24319_0 : rowSum f24319 0 947 = 78129461 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 24319) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover24319 (by decide)
  decide +kernel

theorem c24319_1 : rowSum f24319 947 77 = 70249792 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 24319) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover24319 (by decide)
  decide +kernel

theorem sum24319 : rowSum f24319 0 1024 = 148379253 :=
  rowSum_append (F := f24319) (lo := 0) (n := 947) (m := 77) (A := 78129461) (B := 70249792) c24319_0 (c24319_1)

theorem h24319 : P.leaf 34 24319 = 148379253 :=
  leaf_weighted (k := 24) (d := 10) (H := 24319) (keep := keep2) (twice := twice2) rows (by decide) (by decide) bal2 (invRow2 (H := 24319) (by decide) (by decide +kernel)) sum24319

theorem cover24357 : P.CoversSplit 24 10 24357 0xcc00cc00c80080000000000000000000cc00cc00c80080000000000000000000cc00cc00880080000000000000000000cc00cc00880080000000000000000000cc00cc00c80080000000000000000000cc00cc00c800800000000000000000000000000000000000003300330022002000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 515, 522, 529, 572, 916, 1202, 1210, 1601]) (by decide +kernel)

theorem c24357_0 : P.sumLeaves 24 24941568 1024 = 4733090 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24357) (lo := 0) (len := 1024) (W := 4733090) check rows elimOK (by decide) (by decide) cover24357 (by decide)
  decide +kernel

theorem h24357 : P.leaf 34 24357 = 4733090 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 4733090)]) (.cons c24357_0 (.nil)) (by decide) (by decide))

theorem cover24359 : P.CoversSplit 24 10 24359 0xfffffffffafaa0a0fffffffffafaa0a0fffffffffafaa0a0fffffffffafaa0a0cccccccc88888080cc00cc0088008000cccccccc88888080cc00cc0088008000fffffffffafaa0a00000000000000000fffffffffafaa0a000330033003200200000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 517, 522, 1202, 1210, 1259, 1308, 1601]) (by decide +kernel)

theorem c24359_0 : P.sumLeaves 24 24943616 500 = 11463550 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24359) (lo := 0) (len := 500) (W := 11463550) check rows elimOK (by decide) (by decide) cover24359 (by decide)
  decide +kernel

theorem c24359_1 : P.sumLeaves 24 24944116 302 = 14716793 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24359) (lo := 500) (len := 302) (W := 14716793) check rows elimOK (by decide) (by decide) cover24359 (by decide)
  decide +kernel

theorem c24359_2 : P.sumLeaves 24 24944418 128 = 25295881 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24359) (lo := 802) (len := 128) (W := 25295881) check rows elimOK (by decide) (by decide) cover24359 (by decide)
  decide +kernel

theorem c24359_3 : P.sumLeaves 24 24944546 94 = 40515612 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24359) (lo := 930) (len := 94) (W := 40515612) check rows elimOK (by decide) (by decide) cover24359 (by decide)
  decide +kernel

theorem h24359 : P.leaf 34 24359 = 91991836 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(500, 11463550), (302, 14716793), (128, 25295881), (94, 40515612)]) (.cons c24359_0 (.cons c24359_1 (.cons c24359_2 (.cons c24359_3 (.nil))))) (by decide) (by decide))

theorem cover24364 : P.CoversSplit 24 10 24364 0x8800000088008000000000000000000088000000000000000000000000000000888800008880808088000000880080008888000000000000880000000000000088000000880080000000000000000000880000000000000000000000000000000000000000000000002200000022002000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 508, 515, 517, 522, 529, 572, 916, 1202, 1601]) (ps := [(2, [465], [473])]) (by decide +kernel)

theorem c24364_0 : P.sumLeaves 24 24948736 640 = 900167 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24364) (lo := 0) (len := 640) (W := 900167) check rows elimOK (by decide) (by decide) cover24364 (by decide)
  decide +kernel

theorem contract24364_1 : P.leaf 30 389834 = 0 := by
  exact leaf_contract_zero (ss := [(26, 1, 508), (19, 1, 578), (18, 1, 921), (29, 27, 1601), (27, 1, 572), (3, 0, 522), (2, 0, 417), (5, 0, 417), (4, 0, 404)]) (q := 409) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c24364_1 : P.sumLeaves 24 24949376 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 389834) rows (by decide) (by decide)).symm.trans contract24364_1

theorem c24364_2 : P.sumLeaves 24 24949440 320 = 2636849 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24364) (lo := 704) (len := 320) (W := 2636849) check rows elimOK (by decide) (by decide) cover24364 (by decide)
  decide +kernel

theorem h24364 : P.leaf 34 24364 = 3537016 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(640, 900167), (64, 0), (320, 2636849)]) (.cons c24364_0 (.cons c24364_1 (.cons c24364_2 (.nil)))) (by decide) (by decide))

theorem cover24365 : P.CoversSplit 24 10 24365 0xcc00cc00c80080000000000000000000cc00cc00c80080000000000000000000cc00cc00880080000000000000000000cc00cc00880080000000000000000000cc00cc00c80080000000000000000000cc00cc00c800800000000000000000000000000000000000003300330022002000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 515, 522, 529, 572, 916, 1202, 1210, 1601]) (by decide +kernel)

theorem c24365_0 : P.sumLeaves 24 24949760 1024 = 15081633 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 24365) (lo := 0) (len := 1024) (W := 15081633) check rows elimOK (by decide) (by decide) cover24365 (by decide)
  decide +kernel

theorem h24365 : P.leaf 34 24365 = 15081633 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 15081633)]) (.cons c24365_0 (.nil)) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(24063, 24), (24318, 8), (24319, 8), (24357, 12), (24359, 24), (24364, 48), (24365, 48)]

theorem segOK : checkSeg 16 perms 24063 24366 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 24063 24366 172 29734249192 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 29734249192)
    (SegSum.cons (w := 24) h24063 (SegSum.cons (w := 8) h24318 (SegSum.cons (w := 8) h24319 (SegSum.cons (w := 12) h24357 (SegSum.cons (w := 24) h24359 (SegSum.cons (w := 48) h24364 (SegSum.cons (w := 48) h24365 (show SegSum (P.leaf 34) [] 0 from rfl)))))))) (by decide)

end RACert.S4N1.C0.S90
