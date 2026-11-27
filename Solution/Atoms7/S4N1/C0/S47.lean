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

namespace RACert.S4N1.C0.S47

open RACert RACert.Problem

theorem cover7136 : P.CoversSplit 24 10 7136 0x8888000000000000000000000000000080800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000088000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 515, 522, 523, 565, 859, 879, 916, 1202, 1210, 1259, 1264]) (by decide +kernel)

noncomputable def f7136 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (7307264 + i)

theorem c7136_0 : rowSum f7136 0 1024 = 43212 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 7136) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover7136 (by decide)
  decide +kernel

theorem sum7136 : rowSum f7136 0 1024 = 43212 :=
  c7136_0

theorem h7136 : P.leaf 34 7136 = 43212 :=
  leaf_weighted (k := 24) (d := 10) (H := 7136) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 7136) (by decide) (by decide +kernel)) sum7136

theorem cover7137 : P.CoversSplit 24 10 7137 0xcccc0000000000000000000000000000cccc00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000cc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 515, 522, 523, 859, 879, 916, 1202, 1209, 1210, 1251, 1259]) (by decide +kernel)

theorem c7137_0 : P.sumLeaves 24 7308288 1024 = 1131966 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7137) (lo := 0) (len := 1024) (W := 1131966) check rows elimOK (by decide) (by decide) cover7137 (by decide)
  decide +kernel

theorem h7137 : P.leaf 34 7137 = 1131966 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1131966)]) (.cons c7137_0 (.nil)) (by decide) (by decide))

theorem cover7139 : P.CoversSplit 24 10 7139 0xffff0000000000000000000000000000ffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffff0000000000000000000000000000ffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 522, 523, 859, 916, 1202, 1209, 1210, 1251, 1259, 1264]) (by decide +kernel)

noncomputable def f7139 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (7310336 + i)

theorem c7139_0 : rowSum f7139 0 1024 = 16003415 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 7139) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover7139 (by decide)
  decide +kernel

theorem sum7139 : rowSum f7139 0 1024 = 16003415 :=
  c7139_0

theorem h7139 : P.leaf 34 7139 = 16003415 :=
  leaf_weighted (k := 24) (d := 10) (H := 7139) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 7139) (by decide) (by decide +kernel)) sum7139

theorem cover7140 : P.CoversSplit 24 10 7140 0x8888000000000000000000000000000080800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000088000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 515, 522, 524, 566, 859, 879, 916, 1202, 1210, 1259, 1264]) (by decide +kernel)

theorem c7140_0 : P.sumLeaves 24 7311360 1024 = 648280 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7140) (lo := 0) (len := 1024) (W := 648280) check rows elimOK (by decide) (by decide) cover7140 (by decide)
  decide +kernel

theorem h7140 : P.leaf 34 7140 = 648280 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 648280)]) (.cons c7140_0 (.nil)) (by decide) (by decide))

theorem cover7141 : P.CoversSplit 24 10 7141 0xcccc0000000000000000000000000000cccc00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000cc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 515, 522, 524, 566, 859, 879, 916, 1202, 1209, 1210, 1251, 1259]) (by decide +kernel)

theorem c7141_0 : P.sumLeaves 24 7312384 1024 = 6840542 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7141) (lo := 0) (len := 1024) (W := 6840542) check rows elimOK (by decide) (by decide) cover7141 (by decide)
  decide +kernel

theorem h7141 : P.leaf 34 7141 = 6840542 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 6840542)]) (.cons c7141_0 (.nil)) (by decide) (by decide))

theorem cover7142 : P.CoversSplit 24 10 7142 0xaaaa0000000000000000000000000000a0a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000aaaa0000000000000000000000000000a0a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 515, 522, 524, 566, 859, 879, 1210, 1259, 1264]) (by decide +kernel)

theorem c7142_0 : P.sumLeaves 24 7313408 1024 = 7891498 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7142) (lo := 0) (len := 1024) (W := 7891498) check rows elimOK (by decide) (by decide) cover7142 (by decide)
  decide +kernel

theorem h7142 : P.leaf 34 7142 = 7891498 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 7891498)]) (.cons c7142_0 (.nil)) (by decide) (by decide))

theorem cover7143 : P.CoversSplit 24 10 7143 0xffff0000000000000000000000000000ffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffff0000000000000000000000000000ffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 522, 524, 566, 859, 1202, 1209, 1210, 1251, 1259, 1264]) (by decide +kernel)

theorem c7143_0 : P.sumLeaves 24 7314432 1024 = 34305216 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7143) (lo := 0) (len := 1024) (W := 34305216) check rows elimOK (by decide) (by decide) cover7143 (by decide)
  decide +kernel

theorem h7143 : P.leaf 34 7143 = 34305216 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 34305216)]) (.cons c7143_0 (.nil)) (by decide) (by decide))

theorem cover7148 : P.CoversSplit 24 10 7148 0x8888000000000000000000000000000080800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000088000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 515, 522, 859, 879, 916, 1202, 1210, 1259, 1264]) (by decide +kernel)

noncomputable def f7148 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (7319552 + i)

theorem c7148_0 : rowSum f7148 0 1024 = 3685160 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 7148) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover7148 (by decide)
  decide +kernel

theorem sum7148 : rowSum f7148 0 1024 = 3685160 :=
  c7148_0

theorem h7148 : P.leaf 34 7148 = 3685160 :=
  leaf_weighted (k := 24) (d := 10) (H := 7148) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 7148) (by decide) (by decide +kernel)) sum7148

theorem cover7149 : P.CoversSplit 24 10 7149 0xcccc0000000000000000000000000000cccc00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000cc000000000000000000000000000000cc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 515, 522, 879, 916, 1202, 1209, 1210, 1251, 1259]) (by decide +kernel)

theorem c7149_0 : P.sumLeaves 24 7320576 1024 = 22498770 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7149) (lo := 0) (len := 1024) (W := 22498770) check rows elimOK (by decide) (by decide) cover7149 (by decide)
  decide +kernel

theorem h7149 : P.leaf 34 7149 = 22498770 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 22498770)]) (.cons c7149_0 (.nil)) (by decide) (by decide))

theorem cover7151 : P.CoversSplit 24 10 7151 0xffff0000000000000000000000000000ffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffff0000000000000000000000000000ffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 522, 1202, 1209, 1210, 1251, 1259, 1264]) (by decide +kernel)

noncomputable def f7151 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (7322624 + i)

theorem c7151_0 : rowSum f7151 0 1024 = 88616980 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 7151) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover7151 (by decide)
  decide +kernel

theorem sum7151 : rowSum f7151 0 1024 = 88616980 :=
  c7151_0

theorem h7151 : P.leaf 34 7151 = 88616980 :=
  leaf_weighted (k := 24) (d := 10) (H := 7151) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 7151) (by decide) (by decide +kernel)) sum7151

theorem cover7152 : P.CoversSplit 24 10 7152 0xfac8fac8aa88a080fac8fac8aa88a080f0c0f0c000000000f0c0f0c000000000c8c8c8c888888080c800c80088008000c0c0c0c000000000c000c00000000000fa00fa00aa00a000fa00fa00aa00a000f000fa0000000000f0c0fac8000000000000000000000000000000000000000000000000000000000000000000008888 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 859, 879, 916, 1202, 1259, 1601]) (ps := [(14, [880, 923], [859, 916])]) (by decide +kernel)

noncomputable def f7152 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (7323648 + i)

theorem c7152_0 : rowSum f7152 0 1020 = 638746 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 7152) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover7152 (by decide)
  decide +kernel

theorem c7152_1 : rowSum f7152 1020 4 = 51384 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 7152) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover7152 (by decide)
  decide +kernel

theorem sum7152 : rowSum f7152 0 1024 = 690130 :=
  rowSum_append (F := f7152) (lo := 0) (n := 1020) (m := 4) (A := 638746) (B := 51384) c7152_0 (c7152_1)

theorem h7152 : P.leaf 34 7152 = 690130 :=
  leaf_weighted (k := 24) (d := 10) (H := 7152) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 7152) (by decide) (by decide +kernel)) sum7152

theorem cover7153 : P.CoversSplit 24 10 7153 0xffffffffafafa0a0ffccffccaf8ca080ffffffff00000000ffccffcc00000000ccffccff88888080cc00cc0088008000ccffccff00000000cc00cc0000000000ff00ff00af00a000ff00ff00af00a000ff00ff0000000000ffccffcc00000000000000000000000000cc00cc00880080000000000000000000cc00cc00000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 859, 879, 916, 1202, 1209, 1258, 1259, 1601]) (ps := [(12, [478], [916]), (14, [923], [916])]) (by decide +kernel)

theorem contract7153_0 : P.leaf 30 114448 = 15232 := by
  exact leaf_contract_factors (k := 30) (b := 18) (H := 114448) (ss := [(2, 1, 475), (6, 1, 478), (12, 1, 478), (31, 1, 879), (29, 0, 916), (27, 1, 473), (18, 11, 921), (11, 1, 965), (25, 1, 915), (14, 1, 965), (8, 1, 1609), (17, 1, 880)]) (ids := [1, 2, 3, 5, 7, 8, 11, 13, 14, 17, 18, 19, 20, 22, 24, 26, 28, 21]) (cs := [1, 2, 3, 4, 1, 5, 1, 6, 7, 1, 1, 8, 1, 9, 10, 1, 1, 11, 12, 13, 14, 19, 15, 1, 16, 1, 17, 0, 18, 1]) (bs := [17, 1]) (W := 15232) check rows (by decide) (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel)

theorem c7153_0 : P.sumLeaves 24 7324672 64 = 15232 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 114448) rows (by decide) (by decide)).symm.trans contract7153_0

theorem c7153_1 : P.sumLeaves 24 7324736 445 = 2520186 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7153) (lo := 64) (len := 445) (W := 2520186) check rows elimOK (by decide) (by decide) cover7153 (by decide)
  decide +kernel

theorem c7153_2 : P.sumLeaves 24 7325181 319 = 3074274 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7153) (lo := 509) (len := 319) (W := 3074274) check rows elimOK (by decide) (by decide) cover7153 (by decide)
  decide +kernel

theorem c7153_3 : P.sumLeaves 24 7325500 172 = 6306101 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7153) (lo := 828) (len := 172) (W := 6306101) check rows elimOK (by decide) (by decide) cover7153 (by decide)
  decide +kernel

theorem c7153_4 : P.sumLeaves 24 7325672 24 = 4238290 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7153) (lo := 1000) (len := 24) (W := 4238290) check rows elimOK (by decide) (by decide) cover7153 (by decide)
  decide +kernel

theorem h7153 : P.leaf 34 7153 = 16154083 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(64, 15232), (445, 2520186), (319, 3074274), (172, 6306101), (24, 4238290)]) (.cons c7153_0 (.cons c7153_1 (.cons c7153_2 (.cons c7153_3 (.cons c7153_4 (.nil)))))) (by decide) (by decide))

theorem cover7155 : P.CoversSplit 24 10 7155 0xffffffffafafa0a0ffffffffafafa0a0ffffffffafafa0a0ffffffffafafa0a0ccffccff88888080cc00cc0088008000ccffccff88888080cc00cc0088008000ffffffffafafa0a0ffffffffafafa0a0ffffffffaaaaa0a0ffffffffaaaaa0a0ccffccff88888080cc00cc0088008000cccccccc88888080cc00cc0088008000 :=
  coversSplit check rows (by decide) (by decide) (xs := [859, 916, 1202, 1209, 1217, 1258, 1259, 1601, 1609]) (by decide +kernel)

noncomputable def f7155 (i : ℕ) := rowWeight keep1 twice1 i * P.leaf 24 (7326720 + i)

theorem c7155_0 : rowSum f7155 0 319 = 7123528 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 7155) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover7155 (by decide)
  decide +kernel

theorem c7155_1 : rowSum f7155 319 182 = 22043428 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 7155) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover7155 (by decide)
  decide +kernel

theorem c7155_2 : rowSum f7155 501 523 = 55097507 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 7155) (keep := keep1) (twice := twice1) check rows elimOK (by decide) (by decide) cover7155 (by decide)
  decide +kernel

theorem sum7155 : rowSum f7155 0 1024 = 84264463 :=
  rowSum_append (F := f7155) (lo := 0) (n := 319) (m := 705) (A := 7123528) (B := 77140935) c7155_0 (rowSum_append (F := f7155) (lo := 319) (n := 182) (m := 523) (A := 22043428) (B := 55097507) c7155_1 (c7155_2))

theorem h7155 : P.leaf 34 7155 = 84264463 :=
  leaf_weighted (k := 24) (d := 10) (H := 7155) (keep := keep1) (twice := twice1) rows (by decide) (by decide) bal1 (invRow1 (H := 7155) (by decide) (by decide +kernel)) sum7155

theorem cover7156 : P.CoversSplit 24 10 7156 0xffffffffaaaaa0a0ffffffffaaaaa0a0f0f0f0f000000000f0f0f0f000000000cccccccc88888080cccccccc88888080c0c0c0c000000000c0c0c0c000000000ff00ff00aa00a000ff33ff33aa22a020f000ff0000000000f030ff33000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 859, 879, 916, 1202, 1259, 1601]) (ps := [(14, [880], [859])]) (by decide +kernel)

theorem c7156_0 : P.sumLeaves 24 7327744 623 = 1626076 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7156) (lo := 0) (len := 623) (W := 1626076) check rows elimOK (by decide) (by decide) cover7156 (by decide)
  decide +kernel

theorem c7156_1 : P.sumLeaves 24 7328367 308 = 2470900 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7156) (lo := 623) (len := 308) (W := 2470900) check rows elimOK (by decide) (by decide) cover7156 (by decide)
  decide +kernel

theorem c7156_2 : P.sumLeaves 24 7328675 93 = 5398886 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7156) (lo := 931) (len := 93) (W := 5398886) check rows elimOK (by decide) (by decide) cover7156 (by decide)
  decide +kernel

theorem h7156 : P.leaf 34 7156 = 9495862 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(623, 1626076), (308, 2470900), (93, 5398886)]) (.cons c7156_0 (.cons c7156_1 (.cons c7156_2 (.nil)))) (by decide) (by decide))

theorem cover7157 : P.CoversSplit 24 10 7157 0xffffffffafafa0a0ffffffffafafa0a0ffffffff00000000ffffffff00000000ccffccff88888080cccccccc88888080ccffccff00000000cccccccc00000000ff00ff00af00a000ff33ff33af23a020ff00ff0000000000ff33ff33000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 859, 879, 916, 1202, 1209, 1258, 1259, 1601]) (by decide +kernel)

theorem c7157_0 : P.sumLeaves 24 7328768 508 = 6758494 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7157) (lo := 0) (len := 508) (W := 6758494) check rows elimOK (by decide) (by decide) cover7157 (by decide)
  decide +kernel

theorem c7157_1 : P.sumLeaves 24 7329276 292 = 9476893 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7157) (lo := 508) (len := 292) (W := 9476893) check rows elimOK (by decide) (by decide) cover7157 (by decide)
  decide +kernel

theorem c7157_2 : P.sumLeaves 24 7329568 144 = 10664189 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7157) (lo := 800) (len := 144) (W := 10664189) check rows elimOK (by decide) (by decide) cover7157 (by decide)
  decide +kernel

theorem c7157_3 : P.sumLeaves 24 7329712 80 = 30186694 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 7157) (lo := 944) (len := 80) (W := 30186694) check rows elimOK (by decide) (by decide) cover7157 (by decide)
  decide +kernel

theorem h7157 : P.leaf 34 7157 = 57086270 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(508, 6758494), (292, 9476893), (144, 10664189), (80, 30186694)]) (.cons c7157_0 (.cons c7157_1 (.cons c7157_2 (.cons c7157_3 (.nil))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(7136, 24), (7137, 48), (7139, 24), (7140, 48), (7141, 48), (7142, 48), (7143, 48), (7148, 24), (7149, 48), (7151, 24), (7152, 24), (7153, 48), (7155, 24), (7156, 48), (7157, 48)]

theorem segOK : checkSeg 16 perms 7136 7158 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 7136 7158 576 12129800016 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 12129800016)
    (SegSum.cons (w := 24) h7136 (SegSum.cons (w := 48) h7137 (SegSum.cons (w := 24) h7139 (SegSum.cons (w := 48) h7140 (SegSum.cons (w := 48) h7141 (SegSum.cons (w := 48) h7142 (SegSum.cons (w := 48) h7143 (SegSum.cons (w := 24) h7148 (SegSum.cons (w := 48) h7149 (SegSum.cons (w := 24) h7151 (SegSum.cons (w := 24) h7152 (SegSum.cons (w := 48) h7153 (SegSum.cons (w := 24) h7155 (SegSum.cons (w := 48) h7156 (SegSum.cons (w := 48) h7157 (show SegSum (P.leaf 34) [] 0 from rfl)))))))))))))))) (by decide)

end RACert.S4N1.C0.S47
