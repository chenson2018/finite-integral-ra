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

namespace RACert.S4N1.C0.S40

open RACert RACert.Problem

theorem cover18254 : P.CoversSplit 24 10 18254 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a000000000a0a0000000000000808080808000800000000000000000008080808000000000000000000000000080a080a080a080a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 515, 516, 522, 523, 572, 872, 916, 1202, 1251, 1259, 1601, 1609]) (ps := [(14, [965], [1266])]) (by decide +kernel)

theorem c18254_0 : P.sumLeaves 24 18692096 1024 = 3028816 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 18254) (lo := 0) (len := 1024) (W := 3028816) check rows elimOK (by decide) (by decide) cover18254 (by decide)
  decide +kernel

theorem h18254 : P.leaf 34 18254 = 3028816 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 3028816)]) (.cons c18254_0 (.nil)) (by decide) (by decide))

theorem h7032 : P.leaf 34 7032 = 3028816 :=
  orient4 (v := 18254) (by decide) (by decide +kernel) h18254

theorem cover18255 : P.CoversSplit 24 10 18255 0xfffffffff0f0a0a0fffffffff0f0a0a0ffffffff0000a0a0ffff000000000000cccccccc800080003300330020002000cccccccc00008000330000000000000088aa88aa80a080a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [515, 516, 522, 523, 572, 872, 916, 1202, 1210, 1217, 1251, 1259, 1308, 1601, 1609]) (ps := [(14, [965], [1266])]) (by decide +kernel)

theorem c18255_0 : P.sumLeaves 24 18693120 873 = 5048573 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 18255) (lo := 0) (len := 873) (W := 5048573) check rows elimOK (by decide) (by decide) cover18255 (by decide)
  decide +kernel

theorem c18255_1 : P.sumLeaves 24 18693993 136 = 10787909 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 18255) (lo := 873) (len := 136) (W := 10787909) check rows elimOK (by decide) (by decide) cover18255 (by decide)
  decide +kernel

theorem c18255_2 : P.sumLeaves 24 18694129 15 = 4062860 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 18255) (lo := 1009) (len := 15) (W := 4062860) check rows elimOK (by decide) (by decide) cover18255 (by decide)
  decide +kernel

theorem h18255 : P.leaf 34 18255 = 19899342 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(873, 5048573), (136, 10787909), (15, 4062860)]) (.cons c18255_0 (.cons c18255_1 (.cons c18255_2 (.nil)))) (by decide) (by decide))

theorem h7033 : P.leaf 34 7033 = 19899342 :=
  orient4 (v := 18255) (by decide) (by decide +kernel) h18255

theorem cover51915 : P.CoversSplit 24 10 51915 0xfffffffffa000000fffffffffa0000008888cccc000000008888cccc00000000ffccffccfa00000033003300320000008888cccc000000000000000000000000888888888800000088aa88aa88000000888888880000000088888899000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 516, 522, 536, 573, 859, 879, 915, 916, 1202, 1601]) (by decide +kernel)

theorem c51915_0 : P.sumLeaves 24 53160960 803 = 4304902 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 51915) (lo := 0) (len := 803) (W := 4304902) check rows elimOK (by decide) (by decide) cover51915 (by decide)
  decide +kernel

theorem c51915_1 : P.sumLeaves 24 53161763 218 = 10437400 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 51915) (lo := 803) (len := 218) (W := 10437400) check rows elimOK (by decide) (by decide) cover51915 (by decide)
  decide +kernel

theorem c51915_2 : P.sumLeaves 24 53161981 3 = 747800 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 51915) (lo := 1021) (len := 3) (W := 747800) check rows elimOK (by decide) (by decide) cover51915 (by decide)
  decide +kernel

theorem h51915 : P.leaf 34 51915 = 15490102 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(803, 4304902), (218, 10437400), (3, 747800)]) (.cons c51915_0 (.cons c51915_1 (.cons c51915_2 (.nil)))) (by decide) (by decide))

theorem h7034 : P.leaf 34 7034 = 15490102 :=
  orient25 (v := 51915) (by decide) (by decide +kernel) h51915

theorem cover18271 : P.CoversSplit 24 10 18271 0xfffffffff0f0a0a0fffffffff0f0a0a0ffffffff0000a0a0ffffffff0000a0a0cccccccc800080003300330020002000cccccccc000080003300330000002000fffffffff0f0a0a0ffff0000f0f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [516, 523, 572, 872, 1202, 1210, 1217, 1259, 1264, 1308, 1601, 1609]) (ps := [(14, [965], [1266, 1609])]) (by decide +kernel)

theorem c18271_0 : P.sumLeaves 24 18709504 680 = 5312864 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 18271) (lo := 0) (len := 680) (W := 5312864) check rows elimOK (by decide) (by decide) cover18271 (by decide)
  decide +kernel

theorem c18271_1 : P.sumLeaves 24 18710184 214 = 14683243 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 18271) (lo := 680) (len := 214) (W := 14683243) check rows elimOK (by decide) (by decide) cover18271 (by decide)
  decide +kernel

theorem c18271_2 : P.sumLeaves 24 18710398 130 = 33177388 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 18271) (lo := 894) (len := 130) (W := 33177388) check rows elimOK (by decide) (by decide) cover18271 (by decide)
  decide +kernel

theorem h18271 : P.leaf 34 18271 = 53173495 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(680, 5312864), (214, 14683243), (130, 33177388)]) (.cons c18271_0 (.cons c18271_1 (.cons c18271_2 (.nil)))) (by decide) (by decide))

theorem h7035 : P.leaf 34 7035 = 53173495 :=
  orient4 (v := 18271) (by decide) (by decide +kernel) h18271

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

def seg : List (ℕ × ℕ) := [(7032, 48), (7033, 48), (7034, 48), (7035, 48), (7036, 48), (7037, 48), (7038, 48)]

theorem segOK : checkSeg 16 perms 7032 7039 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 7032 7039 336 12656449008 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 12656449008)
    (SegSum.cons (w := 48) h7032 (SegSum.cons (w := 48) h7033 (SegSum.cons (w := 48) h7034 (SegSum.cons (w := 48) h7035 (SegSum.cons (w := 48) h7036 (SegSum.cons (w := 48) h7037 (SegSum.cons (w := 48) h7038 (show SegSum (P.leaf 34) [] 0 from rfl)))))))) (by decide)

end RACert.S4N1.C0.S40
