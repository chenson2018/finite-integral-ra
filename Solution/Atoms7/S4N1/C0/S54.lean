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

namespace RACert.S4N1.C0.S54

open RACert RACert.Problem

theorem cover44515 : P.CoversSplit 24 10 44515 0xfffffffffafaaaaaffff0000fafa0000ffff000000005050ffff000000000000cccccccc88888888cc00000088000000cccc000040404040cc00000040000000fffffffffafaaaaa0000000000000000ffff55550000505000330000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [466, 515, 522, 858, 865, 915, 1202, 1209, 1258, 1601]) (by decide +kernel)

theorem c44515_0 : P.sumLeaves 24 45583360 631 = 7468144 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 44515) (lo := 0) (len := 631) (W := 7468144) check rows elimOK (by decide) (by decide) cover44515 (by decide)
  decide +kernel

theorem c44515_1 : P.sumLeaves 24 45583991 326 = 16422259 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 44515) (lo := 631) (len := 326) (W := 16422259) check rows elimOK (by decide) (by decide) cover44515 (by decide)
  decide +kernel

theorem c44515_2 : P.sumLeaves 24 45584317 67 = 17214968 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 44515) (lo := 957) (len := 67) (W := 17214968) check rows elimOK (by decide) (by decide) cover44515 (by decide)
  decide +kernel

theorem h44515 : P.leaf 34 44515 = 41105371 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(631, 7468144), (326, 16422259), (67, 17214968)]) (.cons c44515_0 (.cons c44515_1 (.cons c44515_2 (.nil)))) (by decide) (by decide))

theorem h8184 : P.leaf 34 8184 = 41105371 :=
  orient32 (v := 44515) (by decide) (by decide +kernel) h44515

theorem cover20431 : P.CoversSplit 24 10 20431 0xfffffffff0f0a0a0fffffffff0f0a0a0fffffffff0f0a0a0fffffffff0f0a0a0cccccccc80008000ff00ff00a000a000cccccccc80008000ff00ff00a000a000fffffffff0f0a0a00000000000000000ffffffff0000000000ff00aa00000000000000000080008000cc008800800080000000000000000000cc008800000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [515, 522, 1202, 1210, 1259, 1308, 1601]) (ps := [(18, [1210], [1264])]) (by decide +kernel)

theorem contract20431_0 : P.leaf 30 326896 = 0 := by
  exact leaf_contract_zero (ss := [(3, 1, 536), (29, 0, 1259), (27, 1, 522), (30, 18, 1264), (14, 0, 1266), (8, 1, 923), (21, 0, 1266), (20, 1, 1272), (31, 1, 1308)]) (q := 1315) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c20431_0 : P.sumLeaves 24 20921344 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 326896) rows (by decide) (by decide)).symm.trans contract20431_0

theorem c20431_1 : P.sumLeaves 24 20921408 192 = 500913 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 20431) (lo := 64) (len := 192) (W := 500913) check rows elimOK (by decide) (by decide) cover20431 (by decide)
  decide +kernel

theorem contract20431_2 : P.leaf 30 326900 = 0 := by
  exact leaf_contract_zero (ss := [(3, 1, 536), (17, 0, 1259), (29, 0, 1259), (30, 18, 1264), (14, 0, 1266), (8, 1, 923), (21, 0, 1266), (20, 1, 1272), (31, 1, 1273)]) (q := 1315) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c20431_2 : P.sumLeaves 24 20921600 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 326900) rows (by decide) (by decide)).symm.trans contract20431_2

theorem contract20431_3 : P.leaf 30 326901 = 0 := by
  exact leaf_contract_zero (ss := [(3, 1, 536), (14, 0, 1266), (8, 1, 923), (21, 0, 1266), (20, 1, 1272), (31, 1, 1308)]) (q := 1315) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c20431_3 : P.sumLeaves 24 20921664 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 326901) rows (by decide) (by decide)).symm.trans contract20431_3

theorem c20431_4 : P.sumLeaves 24 20921728 314 = 19736616 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 20431) (lo := 384) (len := 314) (W := 19736616) check rows elimOK (by decide) (by decide) cover20431 (by decide)
  decide +kernel

theorem c20431_5 : P.sumLeaves 24 20922042 182 = 30379127 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 20431) (lo := 698) (len := 182) (W := 30379127) check rows elimOK (by decide) (by decide) cover20431 (by decide)
  decide +kernel

theorem c20431_6 : P.sumLeaves 24 20922224 136 = 63955084 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 20431) (lo := 880) (len := 136) (W := 63955084) check rows elimOK (by decide) (by decide) cover20431 (by decide)
  decide +kernel

theorem c20431_7 : P.sumLeaves 24 20922360 8 = 14030868 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 20431) (lo := 1016) (len := 8) (W := 14030868) check rows elimOK (by decide) (by decide) cover20431 (by decide)
  decide +kernel

theorem h20431 : P.leaf 34 20431 = 128602608 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(64, 0), (192, 500913), (64, 0), (64, 0), (314, 19736616), (182, 30379127), (136, 63955084), (8, 14030868)]) (.cons c20431_0 (.cons c20431_1 (.cons c20431_2 (.cons c20431_3 (.cons c20431_4 (.cons c20431_5 (.cons c20431_6 (.cons c20431_7 (.nil))))))))) (by decide) (by decide))

theorem h8185 : P.leaf 34 8185 = 128602608 :=
  orient4 (v := 20431) (by decide) (by decide +kernel) h20431

theorem cover20446 : P.CoversSplit 24 10 20446 0xfffffffff0f0a0a0fffffffff0f0a0a0aaaaafaf00000000aaaaafaf00000000cccccccc80008000ff00ff00a000a00088888c8c00000000aa00af0000000000fffffffff0f0a0a0fffffffff0f0a0a0aaaaafaf00000000aaaaafaf00000000cccccccc80008000ff00ff00a000a00088008c000000000088008c0000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 516, 915, 1202, 1210, 1259, 1601]) (ps := [(8, [1609], [516, 1266]), (14, [1609], [1266])]) (by decide +kernel)

theorem contract20446_0 : P.leaf 30 327136 = 0 := by
  exact leaf_contract_zero (ss := [(3, 1, 536), (18, 1, 867), (29, 1, 1259), (8, 0, 1266), (20, 1, 531), (21, 1, 537), (5, 1, 580), (11, 1, 923), (14, 1, 923)]) (q := 1266) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c20446_0 : P.sumLeaves 24 20936704 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 327136) rows (by decide) (by decide)).symm.trans contract20446_0

theorem contract20446_1 : P.leaf 30 327137 = 0 := by
  exact leaf_contract_zero (ss := [(3, 1, 536), (18, 1, 867), (8, 0, 1266), (20, 1, 531), (21, 1, 537), (5, 1, 580), (11, 1, 923), (14, 1, 923)]) (q := 1266) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c20446_1 : P.sumLeaves 24 20936768 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 327137) rows (by decide) (by decide)).symm.trans contract20446_1

theorem c20446_2 : P.sumLeaves 24 20936832 128 = 3505956 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 20446) (lo := 128) (len := 128) (W := 3505956) check rows elimOK (by decide) (by decide) cover20446 (by decide)
  decide +kernel

theorem contract20446_3 : P.leaf 30 327140 = 0 := by
  exact leaf_contract_zero (ss := [(8, 0, 1266), (20, 1, 531), (21, 1, 537), (11, 1, 923), (14, 1, 923)]) (q := 1266) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c20446_3 : P.sumLeaves 24 20936960 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 327140) rows (by decide) (by decide)).symm.trans contract20446_3

theorem contract20446_4 : P.leaf 30 327141 = 0 := by
  exact leaf_contract_zero (ss := [(8, 0, 1266), (20, 1, 531), (21, 1, 537), (11, 1, 923), (14, 1, 923)]) (q := 1266) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c20446_4 : P.sumLeaves 24 20937024 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 327141) rows (by decide) (by decide)).symm.trans contract20446_4

theorem c20446_5 : P.sumLeaves 24 20937088 189 = 30796699 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 20446) (lo := 384) (len := 189) (W := 30796699) check rows elimOK (by decide) (by decide) cover20446 (by decide)
  decide +kernel

theorem c20446_6 : P.sumLeaves 24 20937277 345 = 45982928 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 20446) (lo := 573) (len := 345) (W := 45982928) check rows elimOK (by decide) (by decide) cover20446 (by decide)
  decide +kernel

theorem c20446_7 : P.sumLeaves 24 20937622 106 = 78810744 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 20446) (lo := 918) (len := 106) (W := 78810744) check rows elimOK (by decide) (by decide) cover20446 (by decide)
  decide +kernel

theorem h20446 : P.leaf 34 20446 = 159096327 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(64, 0), (64, 0), (128, 3505956), (64, 0), (64, 0), (189, 30796699), (345, 45982928), (106, 78810744)]) (.cons c20446_0 (.cons c20446_1 (.cons c20446_2 (.cons c20446_3 (.cons c20446_4 (.cons c20446_5 (.cons c20446_6 (.cons c20446_7 (.nil))))))))) (by decide) (by decide))

theorem h8186 : P.leaf 34 8186 = 159096327 :=
  orient4 (v := 20446) (by decide) (by decide +kernel) h20446

theorem cover20447 : P.CoversSplit 24 10 20447 0xfffffffff0f0a0a0fffffffff0f0a0a0fffffffff0f0a0a0fffffffff0f0a0a0cccccccc80008000ff00ff00a000a000cccccccc80008000ff00ff00a000a000fffffffff0f0a0a0fffffffff0f0a0a0ffffffff00000000ffffffff00000000cccccccc80008000ff00ff00a000a000cc00cc0000000000cc00cc0000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [516, 915, 1202, 1210, 1259, 1308, 1601]) (ps := [(8, [1609], [1266]), (14, [1609], [1266])]) (by decide +kernel)

theorem contract20447_0 : P.leaf 30 327152 = 0 := by
  exact leaf_contract_zero (ss := [(3, 1, 536), (29, 1, 1259), (8, 0, 1266), (5, 1, 622), (11, 1, 923), (14, 1, 923)]) (q := 1266) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c20447_0 : P.sumLeaves 24 20937728 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 327152) rows (by decide) (by decide)).symm.trans contract20447_0

theorem contract20447_1 : P.leaf 30 327153 = 0 := by
  exact leaf_contract_zero (ss := [(3, 1, 536), (8, 0, 1266), (5, 1, 622), (11, 1, 923), (14, 1, 923)]) (q := 1266) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c20447_1 : P.sumLeaves 24 20937792 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 327153) rows (by decide) (by decide)).symm.trans contract20447_1

theorem c20447_2 : P.sumLeaves 24 20937856 128 = 8099640 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 20447) (lo := 128) (len := 128) (W := 8099640) check rows elimOK (by decide) (by decide) cover20447 (by decide)
  decide +kernel

theorem contract20447_3 : P.leaf 30 327156 = 0 := by
  exact leaf_contract_zero (ss := [(8, 0, 1266), (11, 1, 923), (14, 1, 923)]) (q := 1266) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c20447_3 : P.sumLeaves 24 20937984 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 327156) rows (by decide) (by decide)).symm.trans contract20447_3

theorem contract20447_4 : P.leaf 30 327157 = 0 := by
  exact leaf_contract_zero (ss := [(8, 0, 1266), (11, 1, 923), (14, 1, 923)]) (q := 1266) check rows (by decide) (by decide +kernel) (by decide +kernel)

theorem c20447_4 : P.sumLeaves 24 20938048 64 = 0 :=
  (leaf_eq_inner (k := 24) (d := 6) (H := 327157) rows (by decide) (by decide)).symm.trans contract20447_4

theorem c20447_5 : P.sumLeaves 24 20938112 172 = 52359715 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 20447) (lo := 384) (len := 172) (W := 52359715) check rows elimOK (by decide) (by decide) cover20447 (by decide)
  decide +kernel

theorem c20447_6 : P.sumLeaves 24 20938284 260 = 54815500 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 20447) (lo := 556) (len := 260) (W := 54815500) check rows elimOK (by decide) (by decide) cover20447 (by decide)
  decide +kernel

theorem c20447_7 : P.sumLeaves 24 20938544 136 = 88813970 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 20447) (lo := 816) (len := 136) (W := 88813970) check rows elimOK (by decide) (by decide) cover20447 (by decide)
  decide +kernel

theorem c20447_8 : P.sumLeaves 24 20938680 72 = 98524366 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 20447) (lo := 952) (len := 72) (W := 98524366) check rows elimOK (by decide) (by decide) cover20447 (by decide)
  decide +kernel

theorem h20447 : P.leaf 34 20447 = 302613191 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(64, 0), (64, 0), (128, 8099640), (64, 0), (64, 0), (172, 52359715), (260, 54815500), (136, 88813970), (72, 98524366)]) (.cons c20447_0 (.cons c20447_1 (.cons c20447_2 (.cons c20447_3 (.cons c20447_4 (.cons c20447_5 (.cons c20447_6 (.cons c20447_7 (.cons c20447_8 (.nil)))))))))) (by decide) (by decide))

theorem h8187 : P.leaf 34 8187 = 302613191 :=
  orient4 (v := 20447) (by decide) (by decide +kernel) h20447

theorem cover20462 : P.CoversSplit 24 10 20462 0xfffffffffafaaaaafffffffffafaaaaafffffffffafaaaaafffffffffafaaaaacccccccc88888888cccccccc88888888cccccccc88888888cccccccc88888888fffffffffafaaaaa0000000000000000fffffffffafaaaaa00330022003200220000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 515, 522, 1202, 1210, 1259, 1601]) (ps := [(18, [1210], [1264])]) (by decide +kernel)

theorem c20462_0 : P.sumLeaves 24 20953088 493 = 23281118 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 20462) (lo := 0) (len := 493) (W := 23281118) check rows elimOK (by decide) (by decide) cover20462 (by decide)
  decide +kernel

theorem c20462_1 : P.sumLeaves 24 20953581 234 = 23548976 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 20462) (lo := 493) (len := 234) (W := 23548976) check rows elimOK (by decide) (by decide) cover20462 (by decide)
  decide +kernel

theorem c20462_2 : P.sumLeaves 24 20953815 142 = 31019638 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 20462) (lo := 727) (len := 142) (W := 31019638) check rows elimOK (by decide) (by decide) cover20462 (by decide)
  decide +kernel

theorem c20462_3 : P.sumLeaves 24 20953957 120 = 64919508 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 20462) (lo := 869) (len := 120) (W := 64919508) check rows elimOK (by decide) (by decide) cover20462 (by decide)
  decide +kernel

theorem c20462_4 : P.sumLeaves 24 20954077 35 = 46654276 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 20462) (lo := 989) (len := 35) (W := 46654276) check rows elimOK (by decide) (by decide) cover20462 (by decide)
  decide +kernel

theorem h20462 : P.leaf 34 20462 = 189423516 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(493, 23281118), (234, 23548976), (142, 31019638), (120, 64919508), (35, 46654276)]) (.cons c20462_0 (.cons c20462_1 (.cons c20462_2 (.cons c20462_3 (.cons c20462_4 (.nil)))))) (by decide) (by decide))

theorem h8188 : P.leaf 34 8188 = 189423516 :=
  orient4 (v := 20462) (by decide) (by decide +kernel) h20462

def seg : List (ℕ × ℕ) := [(8184, 48), (8185, 48), (8186, 48), (8187, 48), (8188, 48)]

theorem segOK : checkSeg 16 perms 8184 8189 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 8184 8189 240 39400368624 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 39400368624)
    (SegSum.cons (w := 48) h8184 (SegSum.cons (w := 48) h8185 (SegSum.cons (w := 48) h8186 (SegSum.cons (w := 48) h8187 (SegSum.cons (w := 48) h8188 (show SegSum (P.leaf 34) [] 0 from rfl)))))) (by decide)

end RACert.S4N1.C0.S54
