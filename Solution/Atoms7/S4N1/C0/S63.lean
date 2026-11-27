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

namespace RACert.S4N1.C0.S63

open RACert RACert.Problem

theorem cover8186 : P.CoversSplit 24 10 8186 0xffffffffffffaaaaffffffffffffaaaaffffffffffffaaaaffffffffffffaaaaccffccff88888888cc00cc0088008800ccffccff88888888cc00cc0088008800ffffffffffffaaaaffffffffffffaaaafffffffffafaaaaafffffffffafaaaaaccffccff88888888cc00cc0088008800cccccccc88888888cc00cc0088008800 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 916, 1209, 1210, 1217, 1258, 1601, 1609]) (by decide +kernel)

theorem c8186_0 : P.sumLeaves 24 8382464 284 = 3916560 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8186) (lo := 0) (len := 284) (W := 3916560) check rows elimOK (by decide) (by decide) cover8186 (by decide)
  decide +kernel

theorem c8186_1 : P.sumLeaves 24 8382748 116 = 8208577 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8186) (lo := 284) (len := 116) (W := 8208577) check rows elimOK (by decide) (by decide) cover8186 (by decide)
  decide +kernel

theorem c8186_2 : P.sumLeaves 24 8382864 104 = 17295223 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8186) (lo := 400) (len := 104) (W := 17295223) check rows elimOK (by decide) (by decide) cover8186 (by decide)
  decide +kernel

theorem c8186_3 : P.sumLeaves 24 8382968 265 = 24038033 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8186) (lo := 504) (len := 265) (W := 24038033) check rows elimOK (by decide) (by decide) cover8186 (by decide)
  decide +kernel

theorem c8186_4 : P.sumLeaves 24 8383233 111 = 21106227 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8186) (lo := 769) (len := 111) (W := 21106227) check rows elimOK (by decide) (by decide) cover8186 (by decide)
  decide +kernel

theorem c8186_5 : P.sumLeaves 24 8383344 112 = 46949063 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8186) (lo := 880) (len := 112) (W := 46949063) check rows elimOK (by decide) (by decide) cover8186 (by decide)
  decide +kernel

theorem c8186_6 : P.sumLeaves 24 8383456 32 = 37582644 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8186) (lo := 992) (len := 32) (W := 37582644) check rows elimOK (by decide) (by decide) cover8186 (by decide)
  decide +kernel

theorem h8186 : P.leaf 34 8186 = 159096327 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(284, 3916560), (116, 8208577), (104, 17295223), (265, 24038033), (111, 21106227), (112, 46949063), (32, 37582644)]) (.cons c8186_0 (.cons c8186_1 (.cons c8186_2 (.cons c8186_3 (.cons c8186_4 (.cons c8186_5 (.cons c8186_6 (.nil)))))))) (by decide) (by decide))

theorem cover8187 : P.CoversSplit 24 10 8187 0xffffffffffffaaaaffffffffffffaaaaffffffffffffaaaaffffffffffffaaaaccffccff88888888cc00cc0088008800ccffccff88888888cc00cc0088008800ffffffffffffaaaaffffffffffffaaaafffffffffafaaaaafffffffffafaaaaaccffccff88888888cc00cc0088008800cccccccc88888888cc00cc0088008800 :=
  coversSplit check rows (by decide) (by decide) (xs := [916, 1209, 1210, 1217, 1258, 1601, 1609]) (by decide +kernel)

theorem c8187_0 : P.sumLeaves 24 8383488 284 = 9353116 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8187) (lo := 0) (len := 284) (W := 9353116) check rows elimOK (by decide) (by decide) cover8187 (by decide)
  decide +kernel

theorem c8187_1 : P.sumLeaves 24 8383772 116 = 16338810 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8187) (lo := 284) (len := 116) (W := 16338810) check rows elimOK (by decide) (by decide) cover8187 (by decide)
  decide +kernel

theorem c8187_2 : P.sumLeaves 24 8383888 104 = 28503181 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8187) (lo := 400) (len := 104) (W := 28503181) check rows elimOK (by decide) (by decide) cover8187 (by decide)
  decide +kernel

theorem c8187_3 : P.sumLeaves 24 8383992 265 = 47619869 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8187) (lo := 504) (len := 265) (W := 47619869) check rows elimOK (by decide) (by decide) cover8187 (by decide)
  decide +kernel

theorem c8187_4 : P.sumLeaves 24 8384257 111 = 44785906 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8187) (lo := 769) (len := 111) (W := 44785906) check rows elimOK (by decide) (by decide) cover8187 (by decide)
  decide +kernel

theorem c8187_5 : P.sumLeaves 24 8384368 112 = 93435725 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8187) (lo := 880) (len := 112) (W := 93435725) check rows elimOK (by decide) (by decide) cover8187 (by decide)
  decide +kernel

theorem c8187_6 : P.sumLeaves 24 8384480 32 = 62576584 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8187) (lo := 992) (len := 32) (W := 62576584) check rows elimOK (by decide) (by decide) cover8187 (by decide)
  decide +kernel

theorem h8187 : P.leaf 34 8187 = 302613191 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(284, 9353116), (116, 16338810), (104, 28503181), (265, 47619869), (111, 44785906), (112, 93435725), (32, 62576584)]) (.cons c8187_0 (.cons c8187_1 (.cons c8187_2 (.cons c8187_3 (.cons c8187_4 (.cons c8187_5 (.cons c8187_6 (.nil)))))))) (by decide) (by decide))

theorem cover8188 : P.CoversSplit 24 10 8188 0xfffffffffafaaaaafffffffffafaaaaafffffffffafaaaaafffffffffafaaaaacccccccc88888888cccccccc88888888cccccccc88888888cccccccc88888888ff00ff00fa00aa00ff33ff33fa32aa22ff00ff00fa00aa00ff33ff33fa22aa220000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 916, 1210, 1601]) (ps := [(14, [1217], [916])]) (by decide +kernel)

theorem c8188_0 : P.sumLeaves 24 8384512 441 = 11895231 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8188) (lo := 0) (len := 441) (W := 11895231) check rows elimOK (by decide) (by decide) cover8188 (by decide)
  decide +kernel

theorem c8188_1 : P.sumLeaves 24 8384953 246 = 30526564 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8188) (lo := 441) (len := 246) (W := 30526564) check rows elimOK (by decide) (by decide) cover8188 (by decide)
  decide +kernel

theorem c8188_2 : P.sumLeaves 24 8385199 166 = 28908203 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8188) (lo := 687) (len := 166) (W := 28908203) check rows elimOK (by decide) (by decide) cover8188 (by decide)
  decide +kernel

theorem c8188_3 : P.sumLeaves 24 8385365 114 = 54471894 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8188) (lo := 853) (len := 114) (W := 54471894) check rows elimOK (by decide) (by decide) cover8188 (by decide)
  decide +kernel

theorem c8188_4 : P.sumLeaves 24 8385479 57 = 63621624 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8188) (lo := 967) (len := 57) (W := 63621624) check rows elimOK (by decide) (by decide) cover8188 (by decide)
  decide +kernel

theorem h8188 : P.leaf 34 8188 = 189423516 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(441, 11895231), (246, 30526564), (166, 28908203), (114, 54471894), (57, 63621624)]) (.cons c8188_0 (.cons c8188_1 (.cons c8188_2 (.cons c8188_3 (.cons c8188_4 (.nil)))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(8186, 48), (8187, 48), (8188, 48)]

theorem segOK : checkSeg 16 perms 8186 8189 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 8186 8189 144 31254385632 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 31254385632)
    (SegSum.cons (w := 48) h8186 (SegSum.cons (w := 48) h8187 (SegSum.cons (w := 48) h8188 (show SegSum (P.leaf 34) [] 0 from rfl)))) (by decide)

end RACert.S4N1.C0.S63
