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

namespace RACert.S4N1.C0.S62

open RACert RACert.Problem

theorem cover8183 : P.CoversSplit 24 10 8183 0xffffffffffffaaaaffffffffffffaaaaffffffffffffaaaaffffffffffffaaaaccffccff88888888cccccccc88888888ccffccff88888888cccccccc88888888ffffffffffffaaaaffffffffffffaaaafffffffffafaaaaafffffffffafaaaaaccffccff88888888cccccccc88888888cccccccc88888888cccccccc88888888 :=
  coversSplit check rows (by decide) (by decide) (xs := [916, 1209, 1210, 1217, 1258, 1601, 1609]) (by decide +kernel)

theorem c8183_0 : P.sumLeaves 24 8379392 244 = 5588018 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8183) (lo := 0) (len := 244) (W := 5588018) check rows elimOK (by decide) (by decide) cover8183 (by decide)
  decide +kernel

theorem c8183_1 : P.sumLeaves 24 8379636 124 = 23946801 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8183) (lo := 244) (len := 124) (W := 23946801) check rows elimOK (by decide) (by decide) cover8183 (by decide)
  decide +kernel

theorem c8183_2 : P.sumLeaves 24 8379760 112 = 57614383 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8183) (lo := 368) (len := 112) (W := 57614383) check rows elimOK (by decide) (by decide) cover8183 (by decide)
  decide +kernel

theorem c8183_3 : P.sumLeaves 24 8379872 194 = 69488403 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8183) (lo := 480) (len := 194) (W := 69488403) check rows elimOK (by decide) (by decide) cover8183 (by decide)
  decide +kernel

theorem c8183_4 : P.sumLeaves 24 8380066 150 = 60781437 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8183) (lo := 674) (len := 150) (W := 60781437) check rows elimOK (by decide) (by decide) cover8183 (by decide)
  decide +kernel

theorem c8183_5 : P.sumLeaves 24 8380216 112 = 128270815 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8183) (lo := 824) (len := 112) (W := 128270815) check rows elimOK (by decide) (by decide) cover8183 (by decide)
  decide +kernel

theorem c8183_6 : P.sumLeaves 24 8380328 88 = 199525362 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8183) (lo := 936) (len := 88) (W := 199525362) check rows elimOK (by decide) (by decide) cover8183 (by decide)
  decide +kernel

theorem h8183 : P.leaf 34 8183 = 545215219 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(244, 5588018), (124, 23946801), (112, 57614383), (194, 69488403), (150, 60781437), (112, 128270815), (88, 199525362)]) (.cons c8183_0 (.cons c8183_1 (.cons c8183_2 (.cons c8183_3 (.cons c8183_4 (.cons c8183_5 (.cons c8183_6 (.nil)))))))) (by decide) (by decide))

theorem cover8184 : P.CoversSplit 24 10 8184 0xfffffffffafaaaaafffffffffafaaaaafffffffffafaaaaafffffffffafaaaaacccccccc88888888cc00cc0088008800cccccccc88888888cc00cc0088008800ff00ff00fa00aa00ff00ff00fa00aa00ff00ff00fa00aa00fffffffffaaaaaaa0000000000000000cccc00cc888800880000000000000000cccc00cc88888888 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 916, 1210, 1601]) (ps := [(12, [909], [916]), (14, [923, 1217], [916])]) (by decide +kernel)

theorem c8184_0 : P.sumLeaves 24 8380416 350 = 843030 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8184) (lo := 0) (len := 350) (W := 843030) check rows elimOK (by decide) (by decide) cover8184 (by decide)
  decide +kernel

theorem c8184_1 : P.sumLeaves 24 8380766 272 = 5709957 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8184) (lo := 350) (len := 272) (W := 5709957) check rows elimOK (by decide) (by decide) cover8184 (by decide)
  decide +kernel

theorem c8184_2 : P.sumLeaves 24 8381038 208 = 7320166 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8184) (lo := 622) (len := 208) (W := 7320166) check rows elimOK (by decide) (by decide) cover8184 (by decide)
  decide +kernel

theorem c8184_3 : P.sumLeaves 24 8381246 120 = 10030096 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8184) (lo := 830) (len := 120) (W := 10030096) check rows elimOK (by decide) (by decide) cover8184 (by decide)
  decide +kernel

theorem c8184_4 : P.sumLeaves 24 8381366 74 = 17202122 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8184) (lo := 950) (len := 74) (W := 17202122) check rows elimOK (by decide) (by decide) cover8184 (by decide)
  decide +kernel

theorem h8184 : P.leaf 34 8184 = 41105371 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(350, 843030), (272, 5709957), (208, 7320166), (120, 10030096), (74, 17202122)]) (.cons c8184_0 (.cons c8184_1 (.cons c8184_2 (.cons c8184_3 (.cons c8184_4 (.nil)))))) (by decide) (by decide))

theorem cover8185 : P.CoversSplit 24 10 8185 0xffffffffffffaaaaffffffffffffaaaaffffffffffffaaaaffffffffffffaaaaccffccff88888888cc00cc0088008800ccffccff88888888cc00cc0088008800ff00ff00ff00aa00ff00ff00ff00aa00ff00ff00fa00aa00fffffffffaaaaaaa0000000000000000cccc00cc888800880000000000000000cccc00cc88880088 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 916, 1209, 1210, 1217, 1258, 1601]) (ps := [(12, [867], [916]), (14, [923, 1217], [916])]) (by decide +kernel)

theorem c8185_0 : P.sumLeaves 24 8381440 360 = 2289057 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8185) (lo := 0) (len := 360) (W := 2289057) check rows elimOK (by decide) (by decide) cover8185 (by decide)
  decide +kernel

theorem c8185_1 : P.sumLeaves 24 8381800 252 = 11935040 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8185) (lo := 360) (len := 252) (W := 11935040) check rows elimOK (by decide) (by decide) cover8185 (by decide)
  decide +kernel

theorem c8185_2 : P.sumLeaves 24 8382052 196 = 20250177 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8185) (lo := 612) (len := 196) (W := 20250177) check rows elimOK (by decide) (by decide) cover8185 (by decide)
  decide +kernel

theorem c8185_3 : P.sumLeaves 24 8382248 112 = 29004929 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8185) (lo := 808) (len := 112) (W := 29004929) check rows elimOK (by decide) (by decide) cover8185 (by decide)
  decide +kernel

theorem c8185_4 : P.sumLeaves 24 8382360 104 = 65123405 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8185) (lo := 920) (len := 104) (W := 65123405) check rows elimOK (by decide) (by decide) cover8185 (by decide)
  decide +kernel

theorem h8185 : P.leaf 34 8185 = 128602608 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(360, 2289057), (252, 11935040), (196, 20250177), (112, 29004929), (104, 65123405)]) (.cons c8185_0 (.cons c8185_1 (.cons c8185_2 (.cons c8185_3 (.cons c8185_4 (.nil)))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(8183, 48), (8184, 48), (8185, 48)]

theorem segOK : checkSeg 16 perms 8183 8186 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 8183 8186 144 34316313504 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 34316313504)
    (SegSum.cons (w := 48) h8183 (SegSum.cons (w := 48) h8184 (SegSum.cons (w := 48) h8185 (show SegSum (P.leaf 34) [] 0 from rfl)))) (by decide)

end RACert.S4N1.C0.S62
