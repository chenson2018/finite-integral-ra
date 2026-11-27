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

namespace RACert.S4N1.C0.S61

open RACert RACert.Problem

theorem cover8180 : P.CoversSplit 24 10 8180 0xfffffffffafaaaaafffffffffafaaaaafffffffffafaaaaafffffffffafaaaaacccccccc88888888cccccccc88888888cccccccc88888888cccccccc88888888ff00ff00fa00aa00ff33ff33fa32aa22ff00ff00fa00aa00ff33ff33fa22aa220000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 916, 1210, 1601]) (ps := [(14, [1217], [916])]) (by decide +kernel)

theorem c8180_0 : P.sumLeaves 24 8376320 441 = 2289482 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8180) (lo := 0) (len := 441) (W := 2289482) check rows elimOK (by decide) (by decide) cover8180 (by decide)
  decide +kernel

theorem c8180_1 : P.sumLeaves 24 8376761 246 = 5480988 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8180) (lo := 441) (len := 246) (W := 5480988) check rows elimOK (by decide) (by decide) cover8180 (by decide)
  decide +kernel

theorem c8180_2 : P.sumLeaves 24 8377007 166 = 5748822 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8180) (lo := 687) (len := 166) (W := 5748822) check rows elimOK (by decide) (by decide) cover8180 (by decide)
  decide +kernel

theorem c8180_3 : P.sumLeaves 24 8377173 114 = 9660124 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8180) (lo := 853) (len := 114) (W := 9660124) check rows elimOK (by decide) (by decide) cover8180 (by decide)
  decide +kernel

theorem c8180_4 : P.sumLeaves 24 8377287 57 = 10678224 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8180) (lo := 967) (len := 57) (W := 10678224) check rows elimOK (by decide) (by decide) cover8180 (by decide)
  decide +kernel

theorem h8180 : P.leaf 34 8180 = 33857640 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(441, 2289482), (246, 5480988), (166, 5748822), (114, 9660124), (57, 10678224)]) (.cons c8180_0 (.cons c8180_1 (.cons c8180_2 (.cons c8180_3 (.cons c8180_4 (.nil)))))) (by decide) (by decide))

theorem cover8181 : P.CoversSplit 24 10 8181 0xffffffffffffaaaaffffffffffffaaaaffffffffffffaaaaffffffffffffaaaaccffccff88888888cccccccc88888888ccffccff88888888cccccccc88888888ff00ff00ff00aa00ff33ff33ff33aa22ff00ff00fa00aa00ff33ff33fa22aa220000000000000000000000000000000000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 916, 1209, 1210, 1217, 1258, 1601]) (ps := [(14, [1217], [916])]) (by decide +kernel)

theorem c8181_0 : P.sumLeaves 24 8377344 436 = 9690897 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8181) (lo := 0) (len := 436) (W := 9690897) check rows elimOK (by decide) (by decide) cover8181 (by decide)
  decide +kernel

theorem c8181_1 : P.sumLeaves 24 8377780 215 = 28711818 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8181) (lo := 436) (len := 215) (W := 28711818) check rows elimOK (by decide) (by decide) cover8181 (by decide)
  decide +kernel

theorem c8181_2 : P.sumLeaves 24 8377995 167 = 22295025 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8181) (lo := 651) (len := 167) (W := 22295025) check rows elimOK (by decide) (by decide) cover8181 (by decide)
  decide +kernel

theorem c8181_3 : P.sumLeaves 24 8378162 112 = 54080917 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8181) (lo := 818) (len := 112) (W := 54080917) check rows elimOK (by decide) (by decide) cover8181 (by decide)
  decide +kernel

theorem c8181_4 : P.sumLeaves 24 8378274 94 = 95414406 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8181) (lo := 930) (len := 94) (W := 95414406) check rows elimOK (by decide) (by decide) cover8181 (by decide)
  decide +kernel

theorem h8181 : P.leaf 34 8181 = 210193063 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(436, 9690897), (215, 28711818), (167, 22295025), (112, 54080917), (94, 95414406)]) (.cons c8181_0 (.cons c8181_1 (.cons c8181_2 (.cons c8181_3 (.cons c8181_4 (.nil)))))) (by decide) (by decide))

theorem cover8182 : P.CoversSplit 24 10 8182 0xffffffffffffaaaaffffffffffffaaaaffffffffffffaaaaffffffffffffaaaaccffccff88888888cccccccc88888888ccffccff88888888cccccccc88888888ffffffffffffaaaaffffffffffffaaaafffffffffafaaaaafffffffffafaaaaaccffccff88888888cccccccc88888888cccccccc88888888cccccccc88888888 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 916, 1209, 1210, 1217, 1258, 1601, 1609]) (by decide +kernel)

theorem c8182_0 : P.sumLeaves 24 8378368 244 = 2737364 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8182) (lo := 0) (len := 244) (W := 2737364) check rows elimOK (by decide) (by decide) cover8182 (by decide)
  decide +kernel

theorem c8182_1 : P.sumLeaves 24 8378612 124 = 11881447 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8182) (lo := 244) (len := 124) (W := 11881447) check rows elimOK (by decide) (by decide) cover8182 (by decide)
  decide +kernel

theorem c8182_2 : P.sumLeaves 24 8378736 112 = 29945791 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8182) (lo := 368) (len := 112) (W := 29945791) check rows elimOK (by decide) (by decide) cover8182 (by decide)
  decide +kernel

theorem c8182_3 : P.sumLeaves 24 8378848 194 = 38148246 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8182) (lo := 480) (len := 194) (W := 38148246) check rows elimOK (by decide) (by decide) cover8182 (by decide)
  decide +kernel

theorem c8182_4 : P.sumLeaves 24 8379042 150 = 28752873 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8182) (lo := 674) (len := 150) (W := 28752873) check rows elimOK (by decide) (by decide) cover8182 (by decide)
  decide +kernel

theorem c8182_5 : P.sumLeaves 24 8379192 112 = 67192418 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8182) (lo := 824) (len := 112) (W := 67192418) check rows elimOK (by decide) (by decide) cover8182 (by decide)
  decide +kernel

theorem c8182_6 : P.sumLeaves 24 8379304 88 = 119075058 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 8182) (lo := 936) (len := 88) (W := 119075058) check rows elimOK (by decide) (by decide) cover8182 (by decide)
  decide +kernel

theorem h8182 : P.leaf 34 8182 = 297733197 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(244, 2737364), (124, 11881447), (112, 29945791), (194, 38148246), (150, 28752873), (112, 67192418), (88, 119075058)]) (.cons c8182_0 (.cons c8182_1 (.cons c8182_2 (.cons c8182_3 (.cons c8182_4 (.cons c8182_5 (.cons c8182_6 (.nil)))))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(8180, 48), (8181, 48), (8182, 48)]

theorem segOK : checkSeg 16 perms 8180 8183 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 8180 8183 144 26005627200 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 26005627200)
    (SegSum.cons (w := 48) h8180 (SegSum.cons (w := 48) h8181 (SegSum.cons (w := 48) h8182 (show SegSum (P.leaf 34) [] 0 from rfl)))) (by decide)

end RACert.S4N1.C0.S61
