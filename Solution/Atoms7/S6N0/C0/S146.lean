/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Atoms7.S6N0.C0.Defs

/-! Generated certificate for the identity on six symmetric diversity atoms. -/

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option Elab.async false

@[expose] public section

namespace RACert.S6N0.C0.S146

open RACert RACert.Problem

theorem cover1048575 : P.CoversSplit 26 10 1048575 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff :=
  coversSplit check rows (by decide) (by decide) (xs := []) (by decide +kernel)

theorem c1048575_0 : P.sumLeaves 26 1073740800 96 = 1921987166 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1048575) (lo := 0) (len := 96) (W := 1921987166) check rows elimOK (by decide) (by decide) cover1048575 (by decide)
  decide +kernel

theorem c1048575_1 : P.sumLeaves 26 1073740896 96 = 2505244597 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1048575) (lo := 96) (len := 96) (W := 2505244597) check rows elimOK (by decide) (by decide) cover1048575 (by decide)
  decide +kernel

theorem c1048575_2 : P.sumLeaves 26 1073740992 96 = 2708092670 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1048575) (lo := 192) (len := 96) (W := 2708092670) check rows elimOK (by decide) (by decide) cover1048575 (by decide)
  decide +kernel

theorem c1048575_3 : P.sumLeaves 26 1073741088 96 = 2820669237 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1048575) (lo := 288) (len := 96) (W := 2820669237) check rows elimOK (by decide) (by decide) cover1048575 (by decide)
  decide +kernel

theorem c1048575_4 : P.sumLeaves 26 1073741184 96 = 3221457735 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1048575) (lo := 384) (len := 96) (W := 3221457735) check rows elimOK (by decide) (by decide) cover1048575 (by decide)
  decide +kernel

theorem c1048575_5 : P.sumLeaves 26 1073741280 96 = 2972119247 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1048575) (lo := 480) (len := 96) (W := 2972119247) check rows elimOK (by decide) (by decide) cover1048575 (by decide)
  decide +kernel

theorem c1048575_6 : P.sumLeaves 26 1073741376 96 = 2999335508 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1048575) (lo := 576) (len := 96) (W := 2999335508) check rows elimOK (by decide) (by decide) cover1048575 (by decide)
  decide +kernel

theorem c1048575_7 : P.sumLeaves 26 1073741472 96 = 3383015598 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1048575) (lo := 672) (len := 96) (W := 3383015598) check rows elimOK (by decide) (by decide) cover1048575 (by decide)
  decide +kernel

theorem c1048575_8 : P.sumLeaves 26 1073741568 96 = 3108492580 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1048575) (lo := 768) (len := 96) (W := 3108492580) check rows elimOK (by decide) (by decide) cover1048575 (by decide)
  decide +kernel

theorem c1048575_9 : P.sumLeaves 26 1073741664 96 = 3566114521 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1048575) (lo := 864) (len := 96) (W := 3566114521) check rows elimOK (by decide) (by decide) cover1048575 (by decide)
  decide +kernel

theorem c1048575_10 : P.sumLeaves 26 1073741760 64 = 2703841016 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 1048575) (lo := 960) (len := 64) (W := 2703841016) check rows elimOK (by decide) (by decide) cover1048575 (by decide)
  decide +kernel

theorem h1048575 : P.leaf 36 1048575 = 31910369875 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(96, 1921987166), (96, 2505244597), (96, 2708092670), (96, 2820669237), (96, 3221457735), (96, 2972119247), (96, 2999335508), (96, 3383015598), (96, 3108492580), (96, 3566114521), (64, 2703841016)]) (.cons c1048575_0 (.cons c1048575_1 (.cons c1048575_2 (.cons c1048575_3 (.cons c1048575_4 (.cons c1048575_5 (.cons c1048575_6 (.cons c1048575_7 (.cons c1048575_8 (.cons c1048575_9 (.cons c1048575_10 (.nil)))))))))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(1048575, 1)]

theorem segOK : checkSeg 20 perms 1048575 1048576 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 1048575 1048576 1 31910369875 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 31910369875)
    (SegSum.cons (w := 1) h1048575 (show SegSum (P.leaf 36) [] 0 from rfl)) (by decide)

end RACert.S6N0.C0.S146
