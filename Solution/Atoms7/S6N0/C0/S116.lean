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

namespace RACert.S6N0.C0.S116

open RACert RACert.Problem

theorem cover241518 : P.CoversSplit 26 10 241518 0xffffffffffffffffffffffffffffaaaaffffffffffffffccffffaaaaff00aa00fffffffffffffffffafaaaaafafaaaaaffffffffffffffccfafaaaaafa00aa00ffffffffffffffffffffffffffffaaaaffffffffff00ff00ffffaaaaff00aa00fffffffffffffffffafaaaaafafaaaaaffffffffff00ff00fafaaaaafa00aa00 :=
  coversSplit check rows (by decide) (by decide) (xs := [579, 881, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c241518_0 : P.sumLeaves 26 247314432 158 = 20640777 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241518) (lo := 0) (len := 158) (W := 20640777) check rows elimOK (by decide) (by decide) cover241518 (by decide)
  decide +kernel

theorem c241518_1 : P.sumLeaves 26 247314590 128 = 42929000 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241518) (lo := 158) (len := 128) (W := 42929000) check rows elimOK (by decide) (by decide) cover241518 (by decide)
  decide +kernel

theorem c241518_2 : P.sumLeaves 26 247314718 128 = 72759884 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241518) (lo := 286) (len := 128) (W := 72759884) check rows elimOK (by decide) (by decide) cover241518 (by decide)
  decide +kernel

theorem c241518_3 : P.sumLeaves 26 247314846 96 = 197894383 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241518) (lo := 414) (len := 96) (W := 197894383) check rows elimOK (by decide) (by decide) cover241518 (by decide)
  decide +kernel

theorem c241518_4 : P.sumLeaves 26 247314942 139 = 85667490 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241518) (lo := 510) (len := 139) (W := 85667490) check rows elimOK (by decide) (by decide) cover241518 (by decide)
  decide +kernel

theorem c241518_5 : P.sumLeaves 26 247315081 115 = 115773003 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241518) (lo := 649) (len := 115) (W := 115773003) check rows elimOK (by decide) (by decide) cover241518 (by decide)
  decide +kernel

theorem c241518_6 : P.sumLeaves 26 247315196 128 = 144129316 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241518) (lo := 764) (len := 128) (W := 144129316) check rows elimOK (by decide) (by decide) cover241518 (by decide)
  decide +kernel

theorem c241518_7 : P.sumLeaves 26 247315324 104 = 167950770 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241518) (lo := 892) (len := 104) (W := 167950770) check rows elimOK (by decide) (by decide) cover241518 (by decide)
  decide +kernel

theorem c241518_8 : P.sumLeaves 26 247315428 28 = 160147144 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241518) (lo := 996) (len := 28) (W := 160147144) check rows elimOK (by decide) (by decide) cover241518 (by decide)
  decide +kernel

theorem h241518 : P.leaf 36 241518 = 1007891767 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(158, 20640777), (128, 42929000), (128, 72759884), (96, 197894383), (139, 85667490), (115, 115773003), (128, 144129316), (104, 167950770), (28, 160147144)]) (.cons c241518_0 (.cons c241518_1 (.cons c241518_2 (.cons c241518_3 (.cons c241518_4 (.cons c241518_5 (.cons c241518_6 (.cons c241518_7 (.cons c241518_8 (.nil)))))))))) (by decide) (by decide))

theorem cover241519 : P.CoversSplit 26 10 241519 0xffffffffffffffffffffffffffffaaaaffffffffffffffccffffaaaaff00aa00fffffffffffffffffafaaaaafafaaaaaffffffffffffffccfafaaaaafa00aa00ffffffffffffffffffffffffffffaaaaffffffffff00ff00ffffaaaaff00aa00fffffffffffffffffafaaaaafafaaaaaffffffffff00ff00fafaaaaafa00aa00 :=
  coversSplit check rows (by decide) (by decide) (xs := [579, 881, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c241519_0 : P.sumLeaves 26 247315456 158 = 82609154 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241519) (lo := 0) (len := 158) (W := 82609154) check rows elimOK (by decide) (by decide) cover241519 (by decide)
  decide +kernel

theorem c241519_1 : P.sumLeaves 26 247315614 128 = 185072936 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241519) (lo := 158) (len := 128) (W := 185072936) check rows elimOK (by decide) (by decide) cover241519 (by decide)
  decide +kernel

theorem c241519_2 : P.sumLeaves 26 247315742 128 = 179160271 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241519) (lo := 286) (len := 128) (W := 179160271) check rows elimOK (by decide) (by decide) cover241519 (by decide)
  decide +kernel

theorem c241519_3 : P.sumLeaves 26 247315870 96 = 443557267 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241519) (lo := 414) (len := 96) (W := 443557267) check rows elimOK (by decide) (by decide) cover241519 (by decide)
  decide +kernel

theorem c241519_4 : P.sumLeaves 26 247315966 139 = 205198637 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241519) (lo := 510) (len := 139) (W := 205198637) check rows elimOK (by decide) (by decide) cover241519 (by decide)
  decide +kernel

theorem c241519_5 : P.sumLeaves 26 247316105 115 = 350277429 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241519) (lo := 649) (len := 115) (W := 350277429) check rows elimOK (by decide) (by decide) cover241519 (by decide)
  decide +kernel

theorem c241519_6 : P.sumLeaves 26 247316220 128 = 278601135 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241519) (lo := 764) (len := 128) (W := 278601135) check rows elimOK (by decide) (by decide) cover241519 (by decide)
  decide +kernel

theorem c241519_7 : P.sumLeaves 26 247316348 104 = 385425068 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241519) (lo := 892) (len := 104) (W := 385425068) check rows elimOK (by decide) (by decide) cover241519 (by decide)
  decide +kernel

theorem c241519_8 : P.sumLeaves 26 247316452 28 = 288750939 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241519) (lo := 996) (len := 28) (W := 288750939) check rows elimOK (by decide) (by decide) cover241519 (by decide)
  decide +kernel

theorem h241519 : P.leaf 36 241519 = 2398652836 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(158, 82609154), (128, 185072936), (128, 179160271), (96, 443557267), (139, 205198637), (115, 350277429), (128, 278601135), (104, 385425068), (28, 288750939)]) (.cons c241519_0 (.cons c241519_1 (.cons c241519_2 (.cons c241519_3 (.cons c241519_4 (.cons c241519_5 (.cons c241519_6 (.cons c241519_7 (.cons c241519_8 (.nil)))))))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(241518, 360), (241519, 720)]

theorem segOK : checkSeg 20 perms 241518 241534 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 241518 241534 1080 2089871078040 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 2089871078040)
    (SegSum.cons (w := 360) h241518 (SegSum.cons (w := 720) h241519 (show SegSum (P.leaf 36) [] 0 from rfl))) (by decide)

end RACert.S6N0.C0.S116
