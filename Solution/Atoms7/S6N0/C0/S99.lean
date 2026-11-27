/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Atoms7.S6N0.C0.Actions

/-! Generated identity-class certificate for the product-row count. -/

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option Elab.async false

@[expose] public section

namespace RACert.S6N0.C0.S99

open RACert RACert.Problem

theorem cover241515 : P.CoversSplit 26 10 241515 0xffffffffffffffffffffffffffffaaaaffffffffffffffccffffaaaaff00aa00fffffffffffffffffafaaaaafafaaaaaffffffffffffffccfafaaaaafa00aa00ffffffffffffffffffffffffffffaaaaffffffffff00ff00ffffaaaaff00aa00fffffffffffffffffafaaaaafafaaaaaffffffffff00ff00fafaaaaafa00aa00 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 579, 881, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c241515_0 : P.sumLeaves 26 247311360 158 = 22907160 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241515) (lo := 0) (len := 158) (W := 22907160) check rows elimOK (by decide) (by decide) cover241515 (by decide)
  decide +kernel

theorem c241515_1 : P.sumLeaves 26 247311518 128 = 52990808 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241515) (lo := 158) (len := 128) (W := 52990808) check rows elimOK (by decide) (by decide) cover241515 (by decide)
  decide +kernel

theorem c241515_2 : P.sumLeaves 26 247311646 128 = 83517740 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241515) (lo := 286) (len := 128) (W := 83517740) check rows elimOK (by decide) (by decide) cover241515 (by decide)
  decide +kernel

theorem c241515_3 : P.sumLeaves 26 247311774 96 = 201668923 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241515) (lo := 414) (len := 96) (W := 201668923) check rows elimOK (by decide) (by decide) cover241515 (by decide)
  decide +kernel

theorem c241515_4 : P.sumLeaves 26 247311870 139 = 132422188 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241515) (lo := 510) (len := 139) (W := 132422188) check rows elimOK (by decide) (by decide) cover241515 (by decide)
  decide +kernel

theorem c241515_5 : P.sumLeaves 26 247312009 115 = 225563349 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241515) (lo := 649) (len := 115) (W := 225563349) check rows elimOK (by decide) (by decide) cover241515 (by decide)
  decide +kernel

theorem c241515_6 : P.sumLeaves 26 247312124 128 = 180231839 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241515) (lo := 764) (len := 128) (W := 180231839) check rows elimOK (by decide) (by decide) cover241515 (by decide)
  decide +kernel

theorem c241515_7 : P.sumLeaves 26 247312252 104 = 237704687 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241515) (lo := 892) (len := 104) (W := 237704687) check rows elimOK (by decide) (by decide) cover241515 (by decide)
  decide +kernel

theorem c241515_8 : P.sumLeaves 26 247312356 28 = 192682958 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241515) (lo := 996) (len := 28) (W := 192682958) check rows elimOK (by decide) (by decide) cover241515 (by decide)
  decide +kernel

theorem h241515 : P.leaf 36 241515 = 1329689652 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(158, 22907160), (128, 52990808), (128, 83517740), (96, 201668923), (139, 132422188), (115, 225563349), (128, 180231839), (104, 237704687), (28, 192682958)]) (.cons c241515_0 (.cons c241515_1 (.cons c241515_2 (.cons c241515_3 (.cons c241515_4 (.cons c241515_5 (.cons c241515_6 (.cons c241515_7 (.cons c241515_8 (.nil)))))))))) (by decide) (by decide))

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

def seg : List (ℕ × ℕ) := [(241515, 360), (241518, 360)]

theorem segOK : checkSeg 20 perms 241515 241519 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 241515 241519 720 841529310840 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 841529310840)
    (SegSum.cons (w := 360) h241515 (SegSum.cons (w := 360) h241518 (show SegSum (P.leaf 36) [] 0 from rfl))) (by decide)

end RACert.S6N0.C0.S99
