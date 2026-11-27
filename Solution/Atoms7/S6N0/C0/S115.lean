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

namespace RACert.S6N0.C0.S115

open RACert RACert.Problem

theorem cover241514 : P.CoversSplit 26 10 241514 0xffffffffffffffffffffffffffffaaaaffffffffffffffccffffaaaaff00aa00fffffffffffffffffafaaaaafafaaaaaffffffffffffffccfafaaaaafa00aa00ffffffffffffffffffffffffffffaaaaffffffffff00ff00ffffaaaaff00aa00fffffffffffffffffafaaaaafafaaaaaffffffffff00ff00fafaaaaafa00aa00 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 881, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c241514_0 : P.sumLeaves 26 247310336 158 = 4777446 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241514) (lo := 0) (len := 158) (W := 4777446) check rows elimOK (by decide) (by decide) cover241514 (by decide)
  decide +kernel

theorem c241514_1 : P.sumLeaves 26 247310494 128 = 10094971 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241514) (lo := 158) (len := 128) (W := 10094971) check rows elimOK (by decide) (by decide) cover241514 (by decide)
  decide +kernel

theorem c241514_2 : P.sumLeaves 26 247310622 128 = 31062432 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241514) (lo := 286) (len := 128) (W := 31062432) check rows elimOK (by decide) (by decide) cover241514 (by decide)
  decide +kernel

theorem c241514_3 : P.sumLeaves 26 247310750 96 = 78695742 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241514) (lo := 414) (len := 96) (W := 78695742) check rows elimOK (by decide) (by decide) cover241514 (by decide)
  decide +kernel

theorem c241514_4 : P.sumLeaves 26 247310846 139 = 41367684 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241514) (lo := 510) (len := 139) (W := 41367684) check rows elimOK (by decide) (by decide) cover241514 (by decide)
  decide +kernel

theorem c241514_5 : P.sumLeaves 26 247310985 115 = 57514024 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241514) (lo := 649) (len := 115) (W := 57514024) check rows elimOK (by decide) (by decide) cover241514 (by decide)
  decide +kernel

theorem c241514_6 : P.sumLeaves 26 247311100 128 = 67149135 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241514) (lo := 764) (len := 128) (W := 67149135) check rows elimOK (by decide) (by decide) cover241514 (by decide)
  decide +kernel

theorem c241514_7 : P.sumLeaves 26 247311228 104 = 80315254 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241514) (lo := 892) (len := 104) (W := 80315254) check rows elimOK (by decide) (by decide) cover241514 (by decide)
  decide +kernel

theorem c241514_8 : P.sumLeaves 26 247311332 28 = 79845084 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 241514) (lo := 996) (len := 28) (W := 79845084) check rows elimOK (by decide) (by decide) cover241514 (by decide)
  decide +kernel

theorem h241514 : P.leaf 36 241514 = 450821772 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(158, 4777446), (128, 10094971), (128, 31062432), (96, 78695742), (139, 41367684), (115, 57514024), (128, 67149135), (104, 80315254), (28, 79845084)]) (.cons c241514_0 (.cons c241514_1 (.cons c241514_2 (.cons c241514_3 (.cons c241514_4 (.cons c241514_5 (.cons c241514_6 (.cons c241514_7 (.cons c241514_8 (.nil)))))))))) (by decide) (by decide))

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

def seg : List (ℕ × ℕ) := [(241514, 90), (241515, 360)]

theorem segOK : checkSeg 20 perms 241514 241518 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 241514 241518 450 519262234200 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 519262234200)
    (SegSum.cons (w := 90) h241514 (SegSum.cons (w := 360) h241515 (show SegSum (P.leaf 36) [] 0 from rfl))) (by decide)

end RACert.S6N0.C0.S115
