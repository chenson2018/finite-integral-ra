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

namespace RACert.S6N0.C0.S121

open RACert RACert.Problem

theorem cover242543 : P.CoversSplit 26 10 242543 0xfffffffffffffffffffffffffffffafaffffffffffffccccffffaaaaff008800fffffafafffffafafafaaaaafafaaaaafffffafaffffc8c8fafaaaaafa008800fffffffffffffffffffffffffffffafaffccffcccc00cc00ffccaa88cc0088000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [579, 873, 930, 1266, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c242543_0 : P.sumLeaves 26 248364032 428 = 123019490 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 242543) (lo := 0) (len := 428) (W := 123019490) check rows elimOK (by decide) (by decide) cover242543 (by decide)
  decide +kernel

theorem c242543_1 : P.sumLeaves 26 248364460 125 = 234383278 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 242543) (lo := 428) (len := 125) (W := 234383278) check rows elimOK (by decide) (by decide) cover242543 (by decide)
  decide +kernel

theorem c242543_2 : P.sumLeaves 26 248364585 139 = 149250792 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 242543) (lo := 553) (len := 139) (W := 149250792) check rows elimOK (by decide) (by decide) cover242543 (by decide)
  decide +kernel

theorem c242543_3 : P.sumLeaves 26 248364724 136 = 245670648 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 242543) (lo := 692) (len := 136) (W := 245670648) check rows elimOK (by decide) (by decide) cover242543 (by decide)
  decide +kernel

theorem c242543_4 : P.sumLeaves 26 248364860 108 = 191354975 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 242543) (lo := 828) (len := 108) (W := 191354975) check rows elimOK (by decide) (by decide) cover242543 (by decide)
  decide +kernel

theorem c242543_5 : P.sumLeaves 26 248364968 88 = 320010735 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 242543) (lo := 936) (len := 88) (W := 320010735) check rows elimOK (by decide) (by decide) cover242543 (by decide)
  decide +kernel

theorem h242543 : P.leaf 36 242543 = 1263689918 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(428, 123019490), (125, 234383278), (139, 149250792), (136, 245670648), (108, 191354975), (88, 320010735)]) (.cons c242543_0 (.cons c242543_1 (.cons c242543_2 (.cons c242543_3 (.cons c242543_4 (.cons c242543_5 (.nil))))))) (by decide) (by decide))

theorem cover242559 : P.CoversSplit 26 10 242559 0xfffffffffffffffffffffffffffffafaffffffffffffccccffffaaaaff008800fffffafafffffafaffffaaaaffffaaaafffffafaffffc8c8ffffaaaaff008800fffffffffffffffffffffffffffffafaffccffcccc00cc00ffccaa88cc008800fffffafafffffafaffffaaaaffffaaaaffccfac8cc00c800ffccaa88cc008800 :=
  coversSplit check rows (by decide) (by decide) (xs := [579, 873, 930, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c242559_0 : P.sumLeaves 26 248380416 188 = 155652888 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 242559) (lo := 0) (len := 188) (W := 155652888) check rows elimOK (by decide) (by decide) cover242559 (by decide)
  decide +kernel

theorem c242559_1 : P.sumLeaves 26 248380604 172 = 273040602 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 242559) (lo := 188) (len := 172) (W := 273040602) check rows elimOK (by decide) (by decide) cover242559 (by decide)
  decide +kernel

theorem c242559_2 : P.sumLeaves 26 248380776 104 = 292911823 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 242559) (lo := 360) (len := 104) (W := 292911823) check rows elimOK (by decide) (by decide) cover242559 (by decide)
  decide +kernel

theorem c242559_3 : P.sumLeaves 26 248380880 136 = 390835675 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 242559) (lo := 464) (len := 136) (W := 390835675) check rows elimOK (by decide) (by decide) cover242559 (by decide)
  decide +kernel

theorem c242559_4 : P.sumLeaves 26 248381016 120 = 338418264 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 242559) (lo := 600) (len := 120) (W := 338418264) check rows elimOK (by decide) (by decide) cover242559 (by decide)
  decide +kernel

theorem c242559_5 : P.sumLeaves 26 248381136 138 = 450125136 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 242559) (lo := 720) (len := 138) (W := 450125136) check rows elimOK (by decide) (by decide) cover242559 (by decide)
  decide +kernel

theorem c242559_6 : P.sumLeaves 26 248381274 100 = 395069329 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 242559) (lo := 858) (len := 100) (W := 395069329) check rows elimOK (by decide) (by decide) cover242559 (by decide)
  decide +kernel

theorem c242559_7 : P.sumLeaves 26 248381374 66 = 456538706 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 242559) (lo := 958) (len := 66) (W := 456538706) check rows elimOK (by decide) (by decide) cover242559 (by decide)
  decide +kernel

theorem h242559 : P.leaf 36 242559 = 2752592423 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(188, 155652888), (172, 273040602), (104, 292911823), (136, 390835675), (120, 338418264), (138, 450125136), (100, 395069329), (66, 456538706)]) (.cons c242559_0 (.cons c242559_1 (.cons c242559_2 (.cons c242559_3 (.cons c242559_4 (.cons c242559_5 (.cons c242559_6 (.cons c242559_7 (.nil))))))))) (by decide) (by decide))

theorem cover242687 : P.CoversSplit 26 10 242687 0xfffffffffffffffffffffffffffffafaffffffffffffccccffffaaaaffcc8888fffffafafffffafaffffaaaaffffaaaafffffafaffffc8c8ffffaaaaffcc8888fffffffffffffffffffffffffffffafaffccffccccccccccffccaa88cccc8888fffffafafffffafaffffaaaaffffaaaaffccfac8ccccc8c8ffccaa88cccc8888 :=
  coversSplit check rows (by decide) (by decide) (xs := [873, 930, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c242687_0 : P.sumLeaves 26 248511488 175 = 434413272 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 242687) (lo := 0) (len := 175) (W := 434413272) check rows elimOK (by decide) (by decide) cover242687 (by decide)
  decide +kernel

theorem c242687_1 : P.sumLeaves 26 248511663 138 = 584754163 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 242687) (lo := 175) (len := 138) (W := 584754163) check rows elimOK (by decide) (by decide) cover242687 (by decide)
  decide +kernel

theorem c242687_2 : P.sumLeaves 26 248511801 124 = 762685066 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 242687) (lo := 313) (len := 124) (W := 762685066) check rows elimOK (by decide) (by decide) cover242687 (by decide)
  decide +kernel

theorem c242687_3 : P.sumLeaves 26 248511925 118 = 942100943 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 242687) (lo := 437) (len := 118) (W := 942100943) check rows elimOK (by decide) (by decide) cover242687 (by decide)
  decide +kernel

theorem c242687_4 : P.sumLeaves 26 248512043 124 = 777436614 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 242687) (lo := 555) (len := 124) (W := 777436614) check rows elimOK (by decide) (by decide) cover242687 (by decide)
  decide +kernel

theorem c242687_5 : P.sumLeaves 26 248512167 128 = 997298350 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 242687) (lo := 679) (len := 128) (W := 997298350) check rows elimOK (by decide) (by decide) cover242687 (by decide)
  decide +kernel

theorem c242687_6 : P.sumLeaves 26 248512295 112 = 964046237 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 242687) (lo := 807) (len := 112) (W := 964046237) check rows elimOK (by decide) (by decide) cover242687 (by decide)
  decide +kernel

theorem c242687_7 : P.sumLeaves 26 248512407 96 = 1209731189 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 242687) (lo := 919) (len := 96) (W := 1209731189) check rows elimOK (by decide) (by decide) cover242687 (by decide)
  decide +kernel

theorem c242687_8 : P.sumLeaves 26 248512503 9 = 165760749 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 242687) (lo := 1015) (len := 9) (W := 165760749) check rows elimOK (by decide) (by decide) cover242687 (by decide)
  decide +kernel

theorem h242687 : P.leaf 36 242687 = 6838226583 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(175, 434413272), (138, 584754163), (124, 762685066), (118, 942100943), (124, 777436614), (128, 997298350), (112, 964046237), (96, 1209731189), (9, 165760749)]) (.cons c242687_0 (.cons c242687_1 (.cons c242687_2 (.cons c242687_3 (.cons c242687_4 (.cons c242687_5 (.cons c242687_6 (.cons c242687_7 (.cons c242687_8 (.nil)))))))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(242543, 360), (242559, 360), (242687, 72)]

theorem segOK : checkSeg 20 perms 242543 243511 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 242543 243511 792 1938213956736 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 1938213956736)
    (SegSum.cons (w := 360) h242543 (SegSum.cons (w := 360) h242559 (SegSum.cons (w := 72) h242687 (show SegSum (P.leaf 36) [] 0 from rfl)))) (by decide)

end RACert.S6N0.C0.S121
