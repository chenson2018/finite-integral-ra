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

namespace RACert.S6N0.C0.S103

open RACert RACert.Problem

theorem cover242495 : P.CoversSplit 26 10 242495 0xfffffffffffffffffffffffffffff0f0ffffffffffffccccffffaaaaff008000fffffafafffffafaffffa0a0ffffa0a0fffffafaffffc8c8ffffa0a0ff008000fffffffffffffffffffffffffffff0f0ffccffcccc00cc00ffccaa88cc008000fffffafafffffafaffffa0a0ffffa0a0ffccfac8cc00c800ffcca080cc008000 :=
  coversSplit check rows (by decide) (by decide) (xs := [538, 579, 873, 930, 1315, 1322, 1658, 1665]) (by decide +kernel)

noncomputable def f242495 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 26 (248314880 + i)

theorem c242495_0 : rowSum f242495 0 315 = 200753729 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 242495) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover242495 (by decide)
  decide +kernel

theorem c242495_1 : rowSum f242495 315 136 = 339277260 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 242495) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover242495 (by decide)
  decide +kernel

theorem c242495_2 : rowSum f242495 451 399 = 448351854 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 242495) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover242495 (by decide)
  decide +kernel

theorem c242495_3 : rowSum f242495 850 174 = 411035076 := by
  apply weightedChunk_eq (b := 20) (m := 6) (d := 10) (H := 242495) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover242495 (by decide)
  decide +kernel

theorem sum242495 : rowSum f242495 0 1024 = 1399417919 :=
  rowSum_append (F := f242495) (lo := 0) (n := 315) (m := 709) (A := 200753729) (B := 1198664190) c242495_0 (rowSum_append (F := f242495) (lo := 315) (n := 136) (m := 573) (A := 339277260) (B := 859386930) c242495_1 (rowSum_append (F := f242495) (lo := 451) (n := 399) (m := 174) (A := 448351854) (B := 411035076) c242495_2 (c242495_3)))

theorem h242495 : P.leaf 36 242495 = 1399417919 :=
  leaf_weighted (k := 26) (d := 10) (H := 242495) (keep := keep2) (twice := twice2) rows (by decide) (by decide) bal2 (invRow2 (H := 242495) (by decide) (by decide +kernel)) sum242495

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

def seg : List (ℕ × ℕ) := [(242495, 360), (242543, 360), (242559, 360)]

theorem segOK : checkSeg 20 perms 242495 242687 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 242495 242687 1080 1949652093600 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 1949652093600)
    (SegSum.cons (w := 360) h242495 (SegSum.cons (w := 360) h242543 (SegSum.cons (w := 360) h242559 (show SegSum (P.leaf 36) [] 0 from rfl)))) (by decide)

end RACert.S6N0.C0.S103
