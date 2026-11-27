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

namespace RACert.S6N0.C0.S96

open RACert RACert.Problem

theorem cover122742 : P.CoversSplit 26 10 122742 0xfffffffffffffafa0000000000000000fffffffffffffac805050505000000000505000005050000050500000505000005050000050500000505000000000000fffffffffffffafa0000000000000000ffccffcc0000000005040504000000000505000005050000050500000505000005040000000000000504000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 579, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c122742_0 : P.sumLeaves 26 125687808 496 = 82077974 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122742) (lo := 0) (len := 496) (W := 82077974) check rows elimOK (by decide) (by decide) cover122742 (by decide)
  decide +kernel

theorem c122742_1 : P.sumLeaves 26 125688304 387 = 94544602 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122742) (lo := 496) (len := 387) (W := 94544602) check rows elimOK (by decide) (by decide) cover122742 (by decide)
  decide +kernel

theorem c122742_2 : P.sumLeaves 26 125688691 141 = 124200292 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122742) (lo := 883) (len := 141) (W := 124200292) check rows elimOK (by decide) (by decide) cover122742 (by decide)
  decide +kernel

theorem h122742 : P.leaf 36 122742 = 300822868 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(496, 82077974), (387, 94544602), (141, 124200292)]) (.cons c122742_0 (.cons c122742_1 (.cons c122742_2 (.nil)))) (by decide) (by decide))

theorem cover122743 : P.CoversSplit 26 10 122743 0xfffffffffffffafa0000000000000000fffffffffffffac805050505000000000505000005050000050500000505000005050000050500000505000000000000fffffffffffffafa0000000000000000ffffffff0000000005050505000000000505000005050000050500000505000005050000000000000505000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 579, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c122743_0 : P.sumLeaves 26 125688832 484 = 139276536 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122743) (lo := 0) (len := 484) (W := 139276536) check rows elimOK (by decide) (by decide) cover122743 (by decide)
  decide +kernel

theorem c122743_1 : P.sumLeaves 26 125689316 387 = 176099318 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122743) (lo := 484) (len := 387) (W := 176099318) check rows elimOK (by decide) (by decide) cover122743 (by decide)
  decide +kernel

theorem c122743_2 : P.sumLeaves 26 125689703 153 = 260300996 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122743) (lo := 871) (len := 153) (W := 260300996) check rows elimOK (by decide) (by decide) cover122743 (by decide)
  decide +kernel

theorem h122743 : P.leaf 36 122743 = 575676850 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(484, 139276536), (387, 176099318), (153, 260300996)]) (.cons c122743_0 (.cons c122743_1 (.cons c122743_2 (.nil)))) (by decide) (by decide))

theorem cover122750 : P.CoversSplit 26 10 122750 0xfffffffffffffafa0000000000000000fffffffffffffac805050505000000000505000005050000050500000505000005050000050500000505000000000000fffffffffffffafa0000000000000000ffffffff0000000005050505000000000505000005050000050500000505000005050000000000000505000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [579, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c122750_0 : P.sumLeaves 26 125696000 484 = 97472509 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122750) (lo := 0) (len := 484) (W := 97472509) check rows elimOK (by decide) (by decide) cover122750 (by decide)
  decide +kernel

theorem c122750_1 : P.sumLeaves 26 125696484 387 = 156826862 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122750) (lo := 484) (len := 387) (W := 156826862) check rows elimOK (by decide) (by decide) cover122750 (by decide)
  decide +kernel

theorem c122750_2 : P.sumLeaves 26 125696871 153 = 225379932 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122750) (lo := 871) (len := 153) (W := 225379932) check rows elimOK (by decide) (by decide) cover122750 (by decide)
  decide +kernel

theorem h122750 : P.leaf 36 122750 = 479679303 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(484, 97472509), (387, 156826862), (153, 225379932)]) (.cons c122750_0 (.cons c122750_1 (.cons c122750_2 (.nil)))) (by decide) (by decide))

theorem cover122751 : P.CoversSplit 26 10 122751 0xfffffffffffffafa0000000000000000fffffffffffffac805050505000000000505000005050000050500000505000005050000050500000505000000000000fffffffffffffafa0000000000000000ffffffff0000000005050505000000000505000005050000050500000505000005050000000000000505000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [579, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c122751_0 : P.sumLeaves 26 125697024 484 = 147058896 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122751) (lo := 0) (len := 484) (W := 147058896) check rows elimOK (by decide) (by decide) cover122751 (by decide)
  decide +kernel

theorem c122751_1 : P.sumLeaves 26 125697508 387 = 189357978 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122751) (lo := 484) (len := 387) (W := 189357978) check rows elimOK (by decide) (by decide) cover122751 (by decide)
  decide +kernel

theorem c122751_2 : P.sumLeaves 26 125697895 153 = 265200624 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122751) (lo := 871) (len := 153) (W := 265200624) check rows elimOK (by decide) (by decide) cover122751 (by decide)
  decide +kernel

theorem h122751 : P.leaf 36 122751 = 601617498 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(484, 147058896), (387, 189357978), (153, 265200624)]) (.cons c122751_0 (.cons c122751_1 (.cons c122751_2 (.nil)))) (by decide) (by decide))

theorem cover122835 : P.CoversSplit 26 10 122835 0xfffffffffffffafafffffafafffffafaffffffffffccfa00fafafafac8c8c800fffffafafffffafafafafafafafafafafffffafaffccfa00fafafafac8c8c800fffffffffffffafafffffafafffffafaffffffffcc00c800fafafafac800c800fffffafafffffafafafafafafafafafafffffafacc00c800fafafafac800c800 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 489, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c122835_0 : P.sumLeaves 26 125783040 171 = 24500627 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122835) (lo := 0) (len := 171) (W := 24500627) check rows elimOK (by decide) (by decide) cover122835 (by decide)
  decide +kernel

theorem c122835_1 : P.sumLeaves 26 125783211 140 = 43320705 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122835) (lo := 171) (len := 140) (W := 43320705) check rows elimOK (by decide) (by decide) cover122835 (by decide)
  decide +kernel

theorem c122835_2 : P.sumLeaves 26 125783351 131 = 125173741 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122835) (lo := 311) (len := 131) (W := 125173741) check rows elimOK (by decide) (by decide) cover122835 (by decide)
  decide +kernel

theorem c122835_3 : P.sumLeaves 26 125783482 131 = 198118091 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122835) (lo := 442) (len := 131) (W := 198118091) check rows elimOK (by decide) (by decide) cover122835 (by decide)
  decide +kernel

theorem c122835_4 : P.sumLeaves 26 125783613 130 = 131533759 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122835) (lo := 573) (len := 130) (W := 131533759) check rows elimOK (by decide) (by decide) cover122835 (by decide)
  decide +kernel

theorem c122835_5 : P.sumLeaves 26 125783743 147 = 206913966 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122835) (lo := 703) (len := 147) (W := 206913966) check rows elimOK (by decide) (by decide) cover122835 (by decide)
  decide +kernel

theorem c122835_6 : P.sumLeaves 26 125783890 106 = 183238142 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122835) (lo := 850) (len := 106) (W := 183238142) check rows elimOK (by decide) (by decide) cover122835 (by decide)
  decide +kernel

theorem c122835_7 : P.sumLeaves 26 125783996 68 = 248452621 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 122835) (lo := 956) (len := 68) (W := 248452621) check rows elimOK (by decide) (by decide) cover122835 (by decide)
  decide +kernel

theorem h122835 : P.leaf 36 122835 = 1161251652 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(171, 24500627), (140, 43320705), (131, 125173741), (131, 198118091), (130, 131533759), (147, 206913966), (106, 183238142), (68, 248452621)]) (.cons c122835_0 (.cons c122835_1 (.cons c122835_2 (.cons c122835_3 (.cons c122835_4 (.cons c122835_5 (.cons c122835_6 (.cons c122835_7 (.nil))))))))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(122742, 180), (122743, 180), (122750, 180), (122751, 180), (122835, 360)]

theorem segOK : checkSeg 20 perms 122742 122836 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 122742 122836 1080 770453968140 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 770453968140)
    (SegSum.cons (w := 180) h122742 (SegSum.cons (w := 180) h122743 (SegSum.cons (w := 180) h122750 (SegSum.cons (w := 180) h122751 (SegSum.cons (w := 360) h122835 (show SegSum (P.leaf 36) [] 0 from rfl)))))) (by decide)

end RACert.S6N0.C0.S96
