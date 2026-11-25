/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Atoms7.S0N3.C5.Defs

/-! Generated certificate segment; see `certgen`. -/

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option Elab.async false

@[expose] public section

namespace RACert.S0N3.C5

open RACert RACert.Problem

namespace S3

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(451, 12), (455, 24), (463, 12), (465, 24), (466, 24), (467, 24), (469, 24), (470, 24), (471, 24), (473, 24), (474, 24), (475, 24), (476, 12), (477, 24), (478, 24), (479, 24), (496, 12), (497, 24), (499, 12), (500, 24), (501, 24), (502, 24), (503, 24), (508, 12), (509, 24), (511, 12), (783, 6), (797, 6), (798, 6), (799, 12), (831, 3), (839, 12), (843, 12), (847, 12), (853, 24), (854, 24), (855, 24), (857, 24), (858, 24), (859, 24)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(451, 268), (455, 405), (463, 596), (465, 481), (466, 411), (467, 899), (469, 835), (470, 738), (471, 1229), (473, 849), (474, 626), (475, 1191), (476, 827), (477, 1401), (478, 1081), (479, 1993), (496, 250), (497, 751), (499, 1196), (500, 657), (501, 1078), (502, 1187), (503, 1558), (508, 1166), (509, 1636), (511, 2510), (783, 510), (797, 514), (798, 306), (799, 634), (831, 858), (839, 942), (843, 725), (847, 1536), (853, 925), (854, 658), (855, 1274), (857, 656), (858, 550), (859, 931)]

theorem l451 : P.leaf 16 451 = 268 := by decide +kernel

theorem l455 : P.leaf 16 455 = 405 := by decide +kernel

theorem l463 : P.leaf 16 463 = 596 := by decide +kernel

theorem l465 : P.leaf 16 465 = 481 := by decide +kernel

theorem l466 : P.leaf 16 466 = 411 := by decide +kernel

theorem l467 : P.leaf 16 467 = 899 := by decide +kernel

theorem l469 : P.leaf 16 469 = 835 := by decide +kernel

theorem l470 : P.leaf 16 470 = 738 := by decide +kernel

theorem l471 : P.leaf 16 471 = 1229 := by decide +kernel

theorem l473 : P.leaf 16 473 = 849 := by decide +kernel

theorem l474 : P.leaf 16 474 = 626 := by decide +kernel

theorem l475 : P.leaf 16 475 = 1191 := by decide +kernel

theorem l476 : P.leaf 16 476 = 827 := by decide +kernel

theorem l477 : P.leaf 16 477 = 1401 := by decide +kernel

theorem l478 : P.leaf 16 478 = 1081 := by decide +kernel

theorem l479 : P.leaf 16 479 = 1993 := by decide +kernel

theorem l496 : P.leaf 16 496 = 250 := by decide +kernel

theorem l497 : P.leaf 16 497 = 751 := by decide +kernel

theorem l499 : P.leaf 16 499 = 1196 := by decide +kernel

theorem l500 : P.leaf 16 500 = 657 := by decide +kernel

theorem l501 : P.leaf 16 501 = 1078 := by decide +kernel

theorem l502 : P.leaf 16 502 = 1187 := by decide +kernel

theorem l503 : P.leaf 16 503 = 1558 := by decide +kernel

theorem l508 : P.leaf 16 508 = 1166 := by decide +kernel

theorem l509 : P.leaf 16 509 = 1636 := by decide +kernel

theorem l511 : P.leaf 16 511 = 2510 := by decide +kernel

theorem l783 : P.leaf 16 783 = 510 := by decide +kernel

theorem l797 : P.leaf 16 797 = 514 := by decide +kernel

theorem l798 : P.leaf 16 798 = 306 := by decide +kernel

theorem l799 : P.leaf 16 799 = 634 := by decide +kernel

theorem l831 : P.leaf 16 831 = 858 := by decide +kernel

theorem l839 : P.leaf 16 839 = 942 := by decide +kernel

theorem l843 : P.leaf 16 843 = 725 := by decide +kernel

theorem l847 : P.leaf 16 847 = 1536 := by decide +kernel

theorem l853 : P.leaf 16 853 = 925 := by decide +kernel

theorem l854 : P.leaf 16 854 = 658 := by decide +kernel

theorem l855 : P.leaf 16 855 = 1274 := by decide +kernel

theorem l857 : P.leaf 16 857 = 656 := by decide +kernel

theorem l858 : P.leaf 16 858 = 550 := by decide +kernel

theorem l859 : P.leaf 16 859 = 931 := by decide +kernel

theorem segOK : checkSeg 12 perms 451 861 seg = true := by decide +kernel

theorem evOK : P.checkEv 16 seg ev live 0 714354 = true := by decide +kernel

theorem total : OrbitSeg 12 perms (P.leaf 16) 451 861 753 714354 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.cons l451 (.cons l455 (.cons l463 (.cons l465 (.cons l466 (.cons l467 (.cons l469 (.cons l470 (.cons l471 (.cons l473 (.cons l474 (.cons l475 (.cons l476 (.cons l477 (.cons l478 (.cons l479 (.cons l496 (.cons l497 (.cons l499 (.cons l500 (.cons l501 (.cons l502 (.cons l503 (.cons l508 (.cons l509 (.cons l511 (.cons l783 (.cons l797 (.cons l798 (.cons l799 (.cons l831 (.cons l839 (.cons l843 (.cons l847 (.cons l853 (.cons l854 (.cons l855 (.cons l857 (.cons l858 (.cons l859 (.nil))))))))))))))))))))))))))))))))))))))))))

end S3

end RACert.S0N3.C5
