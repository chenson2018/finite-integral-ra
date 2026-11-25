/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Atoms7.S0N3.C1.Defs

/-! Generated certificate segment; see `certgen`. -/

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option Elab.async false

@[expose] public section

namespace RACert.S0N3.C1

open RACert RACert.Problem

namespace S1

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(397, 4), (398, 4), (399, 4), (404, 4), (405, 4), (406, 4), (407, 4), (408, 4), (409, 4), (410, 4), (411, 4), (412, 8), (413, 8), (414, 8), (415, 8), (444, 2), (445, 2), (446, 2), (447, 2), (448, 2), (449, 2), (450, 2), (451, 2), (452, 8), (453, 8), (454, 8), (455, 8), (460, 4), (461, 4), (462, 4), (463, 4), (468, 4), (469, 4), (470, 4), (471, 4), (472, 4), (473, 4), (474, 4), (475, 4), (476, 8), (477, 8), (478, 8), (479, 8), (508, 2), (509, 2), (510, 2), (511, 2), (768, 1), (769, 2), (771, 1), (772, 4), (773, 8), (775, 4), (780, 4), (781, 4), (782, 4), (783, 4), (792, 2), (793, 4), (795, 2), (796, 4), (797, 8), (799, 4), (828, 1), (829, 2), (831, 1), (832, 2), (833, 2), (834, 2), (835, 2), (836, 8), (837, 8), (838, 8), (839, 8), (844, 4), (845, 4)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 602, 0, 1302, 1302, 1316, 1316, 0, 0, 0, 0, 602, 1302, 602, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1316, 1316, 1316, 1316, 0, 0, 0, 0, 1302, 1302, 1316, 1316, 0, 0, 0, 0, 1302, 1302, 0, 0, 0, 0, 0, 0, 433, 531, 531, 433, 580, 580, 433, 634, 433, 634, 433, 531, 531, 433, 635, 635, 433, 1217, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(397, 327), (399, 706), (408, 0), (409, 17), (410, 15), (411, 424), (415, 1701), (444, 1038), (445, 4296), (446, 1976), (447, 14788), (448, 62), (449, 120), (450, 56), (451, 282), (460, 152), (461, 1005), (462, 236), (463, 1594), (472, 14), (473, 53), (474, 444), (475, 1424), (478, 1117), (479, 3167), (508, 2756), (509, 6136), (510, 3948), (511, 15748), (831, 16452), (832, 0), (833, 0), (834, 56), (835, 282), (836, 0), (837, 0), (838, 32), (839, 374), (844, 172), (845, 1227)]

theorem l397 : P.leaf 17 397 = 327 := by decide +kernel

theorem l399 : P.leaf 17 399 = 706 := by decide +kernel

theorem l408 : P.leaf 17 408 = 0 := by decide +kernel

theorem l409 : P.leaf 17 409 = 17 := by decide +kernel

theorem l410 : P.leaf 17 410 = 15 := by decide +kernel

theorem l411 : P.leaf 17 411 = 424 := by decide +kernel

theorem l415 : P.leaf 17 415 = 1701 := by decide +kernel

theorem l444 : P.leaf 17 444 = 1038 := by decide +kernel

theorem l445 : P.leaf 17 445 = 4296 := by decide +kernel

theorem l446 : P.leaf 17 446 = 1976 := by decide +kernel

theorem l447 : P.leaf 17 447 = 14788 := by decide +kernel

theorem l448 : P.leaf 17 448 = 62 := by decide +kernel

theorem l449 : P.leaf 17 449 = 120 := by decide +kernel

theorem l450 : P.leaf 17 450 = 56 := by decide +kernel

theorem l451 : P.leaf 17 451 = 282 := by decide +kernel

theorem l460 : P.leaf 17 460 = 152 := by decide +kernel

theorem l461 : P.leaf 17 461 = 1005 := by decide +kernel

theorem l462 : P.leaf 17 462 = 236 := by decide +kernel

theorem l463 : P.leaf 17 463 = 1594 := by decide +kernel

theorem l472 : P.leaf 17 472 = 14 := by decide +kernel

theorem l473 : P.leaf 17 473 = 53 := by decide +kernel

theorem l474 : P.leaf 17 474 = 444 := by decide +kernel

theorem l475 : P.leaf 17 475 = 1424 := by decide +kernel

theorem l478 : P.leaf 17 478 = 1117 := by decide +kernel

theorem l479 : P.leaf 17 479 = 3167 := by decide +kernel

theorem l508 : P.leaf 17 508 = 2756 := by decide +kernel

theorem l509 : P.leaf 17 509 = 6136 := by decide +kernel

theorem l510 : P.leaf 17 510 = 3948 := by decide +kernel

theorem l511 : P.leaf 17 511 = 15748 := by decide +kernel

theorem l831 : P.leaf 17 831 = 16452 := by decide +kernel

theorem l832 : P.leaf 17 832 = 0 := by decide +kernel

theorem l833 : P.leaf 17 833 = 0 := by decide +kernel

theorem l834 : P.leaf 17 834 = 56 := by decide +kernel

theorem l835 : P.leaf 17 835 = 282 := by decide +kernel

theorem l836 : P.leaf 17 836 = 0 := by decide +kernel

theorem l837 : P.leaf 17 837 = 0 := by decide +kernel

theorem l838 : P.leaf 17 838 = 32 := by decide +kernel

theorem l839 : P.leaf 17 839 = 374 := by decide +kernel

theorem l844 : P.leaf 17 844 = 172 := by decide +kernel

theorem l845 : P.leaf 17 845 = 1227 := by decide +kernel

theorem segOK : checkSeg 11 perms 397 846 seg = true := by decide +kernel

theorem evOK : P.checkEv 17 seg ev live 0 201908 = true := by decide +kernel

theorem total : OrbitSeg 11 perms (P.leaf 17) 397 846 324 201908 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.cons l397 (.cons l399 (.cons l408 (.cons l409 (.cons l410 (.cons l411 (.cons l415 (.cons l444 (.cons l445 (.cons l446 (.cons l447 (.cons l448 (.cons l449 (.cons l450 (.cons l451 (.cons l460 (.cons l461 (.cons l462 (.cons l463 (.cons l472 (.cons l473 (.cons l474 (.cons l475 (.cons l478 (.cons l479 (.cons l508 (.cons l509 (.cons l510 (.cons l511 (.cons l831 (.cons l832 (.cons l833 (.cons l834 (.cons l835 (.cons l836 (.cons l837 (.cons l838 (.cons l839 (.cons l844 (.cons l845 (.nil))))))))))))))))))))))))))))))))))))))))))

end S1

end RACert.S0N3.C1
