/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Atoms7.S0N3.C0.Defs

/-! Generated certificate segment; see `certgen`. -/

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option Elab.async false

@[expose] public section

namespace RACert.S0N3.C0

open RACert RACert.Problem

namespace S0

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(0, 1), (1, 12), (3, 6), (5, 12), (7, 12), (15, 3), (17, 6), (18, 6), (19, 12), (20, 24), (21, 24), (22, 24), (23, 24), (28, 12), (29, 12), (30, 12), (31, 12), (51, 3), (52, 12), (53, 24), (55, 12), (60, 6), (61, 12), (63, 6), (80, 12), (81, 24), (82, 24), (83, 24), (85, 12), (86, 24), (87, 24), (90, 12), (91, 24), (95, 12), (112, 12), (113, 24), (115, 12), (116, 12), (117, 24), (119, 12), (120, 12), (121, 24), (123, 12), (124, 12), (125, 24), (127, 12), (240, 3), (241, 12), (243, 6), (245, 12), (247, 12), (255, 3), (261, 24), (262, 24), (263, 24), (269, 24), (271, 12), (277, 24), (278, 12), (279, 24), (282, 12), (283, 24), (284, 24), (285, 24), (286, 24), (287, 24), (311, 12), (316, 12), (317, 24), (319, 12), (321, 8), (322, 8), (323, 24), (325, 24), (326, 24), (327, 24), (329, 24), (330, 24), (331, 24), (333, 24), (334, 24), (335, 24), (339, 24), (340, 24), (341, 24), (342, 24), (343, 24), (344, 12), (345, 24), (346, 24), (347, 24), (348, 24), (349, 24), (350, 24), (351, 24), (355, 24), (357, 24), (358, 24), (359, 24), (360, 12), (361, 24), (362, 24), (363, 24), (364, 24), (365, 24), (366, 24), (367, 24), (371, 24), (372, 24), (373, 24), (374, 24), (375, 24), (376, 24), (377, 24), (378, 24), (379, 24), (380, 24), (381, 24), (382, 24), (383, 24), (451, 12), (455, 24), (463, 12), (465, 24), (466, 24), (467, 24), (469, 24), (470, 24), (471, 24), (473, 24), (474, 24), (475, 24), (476, 12), (477, 24), (478, 24), (479, 24), (496, 12), (497, 24), (499, 12), (500, 24), (501, 24), (502, 24), (503, 24), (508, 12), (509, 24), (511, 12), (783, 6), (797, 6), (798, 6), (799, 12), (831, 3), (839, 12), (843, 12), (847, 12), (853, 24), (854, 24), (855, 24), (857, 24), (858, 24), (859, 24), (861, 24), (862, 24), (863, 24), (884, 6), (885, 24), (887, 12), (888, 6), (889, 24), (891, 12), (892, 12), (893, 24), (895, 12), (963, 2), (967, 12), (975, 6), (981, 24), (982, 24), (983, 24), (989, 12), (990, 12), (991, 12), (1013, 24), (1015, 12)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 573, 573, 573, 573, 573, 573, 573, 573, 0, 0, 0, 0, 0, 0, 0, 1224, 587, 538, 538, 573, 538, 538, 538, 538, 538, 1218, 587, 538, 1218, 587, 538, 1218, 587, 538, 1218, 587, 538, 1218, 1218, 1218, 1218, 1218, 1218, 0, 424, 0, 418, 0, 573, 424, 573, 0, 0, 424, 573, 424, 573, 0, 0, 0, 0, 419, 427, 518, 518, 424, 518, 418, 518, 518, 418, 424, 518, 538, 424, 573, 424, 538, 0, 419, 538, 538, 424, 573, 424, 538, 518, 518, 427, 518, 418, 418, 518, 518, 418, 418, 518, 518, 538, 1218, 587, 427, 538, 1218, 419, 538, 538, 1218, 587, 538, 538, 518, 518, 518, 419, 427, 573, 573, 424, 573, 419, 573, 573, 424, 573, 424, 573, 1218, 419, 1218, 1218, 1218, 427, 1218, 1218, 1218, 1218, 0, 0, 424, 0, 0, 538, 538, 538, 420, 424, 538, 419, 424, 538, 587, 424, 538, 0, 420, 538, 0, 419, 538, 0, 587, 538, 0, 0, 0, 420, 424, 0, 0, 424, 0, 420, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(0, 410), (1, 68), (3, 124), (5, 6), (7, 51), (15, 144), (17, 76), (18, 22), (19, 88), (51, 382), (52, 12), (53, 6), (55, 43), (60, 24), (61, 14), (63, 106), (261, 18), (263, 33), (271, 38), (282, 7), (283, 24), (311, 25), (316, 39), (317, 12), (319, 47), (344, 12), (783, 70), (797, 34), (799, 58), (831, 154), (884, 43), (888, 13), (892, 52), (963, 8), (967, 14), (975, 40), (983, 28), (989, 18), (991, 80), (1015, 70)]

theorem l0 : P.leaf 18 0 = 410 := by decide +kernel

theorem l1 : P.leaf 18 1 = 68 := by decide +kernel

theorem l3 : P.leaf 18 3 = 124 := by decide +kernel

theorem l5 : P.leaf 18 5 = 6 := by decide +kernel

theorem l7 : P.leaf 18 7 = 51 := by decide +kernel

theorem l15 : P.leaf 18 15 = 144 := by decide +kernel

theorem l17 : P.leaf 18 17 = 76 := by decide +kernel

theorem l18 : P.leaf 18 18 = 22 := by decide +kernel

theorem l19 : P.leaf 18 19 = 88 := by decide +kernel

theorem l51 : P.leaf 18 51 = 382 := by decide +kernel

theorem l52 : P.leaf 18 52 = 12 := by decide +kernel

theorem l53 : P.leaf 18 53 = 6 := by decide +kernel

theorem l55 : P.leaf 18 55 = 43 := by decide +kernel

theorem l60 : P.leaf 18 60 = 24 := by decide +kernel

theorem l61 : P.leaf 18 61 = 14 := by decide +kernel

theorem l63 : P.leaf 18 63 = 106 := by decide +kernel

theorem l261 : P.leaf 18 261 = 18 := by decide +kernel

theorem l263 : P.leaf 18 263 = 33 := by decide +kernel

theorem l271 : P.leaf 18 271 = 38 := by decide +kernel

theorem l282 : P.leaf 18 282 = 7 := by decide +kernel

theorem l283 : P.leaf 18 283 = 24 := by decide +kernel

theorem l311 : P.leaf 18 311 = 25 := by decide +kernel

theorem l316 : P.leaf 18 316 = 39 := by decide +kernel

theorem l317 : P.leaf 18 317 = 12 := by decide +kernel

theorem l319 : P.leaf 18 319 = 47 := by decide +kernel

theorem l344 : P.leaf 18 344 = 12 := by decide +kernel

theorem l783 : P.leaf 18 783 = 70 := by decide +kernel

theorem l797 : P.leaf 18 797 = 34 := by decide +kernel

theorem l799 : P.leaf 18 799 = 58 := by decide +kernel

theorem l831 : P.leaf 18 831 = 154 := by decide +kernel

theorem l884 : P.leaf 18 884 = 43 := by decide +kernel

theorem l888 : P.leaf 18 888 = 13 := by decide +kernel

theorem l892 : P.leaf 18 892 = 52 := by decide +kernel

theorem l963 : P.leaf 18 963 = 8 := by decide +kernel

theorem l967 : P.leaf 18 967 = 14 := by decide +kernel

theorem l975 : P.leaf 18 975 = 40 := by decide +kernel

theorem l983 : P.leaf 18 983 = 28 := by decide +kernel

theorem l989 : P.leaf 18 989 = 18 := by decide +kernel

theorem l991 : P.leaf 18 991 = 80 := by decide +kernel

theorem l1015 : P.leaf 18 1015 = 70 := by decide +kernel

theorem segOK : checkSeg 20 perms 0 1020 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 17586 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 0 1020 3346 17586 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.cons l0 (.cons l1 (.cons l3 (.cons l5 (.cons l7 (.cons l15 (.cons l17 (.cons l18 (.cons l19 (.cons l51 (.cons l52 (.cons l53 (.cons l55 (.cons l60 (.cons l61 (.cons l63 (.cons l261 (.cons l263 (.cons l271 (.cons l282 (.cons l283 (.cons l311 (.cons l316 (.cons l317 (.cons l319 (.cons l344 (.cons l783 (.cons l797 (.cons l799 (.cons l831 (.cons l884 (.cons l888 (.cons l892 (.cons l963 (.cons l967 (.cons l975 (.cons l983 (.cons l989 (.cons l991 (.cons l1015 (.nil))))))))))))))))))))))))))))))))))))))))))

end S0

end RACert.S0N3.C0
