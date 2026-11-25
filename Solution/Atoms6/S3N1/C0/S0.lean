/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Atoms6.S3N1.C0.Defs

/-! Generated certificate segment; see `certgen`. -/

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option Elab.async false

@[expose] public section

namespace RACert.S3N1.C0

open RACert RACert.Problem

namespace S0

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(0, 1), (1, 3), (3, 3), (7, 1), (8, 6), (9, 12), (11, 6), (12, 6), (13, 12), (15, 6), (24, 3), (25, 6), (27, 3), (28, 3), (29, 6), (31, 3), (40, 6), (41, 6), (42, 12), (43, 12), (46, 6), (47, 6), (48, 6), (49, 6), (50, 12), (51, 12), (54, 6), (55, 6), (56, 12), (57, 12), (58, 12), (59, 12), (60, 12), (61, 12), (62, 12), (63, 12), (120, 3), (121, 3), (122, 6), (123, 6), (126, 3), (127, 3), (168, 6), (169, 12), (170, 6), (171, 12), (173, 6), (175, 6), (184, 6), (185, 12), (187, 6), (188, 6), (189, 12), (191, 6), (200, 2), (201, 6), (203, 6), (207, 2), (216, 6), (217, 12), (219, 6), (220, 6), (221, 12), (223, 6), (248, 6), (249, 6), (250, 12), (251, 12), (254, 6), (255, 6), (504, 1), (505, 3), (507, 3), (511, 1)]

/-- Evidence: `0` for a leaf evaluated below, `i + 1` for a leaf killed by the `i`-th quadruple. -/
def ev : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 31, 31, 0, 0, 0, 0, 59, 0, 0, 0, 0, 0, 31, 31, 0, 0, 0, 0, 0, 0, 57, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- Evaluated leaves `(α, value)`, part 0. -/
def live0 : List (ℕ × ℕ) :=
  [(0, 2928), (1, 848), (3, 555), (7, 1438), (8, 126), (9, 152), (11, 1064), (12, 0), (13, 68), (15, 843), (24, 769), (25, 1860), (27, 6790), (28, 861), (29, 2126), (31, 8300), (42, 0), (43, 264), (46, 384), (47, 2928), (49, 0), (50, 0), (51, 232), (54, 1134), (55, 5196), (58, 104), (59, 1780), (60, 1080), (61, 5484), (62, 10920), (63, 21164), (121, 23816), (122, 15574), (123, 67157), (126, 74230), (127, 128424), (168, 251), (169, 0), (170, 0), (171, 2112), (173, 4442), (175, 23451), (184, 521), (185, 0), (187, 6760), (188, 5706), (189, 25746), (191, 73495), (200, 286), (201, 1587), (203, 19749), (207, 54697), (216, 427), (217, 4213), (219, 30682), (220, 6451), (221, 44563), (223, 107436), (248, 765), (249, 54159), (250, 23778), (251, 121023), (254, 127172), (255, 280822), (504, 4142), (505, 148469), (507, 316268), (511, 592247)]

theorem leavesOK0 : P.checkLeavesR 21 qm live0 = true := by decide +kernel

/-- All evaluated leaves of this segment. -/
def live : List (ℕ × ℕ) := live0 ++ ([])

theorem segOK : checkSeg 9 perms 0 512 seg = true := by decide +kernel

theorem evOK : P.checkEvR 21 qmFlat seg ev live 0 11044515 = true := by decide +kernel

theorem total : OrbitSeg 9 perms (P.leaf 21) 0 512 512 11044515 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEvR_sum check rows flatOK evOK (.append (checkLeavesR_spec rows qmOK leavesOK0) (.nil)))

end S0

end RACert.S3N1.C0
