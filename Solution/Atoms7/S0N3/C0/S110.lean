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

namespace S110

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(455550, 48), (455551, 48), (455616, 24), (455617, 48), (455619, 24), (455620, 48), (455621, 48), (455622, 48), (455623, 48), (455628, 24), (455629, 48), (455631, 24), (455632, 48), (455633, 48), (455634, 48), (455635, 48), (455636, 48), (455637, 48), (455638, 48), (455639, 48), (455640, 48), (455641, 48), (455642, 48), (455643, 48), (455644, 48), (455645, 48), (455646, 48), (455647, 48), (455664, 24), (455665, 48), (455667, 24), (455668, 48), (455669, 48), (455670, 48), (455671, 48), (455676, 24), (455677, 48), (455679, 24), (455936, 24), (455937, 48), (455939, 24), (455940, 48), (455941, 48), (455942, 48), (455943, 48), (455948, 24), (455949, 48), (455951, 24), (455952, 48), (455953, 48), (455954, 48), (455955, 48), (455956, 48), (455957, 48), (455958, 48), (455959, 48), (455960, 48), (455961, 48), (455962, 48), (455963, 48), (455964, 48), (455965, 48), (455966, 48), (455967, 48), (455984, 24), (455985, 48), (455987, 24), (455988, 48), (455989, 48), (455990, 48), (455991, 48), (455996, 24), (455997, 48), (455999, 24), (456000, 48), (456001, 48), (456002, 48), (456003, 48), (456004, 48), (456005, 48), (456006, 48), (456007, 48), (456008, 48), (456009, 48), (456010, 48), (456011, 48), (456012, 48), (456013, 48), (456014, 48), (456015, 48), (456016, 48), (456017, 48), (456018, 48), (456019, 48), (456020, 48), (456021, 48), (456022, 48), (456023, 48), (456024, 48), (456025, 48), (456026, 48), (456027, 48), (456028, 48), (456029, 48), (456030, 48), (456031, 48), (456032, 48), (456033, 48), (456034, 48), (456035, 48), (456036, 48), (456037, 48), (456038, 48), (456039, 48), (456040, 48), (456041, 48), (456042, 48), (456043, 48), (456044, 48), (456045, 48), (456046, 48), (456047, 48), (456048, 48), (456049, 48), (456050, 48), (456051, 48), (456052, 48)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 0, 418, 502, 0, 502, 502, 550, 0, 502, 502, 0, 550, 0, 550, 0, 550, 0, 550, 0, 550, 0, 550, 0, 550, 0, 550, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 418, 439, 602, 418, 502, 431, 602, 502, 502, 0, 434, 440, 431, 602, 550, 602, 431, 602, 550, 650, 550, 650, 550, 0, 550, 0, 434, 440, 602, 602, 602, 602, 602, 0, 0, 0, 418, 439, 550, 650, 418, 502, 550, 0, 424, 439, 550, 650, 502, 502, 550, 0, 550, 650, 550, 650, 550, 0, 550, 0, 550, 650, 550, 650, 550, 0, 550, 0, 502, 439, 650, 650, 502, 502, 0, 0, 502, 439, 650, 650, 502, 502, 0, 0, 650, 650, 650, 650, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(455550, 420), (455551, 758), (455619, 966), (455623, 1615), (455631, 3110), (455633, 218), (455635, 1231), (455637, 1062), (455639, 2039), (455641, 1153), (455643, 2054), (455645, 2400), (455647, 4630), (455664, 98), (455665, 284), (455667, 1944), (455668, 362), (455669, 1378), (455670, 1564), (455671, 3128), (455676, 1586), (455677, 3093), (455679, 8398), (455951, 132), (455965, 308), (455967, 460), (455996, 206), (455997, 490), (455999, 790), (456007, 344), (456015, 496), (456021, 617), (456023, 1419), (456029, 1386), (456031, 2465), (456038, 608), (456039, 1424), (456046, 1399), (456047, 2446), (456052, 248)]

theorem l455550 : P.leaf 18 455550 = 420 := by decide +kernel

theorem l455551 : P.leaf 18 455551 = 758 := by decide +kernel

theorem l455619 : P.leaf 18 455619 = 966 := by decide +kernel

theorem l455623 : P.leaf 18 455623 = 1615 := by decide +kernel

theorem l455631 : P.leaf 18 455631 = 3110 := by decide +kernel

theorem l455633 : P.leaf 18 455633 = 218 := by decide +kernel

theorem l455635 : P.leaf 18 455635 = 1231 := by decide +kernel

theorem l455637 : P.leaf 18 455637 = 1062 := by decide +kernel

theorem l455639 : P.leaf 18 455639 = 2039 := by decide +kernel

theorem l455641 : P.leaf 18 455641 = 1153 := by decide +kernel

theorem l455643 : P.leaf 18 455643 = 2054 := by decide +kernel

theorem l455645 : P.leaf 18 455645 = 2400 := by decide +kernel

theorem l455647 : P.leaf 18 455647 = 4630 := by decide +kernel

theorem l455664 : P.leaf 18 455664 = 98 := by decide +kernel

theorem l455665 : P.leaf 18 455665 = 284 := by decide +kernel

theorem l455667 : P.leaf 18 455667 = 1944 := by decide +kernel

theorem l455668 : P.leaf 18 455668 = 362 := by decide +kernel

theorem l455669 : P.leaf 18 455669 = 1378 := by decide +kernel

theorem l455670 : P.leaf 18 455670 = 1564 := by decide +kernel

theorem l455671 : P.leaf 18 455671 = 3128 := by decide +kernel

theorem l455676 : P.leaf 18 455676 = 1586 := by decide +kernel

theorem l455677 : P.leaf 18 455677 = 3093 := by decide +kernel

theorem l455679 : P.leaf 18 455679 = 8398 := by decide +kernel

theorem l455951 : P.leaf 18 455951 = 132 := by decide +kernel

theorem l455965 : P.leaf 18 455965 = 308 := by decide +kernel

theorem l455967 : P.leaf 18 455967 = 460 := by decide +kernel

theorem l455996 : P.leaf 18 455996 = 206 := by decide +kernel

theorem l455997 : P.leaf 18 455997 = 490 := by decide +kernel

theorem l455999 : P.leaf 18 455999 = 790 := by decide +kernel

theorem l456007 : P.leaf 18 456007 = 344 := by decide +kernel

theorem l456015 : P.leaf 18 456015 = 496 := by decide +kernel

theorem l456021 : P.leaf 18 456021 = 617 := by decide +kernel

theorem l456023 : P.leaf 18 456023 = 1419 := by decide +kernel

theorem l456029 : P.leaf 18 456029 = 1386 := by decide +kernel

theorem l456031 : P.leaf 18 456031 = 2465 := by decide +kernel

theorem l456038 : P.leaf 18 456038 = 608 := by decide +kernel

theorem l456039 : P.leaf 18 456039 = 1424 := by decide +kernel

theorem l456046 : P.leaf 18 456046 = 1399 := by decide +kernel

theorem l456047 : P.leaf 18 456047 = 2446 := by decide +kernel

theorem l456052 : P.leaf 18 456052 = 248 := by decide +kernel

theorem segOK : checkSeg 20 perms 455550 456053 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 2405472 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 455550 456053 5712 2405472 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.cons l455550 (.cons l455551 (.cons l455619 (.cons l455623 (.cons l455631 (.cons l455633 (.cons l455635 (.cons l455637 (.cons l455639 (.cons l455641 (.cons l455643 (.cons l455645 (.cons l455647 (.cons l455664 (.cons l455665 (.cons l455667 (.cons l455668 (.cons l455669 (.cons l455670 (.cons l455671 (.cons l455676 (.cons l455677 (.cons l455679 (.cons l455951 (.cons l455965 (.cons l455967 (.cons l455996 (.cons l455997 (.cons l455999 (.cons l456007 (.cons l456015 (.cons l456021 (.cons l456023 (.cons l456029 (.cons l456031 (.cons l456038 (.cons l456039 (.cons l456046 (.cons l456047 (.cons l456052 (.nil))))))))))))))))))))))))))))))))))))))))))

end S110

end RACert.S0N3.C0
