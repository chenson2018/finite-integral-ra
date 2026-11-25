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

namespace S71

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(239058, 24), (239059, 24), (239062, 24), (239063, 24), (239066, 24), (239067, 24), (239069, 12), (239070, 24), (239071, 24), (239073, 24), (239075, 24), (239077, 24), (239079, 24), (239081, 24), (239083, 24), (239085, 24), (239086, 12), (239087, 24), (239089, 24), (239090, 24), (239091, 24), (239093, 24), (239094, 24), (239095, 24), (239097, 24), (239098, 24), (239099, 24), (239101, 24), (239102, 24), (239103, 24), (239107, 24), (239111, 24), (239115, 24), (239119, 24), (239122, 12), (239123, 24), (239126, 24), (239127, 24), (239130, 24), (239131, 24), (239134, 24), (239135, 24), (239137, 12), (239139, 24), (239141, 24), (239143, 24), (239145, 24), (239147, 24), (239149, 24), (239151, 24), (239153, 24), (239154, 24), (239155, 24), (239157, 24), (239158, 24), (239159, 24), (239161, 24), (239162, 24), (239163, 24), (239165, 24), (239166, 24), (239167, 24), (239171, 24), (239175, 24), (239179, 24), (239183, 24), (239187, 24), (239190, 24), (239191, 24), (239194, 12), (239195, 24), (239198, 24), (239199, 24), (239203, 24), (239205, 24), (239207, 24)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 0, 424, 0, 0, 0, 0, 424, 0, 0, 0, 0, 0, 418, 0, 418, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 440, 517, 440, 517, 426, 440, 0, 0, 424, 440, 424, 0, 0, 440, 418, 0, 0, 440, 418, 0, 538, 426, 440, 0, 0, 0, 538, 426, 440, 0, 0, 0, 440, 517, 440, 517, 440, 1224, 1224, 424, 440, 424, 1224, 440, 418, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(239058, 0), (239059, 72), (239063, 639), (239066, 18), (239067, 158), (239069, 213), (239071, 834), (239073, 14), (239075, 76), (239077, 65), (239079, 752), (239083, 184), (239086, 276), (239087, 1060), (239089, 104), (239090, 56), (239091, 176), (239093, 383), (239094, 392), (239095, 1336), (239097, 163), (239098, 178), (239099, 378), (239101, 458), (239102, 472), (239103, 1932), (239126, 0), (239127, 18), (239135, 32), (239137, 32), (239143, 0), (239145, 70), (239151, 0), (239157, 20), (239158, 0), (239159, 102), (239165, 22), (239166, 20), (239167, 140), (239207, 142)]

theorem l239058 : P.leaf 18 239058 = 0 := by decide +kernel

theorem l239059 : P.leaf 18 239059 = 72 := by decide +kernel

theorem l239063 : P.leaf 18 239063 = 639 := by decide +kernel

theorem l239066 : P.leaf 18 239066 = 18 := by decide +kernel

theorem l239067 : P.leaf 18 239067 = 158 := by decide +kernel

theorem l239069 : P.leaf 18 239069 = 213 := by decide +kernel

theorem l239071 : P.leaf 18 239071 = 834 := by decide +kernel

theorem l239073 : P.leaf 18 239073 = 14 := by decide +kernel

theorem l239075 : P.leaf 18 239075 = 76 := by decide +kernel

theorem l239077 : P.leaf 18 239077 = 65 := by decide +kernel

theorem l239079 : P.leaf 18 239079 = 752 := by decide +kernel

theorem l239083 : P.leaf 18 239083 = 184 := by decide +kernel

theorem l239086 : P.leaf 18 239086 = 276 := by decide +kernel

theorem l239087 : P.leaf 18 239087 = 1060 := by decide +kernel

theorem l239089 : P.leaf 18 239089 = 104 := by decide +kernel

theorem l239090 : P.leaf 18 239090 = 56 := by decide +kernel

theorem l239091 : P.leaf 18 239091 = 176 := by decide +kernel

theorem l239093 : P.leaf 18 239093 = 383 := by decide +kernel

theorem l239094 : P.leaf 18 239094 = 392 := by decide +kernel

theorem l239095 : P.leaf 18 239095 = 1336 := by decide +kernel

theorem l239097 : P.leaf 18 239097 = 163 := by decide +kernel

theorem l239098 : P.leaf 18 239098 = 178 := by decide +kernel

theorem l239099 : P.leaf 18 239099 = 378 := by decide +kernel

theorem l239101 : P.leaf 18 239101 = 458 := by decide +kernel

theorem l239102 : P.leaf 18 239102 = 472 := by decide +kernel

theorem l239103 : P.leaf 18 239103 = 1932 := by decide +kernel

theorem l239126 : P.leaf 18 239126 = 0 := by decide +kernel

theorem l239127 : P.leaf 18 239127 = 18 := by decide +kernel

theorem l239135 : P.leaf 18 239135 = 32 := by decide +kernel

theorem l239137 : P.leaf 18 239137 = 32 := by decide +kernel

theorem l239143 : P.leaf 18 239143 = 0 := by decide +kernel

theorem l239145 : P.leaf 18 239145 = 70 := by decide +kernel

theorem l239151 : P.leaf 18 239151 = 0 := by decide +kernel

theorem l239157 : P.leaf 18 239157 = 20 := by decide +kernel

theorem l239158 : P.leaf 18 239158 = 0 := by decide +kernel

theorem l239159 : P.leaf 18 239159 = 102 := by decide +kernel

theorem l239165 : P.leaf 18 239165 = 22 := by decide +kernel

theorem l239166 : P.leaf 18 239166 = 20 := by decide +kernel

theorem l239167 : P.leaf 18 239167 = 140 := by decide +kernel

theorem l239207 : P.leaf 18 239207 = 142 := by decide +kernel

theorem segOK : checkSeg 20 perms 239058 239209 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 257436 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 239058 239209 1764 257436 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.cons l239058 (.cons l239059 (.cons l239063 (.cons l239066 (.cons l239067 (.cons l239069 (.cons l239071 (.cons l239073 (.cons l239075 (.cons l239077 (.cons l239079 (.cons l239083 (.cons l239086 (.cons l239087 (.cons l239089 (.cons l239090 (.cons l239091 (.cons l239093 (.cons l239094 (.cons l239095 (.cons l239097 (.cons l239098 (.cons l239099 (.cons l239101 (.cons l239102 (.cons l239103 (.cons l239126 (.cons l239127 (.cons l239135 (.cons l239137 (.cons l239143 (.cons l239145 (.cons l239151 (.cons l239157 (.cons l239158 (.cons l239159 (.cons l239165 (.cons l239166 (.cons l239167 (.cons l239207 (.nil))))))))))))))))))))))))))))))))))))))))))

end S71

end RACert.S0N3.C0
