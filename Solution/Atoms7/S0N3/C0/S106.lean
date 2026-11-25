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

namespace S106

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(439998, 48), (439999, 48), (440053, 24), (440054, 48), (440055, 48), (440058, 24), (440059, 48), (440063, 24), (440159, 48), (440173, 24), (440175, 48), (440191, 24), (440215, 48), (440223, 48), (440229, 48), (440231, 48), (440237, 48), (440239, 48), (440245, 48), (440246, 24), (440247, 48), (440253, 48), (440254, 48), (440255, 48), (440279, 48), (440283, 16), (440287, 48), (440293, 48), (440295, 48), (440301, 48), (440303, 48), (440309, 48), (440311, 48), (440317, 48), (440318, 24), (440319, 48), (440741, 8), (440743, 48), (440751, 24), (440759, 24), (440765, 48), (440767, 48), (440821, 24), (440823, 48), (440831, 24), (441263, 48), (441279, 24), (441319, 16), (441327, 48), (441341, 24), (441343, 48), (442367, 8), (454656, 12), (454657, 48), (454659, 24), (454661, 24), (454662, 24), (454663, 48), (454671, 12), (454672, 48), (454673, 48), (454674, 48), (454675, 48), (454676, 48), (454677, 48), (454678, 48), (454679, 48), (454680, 48), (454681, 48), (454682, 48), (454683, 48), (454684, 48), (454685, 48), (454686, 48), (454687, 48), (454704, 24), (454705, 48), (454707, 24), (454708, 48), (454709, 48), (454710, 48), (454711, 48), (454716, 24), (454717, 48), (454719, 24), (454736, 24), (454737, 48), (454738, 48), (454739, 48), (454741, 24), (454742, 48), (454743, 48), (454746, 24), (454747, 48), (454751, 24), (454752, 24), (454753, 48), (454754, 48), (454755, 48), (454757, 48), (454758, 24), (454759, 48), (454761, 24), (454763, 48), (454767, 24), (454768, 48), (454769, 48), (454770, 48), (454771, 48), (454772, 48), (454773, 48), (454774, 48), (454775, 48), (454776, 48), (454777, 48), (454778, 48), (454779, 48), (454780, 48), (454781, 48), (454782, 48)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 502, 0, 0, 602, 0, 502, 602, 502, 0, 602, 602, 602, 0, 0, 0, 0, 0, 0, 502, 0, 502, 0, 0, 0, 0, 0, 0, 502, 602, 1302, 602, 1302, 1302, 1302, 1302, 1302, 0, 0, 0, 0, 0, 0, 0, 418, 434, 434, 502, 550, 602, 1218, 434, 434, 434, 434, 550, 602, 550, 602, 550, 650, 550, 650, 550, 1218, 550, 1218, 434, 434, 434, 602, 602, 602, 602, 1218, 1218, 1218, 550, 650, 550, 650, 1218, 550, 1218, 550, 650, 1218, 502, 502, 650, 650, 502, 1224, 1224, 502, 650, 1224, 650, 650, 650, 650, 0, 0, 0, 0, 650, 650, 650, 650, 0, 0, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(439998, 450), (439999, 1527), (440053, 1200), (440054, 253), (440055, 2569), (440058, 336), (440059, 1377), (440063, 5912), (440159, 1553), (440175, 1928), (440191, 4068), (440223, 2068), (440239, 2299), (440253, 2490), (440254, 2186), (440255, 4864), (440279, 2034), (440283, 1690), (440287, 3846), (440295, 2519), (440303, 4477), (440309, 2290), (440311, 4945), (440317, 4837), (440318, 4227), (440319, 10036), (441263, 2938), (441279, 5677), (441319, 3147), (441327, 5649), (441341, 5252), (441343, 10760), (442367, 20068), (454772, 19), (454773, 130), (454774, 63), (454775, 306), (454780, 136), (454781, 264), (454782, 296)]

theorem l439998 : P.leaf 18 439998 = 450 := by decide +kernel

theorem l439999 : P.leaf 18 439999 = 1527 := by decide +kernel

theorem l440053 : P.leaf 18 440053 = 1200 := by decide +kernel

theorem l440054 : P.leaf 18 440054 = 253 := by decide +kernel

theorem l440055 : P.leaf 18 440055 = 2569 := by decide +kernel

theorem l440058 : P.leaf 18 440058 = 336 := by decide +kernel

theorem l440059 : P.leaf 18 440059 = 1377 := by decide +kernel

theorem l440063 : P.leaf 18 440063 = 5912 := by decide +kernel

theorem l440159 : P.leaf 18 440159 = 1553 := by decide +kernel

theorem l440175 : P.leaf 18 440175 = 1928 := by decide +kernel

theorem l440191 : P.leaf 18 440191 = 4068 := by decide +kernel

theorem l440223 : P.leaf 18 440223 = 2068 := by decide +kernel

theorem l440239 : P.leaf 18 440239 = 2299 := by decide +kernel

theorem l440253 : P.leaf 18 440253 = 2490 := by decide +kernel

theorem l440254 : P.leaf 18 440254 = 2186 := by decide +kernel

theorem l440255 : P.leaf 18 440255 = 4864 := by decide +kernel

theorem l440279 : P.leaf 18 440279 = 2034 := by decide +kernel

theorem l440283 : P.leaf 18 440283 = 1690 := by decide +kernel

theorem l440287 : P.leaf 18 440287 = 3846 := by decide +kernel

theorem l440295 : P.leaf 18 440295 = 2519 := by decide +kernel

theorem l440303 : P.leaf 18 440303 = 4477 := by decide +kernel

theorem l440309 : P.leaf 18 440309 = 2290 := by decide +kernel

theorem l440311 : P.leaf 18 440311 = 4945 := by decide +kernel

theorem l440317 : P.leaf 18 440317 = 4837 := by decide +kernel

theorem l440318 : P.leaf 18 440318 = 4227 := by decide +kernel

theorem l440319 : P.leaf 18 440319 = 10036 := by decide +kernel

theorem l441263 : P.leaf 18 441263 = 2938 := by decide +kernel

theorem l441279 : P.leaf 18 441279 = 5677 := by decide +kernel

theorem l441319 : P.leaf 18 441319 = 3147 := by decide +kernel

theorem l441327 : P.leaf 18 441327 = 5649 := by decide +kernel

theorem l441341 : P.leaf 18 441341 = 5252 := by decide +kernel

theorem l441343 : P.leaf 18 441343 = 10760 := by decide +kernel

theorem l442367 : P.leaf 18 442367 = 20068 := by decide +kernel

theorem l454772 : P.leaf 18 454772 = 19 := by decide +kernel

theorem l454773 : P.leaf 18 454773 = 130 := by decide +kernel

theorem l454774 : P.leaf 18 454774 = 63 := by decide +kernel

theorem l454775 : P.leaf 18 454775 = 306 := by decide +kernel

theorem l454780 : P.leaf 18 454780 = 136 := by decide +kernel

theorem l454781 : P.leaf 18 454781 = 264 := by decide +kernel

theorem l454782 : P.leaf 18 454782 = 296 := by decide +kernel

theorem segOK : checkSeg 20 perms 439998 454783 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 4675296 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 439998 454783 4872 4675296 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.cons l439998 (.cons l439999 (.cons l440053 (.cons l440054 (.cons l440055 (.cons l440058 (.cons l440059 (.cons l440063 (.cons l440159 (.cons l440175 (.cons l440191 (.cons l440223 (.cons l440239 (.cons l440253 (.cons l440254 (.cons l440255 (.cons l440279 (.cons l440283 (.cons l440287 (.cons l440295 (.cons l440303 (.cons l440309 (.cons l440311 (.cons l440317 (.cons l440318 (.cons l440319 (.cons l441263 (.cons l441279 (.cons l441319 (.cons l441327 (.cons l441341 (.cons l441343 (.cons l442367 (.cons l454772 (.cons l454773 (.cons l454774 (.cons l454775 (.cons l454780 (.cons l454781 (.cons l454782 (.nil))))))))))))))))))))))))))))))))))))))))))

end S106

end RACert.S0N3.C0
