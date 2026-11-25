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

namespace S121

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(516654, 24), (516655, 24), (516667, 12), (516668, 24), (516669, 24), (516670, 24), (516671, 24), (516673, 8), (516675, 24), (516677, 24), (516679, 24), (516681, 24), (516683, 24), (516685, 24), (516687, 24), (516690, 24), (516691, 24), (516693, 24), (516694, 24), (516695, 24), (516697, 24), (516698, 24), (516699, 24), (516701, 24), (516702, 24), (516703, 24), (516706, 24), (516707, 24), (516708, 24), (516709, 24), (516710, 24), (516711, 24), (516712, 12), (516713, 24), (516714, 24), (516715, 24), (516716, 24), (516717, 24), (516718, 24), (516719, 24), (516722, 24), (516723, 24), (516724, 24), (516725, 24), (516726, 24), (516727, 24), (516728, 24), (516729, 24), (516730, 24), (516731, 24), (516732, 24), (516733, 24), (516734, 24), (516735, 24), (516743, 24), (516747, 24), (516751, 24), (516757, 24), (516758, 24), (516759, 24), (516761, 24), (516762, 24), (516763, 24), (516765, 24), (516766, 24), (516767, 24), (516772, 12), (516773, 24), (516774, 24), (516775, 24), (516777, 24), (516778, 24), (516779, 24), (516780, 24), (516781, 24), (516782, 24), (516783, 24), (516788, 24), (516789, 24), (516790, 24), (516791, 24), (516792, 24), (516793, 24), (516794, 24), (516795, 24), (516796, 24), (516797, 24), (516798, 24), (516799, 24), (516803, 24), (516807, 24), (516811, 24), (516815, 24), (516817, 24), (516818, 24), (516819, 24), (516821, 24), (516822, 24), (516823, 24), (516825, 24), (516826, 24), (516827, 24), (516829, 24), (516830, 24), (516831, 24), (516833, 24), (516834, 24), (516835, 24), (516837, 24), (516838, 24), (516839, 24), (516841, 24), (516842, 24), (516843, 24), (516844, 12), (516845, 24), (516846, 24), (516847, 24), (516848, 24), (516849, 24), (516850, 24), (516851, 24), (516852, 24), (516853, 24), (516854, 24), (516855, 24), (516856, 24), (516857, 24), (516858, 24), (516859, 24), (516860, 24), (516861, 24), (516862, 24), (516863, 24), (516879, 24), (516893, 24), (516894, 12), (516895, 24), (516909, 12), (516911, 24), (516927, 12), (516935, 24)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 538, 418, 0, 0, 538, 418, 0, 538, 538, 1224, 1224, 1224, 1224, 538, 538, 1224, 1224, 1224, 538, 538, 418, 418, 0, 0, 0, 0, 538, 538, 418, 418, 0, 0, 538, 538, 1224, 1224, 1224, 1224, 1224, 1224, 538, 538, 1224, 1224, 1224, 1224, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 418, 418, 1224, 1224, 517, 1224, 1224, 418, 418, 1224, 1224, 1224, 1224, 1224, 1224, 1224, 1224, 1224, 1224, 1224, 1224, 1224, 1224, 0, 0, 0, 0, 1224, 1224, 1224, 1224, 1224, 1224, 1224, 1224, 1224, 1224, 1224, 1224, 517, 1224, 1224, 418, 1224, 1224, 517, 1224, 1224, 418, 418, 1224, 1224, 1224, 1224, 1224, 1224, 1224, 1224, 1224, 1224, 1224, 1224, 1224, 1224, 1224, 1224, 1224, 1224, 0, 0, 0, 0, 418, 0, 0, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(516654, 0), (516655, 0), (516667, 349), (516668, 0), (516669, 0), (516670, 0), (516671, 0), (516673, 64), (516679, 24), (516681, 152), (516687, 99), (516710, 88), (516711, 128), (516712, 196), (516713, 400), (516718, 342), (516719, 649), (516743, 63), (516747, 66), (516751, 171), (516757, 33), (516758, 74), (516759, 129), (516761, 16), (516762, 148), (516763, 148), (516765, 88), (516766, 524), (516767, 524), (516803, 68), (516807, 334), (516811, 83), (516815, 467), (516879, 80), (516893, 94), (516894, 153), (516895, 198), (516911, 104), (516927, 216), (516935, 238)]

theorem l516654 : P.leaf 18 516654 = 0 := by decide +kernel

theorem l516655 : P.leaf 18 516655 = 0 := by decide +kernel

theorem l516667 : P.leaf 18 516667 = 349 := by decide +kernel

theorem l516668 : P.leaf 18 516668 = 0 := by decide +kernel

theorem l516669 : P.leaf 18 516669 = 0 := by decide +kernel

theorem l516670 : P.leaf 18 516670 = 0 := by decide +kernel

theorem l516671 : P.leaf 18 516671 = 0 := by decide +kernel

theorem l516673 : P.leaf 18 516673 = 64 := by decide +kernel

theorem l516679 : P.leaf 18 516679 = 24 := by decide +kernel

theorem l516681 : P.leaf 18 516681 = 152 := by decide +kernel

theorem l516687 : P.leaf 18 516687 = 99 := by decide +kernel

theorem l516710 : P.leaf 18 516710 = 88 := by decide +kernel

theorem l516711 : P.leaf 18 516711 = 128 := by decide +kernel

theorem l516712 : P.leaf 18 516712 = 196 := by decide +kernel

theorem l516713 : P.leaf 18 516713 = 400 := by decide +kernel

theorem l516718 : P.leaf 18 516718 = 342 := by decide +kernel

theorem l516719 : P.leaf 18 516719 = 649 := by decide +kernel

theorem l516743 : P.leaf 18 516743 = 63 := by decide +kernel

theorem l516747 : P.leaf 18 516747 = 66 := by decide +kernel

theorem l516751 : P.leaf 18 516751 = 171 := by decide +kernel

theorem l516757 : P.leaf 18 516757 = 33 := by decide +kernel

theorem l516758 : P.leaf 18 516758 = 74 := by decide +kernel

theorem l516759 : P.leaf 18 516759 = 129 := by decide +kernel

theorem l516761 : P.leaf 18 516761 = 16 := by decide +kernel

theorem l516762 : P.leaf 18 516762 = 148 := by decide +kernel

theorem l516763 : P.leaf 18 516763 = 148 := by decide +kernel

theorem l516765 : P.leaf 18 516765 = 88 := by decide +kernel

theorem l516766 : P.leaf 18 516766 = 524 := by decide +kernel

theorem l516767 : P.leaf 18 516767 = 524 := by decide +kernel

theorem l516803 : P.leaf 18 516803 = 68 := by decide +kernel

theorem l516807 : P.leaf 18 516807 = 334 := by decide +kernel

theorem l516811 : P.leaf 18 516811 = 83 := by decide +kernel

theorem l516815 : P.leaf 18 516815 = 467 := by decide +kernel

theorem l516879 : P.leaf 18 516879 = 80 := by decide +kernel

theorem l516893 : P.leaf 18 516893 = 94 := by decide +kernel

theorem l516894 : P.leaf 18 516894 = 153 := by decide +kernel

theorem l516895 : P.leaf 18 516895 = 198 := by decide +kernel

theorem l516911 : P.leaf 18 516911 = 104 := by decide +kernel

theorem l516927 : P.leaf 18 516927 = 216 := by decide +kernel

theorem l516935 : P.leaf 18 516935 = 238 := by decide +kernel

theorem segOK : checkSeg 20 perms 516654 516939 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 144248 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 516654 516939 3308 144248 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.cons l516654 (.cons l516655 (.cons l516667 (.cons l516668 (.cons l516669 (.cons l516670 (.cons l516671 (.cons l516673 (.cons l516679 (.cons l516681 (.cons l516687 (.cons l516710 (.cons l516711 (.cons l516712 (.cons l516713 (.cons l516718 (.cons l516719 (.cons l516743 (.cons l516747 (.cons l516751 (.cons l516757 (.cons l516758 (.cons l516759 (.cons l516761 (.cons l516762 (.cons l516763 (.cons l516765 (.cons l516766 (.cons l516767 (.cons l516803 (.cons l516807 (.cons l516811 (.cons l516815 (.cons l516879 (.cons l516893 (.cons l516894 (.cons l516895 (.cons l516911 (.cons l516927 (.cons l516935 (.nil))))))))))))))))))))))))))))))))))))))))))

end S121

end RACert.S0N3.C0
