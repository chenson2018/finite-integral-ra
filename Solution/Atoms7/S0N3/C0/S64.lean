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

namespace S64

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(130903, 48), (130904, 48), (130905, 48), (130906, 48), (130907, 48), (130908, 48), (130909, 48), (130910, 48), (130911, 48), (130912, 24), (130913, 48), (130914, 48), (130915, 48), (130917, 48), (130918, 24), (130919, 48), (130921, 24), (130923, 48), (130927, 24), (130928, 48), (130929, 48), (130930, 48), (130931, 48), (130932, 48), (130933, 48), (130934, 48), (130935, 48), (130936, 48), (130937, 48), (130938, 48), (130939, 48), (130940, 48), (130941, 48), (130942, 48), (130943, 48), (130960, 24), (130961, 48), (130962, 48), (130963, 48), (130965, 48), (130966, 24), (130967, 48), (130969, 24), (130971, 48), (130975, 24), (130992, 48), (130993, 48), (130994, 48), (130995, 48), (130996, 48), (130997, 48), (130998, 48), (130999, 48), (131000, 48), (131001, 48), (131002, 48), (131003, 48), (131004, 48), (131005, 48), (131006, 48), (131007, 48), (131056, 24), (131057, 48), (131058, 48), (131059, 48), (131061, 48), (131062, 24), (131063, 48), (131065, 24), (131067, 48), (131071, 24), (237568, 6), (237569, 24), (237571, 12), (237572, 12), (237573, 24), (237575, 12), (237576, 12), (237577, 24), (237579, 12), (237580, 12), (237581, 24), (237583, 12), (237584, 24), (237585, 24), (237586, 24), (237587, 24), (237588, 24), (237589, 24), (237590, 24), (237591, 24), (237592, 24), (237593, 24), (237594, 24), (237595, 24), (237596, 24), (237597, 24), (237598, 24), (237599, 24), (237616, 12), (237617, 24), (237619, 12), (237620, 12)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 438, 439, 438, 440, 550, 0, 550, 0, 502, 432, 438, 440, 418, 0, 0, 418, 440, 0, 650, 439, 438, 440, 0, 0, 0, 0, 438, 439, 438, 440, 0, 0, 0, 0, 550, 439, 550, 602, 602, 550, 602, 439, 0, 0, 602, 439, 602, 602, 602, 602, 602, 602, 439, 439, 0, 0, 0, 0, 0, 0, 0, 439, 0, 0, 0, 0, 0, 439, 0, 0, 434, 434, 434, 0, 573, 517, 0, 573, 517, 0, 573, 517, 434, 434, 434, 434, 573, 0, 573, 0, 0, 573, 0, 573, 573, 0, 573, 0, 434, 434, 434, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(130903, 1740), (130909, 1670), (130911, 2971), (130918, 762), (130919, 1204), (130927, 2107), (130932, 332), (130933, 1148), (130934, 968), (130935, 2344), (130940, 552), (130941, 1980), (130942, 1640), (130943, 4612), (130971, 2184), (130975, 4139), (131002, 1184), (131003, 2382), (131004, 792), (131005, 2608), (131006, 2688), (131007, 6404), (131056, 0), (131058, 400), (131059, 792), (131061, 1492), (131062, 1788), (131063, 3412), (131067, 2844), (131071, 8388), (237572, 12), (237576, 14), (237580, 24), (237589, 4), (237591, 24), (237592, 8), (237594, 5), (237597, 6), (237599, 32), (237620, 8)]

theorem l130903 : P.leaf 18 130903 = 1740 := by decide +kernel

theorem l130909 : P.leaf 18 130909 = 1670 := by decide +kernel

theorem l130911 : P.leaf 18 130911 = 2971 := by decide +kernel

theorem l130918 : P.leaf 18 130918 = 762 := by decide +kernel

theorem l130919 : P.leaf 18 130919 = 1204 := by decide +kernel

theorem l130927 : P.leaf 18 130927 = 2107 := by decide +kernel

theorem l130932 : P.leaf 18 130932 = 332 := by decide +kernel

theorem l130933 : P.leaf 18 130933 = 1148 := by decide +kernel

theorem l130934 : P.leaf 18 130934 = 968 := by decide +kernel

theorem l130935 : P.leaf 18 130935 = 2344 := by decide +kernel

theorem l130940 : P.leaf 18 130940 = 552 := by decide +kernel

theorem l130941 : P.leaf 18 130941 = 1980 := by decide +kernel

theorem l130942 : P.leaf 18 130942 = 1640 := by decide +kernel

theorem l130943 : P.leaf 18 130943 = 4612 := by decide +kernel

theorem l130971 : P.leaf 18 130971 = 2184 := by decide +kernel

theorem l130975 : P.leaf 18 130975 = 4139 := by decide +kernel

theorem l131002 : P.leaf 18 131002 = 1184 := by decide +kernel

theorem l131003 : P.leaf 18 131003 = 2382 := by decide +kernel

theorem l131004 : P.leaf 18 131004 = 792 := by decide +kernel

theorem l131005 : P.leaf 18 131005 = 2608 := by decide +kernel

theorem l131006 : P.leaf 18 131006 = 2688 := by decide +kernel

theorem l131007 : P.leaf 18 131007 = 6404 := by decide +kernel

theorem l131056 : P.leaf 18 131056 = 0 := by decide +kernel

theorem l131058 : P.leaf 18 131058 = 400 := by decide +kernel

theorem l131059 : P.leaf 18 131059 = 792 := by decide +kernel

theorem l131061 : P.leaf 18 131061 = 1492 := by decide +kernel

theorem l131062 : P.leaf 18 131062 = 1788 := by decide +kernel

theorem l131063 : P.leaf 18 131063 = 3412 := by decide +kernel

theorem l131067 : P.leaf 18 131067 = 2844 := by decide +kernel

theorem l131071 : P.leaf 18 131071 = 8388 := by decide +kernel

theorem l237572 : P.leaf 18 237572 = 12 := by decide +kernel

theorem l237576 : P.leaf 18 237576 = 14 := by decide +kernel

theorem l237580 : P.leaf 18 237580 = 24 := by decide +kernel

theorem l237589 : P.leaf 18 237589 = 4 := by decide +kernel

theorem l237591 : P.leaf 18 237591 = 24 := by decide +kernel

theorem l237592 : P.leaf 18 237592 = 8 := by decide +kernel

theorem l237594 : P.leaf 18 237594 = 5 := by decide +kernel

theorem l237597 : P.leaf 18 237597 = 6 := by decide +kernel

theorem l237599 : P.leaf 18 237599 = 32 := by decide +kernel

theorem l237620 : P.leaf 18 237620 = 8 := by decide +kernel

theorem segOK : checkSeg 20 perms 130903 237621 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 2735472 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 130903 237621 3750 2735472 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.cons l130903 (.cons l130909 (.cons l130911 (.cons l130918 (.cons l130919 (.cons l130927 (.cons l130932 (.cons l130933 (.cons l130934 (.cons l130935 (.cons l130940 (.cons l130941 (.cons l130942 (.cons l130943 (.cons l130971 (.cons l130975 (.cons l131002 (.cons l131003 (.cons l131004 (.cons l131005 (.cons l131006 (.cons l131007 (.cons l131056 (.cons l131058 (.cons l131059 (.cons l131061 (.cons l131062 (.cons l131063 (.cons l131067 (.cons l131071 (.cons l237572 (.cons l237576 (.cons l237580 (.cons l237589 (.cons l237591 (.cons l237592 (.cons l237594 (.cons l237597 (.cons l237599 (.cons l237620 (.nil))))))))))))))))))))))))))))))))))))))))))

end S64

end RACert.S0N3.C0
