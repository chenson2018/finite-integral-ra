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

namespace S90

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(258876, 24), (258877, 48), (258879, 24), (258881, 48), (258883, 24), (258885, 48), (258887, 24), (258889, 48), (258891, 24), (258893, 48), (258895, 24), (258897, 48), (258898, 48), (258899, 48), (258901, 48), (258902, 48), (258903, 48), (258905, 48), (258906, 48), (258907, 48), (258909, 48), (258910, 48), (258911, 48), (258929, 48), (258931, 24), (258932, 24), (258933, 48), (258935, 24), (258936, 12), (258937, 48), (258939, 24), (258940, 24), (258941, 48), (258943, 24), (258945, 48), (258947, 24), (258949, 48), (258951, 24), (258953, 48), (258955, 24), (258957, 48), (258959, 24), (258961, 48), (258962, 48), (258963, 48), (258965, 48), (258966, 48), (258967, 48), (258969, 48), (258970, 48), (258971, 48), (258973, 48), (258974, 48), (258975, 48), (258993, 48), (258995, 24), (258996, 12), (258997, 48), (258999, 24), (259001, 48), (259003, 24), (259004, 24), (259005, 48), (259007, 24), (259009, 48), (259011, 24), (259013, 48), (259015, 24), (259017, 48), (259019, 24), (259021, 48)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 0, 0, 439, 650, 502, 0, 439, 650, 502, 0, 439, 438, 650, 0, 550, 0, 439, 438, 650, 0, 550, 0, 439, 650, 0, 0, 0, 650, 439, 650, 0, 0, 0, 502, 0, 502, 0, 502, 0, 502, 0, 0, 550, 0, 0, 550, 0, 0, 550, 0, 0, 550, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 502, 0, 502, 0, 502, 0, 502]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(258876, 36), (258877, 72), (258879, 192), (258887, 363), (258895, 470), (258901, 238), (258903, 444), (258909, 310), (258911, 590), (258932, 92), (258933, 238), (258935, 516), (258940, 160), (258941, 310), (258943, 702), (258947, 96), (258951, 444), (258955, 540), (258959, 1276), (258961, 72), (258963, 128), (258965, 321), (258967, 575), (258969, 358), (258971, 640), (258973, 808), (258975, 1640), (258993, 96), (258995, 176), (258996, 144), (258997, 508), (258999, 884), (259001, 470), (259003, 796), (259004, 552), (259005, 904), (259007, 1880), (259011, 264), (259015, 1972), (259019, 898)]

theorem l258876 : P.leaf 18 258876 = 36 := by decide +kernel

theorem l258877 : P.leaf 18 258877 = 72 := by decide +kernel

theorem l258879 : P.leaf 18 258879 = 192 := by decide +kernel

theorem l258887 : P.leaf 18 258887 = 363 := by decide +kernel

theorem l258895 : P.leaf 18 258895 = 470 := by decide +kernel

theorem l258901 : P.leaf 18 258901 = 238 := by decide +kernel

theorem l258903 : P.leaf 18 258903 = 444 := by decide +kernel

theorem l258909 : P.leaf 18 258909 = 310 := by decide +kernel

theorem l258911 : P.leaf 18 258911 = 590 := by decide +kernel

theorem l258932 : P.leaf 18 258932 = 92 := by decide +kernel

theorem l258933 : P.leaf 18 258933 = 238 := by decide +kernel

theorem l258935 : P.leaf 18 258935 = 516 := by decide +kernel

theorem l258940 : P.leaf 18 258940 = 160 := by decide +kernel

theorem l258941 : P.leaf 18 258941 = 310 := by decide +kernel

theorem l258943 : P.leaf 18 258943 = 702 := by decide +kernel

theorem l258947 : P.leaf 18 258947 = 96 := by decide +kernel

theorem l258951 : P.leaf 18 258951 = 444 := by decide +kernel

theorem l258955 : P.leaf 18 258955 = 540 := by decide +kernel

theorem l258959 : P.leaf 18 258959 = 1276 := by decide +kernel

theorem l258961 : P.leaf 18 258961 = 72 := by decide +kernel

theorem l258963 : P.leaf 18 258963 = 128 := by decide +kernel

theorem l258965 : P.leaf 18 258965 = 321 := by decide +kernel

theorem l258967 : P.leaf 18 258967 = 575 := by decide +kernel

theorem l258969 : P.leaf 18 258969 = 358 := by decide +kernel

theorem l258971 : P.leaf 18 258971 = 640 := by decide +kernel

theorem l258973 : P.leaf 18 258973 = 808 := by decide +kernel

theorem l258975 : P.leaf 18 258975 = 1640 := by decide +kernel

theorem l258993 : P.leaf 18 258993 = 96 := by decide +kernel

theorem l258995 : P.leaf 18 258995 = 176 := by decide +kernel

theorem l258996 : P.leaf 18 258996 = 144 := by decide +kernel

theorem l258997 : P.leaf 18 258997 = 508 := by decide +kernel

theorem l258999 : P.leaf 18 258999 = 884 := by decide +kernel

theorem l259001 : P.leaf 18 259001 = 470 := by decide +kernel

theorem l259003 : P.leaf 18 259003 = 796 := by decide +kernel

theorem l259004 : P.leaf 18 259004 = 552 := by decide +kernel

theorem l259005 : P.leaf 18 259005 = 904 := by decide +kernel

theorem l259007 : P.leaf 18 259007 = 1880 := by decide +kernel

theorem l259011 : P.leaf 18 259011 = 264 := by decide +kernel

theorem l259015 : P.leaf 18 259015 = 1972 := by decide +kernel

theorem l259019 : P.leaf 18 259019 = 898 := by decide +kernel

theorem segOK : checkSeg 20 perms 258876 259023 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 715800 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 258876 259023 2760 715800 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.cons l258876 (.cons l258877 (.cons l258879 (.cons l258887 (.cons l258895 (.cons l258901 (.cons l258903 (.cons l258909 (.cons l258911 (.cons l258932 (.cons l258933 (.cons l258935 (.cons l258940 (.cons l258941 (.cons l258943 (.cons l258947 (.cons l258951 (.cons l258955 (.cons l258959 (.cons l258961 (.cons l258963 (.cons l258965 (.cons l258967 (.cons l258969 (.cons l258971 (.cons l258973 (.cons l258975 (.cons l258993 (.cons l258995 (.cons l258996 (.cons l258997 (.cons l258999 (.cons l259001 (.cons l259003 (.cons l259004 (.cons l259005 (.cons l259007 (.cons l259011 (.cons l259015 (.cons l259019 (.nil))))))))))))))))))))))))))))))))))))))))))

end S90

end RACert.S0N3.C0
