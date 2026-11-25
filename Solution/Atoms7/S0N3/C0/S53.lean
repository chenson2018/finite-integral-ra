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

namespace S53

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(125895, 48), (125896, 48), (125897, 48), (125898, 48), (125899, 48), (125900, 48), (125901, 48), (125902, 48), (125903, 48), (125904, 48), (125905, 48), (125906, 48), (125907, 48), (125908, 48), (125909, 48), (125910, 48), (125911, 48), (125912, 48), (125913, 48), (125914, 48), (125915, 48), (125916, 48), (125917, 48), (125918, 48), (125919, 48), (125920, 48), (125921, 48), (125922, 48), (125923, 48), (125924, 48), (125925, 48), (125926, 48), (125927, 48), (125928, 48), (125929, 48), (125930, 48), (125931, 48), (125932, 48), (125933, 48), (125934, 48), (125935, 48), (125936, 48), (125937, 48), (125938, 48), (125939, 48), (125940, 48), (125941, 48), (125942, 48), (125943, 48), (125944, 48), (125945, 48), (125946, 48), (125947, 48), (125948, 48), (125949, 48), (125950, 48), (125951, 48), (126720, 24), (126721, 48), (126722, 48), (126723, 48), (126725, 48), (126726, 24), (126727, 48), (126729, 24), (126731, 48), (126735, 24), (126736, 48), (126737, 48), (126738, 48), (126739, 48), (126740, 48), (126741, 48), (126742, 48), (126743, 48), (126744, 48), (126745, 48), (126746, 48), (126747, 48), (126748, 48), (126749, 48), (126750, 48), (126751, 48), (126752, 48), (126753, 48), (126754, 48), (126755, 48), (126756, 48), (126757, 48), (126758, 48), (126759, 48), (126760, 48), (126761, 48), (126762, 48), (126763, 48), (126764, 48), (126765, 48), (126766, 48), (126767, 48), (126768, 48), (126769, 48), (126770, 48), (126771, 48), (126772, 48), (126773, 48), (126774, 48), (126775, 48), (126776, 48), (126777, 48), (126778, 48), (126779, 48), (126780, 48), (126781, 48), (126782, 48), (126783, 48), (126800, 48), (126801, 48), (126802, 48), (126803, 48), (126804, 48), (126805, 48), (126806, 48)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 418, 418, 550, 0, 418, 418, 550, 0, 550, 439, 550, 0, 550, 0, 550, 0, 439, 439, 550, 0, 550, 0, 550, 0, 503, 432, 0, 0, 418, 418, 0, 0, 418, 418, 0, 0, 418, 418, 0, 0, 0, 439, 0, 0, 0, 0, 0, 0, 439, 439, 0, 0, 0, 0, 0, 0, 424, 419, 438, 440, 418, 550, 602, 418, 440, 0, 434, 439, 438, 440, 550, 602, 550, 602, 438, 439, 438, 440, 550, 0, 550, 0, 434, 419, 438, 440, 418, 418, 602, 602, 418, 418, 438, 440, 418, 418, 0, 0, 434, 439, 438, 440, 602, 602, 602, 602, 438, 439, 438, 440, 0, 0, 0, 0, 503, 439, 438, 440, 550, 0, 550]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(125895, 164), (125899, 44), (125903, 316), (125907, 138), (125909, 462), (125911, 1296), (125915, 364), (125917, 739), (125919, 2366), (125922, 32), (125923, 40), (125926, 310), (125927, 556), (125930, 96), (125931, 144), (125934, 692), (125935, 1090), (125936, 0), (125938, 64), (125939, 138), (125940, 152), (125941, 624), (125942, 992), (125943, 1932), (125946, 252), (125947, 380), (125948, 364), (125949, 966), (125950, 1738), (125951, 3624), (126735, 80), (126749, 108), (126751, 424), (126766, 108), (126767, 208), (126780, 36), (126781, 130), (126782, 250), (126783, 568), (126805, 252)]

theorem l125895 : P.leaf 18 125895 = 164 := by decide +kernel

theorem l125899 : P.leaf 18 125899 = 44 := by decide +kernel

theorem l125903 : P.leaf 18 125903 = 316 := by decide +kernel

theorem l125907 : P.leaf 18 125907 = 138 := by decide +kernel

theorem l125909 : P.leaf 18 125909 = 462 := by decide +kernel

theorem l125911 : P.leaf 18 125911 = 1296 := by decide +kernel

theorem l125915 : P.leaf 18 125915 = 364 := by decide +kernel

theorem l125917 : P.leaf 18 125917 = 739 := by decide +kernel

theorem l125919 : P.leaf 18 125919 = 2366 := by decide +kernel

theorem l125922 : P.leaf 18 125922 = 32 := by decide +kernel

theorem l125923 : P.leaf 18 125923 = 40 := by decide +kernel

theorem l125926 : P.leaf 18 125926 = 310 := by decide +kernel

theorem l125927 : P.leaf 18 125927 = 556 := by decide +kernel

theorem l125930 : P.leaf 18 125930 = 96 := by decide +kernel

theorem l125931 : P.leaf 18 125931 = 144 := by decide +kernel

theorem l125934 : P.leaf 18 125934 = 692 := by decide +kernel

theorem l125935 : P.leaf 18 125935 = 1090 := by decide +kernel

theorem l125936 : P.leaf 18 125936 = 0 := by decide +kernel

theorem l125938 : P.leaf 18 125938 = 64 := by decide +kernel

theorem l125939 : P.leaf 18 125939 = 138 := by decide +kernel

theorem l125940 : P.leaf 18 125940 = 152 := by decide +kernel

theorem l125941 : P.leaf 18 125941 = 624 := by decide +kernel

theorem l125942 : P.leaf 18 125942 = 992 := by decide +kernel

theorem l125943 : P.leaf 18 125943 = 1932 := by decide +kernel

theorem l125946 : P.leaf 18 125946 = 252 := by decide +kernel

theorem l125947 : P.leaf 18 125947 = 380 := by decide +kernel

theorem l125948 : P.leaf 18 125948 = 364 := by decide +kernel

theorem l125949 : P.leaf 18 125949 = 966 := by decide +kernel

theorem l125950 : P.leaf 18 125950 = 1738 := by decide +kernel

theorem l125951 : P.leaf 18 125951 = 3624 := by decide +kernel

theorem l126735 : P.leaf 18 126735 = 80 := by decide +kernel

theorem l126749 : P.leaf 18 126749 = 108 := by decide +kernel

theorem l126751 : P.leaf 18 126751 = 424 := by decide +kernel

theorem l126766 : P.leaf 18 126766 = 108 := by decide +kernel

theorem l126767 : P.leaf 18 126767 = 208 := by decide +kernel

theorem l126780 : P.leaf 18 126780 = 36 := by decide +kernel

theorem l126781 : P.leaf 18 126781 = 130 := by decide +kernel

theorem l126782 : P.leaf 18 126782 = 250 := by decide +kernel

theorem l126783 : P.leaf 18 126783 = 568 := by decide +kernel

theorem l126805 : P.leaf 18 126805 = 252 := by decide +kernel

theorem segOK : checkSeg 20 perms 125895 126807 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 1065552 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 125895 126807 5760 1065552 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.cons l125895 (.cons l125899 (.cons l125903 (.cons l125907 (.cons l125909 (.cons l125911 (.cons l125915 (.cons l125917 (.cons l125919 (.cons l125922 (.cons l125923 (.cons l125926 (.cons l125927 (.cons l125930 (.cons l125931 (.cons l125934 (.cons l125935 (.cons l125936 (.cons l125938 (.cons l125939 (.cons l125940 (.cons l125941 (.cons l125942 (.cons l125943 (.cons l125946 (.cons l125947 (.cons l125948 (.cons l125949 (.cons l125950 (.cons l125951 (.cons l126735 (.cons l126749 (.cons l126751 (.cons l126766 (.cons l126767 (.cons l126780 (.cons l126781 (.cons l126782 (.cons l126783 (.cons l126805 (.nil))))))))))))))))))))))))))))))))))))))))))

end S53

end RACert.S0N3.C0
