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

namespace S107

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(454783, 48), (454896, 12), (454897, 48), (454899, 24), (454901, 24), (454902, 24), (454903, 48), (454911, 12), (454912, 24), (454913, 48), (454915, 24), (454916, 48), (454917, 48), (454918, 48), (454919, 48), (454924, 24), (454925, 48), (454927, 24), (454928, 48), (454929, 48), (454930, 48), (454931, 48), (454932, 48), (454933, 48), (454934, 48), (454935, 48), (454936, 48), (454937, 48), (454938, 48), (454939, 48), (454940, 48), (454941, 48), (454942, 48), (454943, 48), (454960, 24), (454961, 48), (454963, 24), (454964, 48), (454965, 48), (454966, 48), (454967, 48), (454972, 24), (454973, 48), (454975, 24), (454976, 48), (454977, 48), (454978, 48), (454979, 48), (454980, 48), (454981, 48), (454982, 48), (454983, 48), (454984, 48), (454985, 48), (454986, 48), (454987, 48), (454988, 48), (454989, 48), (454990, 48), (454991, 48), (454992, 48), (454993, 48), (454994, 48), (454995, 48), (454996, 48), (454997, 48), (454998, 48), (454999, 48), (455000, 48), (455001, 48), (455002, 48), (455003, 48), (455004, 48), (455005, 48), (455006, 48), (455007, 48), (455008, 48), (455009, 48), (455010, 48), (455011, 48), (455012, 48), (455013, 48), (455014, 48), (455015, 48), (455016, 48), (455017, 48), (455018, 48), (455019, 48), (455020, 48), (455021, 48), (455022, 48), (455023, 48), (455024, 48), (455025, 48), (455026, 48), (455027, 48), (455028, 48), (455029, 48), (455030, 48), (455031, 48), (455032, 48), (455033, 48), (455034, 48), (455035, 48), (455036, 48), (455037, 48), (455038, 48), (455039, 48), (455104, 24), (455105, 48), (455107, 24), (455108, 48), (455109, 48), (455110, 48), (455111, 48), (455116, 24), (455117, 48), (455119, 24), (455120, 48), (455121, 48), (455122, 48), (455123, 48), (455124, 48), (455125, 48), (455126, 48), (455127, 48), (455128, 48), (455129, 48), (455130, 48)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 418, 434, 434, 418, 502, 431, 602, 502, 502, 0, 434, 434, 431, 434, 550, 602, 431, 602, 550, 650, 550, 650, 550, 0, 550, 0, 434, 434, 434, 602, 602, 602, 602, 0, 0, 0, 418, 439, 550, 650, 418, 502, 550, 0, 424, 439, 550, 650, 502, 502, 550, 0, 550, 650, 550, 650, 550, 0, 550, 0, 550, 650, 550, 650, 550, 0, 550, 0, 502, 439, 650, 650, 502, 502, 0, 0, 502, 439, 650, 650, 502, 502, 0, 0, 650, 650, 650, 650, 0, 0, 0, 0, 650, 650, 650, 650, 0, 0, 0, 0, 418, 502, 0, 418, 502, 550, 0, 502, 502, 0, 550, 0, 550, 0, 550, 0, 550, 0, 550, 0, 550]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(454783, 750), (454896, 17), (454897, 113), (454899, 599), (454901, 461), (454902, 265), (454903, 1350), (454911, 4990), (454927, 22), (454941, 69), (454943, 142), (454972, 70), (454973, 126), (454975, 236), (454983, 49), (454991, 80), (454997, 95), (454999, 228), (455005, 208), (455007, 405), (455014, 100), (455015, 228), (455022, 208), (455023, 405), (455028, 40), (455029, 168), (455030, 194), (455031, 417), (455036, 274), (455037, 360), (455038, 360), (455039, 758), (455107, 93), (455111, 134), (455119, 224), (455121, 188), (455123, 938), (455125, 672), (455127, 1455), (455129, 677)]

theorem l454783 : P.leaf 18 454783 = 750 := by decide +kernel

theorem l454896 : P.leaf 18 454896 = 17 := by decide +kernel

theorem l454897 : P.leaf 18 454897 = 113 := by decide +kernel

theorem l454899 : P.leaf 18 454899 = 599 := by decide +kernel

theorem l454901 : P.leaf 18 454901 = 461 := by decide +kernel

theorem l454902 : P.leaf 18 454902 = 265 := by decide +kernel

theorem l454903 : P.leaf 18 454903 = 1350 := by decide +kernel

theorem l454911 : P.leaf 18 454911 = 4990 := by decide +kernel

theorem l454927 : P.leaf 18 454927 = 22 := by decide +kernel

theorem l454941 : P.leaf 18 454941 = 69 := by decide +kernel

theorem l454943 : P.leaf 18 454943 = 142 := by decide +kernel

theorem l454972 : P.leaf 18 454972 = 70 := by decide +kernel

theorem l454973 : P.leaf 18 454973 = 126 := by decide +kernel

theorem l454975 : P.leaf 18 454975 = 236 := by decide +kernel

theorem l454983 : P.leaf 18 454983 = 49 := by decide +kernel

theorem l454991 : P.leaf 18 454991 = 80 := by decide +kernel

theorem l454997 : P.leaf 18 454997 = 95 := by decide +kernel

theorem l454999 : P.leaf 18 454999 = 228 := by decide +kernel

theorem l455005 : P.leaf 18 455005 = 208 := by decide +kernel

theorem l455007 : P.leaf 18 455007 = 405 := by decide +kernel

theorem l455014 : P.leaf 18 455014 = 100 := by decide +kernel

theorem l455015 : P.leaf 18 455015 = 228 := by decide +kernel

theorem l455022 : P.leaf 18 455022 = 208 := by decide +kernel

theorem l455023 : P.leaf 18 455023 = 405 := by decide +kernel

theorem l455028 : P.leaf 18 455028 = 40 := by decide +kernel

theorem l455029 : P.leaf 18 455029 = 168 := by decide +kernel

theorem l455030 : P.leaf 18 455030 = 194 := by decide +kernel

theorem l455031 : P.leaf 18 455031 = 417 := by decide +kernel

theorem l455036 : P.leaf 18 455036 = 274 := by decide +kernel

theorem l455037 : P.leaf 18 455037 = 360 := by decide +kernel

theorem l455038 : P.leaf 18 455038 = 360 := by decide +kernel

theorem l455039 : P.leaf 18 455039 = 758 := by decide +kernel

theorem l455107 : P.leaf 18 455107 = 93 := by decide +kernel

theorem l455111 : P.leaf 18 455111 = 134 := by decide +kernel

theorem l455119 : P.leaf 18 455119 = 224 := by decide +kernel

theorem l455121 : P.leaf 18 455121 = 188 := by decide +kernel

theorem l455123 : P.leaf 18 455123 = 938 := by decide +kernel

theorem l455125 : P.leaf 18 455125 = 672 := by decide +kernel

theorem l455127 : P.leaf 18 455127 = 1455 := by decide +kernel

theorem l455129 : P.leaf 18 455129 = 677 := by decide +kernel

theorem segOK : checkSeg 20 perms 454783 455131 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 644532 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 454783 455131 5760 644532 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.cons l454783 (.cons l454896 (.cons l454897 (.cons l454899 (.cons l454901 (.cons l454902 (.cons l454903 (.cons l454911 (.cons l454927 (.cons l454941 (.cons l454943 (.cons l454972 (.cons l454973 (.cons l454975 (.cons l454983 (.cons l454991 (.cons l454997 (.cons l454999 (.cons l455005 (.cons l455007 (.cons l455014 (.cons l455015 (.cons l455022 (.cons l455023 (.cons l455028 (.cons l455029 (.cons l455030 (.cons l455031 (.cons l455036 (.cons l455037 (.cons l455038 (.cons l455039 (.cons l455107 (.cons l455111 (.cons l455119 (.cons l455121 (.cons l455123 (.cons l455125 (.cons l455127 (.cons l455129 (.nil))))))))))))))))))))))))))))))))))))))))))

end S107

end RACert.S0N3.C0
