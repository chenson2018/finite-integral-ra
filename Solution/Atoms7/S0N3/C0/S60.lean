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

namespace S60

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(128938, 48), (128939, 48), (128940, 48), (128941, 48), (128942, 48), (128943, 48), (128944, 48), (128945, 48), (128946, 48), (128947, 48), (128948, 48), (128949, 48), (128950, 48), (128951, 48), (128952, 48), (128953, 48), (128954, 48), (128955, 48), (128956, 48), (128957, 48), (128958, 48), (128959, 48), (128960, 48), (128961, 48), (128962, 48), (128963, 48), (128964, 48), (128965, 48), (128966, 48), (128967, 48), (128968, 48), (128969, 48), (128970, 48), (128971, 48), (128972, 48), (128973, 48), (128974, 48), (128975, 48), (128976, 48), (128977, 48), (128978, 48), (128979, 48), (128980, 48), (128981, 48), (128982, 48), (128983, 48), (128984, 48), (128985, 48), (128986, 48), (128987, 48), (128988, 48), (128989, 48), (128990, 48), (128991, 48), (128992, 48), (128993, 48), (128994, 48), (128995, 48), (128996, 48), (128997, 48), (128998, 48), (128999, 48), (129000, 48), (129001, 48), (129002, 48), (129003, 48), (129004, 48), (129005, 48), (129006, 48), (129007, 48), (129008, 48), (129009, 48), (129010, 48), (129011, 48), (129012, 48), (129013, 48), (129014, 48), (129015, 48), (129016, 48), (129017, 48), (129018, 48), (129019, 48), (129020, 48)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 0, 418, 418, 0, 0, 602, 439, 602, 602, 602, 602, 602, 602, 0, 439, 0, 0, 0, 0, 0, 0, 424, 432, 550, 0, 418, 418, 550, 0, 418, 418, 550, 0, 418, 418, 550, 0, 550, 439, 550, 0, 550, 0, 550, 0, 550, 439, 550, 0, 550, 0, 550, 0, 502, 432, 0, 0, 418, 418, 0, 0, 418, 418, 0, 0, 418, 418, 0, 0, 0, 439, 0, 0, 0, 0, 0, 0, 0, 439, 0, 0, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(128938, 535), (128939, 1070), (128942, 1076), (128943, 2032), (128952, 0), (128954, 627), (128955, 1482), (128956, 552), (128957, 1874), (128958, 1810), (128959, 4740), (128963, 96), (128967, 344), (128971, 348), (128975, 752), (128979, 424), (128981, 928), (128983, 1854), (128987, 1544), (128989, 1793), (128991, 4228), (128994, 172), (128995, 312), (128998, 654), (128999, 1194), (129002, 668), (129003, 1260), (129006, 1454), (129007, 3036), (129008, 0), (129010, 200), (129011, 424), (129012, 296), (129013, 1144), (129014, 1208), (129015, 2568), (129016, 0), (129018, 820), (129019, 1764), (129020, 552)]

theorem l128938 : P.leaf 18 128938 = 535 := by decide +kernel

theorem l128939 : P.leaf 18 128939 = 1070 := by decide +kernel

theorem l128942 : P.leaf 18 128942 = 1076 := by decide +kernel

theorem l128943 : P.leaf 18 128943 = 2032 := by decide +kernel

theorem l128952 : P.leaf 18 128952 = 0 := by decide +kernel

theorem l128954 : P.leaf 18 128954 = 627 := by decide +kernel

theorem l128955 : P.leaf 18 128955 = 1482 := by decide +kernel

theorem l128956 : P.leaf 18 128956 = 552 := by decide +kernel

theorem l128957 : P.leaf 18 128957 = 1874 := by decide +kernel

theorem l128958 : P.leaf 18 128958 = 1810 := by decide +kernel

theorem l128959 : P.leaf 18 128959 = 4740 := by decide +kernel

theorem l128963 : P.leaf 18 128963 = 96 := by decide +kernel

theorem l128967 : P.leaf 18 128967 = 344 := by decide +kernel

theorem l128971 : P.leaf 18 128971 = 348 := by decide +kernel

theorem l128975 : P.leaf 18 128975 = 752 := by decide +kernel

theorem l128979 : P.leaf 18 128979 = 424 := by decide +kernel

theorem l128981 : P.leaf 18 128981 = 928 := by decide +kernel

theorem l128983 : P.leaf 18 128983 = 1854 := by decide +kernel

theorem l128987 : P.leaf 18 128987 = 1544 := by decide +kernel

theorem l128989 : P.leaf 18 128989 = 1793 := by decide +kernel

theorem l128991 : P.leaf 18 128991 = 4228 := by decide +kernel

theorem l128994 : P.leaf 18 128994 = 172 := by decide +kernel

theorem l128995 : P.leaf 18 128995 = 312 := by decide +kernel

theorem l128998 : P.leaf 18 128998 = 654 := by decide +kernel

theorem l128999 : P.leaf 18 128999 = 1194 := by decide +kernel

theorem l129002 : P.leaf 18 129002 = 668 := by decide +kernel

theorem l129003 : P.leaf 18 129003 = 1260 := by decide +kernel

theorem l129006 : P.leaf 18 129006 = 1454 := by decide +kernel

theorem l129007 : P.leaf 18 129007 = 3036 := by decide +kernel

theorem l129008 : P.leaf 18 129008 = 0 := by decide +kernel

theorem l129010 : P.leaf 18 129010 = 200 := by decide +kernel

theorem l129011 : P.leaf 18 129011 = 424 := by decide +kernel

theorem l129012 : P.leaf 18 129012 = 296 := by decide +kernel

theorem l129013 : P.leaf 18 129013 = 1144 := by decide +kernel

theorem l129014 : P.leaf 18 129014 = 1208 := by decide +kernel

theorem l129015 : P.leaf 18 129015 = 2568 := by decide +kernel

theorem l129016 : P.leaf 18 129016 = 0 := by decide +kernel

theorem l129018 : P.leaf 18 129018 = 820 := by decide +kernel

theorem l129019 : P.leaf 18 129019 = 1764 := by decide +kernel

theorem l129020 : P.leaf 18 129020 = 552 := by decide +kernel

theorem segOK : checkSeg 20 perms 128938 129021 seg = true := by decide +kernel

theorem evOK : P.checkEv 18 seg ev live 0 2200080 = true := by decide +kernel

theorem total : OrbitSeg 20 perms (P.leaf 18) 128938 129021 3984 2200080 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.cons l128938 (.cons l128939 (.cons l128942 (.cons l128943 (.cons l128952 (.cons l128954 (.cons l128955 (.cons l128956 (.cons l128957 (.cons l128958 (.cons l128959 (.cons l128963 (.cons l128967 (.cons l128971 (.cons l128975 (.cons l128979 (.cons l128981 (.cons l128983 (.cons l128987 (.cons l128989 (.cons l128991 (.cons l128994 (.cons l128995 (.cons l128998 (.cons l128999 (.cons l129002 (.cons l129003 (.cons l129006 (.cons l129007 (.cons l129008 (.cons l129010 (.cons l129011 (.cons l129012 (.cons l129013 (.cons l129014 (.cons l129015 (.cons l129016 (.cons l129018 (.cons l129019 (.cons l129020 (.nil))))))))))))))))))))))))))))))))))))))))))

end S60

end RACert.S0N3.C0
