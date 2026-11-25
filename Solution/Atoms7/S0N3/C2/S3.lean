/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Atoms7.S0N3.C2.Defs

/-! Generated certificate segment; see `certgen`. -/

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option Elab.async false

@[expose] public section

namespace RACert.S0N3.C2

open RACert RACert.Problem

namespace S3

/-- Orbit minima `(α, orbit size)` in this segment. -/
def seg : List (ℕ × ℕ) :=
  [(475, 8), (476, 8), (477, 8), (478, 8), (479, 8), (496, 4), (497, 8), (499, 4), (500, 8), (501, 8), (502, 8), (503, 8), (508, 4), (509, 8), (511, 4), (960, 1), (961, 2), (963, 1), (964, 2), (965, 2), (966, 2), (967, 2), (972, 1), (973, 2), (975, 1), (976, 2), (977, 2), (978, 2), (979, 2), (980, 2), (981, 2), (982, 2), (983, 2), (984, 2), (985, 2), (986, 2), (987, 2), (988, 2), (989, 2), (990, 2), (991, 2), (1008, 1), (1009, 2), (1011, 1), (1012, 2), (1013, 2), (1014, 2), (1015, 2), (1020, 1), (1021, 2), (1023, 1)]

/-- Evidence: `0` for a leaf evaluated below, `x + 1` for a leaf killed by the quadruple `x`. -/
def ev : List ℕ :=
  [0, 434, 602, 0, 0, 417, 602, 0, 433, 602, 0, 0, 0, 0, 0, 417, 0, 0, 418, 0, 0, 0, 418, 0, 0, 417, 0, 0, 0, 433, 0, 0, 0, 417, 0, 0, 0, 434, 0, 0, 0, 417, 0, 0, 433, 0, 0, 0, 0, 0, 0]

/-- The evaluated leaves `(α, value)`. -/
def live : List (ℕ × ℕ) :=
  [(475, 2180), (478, 3273), (479, 4763), (499, 3394), (502, 3492), (503, 8918), (508, 937), (509, 11154), (511, 31930), (961, 130), (963, 704), (965, 2147), (966, 1298), (967, 3114), (973, 3951), (975, 5628), (977, 1832), (978, 696), (979, 2216), (981, 2538), (982, 1874), (983, 3956), (985, 3396), (986, 4070), (987, 6669), (989, 5710), (990, 6026), (991, 8473), (1009, 3594), (1011, 10916), (1013, 6639), (1014, 5998), (1015, 16991), (1020, 4054), (1021, 15715), (1023, 38282)]

theorem l475 : P.leaf 16 475 = 2180 := by decide +kernel

theorem l478 : P.leaf 16 478 = 3273 := by decide +kernel

theorem l479 : P.leaf 16 479 = 4763 := by decide +kernel

theorem l499 : P.leaf 16 499 = 3394 := by decide +kernel

theorem l502 : P.leaf 16 502 = 3492 := by decide +kernel

theorem l503 : P.leaf 16 503 = 8918 := by decide +kernel

theorem l508 : P.leaf 16 508 = 937 := by decide +kernel

theorem l509 : P.leaf 16 509 = 11154 := by decide +kernel

theorem l511 : P.leaf 16 511 = 31930 := by decide +kernel

theorem l961 : P.leaf 16 961 = 130 := by decide +kernel

theorem l963 : P.leaf 16 963 = 704 := by decide +kernel

theorem l965 : P.leaf 16 965 = 2147 := by decide +kernel

theorem l966 : P.leaf 16 966 = 1298 := by decide +kernel

theorem l967 : P.leaf 16 967 = 3114 := by decide +kernel

theorem l973 : P.leaf 16 973 = 3951 := by decide +kernel

theorem l975 : P.leaf 16 975 = 5628 := by decide +kernel

theorem l977 : P.leaf 16 977 = 1832 := by decide +kernel

theorem l978 : P.leaf 16 978 = 696 := by decide +kernel

theorem l979 : P.leaf 16 979 = 2216 := by decide +kernel

theorem l981 : P.leaf 16 981 = 2538 := by decide +kernel

theorem l982 : P.leaf 16 982 = 1874 := by decide +kernel

theorem l983 : P.leaf 16 983 = 3956 := by decide +kernel

theorem l985 : P.leaf 16 985 = 3396 := by decide +kernel

theorem l986 : P.leaf 16 986 = 4070 := by decide +kernel

theorem l987 : P.leaf 16 987 = 6669 := by decide +kernel

theorem l989 : P.leaf 16 989 = 5710 := by decide +kernel

theorem l990 : P.leaf 16 990 = 6026 := by decide +kernel

theorem l991 : P.leaf 16 991 = 8473 := by decide +kernel

theorem l1009 : P.leaf 16 1009 = 3594 := by decide +kernel

theorem l1011 : P.leaf 16 1011 = 10916 := by decide +kernel

theorem l1013 : P.leaf 16 1013 = 6639 := by decide +kernel

theorem l1014 : P.leaf 16 1014 = 5998 := by decide +kernel

theorem l1015 : P.leaf 16 1015 = 16991 := by decide +kernel

theorem l1020 : P.leaf 16 1020 = 4054 := by decide +kernel

theorem l1021 : P.leaf 16 1021 = 15715 := by decide +kernel

theorem l1023 : P.leaf 16 1023 = 38282 := by decide +kernel

theorem segOK : checkSeg 10 perms 475 1024 seg = true := by decide +kernel

theorem evOK : P.checkEv 16 seg ev live 0 688934 = true := by decide +kernel

theorem total : OrbitSeg 10 perms (P.leaf 16) 475 1024 168 688934 :=
  OrbitSeg.of_check segOK (by decide +kernel)
    (checkEv_sum check rows evOK (.cons l475 (.cons l478 (.cons l479 (.cons l499 (.cons l502 (.cons l503 (.cons l508 (.cons l509 (.cons l511 (.cons l961 (.cons l963 (.cons l965 (.cons l966 (.cons l967 (.cons l973 (.cons l975 (.cons l977 (.cons l978 (.cons l979 (.cons l981 (.cons l982 (.cons l983 (.cons l985 (.cons l986 (.cons l987 (.cons l989 (.cons l990 (.cons l991 (.cons l1009 (.cons l1011 (.cons l1013 (.cons l1014 (.cons l1015 (.cons l1020 (.cons l1021 (.cons l1023 (.nil))))))))))))))))))))))))))))))))))))))

end S3

end RACert.S0N3.C2
