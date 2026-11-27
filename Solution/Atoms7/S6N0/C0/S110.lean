/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Atoms7.S6N0.C0.Defs

/-! Generated certificate for the identity on six symmetric diversity atoms. -/

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option Elab.async false

@[expose] public section

namespace RACert.S6N0.C0.S110

open RACert RACert.Problem

theorem cover228351 : P.CoversSplit 26 10 228351 0xfffffffffffffffffffffffafffffafafffffffffffcffccfffffafaffccfac8fffffffffffffffffffffafafffffafafffffffffffcffccfffffafaffccfac8fffffffffffffffffffffffafffffafaffffffffffccffccfffffafaffccfac8fffffffffffffffffffffafafffffafaffffffffffccffccfffffafaffccfac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c228351_0 : P.sumLeaves 26 233831424 119 = 6720095 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 228351) (lo := 0) (len := 119) (W := 6720095) check rows elimOK (by decide) (by decide) cover228351 (by decide)
  decide +kernel

theorem c228351_1 : P.sumLeaves 26 233831543 104 = 7106304 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 228351) (lo := 119) (len := 104) (W := 7106304) check rows elimOK (by decide) (by decide) cover228351 (by decide)
  decide +kernel

theorem c228351_2 : P.sumLeaves 26 233831647 119 = 443190593 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 228351) (lo := 223) (len := 119) (W := 443190593) check rows elimOK (by decide) (by decide) cover228351 (by decide)
  decide +kernel

theorem c228351_3 : P.sumLeaves 26 233831766 102 = 764480634 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 228351) (lo := 342) (len := 102) (W := 764480634) check rows elimOK (by decide) (by decide) cover228351 (by decide)
  decide +kernel

theorem c228351_4 : P.sumLeaves 26 233831868 111 = 814039359 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 228351) (lo := 444) (len := 111) (W := 814039359) check rows elimOK (by decide) (by decide) cover228351 (by decide)
  decide +kernel

theorem c228351_5 : P.sumLeaves 26 233831979 106 = 750241960 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 228351) (lo := 555) (len := 106) (W := 750241960) check rows elimOK (by decide) (by decide) cover228351 (by decide)
  decide +kernel

theorem c228351_6 : P.sumLeaves 26 233832085 100 = 808723758 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 228351) (lo := 661) (len := 100) (W := 808723758) check rows elimOK (by decide) (by decide) cover228351 (by decide)
  decide +kernel

theorem c228351_7 : P.sumLeaves 26 233832185 117 = 1755807944 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 228351) (lo := 761) (len := 117) (W := 1755807944) check rows elimOK (by decide) (by decide) cover228351 (by decide)
  decide +kernel

theorem c228351_8 : P.sumLeaves 26 233832302 102 = 1999730430 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 228351) (lo := 878) (len := 102) (W := 1999730430) check rows elimOK (by decide) (by decide) cover228351 (by decide)
  decide +kernel

theorem c228351_9 : P.sumLeaves 26 233832404 44 = 1043297208 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 228351) (lo := 980) (len := 44) (W := 1043297208) check rows elimOK (by decide) (by decide) cover228351 (by decide)
  decide +kernel

theorem h228351 : P.leaf 36 228351 = 8393338285 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(119, 6720095), (104, 7106304), (119, 443190593), (102, 764480634), (111, 814039359), (106, 750241960), (100, 808723758), (117, 1755807944), (102, 1999730430), (44, 1043297208)]) (.cons c228351_0 (.cons c228351_1 (.cons c228351_2 (.cons c228351_3 (.cons c228351_4 (.cons c228351_5 (.cons c228351_6 (.cons c228351_7 (.cons c228351_8 (.cons c228351_9 (.nil))))))))))) (by decide) (by decide))

theorem cover228863 : P.CoversSplit 26 10 228863 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000400000000000000000000000000000000000000000100000000000000000000000000000000000000000020000000000000000000010000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c228863_0 : P.sumLeaves 26 234355712 1024 = 28907436 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 228863) (lo := 0) (len := 1024) (W := 28907436) check rows elimOK (by decide) (by decide) cover228863 (by decide)
  decide +kernel

theorem h228863 : P.leaf 36 228863 = 28907436 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 28907436)]) (.cons c228863_0 (.nil)) (by decide) (by decide))

theorem cover229047 : P.CoversSplit 26 10 229047 0xcc00cc0000000000cc00cc000000000000000000000000000000000000000000cc00cc0000000000cc00c000000000000000000000000000000000000000000000000000000000000000000000000000000000000033003300000000003300300000000000000000000000000000000000000000003300330000000000330030 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 538, 587, 972, 979]) (by decide +kernel)

theorem c229047_0 : P.sumLeaves 26 234544128 1024 = 188608245 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 229047) (lo := 0) (len := 1024) (W := 188608245) check rows elimOK (by decide) (by decide) cover229047 (by decide)
  decide +kernel

theorem h229047 : P.leaf 36 229047 = 188608245 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 188608245)]) (.cons c229047_0 (.nil)) (by decide) (by decide))

theorem cover229048 : P.CoversSplit 26 10 229048 0xf0f0f0f000000000f0f0f0f50000000000000000000000000000000000000030000000000000000000005050000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 874, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c229048_0 : P.sumLeaves 26 234545152 1024 = 10186154 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 229048) (lo := 0) (len := 1024) (W := 10186154) check rows elimOK (by decide) (by decide) cover229048 (by decide)
  decide +kernel

theorem h229048 : P.leaf 36 229048 = 10186154 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 10186154)]) (.cons c229048_0 (.nil)) (by decide) (by decide))

theorem cover229049 : P.CoversSplit 26 10 229049 0xf0f0f0f000000000f0f0f0f50000000000000000000000000000000000000030000000000000000000005050000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 587, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c229049_0 : P.sumLeaves 26 234546176 1024 = 189051915 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 229049) (lo := 0) (len := 1024) (W := 189051915) check rows elimOK (by decide) (by decide) cover229049 (by decide)
  decide +kernel

theorem h229049 : P.leaf 36 229049 = 189051915 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 189051915)]) (.cons c229049_0 (.nil)) (by decide) (by decide))

theorem cover229051 : P.CoversSplit 26 10 229051 0xf0f0f0f000000000f0f0f0f50000000000000000000000000000000000000030000000000000000000005050000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c229051_0 : P.sumLeaves 26 234548224 1024 = 334923694 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 229051) (lo := 0) (len := 1024) (W := 334923694) check rows elimOK (by decide) (by decide) cover229051 (by decide)
  decide +kernel

theorem h229051 : P.leaf 36 229051 = 334923694 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 334923694)]) (.cons c229051_0 (.nil)) (by decide) (by decide))

theorem cover229052 : P.CoversSplit 26 10 229052 0xffffffff00000000fffffffa0000000000000000000000000000000000000030ffffffff00000000fffff0f0000000000000000000000000000000000000003000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [538, 874, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c229052_0 : P.sumLeaves 26 234549248 998 = 187249832 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 229052) (lo := 0) (len := 998) (W := 187249832) check rows elimOK (by decide) (by decide) cover229052 (by decide)
  decide +kernel

theorem c229052_1 : P.sumLeaves 26 234550246 26 = 152147386 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 229052) (lo := 998) (len := 26) (W := 152147386) check rows elimOK (by decide) (by decide) cover229052 (by decide)
  decide +kernel

theorem h229052 : P.leaf 36 229052 = 339397218 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(998, 187249832), (26, 152147386)]) (.cons c229052_0 (.cons c229052_1 (.nil))) (by decide) (by decide))

theorem cover229053 : P.CoversSplit 26 10 229053 0xffffffff00000000fffffffa0000000000000000000000000000000000000030ffffffff00000000fffff0f0000000000000000000000000000000000000003000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [538, 587, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c229053_0 : P.sumLeaves 26 234550272 998 = 344776437 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 229053) (lo := 0) (len := 998) (W := 344776437) check rows elimOK (by decide) (by decide) cover229053 (by decide)
  decide +kernel

theorem c229053_1 : P.sumLeaves 26 234551270 26 = 249750222 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 229053) (lo := 998) (len := 26) (W := 249750222) check rows elimOK (by decide) (by decide) cover229053 (by decide)
  decide +kernel

theorem h229053 : P.leaf 36 229053 = 594526659 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(998, 344776437), (26, 249750222)]) (.cons c229053_0 (.cons c229053_1 (.nil))) (by decide) (by decide))

theorem cover229055 : P.CoversSplit 26 10 229055 0xffffffff00000000fffffffa0000000000000000000000000000000000000030ffffffff00000000fffff0f0000000000000000000000000000000000000003000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [538, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c229055_0 : P.sumLeaves 26 234552320 998 = 519197862 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 229055) (lo := 0) (len := 998) (W := 519197862) check rows elimOK (by decide) (by decide) cover229055 (by decide)
  decide +kernel

theorem c229055_1 : P.sumLeaves 26 234553318 26 = 354256886 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 229055) (lo := 998) (len := 26) (W := 354256886) check rows elimOK (by decide) (by decide) cover229055 (by decide)
  decide +kernel

theorem h229055 : P.leaf 36 229055 = 873454748 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(998, 519197862), (26, 354256886)]) (.cons c229055_0 (.cons c229055_1 (.nil))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(228351, 60), (228863, 15), (229047, 60), (229048, 180), (229049, 720), (229051, 360), (229052, 360), (229053, 720), (229055, 360)]

theorem segOK : checkSeg 20 perms 228351 229069 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 228351 229069 2835 1638559721940 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 1638559721940)
    (SegSum.cons (w := 60) h228351 (SegSum.cons (w := 15) h228863 (SegSum.cons (w := 60) h229047 (SegSum.cons (w := 180) h229048 (SegSum.cons (w := 720) h229049 (SegSum.cons (w := 360) h229051 (SegSum.cons (w := 360) h229052 (SegSum.cons (w := 720) h229053 (SegSum.cons (w := 360) h229055 (show SegSum (P.leaf 36) [] 0 from rfl)))))))))) (by decide)

end RACert.S6N0.C0.S110
