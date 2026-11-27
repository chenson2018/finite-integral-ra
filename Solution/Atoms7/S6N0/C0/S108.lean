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

namespace RACert.S6N0.C0.S108

open RACert RACert.Problem

theorem cover131071 : P.CoversSplit 26 10 131071 0xfffffffffffffafafffffffffffffafafffffffffffffac8fafafafafac8fac8fffffafafffffafafafafafafafafafafffffafafffffac8fafafafafac8fac8fffffffffffffafafffffffffffffafaffffffffffccfac8fafafafafac8fac8fffffafafffffafafafafafafafafafafffffafaffccfac8fafafafafac8fac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c131071_0 : P.sumLeaves 26 134216704 135 = 908160961 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 131071) (lo := 0) (len := 135) (W := 908160961) check rows elimOK (by decide) (by decide) cover131071 (by decide)
  decide +kernel

theorem c131071_1 : P.sumLeaves 26 134216839 118 = 1099035371 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 131071) (lo := 135) (len := 118) (W := 1099035371) check rows elimOK (by decide) (by decide) cover131071 (by decide)
  decide +kernel

theorem c131071_2 : P.sumLeaves 26 134216957 129 = 1248322562 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 131071) (lo := 253) (len := 129) (W := 1248322562) check rows elimOK (by decide) (by decide) cover131071 (by decide)
  decide +kernel

theorem c131071_3 : P.sumLeaves 26 134217086 104 = 1550626728 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 131071) (lo := 382) (len := 104) (W := 1550626728) check rows elimOK (by decide) (by decide) cover131071 (by decide)
  decide +kernel

theorem c131071_4 : P.sumLeaves 26 134217190 127 = 1642634648 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 131071) (lo := 486) (len := 127) (W := 1642634648) check rows elimOK (by decide) (by decide) cover131071 (by decide)
  decide +kernel

theorem c131071_5 : P.sumLeaves 26 134217317 118 = 1729073308 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 131071) (lo := 613) (len := 118) (W := 1729073308) check rows elimOK (by decide) (by decide) cover131071 (by decide)
  decide +kernel

theorem c131071_6 : P.sumLeaves 26 134217435 129 = 1879818738 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 131071) (lo := 731) (len := 129) (W := 1879818738) check rows elimOK (by decide) (by decide) cover131071 (by decide)
  decide +kernel

theorem c131071_7 : P.sumLeaves 26 134217564 101 = 1920415736 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 131071) (lo := 860) (len := 101) (W := 1920415736) check rows elimOK (by decide) (by decide) cover131071 (by decide)
  decide +kernel

theorem c131071_8 : P.sumLeaves 26 134217665 63 = 1470067724 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 131071) (lo := 961) (len := 63) (W := 1470067724) check rows elimOK (by decide) (by decide) cover131071 (by decide)
  decide +kernel

theorem h131071 : P.leaf 36 131071 = 13448155776 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(135, 908160961), (118, 1099035371), (129, 1248322562), (104, 1550626728), (127, 1642634648), (118, 1729073308), (129, 1879818738), (101, 1920415736), (63, 1470067724)]) (.cons c131071_0 (.cons c131071_1 (.cons c131071_2 (.cons c131071_3 (.cons c131071_4 (.cons c131071_5 (.cons c131071_6 (.cons c131071_7 (.cons c131071_8 (.nil)))))))))) (by decide) (by decide))

theorem cover227823 : P.CoversSplit 26 10 227823 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000400000000000000000000000000000000000000000100000000000000000000000000000000000000000020000000000000000000010000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c227823_0 : P.sumLeaves 26 233290752 1024 = 19872568 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 227823) (lo := 0) (len := 1024) (W := 19872568) check rows elimOK (by decide) (by decide) cover227823 (by decide)
  decide +kernel

theorem h227823 : P.leaf 36 227823 = 19872568 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 19872568)]) (.cons c227823_0 (.nil)) (by decide) (by decide))

theorem cover227839 : P.CoversSplit 26 10 227839 0x8000000000000000000000000000000000000000000000000000000000000001000000000000000000000400000000000000000000000000000000000000000100000000000000000000000000000000000000000020000000000000000000010000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [433, 629, 636, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c227839_0 : P.sumLeaves 26 233307136 1024 = 25393548 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 227839) (lo := 0) (len := 1024) (W := 25393548) check rows elimOK (by decide) (by decide) cover227839 (by decide)
  decide +kernel

theorem h227839 : P.leaf 36 227839 = 25393548 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 25393548)]) (.cons c227839_0 (.nil)) (by decide) (by decide))

theorem cover228023 : P.CoversSplit 26 10 228023 0xcc00cc0000000000cc00cc000000000000000000000000000000000000000000cc00cc0000000000cc00c000000000000000000000000000000000000000000000000000000000000000000000000000000000000033003300000000003300300000000000000000000000000000000000000000003300330000000000330030 :=
  coversSplit check rows (by decide) (by decide) (xs := [489, 538, 587, 972, 979]) (by decide +kernel)

theorem c228023_0 : P.sumLeaves 26 233495552 1024 = 180460821 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 228023) (lo := 0) (len := 1024) (W := 180460821) check rows elimOK (by decide) (by decide) cover228023 (by decide)
  decide +kernel

theorem h228023 : P.leaf 36 228023 = 180460821 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 180460821)]) (.cons c228023_0 (.nil)) (by decide) (by decide))

theorem cover228025 : P.CoversSplit 26 10 228025 0xf0f0f0f000000000f0f0f0f50000000000000000000000000000000000000030000000000000000000005050000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 587, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c228025_0 : P.sumLeaves 26 233497600 1024 = 143256860 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 228025) (lo := 0) (len := 1024) (W := 143256860) check rows elimOK (by decide) (by decide) cover228025 (by decide)
  decide +kernel

theorem h228025 : P.leaf 36 228025 = 143256860 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 143256860)]) (.cons c228025_0 (.nil)) (by decide) (by decide))

theorem cover228027 : P.CoversSplit 26 10 228027 0xf0f0f0f000000000f0f0f0f50000000000000000000000000000000000000030000000000000000000005050000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 538, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c228027_0 : P.sumLeaves 26 233499648 1024 = 329127888 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 228027) (lo := 0) (len := 1024) (W := 329127888) check rows elimOK (by decide) (by decide) cover228027 (by decide)
  decide +kernel

theorem h228027 : P.leaf 36 228027 = 329127888 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 329127888)]) (.cons c228027_0 (.nil)) (by decide) (by decide))

theorem cover228029 : P.CoversSplit 26 10 228029 0xffffffff00000000fffffffa0000000000000000000000000000000000000030ffffffff00000000fffff0f0000000000000000000000000000000000000003000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [538, 587, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c228029_0 : P.sumLeaves 26 233501696 998 = 224947572 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 228029) (lo := 0) (len := 998) (W := 224947572) check rows elimOK (by decide) (by decide) cover228029 (by decide)
  decide +kernel

theorem c228029_1 : P.sumLeaves 26 233502694 26 = 197077268 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 228029) (lo := 998) (len := 26) (W := 197077268) check rows elimOK (by decide) (by decide) cover228029 (by decide)
  decide +kernel

theorem h228029 : P.leaf 36 228029 = 422024840 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(998, 224947572), (26, 197077268)]) (.cons c228029_0 (.cons c228029_1 (.nil))) (by decide) (by decide))

theorem cover228031 : P.CoversSplit 26 10 228031 0xffffffff00000000fffffffa0000000000000000000000000000000000000030ffffffff00000000fffff0f0000000000000000000000000000000000000003000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [538, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c228031_0 : P.sumLeaves 26 233503744 998 = 502996360 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 228031) (lo := 0) (len := 998) (W := 502996360) check rows elimOK (by decide) (by decide) cover228031 (by decide)
  decide +kernel

theorem c228031_1 : P.sumLeaves 26 233504742 26 = 354256886 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 228031) (lo := 998) (len := 26) (W := 354256886) check rows elimOK (by decide) (by decide) cover228031 (by decide)
  decide +kernel

theorem h228031 : P.leaf 36 228031 = 857253246 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(998, 502996360), (26, 354256886)]) (.cons c228031_0 (.cons c228031_1 (.nil))) (by decide) (by decide))

theorem cover228047 : P.CoversSplit 26 10 228047 0xffff0000ffff0000ffff0000ffff050000000000000000000000000000300000000000000000000005050000050500000000000000000000000000000000000000000000003300000000000000330000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 587, 972, 979, 1266, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c228047_0 : P.sumLeaves 26 233520128 1024 = 440773668 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 228047) (lo := 0) (len := 1024) (W := 440773668) check rows elimOK (by decide) (by decide) cover228047 (by decide)
  decide +kernel

theorem h228047 : P.leaf 36 228047 = 440773668 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 440773668)]) (.cons c228047_0 (.nil)) (by decide) (by decide))

theorem cover228061 : P.CoversSplit 26 10 228061 0xffff0000ffff0000ffff0000ffff050000000000000000000000000000300000000000000000000005050000050500000000000000000000000000000000000000000000003300000000000000330000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 587, 923, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c228061_0 : P.sumLeaves 26 233534464 1024 = 482145284 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 228061) (lo := 0) (len := 1024) (W := 482145284) check rows elimOK (by decide) (by decide) cover228061 (by decide)
  decide +kernel

theorem h228061 : P.leaf 36 228061 = 482145284 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 482145284)]) (.cons c228061_0 (.nil)) (by decide) (by decide))

theorem cover228063 : P.CoversSplit 26 10 228063 0xffff0000ffff0000ffff0000ffff050000000000000000000000000000300000000000000000000005050000050500000000000000000000000000000000000000000000003300000000000000330000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [530, 587, 972, 979, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c228063_0 : P.sumLeaves 26 233536512 1024 = 1013094401 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 228063) (lo := 0) (len := 1024) (W := 1013094401) check rows elimOK (by decide) (by decide) cover228063 (by decide)
  decide +kernel

theorem h228063 : P.leaf 36 228063 = 1013094401 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 1013094401)]) (.cons c228063_0 (.nil)) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(131071, 60), (227823, 90), (227839, 60), (228023, 60), (228025, 720), (228027, 360), (228029, 720), (228031, 360), (228047, 360), (228061, 720), (228063, 360)]

theorem segOK : checkSeg 20 perms 131071 228079 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 131071 228079 3870 2525666281380 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 2525666281380)
    (SegSum.cons (w := 60) h131071 (SegSum.cons (w := 90) h227823 (SegSum.cons (w := 60) h227839 (SegSum.cons (w := 60) h228023 (SegSum.cons (w := 720) h228025 (SegSum.cons (w := 360) h228027 (SegSum.cons (w := 720) h228029 (SegSum.cons (w := 360) h228031 (SegSum.cons (w := 360) h228047 (SegSum.cons (w := 720) h228061 (SegSum.cons (w := 360) h228063 (show SegSum (P.leaf 36) [] 0 from rfl)))))))))))) (by decide)

end RACert.S6N0.C0.S108
