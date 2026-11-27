/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Solution.Atoms7.S4N1.C0.Actions

/-! Generated identity-class certificate for the product-row count. -/

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option Elab.async false

@[expose] public section

namespace RACert.S4N1.C0.S25

open RACert RACert.Problem

theorem cover4029 : P.CoversSplit 24 10 4029 0xff00ff00f500a000ff33ff33f531a020ff00ff00f500a000ff00ff00f500a0000000000000000000330033002000200000000000000000003300330020002000ff00ff00f500a000ff33ff33f531a020000000000000000000000000000000000000000000000000330033002000200000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [473, 517, 915, 1202, 1209, 1217, 1308]) (ps := [(14, [923], [915])]) (by decide +kernel)

theorem c4029_0 : P.sumLeaves 24 4125696 798 = 9685769 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 4029) (lo := 0) (len := 798) (W := 9685769) check rows elimOK (by decide) (by decide) cover4029 (by decide)
  decide +kernel

theorem c4029_1 : P.sumLeaves 24 4126494 220 = 39072851 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 4029) (lo := 798) (len := 220) (W := 39072851) check rows elimOK (by decide) (by decide) cover4029 (by decide)
  decide +kernel

theorem c4029_2 : P.sumLeaves 24 4126714 6 = 11078512 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 4029) (lo := 1018) (len := 6) (W := 11078512) check rows elimOK (by decide) (by decide) cover4029 (by decide)
  decide +kernel

theorem h4029 : P.leaf 34 4029 = 59837132 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(798, 9685769), (220, 39072851), (6, 11078512)]) (.cons c4029_0 (.cons c4029_1 (.cons c4029_2 (.nil)))) (by decide) (by decide))

theorem cover4030 : P.CoversSplit 24 10 4030 0xfffffffff5f5a0a0fffffffff5f5a0a0aaaaafaf00000000aaaaafaf00000000ffffffffa000a000ff00ff00a000a000aaaaafaf00000000aa00af0000000000fffffffff5f5a0a0fffffffff5f5a0a000000000000000000000000000000000ffffffffa000a000ff00ff00a000a00000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 517, 915, 1202, 1209, 1258, 1308]) (by decide +kernel)

theorem c4030_0 : P.sumLeaves 24 4126720 440 = 4485108 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 4030) (lo := 0) (len := 440) (W := 4485108) check rows elimOK (by decide) (by decide) cover4030 (by decide)
  decide +kernel

theorem c4030_1 : P.sumLeaves 24 4127160 246 = 12383044 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 4030) (lo := 440) (len := 246) (W := 12383044) check rows elimOK (by decide) (by decide) cover4030 (by decide)
  decide +kernel

theorem c4030_2 : P.sumLeaves 24 4127406 234 = 23884694 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 4030) (lo := 686) (len := 234) (W := 23884694) check rows elimOK (by decide) (by decide) cover4030 (by decide)
  decide +kernel

theorem c4030_3 : P.sumLeaves 24 4127640 104 = 52977781 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 4030) (lo := 920) (len := 104) (W := 52977781) check rows elimOK (by decide) (by decide) cover4030 (by decide)
  decide +kernel

theorem h4030 : P.leaf 34 4030 = 93730627 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(440, 4485108), (246, 12383044), (234, 23884694), (104, 52977781)]) (.cons c4030_0 (.cons c4030_1 (.cons c4030_2 (.cons c4030_3 (.nil))))) (by decide) (by decide))

theorem cover4031 : P.CoversSplit 24 10 4031 0xfffffffff5f5a0a0fffffffff5f5a0a0fffffffff5f5a0a0fffffffff5f5a0a0ffffffffa000a000ff00ff00a000a000ffffffffa000a000ff00ff00a000a000fffffffff5f5a0a0fffffffff5f5a0a000000000000000000000000000000000ffffffffa000a000ff00ff00a000a00000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [517, 915, 1202, 1209, 1217, 1258, 1308]) (by decide +kernel)

theorem c4031_0 : P.sumLeaves 24 4127744 440 = 9571128 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 4031) (lo := 0) (len := 440) (W := 9571128) check rows elimOK (by decide) (by decide) cover4031 (by decide)
  decide +kernel

theorem c4031_1 : P.sumLeaves 24 4128184 184 = 20636165 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 4031) (lo := 440) (len := 184) (W := 20636165) check rows elimOK (by decide) (by decide) cover4031 (by decide)
  decide +kernel

theorem c4031_2 : P.sumLeaves 24 4128368 184 = 34178048 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 4031) (lo := 624) (len := 184) (W := 34178048) check rows elimOK (by decide) (by decide) cover4031 (by decide)
  decide +kernel

theorem c4031_3 : P.sumLeaves 24 4128552 128 = 37288465 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 4031) (lo := 808) (len := 128) (W := 37288465) check rows elimOK (by decide) (by decide) cover4031 (by decide)
  decide +kernel

theorem c4031_4 : P.sumLeaves 24 4128680 88 = 95888470 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 4031) (lo := 936) (len := 88) (W := 95888470) check rows elimOK (by decide) (by decide) cover4031 (by decide)
  decide +kernel

theorem h4031 : P.leaf 34 4031 = 197562276 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(440, 9571128), (184, 20636165), (184, 34178048), (128, 37288465), (88, 95888470)]) (.cons c4031_0 (.cons c4031_1 (.cons c4031_2 (.cons c4031_3 (.cons c4031_4 (.nil)))))) (by decide) (by decide))

theorem cover4076 : P.CoversSplit 24 10 4076 0x8800000088008800000000000000000088000000880088000000000000000000000000000000000000220000002200220000000000000000002200000022002288000000880088000000000000000000880000008800880000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 473, 508, 515, 522, 915, 1258, 1609]) (by decide +kernel)

theorem c4076_0 : P.sumLeaves 24 4173824 1024 = 6272138 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 4076) (lo := 0) (len := 1024) (W := 6272138) check rows elimOK (by decide) (by decide) cover4076 (by decide)
  decide +kernel

theorem h4076 : P.leaf 34 4076 = 6272138 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 6272138)]) (.cons c4076_0 (.nil)) (by decide) (by decide))

theorem cover4077 : P.CoversSplit 24 10 4077 0xcc00cc00cc0088000000000000000000cc00cc00cc00880000000000000000000000000000000000003300330022002200000000000000000033003300220022cc00cc00cc0088000000000000000000cc00cc00c800880000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [473, 515, 522, 915, 1217, 1609]) (by decide +kernel)

theorem c4077_0 : P.sumLeaves 24 4174848 1024 = 32769332 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 4077) (lo := 0) (len := 1024) (W := 32769332) check rows elimOK (by decide) (by decide) cover4077 (by decide)
  decide +kernel

theorem h4077 : P.leaf 34 4077 = 32769332 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(1024, 32769332)]) (.cons c4077_0 (.nil)) (by decide) (by decide))

theorem cover4078 : P.CoversSplit 24 10 4078 0xaaaa0000abab0a0a0000000000000000aaaa0000abab0a0a00220000002300020000000000220002000000000000000000000000002200020000000000000000aaaa0000abab0a0a0000000000000000aaaa0000aaaa0a0a00220000002200020000000000220002000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 515, 522, 1217, 1258, 1609]) (by decide +kernel)

theorem c4078_0 : P.sumLeaves 24 4175872 989 = 35410158 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 4078) (lo := 0) (len := 989) (W := 35410158) check rows elimOK (by decide) (by decide) cover4078 (by decide)
  decide +kernel

theorem c4078_1 : P.sumLeaves 24 4176861 35 = 18859368 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 4078) (lo := 989) (len := 35) (W := 18859368) check rows elimOK (by decide) (by decide) cover4078 (by decide)
  decide +kernel

theorem h4078 : P.leaf 34 4078 = 54269526 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(989, 35410158), (35, 18859368)]) (.cons c4078_0 (.cons c4078_1 (.nil))) (by decide) (by decide))

theorem cover4079 : P.CoversSplit 24 10 4079 0xfffffffffefeaaaa0000000000000000fffffffffefeaaaa00330033003200220000000000220022000000000000000000000000002200220000000000000000fffffffffefeaaaa0000000000000000fffffffffafaaaaa00330033003200220000000000220022000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 522, 1209, 1217, 1258, 1609]) (by decide +kernel)

theorem c4079_0 : P.sumLeaves 24 4176896 485 = 23130375 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 4079) (lo := 0) (len := 485) (W := 23130375) check rows elimOK (by decide) (by decide) cover4079 (by decide)
  decide +kernel

theorem c4079_1 : P.sumLeaves 24 4177381 405 = 59800414 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 4079) (lo := 485) (len := 405) (W := 59800414) check rows elimOK (by decide) (by decide) cover4079 (by decide)
  decide +kernel

theorem c4079_2 : P.sumLeaves 24 4177786 134 = 98154678 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 4079) (lo := 890) (len := 134) (W := 98154678) check rows elimOK (by decide) (by decide) cover4079 (by decide)
  decide +kernel

theorem h4079 : P.leaf 34 4079 = 181085467 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(485, 23130375), (405, 59800414), (134, 98154678)]) (.cons c4079_0 (.cons c4079_1 (.cons c4079_2 (.nil)))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(4029, 48), (4030, 48), (4031, 48), (4076, 12), (4077, 12), (4078, 24), (4079, 24)]

theorem segOK : checkSeg 16 perms 4029 4094 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 4029 4094 216 22971259152 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 22971259152)
    (SegSum.cons (w := 48) h4029 (SegSum.cons (w := 48) h4030 (SegSum.cons (w := 48) h4031 (SegSum.cons (w := 12) h4076 (SegSum.cons (w := 12) h4077 (SegSum.cons (w := 24) h4078 (SegSum.cons (w := 24) h4079 (show SegSum (P.leaf 34) [] 0 from rfl)))))))) (by decide)

end RACert.S4N1.C0.S25
