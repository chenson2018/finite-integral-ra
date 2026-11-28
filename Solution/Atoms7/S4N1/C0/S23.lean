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

namespace RACert.S4N1.C0.S23

open RACert RACert.Problem

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

theorem cover52335 : P.CoversSplit 24 10 52335 0xcc00c800cc00c8000000000000000000cc00c800cc00c80000000000000000000000000000000000003200320032003200000000000000000032003200320032cc00c800cc00c8000000000000000000cc00c800c800c80000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 522, 572, 858, 865, 1217, 1609]) (by decide +kernel)

noncomputable def f52335 (i : ℕ) := rowWeight keep2 twice2 i * P.leaf 24 (53591040 + i)

theorem c52335_0 : rowSum f52335 0 1024 = 32769332 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 52335) (keep := keep2) (twice := twice2) check rows elimOK (by decide) (by decide) cover52335 (by decide)
  decide +kernel

theorem sum52335 : rowSum f52335 0 1024 = 32769332 :=
  c52335_0

theorem h52335 : P.leaf 34 52335 = 32769332 :=
  leaf_weighted (k := 24) (d := 10) (H := 52335) (keep := keep2) (twice := twice2) rows (by decide) (by decide) (bal2) (invRow2 (H := 52335) (by decide) (by decide +kernel)) sum52335

theorem h4077 : P.leaf 34 4077 = 32769332 :=
  orient5 (v := 52335) (by decide) (by decide +kernel) h52335

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

theorem cover50159 : P.CoversSplit 24 10 50159 0xfffffffffafafafafffffffffafafafafffffffffafafafafffffffffafafafaffccffccfac8fac8ffccffccfac8fac8ffccffccfac8fac8ffccffccfac8fac8fffffffffafafafafffffffffafafafafffffffffafafafafffffffffafafafaffccffccfac8fac8ffccffccfac8fac8ffccffccfac8fac8ffccffccfac8fac8 :=
  coversSplit check rows (by decide) (by decide) (xs := [515, 522, 859, 915]) (by decide +kernel)

noncomputable def f50159 (i : ℕ) := rowWeight keep0 twice0 i * P.leaf 24 (51362816 + i)

theorem c50159_0 : rowSum f50159 0 173 = 26165763 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 50159) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover50159 (by decide)
  decide +kernel

theorem c50159_1 : rowSum f50159 173 216 = 66378849 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 50159) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover50159 (by decide)
  decide +kernel

theorem c50159_2 : rowSum f50159 389 110 = 103042226 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 50159) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover50159 (by decide)
  decide +kernel

theorem c50159_3 : rowSum f50159 499 449 = 150852819 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 50159) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover50159 (by decide)
  decide +kernel

theorem c50159_4 : rowSum f50159 948 76 = 55558631 := by
  apply weightedChunk_eq (b := 20) (m := 4) (d := 10) (H := 50159) (keep := keep0) (twice := twice0) check rows elimOK (by decide) (by decide) cover50159 (by decide)
  decide +kernel

theorem sum50159 : rowSum f50159 0 1024 = 401998288 :=
  rowSum_append (F := f50159) (lo := 0) (n := 173) (m := 851) (A := 26165763) (B := 375832525) c50159_0 (rowSum_append (F := f50159) (lo := 173) (n := 216) (m := 635) (A := 66378849) (B := 309453676) c50159_1 (rowSum_append (F := f50159) (lo := 389) (n := 110) (m := 525) (A := 103042226) (B := 206411450) c50159_2 (rowSum_append (F := f50159) (lo := 499) (n := 449) (m := 76) (A := 150852819) (B := 55558631) c50159_3 (c50159_4))))

theorem h50159 : P.leaf 34 50159 = 401998288 :=
  leaf_weighted (k := 24) (d := 10) (H := 50159) (keep := keep0) (twice := twice0) rows (by decide) (by decide) (bal0) (invRow0 (H := 50159) (by decide) (by decide +kernel)) sum50159

theorem h4094 : P.leaf 34 4094 = 401998288 :=
  orient24 (v := 50159) (by decide) (by decide +kernel) h50159

def seg : List (ℕ × ℕ) := [(4030, 48), (4031, 48), (4076, 12), (4077, 12), (4078, 24), (4079, 24), (4094, 12)]

theorem segOK : checkSeg 16 perms 4030 4095 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 4030 4095 180 24923056272 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 24923056272)
    (SegSum.cons (w := 48) h4030 (SegSum.cons (w := 48) h4031 (SegSum.cons (w := 12) h4076 (SegSum.cons (w := 12) h4077 (SegSum.cons (w := 24) h4078 (SegSum.cons (w := 24) h4079 (SegSum.cons (w := 12) h4094 (show SegSum (P.leaf 34) [] 0 from rfl)))))))) (by decide)

end RACert.S4N1.C0.S23
