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

namespace RACert.S4N1.C0.S24

open RACert RACert.Problem

theorem cover4023 : P.CoversSplit 24 10 4023 0xfffffffff5f5a0a0fffffffff5f5a0a0fffffffff5f5a0a0fffffffff5f5a0a0ffffffffa000a000ff00ff00a000a000ffffffffa000a000ff00ff00a000a000fffffffff5f5a0a0fffffffff5f5a0a000000000000000000000000000000000ffffffffa000a000ff00ff00a000a00000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [517, 915, 1202, 1209, 1217, 1258, 1308]) (by decide +kernel)

theorem c4023_0 : P.sumLeaves 24 4119552 440 = 1359990 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 4023) (lo := 0) (len := 440) (W := 1359990) check rows elimOK (by decide) (by decide) cover4023 (by decide)
  decide +kernel

theorem c4023_1 : P.sumLeaves 24 4119992 184 = 3650079 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 4023) (lo := 440) (len := 184) (W := 3650079) check rows elimOK (by decide) (by decide) cover4023 (by decide)
  decide +kernel

theorem c4023_2 : P.sumLeaves 24 4120176 184 = 7970796 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 4023) (lo := 624) (len := 184) (W := 7970796) check rows elimOK (by decide) (by decide) cover4023 (by decide)
  decide +kernel

theorem c4023_3 : P.sumLeaves 24 4120360 128 = 8543446 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 4023) (lo := 808) (len := 128) (W := 8543446) check rows elimOK (by decide) (by decide) cover4023 (by decide)
  decide +kernel

theorem c4023_4 : P.sumLeaves 24 4120488 88 = 23836234 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 4023) (lo := 936) (len := 88) (W := 23836234) check rows elimOK (by decide) (by decide) cover4023 (by decide)
  decide +kernel

theorem h4023 : P.leaf 34 4023 = 45360545 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(440, 1359990), (184, 3650079), (184, 7970796), (128, 8543446), (88, 23836234)]) (.cons c4023_0 (.cons c4023_1 (.cons c4023_2 (.cons c4023_3 (.cons c4023_4 (.nil)))))) (by decide) (by decide))

theorem cover4026 : P.CoversSplit 24 10 4026 0xfffffffff5f5a0a0fffffffff5f5a0a0aaaaafaf00000000aaaaafaf00000000ffffffffa000a000ff00ff00a000a000aaaaafaf00000000aa00af0000000000fffffffff5f5a0a0fffffffff5f5a0a000000000000000000000000000000000ffffffffa000a000ff00ff00a000a00000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [465, 517, 915, 916, 1202, 1209, 1258, 1308]) (by decide +kernel)

theorem c4026_0 : P.sumLeaves 24 4122624 440 = 984948 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 4026) (lo := 0) (len := 440) (W := 984948) check rows elimOK (by decide) (by decide) cover4026 (by decide)
  decide +kernel

theorem c4026_1 : P.sumLeaves 24 4123064 246 = 3640868 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 4026) (lo := 440) (len := 246) (W := 3640868) check rows elimOK (by decide) (by decide) cover4026 (by decide)
  decide +kernel

theorem c4026_2 : P.sumLeaves 24 4123310 234 = 7599564 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 4026) (lo := 686) (len := 234) (W := 7599564) check rows elimOK (by decide) (by decide) cover4026 (by decide)
  decide +kernel

theorem c4026_3 : P.sumLeaves 24 4123544 104 = 16895950 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 4026) (lo := 920) (len := 104) (W := 16895950) check rows elimOK (by decide) (by decide) cover4026 (by decide)
  decide +kernel

theorem h4026 : P.leaf 34 4026 = 29121330 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(440, 984948), (246, 3640868), (234, 7599564), (104, 16895950)]) (.cons c4026_0 (.cons c4026_1 (.cons c4026_2 (.cons c4026_3 (.nil))))) (by decide) (by decide))

theorem cover4027 : P.CoversSplit 24 10 4027 0xfffffffff5f5a0a0fffffffff5f5a0a0fffffffff5f5a0a0fffffffff5f5a0a0ffffffffa000a000ff00ff00a000a000ffffffffa000a000ff00ff00a000a000fffffffff5f5a0a0fffffffff5f5a0a000000000000000000000000000000000ffffffffa000a000ff00ff00a000a00000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [517, 915, 916, 1202, 1209, 1217, 1258, 1308]) (by decide +kernel)

theorem c4027_0 : P.sumLeaves 24 4123648 440 = 2117152 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 4027) (lo := 0) (len := 440) (W := 2117152) check rows elimOK (by decide) (by decide) cover4027 (by decide)
  decide +kernel

theorem c4027_1 : P.sumLeaves 24 4124088 184 = 7141912 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 4027) (lo := 440) (len := 184) (W := 7141912) check rows elimOK (by decide) (by decide) cover4027 (by decide)
  decide +kernel

theorem c4027_2 : P.sumLeaves 24 4124272 184 = 14613289 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 4027) (lo := 624) (len := 184) (W := 14613289) check rows elimOK (by decide) (by decide) cover4027 (by decide)
  decide +kernel

theorem c4027_3 : P.sumLeaves 24 4124456 128 = 16369273 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 4027) (lo := 808) (len := 128) (W := 16369273) check rows elimOK (by decide) (by decide) cover4027 (by decide)
  decide +kernel

theorem c4027_4 : P.sumLeaves 24 4124584 88 = 41937674 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 4027) (lo := 936) (len := 88) (W := 41937674) check rows elimOK (by decide) (by decide) cover4027 (by decide)
  decide +kernel

theorem h4027 : P.leaf 34 4027 = 82179300 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(440, 2117152), (184, 7141912), (184, 14613289), (128, 16369273), (88, 41937674)]) (.cons c4027_0 (.cons c4027_1 (.cons c4027_2 (.cons c4027_3 (.cons c4027_4 (.nil)))))) (by decide) (by decide))

theorem cover4028 : P.CoversSplit 24 10 4028 0xff00ff00f000a000ff22ff22f020a020aa00af0000000000aa00af00000000000000000000000000330033002000200000000000000000002200230000000000ff00ff00f000a000ff22ff22f020a020000000000000000000000000000000000000000000000000330033002000200000000000000000000000000000000000 :=
  coversProjected check rows (by decide) (by decide) (xs := [465, 473, 508, 517, 915, 1202, 1209, 1308]) (ps := [(14, [923], [915])]) (by decide +kernel)

theorem c4028_0 : P.sumLeaves 24 4124672 909 = 3727980 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 4028) (lo := 0) (len := 909) (W := 3727980) check rows elimOK (by decide) (by decide) cover4028 (by decide)
  decide +kernel

theorem c4028_1 : P.sumLeaves 24 4125581 115 = 9599332 := by
  apply sumLeaves_splitChunk (b := 20) (m := 4) (d := 10) (H := 4028) (lo := 909) (len := 115) (W := 9599332) check rows elimOK (by decide) (by decide) cover4028 (by decide)
  decide +kernel

theorem h4028 : P.leaf 34 4028 = 13327312 :=
  (leaf_eq_inner (k := 24) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(909, 3727980), (115, 9599332)]) (.cons c4028_0 (.cons c4028_1 (.nil))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(4023, 24), (4026, 24), (4027, 24), (4028, 48)]

theorem segOK : checkSeg 16 perms 4023 4029 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 16 perms (P.leaf 34) 4023 4029 120 4399579176 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 4399579176)
    (SegSum.cons (w := 24) h4023 (SegSum.cons (w := 24) h4026 (SegSum.cons (w := 24) h4027 (SegSum.cons (w := 48) h4028 (show SegSum (P.leaf 34) [] 0 from rfl))))) (by decide)

end RACert.S4N1.C0.S24
