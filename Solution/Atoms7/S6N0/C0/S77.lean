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

namespace RACert.S6N0.C0.S77

open RACert RACert.Problem

theorem cover97145 : P.CoversSplit 26 10 97145 0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0c000000005000000000000000000000000000000000000000000000000000000000000000000000000f0f0f0f0f0f0f0f00000000000000000f0f0f0f0c000c00000000005000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 579, 923, 972, 979, 1273, 1315, 1322, 1658]) (by decide +kernel)

theorem c97145_0 : P.sumLeaves 26 99476480 982 = 82298136 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97145) (lo := 0) (len := 982) (W := 82298136) check rows elimOK (by decide) (by decide) cover97145 (by decide)
  decide +kernel

theorem c97145_1 : P.sumLeaves 26 99477462 42 = 79683552 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97145) (lo := 982) (len := 42) (W := 79683552) check rows elimOK (by decide) (by decide) cover97145 (by decide)
  decide +kernel

theorem h97145 : P.leaf 36 97145 = 161981688 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(982, 82298136), (42, 79683552)]) (.cons c97145_0 (.cons c97145_1 (.nil))) (by decide) (by decide))

theorem cover97146 : P.CoversSplit 26 10 97146 0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0c000000005000000000000000000000000000000000000000000000000000000000000000000000000f0f0f0f0f0f0f0f00000000000000000f0f0f0f0c000c00000000005000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 874, 972, 979, 1273, 1315, 1322, 1658]) (by decide +kernel)

theorem c97146_0 : P.sumLeaves 26 99477504 982 = 66135650 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97146) (lo := 0) (len := 982) (W := 66135650) check rows elimOK (by decide) (by decide) cover97146 (by decide)
  decide +kernel

theorem c97146_1 : P.sumLeaves 26 99478486 42 = 73404540 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97146) (lo := 982) (len := 42) (W := 73404540) check rows elimOK (by decide) (by decide) cover97146 (by decide)
  decide +kernel

theorem h97146 : P.leaf 36 97146 = 139540190 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(982, 66135650), (42, 73404540)]) (.cons c97146_0 (.cons c97146_1 (.nil))) (by decide) (by decide))

theorem cover97147 : P.CoversSplit 26 10 97147 0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0c000000005000000000000000000000000000000000000000000000000000000000000000000000000f0f0f0f0f0f0f0f00000000000000000f0f0f0f0c000c00000000005000000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [481, 972, 979, 1273, 1315, 1322, 1658]) (by decide +kernel)

theorem c97147_0 : P.sumLeaves 26 99478528 982 = 203331693 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97147) (lo := 0) (len := 982) (W := 203331693) check rows elimOK (by decide) (by decide) cover97147 (by decide)
  decide +kernel

theorem c97147_1 : P.sumLeaves 26 99479510 42 = 152801414 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97147) (lo := 982) (len := 42) (W := 152801414) check rows elimOK (by decide) (by decide) cover97147 (by decide)
  decide +kernel

theorem h97147 : P.leaf 36 97147 = 356133107 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(982, 203331693), (42, 152801414)]) (.cons c97147_0 (.cons c97147_1 (.nil))) (by decide) (by decide))

theorem cover97148 : P.CoversSplit 26 10 97148 0xfffffffffffffafa0000000000000000fffffffffffcfac805050500050000000505000005050000050500000505000005050000050400000505000005000000fffffffffffffafa0000000000000000ffffffffcc00c80005050500040000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [579, 874, 972, 979, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c97148_0 : P.sumLeaves 26 99479552 502 = 42507204 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97148) (lo := 0) (len := 502) (W := 42507204) check rows elimOK (by decide) (by decide) cover97148 (by decide)
  decide +kernel

theorem c97148_1 : P.sumLeaves 26 99480054 388 = 72847789 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97148) (lo := 502) (len := 388) (W := 72847789) check rows elimOK (by decide) (by decide) cover97148 (by decide)
  decide +kernel

theorem c97148_2 : P.sumLeaves 26 99480442 134 = 184864643 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97148) (lo := 890) (len := 134) (W := 184864643) check rows elimOK (by decide) (by decide) cover97148 (by decide)
  decide +kernel

theorem h97148 : P.leaf 36 97148 = 300219636 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(502, 42507204), (388, 72847789), (134, 184864643)]) (.cons c97148_0 (.cons c97148_1 (.cons c97148_2 (.nil)))) (by decide) (by decide))

theorem cover97149 : P.CoversSplit 26 10 97149 0xfffffffffffffafa0000000000000000fffffffffffcfac805050500050000000505000005050000050500000505000005050000050400000505000005000000fffffffffffffafa0000000000000000ffffffffcc00c80005050500040000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [579, 923, 972, 979, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c97149_0 : P.sumLeaves 26 99480576 502 = 111476881 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97149) (lo := 0) (len := 502) (W := 111476881) check rows elimOK (by decide) (by decide) cover97149 (by decide)
  decide +kernel

theorem c97149_1 : P.sumLeaves 26 99481078 388 = 178739277 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97149) (lo := 502) (len := 388) (W := 178739277) check rows elimOK (by decide) (by decide) cover97149 (by decide)
  decide +kernel

theorem c97149_2 : P.sumLeaves 26 99481466 134 = 351986844 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97149) (lo := 890) (len := 134) (W := 351986844) check rows elimOK (by decide) (by decide) cover97149 (by decide)
  decide +kernel

theorem h97149 : P.leaf 36 97149 = 642203002 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(502, 111476881), (388, 178739277), (134, 351986844)]) (.cons c97149_0 (.cons c97149_1 (.cons c97149_2 (.nil)))) (by decide) (by decide))

theorem cover97150 : P.CoversSplit 26 10 97150 0xfffffffffffffafa0000000000000000fffffffffffcfac805050500050000000505000005050000050500000505000005050000050400000505000005000000fffffffffffffafa0000000000000000ffffffffcc00c80005050500040000000000000000000000000000000000000000000000000000000000000000000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [579, 874, 972, 979, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c97150_0 : P.sumLeaves 26 99481600 502 = 94511515 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97150) (lo := 0) (len := 502) (W := 94511515) check rows elimOK (by decide) (by decide) cover97150 (by decide)
  decide +kernel

theorem c97150_1 : P.sumLeaves 26 99482102 388 = 182117766 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97150) (lo := 502) (len := 388) (W := 182117766) check rows elimOK (by decide) (by decide) cover97150 (by decide)
  decide +kernel

theorem c97150_2 : P.sumLeaves 26 99482490 134 = 378832097 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97150) (lo := 890) (len := 134) (W := 378832097) check rows elimOK (by decide) (by decide) cover97150 (by decide)
  decide +kernel

theorem h97150 : P.leaf 36 97150 = 655461378 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(502, 94511515), (388, 182117766), (134, 378832097)]) (.cons c97150_0 (.cons c97150_1 (.cons c97150_2 (.nil)))) (by decide) (by decide))

theorem cover97151 : P.CoversSplit 26 10 97151 0xfffffffffffffafa0000000000000000fffffffffffcfac805050500050000000505000005050000050500000505000005050000050400000505000005000000fffffffffffffafa0000000000000000ffffffffcc00c80005050500040000000505000005050000050500000505000005050000040000000505000004000000 :=
  coversSplit check rows (by decide) (by decide) (xs := [579, 972, 979, 1273, 1315, 1322, 1658, 1665]) (by decide +kernel)

theorem c97151_0 : P.sumLeaves 26 99482624 476 = 144988013 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97151) (lo := 0) (len := 476) (W := 144988013) check rows elimOK (by decide) (by decide) cover97151 (by decide)
  decide +kernel

theorem c97151_1 : P.sumLeaves 26 99483100 388 = 327447055 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97151) (lo := 476) (len := 388) (W := 327447055) check rows elimOK (by decide) (by decide) cover97151 (by decide)
  decide +kernel

theorem c97151_2 : P.sumLeaves 26 99483488 160 = 923666248 := by
  apply sumLeaves_splitChunk (b := 20) (m := 6) (d := 10) (H := 97151) (lo := 864) (len := 160) (W := 923666248) check rows elimOK (by decide) (by decide) cover97151 (by decide)
  decide +kernel

theorem h97151 : P.leaf 36 97151 = 1396101316 :=
  (leaf_eq_inner (k := 26) (d := 10) rows (by decide) (by decide)).trans
    (sumLeaves_of_chunks (cs := [(476, 144988013), (388, 327447055), (160, 923666248)]) (.cons c97151_0 (.cons c97151_1 (.cons c97151_2 (.nil)))) (by decide) (by decide))

def seg : List (ℕ × ℕ) := [(97145, 720), (97146, 720), (97147, 720), (97148, 720), (97149, 720), (97150, 720), (97151, 720)]

theorem segOK : checkSeg 20 perms 97145 97249 seg = true :=
  checkSeg_of_cols colsOK (by decide +kernel)

theorem total : OrbitSeg 20 perms (P.leaf 36) 97145 97249 5040 2629181028240 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel) (W' := 2629181028240)
    (SegSum.cons (w := 720) h97145 (SegSum.cons (w := 720) h97146 (SegSum.cons (w := 720) h97147 (SegSum.cons (w := 720) h97148 (SegSum.cons (w := 720) h97149 (SegSum.cons (w := 720) h97150 (SegSum.cons (w := 720) h97151 (show SegSum (P.leaf 36) [] 0 from rfl)))))))) (by decide)

end RACert.S6N0.C0.S77
